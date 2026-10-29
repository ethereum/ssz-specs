import SszNative.Proofs.Kernel.Avx2.View
import SszNative.Proofs.Kernel.Avx512.Moves

/-!
The eight-lane kernel's data movement: loading and transposing messages, and transposing and storing digests.

```text
    after the loads:      register j holds node j's eight words
    after the transpose:  row t holds word t of every node, node j in lane j
```

The same transpose runs both ways: on the loaded nodes, and on the eight digest words.
-/

namespace EthLib.Consensus.Ssz.Native.Kernel.Avx2

open EthLib.Cryptography.Hash.Sha256 hiding K IV
open EthLib.Consensus.Ssz.Native.Asm
open EthLib.Consensus.Ssz.Native.Kernel.Avx512 (assign_apply)

/-- The mask load, the byte reversals, and the transpose of the loaded nodes. -/
def loadMoves : List Instr :=
  [.vloadHalf mask (tableEntry bswapAvx512)] ++ (List.range 8).map (fun j => .yshufb (home j) (home j) mask) ++ transpose

/-- The mask load, the transpose of the digest words, and the byte reversals. -/
def outMoves : List Instr :=
  [.vloadHalf mask (tableEntry bswapAvx512)] ++ transpose ++
    (List.range 8).map (fun j => .yshufb (transposed j) (transposed j) mask)

/-- Lane j of row t after the input moves is lane t of register j, byte-reversed, and zero above lane 8. -/
theorem loadMoves_sources : ∀ t : Fin 8, ∀ j : Fin 16,
    absExec loadMoves Abs.start (transposed t.val) j =
      if j.val < 8 then .swap (home j.val) ⟨t.val, by omega⟩ else .const 0 := by
  -- The tracker's result for every lane, checked by evaluation.
  decide +kernel

/-- Lane j of row p after the output moves is lane p of register j, byte-reversed, and zero above lane 8. -/
theorem outMoves_sources : ∀ p : Fin 8, ∀ j : Fin 16,
    absExec outMoves Abs.start (transposed p.val) j =
      if j.val < 8 then .swap (home j.val) ⟨p.val, by omega⟩ else .const 0 := by
  -- The tracker's result for every lane, checked by evaluation.
  decide +kernel

/-- The input moves only move lanes. -/
theorem loadMoves_moves : loadMoves.all Instr.moves = true := by
  -- Every instruction is checked by evaluation.
  decide +kernel

/-- The output moves only move lanes. -/
theorem outMoves_moves : outMoves.all Instr.moves = true := by
  -- Every instruction is checked by evaluation.
  decide +kernel

/-- Lane moves leave the carry flag alone. -/
theorem exec_moves_cf (body : List Instr) (h : body.all Instr.moves) (s : State) : (exec body s).cf = s.cf := by
  induction body generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    -- The first move writes only a vector register, and so does the rest.
    rw [exec_cons, ih h.2]
    have := h.1
    cases i <;> simp_all [Instr.moves, exec1] <;> split <;> rfl

/-- Eight node loads, node j into register j. -/
def loads (base : Gpr) (stride : Nat) : List Instr :=
  (List.range 8).map fun j => .vloadHalf (home j) ⟨base, stride * j⟩

/-- Register j, for j below 8, holds node j's eight words after the loads, and zero above. -/
theorem loads_spec (base : Gpr) (stride : Nat) (s : State) :
    (∀ j < 8, ∀ l : Fin 16, (exec (loads base stride) s).vec (home j) l =
      if l.val < 8 then readWord s.mem ((s.gpr base).toNat + stride * j + 4 * l.val) else 0) ∧
    (exec (loads base stride) s).gpr = s.gpr ∧ (exec (loads base stride) s).mem = s.mem ∧
    (exec (loads base stride) s).zf = s.zf ∧ (exec (loads base stride) s).cf = s.cf := by
  refine ⟨fun j hj l => ?_, ?_, ?_, ?_, ?_⟩
  -- Each of the eight loads writes one register.
  · match j, hj with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
      simp [loads, exec, exec1, assign, home, State.addr, List.range, List.range.loop]
  all_goals simp [loads, exec, exec1, List.range, List.range.loop]

/-- Stores of registers to rows at distinct offsets from one base, as one lane sees them. -/
def stores (base : Gpr) (offset : Nat → Nat) (src : Nat → Vreg) (n : Nat) : List Instr :=
  (List.range n).map fun t => .vstoreHalf ⟨base, offset t⟩ (src t)

/-- After stores to distinct rows, each row holds its register's lane, and every other row is kept. -/
theorem viewRun_stores (G : Gpr → UInt64) (base : Gpr) (offset : Nat → Nat) (src : Nat → Vreg) (n : Nat)
    (inj : ∀ t < n, ∀ t' < n, offset t = offset t' → t = t') (v : Avx512x2.View) :
    (∀ t < n, (viewRun G (stores base offset src n) v).mem ((G base).toNat + offset t) = v.regs (src t)) ∧
    (∀ a, (∀ t < n, a ≠ (G base).toNat + offset t) → (viewRun G (stores base offset src n) v).mem a = v.mem a) ∧
    (viewRun G (stores base offset src n) v).regs = v.regs := by
  induction n with
  | zero => exact ⟨fun _ h => absurd h (by omega), fun _ _ => rfl, rfl⟩
  | succ n ih =>
    obtain ⟨rows, others, regs⟩ := ih fun t ht t' ht' e => inj t (by omega) t' (by omega) e
    have split : stores base offset src (n + 1) = stores base offset src n ++ [.vstoreHalf ⟨base, offset n⟩ (src n)] := by
      simp [stores, List.range_succ]
    rw [split, viewRun_append]
    simp only [viewRun, viewStep, Avx512x2.addrOf, assign_apply]
    refine ⟨fun t ht => ?_, fun a ha => ?_, regs⟩
    · -- The last store's row takes its register, and earlier rows sit at other offsets.
      by_cases last : t = n
      · subst last; simp [regs]
      · rw [ite_eq_right (fun e => last (inj t ht n (by omega) (by omega))), rows t (by omega)]
    · rw [ite_eq_right (ha n (by omega)), others a fun t ht => ha t (by omega)]

/-- The rows of one transposed half of a batch's schedule words. -/
abbrev wordStores (first : Nat) : List Instr := stores sp (fun t => wordSlot (first + t)) transposed 8

/-- Loading eight nodes is the loads, the moves, and the stores. -/
theorem loadWords_eq (base : Gpr) (stride first : Nat) :
    loadWords base stride first = loads base stride ++ loadMoves ++ wordStores first := by
  simp [loadWords, loads, loadMoves, wordStores, stores, List.append_assoc]

/-- Schedule rows sit 32 bytes apart. -/
theorem wordSlot_mod (u : Nat) (hu : u < 80) : ∃ q, wordSlot u = 32 * q := ⟨79 - u, by simp only [wordSlot, frame]; omega⟩

/--
Loading eight nodes stores word t of node l, byte-reversed, at schedule row first + t, lane l.

Every other row of the scratch area's 32-byte grid, and every byte outside the eight rows, is kept.
-/
theorem loadWords_spec (base : Gpr) (stride first : Nat) (hf : first ≤ 8) (s : State)
    (table : TableAt s.mem (s.gpr tbl).toNat) :
    let s' := exec (loadWords base stride first) s
    let S := (s.gpr sp).toNat
    (∀ t < 8, ∀ l : Fin 8, readWord s'.mem (S + wordSlot (first + t) + 4 * l.val) =
      bswap (readWord s.mem ((s.gpr base).toNat + stride * l.val + 4 * t))) ∧
    (∀ (q : Nat) (l : Fin 8), (∀ t < 8, S + 32 * q ≠ S + wordSlot (first + t)) →
      readWord s'.mem (S + 32 * q + 4 * l.val) = readWord s.mem (S + 32 * q + 4 * l.val)) ∧
    (∀ x, (∀ t < 8, x < S + wordSlot (first + t) ∨ S + wordSlot (first + t) + 32 ≤ x) → s'.mem x = s.mem x) ∧
    s'.gpr = s.gpr ∧ s'.zf = s.zf ∧ s'.cf = s.cf := by
  intro s' S
  obtain ⟨loaded, g1, m1, z1, c1⟩ := loads_spec base stride s
  let s1 := exec (loads base stride) s
  -- The moves, from the loaded registers.
  have moved := absExec_sound loadMoves loadMoves_moves s1.vec Abs.start s1 (agrees_start _)
    (by rw [g1, m1]; exact table)
  let s2 := exec loadMoves s1
  obtain ⟨agree, m2, g2, z2⟩ := moved
  have c2 : s2.cf = s1.cf := exec_moves_cf _ loadMoves_moves _
  have row : ∀ t < 8, ∀ l : Fin 8, s2.vec (transposed t) (lane l) =
      bswap (readWord s.mem ((s.gpr base).toNat + stride * l.val + 4 * t)) := fun t ht l => by
    have src := loadMoves_sources ⟨t, ht⟩ (lane l)
    rw [ite_eq_left (show (lane l).val < 8 from l.isLt)] at src
    rw [agree _ _ (by rw [src]; simp), src]
    exact congrArg bswap ((loaded (lane l).val l.isLt ⟨t, by omega⟩).trans (ite_eq_left ht))
  -- The stores, lane by lane.
  have whole : s' = exec (wordStores first) s2 := by
    simp only [s', s2, s1, loadWords_eq, exec_append]
  have inj : ∀ t < 8, ∀ t' < 8, wordSlot (first + t) = wordSlot (first + t') → t = t' := fun t _ t' _ e => by
    simp only [wordSlot, frame] at e; omega
  have stored := exec_view (wordStores first) (by simp [wordStores, stores, rowwise]) s2
    (by simp [readsOf, wordStores, stores, readOf])
  obtain ⟨_, smem, sfar, sg, sz, sc⟩ := stored
  have gS : (s2.gpr sp).toNat = S := by rw [g2, g1]
  have clear : ∀ q, Clear (storesOf s2.gpr (wordStores first)) (S + 32 * q) := fun q A hA => by
    simp only [storesOf, wordStores, stores, List.filterMap_map, List.mem_filterMap, List.mem_range, Function.comp,
      storeOf, Option.some.injEq, Avx512x2.addrOf, gS] at hA
    obtain ⟨t, ht, rfl⟩ := hA
    obtain ⟨q', hq'⟩ := wordSlot_mod (first + t) (by omega)
    left; rw [hq']; omega
  refine ⟨fun t ht l => ?_, fun q l hq => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := wordSlot_mod (first + t) (by omega)
    rw [whole, show S + wordSlot (first + t) = S + 32 * q by rw [hq], smem l _ (clear q), ← hq, ← gS,
      (viewRun_stores s2.gpr sp (fun t => wordSlot (first + t)) transposed 8 inj (view s2 l)).1 t ht]
    exact row t ht l
  · rw [whole, smem l _ (clear q), (viewRun_stores s2.gpr sp (fun t => wordSlot (first + t)) transposed 8 inj
      (view s2 l)).2.1 _ (by rw [gS]; exact hq)]
    simp only [view]; rw [m2, m1]
  · rw [whole, sfar x (fun A hA => by
      simp only [storesOf, wordStores, stores, List.filterMap_map, List.mem_filterMap, List.mem_range,
        Function.comp, storeOf, Option.some.injEq, Avx512x2.addrOf, gS] at hA
      obtain ⟨t, ht, rfl⟩ := hA
      exact hx t ht), m2, m1]
  · rw [whole, sg, g2, g1]
  · rw [whole, sz, z2, z1]
  · rw [whole, sc, c2, c1]

/-- The digest stores: row p, the digest of pair p, 32 bytes past the output address per pair. -/
abbrev outStores : List Instr := stores out (fun p => 32 * p) transposed 8

/-- The output is the second feed-forward, the moves, and the stores. -/
theorem outputCode_eq : outputCode = finishCode ++ outMoves ++ outStores := by
  simp [outputCode, outMoves, stores, List.append_assoc]

/-- The digest stores write row p's bytes 32p bytes past the output address, and nothing else. -/
theorem outStores_mem (s : State) (n : Nat) (hn : n ≤ 8) :
    (∀ x, (exec (stores out (fun p => 32 * p) transposed n) s).mem x =
      if (s.gpr out).toNat ≤ x ∧ x < (s.gpr out).toNat + 32 * n then
        laneByte (s.vec (transposed ((x - (s.gpr out).toNat) / 32))) ((x - (s.gpr out).toNat) % 32)
      else s.mem x) ∧
    (exec (stores out (fun p => 32 * p) transposed n) s).gpr = s.gpr ∧
    (exec (stores out (fun p => 32 * p) transposed n) s).vec = s.vec ∧
    (exec (stores out (fun p => 32 * p) transposed n) s).zf = s.zf ∧
    (exec (stores out (fun p => 32 * p) transposed n) s).cf = s.cf := by
  induction n with
  | zero =>
    refine ⟨fun x => ?_, rfl, rfl, rfl, rfl⟩
    simp only [stores, List.range_zero, List.map_nil, exec_nil]
    rw [ite_eq_right (by omega)]
  | succ n ih =>
    obtain ⟨mem, gpr, vec, zf, cf⟩ := ih (by omega)
    have split : stores out (fun p => 32 * p) transposed (n + 1) =
        stores out (fun p => 32 * p) transposed n ++ [.vstoreHalf ⟨out, 32 * n⟩ (transposed n)] := by
      simp [stores, List.range_succ]
    rw [split, exec_append]
    generalize exec (stores out (fun p => 32 * p) transposed n) s = s' at *
    simp only [exec_cons, exec_nil, exec1, State.addr, gpr, vec]
    refine ⟨fun x => ?_, trivial, trivial, zf, cf⟩
    -- The new row, or an earlier one, or memory as it was.
    simp only [store]
    by_cases inside : (s.gpr out).toNat + 32 * n ≤ x ∧ x < (s.gpr out).toNat + 32 * n + 32
    · rw [ite_eq_left inside, ite_eq_left (by omega), show (x - (s.gpr out).toNat) / 32 = n by omega,
        show x - ((s.gpr out).toNat + 32 * n) = (x - (s.gpr out).toNat) % 32 by omega]
    · rw [ite_eq_right inside, mem x]
      by_cases before : (s.gpr out).toNat ≤ x ∧ x < (s.gpr out).toNat + 32 * n
      · rw [ite_eq_left before, ite_eq_left (by omega)]
      · rw [ite_eq_right before, ite_eq_right (by omega)]

/-- Byte m of a byte-reversed word, the least significant first, is byte m of the word, the most significant first. -/
theorem bswap_byte (y : UInt32) (m : Nat) (hm : m < 4) :
    (bswap y >>> (8 * m).toUInt32).toUInt8 = (y >>> (24 - 8 * UInt32.ofNat m)).toUInt8 := by
  -- Each of the four byte positions is checked bit by bit.
  match m, hm with
  | 0, _ | 1, _ | 2, _ | 3, _ =>
    apply byte_ext
    simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
    simp [bswap]

/-- Byte k of the digest of a state. -/
theorem digest_get (st : Vector UInt32 8) (k : Nat) (hk : k < 32) :
    (digest st).get! k = (st[k / 4]'(by omega) >>> (24 - 8 * UInt32.ofNat (k % 4))).toUInt8 := by
  -- The digest writes each word's bytes, the most significant first.
  rw [get!_eq _ _ (by simp [digest, ByteArray.size]; exact hk)]
  simp [digest, ByteArray.getElem_eq_getElem_data]

/-- After the output moves and stores, bytes 32p to 32p + 31 past the output are the digest of lane p's state. -/
theorem output_spec (s : State) (table : TableAt s.mem (s.gpr tbl).toNat) :
    let s' := exec (outMoves ++ outStores) s
    (∀ p (hp : p < 8), ∀ k < 32, s'.mem ((s.gpr out).toNat + 32 * p + k) =
      (digest (Vector.ofFn fun j : Fin 8 => s.vec (home j.val) ⟨p, by omega⟩)).get! k) ∧
    (∀ x, ¬ ((s.gpr out).toNat ≤ x ∧ x < (s.gpr out).toNat + 256) → s'.mem x = s.mem x) ∧
    s'.gpr = s.gpr ∧ s'.zf = s.zf ∧ s'.cf = s.cf := by
  intro s'
  obtain ⟨agree, m1, g1, z1⟩ := absExec_sound outMoves outMoves_moves s.vec Abs.start s (agrees_start _) table
  have c1 := exec_moves_cf _ outMoves_moves s
  obtain ⟨mem, g2, v2, z2, c2⟩ := outStores_mem (exec outMoves s) 8 (Nat.le_refl _)
  have whole : s' = exec outStores (exec outMoves s) := exec_append _ _ _
  rw [← whole] at mem g2 v2 z2 c2
  refine ⟨fun p hp k hk => ?_, fun x hx => ?_, g2.trans g1, z2.trans z1, c2.trans c1⟩
  · rw [mem, g1, ite_eq_left (by omega), show ((s.gpr out).toNat + 32 * p + k - (s.gpr out).toNat) / 32 = p by omega,
      show ((s.gpr out).toNat + 32 * p + k - (s.gpr out).toNat) % 32 = k by omega, digest_get _ _ hk,
      Vector.getElem_ofFn]
    -- Byte k of row p is byte k mod 4 of lane k / 4, which holds word k / 4 of pair p, byte-reversed.
    have src := outMoves_sources ⟨p, hp⟩ ⟨k / 4, by omega⟩
    rw [ite_eq_left (show k / 4 < 8 by omega)] at src
    simp only [laneByte, laneOf, wordByte]
    rw [show (⟨k / 4 % 16, by omega⟩ : Fin 16) = ⟨k / 4, by omega⟩ by apply Fin.ext; simp; omega,
      agree _ _ (by rw [src]; simp), src]
    exact bswap_byte _ (k % 4) (by omega)
  · rw [mem, g1, ite_eq_right (by omega), m1]

end EthLib.Consensus.Ssz.Native.Kernel.Avx2
