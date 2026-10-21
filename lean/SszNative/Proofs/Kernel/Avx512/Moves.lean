import SszNative.Proofs.Kernel.Avx512.Lanes
import SszNative.Proofs.Asm.Spec
import SszNative.Kernel.Avx512

/-!
The sixteen-lane kernel's data movement: loading and transposing messages, and transposing and storing digests.

```text
    after the loads:      register i holds whole nodes, two per register
    after the transpose:  register t holds word t of every message, message j in lane j
    before the stores:    register k holds digests 2k and 2k + 1, one per half
```
-/

namespace Ssz.Native.Kernel.Avx512

open Ssz.Native.Asm Ssz.Sha256

/-- Reversing a little-endian read gives the big-endian read of the same four bytes. -/
theorem bswap_readWord (mem : Nat → UInt8) (a : Nat) :
    bswap (readWord mem a) =
      (mem a).toUInt32 <<< 24 ||| (mem (a + 1)).toUInt32 <<< 16 ||| (mem (a + 2)).toUInt32 <<< 8 |||
        (mem (a + 3)).toUInt32 := by
  -- Compare the words bit by bit.
  apply word_ext
  simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
  simp [readWord, bswap]

/-- Byte i of a pair: the left node's bytes, then the right node's. -/
theorem pairMessage_get (mem : Nat → UInt8) (left right i : Nat) (within : i < 64) :
    (pairMessage mem left right).get! i = if i < 32 then mem (left + i) else mem (right + (i - 32)) := by
  -- The message's byte i is read from the left node below 32, and from the right node above.
  rw [get!_eq _ _ (by simp [pairMessage, ByteArray.size]; exact within)]
  simp [pairMessage, ByteArray.getElem_eq_getElem_data]

/-- Word t of a pair is a byte-reversed read of its node, at word t mod 8. -/
theorem pairMessage_word (mem : Nat → UInt8) (left right t : Nat) (within : t < 16) :
    wordAt (pairMessage mem left right) (4 * t) =
      bswap (readWord mem ((if t < 8 then left else right) + 4 * (t % 8))) := by
  rw [bswap_readWord]
  simp only [wordAt]
  rw [pairMessage_get _ _ _ _ (by omega), pairMessage_get _ _ _ _ (by omega), pairMessage_get _ _ _ _ (by omega),
    pairMessage_get _ _ _ _ (by omega)]
  -- Words 0 to 7 come from the left node, and words 8 to 15 from the right one.
  by_cases low : t < 8
  · simp only [show 4 * t < 32 by omega, show 4 * t + 1 < 32 by omega, show 4 * t + 2 < 32 by omega,
      show 4 * t + 3 < 32 by omega, low, ↓reduceIte, Nat.mod_eq_of_lt low, Nat.add_assoc]
  · simp only [show ¬ 4 * t < 32 by omega, show ¬ 4 * t + 1 < 32 by omega, show ¬ 4 * t + 2 < 32 by omega,
      show ¬ 4 * t + 3 < 32 by omega, low, ↓reduceIte, Nat.add_assoc]
    rw [show 4 * t - 32 = 4 * (t % 8) by omega, show 4 * t + 1 - 32 = 4 * (t % 8) + 1 by omega,
      show 4 * t + 2 - 32 = 4 * (t % 8) + 2 by omega, show 4 * t + 3 - 32 = 4 * (t % 8) + 3 by omega]

/-- The loads write only vector registers. -/
theorem loadCode_frame (ls rs : Nat) (s : State) :
    (exec (loadCode ls rs) s).gpr = s.gpr ∧ (exec (loadCode ls rs) s).mem = s.mem ∧
      (exec (loadCode ls rs) s).zf = s.zf := by
  -- The loads write only vector registers.
  simp [loadCode, exec, exec1, List.range, List.range.loop]

/-- Register i, for i below 8, holds left nodes i and 8 + i. -/
theorem load_left (ls rs : Nat) (s : State) (i : Nat) (hi : i < 8) (l : Fin 16) :
    (exec (loadCode ls rs) s).vec (ring i) l =
      if l.val < 8 then readWord s.mem ((s.gpr left).toNat + ls * i + 4 * l.val)
      else readWord s.mem ((s.gpr left).toNat + ls * (8 + i) + 4 * (l.val - 8)) := by
  -- Each of the eight loads writes one register, its low half and then its high half.
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [loadCode, exec, exec1, assign, ring, State.addr, List.range, List.range.loop]
    split <;> simp_all

/-- Register 8 + i, for i below 8, holds right nodes i and 8 + i. -/
theorem load_right (ls rs : Nat) (s : State) (i : Nat) (hi : i < 8) (l : Fin 16) :
    (exec (loadCode ls rs) s).vec (ring (8 + i)) l =
      if l.val < 8 then readWord s.mem ((s.gpr right).toNat + rs * i + 4 * l.val)
      else readWord s.mem ((s.gpr right).toNat + rs * (8 + i) + 4 * (l.val - 8)) := by
  -- Each of the eight loads writes one register, its low half and then its high half.
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    simp [loadCode, exec, exec1, assign, ring, State.addr, List.range, List.range.loop]
    split <;> simp_all

/-- Lane j of register t after the transpose and byte reversal comes from one loaded lane. -/
theorem transposeIn_sources : ∀ t : Fin 16, ∀ j : Fin 16,
    absExec (transposeIn ++ swapIn) Abs.start (ring t.val) j =
      .swap (ring (j.val % 8 + 8 * (t.val / 8))) ⟨8 * (j.val / 8) + t.val % 8, by omega⟩ := by
  -- The tracker's result for every lane, checked by evaluation.
  decide +kernel

/-- The transpose and the byte reversal only move lanes. -/
theorem transposeIn_moves : (transposeIn ++ swapIn).all Instr.moves = true := by
  -- Every instruction of the transpose is checked by evaluation.
  decide +kernel

/-- Lane j of the loaded register holding word t of message j, read from that message's node. -/
private theorem loaded_word (ls rs : Nat) (s : State) (t j : Nat) (ht : t < 16) (hj : j < 16) :
    (exec (loadCode ls rs) s).vec (ring (j % 8 + 8 * (t / 8))) ⟨8 * (j / 8) + t % 8, by omega⟩ =
      readWord s.mem ((if t < 8 then (s.gpr left).toNat + ls * j else (s.gpr right).toNat + rs * j) +
        4 * (t % 8)) := by
  by_cases low : t < 8
  · rw [show j % 8 + 8 * (t / 8) = j % 8 by omega, load_left ls rs s (j % 8) (by omega)]
    simp only [low, ↓reduceIte]
    -- Lanes 0 to 7 hold node j % 8, and lanes 8 to 15 node 8 + j % 8.
    by_cases first : j < 8
    · simp only [show 8 * (j / 8) + t % 8 < 8 by omega, ↓reduceIte, Nat.mod_eq_of_lt first]
      rw [show 8 * (j / 8) + t % 8 = t % 8 by omega]
    · simp only [show ¬ 8 * (j / 8) + t % 8 < 8 by omega, ↓reduceIte]
      rw [show 8 + j % 8 = j by omega, show 8 * (j / 8) + t % 8 - 8 = t % 8 by omega]
  · rw [show j % 8 + 8 * (t / 8) = 8 + j % 8 by omega, load_right ls rs s (j % 8) (by omega)]
    simp only [low, ↓reduceIte]
    by_cases first : j < 8
    · simp only [show 8 * (j / 8) + t % 8 < 8 by omega, ↓reduceIte, Nat.mod_eq_of_lt first]
      rw [show 8 * (j / 8) + t % 8 = t % 8 by omega]
    · simp only [show ¬ 8 * (j / 8) + t % 8 < 8 by omega, ↓reduceIte]
      rw [show 8 + j % 8 = j by omega, show 8 * (j / 8) + t % 8 - 8 = t % 8 by omega]

/-- After the loads, transpose, and byte reversal, register t holds word t of every message, message j in lane j. -/
theorem prologue (ls rs : Nat) (s : State) (table : TableAt s.mem (s.gpr tbl).toNat) :
    let s' := exec (loadCode ls rs ++ transposeIn ++ swapIn) s
    (∀ t < 16, ∀ j : Fin 16, s'.vec (ring t) j =
      wordAt (pairMessage s.mem ((s.gpr left).toNat + ls * j.val) ((s.gpr right).toNat + rs * j.val)) (4 * t)) ∧
    s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.zf = s.zf := by
  intro s'
  -- The loads, then the lane moves from the loaded state.
  have split : s' = exec (transposeIn ++ swapIn) (exec (loadCode ls rs) s) := by
    simp only [s', exec_append]
  have frame := loadCode_frame ls rs s
  have moved := absExec_sound (transposeIn ++ swapIn) transposeIn_moves (exec (loadCode ls rs) s).vec Abs.start
    (exec (loadCode ls rs) s) (agrees_start _) (by rw [frame.1, frame.2.1]; exact table)
  rw [← split] at moved
  refine ⟨?_, moved.2.2.1.trans frame.1, moved.2.1.trans frame.2.1, moved.2.2.2.trans frame.2.2⟩
  intro t ht j
  have sources := transposeIn_sources ⟨t, ht⟩ j
  rw [moved.1 _ _ (by simp only at sources; rw [sources]; simp), sources]
  simp only [Src.denote]
  rw [loaded_word ls rs s t j.val ht j.isLt, pairMessage_word _ _ _ t ht]

/-- Register k after the transpose out holds digest 2k in its low half and digest 2k + 1 in its high half. -/
theorem transposeOut_sources : ∀ k : Fin 8, ∀ l : Fin 16, absExec transposeOut Abs.start (home k.val) l =
    .reg (home (l.val % 8)) ⟨2 * k.val + l.val / 8, by omega⟩ := by
  -- The tracker's result for every lane, checked by evaluation.
  decide +kernel

/-- The transpose out only moves lanes. -/
theorem transposeOut_moves : transposeOut.all Instr.moves = true := by
  -- Every instruction of the transpose is checked by evaluation.
  decide +kernel

/-- The table's byte-reversal row: lane l is the reversal index of lane l. -/
theorem bswapRow : ∀ l : Fin 16, tableWord (bswapAvx512 / 4 + l.val) = reverseLane l.val := by
  -- Every lane of the row is checked by evaluation.
  decide +kernel

/-- One stored byte: byte x of the 512 output bytes, from the digest register holding it, byte-reversed. -/
def outByte (v : Vreg → Lanes) (x : Nat) : UInt8 :=
  laneByte (fun l => bswap (v (home (x / 64)) l)) (x % 64)

/-- The store body for register k: reverse its bytes, then store its 64 bytes. -/
def storeStep (k : Nat) : List Instr :=
  [.vshufb (home k) (home k) (tmp 2), .vstore ⟨out, 64 * k⟩ (home k)]

/-- No working-word register is the mask temporary. -/
theorem home_ne_tmp (k : Nat) : home k ≠ tmp 2 := by
  -- Working words are registers 0 to 7, and the mask temporary is 27.
  simp only [home, tmp, ne_eq, Fin.ext_iff]
  omega

/-- The eight working-word registers are distinct. -/
theorem home_inj (k j : Nat) (hk : k < 8) (hj : j < 8) (same : home k = home j) : k = j := by
  -- Working words are taken modulo 8, and both indices are below 8.
  simp only [home, Fin.ext_iff] at same
  omega

/-- The first n store bodies write the first 64n output bytes. -/
theorem stores (s : State) (mask : ∀ l, s.vec (tmp 2) l = reverseLane l.val) (n : Nat) (hn : n ≤ 8) :
    let s' := exec ((List.range n).flatMap storeStep) s
    (∀ a, s'.mem a = if (s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 64 * n
      then outByte s.vec (a - (s.gpr out).toNat) else s.mem a) ∧
    s'.gpr = s.gpr ∧ s'.zf = s.zf ∧ (∀ k, n ≤ k → k < 8 → s'.vec (home k) = s.vec (home k)) ∧
    s'.vec (tmp 2) = s.vec (tmp 2) := by
  induction n with
  | zero =>
    simp only [List.range_zero, List.flatMap_nil, exec_nil]
    refine ⟨fun a => ?_, by trivial, by trivial, fun _ _ _ => by trivial, by trivial⟩
    rw [if_neg (by omega)]
  | succ n ih =>
    obtain ⟨mem, gpr, zf, homes, maskReg⟩ := ih (by omega)
    simp only [List.range_succ, List.flatMap_append, List.flatMap_singleton, exec_append]
    generalize hs' : exec ((List.range n).flatMap storeStep) s = s' at *
    simp only [storeStep, exec_cons, exec_nil]
    -- Register n, byte-reversed lane by lane, against the mask still in place.
    have reversed : ∀ l, ofBytes (shuffleBytes (s'.vec (home n)) (s'.vec (tmp 2))) l =
        bswap (s.vec (home n) l) := by
      intro l
      rw [shuffle_reverse _ _ l (by rw [maskReg]; exact mask l), homes n (by omega) (by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro a
      simp only [exec1, store, State.addr, assign, ↓reduceIte, gpr]
      by_cases inside : (s.gpr out).toNat + 64 * n ≤ a ∧ a < (s.gpr out).toNat + 64 * n + 64
      · simp only [inside, and_self, ↓reduceIte, show (s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 64 * (n + 1)
          by omega]
        simp only [outByte, laneByte]
        rw [show (a - (s.gpr out).toNat) / 64 = n by omega,
          show a - ((s.gpr out).toNat + 64 * n) = (a - (s.gpr out).toNat) % 64 by omega, reversed]
      · simp only [inside, ↓reduceIte, mem]
        by_cases before : (s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 64 * n
        · simp only [before, and_self, ↓reduceIte,
            show (s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 64 * (n + 1) by omega]
        · simp only [before, ↓reduceIte,
            show ¬ ((s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 64 * (n + 1)) by omega]
    · simp [exec1, gpr]
    · simp [exec1, zf]
    · intro k hk hk8
      simp only [exec1, assign]
      rw [if_neg (fun e => by have := home_inj k n hk8 (by omega) e; omega), homes k (by omega) hk8]
    · simp only [exec1, assign]
      rw [if_neg (home_ne_tmp n).symm, maskReg]

/-- The stores: the mask load, then one body per digest register. -/
theorem storeCode_eq : storeCode = .vload (tmp 2) (tableEntry bswapAvx512) :: (List.range 8).flatMap storeStep := rfl

/-- Byte m of a byte-reversed word, the least significant first, is byte m of the word, the most significant first. -/
private theorem bswap_byte (y : UInt32) (m : Nat) (hm : m < 4) :
    (bswap y >>> (8 * m).toUInt32).toUInt8 = (y >>> (24 - 8 * UInt32.ofNat m)).toUInt8 := by
  -- Each of the four byte positions is checked bit by bit.
  match m, hm with
  | 0, _ =>
    show (bswap y >>> (0 : UInt32)).toUInt8 = (y >>> (24 - 8 * (0 : UInt32))).toUInt8
    apply byte_ext
    simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
    simp [bswap]
  | 1, _ =>
    show (bswap y >>> (8 : UInt32)).toUInt8 = (y >>> (24 - 8 * (1 : UInt32))).toUInt8
    apply byte_ext
    simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
    simp [bswap]
  | 2, _ =>
    show (bswap y >>> (16 : UInt32)).toUInt8 = (y >>> (24 - 8 * (2 : UInt32))).toUInt8
    apply byte_ext
    simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
    simp [bswap]
  | 3, _ =>
    show (bswap y >>> (24 : UInt32)).toUInt8 = (y >>> (24 - 8 * (3 : UInt32))).toUInt8
    apply byte_ext
    simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
    simp [bswap]

/-- Byte k of the digest of a state. -/
private theorem digest_get (st : Vector UInt32 8) (k : Nat) (hk : k < 32) :
    (digest st).get! k = (st[k / 4]'(by omega) >>> (24 - 8 * UInt32.ofNat (k % 4))).toUInt8 := by
  -- The digest writes each word's bytes, the most significant first.
  rw [get!_eq _ _ (by simp [digest, ByteArray.size]; exact hk)]
  simp [digest, ByteArray.getElem_eq_getElem_data]

/-- After the transpose out, lane l of register k holds word l mod 8 of the state in lane 2k + l / 8. -/
theorem transposeOut_spec (s : State) (table : TableAt s.mem (s.gpr tbl).toNat) :
    (∀ k, (hk : k < 8) → ∀ l : Fin 16, (exec transposeOut s).vec (home k) l =
      s.vec (home (l.val % 8)) ⟨2 * k + l.val / 8, by omega⟩) ∧
    (exec transposeOut s).gpr = s.gpr ∧ (exec transposeOut s).mem = s.mem ∧ (exec transposeOut s).zf = s.zf := by
  -- The tracker's result, made sound for the machine, gives each lane's source.
  have moved := absExec_sound transposeOut transposeOut_moves s.vec Abs.start s (agrees_start s) table
  refine ⟨fun k hk l => ?_, moved.2.2.1, moved.2.1, moved.2.2.2⟩
  have sources := transposeOut_sources ⟨k, hk⟩ l
  rw [moved.1 _ _ (by simp only at sources; rw [sources]; simp), sources]
  rfl

/-- The mask load puts the byte-reversal indices in the temporary, and changes nothing else that matters. -/
theorem maskLoad_spec (s : State) (table : TableAt s.mem (s.gpr tbl).toNat) :
    (∀ l, (exec1 (.vload (tmp 2) (tableEntry bswapAvx512)) s).vec (tmp 2) l = reverseLane l.val) ∧
    (exec1 (.vload (tmp 2) (tableEntry bswapAvx512)) s).gpr = s.gpr ∧
    (exec1 (.vload (tmp 2) (tableEntry bswapAvx512)) s).mem = s.mem ∧
    (exec1 (.vload (tmp 2) (tableEntry bswapAvx512)) s).zf = s.zf ∧
    ∀ k, (exec1 (.vload (tmp 2) (tableEntry bswapAvx512)) s).vec (home k) = s.vec (home k) := by
  -- The mask's lanes are the table's row, and nothing but the temporary changes.
  refine ⟨fun l => ?_, rfl, rfl, rfl, fun k => ?_⟩
  · have := l.isLt
    simp only [exec1, assign, ↓reduceIte, State.addr, tableEntry]
    rw [show (s.gpr tbl).toNat + bswapAvx512 + 4 * l.val = (s.gpr tbl).toNat + 4 * (bswapAvx512 / 4 + l.val) by
        simp [bswapAvx512]; omega,
      readWord_table _ _ table _ (by simp [bswapAvx512, tableSize]; omega), bswapRow l]
  · simp only [exec1, assign]
    rw [if_neg (home_ne_tmp k)]

/-- After the transpose out and the stores, output bytes 32p to 32p + 31 are the digest of the state in lane p. -/
theorem epilogue (s : State) (table : TableAt s.mem (s.gpr tbl).toNat) :
    let s' := exec (transposeOut ++ storeCode) s
    (∀ p : Fin 16, ∀ k < 32, s'.mem ((s.gpr out).toNat + 32 * p.val + k) =
      (digest (Vector.ofFn fun j : Fin 8 => s.vec (home j.val) p)).get! k) ∧
    (∀ a, ¬ ((s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 512) → s'.mem a = s.mem a) ∧
    s'.gpr = s.gpr ∧ s'.zf = s.zf := by
  intro s'
  -- The transpose out moves lanes only, then the mask load reads the table.
  obtain ⟨homes, gpr1, mem1, zf1⟩ := transposeOut_spec s table
  obtain ⟨mask, gpr2, mem2, zf2, homes2⟩ := maskLoad_spec (exec transposeOut s) (by rw [gpr1, mem1]; exact table)
  obtain ⟨mem, gpr, zf, _, _⟩ := stores _ mask 8 (Nat.le_refl _)
  have whole : s' = exec ((List.range 8).flatMap storeStep) (exec1 (.vload (tmp 2) (tableEntry bswapAvx512))
      (exec transposeOut s)) := by
    show exec (transposeOut ++ storeCode) s = _
    rw [exec_append, storeCode_eq, exec_cons]
  rw [← whole] at mem gpr zf
  refine ⟨?_, ?_, gpr.trans (gpr2.trans gpr1), zf.trans (zf2.trans zf1)⟩
  · intro p k hk
    rw [mem, gpr2, gpr1, if_pos (by omega), digest_get _ _ hk, Vector.getElem_ofFn]
    -- Byte 32p + k sits in register p / 2, lane 8 (p mod 2) + k / 4.
    simp only [outByte, laneByte, laneOf, wordByte]
    rw [show (s.gpr out).toNat + 32 * p.val + k - (s.gpr out).toNat = 32 * p.val + k by omega,
      show (32 * p.val + k) / 64 = p.val / 2 by omega, show (32 * p.val + k) % 64 % 4 = k % 4 by omega,
      homes2, homes _ (by omega)]
    have lane : (32 * p.val + k) % 64 / 4 % 16 = 8 * (p.val % 2) + k / 4 := by omega
    simp only [lane, show (8 * (p.val % 2) + k / 4) % 8 = k / 4 by omega,
      show 2 * (p.val / 2) + (8 * (p.val % 2) + k / 4) / 8 = p.val by omega]
    exact bswap_byte _ _ (by omega)
  · intro a outside
    rw [mem, gpr2, gpr1, if_neg outside, mem2, mem1]

/-- The initial-state loads: register j holds word j of the initial state in every lane, and no other register changes. -/
theorem ivLoads_sources : ∀ r : Fin 32, ∀ l : Fin 16,
    absExec ((List.range 8).map fun j => .vload (home j) (tableEntry (ivAvx512 j))) Abs.start r l =
      if r.val < 8 then .const (initialState[r.val % 8]!) else .reg r l := by
  -- The tracker's result for every lane, checked by evaluation.
  decide +kernel

/-- The initial-state loads only read the table. -/
theorem ivLoads_moves : ((List.range 8).map fun j => Instr.vload (home j) (tableEntry (ivAvx512 j))).all Instr.moves = true := by
  -- Every load is checked by evaluation.
  decide +kernel

/-- After the initial-state loads, register j holds word j of the initial state in every lane. -/
theorem ivLoads (s : State) (table : TableAt s.mem (s.gpr tbl).toNat) :
    let s' := exec ((List.range 8).map fun j => .vload (home j) (tableEntry (ivAvx512 j))) s
    (∀ j < 8, ∀ l, s'.vec (home j) l = initialState[j]!) ∧
    (∀ r : Vreg, 8 ≤ r.val → s'.vec r = s.vec r) ∧
    s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.zf = s.zf := by
  intro s'
  -- The tracker's result, made sound for the machine, gives each register's contents.
  have moved := absExec_sound _ ivLoads_moves s.vec Abs.start s (agrees_start s) table
  refine ⟨fun j hj l => ?_, fun r hr => funext fun l => ?_, moved.2.2.1, moved.2.1, moved.2.2.2⟩
  · have sources := ivLoads_sources ⟨j, by omega⟩ l
    rw [if_pos hj] at sources
    have same : home j = ⟨j, by omega⟩ := by simp [home, Nat.mod_eq_of_lt hj]
    rw [same, moved.1 _ _ (by rw [sources]; simp), sources]
    simp only [Src.denote, Nat.mod_eq_of_lt hj]
  · have sources := ivLoads_sources r l
    simp only [show ¬ r.val < 8 by omega, ↓reduceIte] at sources
    rw [moved.1 _ _ (by rw [sources]; simp), sources]
    rfl

end Ssz.Native.Kernel.Avx512
