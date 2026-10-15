import Asm.Sha256.PairRounds
import Asm.Sha256.Proof

/-! The pair hash, read against the specification's node combination. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Sha256

open Ssz.Sha256 (Spec.State Spec.rounds Spec.compression Spec.inputWord Spec.inputWords
  Spec.messageWord Spec.addState Spec.initial Spec.digest)

/-- Message word k of the pair: the first eight from the left node, the rest from the right. -/
def pairWord (m : Machine) (k : Nat) : BitVec 32 :=
  if k < 8 then Spec.inputWord (m.bytes (m.read a1) 32) (4 * k)
  else Spec.inputWord (m.bytes (m.read a2) 32) (4 * (k - 8))

theorem stateHome_eq (j : Nat) (small : j < 8) : stateHome j = wordHome 0 j := by
  simp [stateHome, wordHome, Nat.mod_eq_of_lt small]

theorem ringSlot_ne_a2 (k : Nat) : ringSlot k ≠ a2 := by
  -- The right node's address arrives in the first state home.
  have : wordHome 0 0 = a2 := by decide
  rw [← this]
  exact Ne.symm (wordHome_ne 0 0 k 0).1

/-- The first n message words of the pair, each in its ring slot. -/
theorem loadPair_upto {m : Machine} :
    ∀ n, n ≤ 16 →
      let m' := execBlock ((List.range n).flatMap loadPairWord) m
      (∀ k, k < n → Holds m' (ringSlot k) (pairWord m k)) ∧ m'.mem = m.mem ∧
        ∀ x, x ∉ wordRegs.toList → x ≠ t0 → m'.read x = m.read x
  | 0, _ => by simp
  | n + 1, bound => by
    intro m'
    obtain ⟨loaded, mem, frame⟩ := loadPair_upto n (by omega)
    simp only [m', List.range_succ, List.flatMap_append, List.flatMap_singleton, execBlock_append]
    generalize execBlock ((List.range n).flatMap loadPairWord) m = mn at loaded mem frame
    -- Both node addresses and both nodes' bytes are as they were on entry.
    have left : mn.read a1 = m.read a1 := frame a1 (by decide) (by decide)
    have right : mn.read a2 = m.read a2 := frame a2 (by decide) (by decide)
    have bytes (base : BitVec 64) : mn.bytes base 32 = m.bytes base 32 := by
      simp [Machine.bytes, mem]
    have fresh : Holds (execBlock (loadPairWord n) mn) (ringSlot n) (pairWord m n) ∧
        (execBlock (loadPairWord n) mn).mem = mn.mem ∧
        ∀ x, x ≠ ringSlot n → x ≠ t0 → (execBlock (loadPairWord n) mn).read x = mn.read x := by
      by_cases low : n < 8
      · simp only [loadPairWord, if_pos low, pairWord]
        have := loadWordFrom_spec (m := mn) (k := n) (base := a1) (start := 4 * n) (size := 32)
          (ringSlot_ne n 0).1 (by decide) (by omega) (by omega)
        rwa [left, bytes] at this
      · simp only [loadPairWord, if_neg low, pairWord]
        have := loadWordFrom_spec (m := mn) (k := n) (base := a2) (start := 4 * (n - 8)) (size := 32)
          (ringSlot_ne_a2 n) (by decide) (by omega) (by omega)
        rwa [right, bytes] at this
    obtain ⟨word, mem', frame'⟩ := fresh
    refine ⟨fun k below => ?_, mem'.trans mem, fun x outside xt => ?_⟩
    · by_cases now : k = n
      · subst now
        exact word
      · rw [Holds, frame' _ (ringSlot_ne_ringSlot (by omega)) (ringSlot_ne k 0).2.1]
        exact loaded k (by omega)
    · have : x ≠ ringSlot n := by
        rintro rfl
        exact outside (by simp [ringSlot, Vector.getElem_mem])
      rw [frame' x this xt, frame x outside xt]

/-- Two immediates rebuild a constant in a register, sign-extended. -/
theorem immediates_spec {m : Machine} {r : Reg} {k : BitVec 32} (nonzero : (0 : Reg) ≠ r)
    (rebuilds : Rebuilds k) :
    execBlock [.lui r (upper k), .addiw r r (lower k)] m = m.write r (k.signExtend 64) := by
  simp only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self' nonzero,
    Machine.write_write_same, sext32_eq rebuilds]

theorem iv_rebuilds : ∀ j, j < 8 → Rebuilds (ivWord j) := by
  unfold Rebuilds
  decide

/-- The first n initial words, each in its home. -/
theorem iv_upto {m : Machine} :
    ∀ n, n ≤ 8 →
      let m' := execBlock ((List.range n).flatMap ivWordCode) m
      (∀ j, j < n → Holds m' (stateHome j) (ivWord j)) ∧ m'.mem = m.mem ∧
        ∀ x, x ∉ stateRegs.toList → m'.read x = m.read x
  | 0, _ => by simp
  | n + 1, bound => by
    intro m'
    obtain ⟨built, mem, frame⟩ := iv_upto n (by omega)
    simp only [m', List.range_succ, List.flatMap_append, List.flatMap_singleton, execBlock_append]
    generalize execBlock ((List.range n).flatMap ivWordCode) m = mn at built mem frame
    rw [ivWordCode, immediates_spec (by rw [stateHome_eq n (by omega)]; exact (nonzero 0 n 0 0).1)
      (iv_rebuilds n (by omega))]
    refine ⟨fun j below => ?_, mem, fun x outside => ?_⟩
    · by_cases now : j = n
      · subst now
        exact Machine.read_write_self (by rw [stateHome_eq j (by omega)]; exact (nonzero 0 j 0 0).1.symm)
      · rw [Holds, Machine.read_write_ne (by
          rw [stateHome_eq j (by omega), stateHome_eq n (by omega)]
          exact wordHome_ne_wordHome (by omega) (by omega) now)]
        exact built j (by omega)
    · have : x ≠ stateHome n := by
        rintro rfl
        exact outside (by simp [stateHome, Vector.getElem_mem])
      rw [Machine.read_write_ne this, frame x outside]

theorem stateHome_ne (j : Nat) (small : j < 8) :
    (0 : Reg) ≠ stateHome j ∧ stateHome j ≠ t0 ∧ stateHome j ≠ t1 := by
  rw [stateHome_eq j small]
  exact ⟨(nonzero 0 j 0 0).1, (wordHome_ne 0 j 0 0).2.2.1, (wordHome_ne 0 j 0 0).2.2.2⟩

theorem stateHome_ne_stateHome {j j' : Nat} (small : j < 8) (small' : j' < 8) (apart : j ≠ j') :
    stateHome j ≠ stateHome j' := by
  rw [stateHome_eq j small, stateHome_eq j' small']
  exact wordHome_ne_wordHome small small' apart

theorem not_stateHome {x : Reg} (outside : x ∉ stateRegs.toList) (j : Nat) : x ≠ stateHome j := by
  rintro rfl
  exact outside (by simp [stateHome, Vector.getElem_mem])

/--
The first n words of a feed-forward, where word j adds a value to its home.

The added value comes from a block that leaves memory alone and writes only the home and t0.
-/
theorem forward_upto {code : Nat → List Instr} {m : Machine} {work add : Nat → BitVec 32}
    (step : ∀ j (mj : Machine), j < 8 → (∀ i, i < 8 → j ≤ i → Holds mj (stateHome i) (work i)) →
      (∀ x, x ∉ stateRegs.toList → x ≠ t0 → mj.read x = m.read x) →
      Holds (execBlock (code j) mj) (stateHome j) (work j + add j) ∧
        (execBlock (code j) mj).mem = mj.mem ∧
        ∀ x, x ≠ stateHome j → x ≠ t0 → (execBlock (code j) mj).read x = mj.read x)
    (working : ∀ j, j < 8 → Holds m (stateHome j) (work j)) :
    ∀ n, n ≤ 8 →
      let m' := execBlock ((List.range n).flatMap code) m
      (∀ j, j < n → Holds m' (stateHome j) (work j + add j)) ∧
        (∀ j, j < 8 → n ≤ j → Holds m' (stateHome j) (work j)) ∧ m'.mem = m.mem ∧
        ∀ x, x ∉ stateRegs.toList → x ≠ t0 → m'.read x = m.read x
  | 0, _ => ⟨fun _ below => absurd below (Nat.not_lt_zero _), fun j small _ => working j small, rfl,
      fun _ _ _ => rfl⟩
  | n + 1, bound => by
    intro m'
    obtain ⟨done, waiting, mem, frame⟩ := forward_upto step working n (by omega)
    simp only [m', List.range_succ, List.flatMap_append, List.flatMap_singleton, execBlock_append]
    generalize execBlock ((List.range n).flatMap code) m = mn at done waiting mem frame
    obtain ⟨fresh, mem', frame'⟩ := step n mn (by omega) waiting frame
    have ne (j : Nat) (small : j < 8) (apart : j ≠ n) : stateHome j ≠ stateHome n :=
      stateHome_ne_stateHome small (by omega) apart
    refine ⟨fun j below => ?_, fun j small above => ?_, mem'.trans mem, fun x outside xt => ?_⟩
    · by_cases now : j = n
      · subst now
        exact fresh
      · rw [Holds, frame' _ (ne j (by omega) now) (stateHome_ne j (by omega)).2.1]
        exact done j (by omega)
    · rw [Holds, frame' _ (ne j small (by omega)) (stateHome_ne j small).2.1]
      exact waiting j small (by omega)
    · rw [frame' x (not_stateHome outside n) xt, frame x outside xt]

theorem ivForward_word (j : Nat) (mj : Machine) (small : j < 8) {w : BitVec 32}
    (held : Holds mj (stateHome j) w) :
    Holds (execBlock (ivForwardWord j) mj) (stateHome j) (w + ivWord j) ∧
      (execBlock (ivForwardWord j) mj).mem = mj.mem ∧
      ∀ x, x ≠ stateHome j → x ≠ t0 → (execBlock (ivForwardWord j) mj).read x = mj.read x := by
  obtain ⟨z, s0, -⟩ := stateHome_ne j small
  have rebuilt := immediates_spec (m := mj) (r := t0) (by decide) (iv_rebuilds j small)
  simp only [ivForwardWord]
  rw [show [Instr.lui t0 (upper (ivWord j)), .addiw t0 t0 (lower (ivWord j)),
      .addw (stateHome j) (stateHome j) t0] =
      [Instr.lui t0 (upper (ivWord j)), .addiw t0 t0 (lower (ivWord j))] ++
        [.addw (stateHome j) (stateHome j) t0] from rfl, execBlock_append, rebuilt]
  simp only [execBlock_cons, execBlock_nil, Instr.run]
  refine ⟨?_, rfl, fun x xs xt => ?_⟩
  · rw [Holds, Machine.read_write_self z.symm, Machine.read_write_ne s0, Machine.read_write_self (by decide)]
    simp only [Holds] at held
    rw [held]
    apply sext32_eq
    simp only [setWidth_add32, setWidth_signExtend32]
  · rw [Machine.read_write_ne xs, Machine.read_write_ne xt]

theorem keptForward_word (j : Nat) (mj : Machine) (small : j < 8) {w kept : BitVec 32}
    (held : Holds mj (stateHome j) w) (stash : Holds mj (ringSlot j) kept) :
    Holds (execBlock [keptForwardWord j] mj) (stateHome j) (w + kept) ∧
      (execBlock [keptForwardWord j] mj).mem = mj.mem ∧
      ∀ x, x ≠ stateHome j → x ≠ t0 → (execBlock [keptForwardWord j] mj).read x = mj.read x := by
  obtain ⟨z, -, -⟩ := stateHome_ne j small
  simp only [keptForwardWord, execBlock_cons, execBlock_nil, Instr.run]
  refine ⟨?_, rfl, fun x xs _ => Machine.read_write_ne xs⟩
  rw [Holds, Machine.read_write_self z.symm]
  simp only [Holds] at held stash
  rw [held, stash]
  apply sext32_eq
  simp only [setWidth_add32, setWidth_signExtend32]

theorem ringSlot_not_state_mem {n : Nat} (inside : stateHome n ∈ wordRegs.toList) : False := by
  -- No home is in the ring.
  have all : ∀ a (_ : a < 8), stateRegs[a] ∉ wordRegs.toList := by decide
  exact all (n % 8) (Nat.mod_lt _ (by decide)) inside

/-- The first n chaining words copied into the first n ring slots. -/
theorem keep_upto {m : Machine} {chain : Nat → BitVec 32}
    (held : ∀ j, j < 8 → Holds m (stateHome j) (chain j)) :
    ∀ n, n ≤ 8 →
      let m' := execBlock ((List.range n).map keepWord) m
      (∀ j, j < n → Holds m' (ringSlot j) (chain j)) ∧ m'.mem = m.mem ∧
        ∀ x, x ∉ wordRegs.toList → m'.read x = m.read x
  | 0, _ => by simp
  | n + 1, bound => by
    intro m'
    obtain ⟨copied, mem, frame⟩ := keep_upto held n (by omega)
    simp only [m', List.range_succ, List.map_append, List.map_cons, List.map_nil, execBlock_append,
      execBlock_cons, execBlock_nil, keepWord, Instr.run]
    generalize execBlock ((List.range n).map keepWord) m = mn at copied mem frame
    -- A home is not a ring slot, so the copies so far left every home alone.
    have home : mn.read (stateHome n) = (chain n).signExtend 64 := by
      rw [frame _ (fun inside => ringSlot_not_state_mem inside)]
      exact held n (by omega)
    refine ⟨fun j below => ?_, mem, fun x outside => ?_⟩
    · by_cases now : j = n
      · subst now
        rw [Holds, Machine.read_write_self (nonzero 0 0 j 0).2.1.symm, home]
        simp
      · rw [Holds, Machine.read_write_ne (ringSlot_ne_ringSlot (by omega))]
        exact copied j (by omega)
    · have : x ≠ ringSlot n := by
        rintro rfl
        exact outside (by simp [ringSlot, Vector.getElem_mem])
      rw [Machine.read_write_ne this, frame x outside]

/-- Byte b of a word in big-endian order, most significant first. -/
def digestByte (w : BitVec 32) (b : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (w.toNat / 2 ^ (24 - 8 * b))

theorem storedByte_shift (w : BitVec 32) (s : Nat) :
    ((w >>> s).signExtend 64).setWidth 8 = BitVec.ofNat 8 (w.toNat / 2 ^ s) := by
  -- The low byte of a sign-extended word is the low byte of the word.
  have low : ((w >>> s).signExtend 64).setWidth 8 = (w >>> s).setWidth 8 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_signExtend, BitVec.getElem_signExtend, hi, show i < 32 by omega,
      show i < 64 by omega]
  rw [low]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem storedByte_self (w : BitVec 32) :
    (w.signExtend 64).setWidth 8 = BitVec.ofNat 8 (w.toNat / 2 ^ 0) := by
  have := storedByte_shift w 0
  simpa using this

/-- A one-byte store changes exactly one address. -/
theorem Machine.mem_store1 {m : Machine} {a x v : BitVec 64} :
    (m.store a 1 v).mem x = if x = a then v.setWidth 8 else m.mem x := by
  simp only [Machine.store]
  by_cases same : x = a
  · subst same
    rw [if_pos (by simp), if_pos rfl, BitVec.sub_self, BitVec.toNat_zero, Nat.mul_zero,
      BitVec.ushiftRight_zero]
  · have : ¬(x - a).toNat < 1 := by
      intro below
      apply same
      have zero : x - a = 0 := BitVec.eq_of_toNat_eq (by simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]; omega)
      bv_omega
    rw [if_neg this, if_neg same]

/-- What the digest code of one word does, instruction by instruction. -/
theorem digestWord_eq (j : Nat) (mj : Machine) (small : j < 8) :
    let w := mj.read (stateHome j)
    let out := mj.read t1
    let addr := fun (b : Nat) => out + BitVec.ofNat 64 (4 * j + b)
    let shifted := fun (s : Nat) => ((w.setWidth 32 >>> s).signExtend 64)
    execBlock (digestWord j) mj =
      ((((((mj.write t0 (shifted 24)).store (addr 0) 1 (shifted 24)).write t0 (shifted 16)).store
        (addr 1) 1 (shifted 16)).write t0 (shifted 8)).store (addr 2) 1 (shifted 8)).store (addr 3) 1 w := by
  intro w out addr shifted
  obtain ⟨z, s0, s1⟩ := stateHome_ne j small
  have address (b : Nat) (below : b < 4) :
      (BitVec.ofNat 12 (4 * j + b)).signExtend 64 = BitVec.ofNat 64 (4 * j + b) :=
    signExtend_ofNat12 (by omega)
  simp only [digestWord, execBlock_cons, execBlock_nil, Instr.run]
  simp only [Machine.read_store, Machine.read_write_self (show t0 ≠ 0 by decide),
    Machine.read_write_ne s0, Machine.read_write_ne (show t1 ≠ t0 by decide), Nat.reduceMod,
    address 0 (by omega), address 1 (by omega), address 2 (by omega), address 3 (by omega)]
  rfl

theorem offset_eq_iff {a : BitVec 64} {i j : Nat} (small : i < 2 ^ 64) (small' : j < 2 ^ 64) :
    a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 j ↔ i = j := by
  constructor
  · intro same
    have := congrArg BitVec.toNat same
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    omega
  · rintro rfl
    rfl

/-- The first n digest words, stored big-endian from an address. -/
theorem digest_upto {m : Machine} {out : BitVec 64} {chain : Nat → BitVec 32}
    (base : m.read t1 = out) (held : ∀ j, j < 8 → Holds m (stateHome j) (chain j)) :
    ∀ n, n ≤ 8 →
      let m' := execBlock ((List.range n).flatMap digestWord) m
      (∀ k, k < 4 * n → m'.mem (out + BitVec.ofNat 64 k) = digestByte (chain (k / 4)) (k % 4)) ∧
        (∀ y, ¬Within y out (4 * n) → m'.mem y = m.mem y) ∧
        ∀ x, x ≠ t0 → m'.read x = m.read x
  | 0, _ => ⟨fun _ below => absurd below (by omega), fun _ _ => rfl, fun _ _ => rfl⟩
  | n + 1, bound => by
    intro m'
    obtain ⟨written, mem, frame⟩ := digest_upto base held n (by omega)
    simp only [m', List.range_succ, List.flatMap_append, List.flatMap_singleton, execBlock_append]
    generalize execBlock ((List.range n).flatMap digestWord) m = mn at written mem frame
    rw [digestWord_eq n mn (by omega)]
    have baseN : mn.read t1 = out := by rw [frame t1 (by decide), base]
    have word : mn.read (stateHome n) = (chain n).signExtend 64 := by
      rw [frame _ (stateHome_ne n (by omega)).2.1]
      exact held n (by omega)
    simp only [baseN, word, Machine.mem_store1, Machine.mem_write, setWidth_signExtend32]
    refine ⟨fun k below => ?_, fun y outside => ?_, fun x xt => ?_⟩
    · by_cases old : k < 4 * n
      · -- An earlier byte sits below this word's four addresses.
        rw [if_neg (by rw [offset_eq_iff (by omega) (by omega)]; omega),
          if_neg (by rw [offset_eq_iff (by omega) (by omega)]; omega),
          if_neg (by rw [offset_eq_iff (by omega) (by omega)]; omega),
          if_neg (by rw [offset_eq_iff (by omega) (by omega)]; omega)]
        exact written k old
      · -- This word's bytes, most significant first.
        have quotient : k / 4 = n := by omega
        rw [quotient]
        have ne (b b' : Nat) (lb : b < 4) (lb' : b' < 4) (apart : b ≠ b') :
            out + BitVec.ofNat 64 (4 * n + b) ≠ out + BitVec.ofNat 64 (4 * n + b') := by
          rw [Ne, offset_eq_iff (by omega) (by omega)]
          omega
        have : k = 4 * n + 0 ∨ k = 4 * n + 1 ∨ k = 4 * n + 2 ∨ k = 4 * n + 3 := by omega
        rcases this with h | h | h | h <;> subst h
        · rw [if_neg (ne 0 3 (by omega) (by omega) (by omega)),
            if_neg (ne 0 2 (by omega) (by omega) (by omega)),
            if_neg (ne 0 1 (by omega) (by omega) (by omega)), if_pos rfl, storedByte_shift,
            show (4 * n + 0) % 4 = 0 by omega]
          rfl
        · rw [if_neg (ne 1 3 (by omega) (by omega) (by omega)),
            if_neg (ne 1 2 (by omega) (by omega) (by omega)), if_pos rfl, storedByte_shift,
            show (4 * n + 1) % 4 = 1 by omega]
          rfl
        · rw [if_neg (ne 2 3 (by omega) (by omega) (by omega)), if_pos rfl, storedByte_shift,
            show (4 * n + 2) % 4 = 2 by omega]
          rfl
        · rw [if_pos rfl, storedByte_self, show (4 * n + 3) % 4 = 3 by omega]
          rfl
    · -- An address outside the written range is none of these four.
      have far (b : Nat) (lb : b < 4) : y ≠ out + BitVec.ofNat 64 (4 * n + b) := by
        rintro rfl
        exact outside ((within_offset (by omega)).mpr (by omega))
      rw [if_neg (far 3 (by omega)), if_neg (far 2 (by omega)), if_neg (far 1 (by omega)),
        if_neg (far 0 (by omega))]
      exact mem y fun inside => outside (within_mono inside (by omega))
    · simp only [Machine.read_store, Machine.read_write_ne xt]
      exact frame x xt

theorem stateWord_addState {a b : Spec.State} {j : Nat} (small : j < 8) :
    stateWord (Spec.addState a b) j = stateWord a j + stateWord b j := by
  simp only [Nat.lt_succ_iff_lt_or_eq] at small
  repeat' rcases small with small | rfl
  all_goals try (exfalso; omega)
  all_goals rfl

/-- After the padding block's rounds every working word is back in its round-zero home. -/
theorem homes_of_fused {init : Spec.State} {m0 m : Machine} (inv : FusedInv init m0 64 (by omega) m) :
    ∀ j, j < 8 → Holds m (stateHome j) (stateWord (Spec.rounds padWords init 64 (by omega)) j) := by
  intro j small
  rw [stateHome_eq j small, show wordHome 0 j = wordHome 64 j by simp [wordHome]]
  simp only [Nat.lt_succ_iff_lt_or_eq] at small
  repeat' rcases small with small | rfl
  all_goals try (exfalso; omega)
  all_goals
    first
    | exact inv.a | exact inv.b | exact inv.c | exact inv.d
    | exact inv.e | exact inv.f | exact inv.g | exact inv.h

/-- After sixty-four rounds every working word is back in its round-zero home. -/
theorem homes_of_inv {input : Vector (BitVec 32) 16} {init : Spec.State} {m0 m : Machine}
    (inv : RoundsInv input init m0 64 (by omega) m) :
    ∀ j, j < 8 → Holds m (stateHome j) (stateWord (Spec.rounds input init 64 (by omega)) j) := by
  intro j small
  rw [stateHome_eq j small, show wordHome 0 j = wordHome 64 j by simp [wordHome]]
  simp only [Nat.lt_succ_iff_lt_or_eq] at small
  repeat' rcases small with small | rfl
  all_goals try (exfalso; omega)
  all_goals
    first
    | exact inv.a | exact inv.b | exact inv.c | exact inv.d
    | exact inv.e | exact inv.f | exact inv.g | exact inv.h

end Ssz.Asm.Sha256
