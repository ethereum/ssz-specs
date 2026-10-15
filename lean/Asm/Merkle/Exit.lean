import Asm.Merkle.LevelLoop

/-! The routine's exit: the root in the buffer's first chunk, the caller's registers restored. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Merkle

open Ssz.Asm.Sha256 (sp t0 t1 a0 a1 a2 savedSlots)

/-- Byte j of an eight-byte load is the byte at offset j. -/
theorem load8_byte {m : Machine} {c : BitVec 64} {j : Nat} (below : j < 8) :
    (m.load c 8 >>> (8 * j)).setWidth 8 = m.mem (c + BitVec.ofNat 64 j) := by
  simp only [Nat.lt_succ_iff_lt_or_eq] at below
  repeat' rcases below with below | rfl
  all_goals try (exfalso; omega)
  all_goals
    simp only [Machine.load]
    bitwise

/-- An address at a small offset lies outside a range at a non-overlapping offset of the same base. -/
theorem offset_outside {a : BitVec 64} {c c' n : Nat} (apart : c + 1 ≤ c' ∨ c' + n ≤ c)
    (small : c + 1 < 2 ^ 64 ∧ c' + n < 2 ^ 64) : ¬Within (a + BitVec.ofNat 64 c) (a + BitVec.ofNat 64 c') n := by
  have := disjoint_offsets (a := a) (c := c) (n := 1) (c' := c') (n' := n) apart small
    (a + BitVec.ofNat 64 c) (by simp [Within])
  exact this

/-- The first n words of a 32-byte copy between two ranges that share no byte. -/
theorem copy_upto {M : Machine} {src dst : BitVec 64} (from_ : M.read t2 = src) (to_ : M.read a5 = dst)
    (apart : Disjoint src 32 dst 32) :
    ∀ n, n ≤ 4 →
      let M' := execBlock ((List.range n).flatMap copyWord) M
      (∀ b, b < 8 * n → M'.mem (dst + BitVec.ofNat 64 b) = M.mem (src + BitVec.ofNat 64 b)) ∧
        (∀ y, ¬Within y dst (8 * n) → M'.mem y = M.mem y) ∧ ∀ x, x ≠ t0 → M'.read x = M.read x
  | 0, _ => ⟨fun _ below => absurd below (by omega), fun _ _ => rfl, fun _ _ => rfl⟩
  | n + 1, bound => by
    intro M'
    obtain ⟨copied, mem, frame⟩ := copy_upto from_ to_ apart n (by omega)
    simp only [M', List.range_succ, List.flatMap_append, List.flatMap_singleton, execBlock_append]
    generalize execBlock ((List.range n).flatMap copyWord) M = Mn at copied mem frame
    simp (disch := decide) only [copyWord, execBlock_cons, execBlock_nil, Instr.run,
      Machine.read_write_self, Machine.read_write_ne, frame t2 (by decide), frame a5 (by decide),
      from_, to_, slot, signExtend_ofNat12 (show 8 * n < 2048 by omega)]
    -- The source word is still the original, since the copy so far wrote only the destination.
    have source (j : Nat) (below : j < 8) :
        Mn.mem (src + BitVec.ofNat 64 (8 * n) + BitVec.ofNat 64 j) =
          M.mem (src + BitVec.ofNat 64 (8 * n) + BitVec.ofNat 64 j) := by
      apply mem
      intro within
      apply apart _ _ (within_mono within (by omega))
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, within_offset (by omega)]
      omega
    refine ⟨fun b below => ?_, fun y outside => ?_, fun x xt => ?_⟩
    · by_cases old : b < 8 * n
      · rw [Machine.mem_store_of_not_within (offset_outside (by omega) (by omega)), Machine.mem_write]
        exact copied b old
      · -- Byte b is byte b - 8n of this word.
        have shift : dst + BitVec.ofNat 64 b = dst + BitVec.ofNat 64 (8 * n) + BitVec.ofNat 64 (b - 8 * n) := by
          rw [BitVec.add_assoc, ← BitVec.ofNat_add]
          congr 2
          omega
        rw [shift, Machine.mem_store_inside (by omega) (by omega), load8_byte (by omega),
          source _ (by omega), BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * n + (b - 8 * n) = b by omega]
    · rw [Machine.mem_store_of_not_within fun within => outside (within_sub within (by omega) (by omega)),
        Machine.mem_write]
      exact mem y fun within => outside (within_mono within (by omega))
    · rw [Machine.read_store, Machine.read_write_ne xt]
      exact frame x xt

theorem finishCode_straight_prefix :
    ∀ i ∈ reloads sp savedSlots ++ [Instr.addi sp sp (slot frameSize)], i.straight := by
  decide

theorem fetch_finishBody {k : Nat}
    (within : k < (reloads sp savedSlots ++ [Instr.addi sp sp (slot frameSize)]).length) :
    program[finish + k]? = some (reloads sp savedSlots ++ [Instr.addi sp sp (slot frameSize)])[k] := by
  have := fetch_slice (fun k within => fetch_finish within) 0
    (reloads sp savedSlots ++ [Instr.addi sp sp (slot frameSize)]) rfl (by decide) k within
  rwa [Nat.add_zero] at this

/-- Restore the saved registers, close the frame, and return. -/
theorem finish_reaches {m0 M : Machine} (steady : Steady m0 M) :
    Reaches program ⟨M, finish⟩ fun s =>
      returned program s ∧ s.m.mem = M.mem ∧ ∀ r ∈ Sha256.preserved, s.m.read r = m0.read r := by
  refine Reaches.run (start := finish) (n := 14) (reloads sp savedSlots ++ [Instr.addi sp sp (slot frameSize)])
    (by simp [reloads, savedSlots]) (fun k within => fetch_finishBody within) finishCode_straight_prefix ?_
  refine Reaches.now ⟨?_, ?_, ?_⟩
  · show program[finish + 14]? = some .ret
    exact fetch_finish (k := 14) (by decide)
  · simp only [execBlock_append, execBlock_cons, execBlock_nil, Instr.run, Machine.mem_write]
    exact (reloads_spec (base := sp) (by decide) (by decide) (by decide)).1
  · obtain ⟨_, loaded, kept⟩ := reloads_spec (base := sp) (slots := savedSlots) (m := M)
      (by decide) (by decide) (by decide)
    intro r inside
    simp only [execBlock_append, execBlock_cons, execBlock_nil, Instr.run]
    have savedReg (s : Reg × Nat) (mem : s ∈ savedSlots) (other : s.1 ≠ sp) :
        (execBlock (reloads sp savedSlots) M).read s.1 = m0.read s.1 := by
      rw [loaded s mem, steady.stack]
      exact steady.savedStored s mem
    by_cases isSp : r = sp
    · subst isSp
      rw [Machine.read_write_self (by decide), kept sp (by decide), steady.stack,
        show (slot frameSize).signExtend 64 = BitVec.ofNat 64 frameSize by decide, base,
        BitVec.sub_add_cancel]
    rw [Machine.read_write_ne isSp]
    by_cases isGp : r = 3
    · subst isGp
      rw [kept 3 (by decide), steady.globalPointer]
    by_cases isTp : r = 4
    · subst isTp
      rw [kept 4 (by decide), steady.threadPointer]
    -- Every other preserved register has a slot of its own.
    have saved : r ∈ savedSlots.map Prod.fst := by
      revert inside isSp isGp isTp
      revert r
      decide
    obtain ⟨s, mem, rfl⟩ := List.mem_map.mp saved
    exact savedReg s mem isSp

end Ssz.Asm.Merkle
