import Asm.Merkle.PairLoop

/-! The level loop: fold a level into the one above it, until the top or an empty level. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Merkle

open Ssz.Asm.Sha256 (sp t0 t1 a0 a1 a2 savedSlots pairCode workRegs)

theorem AtPair.write {m0 m : Machine} {k i : Nat} (state : AtPair m0 k i m) {r : Reg} {v : BitVec 64}
    (notSp : r ≠ sp) (notGp : r ≠ 3) (notTp : r ≠ 4) : AtPair m0 k i (m.write r v) where
  steady := state.steady.write notSp notGp notTp
  below := state.below
  nonempty := state.nonempty
  progress := state.progress
  countStored := by rw [Machine.load_write]; exact state.countStored
  heightStored := by rw [Machine.load_write]; exact state.heightStored
  pairStored := by rw [Machine.load_write]; exact state.pairStored
  parents := fun j within => by rw [chunkAt_write]; exact state.parents j within
  children := fun j above within => by rw [chunkAt_write]; exact state.children j above within

/-- With every pair hashed, the loop leaves for the level's end. -/
theorem pair_exit {m0 m : Machine} {k i : Nat} (valid : Valid m0) (state : AtPair m0 k i m)
    (finished : ((level (leaves m0) k).length + 1) / 2 ≤ i) :
    Reaches program ⟨m, pairHead⟩ fun s => s.pc = levelEnd ∧ AtPair m0 k i s.m := by
  have steady := state.steady
  have bounds := width_le m0 k
  have small := valid.small
  have progress := state.progress
  have readPair : m.load (m.read sp + (slot pairSlot).signExtend 64) 8 = BitVec.ofNat 64 i := by
    rw [steady.stack, slot_ext (by decide), state.pairStored]
  have readCount : m.load (m.read sp + (slot countSlot).signExtend 64) 8 =
      BitVec.ofNat 64 (level (leaves m0) k).length := by
    rw [steady.stack, slot_ext (by decide), state.countStored]
  refine Reaches.run (start := pairHead) (n := 4)
    [.ld t0 sp (slot pairSlot), .ld a4 sp (slot countSlot), .addi t1 a4 (slot 1), .srli t1 t1 1] rfl
    (fetch_slice (fun k within => fetch_pairHead within) 0 _ rfl (by decide)) (by decide) ?_
  simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self,
    Machine.read_write_ne, Machine.load_write, readPair, readCount, slot_ext (show 1 < 2048 by decide),
    ← BitVec.ofNat_add, ofNat_half (show (level (leaves m0) k).length + 1 < 2 ^ 64 by omega)]
  refine Reaches.exec (fetch_one (fun k within => fetch_pairHead within) 4 (by decide)) ?_
  simp (disch := decide) only [List.getElem_cons_succ, List.getElem_cons_zero, pairHeadCode,
    Instr.run, Instr.next, Machine.read_write_self, Machine.read_write_ne,
    ofNat_lt_iff (show i < 2 ^ 64 by omega) (show ((level (leaves m0) k).length + 1) / 2 < 2 ^ 64 by omega),
    show ¬i < ((level (leaves m0) k).length + 1) / 2 by omega, if_false]
  exact Reaches.now ⟨rfl, ((((state.write (by decide) (by decide) (by decide)).write (by decide)
    (by decide) (by decide)).write (by decide) (by decide) (by decide)).write (by decide) (by decide)
    (by decide))⟩

/-- The whole pair loop of a level, from any pair onward. -/
theorem pair_loop {m0 : Machine} {k : Nat} (valid : Valid m0) :
    ∀ r i m, ((level (leaves m0) k).length + 1) / 2 - i = r → AtPair m0 k i m →
      Reaches program ⟨m, pairHead⟩ fun s =>
        s.pc = levelEnd ∧ AtPair m0 k (((level (leaves m0) k).length + 1) / 2) s.m := by
  intro r
  induction r with
  | zero =>
    intro i m left state
    have done : i = ((level (leaves m0) k).length + 1) / 2 := by have := state.progress; omega
    subst done
    exact pair_exit valid state (Nat.le_refl _)
  | succ r ih =>
    intro i m left state
    exact (pair_step valid state (by omega)).bind fun s ⟨pc, next⟩ => by
      rw [show s = ⟨s.m, pairHead⟩ by rw [← pc]]
      exact ih (i + 1) s.m (by omega) next

theorem AtLevel.write {m0 m : Machine} {k : Nat} (state : AtLevel m0 k m) {r : Reg} {v : BitVec 64}
    (notSp : r ≠ sp) (notGp : r ≠ 3) (notTp : r ≠ 4) : AtLevel m0 k (m.write r v) where
  steady := state.steady.write notSp notGp notTp
  height := state.height
  countStored := by rw [Machine.load_write]; exact state.countStored
  heightStored := by rw [Machine.load_write]; exact state.heightStored
  chunks := fun j within => by rw [chunkAt_write]; exact state.chunks j within

/-- The level loop has stopped: either every level is folded, or the level is empty. -/
structure AtDone (m0 : Machine) (k : Nat) (m : Machine) : Prop where
  /-- The level reached is in the buffer. -/
  reached : AtLevel m0 k m
  /-- Nothing is left to fold. -/
  top : k = depth m0 ∨ (level (leaves m0) k).length = 0

/-- The end of a level: the parents become the level, one height up. -/
theorem level_end {m0 m : Machine} {k : Nat} (valid : Valid m0)
    (state : AtPair m0 k (((level (leaves m0) k).length + 1) / 2) m) :
    Reaches program ⟨m, levelEnd⟩ fun s => s.pc = levelHead ∧ AtLevel m0 (k + 1) s.m := by
  have steady := state.steady
  have bounds := width_le m0 k
  have small := valid.small
  have below := state.below
  have readCount : m.load (m.read sp + (slot countSlot).signExtend 64) 8 =
      BitVec.ofNat 64 (level (leaves m0) k).length := by
    rw [steady.stack, slot_ext (by decide), state.countStored]
  refine Reaches.run (start := levelEnd) (n := 7)
    [.ld a4 sp (slot countSlot), .addi a4 a4 (slot 1), .srli a4 a4 1, .sd a4 sp (slot countSlot),
      .ld t0 sp (slot heightSlot), .addi t0 t0 (slot 1), .sd t0 sp (slot heightSlot)] rfl
    (fetch_slice (fun k within => fetch_levelEnd within) 0 _ rfl (by decide)) (by decide) ?_
  simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self,
    Machine.read_write_ne, Machine.load_write, Machine.read_store, steady.stack, state.countStored,
    slot_ext (show 1 < 2048 by decide), slot_ext (show countSlot < 2048 by decide),
    slot_ext (show heightSlot < 2048 by decide), ← BitVec.ofNat_add,
    ofNat_half (show (level (leaves m0) k).length + 1 < 2 ^ 64 by omega)]
  -- The count slot now holds the parents' count, and the height slot holds k + 1.
  generalize hm1 : (((m.write a4 (BitVec.ofNat 64 (level (leaves m0) k).length)).write a4
    (BitVec.ofNat 64 ((level (leaves m0) k).length + 1))).write a4
    (BitVec.ofNat 64 (((level (leaves m0) k).length + 1) / 2))).store
    (base m0 + BitVec.ofNat 64 countSlot) 8 (BitVec.ofNat 64 (((level (leaves m0) k).length + 1) / 2)) = m1
  have steady1 : Steady m0 m1 := by
    rw [← hm1]
    exact (((steady.write (by decide) (by decide) (by decide)).write (by decide) (by decide)
      (by decide)).write (by decide) (by decide) (by decide)).store (by simp [dynamicSlots])
  have readHeight : m1.load (base m0 + BitVec.ofNat 64 heightSlot) 8 = BitVec.ofNat 64 k := by
    rw [← hm1, Machine.load_store_of_disjoint (disjoint_offsets (by decide) (by decide)) (by decide),
      Machine.load_write, Machine.load_write, Machine.load_write, state.heightStored]
  simp only [readHeight, ← BitVec.ofNat_add]
  refine Reaches.exec (fetch_one (fun k within => fetch_levelEnd within) 7 (by decide))
    (Reaches.now ⟨rfl, ?_⟩)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero, levelEndCode, Instr.run]
  refine ⟨(((steady1.write (by decide) (by decide) (by decide)).write (by decide) (by decide)
      (by decide)).store (by simp [dynamicSlots])), by omega, ?_, Machine.load_store_self8,
    fun j within => ?_⟩
  · rw [Machine.load_store_of_disjoint (disjoint_offsets (by decide) (by decide)) (by decide),
      Machine.load_write, Machine.load_write, ← hm1, Machine.load_store_self8, level_length]
  · rw [level_length] at within
    rw [chunkAt_store_frame valid (by decide) (by unfold capacity; omega), chunkAt_write, chunkAt_write,
      ← hm1, chunkAt_store_frame valid (by decide) (by unfold capacity; omega), chunkAt_write,
      chunkAt_write, chunkAt_write]
    exact state.parents j within

/-- One pass of the level loop: stop at the top or at an empty level, and otherwise fold one level. -/
theorem level_step {m0 m : Machine} {k : Nat} (valid : Valid m0) (state : AtLevel m0 k m) :
    Reaches program ⟨m, levelHead⟩ fun s =>
      (s.pc = done ∧ AtDone m0 k s.m) ∨ (s.pc = levelHead ∧ k < depth m0 ∧ AtLevel m0 (k + 1) s.m) := by
  have steady := state.steady
  have bounds := width_le m0 k
  have small := valid.small
  have shallow := valid.shallow
  have height := state.height
  refine Reaches.run (start := levelHead) (n := 2)
    [.ld t0 sp (slot heightSlot), .ld t1 sp (slot depthSlot)] rfl
    (fetch_slice (fun k within => fetch_levelHead within) 0 _ rfl (by decide)) (by decide) ?_
  simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self,
    Machine.read_write_ne, Machine.load_write, steady.stack, slot_ext (show heightSlot < 2048 by decide),
    slot_ext (show depthSlot < 2048 by decide), state.heightStored, steady.depthStored]
  -- Stop once the height reaches the depth.
  refine Reaches.exec (fetch_one (fun k within => fetch_levelHead within) 2 (by decide)) ?_
  simp (disch := decide) only [List.getElem_cons_succ, List.getElem_cons_zero, levelHeadCode,
    Instr.run, Instr.next, Machine.read_write_self, Machine.read_write_ne,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  by_cases top : k < (m0.read a2).toNat
  · rw [if_pos top]
    refine Reaches.run (start := levelHead + 2 + 1) (n := 1) [.ld a4 sp (slot countSlot)] rfl
      (fetch_slice (fun k within => fetch_levelHead within) 3 _ rfl (by decide)) (by decide) ?_
    simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self,
      Machine.read_write_ne, Machine.load_write, steady.stack, slot_ext (show countSlot < 2048 by decide),
      state.countStored]
    -- Stop at an empty level.
    refine Reaches.exec (fetch_one (fun k within => fetch_levelHead within) 4 (by decide)) ?_
    simp (disch := decide) only [List.getElem_cons_succ, List.getElem_cons_zero, levelHeadCode,
      Instr.run, Instr.next, Machine.read_write_self, Machine.read_write_ne, Machine.read_zero]
    by_cases empty : (level (leaves m0) k).length = 0
    · rw [if_pos (by rw [empty]; rfl)]
      exact Reaches.now (Or.inl ⟨rfl, ⟨(((state.write (by decide) (by decide) (by decide)).write
        (by decide) (by decide) (by decide)).write (by decide) (by decide) (by decide)),
        Or.inr empty⟩⟩)
    · rw [if_neg (by
        rw [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
          ofNat_eq_iff (by omega) (by decide)]
        exact empty)]
      -- Start at pair zero, then fold the level and move up.
      refine Reaches.run (start := levelHead + 2 + 1 + 1 + 1) (n := 1) [.sd zero sp (slot pairSlot)] rfl
        (fetch_slice (fun k within => fetch_levelHead within) 5 _ rfl (by decide)) (by decide) ?_
      simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_ne,
        Machine.read_zero, steady.stack, slot_ext (show pairSlot < 2048 by decide)]
      rw [show levelHead + 2 + 1 + 1 + 1 + 1 = pairHead from rfl]
      generalize hm1 : ((m.write t0 (BitVec.ofNat 64 k)).write t1 (m0.read a2)).write a4
        (BitVec.ofNat 64 (level (leaves m0) k).length) = m1
      have state1 : AtLevel m0 k m1 := by
        rw [← hm1]
        exact ((state.write (by decide) (by decide) (by decide)).write (by decide) (by decide)
          (by decide)).write (by decide) (by decide) (by decide)
      have slot1 (c : Nat) (fits : c + 8 ≤ frameSize) (apart : c + 8 ≤ pairSlot ∨ pairSlot + 8 ≤ c) :
          (m1.store (base m0 + BitVec.ofNat 64 pairSlot) 8 0).load (base m0 + BitVec.ofNat 64 c) 8 =
            m1.load (base m0 + BitVec.ofNat 64 c) 8 :=
        Machine.load_store_of_disjoint (disjoint_offsets
          (by simp only [frameSize, pairSlot] at fits apart ⊢; omega)
          (by simp only [frameSize, pairSlot] at fits apart ⊢; omega)) (by decide)
      have start : AtPair m0 k 0 (m1.store (base m0 + BitVec.ofNat 64 pairSlot) 8 0) := {
        steady := state1.steady.store (by simp [dynamicSlots])
        below := top
        nonempty := by omega
        progress := Nat.zero_le _
        countStored := by rw [slot1 countSlot (by decide) (by decide), state1.countStored]
        heightStored := by rw [slot1 heightSlot (by decide) (by decide), state1.heightStored]
        pairStored := Machine.load_store_self8
        parents := fun j within => absurd within (Nat.not_lt_zero _)
        children := fun j _ within => by
          rw [chunkAt_store_frame valid (by decide) (by unfold capacity; omega)]
          exact state1.chunks j within }
      exact (pair_loop valid _ 0 _ rfl start).bind fun s ⟨pc, halfway⟩ => by
        rw [show s = ⟨s.m, levelEnd⟩ by rw [← pc]]
        exact (level_end valid halfway).bind fun s' ⟨pc', next⟩ =>
          Reaches.now (Or.inr ⟨pc', top, next⟩)
  · -- Every level is folded.
    rw [if_neg top]
    have topAt : k = depth m0 := by unfold depth at height ⊢; omega
    exact Reaches.now (Or.inl ⟨rfl, ⟨((state.write (by decide) (by decide) (by decide)).write
      (by decide) (by decide) (by decide)), Or.inl topAt⟩⟩)

/-- The level loop runs from any level to its end. -/
theorem level_loop {m0 : Machine} (valid : Valid m0) :
    ∀ r k m, depth m0 - k = r → AtLevel m0 k m →
      Reaches program ⟨m, levelHead⟩ fun s => s.pc = done ∧ ∃ k, AtDone m0 k s.m := by
  intro r
  induction r with
  | zero =>
    intro k m left state
    exact (level_step valid state).bind fun s outcome => by
      rcases outcome with ⟨pc, stopped⟩ | ⟨_, below, _⟩
      · exact Reaches.now ⟨pc, k, stopped⟩
      · omega
  | succ r ih =>
    intro k m left state
    exact (level_step valid state).bind fun s outcome => by
      rcases outcome with ⟨pc, stopped⟩ | ⟨pc, _, next⟩
      · exact Reaches.now ⟨pc, k, stopped⟩
      · rw [show s = ⟨s.m, levelHead⟩ by rw [← pc]]
        exact ih (k + 1) s.m (by omega) next

end Ssz.Asm.Merkle
