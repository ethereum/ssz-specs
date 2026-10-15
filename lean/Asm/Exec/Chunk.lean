import Asm.Exec.State
import Asm.Root.Agree
import Asm.Merkle.Arith

/-! A chunk step's byte loop: copy the run of bytes, then zero-fill the rest of the slot. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Exec

open Ssz.Asm.Sha256 (sp t0 t1 a0 a1 a2 savedSlots)
open Ssz.Asm.Merkle (zero t2 a3 a4 a5 slot ofNat_lt_iff ofNat_eq_iff)
open Ssz.Asm.Sha256 (offset_eq_iff)
open Ssz.Asm.Root (Step Agree)

theorem slot_ext {c : Nat} (small : c < 2048) : (slot c).signExtend 64 = BitVec.ofNat 64 c :=
  signExtend_ofNat12 small

theorem zero_plus {x : BitVec 64} : (0 : BitVec 64) + x = x := by
  simp

/-- A chunk's slot after its first j bytes: copied while within the length, zero after it. -/
def partialChunk (dst src len j : Nat) (v : Root.Scratch) : Root.Scratch :=
  fun a => if dst ≤ a ∧ a < dst + j then (if a - dst < len then v (src + (a - dst)) else 0) else v a

/-- At the byte loop's head, with j bytes of the slot written. -/
structure AtByte (m0 : Machine) (size k dst src len j : Nat) (v : Root.Scratch) (m : Machine) : Prop where
  /-- The facts every state shares. -/
  steady : Steady m0 size m
  /-- The step index is in its slot. -/
  index : m.load (base m0 + BitVec.ofNat 64 indexSlot) 8 = BitVec.ofNat 64 k
  /-- t0 counts the bytes written. -/
  counter : m.read t0 = BitVec.ofNat 64 j
  /-- a1 points at the source. -/
  source : m.read a1 = scratch m0 + BitVec.ofNat 64 src
  /-- a2 holds the length. -/
  length : m.read a2 = BitVec.ofNat 64 len
  /-- t2 points at the slot. -/
  target : m.read t2 = scratch m0 + BitVec.ofNat 64 dst
  /-- The scratch area so far. -/
  sofar : Agree (view m (scratch m0)) (partialChunk dst src len j v) size
  /-- The source lies below the slot, and fits a slot. -/
  below : src + len ≤ dst
  /-- The run fits one slot. -/
  short : len ≤ 32
  /-- The slot lies inside the scratch area. -/
  fits : dst + 32 ≤ size
  /-- At most a slot's worth written. -/
  progress : j ≤ 32
  /-- The scratch area is comfortably small. -/
  small : size < 2 ^ 60
  /-- The scratch area and the frame share no byte. -/
  apart : Disjoint (scratch m0) size (base m0) frameSize

/-- The view after a one-byte store into the scratch area. -/
theorem view_store1 {m : Machine} {area : BitVec 64} {o : Nat} {v : BitVec 64} {a : Nat}
    (smallA : a < 2 ^ 60) (smallO : o < 2 ^ 60) :
    view (m.store (area + BitVec.ofNat 64 o) 1 v) area a =
      if a = o then ⟨v.setWidth 8⟩ else view m area a := by
  simp only [view, Sha256.Machine.mem_store1,
    offset_eq_iff (show a < 2 ^ 64 by omega) (show o < 2 ^ 64 by omega)]
  split <;> rfl

theorem AtByte.write {m0 m : Machine} {size k dst src len j : Nat} {v : Root.Scratch}
    (state : AtByte m0 size k dst src len j v m) {r : Reg} {x : BitVec 64} (notT0 : r ≠ t0)
    (notA1 : r ≠ a1) (notA2 : r ≠ a2) (notT2 : r ≠ t2) (notSp : r ≠ sp) (notGp : r ≠ 3) (notTp : r ≠ 4) :
    AtByte m0 size k dst src len j v (m.write r x) where
  steady := state.steady.write notSp notGp notTp
  index := by rw [Machine.load_write]; exact state.index
  counter := by rw [Machine.read_write_ne (Ne.symm notT0)]; exact state.counter
  source := by rw [Machine.read_write_ne (Ne.symm notA1)]; exact state.source
  length := by rw [Machine.read_write_ne (Ne.symm notA2)]; exact state.length
  target := by rw [Machine.read_write_ne (Ne.symm notT2)]; exact state.target
  sofar := state.sofar
  below := state.below
  short := state.short
  fits := state.fits
  progress := state.progress
  small := state.small
  apart := state.apart

theorem fetch_byte {k : Nat} (within : k < (chunkByteCode next store chunkLoop).length) :
    program[chunkLoop + k]? = some (chunkByteCode next store chunkLoop)[k] :=
  fetch_chunkLoop within

/-- At the store: write the byte in a3 to the slot, count it, and loop. -/
theorem at_store {m0 M : Machine} {size k dst src len j : Nat} {v : Root.Scratch} {b : BitVec 64}
    (state : AtByte m0 size k dst src len j v M) (more : j < 32) (byte : M.read a3 = b)
    (value : (⟨b.setWidth 8⟩ : UInt8) = if j < len then v (src + j) else 0) :
    Reaches program ⟨M, store⟩ fun s => s.pc = chunkLoop ∧ AtByte m0 size k dst src len (j + 1) v s.m := by
  have small := state.small
  have fits := state.fits
  refine Reaches.run (start := store) (n := 3) [.add t1 t2 t0, .sb a3 t1 (slot 0), .addi t0 t0 (slot 1)] rfl
    (by
      intro i within
      have := fetch_slice (fun k within => fetch_chunkLoop within) 6
        [.add t1 t2 t0, .sb a3 t1 (slot 0), .addi t0 t0 (slot 1)] rfl (by decide) i within
      simpa [show chunkLoop + 6 = store from rfl] using this)
    (by decide) ?_
  simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self,
    Machine.read_write_ne, Machine.read_store, state.target, state.counter, byte,
    slot_ext (show 0 < 2048 by decide), slot_ext (show 1 < 2048 by decide), BitVec.add_zero,
    ← BitVec.ofNat_add, BitVec.add_assoc]
  rw [show store + 3 = chunkLoop + 9 from rfl]
  refine Reaches.exec (fetch_byte (k := 9) (by decide)) (Reaches.now ⟨rfl, ?_⟩)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero, chunkByteCode, Instr.run]
  generalize hA : scratch m0 + BitVec.ofNat 64 (dst + j) = A
  -- The byte lands in the scratch area, which the frame never sees.
  have inArea : ∀ y, Within y A 1 → Within y (scratch m0) size := fun y within => by
    rw [← hA] at within
    exact within_sub within (by omega) (by omega)
  have steady1 := state.steady.write (r := t1) (v := A) (by decide) (by decide) (by decide)
  have steady2 : Steady m0 size ((M.write t1 A).store A 1 b) :=
    Steady.of_scratch state.apart steady1
      (fun y outside => Machine.mem_store_of_not_within fun within => outside (inArea y within)) rfl rfl rfl
  refine ⟨steady2.write (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, state.below,
    state.short, state.fits, by omega, state.small, state.apart⟩
  · rw [Machine.load_write, Machine.load_store_of_disjoint (fun y inSlot inByte =>
        state.apart y (inArea y inByte) (by
          have := within_sub inSlot (c := indexSlot) (n := frameSize) (by decide) (by decide)
          simpa using this)) (by decide), Machine.load_write]
    exact state.index
  · exact Machine.read_write_self (by decide)
  · rw [Machine.read_write_ne (by decide), Machine.read_store, Machine.read_write_ne (by decide)]
    exact state.source
  · rw [Machine.read_write_ne (by decide), Machine.read_store, Machine.read_write_ne (by decide)]
    exact state.length
  · rw [Machine.read_write_ne (by decide), Machine.read_store, Machine.read_write_ne (by decide)]
    exact state.target
  · -- Byte dst + j is the new one, and every other byte reads as before.
    intro a below
    have viewEq : view (((M.write t1 A).store A 1 b).write t0 (BitVec.ofNat 64 (j + 1))) (scratch m0) a =
        if a = dst + j then ⟨b.setWidth 8⟩ else view M (scratch m0) a := by
      rw [← hA]
      exact view_store1 (by omega) (by omega)
    rw [viewEq]
    split
    · rename_i now
      subst now
      rw [value]
      simp [partialChunk]
    · rename_i other
      rw [state.sofar a below]
      unfold partialChunk
      by_cases inside : dst ≤ a ∧ a < dst + j
      · have wider : dst ≤ a ∧ a < dst + (j + 1) := ⟨inside.1, by omega⟩
        rw [if_pos inside, if_pos wider]
      · have narrower : ¬(dst ≤ a ∧ a < dst + (j + 1)) := by omega
        rw [if_neg inside, if_neg narrower]

/-- One byte of the loop: copy it while within the length, write zero after it. -/
theorem chunk_byte {m0 m : Machine} {size k dst src len j : Nat} {v : Root.Scratch}
    (state : AtByte m0 size k dst src len j v m) (more : j < 32) :
    Reaches program ⟨m, chunkLoop⟩ fun s => s.pc = chunkLoop ∧ AtByte m0 size k dst src len (j + 1) v s.m := by
  have small := state.small
  have fits := state.fits
  have below := state.below
  refine Reaches.run (start := chunkLoop) (n := 1) [.addi t1 zero (slot 32)] rfl
    (by
      intro i within
      have := fetch_slice (fun k within => fetch_chunkLoop within) 0 [.addi t1 zero (slot 32)] rfl
        (by decide) i within
      simpa using this)
    (by decide) ?_
  simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_zero,
    slot_ext (show 32 < 2048 by decide), zero_plus]
  refine Reaches.exec (fetch_byte (k := 1) (by decide)) ?_
  simp (disch := decide) only [List.getElem_cons_succ, List.getElem_cons_zero, chunkByteCode, Instr.run,
    Instr.next, Machine.read_write_ne, Machine.read_write_self, state.counter,
    ofNat_lt_iff (show j < 2 ^ 64 by omega) (show 32 < 2 ^ 64 by decide), more, if_true]
  rw [show chunkLoop + 1 + 1 = chunkLoop + 2 from rfl]
  refine Reaches.run (start := chunkLoop + 2) (n := 1) [.addi a3 zero (slot 0)] rfl
    (by
      intro i within
      have := fetch_slice (fun k within => fetch_chunkLoop within) 2 [.addi a3 zero (slot 0)] rfl
        (by decide) i within
      simpa using this)
    (by decide) ?_
  simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_zero,
    Machine.read_write_ne, slot_ext (show 0 < 2048 by decide), zero_plus]
  refine Reaches.exec (fetch_byte (k := 3) (by decide)) ?_
  simp (disch := decide) only [List.getElem_cons_succ, List.getElem_cons_zero, chunkByteCode, Instr.run,
    Instr.next, Machine.read_write_ne, Machine.read_write_self, state.counter, state.length,
    ofNat_lt_iff (show j < 2 ^ 64 by omega) (show len < 2 ^ 64 by have := state.short; omega)]
  have stateA := (state.write (r := t1) (x := BitVec.ofNat 64 32) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)).write (r := a3) (x := BitVec.ofNat 64 0) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  by_cases within : j < len
  · -- Within the length: load the source byte, which no earlier store reached.
    rw [if_pos within, show chunkLoop + 2 + 1 + 1 = chunkLoop + 4 from rfl]
    refine Reaches.run (start := chunkLoop + 4) (n := 2) [.add a3 a1 t0, .lbu a3 a3 (slot 0)] rfl
      (by
        intro i w
        have := fetch_slice (fun k within => fetch_chunkLoop within) 4 [.add a3 a1 t0, .lbu a3 a3 (slot 0)]
          rfl (by decide) i w
        simpa using this)
      (by decide) ?_
    simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_ne,
      Machine.read_write_self, Machine.load_write, state.source, state.counter,
      slot_ext (show 0 < 2048 by decide), BitVec.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add]
    rw [show chunkLoop + 4 + 2 = store from rfl]
    have stateB := (stateA.write (r := a3) (x := scratch m0 + BitVec.ofNat 64 (src + j)) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    refine at_store (stateB.write (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) more (Machine.read_write_self (by decide)) ?_
    rw [if_pos within, Machine.load_one]
    -- The source byte lies below the slot, so it is still the one the step started from.
    have source := state.sofar (src + j) (by omega)
    simp only [partialChunk, show ¬(dst ≤ src + j ∧ src + j < dst + j) by omega, if_false] at source
    rw [← source]
    simp [view]
  · -- Past the length: the byte is zero.
    rw [if_neg within]
    refine at_store stateA more (Machine.read_write_self (by decide)) ?_
    rw [if_neg within]
    rfl

/-- After the slot's last byte, the loop leaves with the chunk step done. -/
theorem chunk_exit {m0 m : Machine} {size k dst src len : Nat} {v : Root.Scratch}
    (state : AtByte m0 size k dst src len 32 v m) :
    Reaches program ⟨m, chunkLoop⟩ fun s => s.pc = next ∧ Steady m0 size s.m ∧
      s.m.load (base m0 + BitVec.ofNat 64 indexSlot) 8 = BitVec.ofNat 64 k ∧
      Agree (view s.m (scratch m0)) ((Step.chunk dst src len).run v) size := by
  refine Reaches.run (start := chunkLoop) (n := 1) [.addi t1 zero (slot 32)] rfl
    (by
      intro i within
      have := fetch_slice (fun k within => fetch_chunkLoop within) 0 [.addi t1 zero (slot 32)] rfl
        (by decide) i within
      simpa using this)
    (by decide) ?_
  simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_zero,
    slot_ext (show 32 < 2048 by decide), zero_plus]
  refine Reaches.exec (fetch_byte (k := 1) (by decide)) (Reaches.now ⟨?_, ?_, ?_, ?_⟩)
  · simp (disch := decide) [chunkByteCode, Instr.next, Machine.read_write_ne, Machine.read_write_self,
      state.counter]
  · exact state.steady.write (by decide) (by decide) (by decide)
  · simp only [chunkByteCode, List.getElem_cons_succ, List.getElem_cons_zero, Instr.run, Machine.load_write]
    exact state.index
  · intro a below
    simp only [chunkByteCode, List.getElem_cons_succ, List.getElem_cons_zero, Instr.run]
    rw [show view ((m.write t1 (BitVec.ofNat 64 32))) (scratch m0) a = view m (scratch m0) a from rfl,
      state.sofar a below]
    rfl

/-- The whole byte loop, from any byte on. -/
theorem chunk_loop {m0 : Machine} {size k dst src len : Nat} {v : Root.Scratch} :
    ∀ r j m, 32 - j = r → AtByte m0 size k dst src len j v m →
      Reaches program ⟨m, chunkLoop⟩ fun s => s.pc = next ∧ Steady m0 size s.m ∧
        s.m.load (base m0 + BitVec.ofNat 64 indexSlot) 8 = BitVec.ofNat 64 k ∧
        Agree (view s.m (scratch m0)) ((Step.chunk dst src len).run v) size := by
  intro r
  induction r with
  | zero =>
    intro j m left state
    have done : j = 32 := by have := state.progress; omega
    subst done
    exact chunk_exit state
  | succ r ih =>
    intro j m left state
    exact (chunk_byte state (by omega)).bind fun s ⟨pc, next⟩ => by
      rw [show s = ⟨s.m, chunkLoop⟩ by rw [← pc]]
      exact ih (j + 1) s.m (by omega) next

end Ssz.Asm.Exec
