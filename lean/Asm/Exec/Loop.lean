import Asm.Exec.Chunk

/-! The step loop: decode a step, run it, and count it. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Exec

open Ssz.Asm.Sha256 (sp t0 t1 a0 a1 a2 savedSlots pairCode workRegs pair_spec)
open Ssz.Asm.Merkle (zero t2 a3 a4 a5 slot ofNat_lt_iff ofNat_eq_iff ofNat_shift)
open Ssz.Asm.Root (Step Agree runPlan readSlot)

/-- At the step loop's head, with the first k steps done. -/
structure AtStep (m0 : Machine) (steps : List Step) (size k : Nat) (m : Machine) : Prop where
  /-- The facts every state shares. -/
  steady : Steady m0 size m
  /-- At most every step is done. -/
  progress : k ≤ steps.length
  /-- The step index is in its slot. -/
  index : m.load (base m0 + BitVec.ofNat 64 indexSlot) 8 = BitVec.ofNat 64 k
  /-- The scratch area is the first k steps run over the one on entry. -/
  agree : Agree (view m (scratch m0)) (runPlan (steps.take k) (view m0 (scratch m0))) size

/-- After step k, about to count it. -/
structure AtNext (m0 : Machine) (steps : List Step) (size k : Nat) (m : Machine) : Prop where
  /-- The facts every state shares. -/
  steady : Steady m0 size m
  /-- Step k exists. -/
  within : k < steps.length
  /-- The step index is in its slot. -/
  index : m.load (base m0 + BitVec.ofNat 64 indexSlot) 8 = BitVec.ofNat 64 k
  /-- The scratch area is the first k + 1 steps run over the one on entry. -/
  agree : Agree (view m (scratch m0)) (runPlan (steps.take (k + 1)) (view m0 (scratch m0))) size

theorem runPlan_take_succ {steps : List Step} {k : Nat} (within : k < steps.length) {s : Root.Scratch} :
    runPlan (steps.take (k + 1)) s = steps[k].run (runPlan (steps.take k) s) := by
  rw [List.take_add_one, List.getElem?_eq_getElem within, Option.toList_some, Root.runPlan_append]
  rfl

@[simp] theorem view_write {m : Machine} {r : Reg} {v area : BitVec 64} :
    view (m.write r v) area = view m area :=
  rfl

/-- A slot's 32 bytes, read as the plan reads them. -/
theorem bytes_view {m : Machine} {area : BitVec 64} {o : Nat} :
    (m.bytes (area + BitVec.ofNat 64 o) 32).data = readSlot (view m area) o := by
  simp only [Machine.bytes, readSlot, view]
  congr 1
  funext i
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Count step k and go back to the loop's head. -/
theorem next_step {m0 m : Machine} {steps : List Step} {size k : Nat} (valid : Valid m0 steps size)
    (state : AtNext m0 steps size k m) :
    Reaches program ⟨m, next⟩ fun s => s.pc = stepHead ∧ AtStep m0 steps size (k + 1) s.m := by
  have short := valid.short
  have within := state.within
  refine Reaches.run (start := next) (n := 3)
    [.ld t0 sp (slot indexSlot), .addi t0 t0 (slot 1), .sd t0 sp (slot indexSlot)] rfl
    (by
      intro i w
      have := fetch_slice (fun k within => fetch_next within) 0
        [.ld t0 sp (slot indexSlot), .addi t0 t0 (slot 1), .sd t0 sp (slot indexSlot)] rfl (by decide) i w
      simpa using this)
    (by decide) ?_
  simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self,
    Machine.read_write_ne, state.steady.stack, slot_ext (show indexSlot < 2048 by decide),
    slot_ext (show 1 < 2048 by decide), state.index, ← BitVec.ofNat_add]
  refine Reaches.exec (fetch_one (fun k within => fetch_next within) 3 (by decide)) (Reaches.now ⟨rfl, ?_⟩)
  simp only [nextCode, List.getElem_cons_succ, List.getElem_cons_zero, Instr.run]
  refine ⟨((state.steady.write (by decide) (by decide) (by decide)).write (by decide) (by decide)
    (by decide)).store (by simp [dynamicSlots]), by omega, Machine.load_store_self8, ?_⟩
  intro a below
  -- The index slot lies in the frame, so the scratch area is as the step left it.
  have same : view ((((m.write t0 (BitVec.ofNat 64 k)).write t0 (BitVec.ofNat 64 (k + 1))).store
      (base m0 + BitVec.ofNat 64 indexSlot) 8 (BitVec.ofNat 64 (k + 1)))) (scratch m0) a =
      view m (scratch m0) a := by
    simp only [view]
    rw [Machine.mem_store_of_not_within fun within => valid.scratchFrame _
      ((within_offset (by have := valid.small; omega)).mpr below)
      (within_sub within (by decide) (by decide))]
    rfl
  rw [same]
  exact state.agree a below

/-- A hash step: hash the left and right slots into the written slot. -/
theorem hash_step {m0 m : Machine} {steps : List Step} {size k dst left right : Nat}
    (valid : Valid m0 steps size) (steady : Steady m0 size m) (within : k < steps.length)
    (isHash : steps[k] = .hash dst left right)
    (index : m.load (base m0 + BitVec.ofNat 64 indexSlot) 8 = BitVec.ofNat 64 k)
    (out : m.load (base m0 + BitVec.ofNat 64 outSlot) 8 = scratch m0 + BitVec.ofNat 64 dst)
    (leftAddr : m.read a1 = scratch m0 + BitVec.ofNat 64 left) (scratchReg : m.read a4 = scratch m0)
    (rightWord : m.read a2 = BitVec.ofNat 64 right)
    (agree : Agree (view m (scratch m0)) (runPlan (steps.take k) (view m0 (scratch m0))) size) :
    Reaches program ⟨m, hashStart⟩ fun s => s.pc = next ∧ AtNext m0 steps size k s.m := by
  have small := valid.small
  have reads := valid.reads _ (List.getElem_mem within)
  have writes := valid.writes _ (List.getElem_mem within)
  rw [isHash] at reads writes
  simp only [Root.Step.readsBelow, Root.Step.dst] at reads writes
  refine Reaches.run (start := hashStart) (n := 5092) hashCode hashCode_length
    (fun i w => fetch_hashStart w) (fun i mem => by
      simp only [hashCode, List.mem_cons] at mem
      rcases mem with rfl | mem
      · rfl
      · exact Sha256.pairCode_straight outSlot i mem) ?_
  rw [show hashStart + 5092 = next from rfl]
  refine Reaches.now ⟨rfl, ?_⟩
  simp only [hashCode, execBlock_cons, Instr.run, rightWord, scratchReg]
  generalize hM : m.write a2 (scratch m0 + BitVec.ofNat 64 right) = M
  have steadyM : Steady m0 size M := by rw [← hM]; exact steady.write (by decide) (by decide) (by decide)
  obtain ⟨hashed, memHash, regsHash⟩ := pair_spec M outSlot (by decide)
  have outM : M.load (M.read sp + BitVec.ofNat 64 outSlot) 8 = scratch m0 + BitVec.ofNat 64 dst := by
    rw [steadyM.stack, ← hM, Machine.load_write, out]
  rw [outM] at hashed memHash
  have leftM : M.read a1 = scratch m0 + BitVec.ofNat 64 left := by
    rw [← hM, Machine.read_write_ne (by decide), leftAddr]
  have rightM : M.read a2 = scratch m0 + BitVec.ofNat 64 right := by
    rw [← hM, Machine.read_write_self (by decide)]
  rw [leftM, rightM] at hashed
  generalize execBlock (pairCode outSlot) M = M' at hashed memHash regsHash
  have inArea (y : BitVec 64) (w : Within y (scratch m0 + BitVec.ofNat 64 dst) 32) :
      Within y (scratch m0) size := within_sub w (by omega) (by omega)
  refine ⟨Steady.of_scratch valid.scratchFrame steadyM (fun y out => memHash y fun w => out (inArea y w))
    (regsHash sp (by decide)) (regsHash 3 (by decide)) (regsHash 4 (by decide)), within, ?_, ?_⟩
  · rw [Machine.load_congr fun b below => memHash _ fun w => valid.scratchFrame _ (inArea _ w)
      (slot_within (c := indexSlot) (by decide) below), ← hM, Machine.load_write, index]
  · rw [runPlan_take_succ within, isHash]
    intro a below
    -- Inside the written slot the bytes are the hash, and elsewhere they are untouched.
    simp only [Root.Step.run]
    by_cases slot : dst ≤ a ∧ a < dst + 32
    · rw [if_pos slot]
      have byte := congrArg (fun bytes : ByteArray => bytes.data[a - dst]!) hashed
      simp only at byte
      rw [show (M'.bytes (scratch m0 + BitVec.ofNat 64 dst) 32).data[a - dst]! = (view M' (scratch m0)) a by
        rw [getElem!_pos _ _ (by simp [Machine.bytes]; omega)]
        simp only [Machine.bytes, Array.getElem_ofFn, view]
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, show dst + (a - dst) = a by omega]] at byte
      rw [byte, bytes_view, bytes_view, ← hM, view_write]
      rw [Root.readSlot_congr agree (by omega : left + 32 ≤ size),
        Root.readSlot_congr agree (by omega : right + 32 ≤ size)]
    · rw [if_neg slot]
      have outside : ¬Within (scratch m0 + BitVec.ofNat 64 a) (scratch m0 + BitVec.ofNat 64 dst) 32 := by
        intro w
        simp only [Within] at w
        rw [show scratch m0 + BitVec.ofNat 64 a - (scratch m0 + BitVec.ofNat 64 dst) =
          BitVec.ofNat 64 a - BitVec.ofNat 64 dst by bv_omega] at w
        rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)] at w
        omega
      show (⟨M'.mem (scratch m0 + BitVec.ofNat 64 a)⟩ : UInt8) = _
      rw [memHash _ outside, ← hM]
      exact agree a below

theorem view_store_frame {m0 m : Machine} {size c : Nat} {v : BitVec 64} (valid : Disjoint (scratch m0) size (base m0) frameSize)
    (fits : c + 8 ≤ frameSize) (small : size < 2 ^ 60) :
    Agree (view (m.store (base m0 + BitVec.ofNat 64 c) 8 v) (scratch m0)) (view m (scratch m0)) size := by
  intro a below
  simp only [view]
  rw [Machine.mem_store_of_not_within fun within => valid _ ((within_offset (by omega)).mpr below)
    (within_sub within fits (by decide))]

/-- Word j of step k, read from the plan through the step's address. -/
theorem planWord_at {m0 m : Machine} {steps : List Step} {size k j : Nat} (valid : Valid m0 steps size)
    (steady : Steady m0 size m) (within : k < steps.length) (below : j < 4) :
    m.load (planAddr m0 + BitVec.ofNat 64 (2 ^ 5 * k) + BitVec.ofNat 64 (8 * j)) 8 =
      BitVec.ofNat 64 (stepWord steps[k] j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 2 ^ 5 * k + 8 * j = 32 * k + 8 * j by omega]
  exact planWord valid steady within below

end Ssz.Asm.Exec
