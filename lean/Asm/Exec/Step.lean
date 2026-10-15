import Asm.Exec.Loop

/-! One step of the executor: decode it, run it, and count it. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Exec

open Ssz.Asm.Sha256 (sp t0 t1 a0 a1 a2 savedSlots)
open Ssz.Asm.Merkle (zero t2 a3 a4 a5 slot ofNat_lt_iff ofNat_eq_iff ofNat_shift)
open Ssz.Asm.Root (Step Agree runPlan)

/-- After decoding: read the source or left slot and the last word, then branch on the kind of step. -/
theorem after_decode {m0 M : Machine} {steps : List Step} {size k : Nat} (valid : Valid m0 steps size)
    (more : k < steps.length) (steady : Steady m0 size M)
    (index : M.load (base m0 + BitVec.ofNat 64 indexSlot) 8 = BitVec.ofNat 64 k)
    (out : M.load (base m0 + BitVec.ofNat 64 outSlot) 8 = scratch m0 + BitVec.ofNat 64 (stepWord steps[k] 1))
    (stepAddr : M.read a5 = planAddr m0 + BitVec.ofNat 64 (2 ^ 5 * k)) (scratchReg : M.read a4 = scratch m0)
    (kind : M.read t1 = BitVec.ofNat 64 (stepWord steps[k] 0))
    (slotAddr : M.read t2 = scratch m0 + BitVec.ofNat 64 (stepWord steps[k] 1))
    (agree : Agree (view M (scratch m0)) (runPlan (steps.take k) (view m0 (scratch m0))) size) :
    Reaches program ⟨M, stepHead + 11⟩ fun s => s.pc = next ∧ AtNext m0 steps size k s.m := by
  have small := valid.small
  refine Reaches.run (start := stepHead + 11) (n := 3) [.ld a1 a5 (slot 16), .add a1 a4 a1, .ld a2 a5 (slot 24)]
    rfl (fetch_slice (fun k within => fetch_stepHead within) 11 _ rfl (by decide)) (by decide) ?_
  have w2 := planWord_at (j := 2) valid steady more (by decide)
  have w3 := planWord_at (j := 3) valid steady more (by decide)
  simp only [show 8 * 2 = 16 from rfl, show 8 * 3 = 24 from rfl] at w2 w3
  simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self,
    Machine.read_write_ne, Machine.load_write, stepAddr, scratchReg, slot_ext (show 16 < 2048 by decide),
    slot_ext (show 24 < 2048 by decide), w2, w3]
  refine Reaches.exec (fetch_one (fun k within => fetch_stepHead within) 14 (by decide)) ?_
  simp (disch := decide) only [List.getElem_cons_succ, List.getElem_cons_zero, stepHeadCode,
    Instr.run, Instr.next, Machine.read_write_self, Machine.read_write_ne, Machine.read_zero, kind]
  have reads := valid.reads _ (List.getElem_mem more)
  have writes := valid.writes _ (List.getElem_mem more)
  -- The registers the branch leaves: the source or left slot's address, and the last word.
  generalize hM' : (((M.write a1 (BitVec.ofNat 64 (stepWord steps[k] 2))).write a1
    (scratch m0 + BitVec.ofNat 64 (stepWord steps[k] 2))).write a2 (BitVec.ofNat 64 (stepWord steps[k] 3))) = M'
  have steady' : Steady m0 size M' := by
    rw [← hM']
    exact ((steady.write (by decide) (by decide) (by decide)).write (by decide) (by decide) (by decide)).write
      (by decide) (by decide) (by decide)
  have mem' : M'.mem = M.mem := by rw [← hM']; rfl
  have r1 : M'.read a1 = scratch m0 + BitVec.ofNat 64 (stepWord steps[k] 2) := by
    rw [← hM', Machine.read_write_ne (by decide), Machine.read_write_self (by decide)]
  have r2 : M'.read a2 = BitVec.ofNat 64 (stepWord steps[k] 3) := by
    rw [← hM', Machine.read_write_self (by decide)]
  have r4 : M'.read a4 = scratch m0 := by
    rw [← hM']; simp (disch := decide) [Machine.read_write_ne, scratchReg]
  have r7 : M'.read t2 = scratch m0 + BitVec.ofNat 64 (stepWord steps[k] 1) := by
    rw [← hM']; simp (disch := decide) [Machine.read_write_ne, slotAddr]
  have indexM' := (Machine.load_of_mem mem').trans index
  have outM' := (Machine.load_of_mem mem').trans out
  have agreeM' : Agree (view M' (scratch m0)) (runPlan (steps.take k) (view m0 (scratch m0))) size := by
    rw [← hM']; exact agree
  cases hstep : steps[k] with
  | chunk dst src len =>
    rw [hstep] at reads writes r1 r2 r7
    simp only [Root.Step.readsBelow, Root.Step.dst] at reads writes
    simp only [stepWord] at r1 r2 r7
    simp only [hstep, stepWord]
    rw [if_pos (by decide), show stepHead + 11 + 3 + 1 = chunkStart from rfl]
    -- A chunk step: count bytes from zero.
    refine Reaches.run (start := chunkStart) (n := 1) chunkStartCode rfl
      (fun i w => fetch_chunkStart w) (by decide) ?_
    simp (disch := decide) only [chunkStartCode, execBlock_cons, execBlock_nil, Instr.run,
      Machine.read_zero, slot_ext (show 0 < 2048 by decide), zero_plus]
    rw [show chunkStart + 1 = chunkLoop from rfl]
    have start : AtByte m0 size k dst src len 0 (view M' (scratch m0)) (M'.write t0 (BitVec.ofNat 64 0)) := {
      steady := steady'.write (by decide) (by decide) (by decide)
      index := by rw [Machine.load_write]; exact indexM'
      counter := Machine.read_write_self (by decide)
      source := by rw [Machine.read_write_ne (by decide)]; exact r1
      length := by rw [Machine.read_write_ne (by decide)]; exact r2
      target := by rw [Machine.read_write_ne (by decide)]; exact r7
      sofar := fun a _ => by
        simp only [partialChunk, Nat.add_zero]
        rw [if_neg (by omega)]
        rfl
      below := reads.1
      short := reads.2
      fits := writes
      progress := by omega
      small := small
      apart := valid.scratchFrame }
    exact (chunk_loop 32 0 _ rfl start).bind fun s ⟨pc, steadyS, indexS, agreeS⟩ => Reaches.now ⟨pc, steadyS,
      more, indexS, by
        rw [runPlan_take_succ more, hstep]
        exact Root.agree_trans agreeS (Root.step_congr (step := .chunk dst src len) ⟨reads.1, reads.2⟩
          writes agreeM')⟩
  | hash dst left right =>
    rw [hstep] at r1 r2 outM'
    simp only [stepWord] at r1 r2 outM'
    simp only [hstep, stepWord]
    rw [if_neg (by decide)]
    -- A hash step.
    exact hash_step valid steady' more hstep indexM' outM' r1 r4 r2 agreeM'

theorem step_iteration {m0 m : Machine} {steps : List Step} {size k : Nat} (valid : Valid m0 steps size)
    (state : AtStep m0 steps size k m) (more : k < steps.length) :
    Reaches program ⟨m, stepHead⟩ fun s => s.pc = stepHead ∧ AtStep m0 steps size (k + 1) s.m := by
  have steady := state.steady
  have small := valid.small
  have short := valid.short
  -- Is there a step left?
  refine Reaches.run (start := stepHead) (n := 2) [.ld t0 sp (slot indexSlot), .ld t1 sp (slot stepsSlot)] rfl
    (by
      intro i w
      have := fetch_slice (fun k within => fetch_stepHead within) 0
        [.ld t0 sp (slot indexSlot), .ld t1 sp (slot stepsSlot)] rfl (by decide) i w
      simpa using this)
    (by decide) ?_
  simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self,
    Machine.read_write_ne, Machine.load_write, steady.stack, slot_ext (show indexSlot < 2048 by decide),
    slot_ext (show stepsSlot < 2048 by decide), state.index, steady.stepsStored]
  refine Reaches.exec (fetch_one (fun k within => fetch_stepHead within) 2 (by decide)) ?_
  simp (disch := decide) only [List.getElem_cons_succ, List.getElem_cons_zero, stepHeadCode, Instr.run,
    Instr.next, Machine.read_write_self, Machine.read_write_ne, valid.count, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), more, if_true]
  -- Decode the step: its slot's address goes to the frame for the pair hash.
  rw [show stepHead + 2 + 1 = stepHead + 3 from rfl]
  refine Reaches.run (start := stepHead + 3) (n := 8)
    [.ld a5 sp (slot planSlot), .slli t2 t0 5, .add a5 a5 t2, .ld a4 sp (slot scratchSlot),
      .ld t1 a5 (slot 0), .ld t2 a5 (slot 8), .add t2 a4 t2, .sd t2 sp (slot outSlot)] rfl
    (fetch_slice (fun k within => fetch_stepHead within) 3 _ rfl (by decide)) (by decide) ?_
  have w0 := planWord_at (j := 0) valid steady more (by decide)
  have w1 := planWord_at (j := 1) valid steady more (by decide)
  simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self,
    Machine.read_write_ne, Machine.load_write, steady.stack, slot_ext (show planSlot < 2048 by decide),
    slot_ext (show scratchSlot < 2048 by decide), slot_ext (show 0 < 2048 by decide),
    slot_ext (show 8 < 2048 by decide), slot_ext (show outSlot < 2048 by decide),
    steady.planStored, steady.scratchStored,
    ofNat_shift (show 2 ^ 5 * k < 2 ^ 64 by omega) (by decide)]
  simp only [Nat.mul_zero, Nat.mul_one] at w0 w1
  rw [show stepHead + 3 + 8 = stepHead + 11 from rfl]
  simp only [w0, w1]
  refine (after_decode valid more ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_).bind fun s ⟨pc, done⟩ => by
    rw [show s = ⟨s.m, next⟩ by rw [← pc]]
    exact next_step valid done
  · exact ((((((((steady.write (by decide) (by decide) (by decide)).write (by decide) (by decide)
      (by decide)).write (by decide) (by decide) (by decide)).write (by decide) (by decide) (by decide)).write
      (by decide) (by decide) (by decide)).write (by decide) (by decide) (by decide)).write (by decide)
      (by decide) (by decide)).write (by decide) (by decide) (by decide)).write (by decide) (by decide)
      (by decide) |>.store (by simp [dynamicSlots])
  · rw [Machine.load_store_of_disjoint (disjoint_offsets (by decide) (by decide)) (by decide)]
    simp only [Machine.load_write]
    exact state.index
  · exact Machine.load_store_self8
  · simp (disch := decide) [Machine.read_write_ne, Machine.read_write_self]
  · simp (disch := decide) [Machine.read_write_ne, Machine.read_write_self]
  · simp (disch := decide) [Machine.read_write_ne, Machine.read_write_self]
  · simp (disch := decide) [Machine.read_write_ne, Machine.read_write_self]
  · exact Root.agree_trans (view_store_frame valid.scratchFrame (by decide) small) state.agree

end Ssz.Asm.Exec
