import Asm.Exec.Step

/-! The executor: every step of a plan, run in order, over the scratch area. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Exec

open Ssz.Asm.Sha256 (sp t0 t1 a0 a1 a2 savedSlots)
open Ssz.Asm.Merkle (zero t2 a3 a4 a5 slot ofNat_lt_iff)
open Ssz.Asm.Root (Step Agree runPlan)

theorem entryCode_straight : ∀ i ∈ entryCode, i.straight := by
  decide

theorem entry_reaches {m0 : Machine} {steps : List Step} {size : Nat} (valid : Valid m0 steps size) :
    Reaches program ⟨m0, 0⟩ fun s => s.pc = stepHead ∧ AtStep m0 steps size 0 s.m := by
  refine Reaches.block (s := ⟨m0, 0⟩) entryCode (fun k within => fetch_entry within) entryCode_straight
    (Reaches.now ?_)
  refine ⟨by show 0 + entryCode.length = stepHead; rw [entryCode_length]; rfl, ?_⟩
  have opened : (Instr.addi sp sp (BitVec.ofInt 12 (-(frameSize : Int)))).run m0 = m0.write sp (base m0) := by
    have down : (BitVec.ofInt 12 (-(frameSize : Int))).signExtend 64 = 0 - BitVec.ofNat 64 frameSize := by
      decide
    have moved : m0.read sp + (0 - BitVec.ofNat 64 frameSize) = m0.read sp - BitVec.ofNat 64 frameSize := by
      bv_omega
    simp only [Instr.run, base, down, moved]
  have small : ∀ s ∈ entrySlots, s.2 < 2048 := by decide
  have inside : ∀ s ∈ entrySlots, s.2 + 8 ≤ frameSize := by decide
  have notSp : ∀ s ∈ entrySlots, s.1 ≠ sp := by decide
  have apart : SlotsApart entrySlots := by unfold SlotsApart; decide
  simp only [entryCode, execBlock_cons, opened]
  generalize hm : execBlock (spills sp entrySlots) (m0.write sp (base m0)) = m
  have spillsRead (r : Reg) : m.read r = (m0.write sp (base m0)).read r := by rw [← hm, spills_read]
  have spillsMem (y : BitVec 64) (outside : ¬Within y (base m0) frameSize) : m.mem y = m0.mem y := by
    rw [← hm, spills_mem small fun s mem within => outside (within_sub (by
        rwa [Machine.read_write_self (by decide)] at within) (inside s mem) (by decide)),
      Machine.mem_write]
  have spillsLoad (s : Reg × Nat) (mem : s ∈ entrySlots) :
      m.load (base m0 + BitVec.ofNat 64 s.2) 8 = m0.read s.1 := by
    have loaded := spills_load (base := sp) (m := m0.write sp (base m0)) apart s mem
    rwa [Machine.read_write_self (by decide), Machine.read_write_ne (notSp s mem), hm] at loaded
  refine ⟨⟨?_, ?_, ?_, ?_, fun s mem => ?_, fun y frame _ => spillsMem y frame, ?_, ?_⟩,
    Nat.zero_le _, ?_, fun a below => ?_⟩
  · rw [spillsRead, Machine.read_write_self (by decide)]
  · exact spillsLoad (a0, scratchSlot) (by decide)
  · exact spillsLoad (a1, planSlot) (by decide)
  · exact spillsLoad (a2, stepsSlot) (by decide)
  · exact spillsLoad s (by simp [entrySlots, mem])
  · rw [spillsRead, Machine.read_write_ne (by decide)]
  · rw [spillsRead, Machine.read_write_ne (by decide)]
  · rw [spillsLoad (zero, indexSlot) (by decide), Machine.read_zero]
    rfl
  · -- The scratch area lies outside the frame, so it is as the caller left it.
    simp only [view, List.take_zero]
    rw [spillsMem _ (valid.scratchFrame _ ((within_offset (by have := valid.small; omega)).mpr below))]
    rfl

/-- The whole step loop, from any step on. -/
theorem step_loop {m0 : Machine} {steps : List Step} {size : Nat} (valid : Valid m0 steps size) :
    ∀ r k m, steps.length - k = r → AtStep m0 steps size k m →
      Reaches program ⟨m, stepHead⟩ fun s => s.pc = stepHead ∧ AtStep m0 steps size steps.length s.m := by
  intro r
  induction r with
  | zero =>
    intro k m left state
    have done : k = steps.length := by have := state.progress; omega
    subst done
    exact Reaches.now ⟨rfl, state⟩
  | succ r ih =>
    intro k m left state
    exact (step_iteration valid state (by omega)).bind fun s ⟨pc, next⟩ => by
      rw [show s = ⟨s.m, stepHead⟩ by rw [← pc]]
      exact ih (k + 1) s.m (by omega) next

/-- Registers a caller finds unchanged. -/
abbrev preserved : List Reg :=
  Sha256.preserved

theorem finishBody_straight :
    ∀ i ∈ reloads sp savedSlots ++ [Instr.addi sp sp (slot frameSize)], i.straight := by
  decide

/-- With every step done, restore the saved registers, close the frame, and return. -/
theorem exit_reaches {m0 m : Machine} {steps : List Step} {size : Nat} (valid : Valid m0 steps size)
    (state : AtStep m0 steps size steps.length m) :
    Reaches program ⟨m, stepHead⟩ fun s => returned program s ∧
      Agree (view s.m (scratch m0)) (runPlan steps (view m0 (scratch m0))) size ∧
      (∀ r ∈ preserved, s.m.read r = m0.read r) ∧
      ∀ y, ¬Within y (base m0) frameSize → ¬Within y (scratch m0) size → s.m.mem y = m0.mem y := by
  have steady := state.steady
  have short := valid.short
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
    Nat.mod_eq_of_lt (show steps.length < 2 ^ 64 by omega), Nat.lt_irrefl, if_false]
  generalize hM : (m.write t0 (BitVec.ofNat 64 steps.length)).write t1 (m0.read a2) = M
  have steadyM : Steady m0 size M := by
    rw [← hM]; exact (steady.write (by decide) (by decide) (by decide)).write (by decide) (by decide) (by decide)
  have memM : M.mem = m.mem := by rw [← hM]; rfl
  refine Reaches.run (start := finish) (n := 14) (reloads sp savedSlots ++ [Instr.addi sp sp (slot frameSize)])
    (by simp [reloads, savedSlots]) (fun k w => by
      have := fetch_slice (fun k within => fetch_finish within) 0
        (reloads sp savedSlots ++ [Instr.addi sp sp (slot frameSize)]) rfl (by decide) k w
      simpa using this) finishBody_straight ?_
  obtain ⟨memR, loaded, kept⟩ := reloads_spec (base := sp) (slots := savedSlots) (m := M)
    (by decide) (by decide) (by decide)
  refine Reaches.now ⟨fetch_finish (k := 14) (by decide), ?_, ?_, ?_⟩
  · simp only [execBlock_append, execBlock_cons, execBlock_nil, Instr.run]
    intro a below
    simp only [view, Machine.mem_write, memR, memM]
    have := state.agree a below
    rw [List.take_length] at this
    exact this
  · intro r inside
    simp only [execBlock_append, execBlock_cons, execBlock_nil, Instr.run]
    have savedReg (s : Reg × Nat) (mem : s ∈ savedSlots) :
        (execBlock (reloads sp savedSlots) M).read s.1 = m0.read s.1 := by
      rw [loaded s mem, steadyM.stack]
      exact steadyM.savedStored s mem
    by_cases isSp : r = sp
    · subst isSp
      rw [Machine.read_write_self (by decide), kept sp (by decide), steadyM.stack,
        show (slot frameSize).signExtend 64 = BitVec.ofNat 64 frameSize by decide, base,
        BitVec.sub_add_cancel]
    rw [Machine.read_write_ne isSp]
    by_cases isGp : r = 3
    · subst isGp
      rw [kept 3 (by decide), steadyM.globalPointer]
    by_cases isTp : r = 4
    · subst isTp
      rw [kept 4 (by decide), steadyM.threadPointer]
    have saved : r ∈ savedSlots.map Prod.fst := by
      revert inside isSp isGp isTp
      revert r
      decide
    obtain ⟨s, mem, rfl⟩ := List.mem_map.mp saved
    exact savedReg s mem
  · intro y frame area
    simp only [execBlock_append, execBlock_cons, execBlock_nil, Instr.run, Machine.mem_write, memR, memM]
    exact steady.untouched y frame area

/--
The executor runs the whole plan.

It returns with the scratch area holding what the plan computes from it, the caller's registers
restored, and memory outside its frame and the scratch area untouched.
-/
theorem exec_correct (m0 : Machine) {steps : List Step} {size : Nat} (valid : Valid m0 steps size) :
    Reaches program ⟨m0, 0⟩ fun s => returned program s ∧
      Agree (view s.m (scratch m0)) (runPlan steps (view m0 (scratch m0))) size ∧
      (∀ r ∈ preserved, s.m.read r = m0.read r) ∧
      ∀ y, ¬Within y (base m0) frameSize → ¬Within y (scratch m0) size → s.m.mem y = m0.mem y :=
  (entry_reaches valid).bind fun s ⟨pc, start⟩ => by
    rw [show s = ⟨s.m, stepHead⟩ by rw [← pc]]
    exact (step_loop valid _ 0 s.m rfl start).bind fun s' ⟨pc', finished⟩ => by
      rw [show s' = ⟨s'.m, stepHead⟩ by rw [← pc']]
      exact exit_reaches valid finished

end Ssz.Asm.Exec
