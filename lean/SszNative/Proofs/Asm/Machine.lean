import SszNative.Asm.Machine
import SszNative.Proofs.Asm.Run

/-!
A routine that makes no call runs inside the whole machine as it runs alone, up to its return.

Every kernel is proved as a routine alone.
This lifts each such proof into the image, where its return then pops the caller's address.
-/

namespace Ssz.Native.Asm

/-- Whether a routine calls no other routine. -/
def Leaf (program : Array Instr) : Prop :=
  ∀ i ∈ program.toList, ∀ name, i ≠ .call name

/-- Away from calls and returns, the whole machine steps as the routine does alone. -/
theorem image_step_plain (image : Image) (r : Nat) (s : State) (i : Instr)
    (fetch : (image.code r)[s.pc]? = some i) (notCall : ∀ name, i ≠ .call name) (notRet : i ≠ .ret) :
    image.step ⟨r, s⟩ = ⟨r, step (image.code r) s⟩ := by
  -- The step dispatches on the instruction, and only calls and returns leave the routine's own step.
  simp only [Image.step]
  by_cases running : s.status = .running
  · simp only [running, bne_self_eq_false, Bool.false_eq_true, if_false, fetch]
    cases i <;> simp_all
  · -- A stopped machine stays put, and so does a stopped routine.
    simp [running, step]

/-- Only a return instruction makes a routine alone return. -/
theorem step_returned (program : Array Instr) (s : State) (i : Instr) (fetch : program[s.pc]? = some i)
    (notRet : i ≠ .ret) (running : s.status = .running) : (step program s).status ≠ .returned := by
  -- Every other instruction runs on, branches, or faults.
  simp only [step, running, bne_self_eq_false, Bool.false_eq_true, if_false, fetch]
  cases i <;> simp_all <;> split <;> simp

/--
A routine alone that returns reaches, inside the image, the same return instruction with the same machine.

The whole machine then pops the address its caller pushed.
-/
theorem lift_return (image : Image) (r : Nat) (leaf : Leaf (image.code r)) :
    ∀ (n : Nat) (s : State), s.status = .running → (run (image.code r) n s).status = .returned →
      ∃ k, image.run k ⟨r, s⟩ = ⟨r, { run (image.code r) n s with status := .running }⟩ ∧
        (image.code r)[(run (image.code r) n s).pc]? = some .ret := by
  intro n
  induction n with
  | zero =>
    -- No step taken: the machine is still running, so it has not returned.
    intro s running returned
    simp_all [run]
  | succ n ih =>
    intro s running returned
    -- What sits at the current index decides the first step.
    cases fetch : (image.code r)[s.pc]? with
    | none =>
      -- An index past the routine faults, and a fault never becomes a return.
      have faulted : step (image.code r) s = { s with status := .faulted } := by simp [step, running, fetch]
      simp [run, faulted, run_stopped] at returned
    | some i =>
      by_cases isRet : i = .ret
      · -- The return is the first step: the machine is already there.
        subst isRet
        have stopped : step (image.code r) s = { s with status := .returned } := by simp [step, running, fetch]
        have rest : run (image.code r) (n + 1) s = { s with status := .returned } := by
          simp only [run, stopped]; exact run_stopped _ _ _ (by simp)
        refine ⟨0, ?_, ?_⟩
        · cases s; simp_all [Image.run]
        · simpa [rest] using fetch
      · -- Any other instruction steps alike in both, and the rest follows by induction.
        have notCall : ∀ name, i ≠ .call name := fun name h =>
          leaf i (by rw [← Array.getElem?_toList] at fetch; exact List.mem_of_getElem? fetch) name h
        have next := image_step_plain image r s i fetch notCall isRet
        rw [run] at returned ⊢
        have still : (step (image.code r) s).status = .running := by
          cases stepped : (step (image.code r) s).status with
          | running => rfl
          | returned => exact absurd stepped (step_returned _ s i fetch isRet running)
          | faulted =>
            -- A fault stops the routine for good, so it never returns.
            rw [run_stopped _ _ _ (by simp [stepped]), stepped] at returned
            cases returned
        obtain ⟨k, reach, atRet⟩ := ih (step (image.code r) s) still returned
        exact ⟨k + 1, by rw [Image.run, next, reach], atRet⟩

end Ssz.Native.Asm
