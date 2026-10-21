import SszNative.Asm.Semantics

/-! Running straight-line blocks: a block's steps are its instructions in order. -/

namespace Ssz.Native.Asm

/-- Whether an instruction always passes control to the next one. -/
def Instr.straight : Instr → Bool
  | .jz _ | .jnz _ | .ret => false
  | _ => true

/-- An instruction alone never moves the instruction index. -/
@[simp] theorem exec1_pc (i : Instr) (s : State) : (exec1 i s).pc = s.pc := by
  -- No instruction's own effect touches the index, which only stepping sets.
  cases i <;> rfl

/-- An instruction alone never stops the routine. -/
@[simp] theorem exec1_status (i : Instr) (s : State) : (exec1 i s).status = s.status := by
  -- Only stepping changes whether execution goes on.
  cases i <;> rfl

/-- An empty block leaves the machine as it was. -/
@[simp] theorem exec_nil (s : State) : exec [] s = s := rfl

/-- A block runs its first instruction, then the rest. -/
@[simp] theorem exec_cons (i : Instr) (rest : List Instr) (s : State) :
    exec (i :: rest) s = exec rest (exec1 i s) := rfl

/-- An instruction acts the same whatever the instruction index. -/
theorem exec1_with_pc (i : Instr) (s : State) (pc : Nat) :
    exec1 i { s with pc := pc } = { exec1 i s with pc := pc } := by
  -- The index is carried along untouched.
  cases i <;> rfl

/-- A block acts the same whatever the instruction index. -/
theorem exec_with_pc (body : List Instr) (s : State) (pc : Nat) :
    exec body { s with pc := pc } = { exec body s with pc := pc } := by
  induction body generalizing s with
  | nil => rfl
  | cons i rest ih =>
    have := ih (exec1 i s)
    simp only [exec_cons, exec1_with_pc]
    simpa using this

/-- Two blocks run one after the other. -/
theorem exec_append (a b : List Instr) (s : State) : exec (a ++ b) s = exec b (exec a s) := by
  -- Run the first block, then the second from where it left the machine.
  induction a generalizing s with
  | nil => rfl
  | cons i rest ih => exact ih (exec1 i s)

/-- A block never moves the instruction index. -/
@[simp] theorem exec_pc (body : List Instr) (s : State) : (exec body s).pc = s.pc := by
  induction body generalizing s with
  | nil => rfl
  | cons i rest ih => simp [ih]

/-- A block never stops the routine. -/
@[simp] theorem exec_status (body : List Instr) (s : State) : (exec body s).status = s.status := by
  induction body generalizing s with
  | nil => rfl
  | cons i rest ih => simp [ih]

/-- Steps compose: running m steps then n steps is running m + n steps. -/
theorem run_add (program : Array Instr) (m n : Nat) (s : State) :
    run program (m + n) s = run program n (run program m s) := by
  -- Steps compose: the first m, then the rest.
  induction m generalizing s with
  | zero => simp [run]
  | succ m ih => rw [Nat.add_right_comm, run, ih, run]

/-- A routine that returned or faulted stays where it stopped. -/
theorem run_stopped (program : Array Instr) (n : Nat) (s : State) (stopped : s.status ≠ .running) :
    run program n s = s := by
  -- A routine that returned or faulted stays where it stopped.
  induction n with
  | zero => rfl
  | succ n ih => simp [run, step, stopped, ih]

/-- The step at an index holding a straight-line instruction. -/
theorem step_straight (program : Array Instr) (s : State) (i : Instr) (fetch : program[s.pc]? = some i)
    (straight : i.straight) (running : s.status = .running) :
    step program s = { exec1 i s with pc := s.pc + 1 } := by
  unfold step
  cases i <;> simp_all [Instr.straight]

/--
A block of straight-line instructions inside a program runs as the block itself.

The program is the instructions before the block, the block, and those after it.
-/
theorem run_block (program : Array Instr) (pre body post : List Instr)
    (layout : program.toList = pre ++ body ++ post) (straight : ∀ i ∈ body, i.straight)
    (s : State) (tableEntry : s.pc = pre.length) (running : s.status = .running) :
    run program body.length s = { exec body s with pc := pre.length + body.length } := by
  induction body generalizing s pre with
  | nil => cases s; simp_all [run]
  | cons i rest ih =>
    -- The block's first instruction sits right after the prefix.
    have fetch : program[s.pc]? = some i := by
      rw [tableEntry, ← Array.getElem?_toList, layout]
      simp
    rw [List.length_cons, Nat.add_comm, run_add]
    simp only [run]
    rw [step_straight program s i fetch (straight i (by simp)) running]
    -- The rest of the block follows a prefix one instruction longer.
    have := ih (pre ++ [i]) (by simp [layout]) (fun j h => straight j (by simp [h]))
      { exec1 i s with pc := s.pc + 1 } (by simp [tableEntry]) (by simp [running])
    rw [this, exec_cons, exec_with_pc]
    simp only [List.length_append, List.length_singleton]
    congr 1
    omega

end Ssz.Native.Asm
