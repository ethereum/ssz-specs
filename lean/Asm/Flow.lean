import Asm.Block

/-! Reasoning about programs with branches: which states a run is guaranteed to reach. -/

namespace Ssz.Asm

/-- Running the program from a state eventually passes through a state the predicate admits. -/
def Reaches (program : Array Instr) (s : Cpu) (post : Cpu → Prop) : Prop :=
  ∃ n, post (runFor program n s)

theorem Reaches.now {program : Array Instr} {s : Cpu} {post : Cpu → Prop} (holds : post s) :
    Reaches program s post :=
  ⟨0, holds⟩

/-- Reaching a midpoint from which the goal is reached reaches the goal. -/
theorem Reaches.bind {program : Array Instr} {s : Cpu} {mid post : Cpu → Prop}
    (first : Reaches program s mid) (rest : ∀ s', mid s' → Reaches program s' post) :
    Reaches program s post := by
  obtain ⟨n, reached⟩ := first
  obtain ⟨k, done⟩ := rest _ reached
  exact ⟨n + k, by rw [runFor_add]; exact done⟩

/-- One instruction, then the rest of the run. -/
theorem Reaches.step {program : Array Instr} {s : Cpu} {post : Cpu → Prop}
    (rest : Reaches program (step program s) post) : Reaches program s post := by
  obtain ⟨n, done⟩ := rest
  exact ⟨1 + n, by rw [runFor_add]; exact done⟩

/-- Straight-line code at the program counter, then the rest of the run. -/
theorem Reaches.block {program : Array Instr} {s : Cpu} {post : Cpu → Prop} (code : List Instr)
    (here : ∀ k (within : k < code.length), program[s.pc + k]? = some code[k])
    (straight : ∀ i ∈ code, i.straight)
    (rest : Reaches program ⟨execBlock code s.m, s.pc + code.length⟩ post) :
    Reaches program s post := by
  obtain ⟨n, done⟩ := rest
  exact ⟨code.length + n, by rw [runFor_add, runFor_block code s here straight]; exact done⟩

/-- A single instruction's effect, as one step of the run. -/
theorem step_at {program : Array Instr} {s : Cpu} {i : Instr} (here : program[s.pc]? = some i) :
    step program s = ⟨i.run s.m, i.next s.m s.pc⟩ := by
  simp [step, here]

/-- Straight-line code of a known length at a known index, then the rest of the run. -/
theorem Reaches.run {program : Array Instr} {m : Machine} {start n : Nat} {post : Cpu → Prop}
    (code : List Instr) (length : code.length = n)
    (here : ∀ k (within : k < code.length), program[start + k]? = some code[k])
    (straight : ∀ i ∈ code, i.straight)
    (rest : Reaches program ⟨execBlock code m, start + n⟩ post) : Reaches program ⟨m, start⟩ post := by
  subst length
  exact Reaches.block code here straight rest

/-- One instruction at a known index, then the rest of the run. -/
theorem Reaches.exec {program : Array Instr} {m : Machine} {pc : Nat} {i : Instr} {post : Cpu → Prop}
    (here : program[pc]? = some i) (rest : Reaches program ⟨i.run m, i.next m pc⟩ post) :
    Reaches program ⟨m, pc⟩ post :=
  Reaches.step (by rw [step_at (s := ⟨m, pc⟩) here]; exact rest)

end Ssz.Asm
