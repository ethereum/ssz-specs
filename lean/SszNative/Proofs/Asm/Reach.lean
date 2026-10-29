import SszNative.Proofs.Asm.Machine

/-!
Runs of the whole machine inside one routine: one instruction, a straight block, and their composition.
-/
open Ssz.Native.Asm

namespace Ssz.Native.Asm

/-- Runs compose. -/
theorem Image.run_add (image : Image) (a b : Nat) (m : Machine) :
    image.run (a + b) m = image.run b (image.run a m) := by
  induction a generalizing m with
  | zero => simp [Image.run]
  | succ a ih => rw [Nat.add_right_comm, Image.run, ih, Image.run]

/-- The machine goes from one state to another in some steps, inside one routine. -/
def Reaches (image : Image) (r : Nat) (s s' : State) : Prop :=
  ∃ k, image.run k ⟨r, s⟩ = ⟨r, s'⟩

/-- Every state reaches itself, in no steps. -/
theorem Reaches.refl (image : Image) (r : Nat) (s : State) : Reaches image r s s := ⟨0, rfl⟩

/-- Reaching composes: the steps of one run, then those of the next. -/
theorem Reaches.trans {image : Image} {r : Nat} {s₁ s₂ s₃ : State} (h₁ : Reaches image r s₁ s₂)
    (h₂ : Reaches image r s₂ s₃) : Reaches image r s₁ s₃ := by
  obtain ⟨a, ha⟩ := h₁; obtain ⟨b, hb⟩ := h₂
  exact ⟨a + b, by rw [Image.run_add, ha, hb]⟩

/-- One step of an instruction that neither calls, returns, nor branches. -/
theorem Reaches.straight (image : Image) (r : Nat) (s : State) (i : Instr)
    (fetch : (image.code r)[s.pc]? = some i) (straight : i.straight) (running : s.status = .running) :
    Reaches image r s { exec1 i s with pc := s.pc + 1 } := by
  refine ⟨1, ?_⟩
  have notCall : ∀ name, i ≠ .call name := by intro name h; subst h; simp [Instr.straight] at straight
  have notRet : i ≠ .ret := by intro h; subst h; simp [Instr.straight] at straight
  simp only [Image.run, image_step_plain image r s i fetch notCall notRet,
    step_straight _ s i fetch straight running]

/-- The instruction at an index, read from the layout the routine was built from. -/
theorem fetch_at (image : Image) (r : Nat) (pre post : List Instr) (i : Instr)
    (layout : (image.code r).toList = pre ++ i :: post) : (image.code r)[pre.length]? = some i := by
  rw [← Array.getElem?_toList, layout]; simp

/-- A block of straight instructions runs as the block itself. -/
theorem Reaches.block (image : Image) (r : Nat) (pre body post : List Instr)
    (layout : (image.code r).toList = pre ++ body ++ post) (straight : ∀ i ∈ body, i.straight)
    (s : State) (at_ : s.pc = pre.length) (running : s.status = .running) :
    Reaches image r s { exec body s with pc := pre.length + body.length } := by
  induction body generalizing s pre with
  | nil => cases s; simp_all [Reaches.refl]
  | cons i rest ih =>
    have fetch : (image.code r)[s.pc]? = some i := by
      rw [at_]; exact fetch_at image r pre (rest ++ post) i (by simpa using layout)
    refine (Reaches.straight image r s i fetch (straight i (by simp)) running).trans ?_
    have := ih (pre ++ [i]) (by simpa using layout) (fun j h => straight j (by simp [h]))
      { exec1 i s with pc := s.pc + 1 } (by simp [at_]) (by simp [running])
    rw [exec_cons, ← exec_with_pc] at *
    simp only [List.length_append, List.length_cons] at this ⊢
    rw [show pre.length + (rest.length + 1) = pre.length + 1 + rest.length by omega]
    simpa [exec_with_pc] using this

end Ssz.Native.Asm
