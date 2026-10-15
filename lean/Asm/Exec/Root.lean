import Asm.Exec.Main

/-! The executor over a type's compiled plan: the SSZ root of a value, from its encoding. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Exec

open Ssz
open Ssz.Asm.Root (Step Agree runPlan readSlot planFor plain WritesBelow)
open Ssz.Asm.Sha256 (a2)

/-- Every step of a type's plan writes inside its scratch area, and so does its root. -/
theorem planFor_bounds {d : Desc} (p : plain d = true) :
    WritesBelow (planFor d).steps (planFor d).free ∧ (planFor d).root + 32 ≤ (planFor d).free := by
  -- Any encoding will do, since where a plan writes does not depend on the bytes.
  obtain ⟨above, below, table⟩ := Root.zeroSteps_spec (Root.width d) (Root.treeDepth d) fun _ => 0
  have body := Root.compile_spec (Root.width d) d p 0 (Root.width d + 32 * (Root.treeDepth d + 1))
    (Root.treeDepth d) (Array.replicate (Root.width d) 0) (runPlan (Root.zeroSteps (Root.width d) (Root.treeDepth d)) fun _ => 0)
    (fun i within => by
      simp only [Array.size_replicate] at within
      rw [Root.runPlan_below above (by omega)]
      simp) (by simp) (by omega) table (Nat.le_refl _) (Nat.le_refl _)
  refine ⟨?_, body.rootBelow⟩
  intro t mem
  simp only [planFor] at mem ⊢
  rcases List.mem_append.mp mem with mem | mem
  · have := below t mem
    have := body.grows
    omega
  · exact body.below t mem

/-- Where the plan, the scratch area, and the frame sit, as a caller lays them out. -/
structure Placed (m0 : Machine) (d : Desc) : Prop where
  /-- The step count argument is the plan's length. -/
  count : (m0.read a2).toNat = (planFor d).steps.length
  /-- The plan's words are in memory, four per step. -/
  encoded : ∀ k (within : k < (planFor d).steps.length) j, j < 4 →
    m0.load (planAddr m0 + BitVec.ofNat 64 (32 * k + 8 * j)) 8 =
      BitVec.ofNat 64 (stepWord (planFor d).steps[k] j)
  /-- The scratch area is comfortably small. -/
  small : (planFor d).free < 2 ^ 60
  /-- The plan is comfortably small. -/
  short : 32 * (planFor d).steps.length < 2 ^ 60
  /-- The scratch area and the frame share no byte. -/
  scratchFrame : Disjoint (scratch m0) (planFor d).free (base m0) frameSize
  /-- The plan and the frame share no byte. -/
  planFrame : Disjoint (planAddr m0) (32 * (planFor d).steps.length) (base m0) frameSize
  /-- The plan and the scratch area share no byte. -/
  planScratch : Disjoint (planAddr m0) (32 * (planFor d).steps.length) (scratch m0) (planFor d).free

/--
The executor computes `hashTreeRoot` for every plain type.

Given a value's encoding at the start of the scratch area and the type's plan in memory, the
routine returns with the value's SSZ root in the plan's root slot.
-/
theorem hashTreeRoot_correct (m0 : Machine) {d : Desc} (p : plain d = true) {value : Value} {bytes : Bytes}
    (encoded : serialize d value = .ok bytes) (placed : Placed m0 d)
    (input : ∀ i (within : i < bytes.size), m0.mem (scratch m0 + BitVec.ofNat 64 i) = bytes[i].toBitVec) :
    Reaches program ⟨m0, 0⟩ fun s => returned program s ∧
      hashTreeRoot d value = .ok (s.m.bytes (scratch m0 + BitVec.ofNat 64 (planFor d).root) 32).data ∧
      (∀ r ∈ preserved, s.m.read r = m0.read r) ∧
      ∀ y, ¬Within y (base m0) frameSize → ¬Within y (scratch m0) (planFor d).free → s.m.mem y = m0.mem y := by
  have bounds := planFor_bounds p
  have valid : Valid m0 (planFor d).steps (planFor d).free :=
    ⟨placed.count, placed.encoded, Root.planFor_reads p, bounds.1, placed.small, placed.short,
      placed.scratchFrame, placed.planFrame, placed.planScratch⟩
  refine (exec_correct m0 valid).bind fun s ⟨ret, agree, regs, mem⟩ => Reaches.now ⟨ret, ?_, regs, mem⟩
  rw [bytes_view, Root.readSlot_congr agree bounds.2]
  exact Root.planFor_hashTreeRoot p encoded fun i within => by
    simp only [view, Nat.zero_add]
    rw [input i within]

end Ssz.Asm.Exec
