import Asm.Root.Compile
import Asm.Root.Proof

/-! The whole plan: zero subtrees, then the type's own steps, ending with its SSZ root. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Root

open Ssz
open Ssz.Asm.Merkle (zeroAt)

attribute [local irreducible] Ssz.combine

/-- The zero-subtree steps write their table, in slots from the base up. -/
theorem zeroSteps_spec (zeros : Nat) : ∀ depth (s : Scratch),
    WritesAbove (zeroSteps zeros depth) zeros ∧ WritesBelow (zeroSteps zeros depth) (zeros + 32 * (depth + 1)) ∧
      ZeroTable (runPlan (zeroSteps zeros depth) s) zeros depth
  | 0, s => by
    refine ⟨by simp [zeroSteps, WritesAbove, Step.dst], by simp [zeroSteps, WritesBelow, Step.dst], ?_⟩
    intro k within
    have : k = 0 := by omega
    subst this
    have chunk := chunk_holds (dst := zeros) (src := 0) (len := 0) (s := s)
    simp only [zeroSteps, runPlan, List.foldl_cons, List.foldl_nil, Nat.mul_zero, Nat.add_zero]
    unfold Holds at chunk ⊢
    rw [chunk]
    simp [zeroAt, zeroRoot, zeroChunk, bytesPerChunk]
    rfl
  | depth + 1, s => by
    obtain ⟨above, below, table⟩ := zeroSteps_spec zeros depth s
    have last : WritesAbove [Step.hash (zeros + 32 * (depth + 1)) (zeros + 32 * depth) (zeros + 32 * depth)]
        (zeros + 32 * (depth + 1)) := writesAbove_singleton (by simp [Step.dst])
    refine ⟨?_, ?_, ?_⟩
    · intro t mem
      rcases List.mem_append.mp mem with mem | mem
      · exact above t mem
      · simp at mem; subst mem; simp [Step.dst]
    · intro t mem
      rcases List.mem_append.mp mem with mem | mem
      · have := below t mem; omega
      · simp at mem; subst mem; simp [Step.dst]; omega
    · intro k within
      simp only [zeroSteps]
      rw [runPlan_append]
      by_cases top : k = depth + 1
      · subst top
        have next := hash_holds (dst := zeros + 32 * (depth + 1)) (table depth (Nat.le_refl _))
          (table depth (Nat.le_refl _))
        exact next
      · exact holds_below last (by omega) (table k (by omega))

/-- Running a type's plan over its encoding leaves the type's root in the root slot. -/
theorem planFor_spec {d : Desc} (p : plain d = true) {bytes : Bytes} (sized : bytes.size = width d)
    {s : Scratch} (enc : Encodes s 0 bytes) :
    Holds (runPlan (planFor d).steps s) (planFor d).root (rootOf d bytes) := by
  obtain ⟨above, _, table⟩ := zeroSteps_spec (width d) (treeDepth d) s
  have body := compile_spec (width d) d p 0 (width d + 32 * (treeDepth d + 1)) (treeDepth d) bytes
    (runPlan (zeroSteps (width d) (treeDepth d)) s)
    (encodes_below above (by omega) enc) sized (by omega) table (Nat.le_refl _) (Nat.le_refl _)
  simp only [planFor]
  rw [runPlan_append]
  exact body.holds

/--
The plan computes the SSZ root: for every value of a plain type, running the plan over its encoding
leaves `hashTreeRoot` in the root slot.
-/
theorem planFor_hashTreeRoot {d : Desc} (p : plain d = true) {value : Value} {bytes : Bytes}
    (encoded : serialize d value = .ok bytes) {s : Scratch} (enc : Encodes s 0 bytes) :
    hashTreeRoot d value = .ok (readSlot (runPlan (planFor d).steps s) (planFor d).root) := by
  have sized := serialize_size d p value bytes encoded
  rw [planFor_spec p sized enc]
  have positive := d.nesting_pos
  rw [← hashTreeRootAt_eq_hashTreeRoot d value (d.nesting - 1 + 1) (by omega)]
  exact root_plain d p (d.nesting - 1) (by omega) value bytes encoded

end Ssz.Asm.Root
