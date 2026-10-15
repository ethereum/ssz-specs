import Asm.Root.PlanProof

/-! The compiled plan of a plain type leaves the type's root in the slot it names. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Root

open Ssz
open Ssz.Asm.Merkle (zeroAt)

attribute [local irreducible] Ssz.combine

theorem encodes_prefix {s : Scratch} {src w : Nat} {bytes : Bytes} (enc : Encodes s src bytes) :
    Encodes s src (bytes.extract 0 w) := by
  intro i within
  simp only [Array.size_extract] at within
  rw [enc i (by omega)]
  simp

theorem encodes_suffix {s : Scratch} {src w : Nat} {bytes : Bytes} (enc : Encodes s src bytes) : Encodes s (src + w) (bytes.extract w bytes.size) := by
  intro i within
  simp only [Array.size_extract] at within
  rw [show src + w + i = src + (w + i) by omega, enc (w + i) (by omega)]
  simp

theorem encodes_below {steps : List Step} {free src : Nat} {bytes : Bytes} {s : Scratch}
    (above : WritesAbove steps free) (low : src + bytes.size ≤ free) (enc : Encodes s src bytes) :
    Encodes (runPlan steps s) src bytes := by
  intro i within
  rw [runPlan_below above (by omega)]
  exact enc i within

/-- What a fragment rooting several nodes guarantees. -/
structure RootedMany (s : Scratch) (free : Nat) (out : EmittedMany) (nodes : List Bytes) : Prop where
  /-- Every step writes at or above the free offset it started from. -/
  above : WritesAbove out.steps free
  /-- Every step writes below the free offset it hands on. -/
  below : WritesBelow out.steps out.free
  /-- The free offset only grows. -/
  grows : free ≤ out.free
  /-- Every root slot lies below the free offset handed on. -/
  rootsBelow : ∀ o ∈ out.roots, o + 32 ≤ out.free
  /-- The root slots hold the nodes, in order. -/
  holds : HoldsAll (runPlan out.steps s) out.roots nodes

/-- One fragment followed by others: their roots, the first's surviving the rest. -/
theorem rooted_cons {s : Scratch} {free : Nat} {first : Emitted} {rest : EmittedMany} {node : Bytes}
    {nodes : List Bytes} (head : Rooted s free first node)
    (tail : RootedMany (runPlan first.steps s) first.free rest nodes) :
    RootedMany s free ⟨first.steps ++ rest.steps, first.root :: rest.roots, rest.free⟩ (node :: nodes) where
  above := fun t mem => by
    rcases List.mem_append.mp mem with mem | mem
    · exact head.above t mem
    · have := tail.above t mem
      have := head.grows
      omega
  below := fun t mem => by
    rcases List.mem_append.mp mem with mem | mem
    · have := head.below t mem
      have := tail.grows
      dsimp only
      omega
    · exact tail.below t mem
  grows := Nat.le_trans head.grows tail.grows
  rootsBelow := fun o mem => by
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · have := head.rootBelow
      have := tail.grows
      dsimp only
      omega
    · exact tail.rootsBelow o mem
  holds := by
    rw [runPlan_append]
    exact ⟨holds_below tail.above head.rootBelow head.holds, tail.holds⟩

/-- A level of roots folded into a tree of the given depth: its root is the bounded Merkle root. -/
theorem tree_rooted {zeros depth bound : Nat} {s : Scratch} {free : Nat} {each : EmittedMany}
    {nodes : List Bytes} (rooted : RootedMany s free each nodes) (table : ZeroTable s zeros bound)
    (deep : depth ≤ bound) (zerosLow : zeros + 32 * (bound + 1) ≤ free) :
    Rooted s free ⟨each.steps ++ (treeSteps zeros depth 0 each.roots each.free).steps,
      (treeSteps zeros depth 0 each.roots each.free).root, (treeSteps zeros depth 0 each.roots each.free).free⟩
      (subtreeAt nodes.toArray depth 0) := by
  obtain ⟨treeAbove, treeBelow, treeFree, treeRoot, treeHolds⟩ :=
    treeSteps_spec zeros depth 0 each.roots each.free nodes _ rooted.holds rooted.rootsBelow
      (by rw [Nat.zero_add]
          exact zeroTable_mono (zeroTable_below rooted.above zerosLow table) deep)
      (by have := rooted.grows; have : 32 * (depth + 1) ≤ 32 * (bound + 1) := by omega
          omega)
  refine ⟨?_, ?_, ?_, treeRoot, ?_⟩
  · intro t mem
    rcases List.mem_append.mp mem with mem | mem
    · exact rooted.above t mem
    · have := treeAbove t mem
      have := rooted.grows
      omega
  · intro t mem
    rcases List.mem_append.mp mem with mem | mem
    · have := rooted.below t mem
      dsimp only
      omega
    · exact treeBelow t mem
  · have := rooted.grows
    dsimp only
    omega
  · rw [runPlan_append, ← merkleizeFlat_eq_subtreeAt, List.toList_toArray]
    rw [Nat.zero_add] at treeHolds
    exact treeHolds

/-- Consecutive elements, each rooted by its own fragment. -/
theorem compileEach_spec {zeros : Nat} {element : Desc}
    (ih : ∀ src free depth bytes s, Encodes s src bytes → bytes.size = width element →
      src + width element ≤ free → ZeroTable s zeros depth → treeDepth element ≤ depth →
      zeros + 32 * (depth + 1) ≤ free → Rooted s free (compile zeros element src free) (rootOf element bytes)) :
    ∀ n src free depth (bytes : Bytes) s, Encodes s src bytes → bytes.size = width element * n →
      src + width element * n ≤ free → ZeroTable s zeros depth → treeDepth element ≤ depth →
      zeros + 32 * (depth + 1) ≤ free →
      RootedMany s free (compileEach zeros element n src free)
        ((slices (List.replicate n (width element)) bytes).map (rootOf element))
  | 0, src, free, depth, bytes, s, _, _, _, _, _, _ => by
    simp only [compileEach, List.replicate, slices, List.map_nil]
    exact ⟨by simp [WritesAbove], by simp [WritesBelow], Nat.le_refl _, by simp, trivial⟩
  | n + 1, src, free, depth, bytes, s, enc, sized, low, table, deep, zerosLow => by
    rw [Nat.mul_succ] at sized low
    have first := ih src free depth (bytes.extract 0 (width element)) s (encodes_prefix enc)
      (by simp [sized]) (by omega) table deep zerosLow
    have rest := compileEach_spec ih n (src + width element) (compile zeros element src free).free depth
      (bytes.extract (width element) bytes.size) (runPlan (compile zeros element src free).steps s)
      (encodes_below first.above (by simp [sized]; omega) (encodes_suffix enc))
      (by simp [sized])
      (by have := first.grows; omega)
      (zeroTable_below first.above zerosLow table) deep (by have := first.grows; omega)
    simp only [compileEach, List.replicate_succ, slices, List.map_cons]
    exact rooted_cons first rest

mutual

theorem compile_spec (zeros : Nat) : (d : Desc) → plain d = true → ∀ src free depth (bytes : Bytes) s,
    Encodes s src bytes → bytes.size = width d → src + width d ≤ free → ZeroTable s zeros depth →
    treeDepth d ≤ depth → zeros + 32 * (depth + 1) ≤ free →
    Rooted s free (compile zeros d src free) (rootOf d bytes)
  | .bool, _, src, free, depth, bytes, s, enc, sized, low, table, deep, zerosLow
  | .uint _, _, src, free, depth, bytes, s, enc, sized, low, table, deep, zerosLow
  | .byteVector _, _, src, free, depth, bytes, s, enc, sized, low, table, deep, zerosLow
  | .bitVector _, _, src, free, depth, bytes, s, enc, sized, low, table, deep, zerosLow => by
    simp only [compile, rootOf]
    exact packedSteps_spec enc sized low table deep zerosLow
  | .vector element n, p, src, free, depth, bytes, s, enc, sized, low, table, deep, zerosLow => by
    simp only [plain] at p
    by_cases basic : element.isBasic
    · simp only [treeDepth, basic, if_true] at deep
      simp only [compile, rootOf, basic, if_true]
      exact packedSteps_spec enc sized low table deep zerosLow
    · simp only [treeDepth, basic, if_false, Bool.false_eq_true, Nat.max_le] at deep
      simp only [compile, rootOf, basic, if_false, Bool.false_eq_true]
      exact tree_rooted (compileEach_spec (fun src free depth bytes s => compile_spec zeros element p src
        free depth bytes s) n src free depth bytes s enc sized low table deep.2 zerosLow) table deep.1 zerosLow
  | .container names fields, p, src, free, depth, bytes, s, enc, sized, low, table, deep, zerosLow => by
    simp only [plain] at p
    simp only [treeDepth, Nat.max_le] at deep
    simp only [compile, rootOf]
    exact tree_rooted (compileFields_spec zeros fields p src free depth bytes s enc sized low table deep.2
      zerosLow) table deep.1 zerosLow
  | .byteList _, p, _, _, _, _, _, _, _, _, _, _, _ | .bitList _, p, _, _, _, _, _, _, _, _, _, _, _
  | .progressiveBitList _, p, _, _, _, _, _, _, _, _, _, _, _ | .list _ _, p, _, _, _, _, _, _, _, _, _, _, _
  | .progressiveList _ _, p, _, _, _, _, _, _, _, _, _, _, _
  | .progressiveContainer _ _ _, p, _, _, _, _, _, _, _, _, _, _, _
  | .compatibleUnion _ _, p, _, _, _, _, _, _, _, _, _, _, _ => by simp [plain] at p
termination_by structural d => d

theorem compileFields_spec (zeros : Nat) : (fields : List Desc) → plainAll fields = true →
    ∀ src free depth (bytes : Bytes) s,
    Encodes s src bytes → bytes.size = (widths fields).sum → src + (widths fields).sum ≤ free →
    ZeroTable s zeros depth → treeDepthAll fields ≤ depth → zeros + 32 * (depth + 1) ≤ free →
    RootedMany s free (compileFields zeros fields src free) (rootsOf fields (slices (widths fields) bytes))
  | [], _, src, free, depth, bytes, s, _, _, _, _, _, _ => by
    simp only [compileFields, widths, slices, rootsOf]
    exact ⟨by simp [WritesAbove], by simp [WritesBelow], Nat.le_refl _, by simp, trivial⟩
  | field :: fields, p, src, free, depth, bytes, s, enc, sized, low, table, deep, zerosLow => by
    simp only [plainAll, Bool.and_eq_true] at p
    simp only [treeDepthAll, Nat.max_le] at deep
    simp only [widths, List.sum_cons] at sized low
    have first := compile_spec zeros field p.1 src free depth (bytes.extract 0 (width field)) s
      (encodes_prefix enc) (by simp [sized]) (by omega) table deep.1 zerosLow
    have rest := compileFields_spec zeros fields p.2 (src + width field) (compile zeros field src free).free
      depth (bytes.extract (width field) bytes.size) (runPlan (compile zeros field src free).steps s)
      (encodes_below first.above (by simp [sized]; omega) (encodes_suffix enc)) (by simp [sized])
      (by have := first.grows; omega) (zeroTable_below first.above zerosLow table) deep.2
      (by have := first.grows; omega)
    simp only [compileFields, widths, slices, rootsOf]
    exact rooted_cons first rest
termination_by structural fields => fields

end

end Ssz.Asm.Root
