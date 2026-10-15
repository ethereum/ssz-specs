import Asm.Root.PlanMain

/-! Every step of a compiled plan reads only bytes below the slot it writes. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Root

open Ssz

/-- A step reads only bytes below its own slot, and a chunk copies at most a slot's worth. -/
def Step.readsBelow : Step → Prop
  | chunk dst src len => src + len ≤ dst ∧ len ≤ 32
  | hash dst left right => left + 32 ≤ dst ∧ right + 32 ≤ dst

/-- Every step of a list reads below its own slot. -/
def ReadsBelow (steps : List Step) : Prop :=
  ∀ step ∈ steps, step.readsBelow

theorem readsBelow_append {first second : List Step} (a : ReadsBelow first) (b : ReadsBelow second) :
    ReadsBelow (first ++ second) := fun t mem => by
  rcases List.mem_append.mp mem with mem | mem
  · exact a t mem
  · exact b t mem

theorem pairSteps_reads {fill : Nat} (free : Nat) (nodes : List Nat) :
    (∀ o ∈ nodes, o + 32 ≤ free) → fill + 32 ≤ free → ReadsBelow (pairSteps fill free nodes).1 := by
  induction free, nodes using pairSteps.induct with
  | case1 free => intro _ _; simp [pairSteps, ReadsBelow]
  | case2 free node =>
    intro low lowFill t mem
    simp [pairSteps] at mem
    subst mem
    exact ⟨low node (by simp), lowFill⟩
  | case3 free left right rest ih =>
    intro low lowFill t mem
    simp only [pairSteps, List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact ⟨low left (by simp), low right (by simp)⟩
    · exact ih (fun o mem => by have := low o (by simp [mem]); omega) (by omega) t mem

/-- Where a level's parents go: consecutive slots from the free offset. -/
theorem pairSteps_shape {fill : Nat} (free : Nat) (nodes : List Nat) :
    (pairSteps fill free nodes).2.length = (nodes.length + 1) / 2 ∧
      ∀ o ∈ (pairSteps fill free nodes).2, free ≤ o ∧ o + 32 ≤ free + 32 * ((nodes.length + 1) / 2) := by
  induction free, nodes using pairSteps.induct with
  | case1 free => simp [pairSteps]
  | case2 free node => simp [pairSteps]
  | case3 free left right rest ih =>
    obtain ⟨length, offsets⟩ := ih
    simp only [pairSteps, List.length_cons]
    refine ⟨by rw [length]; omega, ?_⟩
    intro o mem
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · omega
    · have := offsets o mem
      omega

theorem treeSteps_reads (zeros : Nat) (remaining height : Nat) (nodes : List Nat) (free : Nat) :
    (∀ o ∈ nodes, o + 32 ≤ free) → zeros + 32 * (height + remaining + 1) ≤ free →
      ReadsBelow (treeSteps zeros remaining height nodes free).steps := by
  induction remaining, height, nodes, free using treeSteps.induct zeros with
  | case1 height nodes free => intro _ _; simp [treeSteps, ReadsBelow]
  | case2 remaining height nodes free lvl ih =>
    intro low zerosLow
    simp only [lvl] at ih
    obtain ⟨length, offsets⟩ := pairSteps_shape (fill := zeros + 32 * height) free nodes
    simp only [treeSteps]
    apply readsBelow_append
    · exact pairSteps_reads free nodes low (by
        have : 32 * height + 32 ≤ 32 * (height + (remaining + 1) + 1) := by omega
        omega)
    · exact ih (fun o mem => by have := offsets o mem; omega) (by omega)

theorem packedSteps_reads {zeros src size free depth : Nat} (low : src + size ≤ free)
    (deep : depthFor ((size + 31) / 32) ≤ depth) (zerosLow : zeros + 32 * (depth + 1) ≤ free) :
    ReadsBelow (packedSteps zeros src size free).steps := by
  simp only [packedSteps]
  apply readsBelow_append
  · intro t mem
    simp only [chunkSteps, List.mem_map, List.mem_range] at mem
    obtain ⟨i, below, rfl⟩ := mem
    simp only [Step.readsBelow]
    omega
  · exact treeSteps_reads zeros _ 0 _ _ (fun o mem => by
      simp only [chunkSlots, List.mem_map, List.mem_range] at mem
      obtain ⟨i, below, rfl⟩ := mem
      omega) (by
      have : 32 * (0 + depthFor ((size + 31) / 32) + 1) ≤ 32 * (depth + 1) := by omega
      omega)

/-- A tree's root lies below the free offset it hands on, which only grows. -/
theorem treeSteps_shape (zeros : Nat) (remaining height : Nat) (nodes : List Nat) (free : Nat) :
    (∀ o ∈ nodes, o + 32 ≤ free) → zeros + 32 * (height + remaining + 1) ≤ free →
      free ≤ (treeSteps zeros remaining height nodes free).free ∧
        (treeSteps zeros remaining height nodes free).root + 32 ≤ (treeSteps zeros remaining height nodes free).free := by
  induction remaining, height, nodes, free using treeSteps.induct zeros with
  | case1 height nodes free =>
    intro low zerosLow
    simp only [treeSteps]
    refine ⟨Nat.le_refl _, ?_⟩
    cases nodes with
    | nil => simp; omega
    | cons o _ => simpa using low o (by simp)
  | case2 remaining height nodes free lvl ih =>
    intro low zerosLow
    simp only [lvl] at ih
    obtain ⟨length, offsets⟩ := pairSteps_shape (fill := zeros + 32 * height) free nodes
    obtain ⟨grows, root⟩ := ih (fun o mem => by have := offsets o mem; omega) (by omega)
    simp only [treeSteps]
    exact ⟨by omega, root⟩

/-- What a type's fragment does, whatever bytes it roots: it reads below and writes above. -/
structure Shaped (free : Nat) (out : Emitted) : Prop where
  /-- Steps read below their own slots. -/
  reads : ReadsBelow out.steps
  /-- The free offset only grows. -/
  grows : free ≤ out.free
  /-- The root lies below the free offset handed on. -/
  rootBelow : out.root + 32 ≤ out.free

/-- What a fragment for several nodes does, whatever bytes it roots. -/
structure ShapedMany (free : Nat) (out : EmittedMany) : Prop where
  /-- Steps read below their own slots. -/
  reads : ReadsBelow out.steps
  /-- The free offset only grows. -/
  grows : free ≤ out.free
  /-- Every root lies below the free offset handed on. -/
  rootsBelow : ∀ o ∈ out.roots, o + 32 ≤ out.free

theorem shaped_cons {free : Nat} {first : Emitted} {rest : EmittedMany} (head : Shaped free first)
    (tail : ShapedMany first.free rest) :
    ShapedMany free ⟨first.steps ++ rest.steps, first.root :: rest.roots, rest.free⟩ where
  reads := readsBelow_append head.reads tail.reads
  grows := Nat.le_trans head.grows tail.grows
  rootsBelow := fun o mem => by
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · have := head.rootBelow; have := tail.grows; dsimp only; omega
    · exact tail.rootsBelow o mem

theorem tree_shaped {zeros depth bound free : Nat} {each : EmittedMany} (shaped : ShapedMany free each)
    (deep : depth ≤ bound) (zerosLow : zeros + 32 * (bound + 1) ≤ free) :
    Shaped free ⟨each.steps ++ (treeSteps zeros depth 0 each.roots each.free).steps,
      (treeSteps zeros depth 0 each.roots each.free).root, (treeSteps zeros depth 0 each.roots each.free).free⟩ := by
  have zl : zeros + 32 * (0 + depth + 1) ≤ each.free := by
    have := shaped.grows
    have : 32 * (0 + depth + 1) ≤ 32 * (bound + 1) := by omega
    omega
  obtain ⟨grows, root⟩ := treeSteps_shape zeros depth 0 each.roots each.free shaped.rootsBelow zl
  exact ⟨readsBelow_append shaped.reads (treeSteps_reads zeros depth 0 each.roots each.free shaped.rootsBelow zl),
    by have := shaped.grows; dsimp only; omega, root⟩

theorem packed_shaped {zeros src size free depth : Nat} (low : src + size ≤ free)
    (deep : depthFor ((size + 31) / 32) ≤ depth) (zerosLow : zeros + 32 * (depth + 1) ≤ free) :
    Shaped free (packedSteps zeros src size free) := by
  have zl : zeros + 32 * (0 + depthFor ((size + 31) / 32) + 1) ≤ free + 32 * ((size + 31) / 32) := by
    have : 32 * (0 + depthFor ((size + 31) / 32) + 1) ≤ 32 * (depth + 1) := by omega
    omega
  obtain ⟨grows, root⟩ := treeSteps_shape zeros _ 0 (chunkSlots size free) (free + 32 * ((size + 31) / 32))
    (fun o mem => by
      simp only [chunkSlots, List.mem_map, List.mem_range] at mem
      obtain ⟨i, below, rfl⟩ := mem
      omega) zl
  exact ⟨packedSteps_reads low deep zerosLow, by simp only [packedSteps]; omega, root⟩

theorem compileEach_shaped {zeros : Nat} {element : Desc}
    (ih : ∀ src free depth, src + width element ≤ free → treeDepth element ≤ depth →
      zeros + 32 * (depth + 1) ≤ free → Shaped free (compile zeros element src free)) :
    ∀ n src free depth, src + width element * n ≤ free → treeDepth element ≤ depth →
      zeros + 32 * (depth + 1) ≤ free → ShapedMany free (compileEach zeros element n src free)
  | 0, _, _, _, _, _, _ => ⟨by simp [compileEach, ReadsBelow], by simp [compileEach], by simp [compileEach]⟩
  | n + 1, src, free, depth, low, deep, zerosLow => by
    rw [Nat.mul_succ] at low
    have first := ih src free depth (by omega) deep zerosLow
    have rest := compileEach_shaped ih n (src + width element) (compile zeros element src free).free depth
      (by have := first.grows; omega) deep (by have := first.grows; omega)
    simp only [compileEach]
    exact shaped_cons first rest

mutual

theorem compile_shaped (zeros : Nat) : (d : Desc) → plain d = true → ∀ src free depth,
    src + width d ≤ free → treeDepth d ≤ depth → zeros + 32 * (depth + 1) ≤ free →
    Shaped free (compile zeros d src free)
  | .bool, _, src, free, depth, low, deep, zerosLow
  | .uint _, _, src, free, depth, low, deep, zerosLow
  | .byteVector _, _, src, free, depth, low, deep, zerosLow
  | .bitVector _, _, src, free, depth, low, deep, zerosLow => by
    simp only [compile]
    exact packed_shaped low deep zerosLow
  | .vector element n, p, src, free, depth, low, deep, zerosLow => by
    simp only [plain] at p
    by_cases basic : element.isBasic
    · simp only [treeDepth, basic, if_true] at deep
      simp only [compile, basic, if_true]
      exact packed_shaped low deep zerosLow
    · simp only [treeDepth, basic, if_false, Bool.false_eq_true, Nat.max_le] at deep
      simp only [compile, basic, if_false, Bool.false_eq_true]
      exact tree_shaped (compileEach_shaped (fun src free depth => compile_shaped zeros element p src free depth)
        n src free depth low deep.2 zerosLow) deep.1 zerosLow
  | .container names fields, p, src, free, depth, low, deep, zerosLow => by
    simp only [plain] at p
    simp only [treeDepth, Nat.max_le] at deep
    simp only [compile]
    exact tree_shaped (compileFields_shaped zeros fields p src free depth low deep.2 zerosLow) deep.1 zerosLow
  | .byteList _, p, _, _, _, _, _, _ | .bitList _, p, _, _, _, _, _, _
  | .progressiveBitList _, p, _, _, _, _, _, _ | .list _ _, p, _, _, _, _, _, _
  | .progressiveList _ _, p, _, _, _, _, _, _ | .progressiveContainer _ _ _, p, _, _, _, _, _, _
  | .compatibleUnion _ _, p, _, _, _, _, _, _ => by simp [plain] at p
termination_by structural d => d

theorem compileFields_shaped (zeros : Nat) : (fields : List Desc) → plainAll fields = true →
    ∀ src free depth, src + (widths fields).sum ≤ free → treeDepthAll fields ≤ depth →
    zeros + 32 * (depth + 1) ≤ free → ShapedMany free (compileFields zeros fields src free)
  | [], _, _, _, _, _, _, _ => ⟨by simp [compileFields, ReadsBelow], by simp [compileFields],
      by simp [compileFields]⟩
  | field :: fields, p, src, free, depth, low, deep, zerosLow => by
    simp only [plainAll, Bool.and_eq_true] at p
    simp only [treeDepthAll, Nat.max_le] at deep
    simp only [widths, List.sum_cons] at low
    have first := compile_shaped zeros field p.1 src free depth (by omega) deep.1 zerosLow
    have rest := compileFields_shaped zeros fields p.2 (src + width field) (compile zeros field src free).free
      depth (by have := first.grows; omega) deep.2 (by have := first.grows; omega)
    simp only [compileFields]
    exact shaped_cons first rest
termination_by structural fields => fields

end

/-- The zero table: each entry hashes the entry just below it, and the zero chunk copies nothing. -/
theorem zeroSteps_reads (zeros : Nat) : ∀ depth, ReadsBelow (zeroSteps zeros depth)
  | 0 => by
    intro t mem
    simp [zeroSteps] at mem
    subst mem
    simp [Step.readsBelow]
  | k + 1 => by
    intro t mem
    rcases List.mem_append.mp mem with mem | mem
    · exact zeroSteps_reads zeros k t mem
    · simp at mem
      subst mem
      simp only [Step.readsBelow]
      omega

/-- Every step of a type's plan reads below its own slot. -/
theorem planFor_reads {d : Desc} (p : plain d = true) : ReadsBelow (planFor d).steps := by
  simp only [planFor]
  apply readsBelow_append
  · exact zeroSteps_reads _ _
  · exact (compile_shaped (width d) d p 0 _ (treeDepth d) (by omega) (Nat.le_refl _) (Nat.le_refl _)).reads

end Ssz.Asm.Root
