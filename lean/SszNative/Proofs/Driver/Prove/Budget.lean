import SszNative.Branch
import SszNative.Proofs.Root.Record
import Ssz.Proofs.Codec.Admits

/-!
The Lean walk to a node reads the same answer at every budget that covers the type's nesting.

The drivers walk with no budget at all, so this is what ties them to the walk with any budget large enough.
Each step into a value under a tree spends one unit, and that value nests one level less than its tree.
-/

namespace Ssz.Native.Driver.ProveProof

open Ssz Ssz.Native

/-- Every value a layout lists under its tree nests at most a number of levels. -/
def Within (n : Nat) (layout : EncodedLayout) : Prop :=
  ∀ slots, layout.leaves = .nested slots → ∀ i d s e, slots.at i = some (some (d, s, e)) → d.nesting ≤ n

/-- A field placed at a position of a progressive struct is one of the fields placed. -/
theorem placeFields_mem : ∀ (active : List Bool) (fields : List (Desc × Nat × Nat)) (field : Desc × Nat × Nat),
    some field ∈ placeFields active fields → field ∈ fields
  | [], _, _, placed => by simp [placeFields] at placed
  | false :: active, fields, field, placed => by
    simp only [placeFields, List.mem_cons, reduceCtorEq, false_or] at placed
    exact placeFields_mem active fields field placed
  | true :: active, first :: fields, field, placed => by
    simp only [placeFields, List.mem_cons, Option.some.injEq] at placed
    rcases placed with same | later
    · subst same
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (placeFields_mem active fields field later)
  | true :: active, [], field, placed => by
    simp only [placeFields, List.mem_cons, reduceCtorEq, false_or] at placed
    exact placeFields_mem active [] field placed

/-- A listed position holding a value holds one of the values listed. -/
theorem listed_mem {slots : List (Option (Desc × Nat × Nat))} {i : Nat} {x : Desc × Nat × Nat}
    (found : (Slots.listed slots).at i = some (some x)) : some x ∈ slots :=
  List.mem_of_getElem? found

/-- The values a sequence lists under its tree are its elements. -/
theorem sequence_within (element : Desc) (b : ByteArray) (start stop count : Nat) (positions : Option Nat)
    (mixin : Option ByteArray) : Within element.nesting (encodedSequence element b start stop count positions mixin) := by
  intro slots laid i d s e found
  simp only [encodedSequence] at laid
  split at laid
  · -- Basic elements are packed, with nothing listed.
    cases laid
  · simp only [EncodedLeaves.nested.injEq] at laid
    subst laid
    simp only [elementSlots] at found
    split at found
    · -- Fixed-size elements are found one width apart.
      simp only [Slots.at] at found
      split at found
      · cases found
        exact Nat.le_refl _
      · cases found
    · -- The others are found through their offsets, each one the element.
      have mem := listed_mem found
      simp only [List.mem_map] at mem
      obtain ⟨_, _, same⟩ := mem
      cases same
      exact Nat.le_refl _

/-- The fields a struct lists under its tree are its own fields. -/
theorem fields_within (fields : List Desc) (ranges : List (Nat × Nat)) :
    ∀ d s e, some (d, s, e) ∈ (fields.zip ranges).map some → d.nesting ≤ Desc.deepestNesting fields := by
  intro d s e mem
  simp only [List.mem_map, Option.some.injEq] at mem
  obtain ⟨_, inside, same⟩ := mem
  subst same
  exact nesting_le_deepest fields d (List.of_mem_zip inside).1

/-- The values any layout lists under its tree nest one level less than the type. -/
theorem layoutOf_within (d : Desc) (b : ByteArray) (start stop : Nat) (layout : EncodedLayout)
    (laid : layoutOf d b start stop = .ok layout) : Within (d.nesting - 1) layout := by
  intro slots leaves i d' s e found
  cases d with
  | vector element length =>
    simp only [layoutOf, Except.ok.injEq] at laid
    subst laid
    have := sequence_within element b start stop _ _ _ slots leaves i d' s e found
    simp only [Desc.nesting]
    omega
  | list element limit =>
    simp only [layoutOf, Except.ok.injEq] at laid
    subst laid
    have := sequence_within element b start stop _ _ _ slots leaves i d' s e found
    simp only [Desc.nesting]
    omega
  | progressiveList element limit =>
    simp only [layoutOf, Except.ok.injEq] at laid
    subst laid
    have := sequence_within element b start stop _ _ _ slots leaves i d' s e found
    simp only [Desc.nesting]
    omega
  | container names fields =>
    simp only [layoutOf, bind, Except.bind, pure, Except.pure] at laid
    split at laid
    · cases laid
    · cases laid
      simp only [EncodedLeaves.nested.injEq] at leaves
      subst leaves
      have := fields_within fields _ d' s e (listed_mem found)
      simp only [Desc.nesting]
      omega
  | progressiveContainer active names fields =>
    simp only [layoutOf, bind, Except.bind, pure, Except.pure] at laid
    split at laid
    · cases laid
    · cases laid
      simp only [EncodedLeaves.nested.injEq] at leaves
      subst leaves
      -- A placed field is one of the struct's fields with its range.
      have placed := placeFields_mem active _ _ (listed_mem found)
      have := fields_within fields _ d' s e (List.mem_map_of_mem placed)
      simp only [Desc.nesting]
      omega
  | compatibleUnion selectors options =>
    simp only [layoutOf, bind, Except.bind, pure, Except.pure] at laid
    split at laid
    · cases laid
    · rename_i option picked
      cases laid
      simp only [EncodedLeaves.nested.injEq] at leaves
      subst leaves
      -- The one position holds the option picked.
      have mem := listed_mem found
      simp only [List.mem_singleton, Option.some.injEq, Prod.mk.injEq] at mem
      obtain ⟨same, _, _⟩ := mem
      subst same
      have := nesting_le_deepest options _ (Ssz.lookupOption_mem selectors options _ _ picked)
      simp only [Desc.nesting]
      omega
  | bool | uint _ | byteVector _ | byteList _ | bitVector _ | bitList _ | progressiveBitList _ =>
    simp only [layoutOf, Except.ok.injEq] at laid
    subst laid
    cases leaves

/-- Whether the walk reads the same node at a budget and at that budget raised by an amount, for every type it covers. -/
def SameAt (n k : Nat) : Prop :=
  ∀ d, d.nesting ≤ n → ∀ b s e index, nodeRootAt (n + k) d b s e index = nodeRootAt n d b s e index

/-- A step into a bounded subtree reads the same node at both budgets, when the values under it fit the smaller. -/
theorem bounded_budget (n k : Nat) (ih : SameAt n k) (b : ByteArray) (layout : EncodedLayout)
    (within : Within n layout) (index depth leavesFrom capacity : Nat) :
    boundedNode (n + k) b layout index depth leavesFrom capacity =
      boundedNode n b layout index depth leavesFrom capacity := by
  rw [boundedNode, boundedNode]
  split
  · rfl
  · -- Below the subtree, the walk goes on inside one value, which nests within the budget.
    obtain ⟨leaves, limit, mixin⟩ := layout
    cases leaves with
    | packed => rfl
    | nested slots =>
      simp only
      split
      · rename_i d s e found
        exact ih d (within slots rfl _ d s e found) b s e _
      · rfl

/-- A step down a progressive spine reads the same node at both budgets, when the values under it fit the smaller. -/
theorem progressive_budget (n k : Nat) (ih : SameAt n k) (b : ByteArray) (layout : EncodedLayout)
    (within : Within n layout) (index depth start capacity : Nat) :
    progressiveNode (n + k) b layout index depth start capacity =
      progressiveNode n b layout index depth start capacity := by
  rw [progressiveNode, progressiveNode]
  simp only [bounded_budget n k ih b layout within]

/-- Raising a budget that covers the type's nesting changes no node the walk reads. -/
theorem nodeRootAt_raise : ∀ n k, SameAt n k
  | 0, _ => by
    intro d deep
    -- Every type nests at least one level, so no type fits a budget of zero.
    cases d <;> simp [Desc.nesting] at deep
  | n + 1, k => by
    intro d deep b s e index
    have ih := nodeRootAt_raise n k
    rw [show n + 1 + k = n + k + 1 by omega, nodeRootAt, nodeRootAt]
    cases laid : layoutOf d b s e with
    | error _ => rfl
    | ok layout =>
      -- The values under the tree nest within the budget left after the step.
      have within : Within n layout := fun slots leaves i d' s' e' found => by
        have := layoutOf_within d b s e layout laid slots leaves i d' s' e' found
        omega
      simp only [bind, Except.bind, bounded_budget n k ih b layout within,
        progressive_budget n k ih b layout within]

/-- Any two budgets covering the type's nesting read the same node. -/
theorem nodeRootAt_budget (d : Desc) (b : ByteArray) (s e index : Nat) {n n' : Nat} (deep : d.nesting ≤ n)
    (deep' : d.nesting ≤ n') : nodeRootAt n d b s e index = nodeRootAt n' d b s e index := by
  rw [show n = d.nesting + (n - d.nesting) by omega, show n' = d.nesting + (n' - d.nesting) by omega,
    nodeRootAt_raise _ _ d (Nat.le_refl _), nodeRootAt_raise _ _ d (Nat.le_refl _)]

/-- The walk the branch makes, with its budget, reads what the walk with only the type's nesting as budget reads. -/
theorem walkNode_nesting (d : Desc) (b : ByteArray) (index : Nat) :
    nodeRootAt (d.nesting + index) d b 0 b.size index = nodeRootAt d.nesting d b 0 b.size index :=
  nodeRootAt_budget d b 0 b.size index (by omega) (Nat.le_refl _)

end Ssz.Native.Driver.ProveProof
