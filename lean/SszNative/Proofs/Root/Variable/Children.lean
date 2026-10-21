import SszNative.Proofs.Root.Variable.Ranges

/-! Roots of nested values, one per range, agreeing with the specification's root of each decoded value. -/

namespace Ssz.Native.RootProof

open Ssz Ssz.Native

/-- Whether the root of every valid range of an encoding is the specification's root of the value it holds. -/
def Agrees (d : Desc) : Prop :=
  d.wellFormed = .ok () → ∀ (b : ByteArray) (start stop : Nat) (v : Value), start ≤ stop → stop ≤ b.size →
    Small b → deserialize d (slice b start stop) = .ok v → Ssz.hashTreeRoot d v = .ok (rootOf d b start stop).data

/-- Whether two lists pair up, item by item, under a relation. -/
inductive Each {α : Type} (related : α → ByteArray → Prop) : List α → List ByteArray → Prop where
  /-- Two empty lists. -/
  | nil : Each related [] []
  /-- Related heads, and tails that pair up. -/
  | cons {a : α} {r : ByteArray} {as : List α} {rs : List ByteArray} :
    related a r → Each related as rs → Each related (a :: as) (r :: rs)

/-- Whether each root is the specification's root of the value beside it. -/
def RootedBy (d : Desc) (v : Value) (r : ByteArray) : Prop :=
  Ssz.hashTreeRoot d v = .ok r.data

/-- Elements decoded from ranges have, range by range, the roots read from those ranges. -/
theorem variableRoots_spec (element : Desc) (ih : Agrees element) (sound : element.wellFormed = .ok ())
    (b : ByteArray) (small : Small b) :
    ∀ (ranges : List (Nat × Nat)) (values : List Value), (∀ p ∈ ranges, p.1 ≤ p.2 ∧ p.2 ≤ b.size) →
      deserializeEach element (ranges.map fun p => slice b p.1 p.2) = .ok values →
      Each (RootedBy element) values (variableRoots element b ranges)
  | [], values, _, read => by
    -- No ranges decode to no values and give no roots.
    simp only [List.map_nil, deserializeEach] at read
    cases read
    rw [variableRoots.eq_def]
    exact .nil
  | (s, e) :: rest, values, inside, read => by
    -- A successful run decodes the first range, then the rest.
    simp only [List.map_cons, deserializeEach, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    rename_i head decoded
    split at read
    · cases read
    rename_i tail decodedRest
    cases read
    -- The first root is the first value's, by the element's own claim, and the rest follow by induction.
    rw [variableRoots.eq_def]
    have here := inside (s, e) (by simp)
    exact .cons (ih sound b s e head here.1 here.2 small decoded)
      (variableRoots_spec element ih sound b small rest tail (fun p m => inside p (by simp [m])) decodedRest)

/-- Roots of values are whole nodes. -/
theorem rooted_size {d : Desc} {v : Value} {r : ByteArray} (rooted : RootedBy d v r) : r.size = 32 := by
  -- A root of a value is always 32 bytes.
  rw [← ByteArray.size_data]
  exact hashTreeRoot_size d v r.data rooted

/-- Every root of a list rooted value by value is a whole node. -/
theorem forall₂_size {α : Type} {rooted : α → ByteArray → Prop} (each : ∀ a r, rooted a r → r.size = 32) :
    ∀ {xs : List α} {roots : List ByteArray}, Each rooted xs roots → ∀ r ∈ roots, r.size = 32
  -- Every root in the list is the head's or one of the tail's.
  | _, _, .nil => by simp
  | _, _, .cons head tail => by
    intro r member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact each _ _ head
    · exact forall₂_size each tail r member

/-- The leaves of a sequence of nested values are their roots. -/
theorem elements_mapM (element : Desc) :
    ∀ {values : List Value} {roots : List ByteArray}, Each (RootedBy element) values roots →
      (values.map fun v => some (element, v)).mapM slotRoot = .ok (roots.map ByteArray.data)
  -- Each value's leaf is its root, in order.
  | _, _, .nil => rfl
  | _, _, .cons head tail => by
    simp only [RootedBy] at head
    simp only [List.map_cons, List.mapM_cons, slotRoot, head, Bind.bind, Except.bind, elements_mapM element tail,
      pure, Except.pure]

/-- Whether a field's root is the specification's root of its decoded value. -/
def FieldRooted (pair : Desc × Value) (r : ByteArray) : Prop :=
  Ssz.hashTreeRoot pair.1 pair.2 = .ok r.data

/-- Fields decoded from ranges have, field by field, the roots read from those ranges. -/
theorem fieldRoots_spec (b : ByteArray) (small : Small b) :
    ∀ (fields : List Desc) (ranges : List (Nat × Nat)) (values : List Value),
      (∀ field ∈ fields, Agrees field ∧ field.wellFormed = .ok ()) → (∀ p ∈ ranges, p.1 ≤ p.2 ∧ p.2 ≤ b.size) →
      deserializeFields fields (ranges.map fun p => slice b p.1 p.2) = .ok values →
      fields.length = values.length ∧ Each FieldRooted (fields.zip values) (fieldRoots fields b ranges)
  | [], [], values, _, _, read => by
    -- No fields and no ranges decode to no values and give no roots.
    simp only [List.map_nil, deserializeFields] at read
    cases read
    rw [fieldRoots.eq_def]
    exact ⟨rfl, .nil⟩
  -- Fields and ranges of different lengths never decode.
  | [], _ :: _, _, _, _, read => by simp [deserializeFields] at read
  | _ :: _, [], _, _, _, read => by simp [deserializeFields] at read
  | field :: fields, (s, e) :: rest, values, each, inside, read => by
    -- A successful run decodes the first field, then the rest.
    simp only [List.map_cons, deserializeFields, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    rename_i head decoded
    split at read
    · cases read
    rename_i tail decodedRest
    cases read
    -- The first root is the first field's, by that field's own claim, and the rest follow by induction.
    rw [fieldRoots.eq_def]
    have here := inside (s, e) (by simp)
    have this := each field (by simp)
    obtain ⟨lengths, rooted⟩ := fieldRoots_spec b small fields rest tail (fun f m => each f (by simp [m]))
      (fun p m => inside p (by simp [m])) decodedRest
    exact ⟨by simp [lengths], .cons (this.1 this.2 b s e head here.1 here.2 small decoded) rooted⟩

/-- The leaves of a struct's fields are their roots. -/
theorem fields_mapM :
    ∀ {pairs : List (Desc × Value)} {roots : List ByteArray}, Each FieldRooted pairs roots →
      (pairs.map some).mapM slotRoot = .ok (roots.map ByteArray.data)
  | _, _, .nil => rfl
  -- Each field's leaf is its root, in order.
  | _, _, .cons head tail => by
    simp only [List.map_cons, List.mapM_cons, slotRoot, FieldRooted] at head ⊢
    simp only [head, Bind.bind, Except.bind, fields_mapM tail, pure, Except.pure]

end Ssz.Native.RootProof
