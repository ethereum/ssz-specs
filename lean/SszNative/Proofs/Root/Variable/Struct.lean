import SszNative.Proofs.Root.Variable.Sequence
import Ssz.Proofs.Codec.RootDomain

/-! Roots of structs whose fields are not rooted as columns: one root per field, under a bounded or progressive tree. -/

namespace Ssz.Native.RootProof

open Ssz Ssz.Native

variable (facts : Facts)

/-- Reading a struct's slots spends at least a byte per field, all inside the encoding. -/
theorem readSlots_spends (data : Bytes) :
    ∀ (fields : List Desc) (position : Nat) (slots : List Slot) (ending : Nat),
      (∀ field ∈ fields, ∀ w, field.fixedSize = some w → 0 < w) →
      readSlots fields data position = .ok (slots, ending) →
      position + fields.length ≤ ending ∧ (fields ≠ [] → ending ≤ data.size)
  | [], position, slots, ending, _, read => by
    -- No fields spend nothing.
    simp only [readSlots] at read
    cases read
    simp
  | field :: fields, position, slots, ending, positive, read => by
    -- The first slot is read, then the rest from just after it.
    simp only [readSlots] at read
    split at read
    -- A fixed field spends its positive width, inside the fixed part.
    · rename_i w fixed
      simp only [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure] at read
      split at read
      · cases read
      rename_i fits
      split at read
      · cases read
      rename_i rest restRead
      cases read
      have w0 := positive field (by simp) w fixed
      obtain ⟨spent, inside⟩ := readSlots_spends data fields (position + w) _ _
        (fun f m => positive f (by simp [m])) restRead
      refine ⟨by simp; omega, fun _ => ?_⟩
      cases fields with
      | nil => simp [readSlots] at restRead; cases restRead; omega
      | cons _ _ => exact inside (by simp)
    -- A variable field spends its four-byte offset, inside the fixed part.
    · simp only [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure] at read
      split at read
      · cases read
      rename_i fits
      split at read
      · cases read
      rename_i rest restRead
      cases read
      obtain ⟨spent, inside⟩ := readSlots_spends data fields (position + bytesPerOffset) _ _
        (fun f m => positive f (by simp [m])) restRead
      refine ⟨by simp [bytesPerOffset] at spent ⊢; omega, fun _ => ?_⟩
      cases fields with
      | nil => simp [readSlots] at restRead; cases restRead; simp at fits; omega
      | cons _ _ => exact inside (by simp)

/-- A struct of well-formed fields that decodes spends at least a byte per field. -/
theorem structSlices_spends (fields : List Desc) (data : Bytes) (slices : List Bytes)
    (sound : ∀ field ∈ fields, field.wellFormed = .ok ()) (nonempty : fields ≠ [])
    (read : structSlices fields data = .ok slices) : fields.length ≤ data.size := by
  simp only [structSlices, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure,
    Except.pure] at read
  -- An accepted struct read all its slots, so it spends a byte per field.
  split at read
  · cases read
  split at read
  · cases read
  split at read
  · cases read
  rename_i pair readEq
  obtain ⟨slots, leading⟩ := pair
  obtain ⟨spent, within⟩ := readSlots_spends data fields 0 slots leading
    (fun f m w fixed => fixedSize_pos_of_wellFormed (sound f m) fixed) readEq
  have := within nonempty
  omega

/-- A gap's leaf is the zero node. -/
theorem zeroNode_data : zeroNode.data = zeroChunk := rfl

/-- Field roots placed at a layout's positions are, position by position, the leaves the layout gives. -/
theorem placed_mapM :
    ∀ (active : List Bool) (pairs : List (Desc × Value)) (roots : List ByteArray) (slots : List (Option (Desc × Value))),
      Each FieldRooted pairs roots → placeSlots active pairs = .ok slots →
      slots.mapM slotRoot = .ok ((placeRoots active roots).map ByteArray.data) ∧
        (placeRoots active roots).length = active.length ∧ ∀ r ∈ placeRoots active roots, r.size = 32
  | [], [], [], slots, .nil, read => by
    -- An empty layout places nothing.
    simp only [placeSlots] at read
    cases read
    simp [placeRoots]
    rfl
  -- A layout too short for its fields places nothing.
  | [], _ :: _, _, _, _, read => by simp [placeSlots] at read
  | false :: active, pairs, roots, slots, rooted, read => by
    -- A gap takes the zero leaf, and the rest follow by induction.
    simp only [placeSlots, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    rename_i rest restRead
    cases read
    obtain ⟨mapped, length, sized⟩ := placed_mapM active pairs roots rest rooted restRead
    refine ⟨?_, by simp [placeRoots, length], ?_⟩
    · simp only [List.mapM_cons, slotRoot, placeRoots, List.map_cons, mapped, zeroNode_data, Bind.bind,
        Except.bind, pure, Except.pure]
    · intro r member
      simp only [placeRoots, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact sized r member
  | true :: active, pair :: pairs, r :: roots, slots, .cons head tail, read => by
    -- A set position takes the next field's root, and the rest follow by induction.
    simp only [placeSlots, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    rename_i rest restRead
    cases read
    obtain ⟨mapped, length, sized⟩ := placed_mapM active pairs roots rest tail restRead
    refine ⟨?_, by simp [placeRoots, length], ?_⟩
    · simp only [FieldRooted] at head
      simp only [List.mapM_cons, slotRoot, placeRoots, List.map_cons, mapped, head, Bind.bind, Except.bind,
        pure, Except.pure]
    · intro x member
      simp only [placeRoots, List.mem_cons] at member
      rcases member with rfl | member
      · exact rooted_size (d := pair.1) (v := pair.2) head
      · exact sized x member
  -- A layout with set positions left over but no field to put there places nothing.
  | true :: _, [], _, _, _, read => by simp [placeSlots] at read

/-- A well-formed progressive layout has at most as many positions as one node has bits. -/
theorem progressive_width {active : List Bool} {names : List String} {fields : List Desc}
    (sound : (Desc.progressiveContainer active names fields).wellFormed = .ok ()) : active.length ≤ 256 := by
  -- Well-formedness bounds the layout by the bits of one node.
  rw [Desc.wellFormed] at sound
  repeat' first | split at sound | simp only [Bind.bind, Except.bind] at sound
  all_goals simp_all [throw, throwThe, MonadExceptOf.throw]

/-- A well-formed struct has a field. -/
theorem container_nonempty {names : List String} {fields : List Desc}
    (sound : (Desc.container names fields).wellFormed = .ok ()) : fields ≠ [] := by
  -- A struct with no fields is not well-formed.
  intro empty
  subst empty
  simp [Desc.wellFormed, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at sound

/-- A well-formed progressive struct has a field. -/
theorem progressive_nonempty {active : List Bool} {names : List String} {fields : List Desc}
    (sound : (Desc.progressiveContainer active names fields).wellFormed = .ok ()) : fields ≠ [] := by
  -- A progressive struct with no fields is not well-formed.
  intro empty
  subst empty
  rw [Desc.wellFormed] at sound
  repeat' first | split at sound | simp only [Bind.bind, Except.bind] at sound
  all_goals simp_all [throw, throwThe, MonadExceptOf.throw]

/-- What decoding a struct gives: field ranges cutting its slices, and the fields' roots read from them. -/
theorem struct_fields (fields : List Desc) (each : ∀ field ∈ fields, Agrees field ∧ field.wellFormed = .ok ())
    (nonempty : fields ≠ []) (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (small : Small b) (slices : List Bytes) (values : List Value)
    (cut : structSlices fields (slice b start stop) = .ok slices)
    (decoded : deserializeFields fields slices = .ok values) :
    fields.length = values.length ∧ fields.length ≤ stop - start ∧
      Each FieldRooted (fields.zip values) (fieldRoots fields b ((fieldRanges fields b start stop).toOption.getD [])) := by
  -- The check accepted field ranges cutting the same slices deserialization cut.
  have agree := fieldRanges_cut fields b start stop ordered inside
  rw [cut] at agree
  cases ranged : fieldRanges fields b start stop with
  | error e => simp [ranged, CutAgree] at agree
  | ok ranges =>
    simp only [ranged, CutAgree] at agree
    obtain ⟨sliced, within⟩ := agree
    subst sliced
    -- Each field's root is the specification's root of its decoded value.
    obtain ⟨lengths, rooted⟩ := fieldRoots_spec b small fields ranges values each
      (fun p m => ⟨(within p m).2.1, by have := (within p m).2.2; omega⟩) decoded
    have spends := structSlices_spends fields _ _ (fun f m => (each f m).2) nonempty cut
    rw [slice_size b start stop inside] at spends
    exact ⟨lengths, spends, rooted⟩

include facts in
/-- A struct whose fields are not rooted as columns has the specification's root. -/
theorem container_root (names : List String) (fields : List Desc) (ih : ∀ field ∈ fields, Agrees field)
    (sound : (Desc.container names fields).wellFormed = .ok ()) (notPlain : plain (.container names fields) = false)
    (b : ByteArray) (start stop : Nat) (v : Value) (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (small : Small b) (read : deserialize (.container names fields) (slice b start stop) = .ok v) :
    Ssz.hashTreeRoot (.container names fields) v = .ok (rootOf (.container names fields) b start stop).data := by
  -- Decoding cuts the fields' slices, then decodes each.
  simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i slices cut
  split at read
  · cases read
  rename_i values decoded
  cases read
  -- Every field agrees and is well-formed, since the struct is.
  have each : ∀ field ∈ fields, Agrees field ∧ field.wellFormed = .ok () := fun f m =>
    ⟨ih f m, allWellFormed_mem fields (wellFormed_container sound) f m⟩
  obtain ⟨lengths, spends, rooted⟩ := struct_fields fields each (container_nonempty sound) b start stop ordered
    inside small slices values cut decoded
  have sized := forall₂_size (fun p _ h => rooted_size (d := p.1) (v := p.2) h) rooted
  have count := Each.length_eq rooted
  simp only [List.length_zip, ← lengths, Nat.min_self] at count
  -- Both sides bound the tree by the field count, over the fields' roots.
  rw [hashTreeRoot_unfold]
  simp only [merkleLayout, lengths, bne_self_eq_false, Bool.false_eq_true, if_false, MerkleLayout.nesting,
    leafChunks, fields_mapM rooted, finishLayout, Bind.bind, Except.bind, pure, Except.pure]
  rw [rootOf]
  simp only [notPlain, Bool.false_eq_true, if_false]
  unfold Small at small
  have tree := joined_bounded facts _ sized _ (Nat.le_refl _) (by omega)
  rw [← lengths, count, tree]

include facts in
/-- A progressive struct has the specification's root. -/
theorem progressiveContainer_root (active : List Bool) (names : List String) (fields : List Desc)
    (ih : ∀ field ∈ fields, Agrees field) (sound : (Desc.progressiveContainer active names fields).wellFormed = .ok ())
    (b : ByteArray) (start stop : Nat) (v : Value) (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (small : Small b) (read : deserialize (.progressiveContainer active names fields) (slice b start stop) = .ok v) :
    Ssz.hashTreeRoot (.progressiveContainer active names fields) v =
      .ok (rootOf (.progressiveContainer active names fields) b start stop).data := by
  -- Decoding cuts the fields' slices, then decodes each.
  simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i slices cut
  split at read
  · cases read
  rename_i values decoded
  cases read
  have each : ∀ field ∈ fields, Agrees field ∧ field.wellFormed = .ok () := fun f m =>
    ⟨ih f m, allWellFormed_mem fields (wellFormed_progressiveContainer sound) f m⟩
  obtain ⟨lengths, _, rooted⟩ := struct_fields fields each (progressive_nonempty sound) b start stop ordered
    inside small slices values cut decoded
  -- Each set position takes the next field, and each gap a zero leaf.
  have counted := progressive_count sound
  obtain ⟨slots, placed⟩ := placeSlots_exists active (fields.zip values) (by simp [counted, lengths])
  obtain ⟨mapped, length, sized⟩ := placed_mapM active _ _ slots rooted placed
  have cv : List.countP id active = values.length := by rw [counted, lengths]
  -- The specification's layout leaves are the placed roots, under a progressive tree.
  rw [hashTreeRoot_unfold]
  simp only [merkleLayout, layoutSlots, lengths, cv, bne_self_eq_false, Bool.false_eq_true, if_false, placed,
    MerkleLayout.nesting, leafChunks, mapped, finishLayout, Bind.bind, Except.bind, pure, Except.pure, throw,
    throwThe, MonadExceptOf.throw]
  -- The native root places the same roots, then mixes in the layout's node.
  rw [rootOf]
  have width := progressive_width sound
  obtain ⟨nodes, joined⟩ := joinNodes_nodes _ sized
  have tree := progressive_root facts _ _ _ nodes (by omega)
    (Or.inr (by rw [joined, length]; have := USize.le_size; omega))
  rw [hashPair_mixIn tree (facts.activeFields active) (by simp) (by simp)]

end Ssz.Native.RootProof
