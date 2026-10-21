import SszNative.Proofs.Branch.Sequence

/-! Trees of structs and unions, as an encoding lays them out and as the decoded value does. -/

namespace Ssz.Native.BranchProof

open Ssz Ssz.Native

/-- Each field of a successful decoding decodes from its own slice. -/
theorem deserializeFields_get :
    ∀ (fields : List Desc) (slices : List Bytes) (values : List Value),
      deserializeFields fields slices = .ok values →
      fields.length = slices.length ∧ values.length = slices.length ∧
        ∀ j (hf : j < fields.length) (hs : j < slices.length) (hv : j < values.length),
          deserialize fields[j] slices[j] = .ok values[j]
  | [], [], values, read => by
    simp only [deserializeFields] at read
    cases read
    simp
  | field :: fields, slice :: slices, values, read => by
    simp only [deserializeFields, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    rename_i head decoded
    split at read
    · cases read
    rename_i tail decodedRest
    cases read
    obtain ⟨fl, vl, each⟩ := deserializeFields_get fields slices tail decodedRest
    refine ⟨by simp [fl], by simp [vl], ?_⟩
    intro j hf hs hv
    cases j with
    | zero => simpa using decoded
    | succ j => simpa using each j (by simpa using hf) (by simpa using hs) (by simpa using hv)
  | [], _ :: _, _, read => by simp [deserializeFields] at read
  | _ :: _, [], _, read => by simp [deserializeFields] at read

/-- Two lists of positions agreeing position by position. -/
inductive Agreeing (b : ByteArray) : List (Option (Desc × Nat × Nat)) → List (Option (Desc × Value)) → Prop where
  /-- Two empty lists. -/
  | nil : Agreeing b [] []
  /-- Agreeing heads, and tails that agree. -/
  | cons {x : Option (Desc × Nat × Nat)} {y : Option (Desc × Value)} {xs ys} :
    SlotAgrees b x y → Agreeing b xs ys → Agreeing b (x :: xs) (y :: ys)

/-- Agreeing lists have the same length, and agree at every position. -/
theorem Agreeing.get {b : ByteArray} :
    ∀ {xs : List (Option (Desc × Nat × Nat))} {ys : List (Option (Desc × Value))}, Agreeing b xs ys →
      xs.length = ys.length ∧ ∀ j (hx : j < xs.length) (hy : j < ys.length), SlotAgrees b xs[j] ys[j]
  | _, _, .nil => ⟨rfl, fun _ hx => by simp at hx⟩
  | _, _, .cons head tail => by
    obtain ⟨len, each⟩ := tail.get
    refine ⟨by simp [len], fun j hx hy => ?_⟩
    cases j with
    | zero => exact head
    | succ j => exact each j (by simpa using hx) (by simpa using hy)

/-- Positions listed one by one that agree lay out the same leaves. -/
theorem listed_agrees (b : ByteArray) (xs : List (Option (Desc × Nat × Nat))) (ys : List (Option (Desc × Value)))
    (agreeing : Agreeing b xs ys) : LeavesAgree b (.nested (.listed xs)) (.nested ys) := by
  obtain ⟨len, each⟩ := agreeing.get
  refine ⟨len, fun j h => ⟨xs[j], by simp [Slots.at, List.getElem?_eq_getElem (show j < xs.length by omega)],
    each j (by omega) h⟩, fun _ _ _ _ laid => by cases laid⟩

/-- Fields decoded from ranges agree, field by field, with the values decoded. -/
theorem fields_agreeing (b : ByteArray) :
    ∀ (fields : List Desc) (ranges : List (Nat × Nat)) (values : List Value),
      (∀ field ∈ fields, field.wellFormed = .ok ()) → (∀ p ∈ ranges, p.1 ≤ p.2 ∧ p.2 ≤ b.size) →
      deserializeFields fields (ranges.map fun p => slice b p.1 p.2) = .ok values →
      Agreeing b ((fields.zip ranges).map some) ((fields.zip values).map some)
  | [], [], values, _, _, read => by
    simp only [List.map_nil, deserializeFields] at read
    cases read
    exact .nil
  | [], _ :: _, _, _, _, read => by simp [deserializeFields] at read
  | _ :: _, [], _, _, _, read => by simp [deserializeFields] at read
  | field :: fields, (s, e) :: rest, values, sound, inside, read => by
    simp only [List.map_cons, deserializeFields, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    rename_i head decoded
    split at read
    · cases read
    rename_i tail decodedRest
    cases read
    have here := inside (s, e) (by simp)
    exact .cons ⟨rfl, sound field (by simp), here.1, here.2, decoded⟩
      (fields_agreeing b fields rest tail (fun f m => sound f (by simp [m])) (fun p m => inside p (by simp [m]))
        decodedRest)

/-- Placing fields gives one position per bit of the layout. -/
theorem placeFields_length : ∀ (active : List Bool) (xs : List (Desc × Nat × Nat)),
    (placeFields active xs).length = active.length
  | [], _ => rfl
  | false :: active, xs => by simp [placeFields, placeFields_length active xs]
  | true :: active, _ :: xs => by simp [placeFields, placeFields_length active xs]
  | true :: active, [] => by simp [placeFields, placeFields_length active []]

/-- Agreeing fields placed at a layout's positions agree, position by position. -/
theorem placed_agreeing (b : ByteArray) :
    ∀ (active : List Bool) (xs : List (Desc × Nat × Nat)) (ys : List (Desc × Value))
      (slots : List (Option (Desc × Value))), Agreeing b (xs.map some) (ys.map some) →
      placeSlots active ys = .ok slots → Agreeing b (placeFields active xs) slots
  | [], [], [], slots, _, read => by
    simp only [placeSlots] at read
    cases read
    exact .nil
  | [], _, _ :: _, _, _, read => by simp [placeSlots] at read
  | [], x :: xs, [], _, agreeing, _ => by cases agreeing
  | false :: active, xs, ys, slots, agreeing, read => by
    simp only [placeSlots, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    rename_i rest restRead
    cases read
    exact .cons trivial (placed_agreeing b active xs ys rest agreeing restRead)
  | true :: active, x :: xs, y :: ys, slots, agreeing, read => by
    simp only [placeSlots, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    rename_i rest restRead
    cases read
    cases agreeing with
    | cons head tail => exact .cons head (placed_agreeing b active xs ys rest tail restRead)
  | true :: _, _, [], _, _, read => by simp [placeSlots] at read
  | true :: _, [], _ :: _, _, agreeing, _ => by cases agreeing

/-- What decoding a struct gives: ranges cutting its slices, and fields agreeing with the values decoded. -/
theorem struct_agreeing (fields : List Desc) (sound : ∀ field ∈ fields, field.wellFormed = .ok ())
    (nonempty : fields ≠ []) (b : ByteArray) (s e : Nat) (o : s ≤ e) (i : e ≤ b.size) (slices : List Bytes)
    (values : List Value) (cut : structSlices fields (slice b s e) = .ok slices)
    (decoded : deserializeFields fields slices = .ok values) :
    ∃ ranges, fieldRanges fields b s e = .ok ranges ∧ fields.length = values.length ∧ fields.length ≤ e - s ∧
      Agreeing b ((fields.zip ranges).map some) ((fields.zip values).map some) := by
  have agree := fieldRanges_cut fields b s e o i
  rw [cut] at agree
  cases ranged : fieldRanges fields b s e with
  | error err => simp [ranged, CutAgree] at agree
  | ok ranges =>
    simp only [ranged, CutAgree, Cuts] at agree
    obtain ⟨sliced, within⟩ := agree
    subst sliced
    obtain ⟨fl, vl, _⟩ := deserializeFields_get fields _ values decoded
    have spends := RootProof.structSlices_spends fields _ _ sound nonempty cut
    rw [slice_size b s e i] at spends
    refine ⟨ranges, rfl, by omega, spends, fields_agreeing b fields ranges values sound
      (fun p m => ⟨(within p m).2.1, by have := (within p m).2.2; omega⟩) decoded⟩

/-- A struct lays out its tree as its encoding does. -/
theorem container_agrees (names : List String) (fields : List Desc)
    (sound : (Desc.container names fields).wellFormed = .ok ()) (b : ByteArray) (s e : Nat) (v : Value)
    (o : s ≤ e) (i : e ≤ b.size) (small : RootProof.Small b)
    (read : deserialize (.container names fields) (slice b s e) = .ok v) :
    ∃ E L, layoutOf (.container names fields) b s e = .ok E ∧ merkleLayout (.container names fields) v = .ok L ∧
      Corresponds b E L := by
  simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i slices cut
  split at read
  · cases read
  rename_i values decoded
  cases read
  obtain ⟨ranges, ranged, lengths, spends, agreeing⟩ := struct_agreeing fields
    (allWellFormed_mem fields (wellFormed_container sound)) (RootProof.container_nonempty sound) b s e o i slices
    values cut decoded
  have count := agreeing.get.1
  simp only [List.length_map, List.length_zip] at count
  refine ⟨⟨.nested (.listed ((fields.zip ranges).map some)), some fields.length, none⟩,
    ⟨.nested ((fields.zip values).map some), some fields.length, none⟩,
    by simp only [layoutOf, ranged, Bind.bind, Except.bind, pure, Except.pure], ?_,
    ⟨listed_agrees b _ _ agreeing, rfl, rfl, ?_⟩⟩
  · simp only [merkleLayout, lengths, bne_self_eq_false, Bool.false_eq_true, if_false, MerkleLayout.nesting,
      pure, Except.pure]
  · unfold RootProof.Small at small
    simp only [EncodedLayout.count, Slots.count, List.length_map, List.length_zip]
    omega

/-- A progressive struct lays out its tree as its encoding does. -/
theorem progressiveContainer_agrees (active : List Bool) (names : List String) (fields : List Desc)
    (sound : (Desc.progressiveContainer active names fields).wellFormed = .ok ()) (b : ByteArray) (s e : Nat)
    (v : Value) (o : s ≤ e) (i : e ≤ b.size) (_small : RootProof.Small b)
    (read : deserialize (.progressiveContainer active names fields) (slice b s e) = .ok v) :
    ∃ E L, layoutOf (.progressiveContainer active names fields) b s e = .ok E ∧
      merkleLayout (.progressiveContainer active names fields) v = .ok L ∧ Corresponds b E L := by
  simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i slices cut
  split at read
  · cases read
  rename_i values decoded
  cases read
  obtain ⟨ranges, ranged, lengths, _, agreeing⟩ := struct_agreeing fields
    (allWellFormed_mem fields (wellFormed_progressiveContainer sound)) (RootProof.progressive_nonempty sound) b s
    e o i slices values cut decoded
  -- Each set position takes the next field, and each gap is a gap either way.
  have counted := progressive_count sound
  obtain ⟨slots, placed⟩ := placeSlots_exists active (fields.zip values) (by simp [counted, lengths])
  have positions := placed_agreeing b active (fields.zip ranges) (fields.zip values) slots agreeing placed
  have width := RootProof.progressive_width sound
  have cv : List.countP id active = values.length := by rw [counted, lengths]
  refine ⟨⟨.nested (.listed (placeFields active (fields.zip ranges))), none, some (activeFieldsNode active)⟩,
    ⟨.nested slots, none, some (activeFieldsWord active)⟩,
    by simp only [layoutOf, ranged, Bind.bind, Except.bind, pure, Except.pure], ?_,
    ⟨listed_agrees b _ _ positions, rfl, by simp only [Option.map_some, RootProof.facts_hold.activeFields], ?_⟩⟩
  · simp only [merkleLayout, layoutSlots, lengths, cv, bne_self_eq_false, Bool.false_eq_true, if_false, placed,
      MerkleLayout.nesting, Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  · -- One position per bit of the layout, at most one node's worth.
    simp only [EncodedLayout.count, Slots.count, placeFields_length]
    have := USize.le_size
    omega

/-- A compatible union lays out its tree as its encoding does: the chosen option, with the selector mixed in. -/
theorem union_agrees (selectors : List Nat) (options : List Desc)
    (sound : (Desc.compatibleUnion selectors options).wellFormed = .ok ()) (b : ByteArray) (s e : Nat) (v : Value)
    (o : s ≤ e) (i : e ≤ b.size) (_small : RootProof.Small b)
    (read : deserialize (.compatibleUnion selectors options) (slice b s e) = .ok v) :
    ∃ E L, layoutOf (.compatibleUnion selectors options) b s e = .ok E ∧
      merkleLayout (.compatibleUnion selectors options) v = .ok L ∧ Corresponds b E L := by
  have size := slice_size b s e i
  simp only [deserialize, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at read
  split at read
  · cases read
  rename_i nonempty
  -- The first byte selects, and the rest is the option's encoding.
  have first : (slice b s e)[0]! = b.get! s := by
    rw [slice_getElem! b s e 0 i (by omega), Nat.add_zero]
  have rest : (slice b s e).extract 1 (slice b s e).size = slice b (s + 1) e := by
    rw [size, slice_extract b s e 1 _ o (Nat.le_refl _)]
    congr 1
    omega
  rw [first, rest] at read
  obtain ⟨option, inner, member, looked, rfl, decoded, _⟩ :=
    RootProof.option_search b (s + 1) e selectors options _ _ v read
  have optionSound := allWellFormed_mem options (wellFormed_union sound) option member
  have byte : (b.get! s).toNat ≤ 0xFF := by have := (b.get! s).toNat_lt; omega
  refine ⟨⟨.nested (.listed [some (option, s + 1, e)]), some 1, some (lengthNode (b.get! s).toNat)⟩,
    ⟨.nested [some (option, inner)], some 1, some (lengthWord (b.get! s).toNat)⟩, ?_, ?_,
    ⟨listed_agrees b _ _ (.cons ⟨rfl, optionSound, by omega, i, decoded⟩ .nil), rfl,
      by simp only [Option.map_some, RootProof.facts_hold.lengthNode], ?_⟩⟩
  · simp only [layoutOf, looked, Bind.bind, Except.bind, pure, Except.pure]
  · simp only [merkleLayout, looked, selectorWord, show ¬ (b.get! s).toNat > 0xFF by omega, if_false,
      MerkleLayout.nesting, Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  · simp only [EncodedLayout.count, Slots.count, List.length_singleton]
    have := USize.le_size
    omega

end Ssz.Native.BranchProof
