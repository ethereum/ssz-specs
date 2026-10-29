import SszNative.Proofs.Branch.Packed

/-! Trees of sequences, as an encoding lays them out and as the decoded value does. -/

namespace Ssz.Native.BranchProof

open Ssz Ssz.Native

/-- Each element's slot is the range the check accepted for it. -/
theorem elementSlots_at (element : Desc) (b : ByteArray) (s e count : Nat) (r : Ranges)
    (rangesEq : elementRanges element b s e count = r.toList) (i : Nat) (h : i < count) :
    ∃ p, r.toList[i]? = some p ∧ (elementSlots element b s e count).at i = some (some (element, p.1, p.2)) := by
  rw [← rangesEq]
  unfold elementSlots elementRanges
  cases element.fixedSize with
  | some width =>
    -- Elements one width apart.
    refine ⟨(s + i * width, s + (i + 1) * width), by simp [h], ?_⟩
    simp only [Slots.at, h, if_true, Option.some.injEq]
    congr 3 <;> simp [Nat.mul_comm, Nat.mul_succ]
  | none =>
    -- Elements from their offsets.
    have len : (bodyRanges b s e count).length = count := by simp [bodyRanges]; omega
    have hb : i < (bodyRanges b s e count).length := by omega
    refine ⟨(bodyRanges b s e count)[i], by simp [List.getElem?_eq_getElem hb], ?_⟩
    simp only [Slots.at, List.getElem?_map, List.getElem?_eq_getElem hb, Option.map_some]

/-- A sequence's slots hold as many positions as it has elements. -/
theorem elementSlots_count (element : Desc) (b : ByteArray) (s e count : Nat) :
    (elementSlots element b s e count).count = count := by
  unfold elementSlots
  cases element.fixedSize <;> simp [Slots.count, bodyRanges] <;> omega

/-- Only fixed-size elements are laid out one width apart. -/
theorem elementSlots_stride (element : Desc) (b : ByteArray) (s e count : Nat) :
    ∀ element' start width cnt, elementSlots element b s e count = .stride element' start width cnt →
      element'.fixedSize = some width := by
  intro element' start width cnt laid
  unfold elementSlots at laid
  cases fixed : element.fixedSize with
  | some w => rw [fixed] at laid; cases laid; exact fixed
  | none => rw [fixed] at laid; cases laid

/-- A sequence of decoded elements, cut from ranges of an encoding, lays out its tree as its encoding does. -/
theorem sequence_agrees (element : Desc) (sound : element.wellFormed = .ok ()) (b : ByteArray)
    (small : RootProof.Small b) (s e : Nat) (o : s ≤ e) (i : e ≤ b.size) (count : Nat) (slices : List Bytes)
    (values : List Value) (r : Ranges) (sliced : slices = r.toList.map fun p => slice b p.1 p.2)
    (within : ∀ p ∈ r.toList, s ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ e)
    (rangesEq : elementRanges element b s e count = r.toList) (lengths : count = values.length)
    (decoded : deserializeEach element slices = .ok values)
    (packs : element.isBasic = true → packElements slices = packBytes (slice b s e)) (few : count ≤ e - s)
    (positions : Option Nat) (mixinE : Option ByteArray) (mixinL : Option Bytes)
    (mixinEq : mixinE.map ByteArray.data = mixinL) :
    ∃ L, sequenceLayout element values positions mixinL = .ok L ∧
      Corresponds b (encodedSequence element b s e count positions mixinE) L := by
  unfold RootProof.Small at small
  obtain ⟨decodedLength, each⟩ := RootProof.deserializeEach_get element slices values decoded
  by_cases basic : element.isBasic = true
  · -- Basic elements pack, back to back, into the encoding's own nodes.
    have wrote := serializeEach_of_deserializeEach (serialize_of_deserialize element sound) slices values decoded
    refine ⟨⟨.packed (packBytes (slice b s e)), positions.map fun n => chunksForBytes (n * element.itemLength),
      mixinL⟩, ?_, ?_⟩
    · simp only [sequenceLayout, basic, if_true, wrote, packs basic, Bind.bind, Except.bind, pure, Except.pure,
        MerkleLayout.packing]
    · simp only [encodedSequence, basic, if_true]
      exact ⟨packRange_agrees b s e o i (by unfold RootProof.Small; omega), rfl, mixinEq,
        by simpa [EncodedLayout.count] using packed_fits b s e i (by unfold RootProof.Small; omega)⟩
  · -- Other elements are each a leaf of their own, read from their own range.
    have notBasic : element.isBasic = false := by simpa using basic
    refine ⟨⟨.nested (values.map fun v => some (element, v)), positions, mixinL⟩, ?_, ?_⟩
    · simp only [sequenceLayout, notBasic, Bool.false_eq_true, if_false, MerkleLayout.nesting, pure, Except.pure]
    · simp only [encodedSequence, notBasic, Bool.false_eq_true, if_false]
      refine ⟨⟨by rw [elementSlots_count, lengths, List.length_map], fun j hj => ?_,
        elementSlots_stride element b s e count⟩, rfl, mixinEq, ?_⟩
      · simp only [List.length_map] at hj
        obtain ⟨p, found, tableEntry⟩ := elementSlots_at element b s e count r rangesEq j (by omega)
        refine ⟨_, tableEntry, ?_⟩
        -- Element j decodes from the slice of its range.
        have hr : j < r.toList.length := by
          rw [← List.length_map (f := fun p => slice b p.1 p.2), ← sliced]; omega
        have pj : r.toList[j] = p := by
          rw [List.getElem?_eq_getElem hr] at found; exact Option.some.inj found
        have member : p ∈ r.toList := by rw [← pj]; exact List.getElem_mem hr
        have bounds := within p member
        have read := each j (by omega) (by omega)
        simp only [sliced, List.getElem_map, pj] at read
        simp only [List.getElem_map, SlotAgrees]
        exact ⟨trivial, sound, bounds.2.1, by omega, read⟩
      · simp only [EncodedLayout.count, elementSlots_count]
        omega

/-- The elements of a vector of basic elements pack back into the encoding. -/
theorem vector_packs (element : Desc) (length : Nat) (sound : element.wellFormed = .ok ()) (data : Bytes)
    (slices : List Bytes) (cut : vectorSlices element length data = .ok slices) (basic : element.isBasic = true) :
    packElements slices = packBytes data := by
  have fixed := RootProof.basic_fixedSize basic
  have positive := fixedSize_pos_of_wellFormed sound fixed
  simp only [vectorSlices, fixed, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure,
    Except.pure] at cut
  split at cut
  · cases cut
  split at cut
  · cases cut
  rename_i same
  cases cut
  -- The slices are the encoding cut one width apart, all of it.
  have sized : data.size = element.itemLength * length := by simpa using same
  have whole : data.size % element.itemLength = 0 := by rw [sized]; simp
  have count : data.size / element.itemLength = length := by
    rw [sized, Nat.mul_div_cancel_left _ positive]
  have := (RootProof.fixed_slices_pack data element.itemLength whole).1
  rwa [count] at this

/-- A vector lays out its tree as its encoding does. -/
theorem vector_agrees (element : Desc) (length : Nat) (sound : (Desc.vector element length).wellFormed = .ok ())
    (b : ByteArray) (s e : Nat) (v : Value) (o : s ≤ e) (i : e ≤ b.size) (small : RootProof.Small b)
    (read : deserialize (.vector element length) (slice b s e) = .ok v) :
    ∃ E L, layoutOf (.vector element length) b s e = .ok E ∧ merkleLayout (.vector element length) v = .ok L ∧
      Corresponds b E L := by
  have elementSound := wellFormed_vector sound
  simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i slices cut
  split at read
  · cases read
  rename_i values decoded
  cases read
  -- The check accepted ranges cutting the same slices.
  have agree := vectorRanges_cut element length b s e o i
  rw [cut] at agree
  cases ranged : vectorRanges element length b s e with
  | error err => simp [ranged, Except.map, CutAgree] at agree
  | ok r =>
    simp only [ranged, Except.map, CutAgree, Cuts] at agree
    obtain ⟨sliced, within⟩ := agree
    have rangesEq := RootProof.elementRanges_vector element length b s e r ranged
    have lengths : length = values.length := by
      rw [(RootProof.deserializeEach_get element slices values decoded).1, vectorSlices_length cut]
    have few := RootProof.vector_count_le elementSound cut
    rw [slice_size b s e i] at few
    obtain ⟨L, layout, c⟩ := sequence_agrees element elementSound b small s e o i length slices values r sliced
      within rangesEq lengths decoded (vector_packs element length elementSound _ slices cut) few (some length)
      none none rfl
    refine ⟨_, L, rfl, ?_, c⟩
    simp only [merkleLayout, ← lengths, bne_self_eq_false, Bool.false_eq_true, if_false, layout]

/-- A counted sequence lays out its tree as its encoding does, its count mixed in. -/
theorem counted_agrees (element : Desc) (limit : Option Nat) (sound : element.wellFormed = .ok ())
    (b : ByteArray) (s e : Nat) (o : s ≤ e) (i : e ≤ b.size) (small : RootProof.Small b) (slices : List Bytes)
    (values : List Value) (cut : listSlices element limit (slice b s e) = .ok slices)
    (decoded : deserializeEach element slices = .ok values) (positions : Option Nat) :
    elementCount element b s e = values.length ∧ ∃ L,
      sequenceLayout element values positions (some (lengthWord values.length)) = .ok L ∧
      Corresponds b (encodedSequence element b s e (elementCount element b s e) positions
        (some (lengthNode (elementCount element b s e)))) L := by
  -- The check accepted ranges cutting the same slices.
  have agree := listRanges_cut element limit b s e o i
  rw [cut] at agree
  cases ranged : listRanges element limit b s e with
  | error err => simp [ranged, Except.map, CutAgree] at agree
  | ok r =>
    simp only [ranged, Except.map, CutAgree, Cuts] at agree
    obtain ⟨sliced, within⟩ := agree
    obtain ⟨counted, rangesEq⟩ := RootProof.elementRanges_list element limit b s e r ranged
    have lengths : elementCount element b s e = values.length := by
      rw [counted, (RootProof.deserializeEach_get element slices values decoded).1, sliced, List.length_map]
    have few := RootProof.list_count_le sound cut
    rw [slice_size b s e i, (RootProof.deserializeEach_get element slices values decoded).1.symm] at few
    refine ⟨lengths, sequence_agrees element sound b small s e o i _ slices values r sliced within rangesEq lengths
      decoded (fun basic => (RootProof.basic_packing element basic sound _ limit slices values cut decoded).2.1)
      (by omega) positions _ _ ?_⟩
    simp only [Option.map_some, RootProof.facts_hold.lengthNode, lengths]

/-- A list lays out its tree as its encoding does. -/
theorem list_agrees (element : Desc) (limit : Nat) (sound : (Desc.list element limit).wellFormed = .ok ())
    (b : ByteArray) (s e : Nat) (v : Value) (o : s ≤ e) (i : e ≤ b.size) (small : RootProof.Small b)
    (read : deserialize (.list element limit) (slice b s e) = .ok v) :
    ∃ E L, layoutOf (.list element limit) b s e = .ok E ∧ merkleLayout (.list element limit) v = .ok L ∧
      Corresponds b E L := by
  simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i slices cut
  split at read
  · cases read
  rename_i values decoded
  cases read
  have bound := listSlices_bound cut
  have lengths := (RootProof.deserializeEach_get element slices values decoded).1
  obtain ⟨_, L, layout, c⟩ := counted_agrees element (some limit) (wellFormed_list sound) b s e o i small slices
    values cut decoded (some limit)
  refine ⟨_, L, rfl, ?_, c⟩
  simp only [merkleLayout, show ¬ values.length > limit by omega, if_false, layout]

/-- A progressive list lays out its tree as its encoding does. -/
theorem progressiveList_agrees (element : Desc) (limit : Option Nat)
    (sound : (Desc.progressiveList element limit).wellFormed = .ok ()) (b : ByteArray) (s e : Nat) (v : Value)
    (o : s ≤ e) (i : e ≤ b.size) (small : RootProof.Small b)
    (read : deserialize (.progressiveList element limit) (slice b s e) = .ok v) :
    ∃ E L, layoutOf (.progressiveList element limit) b s e = .ok E ∧
      merkleLayout (.progressiveList element limit) v = .ok L ∧ Corresponds b E L := by
  simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i slices cut
  split at read
  · cases read
  rename_i values decoded
  cases read
  obtain ⟨_, L, layout, c⟩ := counted_agrees element limit (wellFormed_progressiveList sound) b s e o i small
    slices values cut decoded none
  have within := listSlices_within cut
  have countedValues := (RootProof.deserializeEach_get element slices values decoded).1
  rw [← countedValues] at within
  have bound := boundCheck_of_withinBound limit values.length within
  refine ⟨_, L, rfl, ?_, c⟩
  simpa only [merkleLayout, bound, Bind.bind, Except.bind] using layout

end Ssz.Native.BranchProof
