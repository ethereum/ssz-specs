import SszNative.Proofs.Validate.Seq

/-! Struct field ranges agreeing with the slices deserialization cuts. -/

namespace Ssz.Native

open Ssz

/-- The slot deserialization reads where the native check reads a place. -/
def Place.toSlot (b : ByteArray) : Place → Slot
  | .inline s e => .inline (slice b s e)
  | .body offset => .body offset

/-- Whether every in-place field lies inside a range. -/
def PlacesInside (start stop : Nat) (places : List Place) : Prop :=
  ∀ s e, Place.inline s e ∈ places → start ≤ s ∧ s ≤ e ∧ e ≤ stop

/-- Struct places read in place agree with the slots deserialization reads. -/
theorem readPlaces_cut (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop) (inside : stop ≤ b.size) :
    ∀ (fields : List Desc) (position : Nat),
      match readPlaces fields b start (stop - start) position, readSlots fields (slice b start stop) position with
      | .error e, .error e' => e = e'
      | .ok (places, ending), .ok (slots, ending') =>
        ending = ending' ∧ slots = places.map (Place.toSlot b) ∧ PlacesInside start stop places
      | _, _ => False
  -- No fields leave nothing to read on either side.
  | [], position => by simp [readPlaces, readSlots, PlacesInside]
  | field :: fields, position => by
    -- The slice has the range's size, and the rest of the fields agree by induction.
    have size := slice_size b start stop inside
    have ih := readPlaces_cut b start stop ordered inside fields
    simp only [readPlaces, readSlots, size]
    -- A fixed field sits in place, and a variable one leaves an offset.
    cases fixed : field.fixedSize with
    | some width =>
      simp only
      -- A fixed field running past the fixed part is refused by both.
      by_cases over : position + width > stop - start
      · simp [over, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
      · simp only [over, ↓reduceIte, Bind.bind, Except.bind, pure, Except.pure]
        -- Otherwise the rest of the fields decide, and this field's slot is its range's slice.
        have := ih (position + width)
        revert this
        cases readPlaces fields b start (stop - start) (position + width) <;>
          cases readSlots fields (slice b start stop) (position + width) <;> simp
        rename_i places slots
        intro same slotsEq placed
        refine ⟨same, ?_, ?_⟩
        · rw [slice_extract b start stop position (position + width) ordered (by omega)]
          simp [slotsEq, Place.toSlot, Nat.add_assoc]
        -- The new place lies inside the range, and the rest are placed by induction.
        · intro s e member
          simp only [List.mem_cons, Place.inline.injEq] at member
          rcases member with ⟨rfl, rfl⟩ | later
          · omega
          · exact placed s e later
    | none =>
      simp only
      -- An offset running past the fixed part is refused by both.
      by_cases over : position + bytesPerOffset > stop - start
      · simp [over, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
      · simp only [over, ↓reduceIte, Bind.bind, Except.bind, pure, Except.pure]
        -- Otherwise the rest of the fields decide, and this field's offset reads alike on both sides.
        have := ih (position + bytesPerOffset)
        revert this
        cases readPlaces fields b start (stop - start) (position + bytesPerOffset) <;>
          cases readSlots fields (slice b start stop) (position + bytesPerOffset) <;> simp
        rename_i places slots
        intro same slotsEq placed
        refine ⟨same, ?_, ?_⟩
        · rw [readUint_slice b start stop position inside (by simp only [bytesPerOffset] at over ⊢; omega)]
          simp [slotsEq, Place.toSlot]
        · intro s e member
          simp only [List.mem_cons, reduceCtorEq, false_or] at member
          exact placed s e member

/-- Places and slots name the same bodies. -/
theorem placeStarts_toSlot (b : ByteArray) :
    ∀ places : List Place, bodyStarts (places.map (Place.toSlot b)) = placeStarts places
  -- Each place names the body its slot names, in order.
  | [] => rfl
  | .inline _ _ :: rest => by simp [bodyStarts, placeStarts, Place.toSlot, placeStarts_toSlot b rest]
  | .body _ :: rest => by simp [bodyStarts, placeStarts, Place.toSlot, placeStarts_toSlot b rest]

/-- Bodies taken as ranges cut the slices deserialization takes, or both refuse alike. -/
theorem takePlaces_cut (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop) :
    ∀ (places : List Place) (spans : List Nat), PlacesInside start stop places →
      (∀ pair ∈ (placeStarts places).zip spans, pair.1 + pair.2 ≤ stop - start) →
      CutAgree b start stop (takePlaces start places spans)
        (takeSlots (slice b start stop) (places.map (Place.toSlot b)) spans)
  -- No places take no bodies.
  | [], _, _, _ => by simp [takePlaces, takeSlots, CutAgree, Cuts]
  | .inline s e :: rest, spans, placed, bound => by
    -- An in-place field keeps its range, and the rest agree by induction.
    have ih := takePlaces_cut b start stop ordered rest spans (fun s e m => placed s e (by simp [m]))
      (by simpa [placeStarts] using bound)
    simp only [takePlaces, takeSlots, List.map_cons, Place.toSlot, Bind.bind, Except.bind, pure, Except.pure]
    revert ih
    cases takePlaces start rest spans <;> cases takeSlots (slice b start stop) (rest.map (Place.toSlot b)) spans <;>
      simp [CutAgree, Cuts]
    intro same within
    refine ⟨same, ?_, within⟩
    exact placed s e (by simp)
  -- A body with no span left is refused by both.
  | .body o :: rest, [], _, _ => by simp [takePlaces, takeSlots, Place.toSlot, CutAgree]
  | .body o :: rest, span :: spans, placed, bound => by
    -- A body runs over its span, which ends inside the range, and the rest agree by induction.
    have ih := takePlaces_cut b start stop ordered rest spans (fun s e m => placed s e (by simp [m]))
      (fun pair m => bound pair (by simp [placeStarts, m]))
    have mine := bound (o, span) (by simp [placeStarts])
    simp only [takePlaces, takeSlots, List.map_cons, Place.toSlot, Bind.bind, Except.bind, pure, Except.pure]
    revert ih
    cases takePlaces start rest spans <;> cases takeSlots (slice b start stop) (rest.map (Place.toSlot b)) spans <;>
      simp [CutAgree, Cuts]
    intro same within
    refine ⟨⟨by rw [slice_extract b start stop o (o + span) ordered (by simpa using mine), Nat.add_assoc],
      same⟩, ?_, within⟩
    simp at mine
    omega

/-- A struct's field ranges cut the slices deserialization cuts, or both refuse alike. -/
theorem fieldRanges_cut (fields : List Desc) (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop)
    (inside : stop ≤ b.size) :
    CutAgree b start stop (fieldRanges fields b start stop) (structSlices fields (slice b start stop)) := by
  -- The slice has the range's size, so the size checks read alike.
  have size := slice_size b start stop inside
  simp only [fieldRanges, structSlices, size]
  -- A size four-byte offsets cannot name is refused first, by both.
  by_cases huge : stop - start ≥ offsetBound
  · simp [huge, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, CutAgree]
  · simp only [offsetBound] at huge
    simp only [huge, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure]
    -- The budget check reads only the size, so it refuses alike.
    cases budget : structBudget fields (stop - start) with
    | error e => simp [CutAgree]
    | ok _ =>
      simp only
      -- The fixed part reads alike, giving the same places and the same end of the fixed part.
      have := readPlaces_cut b start stop ordered inside fields 0
      revert this
      cases readPlaces fields b start (stop - start) 0 <;> cases readSlots fields (slice b start stop) 0 <;>
        simp only [imp_self, CutAgree, false_implies]
      rename_i read slots
      obtain ⟨places, ending⟩ := read
      obtain ⟨slots, ending'⟩ := slots
      rintro ⟨rfl, rfl, placed⟩
      simp only [placeStarts_toSlot]
      -- With no variable fields, the size must be the fixed part's, and every place is in place.
      by_cases empty : (placeStarts places).isEmpty = true
      · simp only [empty, ↓reduceIte]
        by_cases wrong : (stop - start != ending) = true
        · simp [wrong]
        · simp only [wrong, Bool.false_eq_true, ↓reduceIte, Cuts]
          constructor
          · simp only [List.map_map]
            apply List.map_congr_left
            intro place _
            cases place <;> simp [Place.toSlot, Place.held, Slot.held, slice, Nat.min_le_left]
          · intro p member
            simp only [List.mem_map] at member
            obtain ⟨place, inPlaces, rfl⟩ := member
            cases place with
            | inline s e => exact placed s e inPlaces
            | body _ => simp [Place.held]; omega
      -- With variable fields, the first offset must end the fixed part, and then the spans decide.
      · simp only [empty, Bool.false_eq_true, ↓reduceIte]
        by_cases first : ((placeStarts places)[0]! != ending) = true
        · simp only [first, ↓reduceIte]
        · simp only [first, Bool.false_eq_true, ↓reduceIte]
          cases spans : offsetSpans (placeStarts places) (stop - start) with
          | error e => simp
          | ok spans' =>
            simp only
            exact takePlaces_cut b start stop ordered places spans' placed
              (offsetSpans_bound _ _ _ spans)

end Ssz.Native
