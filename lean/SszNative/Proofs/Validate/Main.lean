import SszNative.Proofs.Validate.Records

/-!
The native decoding check refuses exactly what deserialization refuses, for the same reason.

A range of an encoding stands for the slice deserialization would cut out of it.
-/

namespace Ssz.Native

open Ssz

/-- What accepted sequence ranges tell of a stride: it starts the range, and its elements are of the fixed width. -/
def StrideOk (element : Desc) (start stop : Nat) : Ranges → Prop
  | .stride s w c => s = start ∧ hasWidth element = true ∧ w = fixedWidth element ∧ w * c ≤ stop - start ∧
    stop - start < offsetBound
  | .listed _ => True

/-- Accepted vector ranges one width apart are elements of the fixed width, inside an offset-sized range. -/
theorem vectorRanges_stride (element : Desc) (length : Nat) (b : ByteArray) (start stop : Nat) (r : Ranges)
    (read : vectorRanges element length b start stop = .ok r) : StrideOk element start stop r := by
  simp only [vectorRanges, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure,
    Except.pure] at read
  -- An oversized range is refused before any element is placed.
  split at read
  · cases read
  · rename_i small
    -- Fixed-size elements give ranges one width apart, sized exactly.
    split at read
    · rename_i width fixed
      split at read
      · cases read
      · rename_i same
        cases read
        obtain ⟨has, eq⟩ := fixedWidth_of element width fixed
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at same
        exact ⟨rfl, has, eq.symm, by rw [same]; exact Nat.le_refl _, by simpa using small⟩
    -- Elements found through offsets give listed ranges, which promise nothing.
    · repeat' (first | (split at read) | (cases read; trivial) | trivial)
      all_goals (cases read <;> trivial)

/-- Accepted list ranges one width apart are elements of the fixed width, inside an offset-sized range. -/
theorem listRanges_stride (element : Desc) (limit : Option Nat) (b : ByteArray) (start stop : Nat) (r : Ranges)
    (read : listRanges element limit b start stop = .ok r) : StrideOk element start stop r := by
  simp only [listRanges, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure,
    Except.pure] at read
  -- An oversized range is refused before any element is placed.
  split at read
  · cases read
  · rename_i small
    -- An empty range gives listed ranges, which promise nothing.
    split at read
    · cases read; trivial
    · split at read
      -- Fixed-size elements give ranges one width apart, a whole number of them.
      · rename_i width fixed
        obtain ⟨has, eq⟩ := fixedWidth_of element width fixed
        have fits : width * ((stop - start) / width) ≤ stop - start := Nat.mul_div_le _ _
        have stride : r = .stride start width ((stop - start) / width) := by
          repeat' (first | (split at read) | (cases read; rfl) | (cases read))
        subst stride
        exact ⟨rfl, has, eq.symm, fits, by simpa using small⟩
      -- Elements found through offsets give listed ranges, which promise nothing.
      · repeat' (first | (split at read) | (cases read; trivial) | trivial)
        all_goals (cases read <;> trivial)

/-- The result an agreeing check and decoder share. -/
abbrev Agrees (check : Except Err Unit) (decoded : Except Err Value) : Prop :=
  check = decoded.map (fun _ => ())

/-- Listed ranges are refused in order, as deserializing their slices in order refuses them. -/
theorem validateEach_sound (element : Desc) (b : ByteArray) :
    ∀ ranges : List (Nat × Nat), (∀ p ∈ ranges, Agrees (validateRange element b p.1 p.2)
      (deserialize element (slice b p.1 p.2))) →
      validateEach element b ranges =
        (deserializeEach element (ranges.map fun p => slice b p.1 p.2)).map (fun _ => ())
  -- No ranges leave nothing to refuse.
  | [], _ => by simp [validateEach, deserializeEach, Except.map]
  | (s, e) :: rest, each => by
    -- The first range is refused as its slice is, and the rest follow by induction.
    rw [validateEach, List.map_cons, deserializeEach_cons, each (s, e) (by simp),
      validateEach_sound element b rest (fun p m => each p (by simp [m]))]

/-- A sequence's element ranges are refused as deserializing their slices refuses them. -/
theorem validateRanges_sound (element : Desc) (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop)
    (inside : stop ≤ b.size)
    (r : Ranges) (stride : StrideOk element start stop r)
    (each : ∀ p ∈ r.toList, Agrees (validateRange element b p.1 p.2) (deserialize element (slice b p.1 p.2))) :
    validateRanges element b r =
      (deserializeEach element (r.toList.map fun p => slice b p.1 p.2)).map (fun _ => ()) := by
  -- Listed ranges are checked one by one, and ranges one width apart by their probes.
  cases r with
  | listed ranges => rw [validateRanges]; exact validateEach_sound element b ranges each
  | stride s w c =>
    obtain ⟨rfl, has, rfl, fits, small⟩ := stride
    -- The records' slices, one width apart.
    have slices : (Ranges.stride s (fixedWidth element) c).toList.map (fun p => slice b p.1 p.2) =
        (List.range' 0 c).map fun k => slice b (s + k * fixedWidth element) (s + k * fixedWidth element +
          fixedWidth element) := by
      simp only [Ranges.toList, List.map_map, List.range_eq_range']
      apply List.map_congr_left
      intro k _
      simp [Nat.succ_mul, Nat.add_assoc]
    -- Each record is refused as its probes say.
    rw [slices, records_sound element b s (fixedWidth element) 0 c (fun k _ present => by
      have bound : (k + 1) * fixedWidth element ≤ fixedWidth element * c := by
        rw [Nat.mul_comm (fixedWidth element)]
        exact Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at bound
      exact plan_sound element b _ has (fun _ => by omega) (by omega))]
    -- Elements without probes always decode, and the others run the record loop.
    rw [validateRanges]
    split
    · rename_i none; rw [none, repeatProbes_nil]; rfl
    · rw [checkAllRecords_eq]
      have := checkRecords_eq b (fixedWidth element) (plan element) s 0 c
      simp only [Nat.zero_mul, Nat.add_zero] at this
      exact this

/-- That a type's check agrees with its decoder on every range inside an encoding. -/
def AgreesEverywhere (d : Desc) : Prop :=
  ∀ (b : ByteArray) (start stop : Nat), start ≤ stop → stop ≤ b.size →
    Agrees (validateRange d b start stop) (deserialize d (slice b start stop))

/-- Struct fields are refused in order, as deserializing their slices refuses them. -/
theorem validateFields_sound (b : ByteArray) :
    ∀ (fields : List Desc) (ranges : List (Nat × Nat)), (∀ field ∈ fields, AgreesEverywhere field) →
      (∀ p ∈ ranges, p.1 ≤ p.2 ∧ p.2 ≤ b.size) →
      validateFields fields b ranges =
        (deserializeFields fields (ranges.map fun p => slice b p.1 p.2)).map (fun _ => ())
  -- Fields and ranges run out together, or both sides report the mismatch alike.
  | [], [], _, _ => by simp [validateFields, deserializeFields, Except.map]
  | [], _ :: _, _, _ => by simp [validateFields, deserializeFields, Except.map]
  | _ :: _, [], _, _ => by simp [validateFields, deserializeFields, Except.map]
  | field :: fields, (s, e) :: ranges, each, within => by
    -- The first field is refused as its slice is, and the rest follow by induction.
    have here := within (s, e) (by simp)
    rw [validateFields, List.map_cons, deserializeFields_cons, each field (by simp) b s e here.1 here.2,
      validateFields_sound b fields ranges (fun f m => each f (by simp [m])) (fun p m => within p (by simp [m]))]

/-- The option a selector names is refused as deserializing it refuses it. -/
theorem validateOption_sound (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop) (inside : stop ≤ b.size) :
    ∀ (selectors : List Nat) (options : List Desc) (selector : Nat),
      (∀ option ∈ options, AgreesEverywhere option) →
      validateOption selectors options selector b start stop =
        (deserializeOption selectors options selector (slice b start stop)).map (fun _ => ())
  -- Selectors and options run out together, or both sides report the mismatch alike.
  | [], [], _, _ => by simp [validateOption, deserializeOption, Except.map]
  | [], _ :: _, _, _ => by simp [validateOption, deserializeOption, Except.map]
  | _ :: _, [], _, _ => by simp [validateOption, deserializeOption, Except.map]
  | chosen :: selectors, option :: options, selector, each => by
    rw [validateOption, deserializeOption]
    -- The option a selector names is checked, and the others are skipped on both sides.
    by_cases same : (chosen == selector) = true
    · simp only [same, ↓reduceIte, each option (by simp) b start stop ordered inside, Bind.bind, Except.bind,
        pure, Except.pure, Except.map]
      cases deserialize option (slice b start stop) <;> rfl
    · simp only [same, Bool.false_eq_true, ↓reduceIte]
      exact validateOption_sound b start stop ordered inside selectors options selector
        (fun o m => each o (by simp [m]))

/-- A sequence's check agrees with its decoder once their ranges and slices agree. -/
theorem sequence_sound (element : Desc) (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop)
    (inside : stop ≤ b.size) (ih : AgreesEverywhere element) (ranges : Except Err Ranges)
    (slices : Except Err (List Bytes)) (cut : CutAgree b start stop (ranges.map Ranges.toList) slices)
    (stride : ∀ r, ranges = .ok r → StrideOk element start stop r) :
    (do validateRanges element b (← ranges)) =
      (do let parts ← slices; return Value.seq (← deserializeEach element parts)).map (fun _ => ()) := by
  -- A refusal while placing elements is the same refusal on both sides.
  cases ranges with
  | error e =>
    cases slices with
    | error e' => simp only [Except.map, CutAgree] at cut; subst cut; rfl
    | ok _ => simp [Except.map, CutAgree] at cut
  | ok r =>
    cases slices with
    | error _ => simp [Except.map, CutAgree] at cut
    -- Placed elements cut the same slices, which are then refused alike.
    | ok parts =>
      simp only [Except.map, CutAgree, Cuts] at cut
      obtain ⟨rfl, within⟩ := cut
      simp only [Bind.bind, Except.bind, pure, Except.pure]
      rw [validateRanges_sound element b start stop ordered inside r (stride r rfl) (fun p m =>
        ih b p.1 p.2 (within p m).2.1 (by have := (within p m).2.2; omega))]
      cases deserializeEach element _ <;> rfl

/-- The native check of any range of an encoding agrees with deserializing its slice. -/
theorem validate_sound (d : Desc) : AgreesEverywhere d := by
  -- Types and their field lists are handled together, by mutual induction.
  induction d using Desc.rec (motive_2 := fun fields => ∀ field ∈ fields, AgreesEverywhere field) with
  -- Every field of a list agrees, the head directly and the tail by induction.
  | nil => rename_i held member; simp at member
  | cons field fields ihHead ihTail =>
    rename_i held member
    rcases List.mem_cons.mp member with first | later
    · subst held; exact ihHead
    · exact ihTail held later
  | bool | uint _ | byteVector _ | bitVector _ =>
    -- Fixed-size scalars are their sizes and probes.
    intro b start stop ordered inside
    unfold Agrees
    rw [validateRange, if_pos (show hasWidth _ = true from rfl)]
    exact validateFixed_sound _ rfl b start stop ordered inside
  | byteList limit =>
    -- A byte list is refused only for exceeding its limit.
    intro b start stop ordered inside
    unfold Agrees
    rw [validateRange, if_neg (by simp [hasWidth]), validateVariable]
    simp [deserialize, slice_size b start stop inside, throw, throwThe, MonadExceptOf.throw, Bind.bind,
      Except.bind, Except.map, pure, Except.pure]
    split <;> rfl
  | bitList limit =>
    -- Bit lists are refused for their delimiter alike on both sides.
    intro b start stop ordered inside
    unfold Agrees
    rw [validateRange, if_neg (by simp [hasWidth]), validateVariable, deserialize]
    have agrees := delimited_agrees b start stop (some limit) ordered inside
    rw [show discard (delimitedCount b start stop (some limit)) =
        (delimitedCount b start stop (some limit)).map (fun _ => ()) by
      cases delimitedCount b start stop (some limit) <;> rfl, agrees]
    cases unpackDelimited (some limit) (slice b start stop) <;> rfl
  | progressiveBitList limit =>
    intro b start stop ordered inside
    unfold Agrees
    rw [validateRange, if_neg (by simp [hasWidth]), validateVariable, deserialize]
    have agrees := delimited_agrees b start stop limit ordered inside
    rw [show discard (delimitedCount b start stop limit) = (delimitedCount b start stop limit).map (fun _ => ()) by
      cases delimitedCount b start stop limit <;> rfl, agrees]
    cases unpackDelimited limit (slice b start stop) <;> rfl
  | vector element length ih =>
    -- A vector is either fixed-size, or a sequence of ranges.
    intro b start stop ordered inside
    unfold Agrees
    by_cases has : hasWidth element = true
    · rw [validateRange, if_pos (show hasWidth (.vector element length) = true from has)]
      exact validateFixed_sound (.vector element length) has b start stop ordered inside
    · rw [validateRange, if_neg (show ¬ hasWidth (.vector element length) = true from has), validateVariable,
        deserialize]
      exact sequence_sound element b start stop ordered inside ih _ _
        (vectorRanges_cut element length b start stop ordered inside)
        (fun r read => vectorRanges_stride element length b start stop r read)
  | list element limit ih =>
    -- Lists are sequences of ranges, cut alike.
    intro b start stop ordered inside
    unfold Agrees
    rw [validateRange, if_neg (by simp [hasWidth]), validateVariable, deserialize]
    exact sequence_sound element b start stop ordered inside ih _ _
      (listRanges_cut element _ b start stop ordered inside)
      (fun r read => listRanges_stride element _ b start stop r read)
  | progressiveList element limit ih =>
    intro b start stop ordered inside
    unfold Agrees
    rw [validateRange, if_neg (by simp [hasWidth]), validateVariable, deserialize]
    exact sequence_sound element b start stop ordered inside ih _ _
      (listRanges_cut element _ b start stop ordered inside)
      (fun r read => listRanges_stride element _ b start stop r read)
  | container names fields ih =>
    -- A struct is either fixed-size, or its fields' ranges cut alike.
    intro b start stop ordered inside
    unfold Agrees
    by_cases has : allHaveWidth fields = true
    · rw [validateRange, if_pos (show hasWidth (.container names fields) = true from has)]
      exact validateFixed_sound (.container names fields)
        (show hasWidth (.container names fields) = true from has) b start stop ordered inside
    · rw [validateRange, if_neg (show ¬ hasWidth (.container names fields) = true from has), validateVariable]
      have cut := fieldRanges_cut fields b start stop ordered inside
      simp only [deserialize]
      revert cut
      cases fieldRanges fields b start stop <;> cases structSlices fields (slice b start stop) <;>
        simp only [CutAgree, Cuts, Bind.bind, Except.bind, Except.map, false_implies]
      · intro same; rw [same]
      · rename_i ranges slices
        rintro ⟨rfl, within⟩
        rw [validateFields_sound b fields ranges ih (fun p m => ⟨(within p m).2.1, by
          have := (within p m).2.2; omega⟩)]
        cases deserializeFields fields _ <;> rfl
  | progressiveContainer active names fields ih =>
    -- A progressive struct is checked as a struct of its present fields.
    intro b start stop ordered inside
    unfold Agrees
    by_cases has : allHaveWidth fields = true
    · rw [validateRange, if_pos (show hasWidth (.progressiveContainer active names fields) = true from has)]
      exact validateFixed_sound (.progressiveContainer active names fields)
        (show hasWidth (.progressiveContainer active names fields) = true from has) b start stop ordered inside
    · rw [validateRange, if_neg (show ¬ hasWidth (.progressiveContainer active names fields) = true from has),
        validateVariable]
      have cut := fieldRanges_cut fields b start stop ordered inside
      simp only [deserialize]
      revert cut
      cases fieldRanges fields b start stop <;> cases structSlices fields (slice b start stop) <;>
        simp only [CutAgree, Cuts, Bind.bind, Except.bind, Except.map, false_implies]
      · intro same; rw [same]
      · rename_i ranges slices
        rintro ⟨rfl, within⟩
        rw [validateFields_sound b fields ranges ih (fun p m => ⟨(within p m).2.1, by
          have := (within p m).2.2; omega⟩)]
        cases deserializeFields fields _ <;> rfl
  | compatibleUnion selectors options ih =>
    -- A union's selector byte is read alike, and the rest of the range is the chosen option.
    intro b start stop ordered inside
    unfold Agrees
    rw [validateRange, if_neg (by simp [hasWidth]), validateVariable, deserialize]
    have size := slice_size b start stop inside
    by_cases small : stop - start < 1
    · simp [small, size, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, Except.map]
    · simp only [small, size, ↓reduceIte]
      rw [slice_getElem! b start stop 0 inside (by omega), Nat.add_zero]
      have rest : (slice b start stop).extract 1 (slice b start stop).size = slice b (start + 1) stop := by
        rw [size, slice_extract b start stop 1 (stop - start) ordered (Nat.le_refl _)]
        congr 1
        omega
      rw [size] at rest
      rw [rest]
      exact validateOption_sound b (start + 1) stop (by omega) inside selectors options _ ih

/-- The native check of a whole encoding refuses exactly what deserialization refuses, with the same reason. -/
theorem validate_eq (d : Desc) (b : ByteArray) :
    validate d b = (deserialize d b.data).map (fun _ => ()) := by
  -- The whole encoding is its own slice.
  have whole : slice b 0 b.size = b.data := by
    simp [slice, ← ByteArray.size_data]
  rw [validate, validate_sound d b 0 b.size (Nat.zero_le _) (Nat.le_refl _), whole]

end Ssz.Native
