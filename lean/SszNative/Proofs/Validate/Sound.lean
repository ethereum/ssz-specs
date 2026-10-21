import SszNative.Proofs.Validate.Plan

/-! A fixed-size type's probes refuse a value of its width exactly as deserialization does. -/

namespace Ssz.Native

open Ssz

/-- Records one width apart, each refused as its probes refuse it. -/
theorem records_sound (element : Desc) (b : ByteArray) (start width : Nat) :
    ∀ index count, (∀ k, index ≤ k → k < index + count →
      (deserialize element (slice b (start + k * width) (start + k * width + width))).map (fun _ => ()) =
        checkProbes b (start + k * width) (plan element)) →
      (deserializeEach element ((List.range' index count).map fun k =>
        slice b (start + k * width) (start + k * width + width))).map (fun _ => ()) =
        checkProbes b start (repeatProbes (plan element) width index count)
  -- No records leave nothing to refuse.
  | _, 0, _ => by simp [deserializeEach, repeatProbes, checkProbes, Except.map]
  | index, count + 1, each => by
    -- The first record decodes as its probes say, and the rest follow by induction.
    rw [List.range'_succ, List.map_cons, deserializeEach_cons, repeatProbes, checkProbes_append,
      checkProbes_shift, each index (Nat.le_refl _) (by omega),
      records_sound element b start width (index + 1) count (fun k low high => each k (by omega) (by omega))]

/-- Fixed fields in place, each refused as its probes refuse it. -/
theorem fields_sound (b : ByteArray) (start width : Nat) (bounded : width < offsetBound)
    (inside : start + width ≤ b.size) :
    ∀ (fields : List Desc) (position : Nat),
      (∀ field ∈ fields, ∀ (b : ByteArray) (start : Nat), hasWidth field = true →
        (composite field = true → fixedWidth field < offsetBound) → start + fixedWidth field ≤ b.size →
        (deserialize field (slice b start (start + fixedWidth field))).map (fun _ => ()) =
          checkProbes b start (plan field)) →
      allHaveWidth fields = true → position + fieldsWidth fields ≤ width →
      (deserializeFields fields ((fixedSlots (slice b start (start + width)) fields position).map Slot.held)).map
        (fun _ => ()) = checkProbes b start (fieldsPlan fields position)
  -- No fields leave nothing to refuse.
  | [], _, _, _, _ => by simp [fixedSlots, deserializeFields, fieldsPlan, checkProbes, Except.map]
  | field :: fields, position, each, all, fits => by
    -- The first field sits in place at its position, and the rest follow it.
    simp only [allHaveWidth, Bool.and_eq_true] at all
    simp only [fieldsWidth] at fits
    simp only [fixedSlots, List.map_cons, Slot.held]
    -- The first field's slot is a range of the encoding, refused as its probes say.
    rw [slice_extract b start (start + width) _ _ (by omega) (by omega), deserializeFields_cons, fieldsPlan_cons,
      checkProbes_append, checkProbes_shift, ← Nat.add_assoc,
      each field (by simp) b (start + position) all.1 (fun _ => by omega) (by omega),
      fields_sound b start width bounded inside fields _ (fun f m => each f (by simp [m])) all.2 (by omega)]

/-- A fixed-size type's probes refuse a value of its width exactly as deserialization does. -/
theorem plan_sound (d : Desc) : ∀ (b : ByteArray) (start : Nat), hasWidth d = true →
    (composite d = true → fixedWidth d < offsetBound) → start + fixedWidth d ≤ b.size →
    (deserialize d (slice b start (start + fixedWidth d))).map (fun _ => ()) = checkProbes b start (plan d) := by
  induction d using Desc.rec
    (motive_2 := fun fields => ∀ field ∈ fields, ∀ (b : ByteArray) (start : Nat), hasWidth field = true →
      (composite field = true → fixedWidth field < offsetBound) → start + fixedWidth field ≤ b.size →
      (deserialize field (slice b start (start + fixedWidth field))).map (fun _ => ()) =
        checkProbes b start (plan field)) with
  | bool =>
    -- A boolean's one byte is its only probe.
    intro b start _ _ inside
    have size := slice_size b start (start + 1) inside
    have byte := slice_getElem! b start (start + 1) 0 inside (by omega)
    simp only [fixedWidth, Nat.add_zero, show start + 1 - start = 1 by omega] at size byte ⊢
    simp only [deserialize, size, byte, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    -- The byte decodes to false, to true, or is refused as no bit at all.
    split <;> simp_all [Except.map, plan, checkProbes, Probe.check, pure, Except.pure, Bind.bind, Except.bind,
      throw, throwThe, MonadExceptOf.throw]
  | uint width | byteVector width =>
    -- Integers and byte arrays decode from any bytes of their width, and have no probes.
    intro b start _ _ inside
    have size := slice_size b start (start + width) inside
    simp only [fixedWidth] at size ⊢
    simp [deserialize, size, plan, checkProbes, pure, Except.pure, Except.map]
  | bitVector length =>
    -- A bit vector is refused only for set padding bits in its last byte.
    intro b start _ _ inside
    have size := slice_size b start (start + (length + 7) / 8) inside
    simp only [fixedWidth] at size inside ⊢
    simp only [deserialize, size, plan, show start + (length + 7) / 8 - start = (length + 7) / 8 by omega,
      bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, Bind.bind,
      Except.bind, pure, Except.pure]
    by_cases padded : (length % 8 != 0 && (length + 7) / 8 > 0) = true
    · have last := slice_getElem! b start (start + (length + 7) / 8) ((length + 7) / 8 - 1) inside (by
        simp at padded; omega)
      simp only [padded, ↓reduceIte, checkProbes, Probe.check, last]
      split <;> rfl
    · simp only [padded, Bool.false_eq_true, ↓reduceIte]
      simp [checkProbes, Except.map]
  | byteList | bitList | progressiveBitList | list | progressiveList | compatibleUnion =>
    -- Every other kind of type has no fixed size.
    intro _ _ fixed; simp [hasWidth] at fixed
  | vector element length ih =>
    -- A vector of fixed-size elements fits under the offset bound, so its size check passes.
    intro b start fixed bounded inside
    simp only [hasWidth] at fixed
    have elementSize : element.fixedSize = some (fixedWidth element) := by rw [fixedSize_eq, if_pos fixed]
    have small := bounded rfl
    simp only [fixedWidth] at small inside ⊢
    have size := slice_size b start (start + fixedWidth element * length) inside
    simp only [deserialize, vectorSlices, size, show start + fixedWidth element * length - start =
      fixedWidth element * length by omega, elementSize]
    simp only [offsetBound] at small
    simp only [show ¬ fixedWidth element * length ≥ 2 ^ (8 * bytesPerOffset) by omega, ↓reduceIte,
      bne_self_eq_false, Bool.false_eq_true, Bind.bind, Except.bind,
      pure, Except.pure]
    -- Each element's slice is a range of the encoding, one width apart.
    have slices : ((List.range length).map fun i =>
        (slice b start (start + fixedWidth element * length)).extract (i * fixedWidth element)
          ((i + 1) * fixedWidth element)) =
        (List.range' 0 length).map fun k =>
          slice b (start + k * fixedWidth element) (start + k * fixedWidth element + fixedWidth element) := by
      rw [List.range_eq_range']
      apply List.map_congr_left
      intro k member
      have := List.mem_range'.mp member
      have bound : (k + 1) * fixedWidth element ≤ fixedWidth element * length := by
        rw [Nat.mul_comm (fixedWidth element)]
        exact Nat.mul_le_mul_right _ (by omega)
      rw [slice_extract b start _ _ _ (by omega) (by omega), Nat.succ_mul, Nat.add_assoc]
    -- The elements are checked one after the other, as their repeated probes are.
    rw [slices, plan_vector]
    have each := records_sound element b start (fixedWidth element) 0 length (fun k _ present => by
      have bound : (k + 1) * fixedWidth element ≤ fixedWidth element * length := by
        rw [Nat.mul_comm (fixedWidth element)]
        exact Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at bound
      exact ih b (start + k * fixedWidth element) fixed (fun _ => by simp only [offsetBound]; omega)
        (by omega))
    rw [← each]
    cases deserializeEach element _ <;> rfl
  | container _ fields ih | progressiveContainer _ _ fields ih =>
    -- A struct of fixed-size fields fits under the offset bound, and its slots all sit in place.
    intro b start fixed bounded inside
    simp only [hasWidth] at fixed
    have small := bounded rfl
    simp only [fixedWidth] at small inside ⊢
    have size := slice_size b start (start + fieldsWidth fields) inside
    rw [show start + fieldsWidth fields - start = fieldsWidth fields by omega] at size
    simp only [offsetBound] at small
    simp only [deserialize, structSlices, structBudget, size, fieldsFixedSize_eq, fixed, ↓reduceIte,
      bne_self_eq_false, Bool.false_eq_true, show ¬ fieldsWidth fields ≥ 2 ^ (8 * bytesPerOffset) by omega,
      readSlots_fixed (slice b start (start + fieldsWidth fields)) fields 0 fixed (by omega),
      bodyStarts_fixedSlots, List.isEmpty_nil, Nat.zero_add,
      Bind.bind, Except.bind, pure, Except.pure, plan]
    -- The fields are checked one after the other, as their shifted probes are.
    rw [← fields_sound b start (fieldsWidth fields) small inside fields 0 ih fixed (by omega)]
    cases deserializeFields fields _ <;> rfl
  -- A field list's every member satisfies the claim, the head directly and the tail by induction.
  | nil => rename_i held member _ _ _ _ _; simp at member
  | cons field fields ihHead ihTail =>
    rename_i held member b start fixed bounded inside
    rcases List.mem_cons.mp member with first | later
    · subst held; exact ihHead b start fixed bounded inside
    · exact ihTail held later b start fixed bounded inside

end Ssz.Native
