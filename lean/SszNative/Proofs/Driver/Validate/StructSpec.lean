import SszNative.Proofs.Driver.Validate.Seq

/-!
A struct's fields, by position: where each sits in the fixed part, where each body begins and ends.

The Lean check reads the fixed part into places, then turns the places into ranges.
Here both are written field by field, the form the native walk takes.
-/

namespace Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open Ssz Ssz.Native

/-- The bytes a field takes in the fixed part: its width, or an offset. -/
def slot (f : Desc) : Nat := if hasWidth f then fixedWidth f else 4

/-- A fixed part is the sum of its slots. -/
theorem leadingWidth_slot : ∀ fs : List Desc, Desc.leadingWidth fs = (fs.map slot).sum
  | [] => rfl
  | f :: fs => by rw [leadingWidth_cons, leadingWidth_slot fs]; simp [slot]

/-- The places of fields read from a position of the fixed part. -/
def placesFrom (b : ByteArray) (start : Nat) : List Desc → Nat → List Place
  | [], _ => []
  | f :: fs, pos =>
    (if hasWidth f then .inline (start + pos) (start + pos + fixedWidth f) else .body (offsetAt b (start + pos))) ::
      placesFrom b start fs (pos + slot f)

/-- The offsets of the variable fields, read from a position of the fixed part. -/
def varOffs (b : ByteArray) (start : Nat) : List Desc → Nat → List Nat
  | [], _ => []
  | f :: fs, pos =>
    if hasWidth f then varOffs b start fs (pos + slot f) else offsetAt b (start + pos) :: varOffs b start fs (pos + slot f)

/-- Reading the fixed part, its budget settled, reads every place. -/
theorem readPlaces_eq (b : ByteArray) (start size : Nat) : ∀ (fs : List Desc) (pos : Nat),
    pos + Desc.leadingWidth fs ≤ size →
    readPlaces fs b start size pos = .ok (placesFrom b start fs pos, pos + Desc.leadingWidth fs)
  | [], pos, _ => by simp [readPlaces, placesFrom, Desc.leadingWidth]
  | f :: fs, pos, h => by
    rw [leadingWidth_cons] at h
    have rest := readPlaces_eq b start size fs (pos + slot f) (by simp only [slot]; omega)
    simp only [readPlaces, fixedSize_eq f]
    by_cases hw : hasWidth f = true
    · simp only [hw, if_true, slot] at rest h ⊢
      rw [if_neg (by omega)]
      simp [rest, Bind.bind, Except.bind, pure, Except.pure, placesFrom, hw, slot, leadingWidth_cons,
        Nat.add_assoc]
    · simp only [hw, Bool.false_eq_true, if_false, slot] at rest h ⊢
      rw [if_neg (by simp [bytesPerOffset]; omega)]
      simp [rest, Bind.bind, Except.bind, pure, Except.pure, placesFrom, hw, slot, leadingWidth_cons,
        bytesPerOffset, Nat.add_assoc]

/-- The bodies' starts are the variable fields' offsets. -/
theorem placeStarts_eq (b : ByteArray) (start : Nat) : ∀ (fs : List Desc) (pos : Nat),
    placeStarts (placesFrom b start fs pos) = varOffs b start fs pos
  | [], _ => rfl
  | f :: fs, pos => by
    by_cases hw : hasWidth f = true <;>
      simp [placesFrom, varOffs, hw, placeStarts, placeStarts_eq b start fs]

/-- With every field fixed, there are no bodies. -/
theorem varOffs_all (b : ByteArray) (start : Nat) : ∀ (fs : List Desc) (pos : Nat), allHaveWidth fs = true →
    varOffs b start fs pos = []
  | [], _, _ => rfl
  | f :: fs, pos, h => by
    simp only [allHaveWidth, Bool.and_eq_true] at h
    simp [varOffs, h.1, varOffs_all b start fs _ h.2]

/-- With some field variable, there is a body. -/
theorem varOffs_some (b : ByteArray) (start : Nat) : ∀ (fs : List Desc) (pos : Nat), allHaveWidth fs = false →
    varOffs b start fs pos ≠ []
  | [], _, h => by simp [allHaveWidth] at h
  | f :: fs, pos, h => by
    by_cases hw : hasWidth f = true
    · simp only [allHaveWidth, hw, Bool.true_and] at h
      simp only [varOffs, hw, if_true]; exact varOffs_some b start fs _ h
    · simp [varOffs, hw]

/-- Where the next body begins, from a position of the fixed part on: the next variable field's offset, or the size. -/
def nextOff (b : ByteArray) (start size : Nat) (fs : List Desc) (pos : Nat) : Nat := (varOffs b start fs pos).headD size

/-- The range of one field: in place, or from its offset to the next body. -/
def rangeOf (b : ByteArray) (start size : Nat) (f : Desc) (fs : List Desc) (pos : Nat) : Nat × Nat :=
  if hasWidth f then (start + pos, start + pos + fixedWidth f)
  else (start + offsetAt b (start + pos), start + nextOff b start size fs (pos + 4))

/-- The ranges of fields from a position of the fixed part on. -/
def rangesFrom (b : ByteArray) (start size : Nat) : List Desc → Nat → List (Nat × Nat)
  | [], _ => []
  | f :: fs, pos => rangeOf b start size f fs pos :: rangesFrom b start size fs (pos + slot f)

/-- A table that checks out turns places into ranges, each body from its offset to the next. -/
theorem takePlaces_eq (b : ByteArray) (start size : Nat) : ∀ (fs : List Desc) (pos : Nat) (spans : List Nat),
    offsetSpans (varOffs b start fs pos) size = .ok spans →
    takePlaces start (placesFrom b start fs pos) spans = .ok (rangesFrom b start size fs pos)
  | [], _, _, _ => by simp [placesFrom, takePlaces, rangesFrom]
  | f :: fs, pos, spans, h => by
    by_cases hw : hasWidth f = true
    · simp only [varOffs, hw, if_true] at h
      simp [placesFrom, hw, takePlaces, takePlaces_eq b start size fs _ spans h, rangesFrom, rangeOf,
        Bind.bind, Except.bind, pure, Except.pure]
    · simp only [varOffs, hw, Bool.false_eq_true, if_false] at h
      have s4 : slot f = 4 := by simp [slot, hw]
      rw [s4] at h
      cases hl : varOffs b start fs (pos + 4) with
      | nil =>
        rw [hl] at h
        simp only [offsetSpans] at h
        split at h
        · cases h
        · rename_i le
          cases h
          have rest := takePlaces_eq b start size fs (pos + 4) [] (by rw [hl]; rfl)
          simp [placesFrom, hw, takePlaces, rest, rangesFrom, rangeOf, nextOff, slot, hl, Bind.bind, Except.bind,
            pure, Except.pure]
          omega
      | cons n L =>
        rw [hl] at h
        simp only [offsetSpans] at h
        split at h
        · cases h
        · rename_i le
          cases hs : offsetSpans (n :: L) size with
          | error x => rw [hs] at h; cases h
          | ok sp' =>
            rw [hs] at h; cases h
            have rest := takePlaces_eq b start size fs (pos + 4) sp' (by rw [hl]; exact hs)
            simp [placesFrom, hw, takePlaces, rest, rangesFrom, rangeOf, nextOff, slot, hl, Bind.bind, Except.bind,
              pure, Except.pure]
            omega

/-- Fields have one place each. -/
theorem placesFrom_length (b : ByteArray) (start : Nat) : ∀ (fs : List Desc) (pos : Nat),
    (placesFrom b start fs pos).length = fs.length
  | [], _ => rfl
  | _ :: fs, _ => by simp [placesFrom, placesFrom_length b start fs]

/-- Fields have one range each. -/
theorem rangesFrom_length (b : ByteArray) (start size : Nat) : ∀ (fs : List Desc) (pos : Nat),
    (rangesFrom b start size fs pos).length = fs.length
  | [], _ => rfl
  | _ :: fs, _ => by simp [rangesFrom, rangesFrom_length b start size fs]

/-- Places after the first fields are the places of the rest, from where those fields end. -/
theorem placesFrom_drop (b : ByteArray) (start : Nat) : ∀ (fs : List Desc) (pos j : Nat),
    (placesFrom b start fs pos).drop j = placesFrom b start (fs.drop j) (pos + Desc.leadingWidth (fs.take j))
  | [], _, _ => by simp [placesFrom]
  | _ :: _, pos, 0 => by simp [Desc.leadingWidth]
  | f :: fs, pos, j + 1 => by
    simp only [placesFrom, List.drop_succ_cons, List.take_succ_cons, placesFrom_drop b start fs, leadingWidth_cons]
    congr 1; simp [slot]; omega

/-- Ranges after the first fields are the ranges of the rest, from where those fields end. -/
theorem rangesFrom_drop (b : ByteArray) (start size : Nat) : ∀ (fs : List Desc) (pos j : Nat),
    (rangesFrom b start size fs pos).drop j =
      rangesFrom b start size (fs.drop j) (pos + Desc.leadingWidth (fs.take j))
  | [], _, _ => by simp [rangesFrom]
  | _ :: _, pos, 0 => by simp [Desc.leadingWidth]
  | f :: fs, pos, j + 1 => by
    simp only [rangesFrom, List.drop_succ_cons, List.take_succ_cons, rangesFrom_drop b start size fs,
      leadingWidth_cons]
    congr 1; simp [slot]; omega

/-- Fields checked in place, a stretch at a time. -/
theorem validateInline_split (b : ByteArray) : ∀ (fs : List Desc) (ps : List Place) (j : Nat),
    fs.length = ps.length →
    validateInline fs b ps = (do validateInline (fs.take j) b (ps.take j); validateInline (fs.drop j) b (ps.drop j))
  | [], [], _, _ => by simp [validateInline]; rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | f :: fs, p :: ps, 0, _ => by
    have : validateInline [] b [] = .ok () := by rw [validateInline]
    simp only [List.take_zero, List.drop_zero, this]; rfl
  | f :: fs, .inline s t :: ps, j + 1, h => by
    simp only [List.take_succ_cons, List.drop_succ_cons, validateInline]
    rw [validateInline_split b fs ps j (by simpa using h)]
    cases validateRange f b s t <;> simp [Bind.bind, Except.bind]
  | f :: fs, .body o :: ps, j + 1, h => by
    simp only [List.take_succ_cons, List.drop_succ_cons, validateInline]
    exact validateInline_split b fs ps j (by simpa using h)

/-- Fields checked against their ranges, a stretch at a time. -/
theorem validateFields_split (b : ByteArray) : ∀ (fs : List Desc) (rs : List (Nat × Nat)) (j : Nat),
    fs.length = rs.length →
    validateFields fs b rs = (do validateFields (fs.take j) b (rs.take j); validateFields (fs.drop j) b (rs.drop j))
  | [], [], _, _ => by simp [validateFields]; rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | f :: fs, r :: rs, 0, _ => by
    have : validateFields [] b [] = .ok () := by rw [validateFields]
    simp only [List.take_zero, List.drop_zero, this]; rfl
  | f :: fs, (s, t) :: rs, j + 1, h => by
    simp only [List.take_succ_cons, List.drop_succ_cons, validateFields]
    rw [validateFields_split b fs rs j (by simpa using h)]
    cases validateRange f b s t <;> simp [Bind.bind, Except.bind]

/-- Places all in place hold the fields' ranges. -/
theorem held_all (b : ByteArray) (start size : Nat) : ∀ (fs : List Desc) (pos : Nat), allHaveWidth fs = true →
    (placesFrom b start fs pos).map (Place.held start) = rangesFrom b start size fs pos
  | [], _, _ => rfl
  | f :: fs, pos, h => by
    simp only [allHaveWidth, Bool.and_eq_true] at h
    simp [placesFrom, h.1, Place.held, rangesFrom, rangeOf, held_all b start size fs _ h.2]

/-- A struct, refused case by case: budget, fixed fields, table, bodies. -/
theorem struct_outcome (fs : List Desc) (b : ByteArray) (start stop : Nat) :
    validateStruct fs b start stop =
      if 2 ^ 32 ≤ stop - start then .error (.offsetOverflow (stop - start))
      else if allHaveWidth fs then
        if stop - start ≠ fieldsWidth fs then .error (.scope (fieldsWidth fs) (stop - start))
        else validateFields fs b (rangesFrom b start (stop - start) fs 0)
      else if stop - start < Desc.leadingWidth fs then
        .error (.scopeTooSmall (Desc.leadingWidth fs) (stop - start))
      else (do
        validateInline fs b (placesFrom b start fs 0)
        if (varOffs b start fs 0)[0]! ≠ Desc.leadingWidth fs then
          .error (.firstOffset (Desc.leadingWidth fs) (varOffs b start fs 0)[0]!)
        else match spansOutcome (varOffs b start fs 0) (stop - start) with
          | .error x => .error x
          | .ok _ => validateFields fs b (rangesFrom b start (stop - start) fs 0)) := by
  have ob : offsetBound = 2 ^ 32 := rfl
  rw [validateStruct]
  simp only [fieldPlaces, structBudget, fieldsFixedSize_eq, ob]
  by_cases o : 2 ^ 32 ≤ stop - start
  · simp [o, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  by_cases all : allHaveWidth fs = true
  · by_cases sc : stop - start ≠ fieldsWidth fs
    · simp [o, all, sc, Bind.bind, Except.bind]
    simp only [ne_eq, Decidable.not_not] at sc
    have rp := readPlaces_eq b start (stop - start) fs 0 (by rw [leadingWidth_of_all fs all]; omega)
    have none := varOffs_all b start fs 0 all
    have b1 : (stop - start != fieldsWidth fs) = false := by simp [sc]
    have b2 : (stop - start != 0 + Desc.leadingWidth fs) = false := by simp [sc, leadingWidth_of_all fs all]
    rw [if_neg o, if_pos all, if_neg (show ¬ (stop - start ≠ fieldsWidth fs) by omega)]
    simp only [o, all, b1, b2, if_true, if_false, Bool.false_eq_true, rp, Bind.bind, Except.bind, pure,
      Except.pure, placeStarts_eq, none, List.isEmpty_nil, Bool.not_true, placeRanges,
      held_all b start (stop - start) fs 0 all]
  · simp only [Bool.not_eq_true] at all
    by_cases tl : stop - start < Desc.leadingWidth fs
    · simp [o, all, tl, Bind.bind, Except.bind]
    have rp := readPlaces_eq b start (stop - start) fs 0 (by omega)
    have some := varOffs_some b start fs 0 all
    simp only [o, all, tl, if_false, Bool.false_eq_true, rp, Nat.zero_add, Bind.bind, Except.bind, pure,
      Except.pure, placeStarts_eq, placeRanges]
    have ne : (varOffs b start fs 0).isEmpty = false := by
      cases h : varOffs b start fs 0 with
      | nil => exact absurd h some
      | cons _ _ => rfl
    simp only [ne, Bool.not_false, if_true, Bool.false_eq_true, if_false]
    cases validateInline fs b (placesFrom b start fs 0) with
    | error x => rfl
    | ok u =>
      simp only
      generalize (varOffs b start fs 0)[0]! = v0
      by_cases fo : v0 = Desc.leadingWidth fs
      · simp only [fo, ne_eq, not_true_eq_false, if_false, bne_self_eq_false, Bool.false_eq_true]
        cases hs : offsetSpans (varOffs b start fs 0) (stop - start) with
        | error x => simp [spansOutcome, hs, Except.map]
        | ok sp =>
          simp [spansOutcome, hs, Except.map, takePlaces_eq b start (stop - start) fs 0 sp hs]
      · simp [fo, throw, throwThe, MonadExceptOf.throw]

end Ssz.Native.Driver.Validate
