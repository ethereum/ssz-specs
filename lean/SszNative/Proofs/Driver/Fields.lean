import SszNative.Proofs.Driver.View

/-!
The struct view driver writes the ranges `fieldRanges` computes.

The reference reads the fixed part into places, checks the offsets as a table, then takes each body.
Here the same ranges are described field by field, which is how the driver writes them.
-/

namespace Ssz.Native.Driver

open Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Plan

/-- The places of fields from a position of a struct's fixed part, when all of it lies inside the struct. -/
def placesFrom : List Desc → ByteArray → Nat → Nat → List Place
  | [], _, _, _ => []
  | field :: fields, b, start, position =>
    (match field.fixedSize with
      | some width => Place.inline (start + position) (start + position + width)
      | none => Place.body (offsetAt b (start + position))) ::
      placesFrom fields b start (position + field.fixedSize.getD bytesPerOffset)

/-- The width a field takes in the fixed part: its own, or an offset's. -/
theorem leadingWidth_cons (field : Desc) (fields : List Desc) :
    Desc.leadingWidth (field :: fields) = field.fixedSize.getD bytesPerOffset + Desc.leadingWidth fields := rfl

set_option linter.unusedSimpArgs false in
/-- With the fixed part inside the struct, reading it gives the places field by field. -/
theorem readPlaces_inside (b : ByteArray) (start size : Nat) : ∀ (fields : List Desc) (position : Nat),
    position + Desc.leadingWidth fields ≤ size →
    readPlaces fields b start size position =
      .ok (placesFrom fields b start position, position + Desc.leadingWidth fields)
  | [], position, _ => by simp [readPlaces, placesFrom, Desc.leadingWidth]
  | field :: fields, position, inside => by
    rw [leadingWidth_cons] at inside
    cases fixed : field.fixedSize with
    | some width =>
      have rest := readPlaces_inside b start size fields (position + width) (by simp [fixed] at inside; omega)
      simp only [readPlaces, fixed, placesFrom, Option.getD_some, rest, leadingWidth_cons]
      simp [show ¬ position + width > size by simp [fixed] at inside; omega, Bind.bind, Except.bind, pure,
        Except.pure]
      omega
    | none =>
      have rest := readPlaces_inside b start size fields (position + bytesPerOffset)
        (by simp [fixed] at inside; omega)
      simp only [readPlaces, fixed, placesFrom, Option.getD_none, rest, leadingWidth_cons]
      simp [show ¬ position + bytesPerOffset > size by simp [fixed] at inside; omega, Bind.bind, Except.bind,
        pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
      omega

/-- The fields' ranges, each body running to where the next body begins, or to the end. -/
def rangesOf (start size : Nat) : List Place → List (Nat × Nat)
  | [] => []
  | .inline s e :: rest => (s, e) :: rangesOf start size rest
  | .body o :: rest => (start + o, start + (placeStarts rest).headD size) :: rangesOf start size rest

/-- Bodies cut by an accepted table run from each offset to the next offset, the last to the end. -/
theorem takePlaces_accepted (start size : Nat) : ∀ (places : List Place) (spans : List Nat),
    offsetSpans (placeStarts places) size = .ok spans → takePlaces start places spans = .ok (rangesOf start size places)
  | [], _, _ => by simp [takePlaces, rangesOf]
  | .inline s e :: rest, spans, read => by
    have := takePlaces_accepted start size rest spans (by simpa [placeStarts] using read)
    simp [takePlaces, rangesOf, this, Bind.bind, Except.bind, pure, Except.pure]
  | .body o :: rest, spans, read => by
    simp only [placeStarts] at read
    cases tail : placeStarts rest with
    | nil =>
      rw [tail] at read
      simp only [offsetSpans] at read
      split at read
      · cases read
      · rename_i inside
        cases read
        have := takePlaces_accepted start size rest [] (by simp [tail, offsetSpans])
        simp [takePlaces, rangesOf, this, tail, Bind.bind, Except.bind, pure, Except.pure]
        omega
    | cons next more =>
      rw [tail] at read
      simp only [offsetSpans] at read
      split at read
      · cases read
      · rename_i ordered
        cases rest' : offsetSpans (next :: more) size with
        | error e => simp [rest', Bind.bind, Except.bind] at read
        | ok spans' =>
          simp [rest', Bind.bind, Except.bind, pure, Except.pure] at read
          subst read
          have := takePlaces_accepted start size rest spans' (by rw [tail]; exact rest')
          simp [takePlaces, rangesOf, this, tail, Bind.bind, Except.bind, pure, Except.pure]
          omega

/-- A struct of fixed width has a fixed part as wide as the whole struct. -/
theorem leadingWidth_fixed : ∀ (fields : List Desc) (width : Nat), Desc.fieldsFixedSize fields = some width →
    Desc.leadingWidth fields = width
  | [], width, h => by simp [Desc.fieldsFixedSize] at h; simp [Desc.leadingWidth, h]
  | field :: fields, width, h => by
    simp only [Desc.fieldsFixedSize] at h
    cases a : field.fixedSize <;> cases b : Desc.fieldsFixedSize fields <;> simp [a, b] at h
    rename_i x y
    rw [leadingWidth_cons, a, leadingWidth_fixed fields y b]
    simp; omega

/-- Fields with no body among their places are all fixed-size. -/
theorem placesFrom_fixed (b : ByteArray) (start : Nat) : ∀ (fields : List Desc) (position : Nat),
    placeStarts (placesFrom fields b start position) = [] → ∃ width, Desc.fieldsFixedSize fields = some width
  | [], _, _ => ⟨0, rfl⟩
  | field :: fields, position, none_ => by
    cases fixed : field.fixedSize with
    | none => simp [placesFrom, fixed, placeStarts] at none_
    | some width =>
      simp only [placesFrom, fixed, placeStarts] at none_
      obtain ⟨rest, h⟩ := placesFrom_fixed b start fields _ none_
      exact ⟨width + rest, by simp [Desc.fieldsFixedSize, fixed, h]⟩

/-- Places with no body are all held in place, and their ranges are their own. -/
theorem rangesOf_inline (start size : Nat) : ∀ (places : List Place), placeStarts places = [] →
    rangesOf start size places = places.map (Place.held start)
  | [], _ => rfl
  | .inline s e :: rest, h => by
    simp [rangesOf, Place.held, rangesOf_inline start size rest (by simpa [placeStarts] using h)]
  | .body _ :: _, h => by simp [placeStarts] at h

/-- Whether a struct's size fits the budget its fields declare. -/
def budgetOk (fields : List Desc) (size : Nat) : Prop :=
  match Desc.fieldsFixedSize fields with
  | some width => size = width
  | none => Desc.leadingWidth fields ≤ size

/-- Whether a table of offsets is accepted: the first at the end of the fixed part, each body inside the struct. -/
def tableOk (offsets : List Nat) (leading size : Nat) : Prop :=
  offsets = [] ∨ (offsets.head? = some leading ∧ ∀ k (h : k < offsets.length), offsets[k] ≤ nextOffset offsets size k)

set_option linter.unusedSimpArgs false in
/-- A struct within its budget and with an accepted table has the ranges of its places. -/
theorem fieldRanges_accepted (fields : List Desc) (b : ByteArray) (start stop : Nat)
    (small : ¬ offsetBound ≤ stop - start) (budget : budgetOk fields (stop - start))
    (table : tableOk (placeStarts (placesFrom fields b start 0)) (Desc.leadingWidth fields) (stop - start)) :
    fieldRanges fields b start stop = .ok (rangesOf start (stop - start) (placesFrom fields b start 0)) := by
  have inside : 0 + Desc.leadingWidth fields ≤ stop - start := by
    simp only [budgetOk] at budget
    cases fixed : Desc.fieldsFixedSize fields with
    | none => simp [fixed] at budget; omega
    | some width => simp [fixed] at budget; rw [leadingWidth_fixed fields width fixed]; omega
  have budgetRead : structBudget fields (stop - start) = .ok () := by
    simp only [budgetOk] at budget
    simp only [structBudget]
    cases fixed : Desc.fieldsFixedSize fields with
    | none => simp [fixed] at budget; simp [show ¬ stop - start < Desc.leadingWidth fields by omega]
    | some width => simp [fixed] at budget; simp [budget]
  have read := readPlaces_inside b start (stop - start) fields 0 inside
  simp only [fieldRanges, fieldPlaces, small, if_false, budgetRead, read, throw, throwThe, MonadExceptOf.throw,
    Bind.bind, Except.bind, pure, Except.pure, Nat.zero_add, ge_iff_le]
  simp only [placeRanges]
  rcases table with none_ | ⟨head, ordered⟩
  · obtain ⟨width, fixed⟩ := placesFrom_fixed b start fields 0 none_
    have lead := leadingWidth_fixed fields width fixed
    simp only [budgetOk, fixed] at budget
    simp [none_, lead, budget, rangesOf_inline start _ _ none_, pure, Except.pure]
  · have nonEmpty : placeStarts (placesFrom fields b start 0) ≠ [] := by intro h; simp [h] at head
    obtain ⟨spans, spansRead, -⟩ := offsetSpans_ordered start (stop - start) _ ordered
    have first : (placeStarts (placesFrom fields b start 0))[0]! = Desc.leadingWidth fields := by
      cases h : placeStarts (placesFrom fields b start 0) with
      | nil => exact absurd h nonEmpty
      | cons x xs => rw [h] at head; simp at head; simp [head]
    simp [nonEmpty, first, spansRead, takePlaces_accepted start _ _ spans spansRead, Bind.bind, Except.bind]

set_option linter.unusedSimpArgs false in
/-- A struct over its budget, or with a refused table, is refused. -/
theorem fieldRanges_refused (fields : List Desc) (b : ByteArray) (start stop : Nat)
    (small : ¬ offsetBound ≤ stop - start)
    (refused : ¬ (budgetOk fields (stop - start) ∧
      tableOk (placeStarts (placesFrom fields b start 0)) (Desc.leadingWidth fields) (stop - start))) :
    ∀ x, fieldRanges fields b start stop ≠ .ok x := by
  intro x h
  apply refused
  -- An accepted struct passed every check, so its budget and its table were accepted.
  simp only [fieldRanges, fieldPlaces, small, if_false, throw, throwThe, MonadExceptOf.throw, Bind.bind,
    Except.bind, ge_iff_le] at h
  cases budgetRead : structBudget fields (stop - start) with
  | error e => simp [budgetRead] at h
  | ok u =>
    simp [budgetRead] at h
    have budget : budgetOk fields (stop - start) := by
      simp only [structBudget] at budgetRead
      simp only [budgetOk]
      cases fixed : Desc.fieldsFixedSize fields with
      | none => simp [fixed] at budgetRead ⊢; omega
      | some width => simp [fixed] at budgetRead ⊢; omega
    have inside : 0 + Desc.leadingWidth fields ≤ stop - start := by
      simp only [budgetOk] at budget
      cases fixed : Desc.fieldsFixedSize fields with
      | none => simp [fixed] at budget; omega
      | some width => simp [fixed] at budget; rw [leadingWidth_fixed fields width fixed]; omega
    rw [readPlaces_inside b start (stop - start) fields 0 inside] at h
    simp only [Nat.zero_add, placeRanges] at h
    refine ⟨budget, ?_⟩
    by_cases none_ : placeStarts (placesFrom fields b start 0) = []
    · exact Or.inl none_
    · right
      simp only [none_, List.isEmpty_iff, if_false] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
      · rename_i first
        cases spans : offsetSpans (placeStarts (placesFrom fields b start 0)) (stop - start) with
        | error e => simp [spans, Bind.bind, Except.bind] at h
        | ok spans' =>
          refine ⟨?_, fun k hk => ?_⟩
          · cases hs : placeStarts (placesFrom fields b start 0) with
            | nil => exact absurd hs none_
            | cons y ys => rw [hs] at first; simp at first; simp [first]
          · refine Nat.le_of_not_lt (fun bad => ?_)
            obtain ⟨e, err⟩ := offsetSpans_unordered (stop - start) _ ⟨k, hk, bad⟩
            rw [spans] at err; cases err

/-- Fields have one place each. -/
theorem placesFrom_length (b : ByteArray) (start : Nat) : ∀ (fields : List Desc) (position : Nat),
    (placesFrom fields b start position).length = fields.length
  | [], _ => rfl
  | _ :: fields, _ => by simp [placesFrom, placesFrom_length b start fields]

/-- A field's place sits at its position in the fixed part: in place, or as an offset to read there. -/
theorem placesFrom_get (b : ByteArray) (start : Nat) : ∀ (fields : List Desc) (position i : Nat)
    (small : i < fields.length),
    (placesFrom fields b start position)[i]'(by rw [placesFrom_length]; exact small) =
      match fields[i].fixedSize with
      | some width => Place.inline (start + (position + Desc.leadingWidth (fields.take i)))
          (start + (position + Desc.leadingWidth (fields.take i)) + width)
      | none => Place.body (offsetAt b (start + (position + Desc.leadingWidth (fields.take i))))
  | [], _, _, small => absurd small (by simp)
  | field :: fields, position, 0, _ => by
    simp only [placesFrom, List.getElem_cons_zero, List.take_zero, Desc.leadingWidth, Nat.add_zero]
  | field :: fields, position, i + 1, small => by
    simp only [placesFrom, List.getElem_cons_succ, List.take_succ_cons, leadingWidth_cons]
    rw [placesFrom_get b start fields _ i (by simpa using small)]
    simp only [Nat.add_assoc]

/-- Each place has one range. -/
theorem rangesOf_length (start size : Nat) : ∀ (places : List Place), (rangesOf start size places).length = places.length
  | [] => rfl
  | .inline _ _ :: rest => by simp [rangesOf, rangesOf_length start size rest]
  | .body _ :: rest => by simp [rangesOf, rangesOf_length start size rest]

/-- A place's range: its own bytes, or from its offset to the next body's, or to the end. -/
theorem rangesOf_get (start size : Nat) : ∀ (places : List Place) (j : Nat) (small : j < places.length),
    (rangesOf start size places)[j]'(by rw [rangesOf_length]; exact small) =
      match places[j] with
      | .inline s e => (s, e)
      | .body o => (start + o, start + (placeStarts (places.drop (j + 1))).headD size)
  | [], _, small => absurd small (by simp)
  | .inline _ _ :: rest, 0, _ => rfl
  | .body _ :: rest, 0, _ => rfl
  | .inline _ _ :: rest, j + 1, small => by
    simp only [rangesOf, List.getElem_cons_succ, List.drop_succ_cons]
    exact rangesOf_get start size rest j (by simpa using small)
  | .body _ :: rest, j + 1, small => by
    simp only [rangesOf, List.getElem_cons_succ, List.drop_succ_cons]
    exact rangesOf_get start size rest j (by simpa using small)

/-- Whether a place holds an offset to a body. -/
def _root_.Ssz.Native.Place.isBody : Place → Bool
  | .inline _ _ => false
  | .body _ => true

/-- The last place holding a body among the first ones. -/
def lastBody (places : List Place) : Nat → Option Nat
  | 0 => none
  | i + 1 => if (places[i]?.map Place.isBody).getD false then some i else lastBody places i

/-- The last body among the first places comes before them, and every place after it is in place. -/
theorem lastBody_some (places : List Place) : ∀ (i j : Nat), lastBody places i = some j →
    j < i ∧ ∃ h : j < places.length, places[j].isBody = true ∧
      ∀ k (hk : k < places.length), j < k → k < i → places[k].isBody = false
  | 0, j, h => by simp [lastBody] at h
  | i + 1, j, h => by
    simp only [lastBody] at h
    split at h
    · rename_i body
      cases h
      have small : i < places.length := by
        rcases Nat.lt_or_ge i places.length with h | h
        · exact h
        · simp [List.getElem?_eq_none h] at body
      refine ⟨by omega, small, by simpa [List.getElem?_eq_getElem small] using body, fun k _ a b => by omega⟩
    · rename_i inline
      obtain ⟨below, small, isBody, after⟩ := lastBody_some places i j h
      refine ⟨by omega, small, isBody, fun k hk a b => ?_⟩
      by_cases at_ : k = i
      · subst at_; simpa [List.getElem?_eq_getElem hk] using inline
      · exact after k hk a (by omega)

/-- With no body among the first places, all of them are in place. -/
theorem lastBody_none (places : List Place) : ∀ (i : Nat), lastBody places i = none →
    ∀ k (hk : k < places.length), k < i → places[k].isBody = false
  | 0, _, k, _, h => absurd h (Nat.not_lt_zero _)
  | i + 1, h, k, hk, below => by
    simp only [lastBody] at h
    split at h
    · cases h
    · rename_i inline
      by_cases at_ : k = i
      · subst at_; simpa [List.getElem?_eq_getElem hk] using inline
      · exact lastBody_none places i h k hk (by omega)

/-- Places all in place hold no body. -/
theorem placeStarts_inline : ∀ (places : List Place), (∀ k (hk : k < places.length), places[k].isBody = false) →
    placeStarts places = []
  | [], _ => rfl
  | .inline _ _ :: rest, h => by
    simp only [placeStarts]
    exact placeStarts_inline rest (fun k hk => by
      have := h (k + 1) (by simpa using hk)
      rwa [List.getElem_cons_succ] at this)
  | .body _ :: _, h => absurd (h 0 (by simp)) (by simp [Place.isBody])

/-- The first body after some places in place is the body that follows them. -/
theorem placeStarts_drop_body : ∀ (places : List Place) (j i o : Nat) (hi : i < places.length),
    j ≤ i → places[i] = .body o → (∀ k (hk : k < places.length), j ≤ k → k < i → places[k].isBody = false) →
    (placeStarts (places.drop j)).headD 0 = o
  | [], _, _, _, hi, _, _, _ => absurd hi (by simp)
  | p :: rest, 0, 0, o, _, _, h, _ => by simp at h; subst h; simp [placeStarts]
  | p :: rest, 0, i + 1, o, hi, _, h, inline => by
    have first := inline 0 (by simp) (Nat.le_refl _) (by omega)
    cases p with
    | body _ => simp [Place.isBody] at first
    | inline s e =>
      simp only [List.drop_zero, placeStarts]
      have := placeStarts_drop_body rest 0 i o (by simpa using hi) (Nat.zero_le _) (by simpa using h)
        (fun k hk a b => by
          have := inline (k + 1) (by simpa using hk) (by omega) (by omega)
          rwa [List.getElem_cons_succ] at this)
      simpa using this
  | p :: rest, j + 1, i, o, hi, le, h, inline => by
    cases i with
    | zero => omega
    | succ i =>
      simp only [List.drop_succ_cons]
      exact placeStarts_drop_body rest j i o (by simpa using hi) (by omega) (by simpa using h)
        (fun k hk a b => by
          have := inline (k + 1) (by simpa using hk) (by omega) (by omega)
          rwa [List.getElem_cons_succ] at this)

/-- The bodies of two runs of places, one after the other. -/
theorem placeStarts_append : ∀ (a c : List Place), placeStarts (a ++ c) = placeStarts a ++ placeStarts c
  | [], _ => rfl
  | .inline _ _ :: rest, c => by simp [placeStarts, placeStarts_append rest c]
  | .body _ :: rest, c => by simp [placeStarts, placeStarts_append rest c]

/-- Whether a table of offsets opens bodies inside a struct: each offset at most the next, the last at most the end. -/
def spanOk (size : Nat) : List Nat → Bool
  | [] => true
  | [x] => decide (x ≤ size)
  | x :: y :: rest => decide (x ≤ y) && spanOk size (y :: rest)

/-- A table is accepted exactly when it opens bodies inside the struct. -/
theorem offsetSpans_ok_iff (size : Nat) : ∀ (offsets : List Nat),
    (∃ spans, offsetSpans offsets size = .ok spans) ↔ spanOk size offsets = true
  | [] => by simp [offsetSpans, spanOk]
  | [x] => by
    simp only [offsetSpans, spanOk, decide_eq_true_eq]
    by_cases h : size < x <;> simp [h] <;> omega
  | x :: y :: rest => by
    simp only [offsetSpans, spanOk, Bool.and_eq_true, decide_eq_true_eq]
    by_cases h : y < x
    · simp [h]; omega
    · have ih := offsetSpans_ok_iff size (y :: rest)
      cases tail : offsetSpans (y :: rest) size with
      | error e => simp [h, tail, Bind.bind, Except.bind] at ih ⊢; exact fun _ => ih
      | ok spans => simp [h, tail, Bind.bind, Except.bind, pure, Except.pure] at ih ⊢; exact ⟨by omega, ih⟩

/-- The check the struct driver makes of its offsets, one at a time, from the offset before. -/
def checkFrom (leading : Nat) : Option Nat → List Nat → Bool
  | _, [] => true
  | none, o :: rest => (o == leading) && checkFrom leading (some o) rest
  | some p, o :: rest => decide (p ≤ o) && checkFrom leading (some o) rest

/-- The last offset seen, from the offset before. -/
def lastOf : Option Nat → List Nat → Option Nat
  | p, [] => p
  | _, o :: rest => lastOf (some o) rest

/-- One more offset is checked against the last one, or against the fixed part's end when it is the first. -/
theorem checkFrom_snoc (leading o : Nat) : ∀ (p : Option Nat) (offsets : List Nat),
    checkFrom leading p (offsets ++ [o]) = (checkFrom leading p offsets &&
      match lastOf p offsets with
      | none => o == leading
      | some l => decide (l ≤ o))
  | none, [] => by simp [checkFrom, lastOf]
  | some p, [] => by simp [checkFrom, lastOf]
  | none, x :: rest => by
    simp only [List.cons_append, checkFrom, lastOf, checkFrom_snoc leading o (some x) rest, Bool.and_assoc]
  | some p, x :: rest => by
    simp only [List.cons_append, checkFrom, lastOf, checkFrom_snoc leading o (some x) rest, Bool.and_assoc]

/-- The last offset seen after one more is that one. -/
theorem lastOf_snoc (o : Nat) : ∀ (p : Option Nat) (offsets : List Nat), lastOf p (offsets ++ [o]) = some o
  | _, [] => rfl
  | _, x :: rest => by simp [lastOf, lastOf_snoc o (some x) rest]

/-- From an offset, the check and a last offset inside the struct are the spans inside the struct. -/
theorem checkFrom_some (leading size : Nat) : ∀ (p : Nat) (offsets : List Nat),
    (checkFrom leading (some p) offsets = true ∧ ∀ l, lastOf (some p) offsets = some l → l ≤ size) ↔
      spanOk size (p :: offsets) = true
  | p, [] => by simp [checkFrom, lastOf, spanOk]
  | p, x :: rest => by
    have ih := checkFrom_some leading size x rest
    simp only [checkFrom, lastOf, spanOk, Bool.and_eq_true, decide_eq_true_eq] at ih ⊢
    constructor
    · rintro ⟨⟨a, b⟩, c⟩; exact ⟨a, ih.mp ⟨b, c⟩⟩
    · rintro ⟨a, b⟩; exact ⟨⟨a, (ih.mpr b).1⟩, (ih.mpr b).2⟩

/-- Whether a struct's table is accepted: no bodies, or the first at the end of the fixed part and all inside. -/
def tableAccepts (offsets : List Nat) (leading size : Nat) : Prop :=
  offsets = [] ∨ (offsets.head? = some leading ∧ spanOk size offsets = true)

/-- The driver's check and its last test are the table being accepted. -/
theorem checkFrom_none (leading size : Nat) (offsets : List Nat) :
    (checkFrom leading none offsets = true ∧ ∀ l, lastOf none offsets = some l → l ≤ size) ↔
      tableAccepts offsets leading size := by
  cases offsets with
  | nil => simp [checkFrom, lastOf, tableAccepts]
  | cons x rest =>
    have := checkFrom_some leading size x rest
    simp only [checkFrom, lastOf, tableAccepts, Bool.and_eq_true, beq_iff_eq, reduceCtorEq, false_or,
      List.head?_cons, Option.some.injEq] at this ⊢
    constructor
    · rintro ⟨⟨a, b⟩, c⟩; exact ⟨a, this.mp ⟨b, c⟩⟩
    · rintro ⟨a, b⟩; exact ⟨⟨a, (this.mpr b).1⟩, (this.mpr b).2⟩

/-- An accepted table, as the reference checks it and as the driver does. -/
theorem tableOk_iff_accepts (offsets : List Nat) (leading size : Nat) :
    tableOk offsets leading size ↔ tableAccepts offsets leading size := by
  simp only [tableOk, tableAccepts]
  -- Offsets each at most where their body ends are exactly the spans the table accepts.
  have spans : (∀ k (h : k < offsets.length), offsets[k] ≤ nextOffset offsets size k) ↔ spanOk size offsets = true := by
    rw [← offsetSpans_ok_iff]
    constructor
    · intro ordered
      obtain ⟨spans, read, -⟩ := offsetSpans_ordered 0 size offsets ordered
      exact ⟨spans, read⟩
    · rintro ⟨spans, read⟩ k h
      refine Nat.le_of_not_lt (fun bad => ?_)
      obtain ⟨e, err⟩ := offsetSpans_unordered size offsets ⟨k, h, bad⟩
      rw [read] at err; cases err
  rw [spans]

/-- The loop of the struct view that checks the offsets. -/
def fieldsCheck : Stmt :=
  .loop (.op .and (Expr.lt (.var 10) (.var 4)) (.var 9))
    (.block [.call "ssz_plan_width" [.var 11] 12,
      .ite (Expr.ne (.var 12) (.lit (none64 : Nat).toUInt64)) (.block [.set 13 (.var 13 + .var 12)])
        (.block [.set 14 (Expr.ld4 (.var 1 + .var 2 + .var 13)),
          .ite (Expr.eq (.var 15) (.lit (none64 : Nat).toUInt64)) (.block [.set 9 (Expr.eq (.var 14) (.var 8))])
            (.block [.set 9 (Expr.le (.var 15) (.var 14))]),
          .set 15 (.var 14), .set 13 (.var 13 + 4)]),
      .call "ssz_plan_next" [.var 11] 11, .set 10 (.var 10 + 1)])

/-- The loop of the struct view that writes the ranges. -/
def fieldsWrite : Stmt :=
  .loop (Expr.lt (.var 10) (.var 4))
    (.block [.call "ssz_plan_width" [.var 11] 12,
      .ite (Expr.ne (.var 12) (.lit (none64 : Nat).toUInt64))
        (.block [Stmt.st (.var 5 + 8 + 16 * .var 10) (.var 2 + .var 13),
          Stmt.st (.var 5 + 16 + 16 * .var 10) (.var 2 + .var 13 + .var 12), .set 13 (.var 13 + .var 12)])
        (.block [.set 14 (Expr.ld4 (.var 1 + .var 2 + .var 13)), Stmt.st (.var 5 + 8 + 16 * .var 10) (.var 2 + .var 14),
          .ite (Expr.ne (.var 15) (.lit (none64 : Nat).toUInt64))
            (.block [Stmt.st (.var 5 + 16 + 16 * .var 15) (.var 2 + .var 14)]) .skip,
          .set 15 (.var 10), .set 13 (.var 13 + 4)]),
      .call "ssz_plan_next" [.var 11] 11, .set 10 (.var 10 + 1)])

/-- The struct view: the budget, the check, the last offset against the end, then the write. -/
theorem fieldsView_main : afterTwo fieldsView.body = .ite (Expr.lt (.var 7) (.lit (offsetLimit : Nat).toUInt64))
    (.block [.call "ssz_plan_fields_width" [.var 0, .var 4] 16,
      .ite (Expr.ne (.var 16) (.lit (none64 : Nat).toUInt64))
        (.block [.set 8 (.var 16), .set 9 (Expr.eq (.var 7) (.var 16))])
        (.block [.call "ssz_plan_leading" [.var 0, .var 4] 8, .set 9 (Expr.le (.var 8) (.var 7))]),
      .set 10 0, .set 11 (.var 0), .set 13 0, .set 15 (.lit (none64 : Nat).toUInt64), fieldsCheck,
      .ite (.op .and (.var 9) (Expr.ne (.var 15) (.lit (none64 : Nat).toUInt64)))
        (.block [.set 9 (Expr.le (.var 15) (.var 7))]) .skip,
      .ite (.var 9) (.block [.set 6 2, .ite (Expr.le (.var 4) (Expr.ld (.var 5)))
        (.block [.set 10 0, .set 11 (.var 0), .set 13 0, .set 15 (.lit (none64 : Nat).toUInt64), fieldsWrite,
          .ite (Expr.ne (.var 15) (.lit (none64 : Nat).toUInt64))
            (.block [Stmt.st (.var 5 + 16 + 16 * .var 15) (.var 3)]) .skip,
          Stmt.st (.var 5) (.var 4), .set 6 0]) .skip]) .skip]) .skip := rfl

/-- The struct view sets its size and its refusal code, then does the rest. -/
theorem fieldsView_body : fieldsView.body =
    .seq (.set 7 (.op .sub (.var 3) (.var 2))) (.seq (.set 6 (.lit 1)) (afterTwo fieldsView.body)) := rfl

/-- A check that passes a table passes every first part of it. -/
theorem checkFrom_prefix (leading : Nat) : ∀ (p : Option Nat) (a c : List Nat),
    checkFrom leading p (a ++ c) = true → checkFrom leading p a = true
  | _, [], _, _ => by simp [checkFrom]
  | none, x :: rest, c, h => by
    simp only [List.cons_append, checkFrom, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, checkFrom_prefix leading (some x) rest c h.2⟩
  | some p, x :: rest, c, h => by
    simp only [List.cons_append, checkFrom, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, checkFrom_prefix leading (some x) rest c h.2⟩

/-- The word a driver keeps for the last offset: the offset, or the word for none. -/
def prevWord : Option Nat → UInt64
  | none => (none64 : Nat).toUInt64
  | some l => l.toUInt64

/-- The fixed part of the first fields grows by each field's part. -/
theorem leadingWidth_take_succ (fields : List Desc) (i : Nat) (small : i < fields.length) :
    Desc.leadingWidth (fields.take (i + 1)) =
      Desc.leadingWidth (fields.take i) + fields[i].fixedSize.getD bytesPerOffset := by
  rw [List.take_add_one, List.getElem?_eq_getElem small, Option.toList_some, leadingWidth_append]
  simp [Desc.leadingWidth]

/-- The fixed part of the first fields is at most the whole fixed part. -/
theorem leadingWidth_take_le (fields : List Desc) (i : Nat) :
    Desc.leadingWidth (fields.take i) ≤ Desc.leadingWidth fields := by
  have := leadingWidth_append (fields.take i) (fields.drop i)
  rw [List.take_append_drop] at this
  omega

/-- The bodies of the first places grow by the next place's body, when it has one. -/
theorem placeStarts_take_succ (places : List Place) (i : Nat) (small : i < places.length) :
    placeStarts (places.take (i + 1)) = placeStarts (places.take i) ++ placeStarts [places[i]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem small, Option.toList_some, placeStarts_append]

/-- An offset is four bytes, so below 2^32. -/
theorem offsetAt_small (b : ByteArray) (pos : Nat) : offsetAt b pos < 2 ^ 32 := by
  have := (b.get! pos).toNat_lt; have := (b.get! (pos + 1)).toNat_lt
  have := (b.get! (pos + 2)).toNat_lt; have := (b.get! (pos + 3)).toNat_lt
  simp only [offsetAt]; omega

/-- Every body a struct's places name starts at an offset read from the encoding. -/
theorem placesFrom_starts_small (b : ByteArray) (start : Nat) : ∀ (fields : List Desc) (position x : Nat),
    x ∈ placeStarts (placesFrom fields b start position) → x < 2 ^ 32
  | [], _, _, h => by simp [placesFrom, placeStarts] at h
  | field :: fields, position, x, h => by
    cases fixed : field.fixedSize with
    | some width =>
      simp only [placesFrom, fixed, placeStarts] at h
      exact placesFrom_starts_small b start fields _ x h
    | none =>
      simp only [placesFrom, fixed, placeStarts, List.mem_cons] at h
      rcases h with rfl | later
      · exact offsetAt_small b _
      · exact placesFrom_starts_small b start fields _ x later

/-- The last offset seen is one of them, or the one before them. -/
theorem lastOf_mem : ∀ (p : Option Nat) (offsets : List Nat) (l : Nat), lastOf p offsets = some l →
    l ∈ offsets ∨ p = some l
  | _, [], _, h => Or.inr h
  | _, x :: rest, l, h => by
    rcases lastOf_mem (some x) rest l h with inside | first
    · exact Or.inl (List.mem_cons_of_mem _ inside)
    · simp at first; subst first; exact Or.inl (List.mem_cons_self ..)

/-- The bodies of the first places are among all of them. -/
theorem placeStarts_take_mem (places : List Place) (i x : Nat) (h : x ∈ placeStarts (places.take i)) :
    x ∈ placeStarts places := by
  rw [← List.take_append_drop i places, placeStarts_append]
  exact List.mem_append_left _ h

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/--
The check of a struct's offsets, field by field.

It ends with the flag up when the budget held and the offsets were in order, the last offset kept;
otherwise the flag is down and the reference refuses the struct.
-/
theorem fieldsCheck_runs (m : Module) (w : World) (linked : HasCodec m) (fields : List Desc)
    (sound : ∀ f ∈ fields, f.wellFormed = .ok ()) (thin : ∀ f ∈ fields, narrow f = true)
    (each : ∀ f ∈ fields, WidthOk m w f) (inner : Nat) (mem : Memory) (q data start stop out cap : Nat)
    (b : ByteArray) (plan : PlanAt w mem q (wordsAll fields)) (at_ : ViewMemory w mem data b out cap)
    (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (leadSmall : Desc.leadingWidth fields < 2 ^ 62)
    (room : w.stackLo + (widthLevel + walkLevel) * Desc.deepestNesting fields ≤ inner)
    (env : Env) (e1 : env 1 = data.toUInt64) (e2 : env 2 = start.toUInt64)
    (e4 : env 4 = fields.length.toUInt64) (e8 : env 8 = (Desc.leadingWidth fields).toUInt64)
    (e10 : env 10 = 0) (e11 : env 11 = q.toUInt64) (e13 : env 13 = 0) (e15 : env 15 = prevWord none)
    (flag : (env 9 = 1 ∧ budgetOk fields (stop - start)) ∨ (env 9 = 0 ∧ ¬ budgetOk fields (stop - start))) :
    ∃ env', Runs m w inner env mem fieldsCheck env' mem ∧ (∀ k, k < 9 → env' k = env k) ∧
      ((env' 9 = 1 ∧ budgetOk fields (stop - start) ∧
          checkFrom (Desc.leadingWidth fields) none (placeStarts (placesFrom fields b start 0)) = true ∧
          env' 15 = prevWord (lastOf none (placeStarts (placesFrom fields b start 0)))) ∨
        (env' 9 = 0 ∧ ¬ (budgetOk fields (stop - start) ∧
          tableAccepts (placeStarts (placesFrom fields b start 0)) (Desc.leadingWidth fields) (stop - start)))) := by
  let lead := Desc.leadingWidth fields
  let size := stop - start
  let P := placesFrom fields b start 0
  let O (i : Nat) := placeStarts (P.take i)
  let pos (i : Nat) : Nat := q + 8 * (wordsAll (fields.take i)).length
  let lw (i : Nat) := Desc.leadingWidth (fields.take i)
  have bound := plan.1
  have lenSmall : fields.length < 2 ^ 63 := by
    have := wordsAll_length_ge fields
    simp only [addressBound] at bound
    omega
  have lenP : P.length = fields.length := placesFrom_length b start fields 0
  have dataBound : data + b.size ≤ 2 ^ 63 := by
    have := at_.readable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  -- The whole table, once every field is read.
  have whole : O fields.length = placeStarts P := by simp [O, ← lenP]
  -- A check failing on the first offsets fails on the whole table.
  have refusedFrom : ∀ i, i ≤ fields.length → checkFrom lead none (O i) = false →
      ¬ (budgetOk fields size ∧ tableAccepts (placeStarts P) lead size) := by
    rintro i within bad ⟨-, accepts⟩
    have all := ((checkFrom_none lead size (placeStarts P)).mpr accepts).1
    have split : placeStarts P = O i ++ placeStarts (P.drop i) := by
      simp only [O]; rw [← placeStarts_append, List.take_append_drop]
    rw [split] at all
    rw [checkFrom_prefix lead none _ _ all] at bad
    cases bad
  let inv : Env → Memory → Prop := fun env' cur =>
    cur = mem ∧ (∀ k, k < 9 → env' k = env k) ∧ ∃ i, i ≤ fields.length ∧ env' 10 = i.toUInt64 ∧
      env' 11 = (pos i).toUInt64 ∧ env' 13 = (lw i).toUInt64 ∧ env' 15 = prevWord (lastOf none (O i)) ∧
      ((env' 9 = 1 ∧ budgetOk fields size ∧ checkFrom lead none (O i) = true) ∨
        (env' 9 = 0 ∧ ¬ (budgetOk fields size ∧ tableAccepts (placeStarts P) lead size)))
  have loop := Runs.loop_inv (m := m) (w := w) (sp := inner)
    (c := .op .and (Expr.lt (.var 10) (.var 4)) (.var 9))
    (body := .block [.call "ssz_plan_width" [.var 11] 12,
      .ite (Expr.ne (.var 12) (.lit (none64 : Nat).toUInt64)) (.block [.set 13 (.var 13 + .var 12)])
        (.block [.set 14 (Expr.ld4 (.var 1 + .var 2 + .var 13)),
          .ite (Expr.eq (.var 15) (.lit (none64 : Nat).toUInt64)) (.block [.set 9 (Expr.eq (.var 14) (.var 8))])
            (.block [.set 9 (Expr.le (.var 15) (.var 14))]),
          .set 15 (.var 14), .set 13 (.var 13 + 4)]),
      .call "ssz_plan_next" [.var 11] 11, .set 10 (.var 10 + 1)])
    inv (fun env' _ => fields.length - (env' 10).toNat) (fun _ _ _ => ⟨_, rfl⟩)
    (by
      rintro env₁ cur v ⟨hcur, kept, i, within, g10, g11, g13, g15, sofar⟩ cond nonzero
      subst cur
      have small_i : i < 2 ^ 64 := by omega
      have g4 : env₁ 4 = fields.length.toUInt64 := by rw [kept 4 (by decide), e4]
      -- The condition holds, so another field is left and the offsets so far are in order.
      obtain ⟨more, up, budget, checked⟩ : i < fields.length ∧ env₁ 9 = 1 ∧ budgetOk fields size ∧
          checkFrom lead none (O i) = true := by
        rcases sofar with ⟨e9, budget, checked⟩ | ⟨e9, -⟩
        · refine ⟨?_, e9, budget, checked⟩
          by_cases done : i < fields.length
          · exact done
          · simp [eval, Expr.lt, g10, g4, e9, Cond.holds, aluResult, ofNat_lt_ofNat i fields.length small_i (by omega),
              done] at cond
            exact absurd cond.symm nonzero
        · simp [eval, Expr.lt, g10, g4, e9, Cond.holds, aluResult] at cond
          exact absurd cond.symm nonzero
      have member : fields[i] ∈ fields := List.getElem_mem more
      have split : fields = fields.take i ++ fields[i] :: fields.drop (i + 1) := by simp
      have planField : PlanAt w mem (pos i) (words fields[i]) := by
        have all := plan
        rw [split, wordsAll_append, wordsAll] at all
        exact (all.right).left
      have deep := nesting_le_deepest fields fields[i] member
      have deeper : (widthLevel + walkLevel) * fields[i].nesting ≤
          (widthLevel + walkLevel) * Desc.deepestNesting fields := Nat.mul_le_mul_left _ deep
      have measured := each fields[i] member inner mem (pos i) planField (by omega)
      have ranWidth := Runs.call (m := m) (w := w) (sp := inner) (env := env₁) (args := [.var 11]) (dst := 12)
        (values := [(pos i).toUInt64]) (by simp [eval, g11]) measured
      have step : pos i + 8 * (words fields[i]).length = pos (i + 1) := by
        simp only [pos, List.take_add_one, List.getElem?_eq_getElem more, Option.toList_some, wordsAll_append,
          wordsAll, List.append_nil, List.length_append]
        omega
      have walked := next_ok m w linked fields[i] (sound _ member) inner mem (pos i) planField (by
        have : walkLevel * fields[i].nesting ≤ (widthLevel + walkLevel) * fields[i].nesting :=
          Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
        omega)
      rw [step] at walked
      have grow := leadingWidth_take_succ fields i more
      have nextLe := leadingWidth_take_le fields (i + 1)
      have place := placesFrom_get b start fields 0 i more
      have bodies := placeStarts_take_succ P i (by rw [lenP]; exact more)
      -- The budget held, so the fixed part lies inside the struct.
      have leadLe : lead ≤ size := by
        simp only [budgetOk] at budget
        cases fixed : Desc.fieldsFixedSize fields with
        | none => simp [fixed] at budget; exact budget
        | some width =>
          simp [fixed] at budget
          show Desc.leadingWidth fields ≤ size
          rw [leadingWidth_fixed fields width fixed]; omega
      let env₂ := assign env₁ 12 (widthWord fields[i])
      -- What is left of the pass, once the field's width is known and the position has moved past it.
      have finish : ∀ env₃, env₃ 11 = env₁ 11 → env₃ 10 = env₁ 10 → (∀ k, k < 9 → env₃ k = env₁ k) →
          Runs m w inner env₂ mem
            (.ite (Expr.ne (.var 12) (.lit (none64 : Nat).toUInt64)) (.block [.set 13 (.var 13 + .var 12)])
              (.block [.set 14 (Expr.ld4 (.var 1 + .var 2 + .var 13)),
                .ite (Expr.eq (.var 15) (.lit (none64 : Nat).toUInt64))
                  (.block [.set 9 (Expr.eq (.var 14) (.var 8))]) (.block [.set 9 (Expr.le (.var 15) (.var 14))]),
                .set 15 (.var 14), .set 13 (.var 13 + 4)])) env₃ mem →
          env₃ 13 = (lw (i + 1)).toUInt64 → env₃ 15 = prevWord (lastOf none (O (i + 1))) →
          ((env₃ 9 = 1 ∧ budgetOk fields size ∧ checkFrom lead none (O (i + 1)) = true) ∨
            (env₃ 9 = 0 ∧ ¬ (budgetOk fields size ∧ tableAccepts (placeStarts P) lead size))) →
          ∃ env' mem', Runs m w inner env₁ mem (.block [.call "ssz_plan_width" [.var 11] 12,
            .ite (Expr.ne (.var 12) (.lit (none64 : Nat).toUInt64)) (.block [.set 13 (.var 13 + .var 12)])
              (.block [.set 14 (Expr.ld4 (.var 1 + .var 2 + .var 13)),
                .ite (Expr.eq (.var 15) (.lit (none64 : Nat).toUInt64))
                  (.block [.set 9 (Expr.eq (.var 14) (.var 8))]) (.block [.set 9 (Expr.le (.var 15) (.var 14))]),
                .set 15 (.var 14), .set 13 (.var 13 + 4)]),
            .call "ssz_plan_next" [.var 11] 11, .set 10 (.var 10 + 1)]) env' mem' ∧ inv env' mem' ∧
            fields.length - (env' 10).toNat < fields.length - (env₁ 10).toNat := by
        intro env₃ k11 k10 k9 ranRest e13' e15' flag'
        have ranNext := Runs.call (m := m) (w := w) (sp := inner) (env := env₃) (args := [.var 11]) (dst := 11)
          (values := [(pos i).toUInt64]) (by simp [eval, k11, g11]) walked
        refine ⟨_, mem, Runs.block_cons ranWidth (Runs.block_cons ranRest (Runs.block_cons ranNext
          (Runs.set _ _ _ _ _ 10 _ (i + 1).toUInt64 (by simp [eval, assign, k10, g10, aluResult])))),
          ⟨rfl, fun k hk => ?_, i + 1, more, by simp [assign], by simp [assign], by simp [assign, e13'],
            by simp [assign, e15'], by simpa [assign] using flag'⟩, ?_⟩
        · simp [assign, show k ≠ 10 by omega, show k ≠ 11 by omega, k9 k hk, kept k hk]
        · simp [assign, g10, toNat_toUInt64 _ small_i, toNat_toUInt64 (i + 1) (by omega)]
          omega
      have g13' : env₂ 13 = (lw i).toUInt64 := by simp [env₂, assign, g13]
      have g12 : env₂ 12 = widthWord fields[i] := by simp [env₂, assign]
      cases fixed : fields[i].fixedSize with
      | some width =>
        -- A field in place: the position moves past it, and no offset is read.
        have notNone := widthWord_none fields[i] width fixed (narrow_width fields[i] (thin _ member) width fixed)
        have notNone' : widthWord fields[i] ≠ 18446744073709551615 := by simpa using notNone
        have word : widthWord fields[i] = width.toUInt64 := by simp [widthWord, fixed]
        have same : O (i + 1) = O i := by
          simp only [O]; rw [bodies]
          simp [P, place, fixed, placeStarts]
        refine finish (assign env₂ 13 (lw (i + 1)).toUInt64) (by simp [env₂, assign]) (by simp [env₂, assign])
          (fun k hk => by simp [env₂, assign, show k ≠ 13 by omega, show k ≠ 12 by omega])
          (Runs.ite_true 1 (by simp [eval, Expr.ne, g12, Cond.holds, notNone']) (by decide)
            (Runs.set _ _ _ _ _ 13 _ _ (by simp [eval, g13', g12, word, aluResult, lw, grow, fixed])))
          (by simp [assign]) (by simp [env₂, assign, g15, same]) (Or.inl ⟨by simp [env₂, assign, up], budget,
            by rw [same]; exact checked⟩)
      | none =>
        -- A field behind an offset: the offset is read and checked against the last one.
        have word : widthWord fields[i] = 18446744073709551615 := by simp [widthWord, fixed]
        let o := offsetAt b (start + lw i)
        have stepLw : lw (i + 1) = lw i + 4 := by simp only [lw, grow, fixed]; rfl
        have readInside : start + lw i + 4 ≤ b.size := by
          have : lw (i + 1) ≤ lead := nextLe
          omega
        have readO : eval w env₂ mem (Expr.ld4 (.var 1 + .var 2 + .var 13)) = some o.toUInt64 := by
          have addr : (UInt64.ofNat data + UInt64.ofNat start + UInt64.ofNat (lw i)).toNat = data + (start + lw i) := by
            rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
              UInt64.toNat_ofNat_of_lt' (lt_size (by omega)), UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
            omega
          have acc : w.access (data + (start + lw i)) 4 := access_inside at_.readable _ 4 (by omega)
          have g1 : env₂ 1 = data.toUInt64 := by simp [env₂, assign, kept 1 (by decide), e1]
          have g2 : env₂ 2 = start.toUInt64 := by simp [env₂, assign, kept 2 (by decide), e2]
          simp [eval, Expr.ld4, g1, g2, g13', aluResult, Width.bytes, addr, acc,
            readLE_offset mem data b at_.bytes (start + lw i) (by omega), o]
        have oBody : placeStarts [P[i]] = [o] := by simp [P, place, fixed, placeStarts, o, lw]
        have grown : O (i + 1) = O i ++ [o] := by simp only [O]; rw [bodies, oBody]
        let env₃ := assign env₂ 14 o.toUInt64
        have g8 : env₃ 8 = lead.toUInt64 := by simp [env₃, env₂, assign, kept 8 (by decide), e8, lead]
        have g15' : env₃ 15 = prevWord (lastOf none (O i)) := by simp [env₃, env₂, assign, g15]
        have g14 : env₃ 14 = o.toUInt64 := by simp [env₃, assign]
        have oSmall : o < 2 ^ 32 := offsetAt_small b _
        -- The test this offset faces: against the fixed part's end, or against the last offset.
        let passes : Bool := match lastOf none (O i) with
          | none => o == lead
          | some l => decide (l ≤ o)
        have tested : ∃ env₄, Runs m w inner env₃ mem
            (.ite (Expr.eq (.var 15) (.lit (none64 : Nat).toUInt64)) (.block [.set 9 (Expr.eq (.var 14) (.var 8))])
              (.block [.set 9 (Expr.le (.var 15) (.var 14))])) env₄ mem ∧
            env₄ = assign env₃ 9 (if passes then 1 else 0) := by
          cases last : lastOf none (O i) with
          | none =>
            refine ⟨_, Runs.ite_true 1 (by simp [eval, Expr.eq, g15', last, prevWord, Cond.holds]) (by decide)
              (Runs.set _ _ _ _ _ 9 _ _ ?_), rfl⟩
            simp only [eval, Expr.eq, g14, g8, Cond.holds, passes, last]
            simp [ofNat_eq_ofNat o lead (by omega) (by omega), lead]
          | some l =>
            have lSmall : l < 2 ^ 32 := by
              rcases lastOf_mem none _ l last with inside | first
              · exact placesFrom_starts_small b start fields 0 l (placeStarts_take_mem P i l inside)
              · cases first
            have lWord : l.toUInt64 ≠ 18446744073709551615 := by
              intro h
              have := congrArg UInt64.toNat h
              rw [toNat_toUInt64 _ (by omega)] at this
              simp at this; omega
            refine ⟨_, Runs.ite_false (by simp [eval, Expr.eq, g15', last, prevWord, Cond.holds, lWord])
              (Runs.set _ _ _ _ _ 9 _ _ ?_), rfl⟩
            simp only [eval, Expr.le, g14, g15', last, prevWord, passes]
            simp only [Bind.bind, Option.bind, pure, holds_be, Nat.toUInt64_eq,
              ofNat_le_iff l o (by omega) (by omega)]
        obtain ⟨env₄, ranTest, rfl⟩ := tested
        have ranRest : Runs m w inner env₂ mem
            (.ite (Expr.ne (.var 12) (.lit (none64 : Nat).toUInt64)) (.block [.set 13 (.var 13 + .var 12)])
              (.block [.set 14 (Expr.ld4 (.var 1 + .var 2 + .var 13)),
                .ite (Expr.eq (.var 15) (.lit (none64 : Nat).toUInt64))
                  (.block [.set 9 (Expr.eq (.var 14) (.var 8))]) (.block [.set 9 (Expr.le (.var 15) (.var 14))]),
                .set 15 (.var 14), .set 13 (.var 13 + 4)]))
            (assign (assign (assign env₃ 9 (if passes then 1 else 0)) 15 o.toUInt64) 13 (lw (i + 1)).toUInt64)
            mem :=
          Runs.ite_false (by simp [eval, Expr.ne, g12, word, Cond.holds])
            (Runs.block_cons (Runs.set _ _ _ _ _ 14 _ _ readO) (Runs.block_cons ranTest
              (Runs.block_cons (Runs.set _ _ _ _ _ 15 _ _ (by simp [eval, assign, g14]))
                (Runs.set _ _ _ _ _ 13 _ _ (by simp [eval, assign, env₃, g13', aluResult, stepLw])))))
        have check' : checkFrom lead none (O (i + 1)) = passes := by
          rw [grown, checkFrom_snoc, checked]; rfl
        refine finish _ (by simp [assign, env₃, env₂]) (by simp [assign, env₃, env₂])
          (fun k hk => by simp [assign, env₃, env₂, show k ≠ 9 by omega, show k ≠ 12 by omega,
            show k ≠ 13 by omega, show k ≠ 14 by omega, show k ≠ 15 by omega]) ranRest (by simp [assign])
          (by simp [assign, grown, lastOf_snoc, prevWord]) ?_
        by_cases ok : passes = true
        · exact Or.inl ⟨by simp [assign, ok], budget, by rw [check', ok]⟩
        · exact Or.inr ⟨by simp [assign, ok], refusedFrom (i + 1) more (by rw [check']; simpa using ok)⟩
      )
  have start₀ : inv env mem := by
    refine ⟨rfl, fun _ _ => rfl, 0, Nat.zero_le _, by simp [e10], by simp [e11, pos, wordsAll],
      by simp [e13, lw, Desc.leadingWidth], by simp [e15, O, placeStarts, lastOf], ?_⟩
    rcases flag with ⟨e9, budget⟩ | ⟨e9, budget⟩
    · exact Or.inl ⟨e9, budget, by simp [O, placeStarts, checkFrom]⟩
    · exact Or.inr ⟨e9, fun ⟨b', _⟩ => budget b'⟩
  obtain ⟨env', mem', runs, ⟨hmem, kept, i, within, g10, -, -, g15, sofar⟩, exit⟩ := loop env mem start₀
  subst mem'
  refine ⟨env', runs, kept, ?_⟩
  rcases sofar with ⟨e9, budget, checked⟩ | refused
  · -- The flag stayed up, so the loop ran out of fields.
    have done : i = fields.length := by
      have small_i : i < 2 ^ 64 := by omega
      have g4 : env' 4 = fields.length.toUInt64 := by rw [kept 4 (by decide), e4]
      by_cases more : i < fields.length
      · simp [eval, Expr.lt, g10, g4, e9, Cond.holds, aluResult,
          ofNat_lt_ofNat i fields.length small_i (by omega), more] at exit
      · omega
    subst done
    rw [whole] at checked g15
    exact Or.inl ⟨e9, budget, checked, g15⟩
  · exact Or.inr refused

/-- The words of a view at a range's start and stop, for any ranges. -/
theorem viewWord_get (ranges : List (Nat × Nat)) (j : Nat) (small : j < ranges.length) :
    viewWord ranges (1 + 2 * j) = ranges[j].1.toUInt64 ∧ viewWord ranges (2 + 2 * j) = ranges[j].2.toUInt64 := by
  constructor
  · simp only [viewWord]
    rw [if_neg (by omega), if_pos (by omega), show (1 + 2 * j - 1) / 2 = j by omega]
    simp [List.getD_eq_getElem?_getD, small]
  · simp only [viewWord]
    rw [if_neg (by omega), if_neg (by omega), show (2 + 2 * j - 1) / 2 = j by omega]
    simp [List.getD_eq_getElem?_getD, small]

/-- The first body after some places in place is the body that follows them, whatever the default. -/
theorem placeStarts_drop_head (places : List Place) (j i o : Nat) (hi : i < places.length) (le : j ≤ i)
    (body : places[i] = .body o)
    (inline : ∀ k (hk : k < places.length), j ≤ k → k < i → places[k].isBody = false) (d : Nat) :
    (placeStarts (places.drop j)).headD d = o := by
  have := placeStarts_drop_body places j i o hi le body inline
  -- The body at i makes the list of bodies non-empty, so the default plays no part.
  have nonEmpty : placeStarts (places.drop j) ≠ [] := by
    intro h; rw [h] at this; simp at this
    have : placeStarts (places.drop j) = placeStarts ((places.drop j).take (i - j)) ++
        placeStarts ((places.drop j).drop (i - j)) := by rw [← placeStarts_append, List.take_append_drop]
    rw [h, List.drop_drop] at this
    have at_ : places.drop (j + (i - j)) = places[i] :: places.drop (i + 1) := by
      rw [show j + (i - j) = i by omega]; simp
    rw [at_, body] at this
    simp [placeStarts] at this
  cases h : placeStarts (places.drop j) with
  | nil => exact absurd h nonEmpty
  | cons x xs => rw [h] at this; simpa using this

/-- The word a driver keeps for the last body's index: the index, or the word for none. -/
def indexWord : Option Nat → UInt64
  | none => (none64 : Nat).toUInt64
  | some j => j.toUInt64

/-- The words the struct view has written after some fields: every start and stop but a pending last body's stop. -/
def writtenFields (i : Nat) (prev : Option Nat) (k : Nat) : Bool :=
  decide (1 ≤ k ∧ k < 1 + 2 * i) && (match prev with | some j => k != 2 + 2 * j | none => true)

/-- A plan apart from the words written still reads as itself. -/
theorem PlanAt.wordsAt {w : World} {mem : Memory} {q : Nat} {ws : List Nat} (h : PlanAt w mem q ws) (out n : Nat)
    (f : Nat → UInt64) (written : Nat → Bool) (bounded : ∀ k, written k = true → k < n)
    (apart : q + 8 * ws.length ≤ out ∨ out + 8 * n ≤ q) : PlanAt w (wordsAt out f written mem) q ws := by
  refine ⟨h.1, fun k small => ⟨(h.2 k small).1, ?_⟩⟩
  rw [← (h.2 k small).2]
  apply readLE_congr
  intro x hx
  exact wordsAt_far out f written mem n _ bounded (by omega)

/-- Where a word of the output sits, from the output's address and the word's index. -/
theorem out_addr (out a i : Nat) (small : out + a + 16 * i < 2 ^ 64) :
    (UInt64.ofNat out + UInt64.ofNat a + 16 * UInt64.ofNat i).toNat = out + a + 16 * i := by
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
    UInt64.toNat_ofNat_of_lt' (lt_size (by omega)), UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
  simp
  omega

/-- A field in place adds its start and its stop to the words written. -/
theorem writtenFields_inline (i : Nat) (prev : Option Nat) (before : ∀ j, prev = some j → j < i) :
    (fun k => k == 2 + 2 * i || (k == 1 + 2 * i || writtenFields i prev k)) = writtenFields (i + 1) prev := by
  funext k
  apply Bool.eq_iff_iff.mpr
  cases prev with
  | none => simp [writtenFields]; omega
  | some j => have := before j rfl; simp [writtenFields]; omega

/-- The first body adds its start, its stop waiting. -/
theorem writtenFields_first (i : Nat) :
    (fun k => k == 1 + 2 * i || writtenFields i none k) = writtenFields (i + 1) (some i) := by
  funext k
  apply Bool.eq_iff_iff.mpr
  simp [writtenFields]; omega

/-- A later body adds its start, and the stop of the body before it. -/
theorem writtenFields_next (i j : Nat) (before : j < i) :
    (fun k => k == 2 + 2 * j || (k == 1 + 2 * i || writtenFields i (some j) k)) = writtenFields (i + 1) (some i) := by
  funext k
  apply Bool.eq_iff_iff.mpr
  simp [writtenFields]; omega

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
/--
The write of a struct's ranges, field by field.

Every range is written but the stop of the last body, which waits for the end of the struct.
-/
theorem fieldsWrite_runs (m : Module) (w : World) (linked : HasCodec m) (fields : List Desc)
    (sound : ∀ f ∈ fields, f.wellFormed = .ok ()) (thin : ∀ f ∈ fields, narrow f = true)
    (each : ∀ f ∈ fields, WidthOk m w f) (inner : Nat) (mem : Memory) (q data start stop out cap : Nat)
    (b : ByteArray) (plan : PlanAt w mem q (wordsAll fields)) (at_ : ViewMemory w mem data b out cap)
    (planApart : q + 8 * (wordsAll fields).length ≤ out ∨ out + 8 * (1 + 2 * cap) ≤ q)
    (ordered : start ≤ stop) (inside : stop ≤ b.size) (leadLe : Desc.leadingWidth fields ≤ stop - start)
    (fits : fields.length ≤ cap)
    (room : w.stackLo + (widthLevel + walkLevel) * Desc.deepestNesting fields ≤ inner)
    (env : Env) (e1 : env 1 = data.toUInt64) (e2 : env 2 = start.toUInt64)
    (e4 : env 4 = fields.length.toUInt64) (e5 : env 5 = out.toUInt64)
    (e10 : env 10 = 0) (e11 : env 11 = q.toUInt64) (e13 : env 13 = 0) (e15 : env 15 = indexWord none) :
    ∃ env', Runs m w inner env mem fieldsWrite env'
        (wordsAt out (viewWord (rangesOf start (stop - start) (placesFrom fields b start 0)))
          (writtenFields fields.length (lastBody (placesFrom fields b start 0) fields.length)) mem) ∧
      (∀ k, k < 10 → env' k = env k) ∧
      env' 15 = indexWord (lastBody (placesFrom fields b start 0) fields.length) := by
  let size := stop - start
  let P := placesFrom fields b start 0
  let R := rangesOf start size P
  let f := viewWord R
  let pos (i : Nat) : Nat := q + 8 * (wordsAll (fields.take i)).length
  let lw (i : Nat) := Desc.leadingWidth (fields.take i)
  let state (i : Nat) : Memory := wordsAt out f (writtenFields i (lastBody P i)) mem
  have bound := plan.1
  have lenSmall : fields.length < 2 ^ 63 := by
    have := wordsAll_length_ge fields
    simp only [addressBound] at bound
    omega
  have lenP : P.length = fields.length := placesFrom_length b start fields 0
  have lenR : R.length = fields.length := by simp [R, rangesOf_length, lenP]
  have dataBound : data + b.size ≤ 2 ^ 63 := by
    have := at_.readable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have outBound : out + 8 + 16 * cap ≤ 2 ^ 63 := by
    have := at_.writable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  -- What every state of the write leaves alone: the encoding and the plan.
  have bounded : ∀ i prev k, i ≤ cap → writtenFields i prev k = true → k < 1 + 2 * cap := by
    intro i prev k le h
    simp only [writtenFields, Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  have bytesIn : ∀ i, i ≤ fields.length → BytesAt (state i) data b := fun i le =>
    at_.wordsAt f _ (fun k h => bounded i _ k (by omega) h)
  have planIn : ∀ i, i ≤ fields.length → PlanAt w (state i) q (wordsAll fields) := fun i le =>
    plan.wordsAt out (1 + 2 * cap) f _ (fun k h => bounded i _ k (by omega) h) (by omega)
  let inv : Env → Memory → Prop := fun env' cur =>
    (∀ k, k < 10 → env' k = env k) ∧ ∃ i, i ≤ fields.length ∧ env' 10 = i.toUInt64 ∧
      env' 11 = (pos i).toUInt64 ∧ env' 13 = (lw i).toUInt64 ∧ env' 15 = indexWord (lastBody P i) ∧ cur = state i
  have loop := Runs.loop_inv (m := m) (w := w) (sp := inner) (c := Expr.lt (.var 10) (.var 4))
    (body := .block [.call "ssz_plan_width" [.var 11] 12,
      .ite (Expr.ne (.var 12) (.lit (none64 : Nat).toUInt64))
        (.block [Stmt.st (.var 5 + 8 + 16 * .var 10) (.var 2 + .var 13),
          Stmt.st (.var 5 + 16 + 16 * .var 10) (.var 2 + .var 13 + .var 12), .set 13 (.var 13 + .var 12)])
        (.block [.set 14 (Expr.ld4 (.var 1 + .var 2 + .var 13)), Stmt.st (.var 5 + 8 + 16 * .var 10) (.var 2 + .var 14),
          .ite (Expr.ne (.var 15) (.lit (none64 : Nat).toUInt64))
            (.block [Stmt.st (.var 5 + 16 + 16 * .var 15) (.var 2 + .var 14)]) .skip,
          .set 15 (.var 10), .set 13 (.var 13 + 4)]),
      .call "ssz_plan_next" [.var 11] 11, .set 10 (.var 10 + 1)])
    inv (fun env' _ => fields.length - (env' 10).toNat) (fun _ _ _ => ⟨_, rfl⟩)
    (by
      rintro env₁ cur v ⟨kept, i, within, g10, g11, g13, g15, hcur⟩ cond nonzero
      subst cur
      have small_i : i < 2 ^ 64 := by omega
      have g4 : env₁ 4 = fields.length.toUInt64 := by rw [kept 4 (by decide), e4]
      have g5 : env₁ 5 = out.toUInt64 := by rw [kept 5 (by decide), e5]
      have g2 : env₁ 2 = start.toUInt64 := by rw [kept 2 (by decide), e2]
      have g1 : env₁ 1 = data.toUInt64 := by rw [kept 1 (by decide), e1]
      have more : i < fields.length := by
        by_cases done : i < fields.length
        · exact done
        · simp [eval, Expr.lt, g10, g4, Cond.holds, ofNat_lt_ofNat i fields.length small_i (by omega), done] at cond
          exact absurd cond.symm nonzero
      have member : fields[i] ∈ fields := List.getElem_mem more
      have split : fields = fields.take i ++ fields[i] :: fields.drop (i + 1) := by simp
      have planField : PlanAt w (state i) (pos i) (words fields[i]) := by
        have all := planIn i within
        rw [split, wordsAll_append, wordsAll] at all
        exact (all.right).left
      have deep := nesting_le_deepest fields fields[i] member
      have deeper : (widthLevel + walkLevel) * fields[i].nesting ≤
          (widthLevel + walkLevel) * Desc.deepestNesting fields := Nat.mul_le_mul_left _ deep
      have measured := each fields[i] member inner (state i) (pos i) planField (by omega)
      have ranWidth := Runs.call (m := m) (w := w) (sp := inner) (env := env₁) (args := [.var 11]) (dst := 12)
        (values := [(pos i).toUInt64]) (by simp [eval, g11]) measured
      have step : pos i + 8 * (words fields[i]).length = pos (i + 1) := by
        simp only [pos, List.take_add_one, List.getElem?_eq_getElem more, Option.toList_some, wordsAll_append,
          wordsAll, List.append_nil, List.length_append]
        omega
      have grow := leadingWidth_take_succ fields i more
      have nextLe := leadingWidth_take_le fields (i + 1)
      have place := placesFrom_get b start fields 0 i more
      have rangeI := rangesOf_get start size P i (by rw [lenP]; exact more)
      obtain ⟨wStart, wStop⟩ := viewWord_get R i (by rw [lenR]; exact more)
      have g13' : env₁ 13 = (lw i).toUInt64 := g13
      let env₂ := assign env₁ 12 (widthWord fields[i])
      have a1 := out_addr out 8 i (by omega)
      have a2 := out_addr out 16 i (by omega)
      -- What is left of the pass, once the field's ranges are written and its place walked past.
      have finish : ∀ env₃, env₃ 11 = env₁ 11 → env₃ 10 = env₁ 10 → (∀ k, k < 10 → env₃ k = env₁ k) →
          Runs m w inner env₂ (state i)
            (.ite (Expr.ne (.var 12) (.lit (none64 : Nat).toUInt64))
              (.block [Stmt.st (.var 5 + 8 + 16 * .var 10) (.var 2 + .var 13),
                Stmt.st (.var 5 + 16 + 16 * .var 10) (.var 2 + .var 13 + .var 12), .set 13 (.var 13 + .var 12)])
              (.block [.set 14 (Expr.ld4 (.var 1 + .var 2 + .var 13)),
                Stmt.st (.var 5 + 8 + 16 * .var 10) (.var 2 + .var 14),
                .ite (Expr.ne (.var 15) (.lit (none64 : Nat).toUInt64))
                  (.block [Stmt.st (.var 5 + 16 + 16 * .var 15) (.var 2 + .var 14)]) .skip,
                .set 15 (.var 10), .set 13 (.var 13 + 4)])) env₃ (state (i + 1)) →
          env₃ 13 = (lw (i + 1)).toUInt64 → env₃ 15 = indexWord (lastBody P (i + 1)) →
          ∃ env' mem', Runs m w inner env₁ (state i) (.block [.call "ssz_plan_width" [.var 11] 12,
            .ite (Expr.ne (.var 12) (.lit (none64 : Nat).toUInt64))
              (.block [Stmt.st (.var 5 + 8 + 16 * .var 10) (.var 2 + .var 13),
                Stmt.st (.var 5 + 16 + 16 * .var 10) (.var 2 + .var 13 + .var 12), .set 13 (.var 13 + .var 12)])
              (.block [.set 14 (Expr.ld4 (.var 1 + .var 2 + .var 13)),
                Stmt.st (.var 5 + 8 + 16 * .var 10) (.var 2 + .var 14),
                .ite (Expr.ne (.var 15) (.lit (none64 : Nat).toUInt64))
                  (.block [Stmt.st (.var 5 + 16 + 16 * .var 15) (.var 2 + .var 14)]) .skip,
                .set 15 (.var 10), .set 13 (.var 13 + 4)]),
            .call "ssz_plan_next" [.var 11] 11, .set 10 (.var 10 + 1)]) env' mem' ∧ inv env' mem' ∧
            fields.length - (env' 10).toNat < fields.length - (env₁ 10).toNat := by
        intro env₃ k11 k10 kept₃ ranRest e13' e15'
        have planNext : PlanAt w (state (i + 1)) (pos i) (words fields[i]) := by
          have all := planIn (i + 1) more
          rw [split, wordsAll_append, wordsAll] at all
          exact (all.right).left
        have walked := next_ok m w linked fields[i] (sound _ member) inner (state (i + 1)) (pos i) planNext (by
          have : walkLevel * fields[i].nesting ≤ (widthLevel + walkLevel) * fields[i].nesting :=
            Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
          omega)
        rw [step] at walked
        have ranNext := Runs.call (m := m) (w := w) (sp := inner) (env := env₃) (args := [.var 11]) (dst := 11)
          (values := [(pos i).toUInt64]) (by simp [eval, k11, g11]) walked
        refine ⟨_, _, Runs.block_cons ranWidth (Runs.block_cons ranRest (Runs.block_cons ranNext
          (Runs.set _ _ _ _ _ 10 _ (i + 1).toUInt64 (by simp [eval, assign, k10, g10, aluResult])))),
          ⟨fun k hk => ?_, i + 1, more, by simp [assign], by simp [assign], by simp [assign, e13'],
            by simp [assign, e15'], rfl⟩, ?_⟩
        · simp [assign, show k ≠ 10 by omega, show k ≠ 11 by omega, kept₃ k hk, kept k hk]
        · simp [assign, g10, toNat_toUInt64 _ small_i, toNat_toUInt64 (i + 1) (by omega)]
          omega
      have g12 : env₂ 12 = widthWord fields[i] := by simp [env₂, assign]
      have h13 : env₂ 13 = (lw i).toUInt64 := by simp [env₂, assign, g13]
      have h10 : env₂ 10 = i.toUInt64 := by simp [env₂, assign, g10]
      have h5 : env₂ 5 = out.toUInt64 := by simp [env₂, assign, g5]
      have h2 : env₂ 2 = start.toUInt64 := by simp [env₂, assign, g2]
      have h1 : env₂ 1 = data.toUInt64 := by simp [env₂, assign, g1]
      have h15 : env₂ 15 = indexWord (lastBody P i) := by simp [env₂, assign, g15]
      have prevBefore : ∀ j, lastBody P i = some j → j < i := fun j h => (lastBody_some P i j h).1
      have acc1 : w.access (out + 8 * (1 + 2 * i)) 8 := access_inside at_.writable _ 8 (by omega)
      have acc2 : w.access (out + 8 * (2 + 2 * i)) 8 := access_inside at_.writable _ 8 (by omega)
      have r1 : (UInt64.ofNat out + 8 + 16 * UInt64.ofNat i).toNat = out + 8 * (1 + 2 * i) := by
        have := out_addr out 8 i (by omega)
        simp only [show UInt64.ofNat 8 = 8 from rfl] at this; rw [this]; omega
      have r2 : (UInt64.ofNat out + 16 + 16 * UInt64.ofNat i).toNat = out + 8 * (2 + 2 * i) := by
        have := out_addr out 16 i (by omega)
        simp only [show UInt64.ofNat 16 = 16 from rfl] at this; rw [this]; omega
      cases fixed : fields[i].fixedSize with
      | some width =>
        -- A field in place: its start and its stop are written.
        have notNone := widthWord_none fields[i] width fixed (narrow_width fields[i] (thin _ member) width fixed)
        have notNone' : widthWord fields[i] ≠ 18446744073709551615 := by simpa using notNone
        have word : widthWord fields[i] = width.toUInt64 := by simp [widthWord, fixed]
        have atI : P[i] = Place.inline (start + (0 + lw i)) (start + (0 + lw i) + width) := by
          simp [P, place, fixed, lw]
        rw [atI] at rangeI
        have sameLast : lastBody P (i + 1) = lastBody P i := by
          simp [lastBody, List.getElem?_eq_getElem (show i < P.length by rw [lenP]; exact more), atI, Place.isBody]
        have s1 := Runs.store m w inner env₂ (state i) .b8 (.var 5 + 8 + 16 * .var 10) (.var 2 + .var 13)
          (UInt64.ofNat out + 8 + 16 * UInt64.ofNat i) (f (1 + 2 * i))
          (by simp [eval, h5, h10, aluResult]) (by simp [eval, h2, h13, aluResult, f, wStart, R, rangeI, lw])
          (by rw [r1]; exact acc1)
        rw [r1, Width.bytes, store_wordsAt] at s1
        have s2 := Runs.store m w inner env₂ (wordsAt out f (fun j => j == 1 + 2 * i || writtenFields i (lastBody P i) j) mem)
          .b8 (.var 5 + 16 + 16 * .var 10) (.var 2 + .var 13 + .var 12)
          (UInt64.ofNat out + 16 + 16 * UInt64.ofNat i) (f (2 + 2 * i))
          (by simp [eval, h5, h10, aluResult]) (by simp [eval, h2, h13, g12, word, aluResult, f, wStop, R, rangeI, lw])
          (by rw [r2]; exact acc2)
        have hstate : state (i + 1) = wordsAt out f (writtenFields (i + 1) (lastBody P i)) mem := by
          simp only [state, sameLast]
        rw [r2, Width.bytes, store_wordsAt, writtenFields_inline i _ prevBefore, ← hstate] at s2
        refine finish (assign env₂ 13 (lw (i + 1)).toUInt64) (by simp [env₂, assign]) (by simp [env₂, assign])
          (fun k hk => by simp [env₂, assign, show k ≠ 13 by omega, show k ≠ 12 by omega])
          (Runs.ite_true 1 (by simp [eval, Expr.ne, g12, Cond.holds, notNone']) (by decide)
            (Runs.block_cons s1 (Runs.block_cons s2
              (Runs.set _ _ _ _ _ 13 _ _ (by simp [eval, h13, g12, word, aluResult, lw, grow, fixed])))))
          (by simp [assign]) (by simp [env₂, assign, g15, sameLast])
      | none =>
        -- A field behind an offset: its start is written, and it closes the body before it.
        have word : widthWord fields[i] = 18446744073709551615 := by simp [widthWord, fixed]
        let o := offsetAt b (start + lw i)
        have stepLw : lw (i + 1) = lw i + 4 := by simp only [lw, grow, fixed]; rfl
        have atI : P[i] = Place.body o := by simp [P, place, fixed, o, lw]
        rw [atI] at rangeI
        have nowLast : lastBody P (i + 1) = some i := by
          simp [lastBody, List.getElem?_eq_getElem (show i < P.length by rw [lenP]; exact more), atI, Place.isBody]
        have readInside : start + lw i + 4 ≤ b.size := by
          have : lw (i + 1) ≤ Desc.leadingWidth fields := nextLe
          omega
        have readO : eval w env₂ (state i) (Expr.ld4 (.var 1 + .var 2 + .var 13)) = some o.toUInt64 := by
          have addr : (UInt64.ofNat data + UInt64.ofNat start + UInt64.ofNat (lw i)).toNat = data + (start + lw i) := by
            rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
              UInt64.toNat_ofNat_of_lt' (lt_size (by omega)), UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
            omega
          have acc : w.access (data + (start + lw i)) 4 := access_inside at_.readable _ 4 (by omega)
          simp [eval, Expr.ld4, h1, h2, h13, aluResult, Width.bytes, addr, acc,
            readLE_offset (state i) data b (bytesIn i within) (start + lw i) (by omega), o]
        let env₃ := assign env₂ 14 o.toUInt64
        have k14 : env₃ 14 = o.toUInt64 := by simp [env₃, assign]
        have s1 := Runs.store m w inner env₃ (state i) .b8 (.var 5 + 8 + 16 * .var 10) (.var 2 + .var 14)
          (UInt64.ofNat out + 8 + 16 * UInt64.ofNat i) (f (1 + 2 * i))
          (by simp [env₃, eval, assign, h5, h10, aluResult]) (by simp [env₃, eval, assign, h2, aluResult, f, wStart, R, rangeI])
          (by rw [r1]; exact acc1)
        rw [r1, Width.bytes, store_wordsAt] at s1
        -- The body before this one, if any, now ends where this one begins.
        have closed : Runs m w inner env₃
            (wordsAt out f (fun j => j == 1 + 2 * i || writtenFields i (lastBody P i) j) mem)
            (.ite (Expr.ne (.var 15) (.lit (none64 : Nat).toUInt64))
              (.block [Stmt.st (.var 5 + 16 + 16 * .var 15) (.var 2 + .var 14)]) .skip) env₃
            (wordsAt out f (writtenFields (i + 1) (some i)) mem) := by
          cases last : lastBody P i with
          | none =>
            rw [writtenFields_first]
            exact Runs.ite_false (by simp [env₃, eval, Expr.ne, assign, h15, last, indexWord, Cond.holds])
              (Runs.skip _ _ _ _ _)
          | some j =>
            obtain ⟨before, smallJ, isBody, between⟩ := lastBody_some P i j last
            have jWord : j.toUInt64 ≠ 18446744073709551615 := by
              intro h
              have := congrArg UInt64.toNat h
              rw [toNat_toUInt64 _ (by omega)] at this
              simp at this; omega
            -- The stop of body j is where body i begins.
            have stopJ : f (2 + 2 * j) = (start + o).toUInt64 := by
              have rangeJ := rangesOf_get start size P j smallJ
              obtain ⟨-, wj⟩ := viewWord_get R j (by rw [lenR]; rw [lenP] at smallJ; exact smallJ)
              have nextBody := placeStarts_drop_head P (j + 1) i o (by rw [lenP]; exact more) (by omega) atI
                (fun k hk a b => between k hk (by omega) b) size
              cases hj : P[j] with
              | inline _ _ => rw [hj] at isBody; simp [Place.isBody] at isBody
              | body oj =>
                rw [hj] at rangeJ
                simp only [f, wj, R, rangeJ, nextBody]
            have rj : (UInt64.ofNat out + 16 + 16 * UInt64.ofNat j).toNat = out + 8 * (2 + 2 * j) := by
              have := out_addr out 16 j (by omega)
              simp only [show UInt64.ofNat 16 = 16 from rfl] at this; rw [this]; omega
            have accJ : w.access (out + 8 * (2 + 2 * j)) 8 := access_inside at_.writable _ 8 (by omega)
            have s2 := Runs.store m w inner env₃
              (wordsAt out f (fun k => k == 1 + 2 * i || writtenFields i (some j) k) mem) .b8
              (.var 5 + 16 + 16 * .var 15) (.var 2 + .var 14) (UInt64.ofNat out + 16 + 16 * UInt64.ofNat j)
              (f (2 + 2 * j)) (by simp [env₃, eval, assign, h5, h15, last, indexWord, aluResult])
              (by simp [env₃, eval, assign, h2, aluResult, stopJ]) (by rw [rj]; exact accJ)
            rw [rj, Width.bytes, store_wordsAt, writtenFields_next i j before] at s2
            exact Runs.ite_true 1 (by simp [env₃, eval, Expr.ne, assign, h15, last, indexWord, Cond.holds, jWord])
              (by decide) (Runs.block_cons s2 (Runs.block_nil _ _ _ _ _))
        have hstate : state (i + 1) = wordsAt out f (writtenFields (i + 1) (some i)) mem := by
          simp only [state, nowLast]
        rw [← hstate] at closed
        refine finish (assign (assign env₃ 15 i.toUInt64) 13 (lw (i + 1)).toUInt64)
          (by simp [env₃, env₂, assign]) (by simp [env₃, env₂, assign])
          (fun k hk => by simp [env₃, env₂, assign, show k ≠ 13 by omega, show k ≠ 12 by omega,
            show k ≠ 14 by omega, show k ≠ 15 by omega])
          (Runs.ite_false (by simp [eval, Expr.ne, g12, word, Cond.holds])
            (Runs.block_cons (Runs.set _ _ _ _ _ 14 _ _ readO) (Runs.block_cons s1 (Runs.block_cons closed
              (Runs.block_cons (Runs.set _ _ _ _ _ 15 _ _ (by simp [env₃, eval, assign, h10]))
                (Runs.set _ _ _ _ _ 13 _ _ (by simp [env₃, eval, assign, h13, aluResult, stepLw])))))))
          (by simp [assign]) (by simp [assign, nowLast, indexWord])
      )
  have none₀ : state 0 = mem := by
    have empty : writtenFields 0 (lastBody P 0) = fun _ => false := by
      funext k; simp [writtenFields, lastBody]; omega
    simp only [state, empty, wordsAt_none]
  obtain ⟨env', mem', runs, ⟨kept, i, within, g10, -, -, g15, hmem⟩, exit⟩ :=
    loop env mem ⟨fun _ _ => rfl, 0, Nat.zero_le _, by simp [e10], by simp [e11, pos, wordsAll],
      by simp [e13, lw, Desc.leadingWidth], by simp [e15, lastBody], none₀.symm⟩
  have done : i = fields.length := by
    have small_i : i < 2 ^ 64 := by omega
    have g4 : env' 4 = fields.length.toUInt64 := by rw [kept 4 (by decide), e4]
    by_cases more : i < fields.length
    · simp [eval, Expr.lt, g10, g4, Cond.holds, ofNat_lt_ofNat i fields.length small_i (by omega), more] at exit
    · omega
  subst done hmem
  exact ⟨env', runs, kept, g15⟩

/-- A run of two statements in order is a run of the first, then of the second. -/
theorem Runs.seq_inv {m : Module} {w : World} {sp : Nat} {env env'' : Env} {mem mem'' : Memory} {a c : Stmt}
    (h : Runs m w sp env mem (.seq a c) env'' mem'') :
    ∃ env' mem', Runs m w sp env mem a env' mem' ∧ Runs m w sp env' mem' c env'' mem'' := by
  obtain ⟨fuel, run⟩ := h
  cases fuel with
  | zero => simp [Ir.exec] at run
  | succ fuel =>
    simp only [Ir.exec, bind, Option.bind] at run
    cases first : Ir.exec m w fuel sp env mem a with
    | none => simp [first] at run
    | some r =>
      obtain ⟨env', mem'⟩ := r
      simp only [first] at run
      exact ⟨env', mem', ⟨fuel, first⟩, ⟨fuel, run⟩⟩

/-- Two blocks run one after the other run as the block of both. -/
theorem Runs.block_join {m : Module} {w : World} {sp : Nat} {env env' env'' : Env} {mem mem' mem'' : Memory} :
    ∀ (first rest : List Stmt), first ≠ [] → Runs m w sp env mem (.block first) env' mem' →
      Runs m w sp env' mem' (.block rest) env'' mem'' → Runs m w sp env mem (.block (first ++ rest)) env'' mem''
  | [], _, h, _, _ => absurd rfl h
  | [s], rest, _, h₁, h₂ => Runs.block_cons h₁ h₂
  | s :: t :: more, rest, _, h₁, h₂ => by
    obtain ⟨envₘ, memₘ, hs, ht⟩ := Runs.seq_inv h₁
    exact Runs.block_cons hs (Runs.block_join (t :: more) rest (by simp) ht h₂)

/-- The stack the struct view needs below its own frame: the width walks, then the checks and the write. -/
def fieldsRoom (fields : List Desc) : Nat :=
  (8 + 8 * planFieldsWidth.frame) + (8 + 8 * planLeading.frame) + (widthLevel + walkLevel) * Desc.deepestNesting fields

/-- The last body of a struct ends at the end, since only fields in place follow it. -/
theorem lastBody_stop (places : List Place) (j : Nat) (last : lastBody places places.length = some j) (size : Nat) :
    (placeStarts (places.drop (j + 1))).headD size = size := by
  obtain ⟨before, small, -, after⟩ := lastBody_some places places.length j last
  rw [placeStarts_inline (places.drop (j + 1)) (fun k hk => by
    have := after (j + 1 + k) (by simp at hk; omega) (by omega) (by simp at hk; omega)
    simpa [List.getElem_drop] using this)]
  rfl

/-- The last stop and the count complete the words of a view. -/
theorem writtenFields_last (n j : Nat) (before : j < n) :
    (fun k => k == 0 || (fun k => k == 2 + 2 * j || writtenFields n (some j) k) k) = fun k => decide (k < 1 + 2 * n) := by
  funext k
  apply Bool.eq_iff_iff.mpr
  simp [writtenFields]; omega

/-- The count completes the words of a view with no body. -/
theorem writtenFields_count (n : Nat) :
    (fun k => k == 0 || writtenFields n none k) = fun k => decide (k < 1 + 2 * n) := by
  funext k
  apply Bool.eq_iff_iff.mpr
  simp [writtenFields]; omega

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- The budget of the struct view: the fixed part's width, and whether the struct's size fits it. -/
theorem fieldsBudget_runs (m : Module) (w : World) (linked : HasCodec m) (fields : List Desc)
    (sound : ∀ f ∈ fields, f.wellFormed = .ok ()) (thin : ∀ f ∈ fields, narrow f = true)
    (total : ∀ width, Desc.fieldsFixedSize fields = some width → width < 2 ^ 62)
    (leadSmall : Desc.leadingWidth fields < 2 ^ 62)
    (inner : Nat) (mem : Memory) (q size : Nat) (sizeSmall : size < 2 ^ 64)
    (plan : PlanAt w mem q (wordsAll fields)) (room : w.stackLo + fieldsRoom fields ≤ inner)
    (env : Env) (e0 : env 0 = q.toUInt64) (e4 : env 4 = fields.length.toUInt64) (e7 : env 7 = size.toUInt64) :
    ∃ env', Runs m w inner env mem (.seq (.call "ssz_plan_fields_width" [.var 0, .var 4] 16)
        (.ite (Expr.ne (.var 16) (.lit (none64 : Nat).toUInt64))
          (.block [.set 8 (.var 16), .set 9 (Expr.eq (.var 7) (.var 16))])
          (.block [.call "ssz_plan_leading" [.var 0, .var 4] 8, .set 9 (Expr.le (.var 8) (.var 7))]))) env' mem ∧
      (∀ k, k < 8 → env' k = env k) ∧ env' 8 = (Desc.leadingWidth fields).toUInt64 ∧
      ((env' 9 = 1 ∧ budgetOk fields size) ∨ (env' 9 = 0 ∧ ¬ budgetOk fields size)) := by
  have each : ∀ f ∈ fields, WidthOk m w f := fun f member => width_ok m w linked f (sound f member) (thin f member)
  have fr : fieldsRoom fields = (8 + 8 * planFieldsWidth.frame) + (8 + 8 * planLeading.frame) +
      (widthLevel + walkLevel) * Desc.deepestNesting fields := rfl
  have measured := fieldsWidth_ok m w linked fields sound thin total each inner mem q plan (by omega)
  have ranWidth := Runs.call (m := m) (w := w) (sp := inner) (env := env) (args := [.var 0, .var 4]) (dst := 16)
    (values := [q.toUInt64, fields.length.toUInt64]) (by simp [eval, e0, e4]) measured
  let env₁ := assign env 16 (fieldsWord fields)
  have g7 : env₁ 7 = size.toUInt64 := by simp [env₁, assign, e7]
  cases fixed : Desc.fieldsFixedSize fields with
  | some width =>
    have wSmall := total width fixed
    have word : fieldsWord fields = width.toUInt64 := by simp [fieldsWord, fixed]
    have notNone : width.toUInt64 ≠ 18446744073709551615 := by
      intro h; have := congrArg UInt64.toNat h; rw [toNat_toUInt64 _ (by omega)] at this; simp at this; omega
    have lead := leadingWidth_fixed fields width fixed
    refine ⟨_, Runs.seq ranWidth (Runs.ite_true 1 (by simp [env₁, eval, Expr.ne, assign, word, Cond.holds, notNone])
      (by decide) (Runs.block_cons (Runs.set _ _ _ _ _ 8 _ width.toUInt64 (by simp [env₁, eval, assign, word]))
        (Runs.set _ _ _ _ _ 9 _ (if size = width then 1 else 0) ?_))), fun k hk => ?_, ?_, ?_⟩
    · simp only [Expr.eq]
      rw [eval_cmp .e (x := size.toUInt64) (y := width.toUInt64) (by simp [eval, assign, e7, env₁])
        (by simp [eval, assign, env₁, word])]
      simp [Cond.holds, ofNat_eq_ofNat size width sizeSmall (by omega)]
    · simp [assign, env₁, show k ≠ 9 by omega, show k ≠ 8 by omega, show k ≠ 16 by omega]
    · simp [assign, lead]
    · by_cases same : size = width
      · exact Or.inl ⟨by simp [assign, same], by simp [budgetOk, fixed, same]⟩
      · exact Or.inr ⟨by simp [assign, same], by simp [budgetOk, fixed, same]⟩
  | none =>
    have word : fieldsWord fields = 18446744073709551615 := by simp [fieldsWord, fixed]
    have led := leading_ok m w linked fields sound thin each inner mem q plan (by omega)
    have ranLead := Runs.call (m := m) (w := w) (sp := inner) (env := env₁) (args := [.var 0, .var 4]) (dst := 8)
      (values := [q.toUInt64, fields.length.toUInt64]) (by simp [env₁, eval, assign, e0, e4]) led
    refine ⟨_, Runs.seq ranWidth (Runs.ite_false (by simp [env₁, eval, Expr.ne, assign, word, Cond.holds])
      (Runs.block_cons ranLead (Runs.set _ _ _ _ _ 9 _ (if Desc.leadingWidth fields ≤ size then 1 else 0) ?_))),
      fun k hk => ?_, ?_, ?_⟩
    · simp only [Expr.le]
      rw [eval_cmp .be (x := (Desc.leadingWidth fields).toUInt64) (y := size.toUInt64) (by simp [eval, assign])
        (by simp [eval, assign, env₁, e7])]
      simp only [holds_be, Nat.toUInt64_eq, ofNat_le_iff _ _ (show Desc.leadingWidth fields < 2 ^ 64 by omega)
        sizeSmall, decide_eq_true_eq]
    · simp [assign, env₁, show k ≠ 9 by omega, show k ≠ 8 by omega, show k ≠ 16 by omega]
    · simp [assign]
    · by_cases fits : Desc.leadingWidth fields ≤ size
      · exact Or.inl ⟨by simp [assign, fits], by simp [budgetOk, fixed, fits]⟩
      · exact Or.inr ⟨by simp [assign, fits], by simp [budgetOk, fixed, fits]⟩

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
/-- A struct's view: the driver writes the ranges `fieldRanges` computes, or refuses as it does. -/
theorem fields_ok (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory) (fields : List Desc)
    (data start stop out cap q : Nat) (b : ByteArray)
    (sound : ∀ f ∈ fields, f.wellFormed = .ok ()) (thin : ∀ f ∈ fields, narrow f = true)
    (total : ∀ width, Desc.fieldsFixedSize fields = some width → width < 2 ^ 62)
    (leadSmall : Desc.leadingWidth fields < 2 ^ 62)
    (plan : PlanAt w mem q (wordsAll fields))
    (planApart : q + 8 * (wordsAll fields).length ≤ out ∨ out + 8 * (1 + 2 * cap) ≤ q)
    (at_ : ViewMemory w mem data b out cap) (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (room : w.stackLo + 8 + 8 * fieldsView.frame + fieldsRoom fields ≤ sp) :
    Calls m w "ssz_fields_ranges" sp
      [q.toUInt64, data.toUInt64, start.toUInt64, stop.toUInt64, fields.length.toUInt64, out.toUInt64] mem
      (viewOutcome out cap mem (fieldRanges fields b start stop)).1
      (viewOutcome out cap mem (fieldRanges fields b start stop)).2 := by
  have found : m.fns.lookup "ssz_fields_ranges" = some fieldsView :=
    linked ("ssz_fields_ranges", fieldsView) (by simp [codecFns])
  have each : ∀ f ∈ fields, WidthOk m w f := fun f member => width_ok m w linked f (sound f member) (thin f member)
  have fr : fieldsRoom fields = (8 + 8 * planFieldsWidth.frame) + (8 + 8 * planLeading.frame) +
      (widthLevel + walkLevel) * Desc.deepestNesting fields := rfl
  have outBound : out + 8 + 16 * cap ≤ 2 ^ 63 := by
    have := at_.writable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have dataBound : data + b.size ≤ 2 ^ 63 := by
    have := at_.readable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have lenSmall : fields.length < 2 ^ 63 := by
    have := wordsAll_length_ge fields; have := plan.1; simp only [addressBound] at this; omega
  have outReadable : w.access out 8 := by simpa using access_inside at_.writable 0 8 (by omega)
  let inner := sp - 8 - 8 * fieldsView.frame
  let args := [q.toUInt64, data.toUInt64, start.toUInt64, stop.toUInt64, fields.length.toUInt64, out.toUInt64]
  let size := stop - start
  let P := placesFrom fields b start 0
  have sizeSmall : size < 2 ^ 64 := by omega
  have s7 := Runs.set m w inner (entryEnv args) mem 7 (.op .sub (.var 3) (.var 2)) size.toUInt64
    (by simp [eval, args, entryEnv, aluResult, size, ofNat_sub _ _ ordered (by omega)])
  have s6 := Runs.set m w inner (assign (entryEnv args) 7 size.toUInt64) mem 6 (.lit 1) 1 rfl
  let env₁ := assign (assign (entryEnv args) 7 size.toUInt64) 6 1
  have finish : ∀ env' mem' (r : UInt64),
      Runs m w inner env₁ mem (afterTwo fieldsView.body) env' mem' → env' 6 = r →
      Calls m w "ssz_fields_ranges" sp args mem r mem' := by
    intro env' mem' r main answer
    refine Calls.fn (env' := env') found (by omega) rfl ?_ (by simp [fieldsView, Struct.r, eval, answer])
    rw [fieldsView_body]
    exact Runs.seq s7 (Runs.seq s6 main)
  have arg : ∀ k, k < 6 → env₁ k = args.getD k 0 := by
    intro k hk; simp [env₁, assign, entryEnv, show k ≠ 6 by omega, show k ≠ 7 by omega]
  by_cases big : offsetBound ≤ size
  · -- Too big for four-byte offsets: refused before anything else.
    rw [viewOutcome_refused out cap mem _ (fun x h => by
      simp [fieldRanges, fieldPlaces, show offsetBound ≤ stop - start from big, throw, throwThe,
        MonadExceptOf.throw, Bind.bind, Except.bind] at h)]
    refine finish env₁ mem 1 ?_ (by simp [env₁, assign])
    rw [fieldsView_main]
    refine Runs.ite_false ?_ (Runs.skip _ _ _ _ _)
    simp [env₁, eval, Expr.lt, assign, Cond.holds, ofNat_lt_ofNat size 4294967296 sizeSmall (by decide)]
    simp [offsetBound] at big; omega
  have small : size < offsetBound := by omega
  have fitsWords : eval w env₁ mem (Expr.lt (.var 7) (.lit (offsetLimit : Nat).toUInt64)) = some 1 := by
    simp [env₁, eval, Expr.lt, assign, Cond.holds, ofNat_lt_ofNat size 4294967296 sizeSmall (by decide)]
    simp [offsetBound] at small; omega
  -- The budget.
  obtain ⟨env₂, ranBudget, kept₂, l8, flag⟩ := fieldsBudget_runs m w linked fields sound thin total leadSmall inner
    mem q size sizeSmall plan (by simp only [inner]; omega) env₁ (by rw [arg 0 (by decide)]; rfl)
    (by rw [arg 4 (by decide)]; rfl) (by simp [env₁, assign])
  -- The check.
  let env₃ := assign (assign (assign (assign env₂ 10 0) 11 (env₂ 0)) 13 0) 15 (prevWord none)
  have k3 : ∀ k, k < 10 → env₃ k = env₂ k := by
    intro k hk; simp [env₃, assign, show k ≠ 10 by omega, show k ≠ 11 by omega, show k ≠ 13 by omega,
      show k ≠ 15 by omega]
  have q0 : env₂ 0 = q.toUInt64 := by rw [kept₂ 0 (by decide), arg 0 (by decide)]; rfl
  have setup : Runs m w inner env₂ mem (.block [.set 10 0, .set 11 (.var 0), .set 13 0,
      .set 15 (.lit (none64 : Nat).toUInt64)]) env₃ mem :=
    Runs.block_cons (Runs.set _ _ _ _ _ 10 _ _ rfl) (Runs.block_cons (Runs.set _ _ _ _ _ 11 _ _
      (by simp [eval, assign])) (Runs.block_cons (Runs.set _ _ _ _ _ 13 _ _ rfl)
        (Runs.set _ _ _ _ _ 15 _ _ (by simp [eval, prevWord]))))
  obtain ⟨env₄, ranCheck, kept₄, result⟩ := fieldsCheck_runs m w linked fields sound thin each inner mem q data
    start stop out cap b plan at_ ordered inside leadSmall (by simp only [inner]; omega) env₃
    (by rw [k3 1 (by decide), kept₂ 1 (by decide), arg 1 (by decide)]; rfl)
    (by rw [k3 2 (by decide), kept₂ 2 (by decide), arg 2 (by decide)]; rfl)
    (by rw [k3 4 (by decide), kept₂ 4 (by decide), arg 4 (by decide)]; rfl)
    (by rw [k3 8 (by decide)]; exact l8) (by simp [env₃, assign]) (by simp [env₃, assign, q0])
    (by simp [env₃, assign]) (by simp [env₃, assign])
    (by simpa [env₃, assign] using flag)
  let a8 : Stmt := .ite (.op .and (.var 9) (Expr.ne (.var 15) (.lit (none64 : Nat).toUInt64)))
    (.block [.set 9 (Expr.le (.var 15) (.var 7))]) .skip
  let a9 : Stmt := .ite (.var 9) (.block [.set 6 2, .ite (Expr.le (.var 4) (Expr.ld (.var 5)))
    (.block [.set 10 0, .set 11 (.var 0), .set 13 0, .set 15 (.lit (none64 : Nat).toUInt64), fieldsWrite,
      .ite (Expr.ne (.var 15) (.lit (none64 : Nat).toUInt64))
        (.block [Stmt.st (.var 5 + 16 + 16 * .var 15) (.var 3)]) .skip,
      Stmt.st (.var 5) (.var 4), .set 6 0]) .skip]) .skip
  -- Everything before the last test, then the last test and the write.
  have through : ∀ env' mem', Runs m w inner env₄ mem (.block [a8, a9]) env' mem' →
      Runs m w inner env₁ mem (afterTwo fieldsView.body) env' mem' := by
    intro env' mem' tail
    rw [fieldsView_main]
    refine Runs.ite_true 1 fitsWords (by decide) ?_
    have all := Runs.block_join [.call "ssz_plan_fields_width" [.var 0, .var 4] 16,
      .ite (Expr.ne (.var 16) (.lit (none64 : Nat).toUInt64))
        (.block [.set 8 (.var 16), .set 9 (Expr.eq (.var 7) (.var 16))])
        (.block [.call "ssz_plan_leading" [.var 0, .var 4] 8, .set 9 (Expr.le (.var 8) (.var 7))])] _ (by simp)
      ranBudget (Runs.block_join _ _ (by simp) setup (Runs.block_cons ranCheck tail))
    exact all
  have k4 : ∀ k, k < 9 → env₄ k = env₁ k ∨ k = 8 := by
    intro k hk
    by_cases e8 : k = 8
    · exact Or.inr e8
    · left; rw [kept₄ k hk, k3 k (by omega), kept₂ k (by omega)]
  have f3 : env₄ 3 = stop.toUInt64 := by
    rw [kept₄ 3 (by decide), k3 3 (by decide), kept₂ 3 (by decide)]; simp [env₁, assign, args, entryEnv]
  have f4 : env₄ 4 = fields.length.toUInt64 := by
    rw [kept₄ 4 (by decide), k3 4 (by decide), kept₂ 4 (by decide)]; simp [env₁, assign, args, entryEnv]
  have f5 : env₄ 5 = out.toUInt64 := by
    rw [kept₄ 5 (by decide), k3 5 (by decide), kept₂ 5 (by decide)]; simp [env₁, assign, args, entryEnv]
  have f7 : env₄ 7 = size.toUInt64 := by
    rw [kept₄ 7 (by decide), k3 7 (by decide), kept₂ 7 (by decide)]; simp [env₁, assign, args, entryEnv]
  rcases result with ⟨up, budget, checked, last⟩ | ⟨down, refused⟩
  · -- The budget held and the offsets were in order: the last offset is checked against the end.
    obtain ⟨env₅, ranLast, f9, decided⟩ : ∃ env₅, Runs m w inner env₄ mem a8 env₅ mem ∧
        (∀ k, k ≠ 9 → env₅ k = env₄ k) ∧
        ((env₅ 9 = 1 ∧ tableAccepts (placeStarts P) (Desc.leadingWidth fields) size) ∨
          (env₅ 9 = 0 ∧ ¬ tableAccepts (placeStarts P) (Desc.leadingWidth fields) size)) := by
      have accepts := checkFrom_none (Desc.leadingWidth fields) size (placeStarts (placesFrom fields b start 0))
      cases hl : lastOf none (placeStarts (placesFrom fields b start 0)) with
      | none =>
        refine ⟨env₄, Runs.ite_false (by simp [eval, up, last, hl, prevWord, Expr.ne, Cond.holds, aluResult])
          (Runs.skip _ _ _ _ _), fun _ _ => rfl, Or.inl ⟨up, accepts.mp ⟨checked, by simp [hl]⟩⟩⟩
      | some l =>
        have lSmall : l < 2 ^ 32 := by
          rcases lastOf_mem none _ l hl with inside | first
          · exact placesFrom_starts_small b start fields 0 l inside
          · cases first
        have lWord : l.toUInt64 ≠ 18446744073709551615 := by
          intro h; have := congrArg UInt64.toNat h; rw [toNat_toUInt64 _ (by omega)] at this; simp at this; omega
        refine ⟨assign env₄ 9 (if l ≤ size then 1 else 0), Runs.ite_true 1
          (by simp [eval, up, last, hl, prevWord, Expr.ne, Cond.holds, aluResult, lWord]) (by decide)
          (Runs.set _ _ _ _ _ 9 _ _ ?_), fun k hk => by simp [assign, hk], ?_⟩
        · simp only [Expr.le]
          rw [eval_cmp .be (x := l.toUInt64) (y := size.toUInt64) (by simp [eval, last, hl, prevWord])
            (by simp [eval, f7])]
          simp only [holds_be, Nat.toUInt64_eq, ofNat_le_iff l size (by omega) sizeSmall, decide_eq_true_eq]
        · by_cases inside : l ≤ size
          · exact Or.inl ⟨by simp [assign, inside], accepts.mp ⟨checked, by simp [hl, inside]⟩⟩
          · refine Or.inr ⟨by simp [assign, inside], fun acc => inside ?_⟩
            exact (accepts.mpr acc).2 l hl
    have r6 : env₅ 6 = 1 := by
      rw [f9 6 (by decide), kept₄ 6 (by decide), k3 6 (by decide), kept₂ 6 (by decide)]; simp [env₁, assign]
    have g k (hk : k < 9) (h9 : k ≠ 9) : env₅ k = env₄ k := f9 k h9
    rcases decided with ⟨up₅, accepts⟩ | ⟨down₅, rejects⟩
    · -- Accepted: the ranges are written when they fit.
      have accepted := fieldRanges_accepted fields b start stop (by omega) budget
        ((tableOk_iff_accepts _ _ _).mpr accepts)
      let R := rangesOf start size P
      have lenR : R.length = fields.length := by simp [R, rangesOf_length, P, placesFrom_length]
      rw [accepted]
      simp only [viewOutcome, show (rangesOf start (stop - start) (placesFrom fields b start 0)).length =
        fields.length from lenR]
      let env₆ := assign env₅ 6 2
      have h4 : env₆ 4 = fields.length.toUInt64 := by simp [env₆, assign, g 4 (by decide) (by decide), f4]
      have h5 : env₆ 5 = out.toUInt64 := by simp [env₆, assign, g 5 (by decide) (by decide), f5]
      have h3 : env₆ 3 = stop.toUInt64 := by simp [env₆, assign, g 3 (by decide) (by decide), f3]
      have room' : eval w env₆ mem (Expr.le (.var 4) (Expr.ld (.var 5))) =
          some (if fields.length ≤ cap then 1 else 0) := by
        simp only [Expr.le, Expr.ld]
        rw [eval_cmp .be (x := fields.length.toUInt64) (y := cap.toUInt64) (by simp [eval, h4])
          (by simp [eval, h5, Width.bytes, toNat_toUInt64 out (by omega), outReadable, at_.capacity])]
        simp only [holds_be, Nat.toUInt64_eq, decide_eq_true_eq]
        have le := ofNat_le_iff fields.length cap (by omega) at_.smallCap
        by_cases c : fields.length ≤ cap <;> simp [c, le]
      by_cases fits : fields.length ≤ cap
      · simp only [fits, if_true]
        let env₇ := assign (assign (assign (assign env₆ 10 0) 11 (env₆ 0)) 13 0) 15 (indexWord none)
        have k7 : ∀ k, k < 10 → env₇ k = env₆ k := by
          intro k hk; simp [env₇, assign, show k ≠ 10 by omega, show k ≠ 11 by omega, show k ≠ 13 by omega,
            show k ≠ 15 by omega]
        have q6 : env₆ 0 = q.toUInt64 := by
          simp [env₆, assign, g 0 (by decide) (by decide), kept₄ 0 (by decide), k3 0 (by decide), q0]
        have setup₂ : Runs m w inner env₆ mem (.block [.set 10 0, .set 11 (.var 0), .set 13 0,
            .set 15 (.lit (none64 : Nat).toUInt64)]) env₇ mem :=
          Runs.block_cons (Runs.set _ _ _ _ _ 10 _ _ rfl) (Runs.block_cons (Runs.set _ _ _ _ _ 11 _ _
            (by simp [eval, assign])) (Runs.block_cons (Runs.set _ _ _ _ _ 13 _ _ rfl)
              (Runs.set _ _ _ _ _ 15 _ _ (by simp [eval, indexWord]))))
        have eh : ∀ k, k < 6 → env₆ k = args.getD k 0 := by
          intro k hk
          simp [env₆, assign, show k ≠ 6 by omega]
          rw [g k (by omega) (by omega), kept₄ k (by omega), k3 k (by omega), kept₂ k (by omega), arg k hk]; rfl
        obtain ⟨env₈, ranWrite, kept₈, last₈⟩ := fieldsWrite_runs m w linked fields sound thin each inner mem q
          data start stop out cap b plan at_ planApart ordered inside (by
            simp only [budgetOk] at budget
            cases fixed : Desc.fieldsFixedSize fields with
            | none => simp [fixed] at budget; exact budget
            | some width => simp [fixed] at budget; rw [leadingWidth_fixed fields width fixed]; omega)
          fits (by simp only [inner]; omega) env₇
          (by rw [k7 1 (by decide), eh 1 (by decide)]; rfl) (by rw [k7 2 (by decide), eh 2 (by decide)]; rfl)
          (by rw [k7 4 (by decide), eh 4 (by decide)]; rfl) (by rw [k7 5 (by decide), eh 5 (by decide)]; rfl)
          (by simp [env₇, assign]) (by simp [env₇, assign, q6]) (by simp [env₇, assign]) (by simp [env₇, assign])
        have j3 : env₈ 3 = stop.toUInt64 := by rw [kept₈ 3 (by decide), k7 3 (by decide), h3]
        have j4 : env₈ 4 = fields.length.toUInt64 := by rw [kept₈ 4 (by decide), k7 4 (by decide), h4]
        have j5 : env₈ 5 = out.toUInt64 := by rw [kept₈ 5 (by decide), k7 5 (by decide), h5]
        let f := viewWord R
        -- The last body's stop is the end, then the count goes first.
        have closing : Runs m w inner env₈
            (wordsAt out f (writtenFields fields.length (lastBody P fields.length)) mem)
            (.block [.ite (Expr.ne (.var 15) (.lit (none64 : Nat).toUInt64))
                (.block [Stmt.st (.var 5 + 16 + 16 * .var 15) (.var 3)]) .skip,
              Stmt.st (.var 5) (.var 4), .set 6 0]) (assign env₈ 6 0) (viewed out R mem) := by
          have countWord : f 0 = fields.length.toUInt64 := by simp [f, viewWord, lenR]
          have final : viewed out R mem = wordsAt out f (fun k => decide (k < 1 + 2 * fields.length)) mem := by
            simp only [viewed, lenR]; rfl
          rw [final]
          cases lb : lastBody P fields.length with
          | none =>
            have lb' : lastBody (placesFrom fields b start 0) fields.length = none := lb
            have stored := Runs.store m w inner env₈ (wordsAt out f (writtenFields fields.length none) mem) .b8
              (.var 5) (.var 4) out.toUInt64 (f 0) (by simp [eval, j5]) (by simp [eval, j4, countWord])
              (by rw [toNat_toUInt64 out (by omega)]; exact outReadable)
            rw [toNat_toUInt64 out (by omega), Width.bytes, store_wordsAt_zero, writtenFields_count] at stored
            exact Runs.block_cons (Runs.ite_false (by simp [eval, Expr.ne, last₈, lb', indexWord, Cond.holds])
              (Runs.skip _ _ _ _ _)) (Runs.block_cons stored (Runs.set _ _ _ _ _ 6 _ _ rfl))
          | some j =>
            have lb' : lastBody (placesFrom fields b start 0) fields.length = some j := lb
            have jSmall : j < fields.length := by
              have := (lastBody_some P P.length j (by simp [P, placesFrom_length, lb])).1
              simp [P, placesFrom_length] at this; exact this
            have jWord : j.toUInt64 ≠ 18446744073709551615 := by
              intro h; have := congrArg UInt64.toNat h; rw [toNat_toUInt64 _ (by omega)] at this; simp at this
              omega
            have stopJ : f (2 + 2 * j) = stop.toUInt64 := by
              have small : j < P.length := by simp [P, placesFrom_length]; exact jSmall
              have rangeJ := rangesOf_get start size P j small
              obtain ⟨-, wj⟩ := viewWord_get R j (by rw [lenR]; exact jSmall)
              have ends := lastBody_stop P j (by simp [P, placesFrom_length, lb]) size
              have isBody := (lastBody_some P P.length j (by simp [P, placesFrom_length, lb])).2.2.1
              cases hj : P[j] with
              | inline _ _ => rw [hj] at isBody; simp [Place.isBody] at isBody
              | body oj =>
                rw [hj] at rangeJ
                simp only [f, wj, R, rangeJ, ends, size]
                congr 1; omega
            have rj : (UInt64.ofNat out + 16 + 16 * UInt64.ofNat j).toNat = out + 8 * (2 + 2 * j) := by
              have := out_addr out 16 j (by omega)
              simp only [show UInt64.ofNat 16 = 16 from rfl] at this; rw [this]; omega
            have accJ : w.access (out + 8 * (2 + 2 * j)) 8 := access_inside at_.writable _ 8 (by omega)
            have s1 := Runs.store m w inner env₈ (wordsAt out f (writtenFields fields.length (some j)) mem) .b8
              (.var 5 + 16 + 16 * .var 15) (.var 3) (UInt64.ofNat out + 16 + 16 * UInt64.ofNat j) (f (2 + 2 * j))
              (by simp [eval, j5, last₈, lb', indexWord, aluResult]) (by simp [eval, j3, stopJ])
              (by rw [rj]; exact accJ)
            rw [rj, Width.bytes, store_wordsAt] at s1
            have s2 := Runs.store m w inner env₈
              (wordsAt out f (fun k => k == 2 + 2 * j || writtenFields fields.length (some j) k) mem) .b8
              (.var 5) (.var 4) out.toUInt64 (f 0) (by simp [eval, j5]) (by simp [eval, j4, countWord])
              (by rw [toNat_toUInt64 out (by omega)]; exact outReadable)
            rw [toNat_toUInt64 out (by omega), Width.bytes, store_wordsAt_zero,
              writtenFields_last fields.length j jSmall] at s2
            exact Runs.block_cons (Runs.ite_true 1 (by simp [eval, Expr.ne, last₈, lb', indexWord, Cond.holds, jWord])
              (by decide) (Runs.block_cons s1 (Runs.block_nil _ _ _ _ _)))
              (Runs.block_cons s2 (Runs.set _ _ _ _ _ 6 _ _ rfl))
        refine finish _ _ _ (through _ _ (Runs.block_cons ranLast (Runs.ite_true 1 (by simp [eval, up₅])
          (by decide) (Runs.block_cons (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_true 1 (by rw [room']; simp [fits])
            (by decide) (Runs.block_join _ _ (by simp) setup₂ (Runs.block_cons ranWrite closing))))))) (by
              simp [assign])
      · simp only [fits, if_false]
        refine finish _ _ _ (through _ _ (Runs.block_cons ranLast (Runs.ite_true 1 (by simp [eval, up₅])
          (by decide) (Runs.block_cons (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_false (by rw [room']; simp [fits])
            (Runs.skip _ _ _ _ _)))))) (by simp [env₆, assign])
    · -- Refused at the end: nothing written.
      rw [viewOutcome_refused out cap mem _ (fieldRanges_refused fields b start stop (by omega)
        (fun ⟨_, table⟩ => rejects ((tableOk_iff_accepts _ _ _).mp table)))]
      refine finish env₅ mem 1 (through env₅ mem (Runs.block_cons ranLast (Runs.ite_false (by simp [eval, down₅])
        (Runs.skip _ _ _ _ _)))) r6
  · -- The budget failed or the offsets were out of order: refused, with nothing written.
    rw [viewOutcome_refused out cap mem _ (fieldRanges_refused fields b start stop (by omega)
      (fun ⟨budget, table⟩ => refused ⟨budget, (tableOk_iff_accepts _ _ _).mp table⟩))]
    refine finish env₄ mem 1 (through env₄ mem (Runs.block_cons (Runs.ite_false (by simp [eval, down, aluResult, Expr.ne, Cond.holds])
      (Runs.skip _ _ _ _ _)) (Runs.ite_false (by simp [eval, down]) (Runs.skip _ _ _ _ _)))) ?_
    rw [kept₄ 6 (by decide), k3 6 (by decide), kept₂ 6 (by decide)]
    simp [env₁, assign]

end Ssz.Native.Driver
