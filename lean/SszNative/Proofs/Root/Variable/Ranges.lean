import SszNative.Proofs.Root.Variable.Facts

/-! The ranges the root reads a sequence's elements from are the ranges the decoding check accepted. -/

namespace Ssz.Native.RootProof

open Ssz Ssz.Native

/-- Bodies opened by a valid offset table run from each offset to the next, the last to the end. -/
theorem bodies_eq (start scope : Nat) : ∀ (offsets spans : List Nat), offsetSpans offsets scope = .ok spans →
    bodies start offsets spans =
      (offsets.zip (offsets.drop 1 ++ [scope])).map fun (o, e) => (start + o, start + e)
  | [], spans, read => by
    -- No offsets open no bodies.
    simp only [offsetSpans] at read
    cases read
    rfl
  | [o], spans, read => by
    -- The last offset's body runs to the end of the scope.
    simp only [offsetSpans] at read
    split at read
    · cases read
    · cases read
      simp [bodies]
      omega
  | o :: n :: rest, spans, read => by
    -- Ordered offsets give a span each, and the rest follow by induction.
    simp only [offsetSpans, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    · rename_i ordered
      cases tail : offsetSpans (n :: rest) scope with
      | error e => simp [tail] at read
      | ok rest' =>
        simp only [tail] at read
        cases read
        have ih := bodies_eq start scope (n :: rest) rest' tail
        simp only [bodies, List.zip_cons_cons, List.map_cons] at ih ⊢
        rw [ih]
        simp only [List.drop_one, List.tail_cons, List.cons_append, List.zip_cons_cons, List.map_cons]
        congr 2
        omega

/-- A vector's element ranges are the ranges its check accepted. -/
theorem elementRanges_vector (element : Desc) (length : Nat) (b : ByteArray) (start stop : Nat) (r : Ranges)
    (read : vectorRanges element length b start stop = .ok r) :
    elementRanges element b start stop length = r.toList := by
  -- An accepted vector passed its size check.
  simp only [vectorRanges, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure,
    Except.pure] at read
  split at read
  · cases read
  · simp only [elementRanges]
    split at read
    -- Fixed-size elements sit one width apart on both sides.
    · rename_i width fixed
      rw [fixed]
      split at read
      · cases read
      · cases read; rfl
    -- Elements found through offsets: none for an empty vector, else the bodies the table opens.
    · rename_i fixed
      rw [fixed]
      split at read
      · cases read
      split at read
      · rename_i zero
        cases read
        simp at zero
        subst zero
        rfl
      split at read
      · cases read
      cases spans : offsetSpans ((List.range length).map fun i => offsetAt b (start + i * bytesPerOffset))
          (stop - start) with
      | error e => simp [spans] at read
      | ok spans' =>
        simp only [spans] at read
        cases read
        simp only [Ranges.toList, bodyRanges]
        rw [bodies_eq start (stop - start) _ _ spans]

/-- A list's element count and ranges are the count and ranges its check accepted. -/
theorem elementRanges_list (element : Desc) (limit : Option Nat) (b : ByteArray) (start stop : Nat) (r : Ranges)
    (read : listRanges element limit b start stop = .ok r) :
    elementCount element b start stop = r.toList.length ∧
      elementRanges element b start stop (elementCount element b start stop) = r.toList := by
  -- An accepted list passed its size check.
  simp only [listRanges, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure,
    Except.pure] at read
  split at read
  · cases read
  split at read
  -- An empty list has no elements on either side.
  · rename_i empty
    cases read
    simp at empty
    simp only [elementCount, elementRanges, empty, Ranges.toList]
    split <;> simp [bodyRanges]
  simp only [elementCount, elementRanges]
  split at read
  -- Fixed-size elements are counted by width and sit one width apart on both sides.
  · rename_i width fixed
    rw [fixed]
    repeat' (first | (split at read) | (cases read))
    all_goals simp_all [Ranges.toList]
  -- Elements found through offsets are counted by the first offset, and run from offset to offset.
  · rename_i fixed
    rw [fixed]
    rename_i _ nonzero _
    simp only [beq_iff_eq] at nonzero
    simp only [beq_iff_eq, nonzero, ↓reduceIte]
    cases spans : offsetSpans ((List.range (offsetAt b start / bytesPerOffset)).map fun i =>
        offsetAt b (start + i * bytesPerOffset)) (stop - start) with
    | error e =>
      simp only [spans] at read
      repeat' (first | (split at read) | (cases read))
    | ok spans' =>
      simp only [spans] at read
      have listed : r = .listed (bodies start ((List.range (offsetAt b start / bytesPerOffset)).map fun i =>
          offsetAt b (start + i * bytesPerOffset)) spans') := by
        repeat' (first | (split at read) | (cases read; rfl) | (cases read))
      subst listed
      -- The spans pair up with the offsets, so the count is the number of offsets.
      have lengths := offsetSpans_length spans
      simp only [Ranges.toList, bodies, List.length_map, List.length_zip, lengths, List.length_range,
        Nat.min_self, bodyRanges, true_and]
      rw [← bodies_eq start (stop - start) _ _ spans]
      rfl
