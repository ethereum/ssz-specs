import SszNative.Proofs.Validate.Slices

/-! The checks of a range agreeing with deserialization's checks of its slice, one kind of type at a time. -/

namespace Ssz.Native

open Ssz

/-- A delimited bit encoding is refused for the same reason in both readings. -/
theorem delimited_agrees (b : ByteArray) (start stop : Nat) (limit : Option Nat) (ordered : start ≤ stop)
    (inside : stop ≤ b.size) :
    (delimitedCount b start stop limit).map (fun _ => ()) =
      (unpackDelimited limit (slice b start stop)).map (fun _ => ()) := by
  -- The slice has the range's size, and its bytes are the range's.
  have size := slice_size b start stop inside
  simp only [delimitedCount, unpackDelimited]
  rw [slice_all b start stop inside, size]
  -- An empty range has no delimiter byte, and both refuse it.
  by_cases empty : stop - start = 0
  · simp [empty, throw, throwThe, MonadExceptOf.throw, Except.map, Bind.bind, Except.bind]
  -- The last byte of the slice is the last byte of the range.
  · have final := slice_getElem! b start stop (stop - start - 1) inside (by omega)
    rw [show start + (stop - start - 1) = stop - 1 by omega] at final
    simp only [final]
    simp only [throw, throwThe, MonadExceptOf.throw, Except.map, Bind.bind, Except.bind, pure, Except.pure,
      beq_iff_eq]
    -- A zero last byte is refused, as all zeros or as trailing zeros, alike on both sides.
    by_cases zero : b.get! (stop - 1) = 0
    · simp only [zero, empty, ↓reduceIte]
      by_cases all : ((List.range (stop - start)).all fun i => b.get! (start + i) == 0) = true <;>
        simp only [all, ↓reduceIte, Bool.false_eq_true]
    -- Otherwise the bit count is the same, and only a declared cap can refuse it.
    · simp only [zero, empty, ↓reduceIte]
      cases limit with
      | none => rfl
      | some cap =>
        by_cases over : cap < 8 * (stop - start - 1) + highestBit (b.get! (stop - 1)) <;>
          simp [over]

/-- Ranges inside a range, each standing for the slice deserialization cut. -/
def Cuts (b : ByteArray) (start stop : Nat) (ranges : List (Nat × Nat)) (slices : List Bytes) : Prop :=
  slices = ranges.map (fun p => slice b p.1 p.2) ∧ ∀ p ∈ ranges, start ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ stop

/-- A native step and a deserialization step agreeing: the same refusal, or ranges that cut the same slices. -/
def CutAgree (b : ByteArray) (start stop : Nat) : Except Err (List (Nat × Nat)) → Except Err (List Bytes) → Prop
  | .error e, .error e' => e = e'
  | .ok ranges, .ok slices => Cuts b start stop ranges slices
  | _, _ => False

/-- Bodies an offset table opens, cut from the range as deserialization cuts them from the slice. -/
theorem bodies_cut (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop) (offsets spans : List Nat)
    (bound : ∀ pair ∈ offsets.zip spans, pair.1 + pair.2 ≤ stop - start) :
    Cuts b start stop (bodies start offsets spans)
      ((offsets.zip spans).map fun (o, s) => (slice b start stop).extract o (o + s)) := by
  -- Each body cuts the slice deserialization cuts at the same offsets.
  constructor
  · simp only [bodies, List.map_map]
    apply List.map_congr_left
    intro pair member
    obtain ⟨o, s⟩ := pair
    have := bound (o, s) member
    simp only [Function.comp, slice_extract b start stop _ _ ordered this, Nat.add_assoc]
  -- Each body lies inside the range, since its span ends within the scope.
  · intro p member
    simp only [bodies, List.mem_map] at member
    obtain ⟨pair, inside, rfl⟩ := member
    have := bound pair inside
    simp only
    omega

/-- Elements one width apart, cut from the range as deserialization cuts them from the slice. -/
theorem stride_cut (b : ByteArray) (start stop width count : Nat) (ordered : start ≤ stop)
    (fits : width * count ≤ stop - start) :
    Cuts b start stop (Ranges.stride start width count).toList
      ((List.range count).map fun i => (slice b start stop).extract (i * width) ((i + 1) * width)) := by
  -- Every element, the last included, ends inside the range.
  have within : ∀ i, i < count → (i + 1) * width ≤ stop - start := fun i small => by
    have : (i + 1) * width ≤ count * width := Nat.mul_le_mul_right _ small
    rw [Nat.mul_comm count] at this
    omega
  -- Each element's range cuts the slice deserialization cuts one width further on.
  constructor
  · simp only [Ranges.toList, List.map_map]
    apply List.map_congr_left
    intro i member
    simp only [Function.comp, slice_extract b start stop _ _ ordered (within i (List.mem_range.mp member))]
  -- Each element's range lies inside the whole range.
  · intro p member
    simp only [Ranges.toList, List.mem_map] at member
    obtain ⟨i, inside, rfl⟩ := member
    have := within i (List.mem_range.mp inside)
    simp only [Nat.succ_mul] at *
    omega

end Ssz.Native
