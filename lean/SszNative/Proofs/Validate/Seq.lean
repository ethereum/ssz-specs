import SszNative.Proofs.Validate.Parts

/-! Sequence ranges agreeing with the slices deserialization cuts. -/

namespace Ssz.Native

open Ssz

/-- A vector's ranges cut the slices deserialization cuts, or both refuse alike. -/
theorem vectorRanges_cut (element : Desc) (length : Nat) (b : ByteArray) (start stop : Nat)
    (ordered : start ≤ stop) (inside : stop ≤ b.size) :
    CutAgree b start stop ((vectorRanges element length b start stop).map Ranges.toList)
      (vectorSlices element length (slice b start stop)) := by
  -- Both sides read the same bytes, so the slice has the range's size.
  have size := slice_size b start stop inside
  simp only [vectorRanges, vectorSlices, size]
  -- A size four-byte offsets cannot name is refused first, by both.
  by_cases huge : stop - start ≥ offsetBound
  · simp [huge, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, Except.map, CutAgree]
  · simp only [offsetBound] at huge
    simp only [huge, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure]
    -- Fixed-size elements sit one width apart, and others are found through offsets.
    cases fixed : element.fixedSize with
    | some width =>
      simp only
      -- A size that is not the declared count of widths is refused by both.
      by_cases wrong : (stop - start != width * length) = true
      · simp [wrong, Except.map, CutAgree]
      · simp only [wrong, Bool.false_eq_true, ↓reduceIte, Except.map, CutAgree]
        -- Otherwise the ranges are the slices, one width apart.
        exact stride_cut b start stop width length ordered (by simp at wrong; omega)
    | none =>
      simp only
      -- Too small to hold the offset table: both refuse.
      by_cases small : stop - start < length * bytesPerOffset
      · simp [small, Except.map, CutAgree]
      · simp only [small, ↓reduceIte]
        -- No elements at all: both give an empty sequence.
        by_cases zero : (length == 0) = true
        · simp [zero, Except.map, CutAgree, Cuts, Ranges.toList]
        · simp only [zero, Bool.false_eq_true, ↓reduceIte]
          -- The offsets read from the range are the ones read from the slice.
          rw [readOffsets_slice b start stop length inside (by omega)]
          -- A wrong first offset is refused by both, and otherwise the spans decide.
          split
          · simp [Except.map, CutAgree]
          · cases spans : offsetSpans ((List.range length).map fun i => offsetAt b (start + i * bytesPerOffset))
              (stop - start) with
            | error e => simp [Except.map, CutAgree]
            | ok spans' =>
              simp only [Except.map, CutAgree]
              -- Every body lies inside the range, so each range cuts its slice.
              exact bodies_cut b start stop ordered _ _ (offsetSpans_bound _ _ _ spans)

/-- A list's ranges cut the slices deserialization cuts, or both refuse alike. -/
theorem listRanges_cut (element : Desc) (limit : Option Nat) (b : ByteArray) (start stop : Nat)
    (ordered : start ≤ stop) (inside : stop ≤ b.size) :
    CutAgree b start stop ((listRanges element limit b start stop).map Ranges.toList)
      (listSlices element limit (slice b start stop)) := by
  -- Both sides read the same bytes, so the slice has the range's size.
  have size := slice_size b start stop inside
  simp only [listRanges, listSlices, size]
  -- A size four-byte offsets cannot name is refused first, by both.
  by_cases huge : stop - start ≥ offsetBound
  · simp [huge, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, Except.map, CutAgree]
  · simp only [offsetBound] at huge
    simp only [huge, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure]
    -- An empty range is an empty list on both sides.
    by_cases empty : (stop - start == 0) = true
    · simp [empty, Except.map, CutAgree, Cuts, Ranges.toList]
    · simp only [empty, Bool.false_eq_true, ↓reduceIte]
      cases fixed : element.fixedSize with
      | some width =>
        simp only
        -- A zero width cannot divide the size, and both refuse it.
        by_cases zero : (width == 0) = true
        · simp [zero, Except.map, CutAgree]
        · simp only [zero, Bool.false_eq_true, ↓reduceIte]
          -- A size that is no whole number of elements is refused by both.
          by_cases uneven : (stop - start) % width != 0
          · simp [uneven, Except.map, CutAgree]
          · simp only [uneven, Bool.false_eq_true, ↓reduceIte]
            -- The elements cover at most the range.
            have fits : width * ((stop - start) / width) ≤ stop - start := Nat.mul_div_le _ _
            -- With a cap, both check the count first, and then the ranges are the slices.
            cases limit with
            | none => exact stride_cut b start stop width _ ordered fits
            | some cap =>
              simp only
              split
              · simp [Except.map, CutAgree]
              · exact stride_cut b start stop width _ ordered fits
      | none =>
        simp only
        -- Too small to hold even one offset: both refuse.
        by_cases small : stop - start < bytesPerOffset
        · simp [small, Except.map, CutAgree]
        · simp only [small, ↓reduceIte]
          -- The first offset is the same four bytes on both sides.
          rw [readUint_slice b start stop 0 inside (by simp only [bytesPerOffset] at small ⊢; omega), Nat.add_zero]
          -- The first offset's checks, below the table, unaligned, and past the end, refuse alike.
          by_cases below : offsetAt b start < bytesPerOffset
          · simp [below, Except.map, CutAgree]
          · simp only [below, ↓reduceIte]
            by_cases unaligned : (offsetAt b start % bytesPerOffset != 0) = true
            · simp [unaligned, Except.map, CutAgree]
            · simp only [unaligned, Bool.false_eq_true, ↓reduceIte]
              by_cases past : offsetAt b start > stop - start
              · simp [past, Except.map, CutAgree]
              · simp only [past, ↓reduceIte]
                -- The offset table fits in the range.
                have table : offsetAt b start / bytesPerOffset * bytesPerOffset ≤ stop - start := by
                  have := Nat.div_mul_le_self (offsetAt b start) bytesPerOffset
                  omega
                -- The offsets read from the range are the ones read from the slice.
                rw [readOffsets_slice b start stop _ inside table]
                -- Once the offsets are read, the spans decide both sides alike.
                have rest : ∀ (offsets : List Nat) (spans : Except Err (List Nat)),
                    offsetSpans offsets (stop - start) = spans →
                    CutAgree b start stop
                      (Except.map Ranges.toList (do
                        let spans ← offsetSpans offsets (stop - start)
                        return Ranges.listed (bodies start offsets spans)))
                      (do
                        let spans ← offsetSpans offsets (stop - start)
                        return (offsets.zip spans).map fun (o, s) => (slice b start stop).extract o (o + s)) := by
                  intro offsets spans read
                  cases spans with
                  | error e => simp [read, Bind.bind, Except.bind, Except.map, CutAgree]
                  | ok spans' =>
                    simp only [read, Bind.bind, Except.bind, pure, Except.pure, Except.map, CutAgree]
                    exact bodies_cut b start stop ordered _ _ (offsetSpans_bound _ _ _ read)
                -- With a cap, both check the count first, and then the offsets decide.
                cases limit with
                | none => exact rest _ _ rfl
                | some cap =>
                  simp only
                  split
                  · simp [Except.map, CutAgree]
                  · exact rest _ _ rfl

end Ssz.Native
