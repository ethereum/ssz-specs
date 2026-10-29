import SszNative.Validate
import Ssz.Proofs.Codec.DecodeFits

/-! Ranges of an encoding read as the slices deserialization cuts out of it. -/

namespace Ssz.Native

open Ssz

/-- The bytes of a range, as deserialization would see them. -/
def slice (b : ByteArray) (start stop : Nat) : Bytes :=
  b.data.extract start stop

/-- A slice inside the array is as long as its range. -/
theorem slice_size (b : ByteArray) (start stop : Nat) (inside : stop ≤ b.size) :
    (slice b start stop).size = stop - start := by
  -- Extraction keeps the whole range when it lies inside the array.
  simp only [slice, Array.size_extract, ByteArray.size_data]
  omega

/-- A position inside a slice reads the array at the shifted position. -/
theorem slice_getElem? (b : ByteArray) (start stop i : Nat) (inside : stop ≤ b.size)
    (within : i < stop - start) : (slice b start stop)[i]? = some (b.get! (start + i)) := by
  -- A position inside the range reads the array at the shifted position.
  have h : start + i < b.data.size := by rw [ByteArray.size_data]; omega
  simp only [slice, Array.getElem?_extract]
  rw [if_pos (by rw [ByteArray.size_data]; omega)]
  cases b with
  | mk data => simp [ByteArray.get!, getElem!_pos data (start + i) h, getElem?_pos data (start + i) h]

/-- A position inside a slice reads the array at the shifted position, with a default. -/
theorem slice_getElem! (b : ByteArray) (start stop i : Nat) (inside : stop ≤ b.size)
    (within : i < stop - start) : (slice b start stop)[i]! = b.get! (start + i) := by
  rw [getElem!_def, slice_getElem? b start stop i inside within]

/-- An offset read from a slice is the offset read in place. -/
theorem readUint_slice (b : ByteArray) (start stop pos : Nat) (inside : stop ≤ b.size)
    (within : pos + 4 ≤ stop - start) :
    readUint (slice b start stop) pos bytesPerOffset = offsetAt b (start + pos) := by
  -- Four little-endian bytes, each inside the range.
  simp only [readUint, offsetAt]
  rw [show pos + 1 + 1 = pos + 2 by omega, show pos + 2 + 1 = pos + 3 by omega,
    slice_getElem? b start stop pos inside (by omega), slice_getElem? b start stop (pos + 1) inside (by omega),
    slice_getElem? b start stop (pos + 2) inside (by omega), slice_getElem? b start stop (pos + 3) inside (by omega)]
  simp only [Option.getD_some, Nat.add_assoc]
  omega

/-- A slice of a slice is the slice of the composed range. -/
theorem slice_extract (b : ByteArray) (start stop x y : Nat) (ordered : start ≤ stop)
    (within : y ≤ stop - start) :
    (slice b start stop).extract x y = slice b (start + x) (start + y) := by
  -- A slice of a slice is the slice of the composed range.
  simp only [slice, Array.extract_extract]
  congr 1
  omega

/-- A test of every byte of a slice is the test of every byte of its range. -/
theorem slice_all (b : ByteArray) (start stop : Nat) (inside : stop ≤ b.size) (p : UInt8 → Bool) :
    (slice b start stop).all p = (List.range (stop - start)).all fun i => p (b.get! (start + i)) := by
  -- Both sides ask the same question of every position of the range.
  apply Bool.eq_iff_iff.mpr
  rw [Array.all_eq_true, List.all_eq_true]
  constructor
  · intro all i member
    have small := List.mem_range.mp member
    have := all i (by rw [slice_size b start stop inside]; exact small)
    rwa [← slice_getElem! b start stop i inside small, getElem!_pos _ _ (by
      rw [slice_size b start stop inside]; exact small)]
  · intro all i small
    rw [slice_size b start stop inside] at small
    have := all i (List.mem_range.mpr small)
    rwa [← slice_getElem! b start stop i inside small, getElem!_pos _ _ (by
      rw [slice_size b start stop inside]; exact small)] at this

/-- An offset table read from a slice is the table read in place. -/
theorem readOffsets_slice (b : ByteArray) (start stop count : Nat) (inside : stop ≤ b.size)
    (within : count * bytesPerOffset ≤ stop - start) :
    readOffsets (slice b start stop) count =
      (List.range count).map fun i => offsetAt b (start + i * bytesPerOffset) := by
  -- Every entry of the table lies inside the range.
  simp only [readOffsets]
  apply List.map_congr_left
  intro i member
  have small := List.mem_range.mp member
  exact readUint_slice b start stop (i * bytesPerOffset) inside (by
    have : (i + 1) * bytesPerOffset ≤ count * bytesPerOffset := Nat.mul_le_mul_right _ small
    simp only [bytesPerOffset] at *
    omega)

/-- Every body a valid offset table opens ends inside the range. -/
theorem offsetSpans_bound : ∀ (offsets spans : List Nat) (scope : Nat),
    offsetSpans offsets scope = .ok spans → ∀ pair ∈ offsets.zip spans, pair.1 + pair.2 ≤ scope
  -- No offsets give no spans.
  | [], _, _, read => by simp [offsetSpans] at read; subst read; simp
  | [start], spans, scope, read => by
    -- The last offset's span runs to the end of the scope.
    simp only [offsetSpans] at read
    split at read
    · cases read
    · cases read
      intro pair member
      simp at member
      subst member
      simp
      omega
  | start :: next :: rest, spans, scope, read => by
    -- Ordered offsets give a span each, and the rest are bounded by induction.
    simp only [offsetSpans] at read
    split at read
    · cases read
    · rename_i ordered
      cases tail : offsetSpans (next :: rest) scope with
      | error e => simp [tail, Bind.bind, Except.bind] at read
      | ok more =>
        simp [tail, Bind.bind, Except.bind, pure, Except.pure] at read
        subst read
        have bound := offsetSpans_bound (next :: rest) more scope tail
        intro pair member
        simp only [List.zip_cons_cons, List.mem_cons] at member
        rcases member with first | later
        · subst first
          -- The first body ends where the next begins, and that one ends inside the range.
          cases more with
          | nil => have := offsetSpans_length tail; simp at this
          | cons span more =>
            have := bound (next, span) (by simp)
            simp at this ⊢
            omega
        · exact bound pair later

end Ssz.Native
