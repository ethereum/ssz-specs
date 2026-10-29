import SszNative.Proofs.Driver.Root.Sequence

/-!
What decoding a list gives its root: the count of elements, each element's range, and how the count is read.
-/

namespace Ssz.Native.Driver

open Ssz

/-- What a list's decoding gives its root, read on the encoding: the count, each element's range, and the bounds. -/
theorem list_decoded {element : Desc} {lim : Option Nat} {b : ByteArray} {start stop : Nat} {slices : List Bytes}
    {values : List Value} (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (read : listSlices element lim (slice b start stop) = .ok slices)
    (decoded : deserializeEach element slices = .ok values) :
    elementCount element b start stop = slices.length ∧
    (∀ i < slices.length, start ≤ (elemRange element b start stop slices.length i).1 ∧
      (elemRange element b start stop slices.length i).1 ≤ (elemRange element b start stop slices.length i).2 ∧
      (elemRange element b start stop slices.length i).2 ≤ stop ∧
      ∃ v, deserialize element (slice b (elemRange element b start stop slices.length i).1
        (elemRange element b start stop slices.length i).2) = .ok v) ∧
    (elementRanges element b start stop slices.length).length = slices.length ∧
    (∀ l, lim = some l → slices.length ≤ l) ∧
    (hasWidth element = true → slices.length * fixedWidth element = stop - start ∧
      (fixedWidth element = 0 → slices.length = 0)) ∧
    (hasWidth element = false → (stop - start = 0 ∧ slices.length = 0) ∨
      (4 ≤ stop - start ∧ slices.length = offsetAt b start / 4 ∧ 4 * slices.length ≤ stop - start)) := by
  have size := slice_size b start stop inside
  obtain ⟨capped, fixedFacts, varFacts⟩ := listSlices_facts read
  have agree := listRanges_cut element lim b start stop ordered inside
  rw [read] at agree
  cases ranged : listRanges element lim b start stop with
  | error e => simp [ranged, Except.map, CutAgree] at agree
  | ok r =>
    simp only [ranged, Except.map, CutAgree] at agree
    obtain ⟨sliced, within⟩ := agree
    obtain ⟨counted, rangesEq⟩ := RootProof.elementRanges_list element lim b start stop r ranged
    have len : r.toList.length = slices.length := by rw [sliced, List.length_map]
    rw [len] at counted
    rw [counted] at rangesEq
    subst sliced
    refine ⟨counted, ranges_of_cut rangesEq len within decoded, by rw [rangesEq, len], capped, fun fx => ?_,
      fun fx => ?_⟩
    · have := fixedFacts (fixedWidth element) (by rw [fixedSize_eq, if_pos fx])
      rw [size] at this; exact this
    · have := varFacts (by rw [fixedSize_eq, if_neg (by simp [fx])])
      rw [size] at this
      rcases this with h | ⟨four, cnt, table⟩
      · exact .inl h
      · refine .inr ⟨four, ?_, table⟩
        rw [cnt, readUint_slice b start stop 0 inside (by omega), Nat.add_zero]

end Ssz.Native.Driver
