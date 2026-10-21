import SszNative.Proofs.Root.Variable.Union

/-! Roots of types rooted as columns, as one record of its own. -/

namespace Ssz.Native.RootProof

open Ssz Ssz.Native

variable (facts : Facts)

/-- A type rooted as columns is rooted as one record. -/
theorem rootOf_plain (d : Desc) (isPlain : plain d = true) (b : ByteArray) (start stop : Nat) :
    rootOf d b start stop = rootsOf d b start (fixedWidth d) 1 := by
  -- Every plain kind of type takes the columns path for a single record.
  cases d <;> rw [rootOf] <;> simp_all [plain]

include facts in
/-- A type rooted as columns has the specification's root. -/
theorem plain_root (d : Desc) (isPlain : plain d = true) (sound : d.wellFormed = .ok ()) (b : ByteArray)
    (start stop : Nat) (v : Value) (ordered : start ≤ stop) (inside : stop ≤ b.size) (small : Small b)
    (read : deserialize d (slice b start stop) = .ok v) :
    Ssz.hashTreeRoot d v = .ok (rootOf d b start stop).data := by
  -- A plain type has a fixed size.
  have fixed := hasWidth_of_plain d isPlain
  have size := slice_size b start stop inside
  -- A value of a fixed-size type decodes only from exactly its width.
  have exact : stop - start = fixedWidth d := by
    have head := deserialize_head d (slice b start stop) fixed
    by_cases huge : composite d = true ∧ (slice b start stop).size ≥ offsetBound
    · have := head.1 huge; simp [read, Except.map] at this
    · by_cases wrong : (slice b start stop).size ≠ fixedWidth d
      · have := head.2 huge wrong; simp [read, Except.map] at this
      · omega
  -- The value is one record, starting where the range starts.
  have records : RecordsDecode d b start (fixedWidth d) 1 := by
    intro i one
    have : i = 0 := by omega
    subst this
    simp only [Nat.mul_zero, Nat.add_zero]
    exact ⟨by omega, v, by rw [show start + fixedWidth d = stop by omega]; exact read⟩
  -- The columns path roots that record to the specification's root.
  obtain ⟨sized, rooted⟩ := facts.rootsOf d isPlain sound b start (fixedWidth d) 1 small (by omega) rfl records
  have root := rooted 0 (by omega) v (by
    simp only [Nat.mul_zero, Nat.add_zero]; rw [show start + fixedWidth d = stop by omega]; exact read)
  -- A single record's roots are its root alone.
  rw [rootOf_plain d isPlain, root]
  simp only [Nat.mul_zero, Nat.zero_add, ByteArray.data_extract]
  rw [Array.extract_eq_self_of_le (by rw [ByteArray.size_data, sized]; omega)]

end Ssz.Native.RootProof
