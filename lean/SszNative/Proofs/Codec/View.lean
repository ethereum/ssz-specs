import SszNative.Codec
import SszNative.Proofs.Validate.Seq
import SszNative.Proofs.Validate.Struct
import EthLib.Consensus.Proofs.Ssz.Codec.StructOrder

/-!
The ranges a composite's encoding is cut into are where deserialization cuts the slices it decodes the parts from.

A range of an encoding stands for the slice deserialization would cut out of it.
-/

namespace EthLib.Consensus.Ssz.Native

open EthLib.Consensus.Ssz

/-- The slices a list of ranges cuts out of an encoding. -/
def slicesOf (b : ByteArray) (ranges : List (Nat × Nat)) : List Bytes :=
  ranges.map fun r => slice b r.1 r.2

/-- A sequence decodes its elements from the slices its ranges cut, once the two cutting steps agree. -/
theorem sequence_of_cut (element : Desc) (b : ByteArray) (start stop : Nat)
    (ranges : Except Err (List (Nat × Nat))) (slices : Except Err (List Bytes))
    (cut : CutAgree b start stop ranges slices) :
    (do let parts ← slices; return Value.seq (← deserializeEach element parts)) =
      (do let found ← ranges; return Value.seq (← deserializeEach element (slicesOf b found))) := by
  -- A refusal while cutting is the same refusal on both sides, and otherwise the slices are the same.
  cases ranges <;> cases slices <;> simp only [CutAgree] at cut
  · subst cut; rfl
  · obtain ⟨rfl, -⟩ := cut
    rfl

/-- A vector decodes its elements from the slices its ranges cut, or both refuse alike. -/
theorem view_vector (element : Desc) (length : Nat) (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop)
    (inside : stop ≤ b.size) :
    deserialize (.vector element length) (slice b start stop) =
      (do
        let ranges ← viewRanges (.vector element length) b start stop
        return Value.seq (← deserializeEach element (slicesOf b ranges))) := by
  rw [deserialize, viewRanges]
  exact sequence_of_cut element b start stop _ _ (vectorRanges_cut element length b start stop ordered inside)

/-- A list decodes its elements from the slices its ranges cut, or both refuse alike. -/
theorem view_list (element : Desc) (limit : Nat) (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop)
    (inside : stop ≤ b.size) :
    deserialize (.list element limit) (slice b start stop) =
      (do
        let ranges ← viewRanges (.list element limit) b start stop
        return Value.seq (← deserializeEach element (slicesOf b ranges))) := by
  rw [deserialize, viewRanges]
  exact sequence_of_cut element b start stop _ _ (listRanges_cut element (some limit) b start stop ordered inside)

/-- A progressive list decodes its elements from the slices its ranges cut, or both refuse alike. -/
theorem view_progressiveList (element : Desc) (limit : Option Nat) (b : ByteArray) (start stop : Nat)
    (ordered : start ≤ stop) (inside : stop ≤ b.size) :
    deserialize (.progressiveList element limit) (slice b start stop) =
      (do
        let ranges ← viewRanges (.progressiveList element limit) b start stop
        return Value.seq (← deserializeEach element (slicesOf b ranges))) := by
  rw [deserialize, viewRanges]
  exact sequence_of_cut element b start stop _ _ (listRanges_cut element limit b start stop ordered inside)

/--
A struct's fields decode from the slices its ranges cut.

Deserialization checks fixed fields before it trusts any offset, so a struct broken twice may be refused for another
reason; what is accepted, and the value it holds, are the same.
-/
theorem view_struct (fields : List Desc) (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop)
    (inside : stop ≤ b.size) (values : List Value) :
    deserializeStruct fields (slice b start stop) = .ok values ↔
      (do
        let ranges ← fieldRanges fields b start stop
        deserializeFields fields (slicesOf b ranges)) = .ok values := by
  -- The ranges and the slices agree: the same refusal, or the same parts.
  have cut := fieldRanges_cut fields b start stop ordered inside
  constructor
  · intro read
    obtain ⟨slices, sliced, decoded⟩ := deserializeStruct_ok read
    rw [sliced] at cut
    cases found : fieldRanges fields b start stop with
    | error e => rw [found] at cut; cases cut
    | ok ranges =>
      rw [found] at cut
      obtain ⟨rfl, -⟩ := cut
      exact decoded
  · intro read
    obtain ⟨ranges, found, decoded⟩ := checksPassed read
    rw [found] at cut
    cases sliced : structSlices fields (slice b start stop) with
    | error e => rw [sliced] at cut; cases cut
    | ok slices =>
      rw [sliced] at cut
      obtain ⟨rfl, -⟩ := cut
      exact deserializeStruct_of sliced decoded

/-- A struct wrapped as a sequence holds the values its fields decode to from the slices its ranges cut. -/
theorem view_struct_seq (fields : List Desc) (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop)
    (inside : stop ≤ b.size) (value : Value) :
    (do let values ← deserializeStruct fields (slice b start stop); return Value.seq values) = .ok value ↔
      (do
        let ranges ← fieldRanges fields b start stop
        return Value.seq (← deserializeFields fields (slicesOf b ranges))) = .ok value := by
  -- Both sides wrap the same field values, once those agree.
  have same := view_struct fields b start stop ordered inside
  constructor
  · intro read
    obtain ⟨values, decoded, wrapped⟩ := checksPassed read
    cases wrapped
    obtain ⟨ranges, found, rest⟩ := checksPassed ((same values).mp decoded)
    simp [found, rest, Bind.bind, Except.bind, pure, Except.pure]
  · intro read
    obtain ⟨ranges, found, rest⟩ := checksPassed read
    obtain ⟨values, decoded, wrapped⟩ := checksPassed rest
    cases wrapped
    have := (same values).mpr (by simp [found, decoded, Bind.bind, Except.bind])
    simp [this, Bind.bind, Except.bind, pure, Except.pure]

/-- A container holds the values its fields decode to from the slices its ranges cut, and nothing else. -/
theorem view_container (names : List String) (fields : List Desc) (b : ByteArray) (start stop : Nat)
    (ordered : start ≤ stop) (inside : stop ≤ b.size) (value : Value) :
    deserialize (.container names fields) (slice b start stop) = .ok value ↔
      (do
        let ranges ← viewRanges (.container names fields) b start stop
        return Value.seq (← deserializeFields fields (slicesOf b ranges))) = .ok value := by
  rw [deserialize, viewRanges]
  exact view_struct_seq fields b start stop ordered inside value

/-- A progressive container holds the values its fields decode to from the slices its ranges cut, and nothing else. -/
theorem view_progressiveContainer (active : List Bool) (names : List String) (fields : List Desc) (b : ByteArray)
    (start stop : Nat) (ordered : start ≤ stop) (inside : stop ≤ b.size) (value : Value) :
    deserialize (.progressiveContainer active names fields) (slice b start stop) = .ok value ↔
      (do
        let ranges ← viewRanges (.progressiveContainer active names fields) b start stop
        return Value.seq (← deserializeFields fields (slicesOf b ranges))) = .ok value := by
  -- A gap holds no field, so the struct reads exactly as a container of its fields does.
  rw [deserialize, viewRanges]
  exact view_struct_seq fields b start stop ordered inside value

/-- An empty range holds no selector, and both readings refuse it so. -/
theorem view_union_empty (selectors : List Nat) (options : List Desc) (b : ByteArray) (start stop : Nat)
    (empty : stop ≤ start) (inside : stop ≤ b.size) :
    viewRanges (.compatibleUnion selectors options) b start stop = .error .noSelector ∧
      deserialize (.compatibleUnion selectors options) (slice b start stop) = .error .noSelector := by
  have size := slice_size b start stop inside
  constructor
  · simp [viewRanges, show stop - start = 0 by omega]
  · simp [deserialize, size, show stop - start = 0 by omega, throw, throwThe, MonadExceptOf.throw, Bind.bind,
      Except.bind]

/--
A union's ranges are its selector byte and the rest.

The union holds what the option its selector names decodes to from the rest.
-/
theorem view_union (selectors : List Nat) (options : List Desc) (b : ByteArray) (start stop : Nat)
    (nonempty : start < stop) (inside : stop ≤ b.size) :
    viewRanges (.compatibleUnion selectors options) b start stop = .ok [(start, start + 1), (start + 1, stop)] ∧
      slice b start (start + 1) = #[b.get! start] ∧
      deserialize (.compatibleUnion selectors options) (slice b start stop) =
        deserializeOption selectors options (b.get! start).toNat (slice b (start + 1) stop) := by
  have size := slice_size b start stop inside
  refine ⟨by simp [viewRanges, show ¬ stop - start < 1 by omega], ?_, ?_⟩
  -- The selector's range holds the one byte at the start.
  · apply Array.ext
    · rw [slice_size b start (start + 1) (by omega)]; simp
    · intro i small _
      rw [slice_size b start (start + 1) (by omega)] at small
      obtain rfl : i = 0 := by omega
      have one := slice_getElem? b start (start + 1) 0 (by omega) (by omega)
      rw [Array.getElem?_eq_getElem] at one
      simpa using one
  -- The rest of the slice is the slice of the rest of the range.
  · have rest : (slice b start stop).extract 1 (slice b start stop).size = slice b (start + 1) stop := by
      rw [size, slice_extract b start stop 1 (stop - start) (by omega) (Nat.le_refl _)]
      congr 1
      omega
    simp only [deserialize, size, show ¬ stop - start < 1 by omega, ↓reduceIte]
    rw [slice_getElem! b start stop 0 inside (by omega), Nat.add_zero, ← size, rest]

end EthLib.Consensus.Ssz.Native
