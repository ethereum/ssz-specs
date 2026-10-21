import SszNative.Proofs.Validate.Sound

/-! A fixed-size type's sizes and probes refuse a range exactly as deserialization refuses its slice. -/

namespace Ssz.Native

open Ssz

/-- The size checks deserialization makes of a fixed-size type, before reading any byte. -/
theorem deserialize_head (d : Desc) (data : Bytes) (fixed : hasWidth d = true) :
    (composite d = true ∧ data.size ≥ offsetBound →
      (deserialize d data).map (fun _ => ()) = .error (.offsetOverflow data.size)) ∧
    (¬ (composite d = true ∧ data.size ≥ offsetBound) → data.size ≠ fixedWidth d →
      (deserialize d data).map (fun _ => ()) = .error (.scope (fixedWidth d) data.size)) := by
  -- Each fixed-size kind of type is taken in turn.
  cases d with
  | bool | uint | byteVector | bitVector =>
    -- A scalar is never composite, so only its width can be wrong.
    refine ⟨fun h => by simp [composite] at h, fun _ wrong => ?_⟩
    simp only [fixedWidth] at wrong ⊢
    simp [deserialize, wrong, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind,
      Except.map]
  | vector element length =>
    -- A vector of fixed-size elements knows its element width before reading.
    simp only [hasWidth] at fixed
    have sized : element.fixedSize = some (fixedWidth element) := by rw [fixedSize_eq, if_pos fixed]
    -- Too large for offsets, or not the declared width: either way the vector is refused before any element.
    refine ⟨fun h => ?_, fun small wrong => ?_⟩
    · simp [deserialize, vectorSlices, h.2, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind,
        Except.map]
    · simp only [composite, true_and, offsetBound] at small
      simp only [fixedWidth] at wrong ⊢
      simp [deserialize, vectorSlices, small, sized, wrong, throw, throwThe, MonadExceptOf.throw,
        Bind.bind, Except.bind, Except.map]
  | container _ fields | progressiveContainer _ _ fields =>
    -- A struct of fixed-size fields knows its whole width before reading.
    simp only [hasWidth] at fixed
    -- Too large for offsets, or not the declared width: either way the struct is refused before any field.
    refine ⟨fun h => ?_, fun small wrong => ?_⟩
    · simp [deserialize, structSlices, h.2, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind,
        Except.map]
    · simp only [composite, true_and, offsetBound] at small
      simp only [fixedWidth] at wrong ⊢
      simp [deserialize, structSlices, structBudget, small, fieldsFixedSize_eq, fixed, wrong, 
        Bind.bind, Except.bind, Except.map]
  -- Every other type has no fixed size.
  | _ => simp [hasWidth] at fixed

/-- A fixed-size type is refused by its sizes and probes exactly as deserialization refuses it. -/
theorem validateFixed_sound (d : Desc) (fixed : hasWidth d = true) (b : ByteArray) (start stop : Nat)
    (ordered : start ≤ stop) (inside : stop ≤ b.size) :
    validateFixed d (fixedWidth d) b start stop = (deserialize d (slice b start stop)).map (fun _ => ()) := by
  -- The slice has the range's size, so the size checks read alike.
  have size := slice_size b start stop inside
  have head := deserialize_head d (slice b start stop) fixed
  rw [size] at head
  simp only [validateFixed]
  -- An oversized composite is refused first, on both sides.
  by_cases over : composite d = true ∧ stop - start ≥ offsetBound
  · simp only [offsetBound] at over
    simp [over, head.1 over, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  · have over' : ¬ (composite d && decide (stop - start ≥ 2 ^ (8 * bytesPerOffset))) = true := by
      simpa [offsetBound] using over
    simp only [over', Bool.false_eq_true, ↓reduceIte]
    -- At the declared width, the probes stand for every check left.
    by_cases wrong : stop - start = fixedWidth d
    · simp only [wrong, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      have eq : stop = start + fixedWidth d := by omega
      subst eq
      rw [plan_sound d b start fixed (fun c => by simp_all [offsetBound]) inside]
    -- At any other width, both refuse with the same scope error.
    · simp [wrong, head.2 over wrong, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]

end Ssz.Native
