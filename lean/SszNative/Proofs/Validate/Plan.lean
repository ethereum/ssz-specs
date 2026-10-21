import SszNative.Proofs.Validate.Struct

/-! The probes of a fixed-size type refusing a value of its width exactly as deserialization does. -/

namespace Ssz.Native

open Ssz

/-- The allocation-free width functions agree with the type's fixed size. -/
theorem fixedSize_eq (d : Desc) : d.fixedSize = if hasWidth d then some (fixedWidth d) else none := by
  -- Types and their field lists are handled together, by mutual induction.
  induction d using Desc.rec
    (motive_2 := fun fields =>
      Desc.fieldsFixedSize fields = if allHaveWidth fields then some (fieldsWidth fields) else none) with
  -- Scalars and byte or bit sequences answer directly.
  | bool | uint | byteVector | bitVector | byteList | bitList | progressiveBitList =>
    simp [Desc.fixedSize, hasWidth, fixedWidth]
  -- A vector has a fixed size exactly when its element does.
  | vector element length ih =>
    simp only [Desc.fixedSize, hasWidth, fixedWidth, ih]
    split <;> simp_all
  -- Counted sequences and unions never have a fixed size.
  | list | progressiveList | compatibleUnion => simp [Desc.fixedSize, hasWidth]
  -- A struct's fixed size is its fields'.
  | container _ fields ih | progressiveContainer _ _ fields ih => rw [Desc.fixedSize, ih]; rfl
  | nil => simp [Desc.fieldsFixedSize, allHaveWidth, fieldsWidth]
  -- A field list is fixed when its head and its tail are.
  | cons field fields ihHead ihTail =>
    simp only [Desc.fieldsFixedSize, allHaveWidth, fieldsWidth, ihHead, ihTail]
    by_cases h : hasWidth field <;> by_cases t : allHaveWidth fields <;> simp [h, t]

/-- The allocation-free widths agree with a field list's fixed size. -/
theorem fieldsFixedSize_eq (fields : List Desc) :
    Desc.fieldsFixedSize fields = if allHaveWidth fields then some (fieldsWidth fields) else none := by
  -- A field list is fixed when its head and its tail are, by induction on the list.
  induction fields with
  | nil => simp [Desc.fieldsFixedSize, allHaveWidth, fieldsWidth]
  | cons field fields ih =>
    simp only [Desc.fieldsFixedSize, allHaveWidth, fieldsWidth, ih, fixedSize_eq field]
    by_cases h : hasWidth field <;> by_cases t : allHaveWidth fields <;> simp [h, t]

/-- A type with a fixed size has the allocation-free width of that size. -/
theorem fixedWidth_of (d : Desc) (w : Nat) (fixed : d.fixedSize = some w) : hasWidth d ∧ fixedWidth d = w := by
  -- Only the fixed branch gives a size.
  rw [fixedSize_eq] at fixed
  split at fixed <;> simp_all

/-- Two lists of probes run one after the other. -/
theorem checkProbes_append (b : ByteArray) (start : Nat) (p q : List Probe) :
    checkProbes b start (p ++ q) = (do checkProbes b start p; checkProbes b start q) := by
  -- Running the first list's probes, then the second's, is running them joined.
  induction p with
  | nil => simp [checkProbes, Bind.bind, Except.bind]
  | cons probe rest ih =>
    simp only [List.cons_append, checkProbes, ih, Bind.bind, Except.bind]
    cases probe.check b start <;> rfl

/-- Shifted probes are the probes of a later start. -/
theorem checkProbes_shift (b : ByteArray) (start offset : Nat) (p : List Probe) :
    checkProbes b start (shiftAll offset p) = checkProbes b (start + offset) p := by
  -- Each probe reads its byte at its own offset from the start.
  induction p with
  | nil => rfl
  | cons probe rest ih =>
    simp only [shiftAll, checkProbes, ih]
    cases probe <;> simp [Probe.shift, Probe.check, Nat.add_assoc]

/-- Shifting no probes leaves none. -/
theorem shiftAll_nil (offset : Nat) : shiftAll offset [] = [] := rfl

/-- Repeating no probes leaves none. -/
theorem repeatProbes_nil (width index count : Nat) : repeatProbes [] width index count = [] := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih => simp [repeatProbes, shiftAll_nil, ih]

/-- A vector's probes are its element's, repeated once per element. -/
theorem plan_vector (element : Desc) (length : Nat) :
    plan (.vector element length) = repeatProbes (plan element) (fixedWidth element) 0 length := by
  -- Empty element probes repeat to nothing.
  simp only [plan]
  split
  · rename_i h; rw [h, repeatProbes_nil]
  · rfl

/-- A struct's probes are its first field's, then the rest's. -/
theorem fieldsPlan_cons (field : Desc) (fields : List Desc) (offset : Nat) :
    fieldsPlan (field :: fields) offset =
      shiftAll offset (plan field) ++ fieldsPlan fields (offset + fixedWidth field) := by
  -- A field without probes adds none.
  simp only [fieldsPlan]
  split
  · rename_i h; rw [h]; rfl
  · rfl

/-- Deserializing elements in order refuses at the first element refused. -/
theorem deserializeEach_cons (element : Desc) (x : Bytes) (xs : List Bytes) :
    (deserializeEach element (x :: xs)).map (fun _ => ()) =
      (do (deserialize element x).map (fun _ => ()); (deserializeEach element xs).map (fun _ => ())) := by
  -- The first element's refusal stops the run, and otherwise the rest decide.
  rw [deserializeEach]
  simp only [Bind.bind, Except.bind, Except.map, pure, Except.pure]
  cases deserialize element x <;> simp only
  cases deserializeEach element xs <;> rfl

/-- Deserializing fields in order refuses at the first field refused. -/
theorem deserializeFields_cons (field : Desc) (fields : List Desc) (x : Bytes) (xs : List Bytes) :
    (deserializeFields (field :: fields) (x :: xs)).map (fun _ => ()) =
      (do (deserialize field x).map (fun _ => ()); (deserializeFields fields xs).map (fun _ => ())) := by
  -- The first field's refusal stops the run, and otherwise the rest decide.
  rw [deserializeFields]
  simp only [Bind.bind, Except.bind, Except.map, pure, Except.pure]
  cases deserialize field x <;> simp only
  cases deserializeFields fields xs <;> rfl

/-- The slices of fields that are all fixed, read in place from a position. -/
def fixedSlots (data : Bytes) : List Desc → Nat → List Slot
  | [], _ => []
  | field :: fields, position =>
    .inline (data.extract position (position + fixedWidth field)) ::
      fixedSlots data fields (position + fixedWidth field)

/-- Fixed fields are all read in place, with no offset among them. -/
theorem readSlots_fixed (data : Bytes) :
    ∀ (fields : List Desc) (position : Nat), allHaveWidth fields = true →
      position + fieldsWidth fields ≤ data.size →
      readSlots fields data position = .ok (fixedSlots data fields position, position + fieldsWidth fields)
  -- No fields read nothing.
  | [], position, _, _ => by simp [readSlots, fixedSlots, fieldsWidth]
  | field :: fields, position, all, fits => by
    -- The first field is fixed, so it fits in place, and the rest follow it.
    simp only [allHaveWidth, Bool.and_eq_true] at all
    have sized : field.fixedSize = some (fixedWidth field) := by rw [fixedSize_eq, if_pos all.1]
    simp only [fieldsWidth] at fits
    rw [readSlots, sized]
    simp only [show ¬ position + fixedWidth field > data.size by omega, ↓reduceIte,
      readSlots_fixed data fields (position + fixedWidth field) all.2 (by omega), Bind.bind, Except.bind, pure,
      Except.pure, fixedSlots, Nat.add_assoc, fieldsWidth]

/-- Fields read in place name no bodies. -/
theorem bodyStarts_fixedSlots (data : Bytes) :
    ∀ (fields : List Desc) (position : Nat), bodyStarts (fixedSlots data fields position) = []
  -- In-place slots never name a body.
  | [], _ => rfl
  | _ :: fields, position => by simp [fixedSlots, bodyStarts, bodyStarts_fixedSlots data fields]

end Ssz.Native
