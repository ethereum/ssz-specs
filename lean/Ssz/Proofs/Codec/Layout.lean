import Ssz.Codec.Layout
import Ssz.Proofs.Merkle.Tree

/-! Laws of the layout that places a progressive container's fields around its gaps. -/

namespace Ssz

/-- A successful layout preserves every field in order and has one slot per position. -/
private theorem placeSlots_preserves {active : List Bool} {fields : List (Desc × Value)}
    {slots : List (Option (Desc × Value))} (placed : placeSlots active fields = .ok slots) :
    slots.filterMap id = fields ∧ slots.length = active.length := by
  induction active generalizing fields slots with
  | nil =>
    -- With no positions left, success requires no fields left either.
    cases fields <;> simp [placeSlots] at placed
    subst slots
    simp
  | cons bit active ih =>
    cases bit with
    | false =>
      -- Removing a gap keeps the field sequence and shortens the layout by one.
      cases tail : placeSlots active fields with
      | error fault => simp [placeSlots, tail, Bind.bind, Except.bind] at placed
      | ok rest =>
        simp [placeSlots, tail, Bind.bind, Except.bind, pure, Except.pure] at placed
        subst slots
        simpa using ih tail
    | true =>
      -- An occupied position keeps the first field and delegates the remaining positions.
      cases fields with
      | nil => simp [placeSlots] at placed
      | cons field fields =>
        cases tail : placeSlots active fields with
        | error fault => simp [placeSlots, tail, Bind.bind, Except.bind] at placed
        | ok rest =>
          simp [placeSlots, tail, Bind.bind, Except.bind, pure, Except.pure] at placed
          subst slots
          obtain ⟨ordered, sized⟩ := ih tail
          simp [ordered, sized]

/-- Removing gaps from a successful layout recovers the declared fields in order. -/
theorem placeSlots_fields {active : List Bool} {fields : List (Desc × Value)}
    {slots : List (Option (Desc × Value))} (placed : placeSlots active fields = .ok slots) :
    slots.filterMap id = fields :=
  -- Field preservation follows independently of the number of gaps.
  (placeSlots_preserves placed).1

/-- A successful layout has exactly one slot for every declared position. -/
theorem placeSlots_length {active : List Bool} {fields : List (Desc × Value)}
    {slots : List (Option (Desc × Value))} (placed : placeSlots active fields = .ok slots) :
    slots.length = active.length :=
  -- Gaps occupy positions just as present fields do.
  (placeSlots_preserves placed).2

end Ssz
