import Ssz.Proofs.Codec.JsonHex
import Std.Data.TreeMap.Raw.WF
import Std.Data.TreeMap.Raw.Lemmas
import Std.Data.String.ToNat

/-! Reading back what the JSON mapping writes, and what the mapping does not pin down. -/

namespace Ssz

open Lean Std

/--
A name written into an object is read back from it, when no name was written twice.

A struct's field names are distinct by declaration, which is what makes this apply to one.
-/
theorem getObjVal?_mkObj {pairs : List (String × Json)} {name : String} {value : Json}
    (distinct : pairs.Pairwise fun a b => a.1 ≠ b.1) (member : (name, value) ∈ pairs) :
    (Json.mkObj pairs).getObjVal? name = .ok value := by
  -- Distinct names stay distinct under the order an object is built with.
  have keys : pairs.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) := by
    refine distinct.imp ?_
    intro a b different equal
    exact different (compare_eq_iff_eq.mp equal)
  have read := Std.TreeMap.Raw.getElem?_ofList_of_mem (cmp := compare) compare_self keys member
  simp only [Json.mkObj, Json.getObjVal?, Std.TreeMap.Raw.get?_eq_getElem?, read]
  rfl

/--
Every name an object carries is one of the names it was written from.

A written struct therefore never trips the undeclared-field refusal.
-/
theorem objectNames_mkObj {pairs : List (String × Json)} {name : String}
    (member : name ∈ objectNames (Json.mkObj pairs)) : name ∈ pairs.map Prod.fst := by
  have wf : (Std.TreeMap.Raw.ofList pairs (cmp := compare)).WF := Std.TreeMap.Raw.WF.ofList
  simp only [objectNames, Json.mkObj] at member
  rw [Std.TreeMap.Raw.map_fst_toList_eq_keys] at member
  simpa using Std.TreeMap.Raw.mem_ofList.mp ((Std.TreeMap.Raw.mem_keys wf).mp member)

/-- The digits of a number read back as that number. -/
@[simp] theorem readNat_decimal (n : Nat) : readNat (decimal n) = .ok n := by
  simp [readNat, decimal, Nat.toNat?_repr]

/--
The mapping is not canonical: two documents give one value.

A hex digit is read in either letter case, so a byte array has as many documents as its
bytes have spellings.

The byte encoding pins one string per value, and nothing here does the same for documents.
-/
theorem valueOf_not_canonical :
    ∃ (shape : Desc) (spelling : Spelling) (left right : Json) (value : Value),
      left ≠ right ∧ valueOf shape spelling left = .ok value
        ∧ valueOf shape spelling right = .ok value := by
  have lower : ofHex "0x0a" = .ok #[10] := by rfl
  have upper : ofHex "0x0A" = .ok #[10] := by rfl
  refine ⟨.byteVector 1, .opaque, .str "0x0a", .str "0x0A", .bytes #[10], by simp, ?_, ?_⟩ <;>
    simp [valueOf, collectionHex, lower, upper, Bind.bind, Except.bind, pure, Except.pure]

end Ssz
