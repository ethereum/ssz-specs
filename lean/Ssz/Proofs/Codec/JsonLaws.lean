import Ssz.Proofs.Codec.JsonHex
import Ssz.Proofs.Codec.RoundTrip
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

/-- The digits of a number read back as that number, however the string was reached. -/
@[simp] theorem readNat_str (n : Nat) : readNat (.str (toString n)) = .ok n := by
  simp [readNat, Nat.toNat?_repr]

@[simp, inherit_doc readNat_str] theorem readNat_decimal (n : Nat) :
    readNat (decimal n) = .ok n := readNat_str n

/-- A boolean document reads back as the boolean it was written from. -/
theorem valueOf_jsonOf_bool {spelling : Spelling} {b : Bool} {document : Json}
    (written : jsonOf .bool spelling (.bool b) = .ok document) :
    valueOf .bool spelling document = .ok (.bool b) := by
  rw [jsonOf] at written
  simp only [Except.ok.injEq] at written
  subst written
  rw [valueOf]

/--
An unsigned integer document reads back as the integer it was written from.

The alias marks a one-byte integer, so the one byte its hex names is the whole value, and
every other spelling writes the digits, which read back at any width.
-/
theorem valueOf_jsonOf_uint {spelling : Spelling} {width n : Nat} {document : Json}
    (fitted : n < 2 ^ (8 * width))
    (written : jsonOf (.uint width) spelling (.uint n) = .ok document) :
    valueOf (.uint width) spelling document = .ok (.uint n) := by
  have wide : ¬ (2 ^ (8 * width) ≤ n) := Nat.not_le.mpr fitted
  rw [jsonOf] at written
  by_cases alias? : (spelling.isByte && width == 1) = true
  · have single : width = 1 := by simpa using ((Bool.and_eq_true ..).mp alias?).2
    have small : n < 256 := by rw [single] at fitted; simpa using fitted
    have byte : (UInt8.ofNat n).toNat = n := by
      simpa [UInt8.toNat_ofNat] using Nat.mod_eq_of_lt small
    simp only [wide, if_false, alias?, if_true, Except.ok.injEq] at written
    subst written
    rw [valueOf, if_pos alias?]
    simp [ofHex_toHex, byte, Bind.bind, Except.bind, pure, Except.pure]
  · rw [if_neg wide, if_neg (by simpa using alias?), Except.ok.injEq] at written
    subst written
    -- The digits have to be a constructor before the reader's own match can reduce.
    simp only [decimal]
    rw [valueOf, if_neg alias?, readNat_str]
    simp [wide, Bind.bind, Except.bind, pure, Except.pure]

/-- A byte array document reads back as the bytes it was written from. -/
theorem valueOf_jsonOf_byteVector {spelling : Spelling} {length : Nat} {data : Bytes}
    {document : Json} (fitted : data.size = length)
    (written : jsonOf (.byteVector length) spelling (.bytes data) = .ok document) :
    valueOf (.byteVector length) spelling document = .ok (.bytes data) := by
  rw [jsonOf] at written
  simp only [Except.ok.injEq] at written
  subst written
  rw [valueOf]
  simp [collectionHex, ofHex_toHex, fitted, Bind.bind, Except.bind, pure, Except.pure]

/-- A byte list document reads back as the bytes it was written from. -/
theorem valueOf_jsonOf_byteList {spelling : Spelling} {limit : Nat} {data : Bytes}
    {document : Json} (fitted : data.size ≤ limit)
    (written : jsonOf (.byteList limit) spelling (.bytes data) = .ok document) :
    valueOf (.byteList limit) spelling document = .ok (.bytes data) := by
  rw [jsonOf] at written
  simp only [Except.ok.injEq] at written
  subst written
  rw [valueOf]
  simp [collectionHex, ofHex_toHex, Nat.not_lt.mpr fitted, Bind.bind, Except.bind,
    pure, Except.pure]

/--
A bitfield document reads back as the bits it was written from.

A bitfield is written as the hex of its own encoding, so the codec is what reads it back.
-/
theorem valueOf_jsonOf_bitVector {spelling : Spelling} {data : Array Bool} {document : Json}
    (legal : (Desc.bitVector data.size).wellFormed = .ok ())
    (fitted : Fits (.bitVector data.size) (.bits data))
    (written : jsonOf (.bitVector data.size) spelling (.bits data) = .ok document) :
    valueOf (.bitVector data.size) spelling document = .ok (.bits data) := by
  have wrote : serialize (.bitVector data.size) (.bits data)
      = .ok (packBits data ((data.size + 7) / 8)) := by simp [serialize]
  have back := roundTrip_of_wellFormed legal fitted wrote
  rw [jsonOf, wrote] at written
  simp only [Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at written
  subst written
  rw [valueOf]
  simp [readBitfield, collectionHex, ofHex_toHex, back, Bind.bind, Except.bind,
    pure, Except.pure]

@[inherit_doc valueOf_jsonOf_bitVector]
theorem valueOf_jsonOf_bitList {spelling : Spelling} {limit : Nat} {data : Array Bool}
    {document : Json} (within : data.size ≤ limit)
    (legal : (Desc.bitList limit).wellFormed = .ok ())
    (fitted : Fits (.bitList limit) (.bits data))
    (written : jsonOf (.bitList limit) spelling (.bits data) = .ok document) :
    valueOf (.bitList limit) spelling document = .ok (.bits data) := by
  have wrote : serialize (.bitList limit) (.bits data) = .ok (packBitsDelimited data) := by
    simp [serialize, within]
  have back := roundTrip_of_wellFormed legal fitted wrote
  rw [jsonOf, wrote] at written
  simp only [Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at written
  subst written
  rw [valueOf]
  simp [readBitfield, collectionHex, ofHex_toHex, back, Bind.bind, Except.bind,
    pure, Except.pure]

@[inherit_doc valueOf_jsonOf_bitVector]
theorem valueOf_jsonOf_progressiveBitList {spelling : Spelling} {limit : Option Nat}
    {data : Array Bool} {document : Json}
    (within : withinBound limit data.size = true)
    (legal : (Desc.progressiveBitList limit).wellFormed = .ok ())
    (fitted : Fits (.progressiveBitList limit) (.bits data))
    (written : jsonOf (.progressiveBitList limit) spelling (.bits data) = .ok document) :
    valueOf (.progressiveBitList limit) spelling document = .ok (.bits data) := by
  have wrote : serialize (.progressiveBitList limit) (.bits data)
      = .ok (packBitsDelimited data) := by
    simp [serialize, boundCheck_of_withinBound limit _ within, Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  have back := roundTrip_of_wellFormed legal fitted wrote
  rw [jsonOf, wrote] at written
  simp only [Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at written
  subst written
  rw [valueOf]
  simp [readBitfield, collectionHex, ofHex_toHex, back, Bind.bind, Except.bind,
    pure, Except.pure]

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
