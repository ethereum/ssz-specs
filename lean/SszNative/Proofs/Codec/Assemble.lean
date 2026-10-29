import SszNative.Codec
import Ssz.Proofs.Codec.RoundTrip
import Ssz.Proofs.Codec.RoundTripComposite
import Ssz.Proofs.Codec.RoundTripScalar

/-!
Laying out the encodings of a value's parts gives the value's encoding.

Each theorem takes a value whose parts serialize to some encodings.
Assembling those encodings is then serializing the value, refusals included.
A fixed-size part must have its type's width, which serialization guarantees for every type of the specification.
-/

namespace Ssz.Native

open Ssz

/-- Parts each of their type's width pass the check, so nothing is refused before the layout. -/
theorem checkParts_ok : ∀ (fields : List Desc) (parts : List Bytes),
    (∀ pair ∈ fields.zip parts, ∀ width, pair.1.fixedSize = some width → pair.2.size = width) →
    checkParts fields (parts.map ByteArray.mk) = .ok ()
  | [], _, _ => by simp [checkParts]
  | _ :: _, [], _ => by simp [checkParts]
  | field :: fields, part :: parts, widths => by
    -- The first part has its field's width, and the rest pass by induction.
    have head : partFits field ⟨part⟩ = .ok () := by
      unfold partFits
      split
      · rename_i width fixed
        simp [ByteArray.size, widths (field, part) (by simp) width fixed]
      · rfl
    simp only [List.map_cons, checkParts, head, Bind.bind, Except.bind]
    exact checkParts_ok fields parts (fun pair member => widths pair (List.mem_cons_of_mem _ member))

/-- Parts each of their type's width are laid out as serialization lays them out. -/
theorem layOut_ok (fields : List Desc) (parts : List Bytes)
    (widths : ∀ pair ∈ fields.zip parts, ∀ width, pair.1.fixedSize = some width → pair.2.size = width) :
    layOut fields (parts.map ByteArray.mk) = (Ssz.assemble (fields.map Desc.isFixed) parts).map ByteArray.mk := by
  simp only [layOut, checkParts_ok fields parts widths, Bind.bind, Except.bind, List.map_map]
  -- Wrapping each part and unwrapping it again gives the part back.
  have same : (ByteArray.data ∘ ByteArray.mk) = id := rfl
  rw [same, List.map_id]
  cases Ssz.assemble (fields.map Desc.isFixed) parts <;> rfl

/-- The elements of a sequence, each encoded, have the element type's width when it has one. -/
theorem sequence_widths (element : Desc) (sound : element.wellFormed = .ok ()) (values : List Value)
    (parts : List Bytes) (wrote : serializeEach element values = .ok parts) :
    ∀ pair ∈ (List.replicate parts.length element).zip parts, ∀ width, pair.1.fixedSize = some width →
      pair.2.size = width := by
  intro pair member width fixed
  obtain ⟨first, second⟩ := pair
  obtain ⟨isElement, isPart⟩ := List.of_mem_zip member
  obtain ⟨-, rfl⟩ := List.mem_replicate.mp isElement
  -- Every element's encoding has the element type's width.
  exact serializeEach_widths first values parts width fixed wrote
    (fun _ _ bytes written => serialize_size_of_encoding sound fixed written) second isPart

/-- A sequence of parts all of one type is laid out as serialization lays out the sequence. -/
theorem layOut_sequence (element : Desc) (sound : element.wellFormed = .ok ()) (values : List Value)
    (parts : List Bytes) (wrote : serializeEach element values = .ok parts) :
    layOut (List.replicate (parts.map ByteArray.mk).length element) (parts.map ByteArray.mk) =
      (serializeSequence element values).map ByteArray.mk := by
  rw [List.length_map, layOut_ok _ parts (sequence_widths element sound values parts wrote)]
  simp only [serializeSequence, wrote, Bind.bind, Except.bind, List.map_replicate, List.map_const']

/-- Assembling the encodings of a vector's elements is serializing the vector. -/
theorem assemble_vector (element : Desc) (length : Nat) (sound : element.wellFormed = .ok ()) (values : List Value)
    (parts : List Bytes) (wrote : serializeEach element values = .ok parts) :
    assemble (.vector element length) (parts.map ByteArray.mk) =
      (serialize (.vector element length) (.seq values)).map ByteArray.mk := by
  have count := serializeEach_length element values parts wrote
  simp only [assemble, serialize, List.length_map, count]
  -- A wrong count is refused alike, and otherwise the layouts agree.
  split
  · rename_i wrong
    simp only [bne_iff_ne, ne_eq] at wrong
    simp [wrong, Except.map]
  · rename_i right
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at right
    rw [← count, ← List.length_map (f := ByteArray.mk), layOut_sequence element sound values parts wrote]
    simp [right, count]

/-- Assembling the encodings of a list's elements is serializing the list. -/
theorem assemble_list (element : Desc) (limit : Nat) (sound : element.wellFormed = .ok ()) (values : List Value)
    (parts : List Bytes) (wrote : serializeEach element values = .ok parts) :
    assemble (.list element limit) (parts.map ByteArray.mk) =
      (serialize (.list element limit) (.seq values)).map ByteArray.mk := by
  have count := serializeEach_length element values parts wrote
  simp only [assemble, serialize, List.length_map, count]
  -- A count over the limit is refused alike, and otherwise the layouts agree.
  split
  · rename_i over
    simp [Nat.not_le.mpr over, Except.map]
  · rename_i within
    rw [← count, ← List.length_map (f := ByteArray.mk), layOut_sequence element sound values parts wrote]
    simp [Nat.le_of_not_lt within, count]

/-- Assembling the encodings of a progressive list's elements is serializing the list. -/
theorem assemble_progressiveList (element : Desc) (limit : Option Nat) (sound : element.wellFormed = .ok ())
    (values : List Value) (parts : List Bytes) (wrote : serializeEach element values = .ok parts) :
    assemble (.progressiveList element limit) (parts.map ByteArray.mk) =
      (serialize (.progressiveList element limit) (.seq values)).map ByteArray.mk := by
  have count := serializeEach_length element values parts wrote
  simp only [assemble, serialize]
  -- The bound is checked alike, and then the layouts agree.
  cases bound : boundCheck limit values.length with
  | error e =>
    rw [List.length_map, count, bound]
    rfl
  | ok u =>
    rw [layOut_sequence element sound values parts wrote, List.length_map, count, bound]
    rfl

/-- The fields of a struct, each encoded, have their own type's width when it has one. -/
theorem struct_widths (fields : List Desc) (sound : ∀ field ∈ fields, field.wellFormed = .ok ())
    (values : List Value) (parts : List Bytes) (wrote : serializeFields fields values = .ok parts) :
    ∀ pair ∈ fields.zip parts, ∀ width, pair.1.fixedSize = some width → pair.2.size = width :=
  serializeFields_widths fields values parts wrote (fun pair member _ _ fixed written =>
    serialize_size_of_encoding (sound pair.1 (List.of_mem_zip member).1) fixed written)

/-- A struct's parts are laid out as serialization lays out the struct. -/
theorem assemble_struct (fields : List Desc) (sound : ∀ field ∈ fields, field.wellFormed = .ok ())
    (values : List Value) (parts : List Bytes) (wrote : serializeFields fields values = .ok parts) :
    (if (parts.map ByteArray.mk).length != fields.length then .error (.scope fields.length parts.length)
      else layOut fields (parts.map ByteArray.mk)) = (serializeStruct fields values).map ByteArray.mk := by
  -- A struct has one part per field, so the count always matches.
  have count := serializeFields_length fields values parts wrote
  rw [List.length_map, count, bne_self_eq_false, if_neg (by decide),
    layOut_ok fields parts (struct_widths fields sound values parts wrote)]
  simp [serializeStruct, wrote, Bind.bind, Except.bind]

/-- Assembling the encodings of a container's fields is serializing the container. -/
theorem assemble_container (names : List String) (fields : List Desc)
    (sound : ∀ field ∈ fields, field.wellFormed = .ok ()) (values : List Value) (parts : List Bytes)
    (wrote : serializeFields fields values = .ok parts) :
    assemble (.container names fields) (parts.map ByteArray.mk) =
      (serialize (.container names fields) (.seq values)).map ByteArray.mk := by
  rw [assemble, serialize, ← assemble_struct fields sound values parts wrote, List.length_map]

/-- Assembling the encodings of a progressive container's fields is serializing the container. -/
theorem assemble_progressiveContainer (active : List Bool) (names : List String) (fields : List Desc)
    (sound : ∀ field ∈ fields, field.wellFormed = .ok ()) (values : List Value) (parts : List Bytes)
    (wrote : serializeFields fields values = .ok parts) :
    assemble (.progressiveContainer active names fields) (parts.map ByteArray.mk) =
      (serialize (.progressiveContainer active names fields) (.seq values)).map ByteArray.mk := by
  rw [assemble, serialize, ← assemble_struct fields sound values parts wrote, List.length_map]

/-- Assembling a selector byte and the encoding of the option it names is serializing the union. -/
theorem assemble_union (selectors : List Nat) (options : List Desc) (selector : Nat) (small : selector < 256)
    (option : Desc) (found : lookupOption selectors options selector = .ok option)
    (sound : option.wellFormed = .ok ()) (data : Value) (body : Bytes) (wrote : serialize option data = .ok body) :
    assemble (.compatibleUnion selectors options) [⟨#[UInt8.ofNat selector]⟩, ⟨body⟩] =
      (serialize (.compatibleUnion selectors options) (.union selector data)).map ByteArray.mk := by
  -- The selector byte reads back as the selector, since it fits a byte.
  have byte : (ByteArray.get! ⟨#[UInt8.ofNat selector]⟩ 0).toNat = selector := by
    simp [ByteArray.get!, Nat.mod_eq_of_lt small]
  -- The body has the option's width when the option has one.
  have fits : partFits option ⟨body⟩ = .ok () := by
    unfold partFits
    split
    · rename_i width fixed
      simp [ByteArray.size, serialize_size_of_encoding sound fixed wrote]
    · rfl
  simp only [assemble, serialize, byte, found, fits, wrote, ByteArray.size, List.size_toArray, List.length_cons,
    List.length_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, pure, Except.pure]
  -- A selector out of range is refused alike, and otherwise the bytes are the same.
  cases checkSelector selector with
  | error e => rfl
  | ok u =>
    -- Joining two wrapped arrays wraps the joined arrays.
    simp only [Except.map]
    congr 1
    exact ByteArray.ext (by simp [ByteArray.data_append])

/-- Assembling bytes of a byte vector is serializing the bytes they join to. -/
theorem assemble_byteVector (length : Nat) (parts : List ByteArray) :
    assemble (.byteVector length) parts =
      (serialize (.byteVector length) (.bytes (joinParts parts).data)).map ByteArray.mk := by
  simp only [assemble, serialize, ByteArray.size, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind,
    pure, Except.pure]
  -- The same two checks, in the same order, on the same bytes.
  split <;> (try split) <;> rfl

/-- Assembling bytes of a byte list is serializing the bytes they join to. -/
theorem assemble_byteList (limit : Nat) (parts : List ByteArray) :
    assemble (.byteList limit) parts =
      (serialize (.byteList limit) (.bytes (joinParts parts).data)).map ByteArray.mk := by
  simp only [assemble, serialize, ByteArray.size, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind,
    pure, Except.pure]
  -- The same two checks, in the same order, on the same bytes.
  split <;> (try split) <;> rfl

/-- Pushing a bit leaves every other position as it was. -/
theorem push_other (bits : Array Bool) (bit : Bool) (i : Nat) (other : i ≠ bits.size) :
    (bits.push bit)[i]? = bits[i]? := by
  rw [Array.getElem?_push, if_neg other]

/-- Pushing a bit puts it right after the last one. -/
theorem push_at (bits : Array Bool) (bit : Bool) (i : Nat) (at_ : i = bits.size) :
    (bits.push bit)[i]? = some bit := by
  rw [at_, Array.getElem?_push_size]

/-- A byte away from the one the closing bit lands in packs the same bits with or without it. -/
theorem packByte_push_other (bits : Array Bool) (j : Nat) (other : j ≠ bits.size / 8) :
    packByte (bits.push true) j = packByte bits j := by
  simp (disch := omega) only [packByte, push_other]

/-- The byte the closing bit lands in packs the bits before it, and the closing bit just above them. -/
theorem packByte_push_last (bits : Array Bool) :
    packByte (bits.push true) (bits.size / 8) = packByte bits (bits.size / 8) ||| (1 <<< UInt8.ofNat (bits.size % 8)) := by
  obtain ⟨q, u, hq, hu⟩ : ∃ q u, bits.size / 8 = q ∧ bits.size % 8 = u := ⟨_, _, rfl, rfl⟩
  have size : bits.size = q * 8 + u := by omega
  have small : u < 8 := by omega
  rw [hq, hu]
  -- The position of the closing bit is one of eight, so it is made concrete first.
  rcases (by omega : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 5 ∨ u = 6 ∨ u = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  -- Below the closing bit both read the same bits, it reads set, and above it both read nothing.
  simp (disch := omega) only [packByte, push_other, push_at, Array.getElem?_eq_none, Option.getD_none,
    Option.getD_some] <;>
  generalize bits[q * 8 + 0]?.getD false = b0 <;>
  generalize bits[q * 8 + 1]?.getD false = b1 <;>
  generalize bits[q * 8 + 2]?.getD false = b2 <;>
  generalize bits[q * 8 + 3]?.getD false = b3 <;>
  generalize bits[q * 8 + 4]?.getD false = b4 <;>
  generalize bits[q * 8 + 5]?.getD false = b5 <;>
  generalize bits[q * 8 + 6]?.getD false = b6 <;>
  decide +revert

/-- The bits packed, then closed by a set bit, are the delimited encoding of the bits. -/
theorem assembleBits_packed (limit : Option Nat) (bits : Array Bool) :
    assembleBits limit bits.size ⟨packBits bits ((bits.size + 7) / 8)⟩ =
      (do boundCheck limit bits.size; return ⟨packBitsDelimited bits⟩) := by
  -- The packed bytes are as many as the bits need, so their size is never refused.
  have packedSize : (packBits bits ((bits.size + 7) / 8)).size = (bits.size + 7) / 8 := by simp [packBits]
  -- Every byte is a packed byte, read by its index.
  have byteAt : ∀ (data : Array Bool) (count i : Nat) (small : i < count),
      (packBits data count)[i]! = packByte data i := by
    intro data count i small
    simp [packBits, getElem!_pos, small]
  simp only [assembleBits, ByteArray.size, packedSize, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure]
  cases boundCheck limit bits.size with
  | error e => rfl
  | ok u =>
    simp only
    by_cases whole : bits.size % 8 = 0
    -- A whole number of bytes: the closing bit takes a byte of its own.
    · simp only [whole, beq_self_eq_true, ↓reduceIte]
      congr 1
      apply ByteArray.ext
      simp only [ByteArray.data_push, packBitsDelimited]
      apply Array.ext
      · simp [packBits]; omega
      · intro i inLeft _
        simp only [Array.size_push, packedSize] at inLeft
        rw [Array.getElem_push]
        simp only [packBits, Array.getElem_ofFn]
        split
        · rename_i before
          have : i < (bits.size + 7) / 8 := by simpa [packBits] using before
          exact (packByte_push_other bits i (by omega)).symm
        -- The last byte holds nothing but the closing bit.
        · rename_i after
          have : ¬ i < (bits.size + 7) / 8 := by simpa [packBits] using after
          have last : i = bits.size / 8 := by omega
          subst last
          rw [packByte_push_last, whole]
          have empty := packByte_high_clear bits (bits.size / 8) 0 (by decide) (by omega)
          rw [show UInt8.ofNat 0 = 0 from rfl, UInt8.shiftRight_zero] at empty
          rw [empty]
          decide
    -- Otherwise the closing bit goes into the last byte, above the bits there, which are clear.
    · have notWhole : (bits.size % 8 == 0) = false := by simpa using whole
      have lastIndex : (bits.size + 7) / 8 - 1 = bits.size / 8 := by omega
      have clear := packByte_high_clear bits (bits.size / 8) (bits.size % 8) (Nat.mod_lt _ (by decide)) (by omega)
      have readLast : ByteArray.get! ⟨packBits bits ((bits.size + 7) / 8)⟩ ((bits.size + 7) / 8 - 1) =
          packByte bits (bits.size / 8) := by
        rw [lastIndex]
        exact byteAt bits _ _ (by omega)
      simp only [notWhole, Bool.false_eq_true, ↓reduceIte, readLast, clear, bne_self_eq_false]
      congr 1
      apply ByteArray.ext
      show (packBits bits ((bits.size + 7) / 8)).set! _ _ = packBitsDelimited bits
      simp only [packBitsDelimited]
      apply Array.ext
      · simp [packBits]; omega
      · intro i inLeft _
        simp only [Array.size_set!, packedSize] at inLeft
        simp only [Array.set!_eq_setIfInBounds, packBits, lastIndex]
        by_cases same : i = bits.size / 8
        · subst same
          rw [Array.getElem_setIfInBounds_self, Array.getElem_ofFn, packByte_push_last]
        · rw [Array.getElem_setIfInBounds_ne (by simpa using inLeft) (Ne.symm same), Array.getElem_ofFn,
            Array.getElem_ofFn]
          exact (packByte_push_other bits i same).symm

/-- Assembling a bit list's packed bits from its bit count is serializing the bit list. -/
theorem assemble_bitList (limit : Nat) (bits : Array Bool) :
    assembleBits (some limit) bits.size ⟨packBits bits ((bits.size + 7) / 8)⟩ =
      (serialize (.bitList limit) (.bits bits)).map ByteArray.mk := by
  rw [assembleBits_packed, serialize]
  -- The one bound is checked alike.
  by_cases within : bits.size ≤ limit <;> simp [boundCheck, within, Bind.bind, Except.bind, Except.map, pure, Except.pure]

/-- Assembling a progressive bit list's packed bits from its bit count is serializing the bit list. -/
theorem assemble_progressiveBitList (limit : Option Nat) (bits : Array Bool) :
    assembleBits limit bits.size ⟨packBits bits ((bits.size + 7) / 8)⟩ =
      (serialize (.progressiveBitList limit) (.bits bits)).map ByteArray.mk := by
  rw [assembleBits_packed, serialize]
  -- The one bound is checked alike.
  cases boundCheck limit bits.size <;> rfl

end Ssz.Native
