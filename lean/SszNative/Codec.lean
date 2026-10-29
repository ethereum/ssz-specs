import SszNative.Validate

/-!
Deserialization and serialization one layer at a time, on encodings rather than values.

A composite's encoding is cut into the ranges its parts sit at, exactly where deserialization cuts its slices.
The encodings of a composite's parts are laid out into its encoding, exactly as serialization lays them out.
Nothing here builds a value: a caller decodes or encodes each part itself, one layer down.

    view      the range of a composite's encoding  ->  one range per part
    assemble  one encoding per part                ->  the composite's encoding

A union has two parts: its selector byte, then the encoding of the option the selector names.
-/

namespace EthLib.Consensus.Ssz.Native

open EthLib.Consensus.Ssz

/--
Where each part of a composite sits inside the range of its encoding, refusing the range as deserialization does.

Only the composite's own layer is checked: its sizes and its offsets.
Each part's range is then decoded, or checked, on its own.

A type with no parts to cut, a basic or a packed one, is refused.
-/
def viewRanges (d : Desc) (b : ByteArray) (start stop : Nat) : Except Err (List (Nat × Nat)) :=
  match d with
  | .vector element length => (vectorRanges element length b start stop).map Ranges.toList
  | .list element limit => (listRanges element (some limit) b start stop).map Ranges.toList
  | .progressiveList element limit => (listRanges element limit b start stop).map Ranges.toList
  | .container _ fields => fieldRanges fields b start stop
  | .progressiveContainer _ _ fields => fieldRanges fields b start stop
  -- The selector byte, then the option's encoding, which is all the rest.
  | .compatibleUnion _ _ =>
    if stop - start < 1 then .error .noSelector else .ok [(start, start + 1), (start + 1, stop)]
  | _ => .error .typeMismatch

/-- The bytes of several parts, one after the other. -/
def joinParts : List ByteArray → ByteArray
  | [] => .empty
  | part :: rest => part ++ joinParts rest

/--
Refuses a part that cannot be the encoding of a type.

A fixed-size type encodes to its width, whatever value it holds.
Any size can be the encoding of a variable-size type.
-/
def partFits (d : Desc) (part : ByteArray) : Except Err Unit :=
  match d.fixedSize with
  | some width => if part.size != width then .error (.count width part.size) else .ok ()
  | none => .ok ()

/-- Refuses the first part, in order, that cannot be the encoding of the type it is paired with. -/
def checkParts : List Desc → List ByteArray → Except Err Unit
  | field :: fields, part :: parts => do
    partFits field part
    checkParts fields parts
  | _, _ => .ok ()

/--
Parts laid out as a struct or a sequence encodes them, each part paired with its type.

Fixed parts sit in place, and variable ones leave an offset behind and follow after.
-/
def layOut (fields : List Desc) (parts : List ByteArray) : Except Err ByteArray := do
  checkParts fields parts
  let bytes ← Ssz.assemble (fields.map Desc.isFixed) (parts.map ByteArray.data)
  return ⟨bytes⟩

/--
The encoding of a composite, from the encodings of its parts, refusing parts no value could have.

    vectors, lists      one part per element
    structs             one part per field
    unions              the selector byte, then the option's encoding
    byte arrays         the bytes, cut into parts of any sizes

A count the type does not allow is refused as serialization refuses it.
A part of the wrong size for a fixed-size type is refused before anything is laid out.
Bit lists have their own assembly, from a bit count.
-/
def assemble (d : Desc) (parts : List ByteArray) : Except Err ByteArray :=
  match d with
  | .byteVector length => do
    let data := joinParts parts
    if data.size != length then throw (.scope length data.size)
    if data.size ≥ offsetBound then throw (.offsetOverflow data.size)
    return data
  | .byteList limit => do
    let data := joinParts parts
    if data.size > limit then throw (.overLimit limit data.size)
    if data.size ≥ offsetBound then throw (.offsetOverflow data.size)
    return data
  | .vector element length =>
    if parts.length != length then .error (.scope length parts.length)
    else layOut (List.replicate parts.length element) parts
  | .list element limit =>
    if parts.length > limit then .error (.overLimit limit parts.length)
    else layOut (List.replicate parts.length element) parts
  | .progressiveList element limit => do
    boundCheck limit parts.length
    layOut (List.replicate parts.length element) parts
  | .container _ fields =>
    if parts.length != fields.length then .error (.scope fields.length parts.length)
    else layOut fields parts
  | .progressiveContainer _ _ fields =>
    if parts.length != fields.length then .error (.scope fields.length parts.length)
    else layOut fields parts
  | .compatibleUnion selectors options =>
    match parts with
    | [selector, body] => do
      if selector.size != 1 then throw (.count 1 selector.size)
      let chosen := (selector.get! 0).toNat
      let option ← lookupOption selectors options chosen
      checkSelector chosen
      partFits option body
      return selector ++ body
    | _ => .error (.scope 2 parts.length)
  | _ => .error .typeMismatch

/--
The encoding of a bit list, from its bit count and its bits packed into bytes.

The packed bytes hold the bits lowest first, as the encoding does, with any padding bits of the last byte clear.
The closing bit then goes right after the last bit: into the last byte, or into a byte of its own.

    bits 1, 0, 1        packed 0b00000101   encoding 0b00001101
    bits 1 .. 8 set     packed 0xff         encoding 0xff 0x01
-/
def assembleBits (limit : Option Nat) (count : Nat) (packed : ByteArray) : Except Err ByteArray := do
  boundCheck limit count
  if packed.size != (count + 7) / 8 then throw (.count ((count + 7) / 8) packed.size)
  let used := count % 8
  -- A whole number of bytes leaves no room in the last one, so the closing bit takes a byte.
  if used == 0 then return packed.push 1
  let last := packed.get! (packed.size - 1)
  if last >>> UInt8.ofNat used != 0 then throw .paddingBits
  return packed.set! (packed.size - 1) (last ||| (1 <<< UInt8.ofNat used))

end EthLib.Consensus.Ssz.Native
