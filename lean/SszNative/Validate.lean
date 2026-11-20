import EthLib.Consensus.Ssz.Codec.Deserialize

/-!
Checking an encoding against a type, without building the value it holds.

Each check refuses exactly what deserialization refuses, with the same reason, in the same order.
A range of the encoding stands for the slice deserialization would cut out of it.
Every step mirrors a step of deserialization, on ranges in place of slices.
-/

namespace EthLib.Consensus.Ssz.Native

open EthLib.Consensus.Ssz

/-- The little-endian four-byte offset at a position. -/
@[inline] def offsetAt (b : ByteArray) (pos : Nat) : Nat :=
  (b.get! pos).toNat + 256 * ((b.get! (pos + 1)).toNat + 256 * ((b.get! (pos + 2)).toNat +
    256 * (b.get! (pos + 3)).toNat))

/-- The first composite size four-byte offsets cannot name. -/
abbrev offsetBound : Nat := 2 ^ (8 * bytesPerOffset)

/--
One byte a fixed-size value can be refused for, at an offset from the value's start.

Integers and byte arrays decode from any bytes of their width, so only booleans and padded bit vectors leave probes.
-/
inductive Probe where
  /-- A boolean's byte, which must be zero or one. -/
  | bit (offset : Nat)
  /-- A bit vector's last byte, whose bits from a position up are padding and must be clear. -/
  | padding (offset bits : Nat)

/-- The probe moved a number of bytes further from the start. -/
def Probe.shift (by_ : Nat) : Probe → Probe
  | .bit offset => .bit (by_ + offset)
  | .padding offset bits => .padding (by_ + offset) bits

/-- Refuses a value starting at a position for one probe, as deserialization would. -/
def Probe.check (b : ByteArray) (start : Nat) : Probe → Except Err Unit
  | .bit offset =>
    let byte := b.get! (start + offset)
    if byte != 0 && byte != 1 then .error (.notABit byte.toNat) else .ok ()
  | .padding offset bits =>
    if b.get! (start + offset) >>> UInt8.ofNat bits != 0 then .error .paddingBits else .ok ()

/-- Runs probes in order, stopping at the first refusal. -/
def checkProbes (b : ByteArray) (start : Nat) : List Probe → Except Err Unit
  | [] => .ok ()
  | probe :: rest => do
    probe.check b start
    checkProbes b start rest

/-- Whether every probe passes, without building a refusal. -/
def probesPass (b : ByteArray) (start : Nat) : List Probe → Bool
  | [] => true
  | .bit offset :: rest =>
    let byte := b.get! (start + offset)
    (byte == 0 || byte == 1) && probesPass b start rest
  | .padding offset bits :: rest =>
    b.get! (start + offset) >>> UInt8.ofNat bits == 0 && probesPass b start rest

mutual

/-- Whether a type has a fixed size, computed without allocating. -/
def hasWidth : Desc → Bool
  | .bool | .uint _ | .byteVector _ | .bitVector _ => true
  | .vector element _ => hasWidth element
  | .container _ fields => allHaveWidth fields
  | .progressiveContainer _ _ fields => allHaveWidth fields
  | _ => false

/-- Whether every type of a list has a fixed size. -/
def allHaveWidth : List Desc → Bool
  | [] => true
  | field :: rest => hasWidth field && allHaveWidth rest

end

mutual

/-- A fixed-size type's width, computed without allocating. -/
def fixedWidth : Desc → Nat
  | .bool => 1
  | .uint width => width
  | .byteVector length => length
  | .bitVector length => (length + 7) / 8
  | .vector element length => fixedWidth element * length
  | .container _ fields => fieldsWidth fields
  | .progressiveContainer _ _ fields => fieldsWidth fields
  | _ => 0

/-- The total width of a list of fixed-size types. -/
def fieldsWidth : List Desc → Nat
  | [] => 0
  | field :: rest => fixedWidth field + fieldsWidth rest

end

/-- Probes moved a number of bytes further from the start. -/
def shiftAll (by_ : Nat) : List Probe → List Probe
  | [] => []
  | probe :: rest => probe.shift by_ :: shiftAll by_ rest

/-- Probes repeated for a count of records one width apart, from an index on. -/
def repeatProbes (probes : List Probe) (width index : Nat) : Nat → List Probe
  | 0 => []
  | count + 1 => shiftAll (index * width) probes ++ repeatProbes probes width (index + 1) count

mutual

/--
The probes of a fixed-size type, in the order deserialization reads the bytes they test.

A value of the type's width is refused exactly where one of these probes fails.
-/
def plan : Desc → List Probe
  | .bool => [.bit 0]
  | .bitVector length =>
    if length % 8 != 0 && (length + 7) / 8 > 0 then [.padding ((length + 7) / 8 - 1) (length % 8)] else []
  | .vector element length =>
    match plan element with
    -- Elements without probes leave none, however many there are.
    | [] => []
    | probes => repeatProbes probes (fixedWidth element) 0 length
  | .container _ fields => fieldsPlan fields 0
  | .progressiveContainer _ _ fields => fieldsPlan fields 0
  | _ => []

/-- The probes of a struct's fixed fields, from an offset on. -/
def fieldsPlan : List Desc → Nat → List Probe
  | [], _ => []
  | field :: fields, offset =>
    match plan field with
    | [] => fieldsPlan fields (offset + fixedWidth field)
    | probes => shiftAll offset probes ++ fieldsPlan fields (offset + fixedWidth field)

end

/-- Whether deserializing the type first bounds its size by what four-byte offsets can name. -/
def composite : Desc → Bool
  | .byteVector _ | .byteList _ | .vector _ _ | .container _ _ | .progressiveContainer _ _ _ => true
  | _ => false

/-- Refuses a count of records one width apart, running the same probes on each. -/
def checkRecords (b : ByteArray) (width : Nat) (probes : List Probe) (start : Nat) : Nat → Except Err Unit
  | 0 => .ok ()
  | count + 1 =>
    -- A passing record needs no refusal built.
    if probesPass b start probes then checkRecords b width probes (start + width) count
    else checkProbes b start probes

/-- Whether every one of a count of records one width apart passes the same probes. -/
def recordsPass (b : ByteArray) (width : Nat) (probes : List Probe) (start : Nat) : Nat → Bool
  | 0 => true
  | count + 1 => if probesPass b start probes then recordsPass b width probes (start + width) count else false

/--
Records one task checks.

A task then checks thousands of records, far above the cost of starting it.
-/
abbrev recordsPerTask : Nat := 16384

/--
Refuses a count of records one width apart, as the record loop does, checking runs of records in parallel.

Only a failing run is checked again in order, to find the first refusal.
-/
def checkAllRecords (b : ByteArray) (width : Nat) (probes : List Probe) (start count : Nat) : Except Err Unit :=
  -- A single run is checked in place, with no task.
  if count ≤ recordsPerTask then checkRecords b width probes start count else
  let runs := (count + recordsPerTask - 1) / recordsPerTask
  let tasks := (List.range runs).map fun k =>
    Task.spawn fun _ =>
      recordsPass b width probes (start + width * (recordsPerTask * k))
        (min recordsPerTask (count - recordsPerTask * k))
  if tasks.all (·.get) then .ok () else checkRecords b width probes start count

/-- The same probes run over a count of records one width apart, from an offset on. -/
structure ProbeRun where
  /-- Where the first record starts, from the value's start. -/
  offset : Nat
  /-- The distance from one record's start to the next. -/
  width : Nat
  /-- How many records there are. -/
  count : Nat
  /-- The probes of one record. -/
  probes : List Probe

/-- The run moved a number of bytes further from the start. -/
def ProbeRun.shift (by_ : Nat) (run : ProbeRun) : ProbeRun :=
  { run with offset := by_ + run.offset }

mutual

/--
The probes of a fixed-size type, as runs over records instead of one probe per record.

A vector keeps its element's probes once, however many elements it has.
-/
def runs : Desc → List ProbeRun
  | .vector element length =>
    match plan element with
    | [] => []
    | probes => [⟨0, fixedWidth element, length, probes⟩]
  | .container _ fields => fieldsRuns fields 0
  | .progressiveContainer _ _ fields => fieldsRuns fields 0
  -- Any other type is one record of its own probes.
  | d =>
    match plan d with
    | [] => []
    | probes => [⟨0, 0, 1, probes⟩]

/-- The runs of a struct's fixed fields, from an offset on. -/
def fieldsRuns : List Desc → Nat → List ProbeRun
  | [], _ => []
  | field :: fields, offset =>
    (runs field).map (ProbeRun.shift offset) ++ fieldsRuns fields (offset + fixedWidth field)

end

/-- Runs each run's records in order, stopping at the first refusal. -/
def checkRuns (b : ByteArray) (start : Nat) : List ProbeRun → Except Err Unit
  | [] => .ok ()
  | run :: rest => do
    checkAllRecords b run.width run.probes (start + run.offset) run.count
    checkRuns b start rest

/-- Refuses a range against a fixed-size type of a width: the size checks, then the probes. -/
def validateFixed (d : Desc) (width : Nat) (b : ByteArray) (start stop : Nat) : Except Err Unit := do
  let size := stop - start
  if composite d && size ≥ 2 ^ (8 * bytesPerOffset) then throw (.offsetOverflow size)
  if size != width then throw (.scope width size)
  checkRuns b start (runs d)

/-- Refuses a delimited bit encoding as deserialization does, giving the number of bits it holds. -/
def delimitedCount (b : ByteArray) (start stop : Nat) (limit : Option Nat) : Except Err Nat := do
  let size := stop - start
  if size == 0 then throw .emptyEncoding
  let final := b.get! (stop - 1)
  -- Trailing zero bytes would give one value a second encoding.
  if final == 0 then
    if (List.range size).all (fun i => b.get! (start + i) == 0) then throw .noDelimiter
    else throw .trailingZeros
  let count := 8 * (size - 1) + highestBit final
  if let some cap := limit then
    if count > cap then throw (.overLimit cap count)
  return count

/-- Element ranges: a count of them one width apart from a start, or listed one by one. -/
inductive Ranges where
  /-- The ranges of a count of elements of one width, back to back from a start. -/
  | stride (start width count : Nat)
  /-- Ranges given one by one. -/
  | listed (ranges : List (Nat × Nat))

/-- The ranges, one by one. -/
def Ranges.toList : Ranges → List (Nat × Nat)
  | .stride start width count => (List.range count).map fun i => (start + i * width, start + (i + 1) * width)
  | .listed ranges => ranges

/-- The bodies a table of offsets opens, as ranges from a start. -/
def bodies (start : Nat) (offsets spans : List Nat) : List (Nat × Nat) :=
  (offsets.zip spans).map fun (o, s) => (start + o, start + o + s)

/-- Where a fixed-count sequence's elements sit, refusing it as deserialization does. -/
def vectorRanges (element : Desc) (length : Nat) (b : ByteArray) (start stop : Nat) : Except Err Ranges := do
  let size := stop - start
  if size ≥ offsetBound then throw (.offsetOverflow size)
  match element.fixedSize with
  | some width =>
    let expected := width * length
    if size != expected then throw (.scope expected size)
    return .stride start width length
  | none =>
    let expectedFirst := length * bytesPerOffset
    if size < expectedFirst then throw (.scopeTooSmall expectedFirst size)
    if length == 0 then return .listed []
    let offsets := (List.range length).map fun i => offsetAt b (start + i * bytesPerOffset)
    if offsets[0]! != expectedFirst then throw (.firstOffset expectedFirst offsets[0]!)
    let spans ← offsetSpans offsets size
    return .listed (bodies start offsets spans)

/-- Where a counted sequence's elements sit, refusing it as deserialization does. -/
def listRanges (element : Desc) (limit : Option Nat) (b : ByteArray) (start stop : Nat) : Except Err Ranges := do
  let size := stop - start
  if size ≥ offsetBound then throw (.offsetOverflow size)
  if size == 0 then return .listed []
  match element.fixedSize with
  | some width =>
    if width == 0 then throw .scopeWidthless
    if size % width != 0 then throw (.scopeUndivided size width)
    let count := size / width
    if let some cap := limit then
      if count > cap then throw (.overLimit cap count)
    return .stride start width count
  | none =>
    if size < bytesPerOffset then throw (.scopeTooSmall bytesPerOffset size)
    let first := offsetAt b start
    if first < bytesPerOffset then throw .offsetBelowTable
    if first % bytesPerOffset != 0 then throw .offsetUnaligned
    if first > size then throw .offsetPastScope
    let count := first / bytesPerOffset
    if let some cap := limit then
      if count > cap then throw (.overLimit cap count)
    let offsets := (List.range count).map fun i => offsetAt b (start + i * bytesPerOffset)
    let spans ← offsetSpans offsets size
    return .listed (bodies start offsets spans)

/-- Where one field of a struct sits: a range in place, or an offset to its body. -/
inductive Place where
  /-- The field's bytes, in place. -/
  | inline (start stop : Nat)
  /-- Where the field's body begins, from the struct's start. -/
  | body (offset : Nat)

/-- The places of a struct's fields, from a position of its fixed part. -/
def readPlaces : List Desc → ByteArray → Nat → Nat → Nat → Except Err (List Place × Nat)
  | [], _, _, _, position => .ok ([], position)
  | field :: fields, b, start, size, position =>
    match field.fixedSize with
    | some width => do
      if position + width > size then throw .truncated
      let (rest, ending) ← readPlaces fields b start size (position + width)
      return (.inline (start + position) (start + position + width) :: rest, ending)
    | none => do
      if position + bytesPerOffset > size then throw .truncated
      let (rest, ending) ← readPlaces fields b start size (position + bytesPerOffset)
      return (.body (offsetAt b (start + position)) :: rest, ending)

/-- Where each body begins, in the order the table names them. -/
def placeStarts : List Place → List Nat
  | [] => []
  | .inline _ _ :: rest => placeStarts rest
  | .body offset :: rest => offset :: placeStarts rest

/-- The range of a field with no body to read, a body standing for nothing here. -/
def Place.held (start : Nat) : Place → Nat × Nat
  | .inline s e => (s, e)
  | .body _ => (start, start)

/-- The fields' ranges in order, each body taken from the span its offset opened. -/
def takePlaces (start : Nat) : List Place → List Nat → Except Err (List (Nat × Nat))
  | [], _ => .ok []
  | .inline s e :: rest, spans => do return (s, e) :: (← takePlaces start rest spans)
  | .body o :: rest, span :: spans => do return (start + o, start + o + span) :: (← takePlaces start rest spans)
  | .body _ :: _, [] => .error .badDeclaration

/--
The places of a struct's fixed part, and where that part ends.

The budget is settled first, so no place is read past the range.
-/
def fieldPlaces (fields : List Desc) (b : ByteArray) (start stop : Nat) : Except Err (List Place × Nat) := do
  let size := stop - start
  if size ≥ offsetBound then throw (.offsetOverflow size)
  -- The budget is settled before any field is read, so a refusal names the input.
  structBudget fields size
  readPlaces fields b start size 0

/-- Each field's range, once the offsets in the fixed part are checked against the range. -/
def placeRanges (start stop : Nat) (places : List Place) (leading : Nat) : Except Err (List (Nat × Nat)) := do
  let size := stop - start
  let offsets := placeStarts places
  -- With no bodies, the places just read are the whole encoding.
  if offsets.isEmpty then
    if size != leading then throw (.scope leading size)
    return places.map (Place.held start)
  -- The first body starts where the fixed part ends.
  if offsets[0]! != leading then throw (.firstOffset leading offsets[0]!)
  let spans ← offsetSpans offsets size
  takePlaces start places spans

/--
Where each field's bytes sit, refusing the struct as deserialization does.

Fixed fields sit in place, and each variable field's body runs from its offset to the next offset.
-/
def fieldRanges (fields : List Desc) (b : ByteArray) (start stop : Nat) : Except Err (List (Nat × Nat)) := do
  let (places, leading) ← fieldPlaces fields b start stop
  placeRanges start stop places leading

mutual

/-- Refuses the range of an encoding exactly as deserializing it against the type would. -/
def validateRange (d : Desc) (b : ByteArray) (start stop : Nat) : Except Err Unit :=
  -- A fixed-size type is checked by its sizes and its probes alone.
  if hasWidth d then validateFixed d (fixedWidth d) b start stop
  else validateVariable d b start stop
termination_by (sizeOf d, 1, 0)

/-- Refuses the range of an encoding against a variable-size type. -/
def validateVariable (d : Desc) (b : ByteArray) (start stop : Nat) : Except Err Unit := do
  let size := stop - start
  match d with
  | .byteList limit =>
    if size ≥ offsetBound then throw (.offsetOverflow size)
    if size > limit then throw (.overLimit limit size)
  | .bitList limit => discard <| delimitedCount b start stop (some limit)
  | .progressiveBitList limit => discard <| delimitedCount b start stop limit
  | .vector element length => validateRanges element b (← vectorRanges element length b start stop)
  | .list element limit => validateRanges element b (← listRanges element (some limit) b start stop)
  | .progressiveList element limit => validateRanges element b (← listRanges element limit b start stop)
  | .container _ fields => validateStruct fields b start stop
  | .progressiveContainer _ _ fields => validateStruct fields b start stop
  | .compatibleUnion selectors options =>
    if size < 1 then throw .noSelector
    validateOption selectors options (b.get! start).toNat b (start + 1) stop
  -- Every other type has a fixed size.
  | _ => .ok ()
termination_by (sizeOf d, 0, 0)

/-- Refuses each element's range in order, stopping at the first refusal. -/
def validateRanges (element : Desc) (b : ByteArray) : Ranges → Except Err Unit
  -- Elements one width apart are fixed-size, so each is checked by the same probes.
  | .stride start width count =>
    match plan element with
    | [] => .ok ()
    | probes => checkAllRecords b width probes start count
  | .listed ranges => validateEach element b ranges
termination_by (sizeOf element, 3, 0)

/-- Refuses each listed range in order. -/
def validateEach (element : Desc) (b : ByteArray) : List (Nat × Nat) → Except Err Unit
  | [] => .ok ()
  | (s, e) :: rest => do
    validateRange element b s e
    validateEach element b rest
termination_by ranges => (sizeOf element, 2, ranges.length)

/--
Each field of a struct against its own range, in the order deserialization reads them.

    budget        the range against the width of the fixed part
    fixed part    each fixed field, in place
    table         the offsets, as a whole
    bodies        each variable field, in declaration order

A range breaking several rules is refused for the first one met in that order.
-/
def validateStruct (fields : List Desc) (b : ByteArray) (start stop : Nat) : Except Err Unit := do
  let (places, leading) ← fieldPlaces fields b start stop
  -- Fixed fields are checked before any offset is trusted.
  -- Without offsets, declaration order is already reading order, so nothing is checked ahead.
  if !(placeStarts places).isEmpty then validateInline fields b places
  -- A fixed field checked above is checked the same way here, so only a body can refuse now.
  validateFields fields b (← placeRanges start stop places leading)
termination_by (sizeOf fields, 3, 0)

/-- Each field in place against its range, a field behind an offset skipped. -/
def validateInline : List Desc → ByteArray → List Place → Except Err Unit
  | [], _, _ | _ :: _, _, [] => .ok ()
  | field :: fields, b, .inline s e :: places => do
    validateRange field b s e
    validateInline fields b places
  | _ :: fields, b, .body _ :: places => validateInline fields b places
termination_by fields => (sizeOf fields, 2, 0)

/-- Each field against its own range, in declaration order. -/
def validateFields : List Desc → ByteArray → List (Nat × Nat) → Except Err Unit
  | [], _, [] => .ok ()
  | field :: fields, b, (s, e) :: ranges => do
    validateRange field b s e
    validateFields fields b ranges
  | _, _, _ => .error .typeMismatch
termination_by fields => (sizeOf fields, 2, 0)

/-- The option a selector names, checked against the rest of the range. -/
def validateOption : List Nat → List Desc → Nat → ByteArray → Nat → Nat → Except Err Unit
  | [], [], selector, _, _, _ => .error (.unknownSelector selector)
  | chosen :: selectors, option :: options, selector, b, start, stop =>
    if chosen == selector then do
      checkSelector selector
      validateRange option b start stop
    else validateOption selectors options selector b start stop
  | _, _, _, _, _, _ => .error .badDeclaration
termination_by _ options => (sizeOf options, 2, 0)

end

/--
Refuses an encoding exactly as deserializing it against the type would, for every descriptor.

This validates bytes, not declaration legality. Check `d.wellFormed` at the boundary
where an external descriptor is accepted before using it for roots or proofs.
-/
def validate (d : Desc) (b : ByteArray) : Except Err Unit :=
  validateRange d b 0 b.size

end EthLib.Consensus.Ssz.Native
