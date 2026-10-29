import SszNative.Tree
import SszNative.Validate
import Ssz.Codec.Layout

/-!
The root of an encoded value, computed from its bytes.

Roots assume an encoding that validation accepted, and the public entry point checks it first.

Values of a fixed-size type are rooted many at a time, as columns.
Records sit one width apart in the encoding.
Column j holds field j's root for every record, from one gather or one slice.
Columns are then hashed pairwise, level by level, until one column holds every record's root.
-/

namespace Ssz.Native

open Ssz

/-- A buffer of zero bytes: one empty field in a slot of that size. -/
def zeros (size : Nat) : ByteArray :=
  gather ByteArray.empty 0 0 0 1 size.toUSize

/-- Nodes needed to hold a number of bytes. -/
def nodesFor (bytes : Nat) : Nat := (bytes + 31) / 32

/-- Bytes of a range, padded with zeros to whole nodes, and one spare node for an odd level. -/
def packRange (b : ByteArray) (start stop : Nat) : ByteArray :=
  let size := stop - start
  ByteArray.copySlice b start (zeros (32 * nodesFor size + 32)) 0 size

/--
The tree over a list of columns, every column holding a count of nodes.

Pairs of columns are hashed into one column per level.
An odd column out is hashed against the zero tree of its height.
-/
def columnTree (columns : List ByteArray) (count : Nat) : (height : Nat) → (fuel : Nat) → ByteArray
  | _, 0 => columns.headD ByteArray.empty
  | height, fuel + 1 =>
    match columns with
    | [] => ByteArray.empty
    | [root] => root
    | _ =>
      let rec pairUp : List ByteArray → List ByteArray
        | a :: b :: rest => hashColumns a 0 b 0 count.toUSize :: pairUp rest
        | [a] => [hashFixed a 0 (zeroRoot height) count.toUSize]
        | [] => []
      columnTree (pairUp columns) count (height + 1) fuel

/-- The tree over a list of columns, with as many levels as the column count needs. -/
def columnRoots (columns : List ByteArray) (count : Nat) : ByteArray :=
  columnTree columns count 0 (columns.length + 1)

/-- A column of nodes climbed a number of levels against the zero trees. -/
def climbColumn (column : ByteArray) (count height : Nat) : (levels : Nat) → ByteArray
  | 0 => column
  | levels + 1 => climbColumn (hashFixed column 0 (zeroRoot height) count.toUSize) count (height + 1) levels

mutual

/-- Whether a type is built from booleans, integers, byte and bit vectors, vectors, and containers. -/
def plain : Desc → Bool
  | .bool | .uint _ | .byteVector _ | .bitVector _ => true
  | .vector element _ => plain element
  | .container _ fields => plainAll fields
  | _ => false

/-- Whether every type of a list is plain. -/
def plainAll : List Desc → Bool
  | [] => true
  | field :: rest => plain field && plainAll rest

end

/--
The roots of a count of packed values: each value's bytes, split into nodes and folded.

A value of up to 32 bytes is its own root, zero-padded.
-/
def packedRoots (width nodes : Nat) (b : ByteArray) (start stride count : Nat) : ByteArray :=
  let depth := depthFor nodes
  -- Each value gets a block of 2^depth nodes; its padding nodes are zero.
  let slots := gather b start.toUSize stride.toUSize width.toUSize count.toUSize (32 * 2 ^ depth).toUSize
  -- Blocks are aligned powers of two, so every level's pairs stay inside one value.
  (List.range depth).foldl (fun level _ => hashPairs level 0 (level.size / 64).toUSize) slots

/-- The tree over columns, padded with zero-tree levels up to a depth. -/
def columnTreeTo (columns : List ByteArray) (count depth : Nat) : ByteArray :=
  let levels := depthFor columns.length
  climbColumn (columnRoots columns count) count levels (depth - levels)

/-- Whether a fixed-size value's root is its own bytes, zero-padded to one node. -/
def packsIntoNode (d : Desc) : Bool :=
  match d with
  | .bool | .uint _ => true
  | .byteVector length => length ≤ 32
  | .bitVector length => length ≤ 256
  | _ => false

/--
Records one chunk of a long sequence holds.

A chunk's records and their columns then fit in one core's cache, and each chunk is a task of its own.
-/
abbrev recordsPerChunk : Nat := 1024

mutual

/--
The roots of a count of values of a fixed-size type, one every stride bytes from a start.

The result holds the roots back to back, 32 bytes each.
-/
def rootsOf (d : Desc) (b : ByteArray) (start stride count : Nat) : ByteArray :=
  match d with
  | .vector element length =>
    if element.isBasic then packedRoots (fixedWidth d) (nodesFor (fixedWidth d)) b start stride count
    else if count == 1 then
      -- One value: its elements' roots side by side, then their tree.
      merkleizeDepth (chunkedRoots element b start (fixedWidth element) length) length (depthFor length)
    else
      -- One column per element, then the element tree across them.
      let w := fixedWidth element
      columnTreeTo (elementColumns element b start stride count w length) count (depthFor length)
  | .container _ fields =>
    if count == 1 then merkleizeDepth (fieldLeaves fields b start 0 (zeros (32 * fields.length + 32)) 0)
      fields.length (depthFor fields.length)
    else columnTreeTo (fieldColumns fields b start stride count 0) count (depthFor fields.length)
  | _ => packedRoots (fixedWidth d) (nodesFor (fixedWidth d)) b start stride count
termination_by (sizeOf d, 0, 0)

/-- The roots of a long run of values, a chunk of records per task. -/
def chunkedRoots (d : Desc) (b : ByteArray) (start stride count : Nat) : ByteArray :=
  if count ≤ recordsPerChunk then rootsOf d b start stride count
  else
    let chunks := (count + recordsPerChunk - 1) / recordsPerChunk
    let tasks := (List.range chunks).map fun k =>
      Task.spawn fun _ =>
        rootsOf d b (start + stride * recordsPerChunk * k) stride (min recordsPerChunk (count - recordsPerChunk * k))
    -- The parts join in order, with room for one more node at the end.
    tasks.foldl (fun out task => out ++ task.get) (ByteArray.emptyWithCapacity (32 * count + 32))
termination_by (sizeOf d, 1, 0)

/-- The column of each of a sequence's elements, across a count of records. -/
def elementColumns (element : Desc) (b : ByteArray) (start stride count width length : Nat) : List ByteArray :=
  -- Build in element order without repeatedly traversing an already-built column list.
  (List.range length).map fun i => rootsOf element b (start + width * i) stride count
termination_by (sizeOf element, 0, length + 1)

/-- The column of each field, across a count of records. -/
def fieldColumns : List Desc → ByteArray → Nat → Nat → Nat → Nat → List ByteArray
  | [], _, _, _, _, _ => []
  | field :: rest, b, start, stride, count, offset =>
    rootsOf field b (start + offset) stride count ::
      fieldColumns rest b start stride count (offset + fixedWidth field)
termination_by fields => (sizeOf fields, 0, 0)

/-- One record's field roots, written into a buffer of nodes from a given node on. -/
def fieldLeaves : List Desc → ByteArray → Nat → Nat → ByteArray → Nat → ByteArray
  | [], _, _, _, leaves, _ => leaves
  | field :: rest, b, start, offset, leaves, node =>
    -- A field that fits one node is its own bytes, already zero-padded by the buffer.
    let leaves :=
      if packsIntoNode field then b.copySlice (start + offset) leaves (32 * node) (fixedWidth field)
      else (rootsOf field b (start + offset) (fixedWidth field) 1).copySlice 0 leaves (32 * node) 32
    fieldLeaves rest b start (offset + fixedWidth field) leaves (node + 1)
termination_by fields => (sizeOf fields, 0, 0)

end

/-- The number of bits a valid delimited encoding holds. -/
def bitCount (b : ByteArray) (start stop : Nat) : Nat :=
  8 * (stop - start - 1) + highestBit (b.get! (stop - 1))

/-- The nodes a bit list's bits pack into: its bytes without the delimiter bit. -/
def bitNodes (b : ByteArray) (start count : Nat) : ByteArray :=
  let nodes := packRange b start (start + (count + 7) / 8)
  -- The delimiter shares a byte with the last bits only when the count is not a whole number of bytes.
  if count % 8 == 0 then nodes
  else nodes.set! (count / 8) (nodes.get! (count / 8) &&& ~~~((1 : UInt8) <<< UInt8.ofNat (count % 8)))

/-- Element ranges of a counted sequence of variable-size elements, from its offsets. -/
def bodyRanges (b : ByteArray) (start stop count : Nat) : List (Nat × Nat) :=
  let offsets := (List.range count).map fun i => offsetAt b (start + i * bytesPerOffset)
  let ends := offsets.drop 1 ++ [stop - start]
  (offsets.zip ends).map fun (o, e) => (start + o, start + e)

/-- Element ranges of a sequence: one width apart for fixed-size elements, from the offsets otherwise. -/
def elementRanges (element : Desc) (b : ByteArray) (start stop count : Nat) : List (Nat × Nat) :=
  match element.fixedSize with
  | some width => (List.range count).map fun i => (start + i * width, start + (i + 1) * width)
  | none => bodyRanges b start stop count

/-- Nodes back to back, as one buffer with room for one more node, which an odd level needs. -/
def joinNodes (roots : List ByteArray) : ByteArray :=
  roots.foldl (· ++ ·) (ByteArray.emptyWithCapacity (32 * roots.length + 32))

/-- The number of elements a valid encoding of a counted sequence holds. -/
def elementCount (element : Desc) (b : ByteArray) (start stop : Nat) : Nat :=
  let size := stop - start
  match element.fixedSize with
  | some width => if width == 0 then 0 else size / width
  | none => if size == 0 then 0 else offsetAt b start / bytesPerOffset

/-- Field roots placed at a layout's set positions, with zero leaves at its gaps. -/
def placeRoots : List Bool → List ByteArray → List ByteArray
  | [], _ => []
  | false :: active, roots => zeroNode :: placeRoots active roots
  | true :: active, root :: roots => root :: placeRoots active roots
  | true :: active, [] => zeroNode :: placeRoots active []

mutual

/-- The root of the value a valid range of an encoding holds. -/
def rootOf (d : Desc) (b : ByteArray) (start stop : Nat) : ByteArray :=
  let size := stop - start
  match d with
  | .byteList limit =>
    hashPair (merkleizeCapacity (packRange b start stop) (nodesFor size) (nodesFor limit)) (lengthNode size)
  | .bitList limit =>
    let count := bitCount b start stop
    hashPair (merkleizeCapacity (bitNodes b start count) (nodesFor ((count + 7) / 8)) ((limit + 255) / 256))
      (lengthNode count)
  | .progressiveBitList _ =>
    let count := bitCount b start stop
    hashPair (merkleizeProgressive (bitNodes b start count) (nodesFor ((count + 7) / 8))) (lengthNode count)
  | .vector element length =>
    if plain d then rootsOf d b start (fixedWidth d) 1
    else merkleizeCapacity (joinNodes (variableRoots element b (elementRanges element b start stop length)))
      length length
  | .list element limit =>
    let (roots, count, capacity) := sequenceNodes element b start stop limit
    hashPair (merkleizeCapacity roots count capacity) (lengthNode (elementCount element b start stop))
  | .progressiveList element _ =>
    let (roots, count, _) := sequenceNodes element b start stop 0
    hashPair (merkleizeProgressive roots count) (lengthNode (elementCount element b start stop))
  | .container _ fields =>
    if plain d then rootsOf d b start (fixedWidth d) 1
    else
      let ranges := (fieldRanges fields b start stop).toOption.getD []
      merkleizeCapacity (joinNodes (fieldRoots fields b ranges)) fields.length fields.length
  | .progressiveContainer active _ fields =>
    let ranges := (fieldRanges fields b start stop).toOption.getD []
    let roots := fieldRoots fields b ranges
    -- A gap in the layout is a zero leaf.
    let leaves := (placeRoots active roots)
    hashPair (merkleizeProgressive (joinNodes leaves) leaves.length) (activeFieldsNode active)
  | .compatibleUnion selectors options =>
    let selector := (b.get! start).toNat
    hashPair (optionRoot selectors options selector b (start + 1) stop) (lengthNode selector)
  | _ => rootsOf d b start (fixedWidth d) 1
termination_by (sizeOf d, 0, 0)

/-- The nodes under a counted sequence: packed bytes, or element roots, with the capacity of its tree. -/
def sequenceNodes (element : Desc) (b : ByteArray) (start stop limit : Nat) : ByteArray × Nat × Nat :=
  let size := stop - start
  if element.isBasic then (packRange b start stop, nodesFor size, nodesFor (limit * element.itemLength))
  else
    let count := elementCount element b start stop
    -- Plain elements are rooted together, as columns.
    if plain element then (chunkedRoots element b start (fixedWidth element) count, count, limit)
    else (joinNodes (variableRoots element b (elementRanges element b start stop count)), count, limit)
termination_by (sizeOf element, 2, 0)

/-- The roots of variable-size values, one per range. -/
def variableRoots (element : Desc) (b : ByteArray) : List (Nat × Nat) → List ByteArray
  | [] => []
  | (s, e) :: rest => rootOf element b s e :: variableRoots element b rest
termination_by ranges => (sizeOf element, 1, ranges.length)

/-- The root of the option a selector names, searched for so that it stays part of the union's type. -/
def optionRoot : List Nat → List Desc → Nat → ByteArray → Nat → Nat → ByteArray
  | chosen :: selectors, option :: options, selector, b, start, stop =>
    if chosen == selector then rootOf option b start stop
    else optionRoot selectors options selector b start stop
  | _, _, _, _, _, _ => zeroNode
termination_by _ options => (sizeOf options, 0, 0)

/-- The roots of a struct's fields, each from its own range. -/
def fieldRoots : List Desc → ByteArray → List (Nat × Nat) → List ByteArray
  | field :: fields, b, (s, e) :: ranges => rootOf field b s e :: fieldRoots fields b ranges
  | _, _, _ => []
termination_by fields => (sizeOf fields, 0, 0)

end

/--
The SSZ root of the value an encoding holds, or the reason deserialization refuses the encoding.

The type must be well formed; encoding validation does not check declaration legality.
Reference equivalence additionally requires `64 * b.size + 128 < USize.size`.
-/
def hashTreeRoot (d : Desc) (b : ByteArray) : Except Err ByteArray := do
  validate d b
  return rootOf d b 0 b.size

end Ssz.Native
