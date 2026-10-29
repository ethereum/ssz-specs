import SszNative.Hash
import Ssz.Merkle.Merkleize

/-!
Merkle trees over buffers of 32-byte nodes.

A level is one call to the hashing kernels.
A wide tree is split into subtrees, one task each.
Tasks are pure, so a parallel tree is the sequential tree by definition.
-/

namespace Ssz.Native

/-- The all-zero node. -/
def zeroNode : ByteArray :=
  ⟨Array.replicate 32 0⟩

/-- Zero trees cached, enough for any capacity a 64-bit count can reach. -/
abbrev cachedHeights : Nat := 64

/-- The roots of the all-zero trees of heights 0 to h, 32 bytes each. -/
def zeroTable : Nat → ByteArray
  | 0 => zeroNode
  | h + 1 =>
    -- Each height is the one below hashed with itself.
    let table := zeroTable h
    let below := table.extract (32 * h) (32 * h + 32)
    table ++ hashPairs (below ++ below) 0 1

/-- The roots of the all-zero trees of heights 0 to 64, one buffer each. -/
def zeroRoots : Array ByteArray :=
  let table := zeroTable cachedHeights
  (Array.range (cachedHeights + 1)).map fun h => table.extract (32 * h) (32 * h + 32)

/-- The root of the all-zero tree of a given height. -/
def zeroRoot (height : Nat) : ByteArray :=
  if height ≤ cachedHeights then zeroRoots[height]!
  else (zeroTable height).extract (32 * height) (32 * height + 32)

/-- A node climbed a number of levels, each against the zero tree of its height. -/
def climb (node : ByteArray) (height : Nat) : (levels : Nat) → ByteArray
  | 0 => node
  | levels + 1 => climb (hashFixed node 0 (zeroRoot height) 1) (height + 1) levels

/--
The parents of a level of nodes from an offset.

An odd level's last node is hashed against the zero tree of its height.
-/
def parentsOf (level : ByteArray) (offset width height : Nat) : ByteArray :=
  let parents := hashPairs level offset.toUSize (width / 2).toUSize
  if width % 2 == 0 then parents
  else parents ++ hashFixed level (offset + 32 * (width - 1)).toUSize (zeroRoot height) 1

/-- A level of nodes from an offset folded the remaining levels up, from a given height. -/
def fold (level : ByteArray) (offset width height : Nat) : (remaining : Nat) → ByteArray
  | 0 => level.extract offset (offset + 32)
  | remaining + 1 =>
    -- A lone node climbs the rest of the way against zero trees.
    if width ≤ 1 then climb (level.extract offset (offset + 32)) height (remaining + 1)
    else fold (parentsOf level offset width height) 0 ((width + 1) / 2) (height + 1) remaining

/--
The height of the subtrees one task builds.

A task then hashes about two thousand pairs, far above the cost of starting it.
-/
abbrev taskHeight : Nat := 11

/--
The root of the perfect tree of a given depth over nodes from an offset, padded with zeros.

A wide tree is split into aligned subtrees built in parallel, then the levels above them.
The count must fit the depth.
-/
def merkleizeAt (nodes : ByteArray) (offset count depth : Nat) : ByteArray :=
  let width := 2 ^ taskHeight
  if count == 0 then zeroRoot depth
  else if count ≤ width || depth ≤ taskHeight then fold nodes offset count 0 depth
  else
    -- Subtree k holds nodes from k * width, and only the last may be partial.
    let parts := (count + width - 1) / width
    let tasks := (List.range parts).map fun k =>
      Task.spawn fun _ => fold nodes (offset + 32 * width * k) (min width (count - width * k)) 0 taskHeight
    let roots := tasks.foldl (fun out task => out ++ task.get) (ByteArray.emptyWithCapacity (32 * parts + 32))
    fold roots 0 parts taskHeight (depth - taskHeight)

/-- The root of the perfect tree of a given depth over the first nodes of a buffer, padded with zeros. -/
def merkleizeDepth (nodes : ByteArray) (count depth : Nat) : ByteArray :=
  merkleizeAt nodes 0 count depth

/-- The root of the tree a capacity calls for, over the first nodes of a buffer. -/
def merkleizeCapacity (nodes : ByteArray) (count capacity : Nat) : ByteArray :=
  merkleizeDepth nodes count (depthFor capacity)

/-- The spine of a progressive tree over nodes from a start, with the current level's width. -/
def spine (nodes : ByteArray) (count start width : Nat) : (fuel : Nat) → ByteArray
  | 0 => zeroNode
  | fuel + 1 =>
    -- The spine closes with a zero node once the nodes run out.
    if count ≤ start then zeroNode
    else
      let here := min width (count - start)
      let subtree := merkleizeAt nodes (32 * start) here (Nat.log2 width)
      hashPair subtree (spine nodes count (start + width) (4 * width) fuel)

/--
The root of the progressive tree over the first nodes of a buffer (EIP-7916).

The spine holds subtrees of 1, 4, 16, and so on nodes, from a given starting width, and closes with a zero node.
-/
def merkleizeProgressive (nodes : ByteArray) (count : Nat) (width : Nat := 1) : ByteArray :=
  -- Every level holds at least one node, so the count bounds the levels.
  spine nodes count 0 width (count + 1)

/-- A count as one little-endian node, keeping its low 256 bits. -/
def lengthNode (count : Nat) : ByteArray :=
  ⟨(Array.range 32).map fun i => UInt8.ofNat (count >>> (8 * i))⟩

/-- A progressive container's layout, one bit per position from the lowest, as one node. -/
def activeFieldsNode (active : List Bool) : ByteArray :=
  ⟨(Array.range 32).map fun byte =>
    (List.range 8).foldl (fun acc bit =>
      if active.getD (8 * byte + bit) false then acc ||| ((1 : UInt8) <<< UInt8.ofNat bit) else acc) 0⟩

end Ssz.Native
