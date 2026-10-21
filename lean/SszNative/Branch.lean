import SszNative.Root
import Ssz.Codec.Proof

/-!
Nodes, branches, and multiproofs read from an encoding, and their verification.

Each walk is the specification's, with a range of the encoding in place of a value.
A node's subtree is rooted from its own bytes alone, so a branch costs about one root of the value.
-/

namespace Ssz.Native

open Ssz

/-- The values under a tree: fixed-size elements back to back, or listed one by one with gaps. -/
inductive Slots where
  /-- A count of elements of one type, a width apart from a start. -/
  | stride (element : Desc) (start width count : Nat)
  /-- Each position's type and range, or nothing for a gap. -/
  | listed (slots : List (Option (Desc × Nat × Nat)))

/-- Positions the slots hold, gaps included. -/
def Slots.count : Slots → Nat
  | .stride _ _ _ count => count
  | .listed slots => slots.length

/-- The type and range at a position, or nothing for a gap, or no entry past the end. -/
def Slots.at (slots : Slots) (position : Nat) : Option (Option (Desc × Nat × Nat)) :=
  match slots with
  | .stride element start width count =>
    if position < count then some (some (element, start + width * position, start + width * (position + 1)))
    else none
  | .listed slots => slots[position]?

/-- The leaves of a tree read from an encoding: packed nodes and their count, or values with roots of their own. -/
inductive EncodedLeaves where
  /-- Nodes back to back, the data packed into them. -/
  | packed (nodes : ByteArray) (count : Nat)
  /-- Values whose roots are the leaves. -/
  | nested (slots : Slots)

/-- The tree one encoded value merkleizes into: its leaves, their capacity, and the word mixed in. -/
structure EncodedLayout where
  /-- What sits under the tree. -/
  leaves : EncodedLeaves
  /-- Node capacity of the bounded tree, or none for a progressive spine. -/
  limit : Option Nat
  /-- The node the subtree root is hashed against, where the type mixes one in. -/
  mixin : Option ByteArray

/-- Leaves the layout holds, gaps included. -/
def EncodedLayout.count (layout : EncodedLayout) : Nat :=
  match layout.leaves with
  | .packed _ count => count
  | .nested slots => slots.count

/-- The slots of a sequence's elements: back to back when fixed-size, from their offsets otherwise. -/
def elementSlots (element : Desc) (b : ByteArray) (start stop count : Nat) : Slots :=
  match element.fixedSize with
  | some width => .stride element start width count
  | none => .listed ((bodyRanges b start stop count).map fun (s, e) => some (element, s, e))

/-- Fields paired with their ranges, a gap at each inactive position of a layout. -/
def placeFields : List Bool → List (Desc × Nat × Nat) → List (Option (Desc × Nat × Nat))
  | [], _ => []
  | false :: active, fields => none :: placeFields active fields
  | true :: active, field :: fields => some field :: placeFields active fields
  | true :: active, [] => none :: placeFields active []

/-- The packed layout of a count of basic elements, or the nested layout of any other. -/
def encodedSequence (element : Desc) (b : ByteArray) (start stop count : Nat) (positions : Option Nat)
    (mixin : Option ByteArray) : EncodedLayout :=
  if element.isBasic then
    ⟨.packed (packRange b start stop) (nodesFor (stop - start)),
      positions.map fun n => chunksForBytes (n * element.itemLength), mixin⟩
  else ⟨.nested (elementSlots element b start stop count), positions, mixin⟩

/-- The tree a valid range of an encoding merkleizes into. -/
def layoutOf (d : Desc) (b : ByteArray) (start stop : Nat) : Except Err EncodedLayout :=
  let size := stop - start
  match d with
  | .bool | .uint _ | .byteVector _ =>
    .ok ⟨.packed (packRange b start stop) (nodesFor size), some (nodesFor size), none⟩
  | .byteList limit =>
    .ok ⟨.packed (packRange b start stop) (nodesFor size), some (chunksForBytes limit), some (lengthNode size)⟩
  | .bitVector length =>
    .ok ⟨.packed (packRange b start stop) (nodesFor size), some (chunksForBits length), none⟩
  | .bitList limit =>
    let count := bitCount b start stop
    .ok ⟨.packed (bitNodes b start count) (nodesFor ((count + 7) / 8)), some (chunksForBits limit),
      some (lengthNode count)⟩
  | .progressiveBitList _ =>
    let count := bitCount b start stop
    .ok ⟨.packed (bitNodes b start count) (nodesFor ((count + 7) / 8)), none, some (lengthNode count)⟩
  | .vector element length => .ok (encodedSequence element b start stop length (some length) none)
  | .list element limit =>
    let count := elementCount element b start stop
    .ok (encodedSequence element b start stop count (some limit) (some (lengthNode count)))
  | .progressiveList element _ =>
    let count := elementCount element b start stop
    .ok (encodedSequence element b start stop count none (some (lengthNode count)))
  | .container _ fields => do
    let ranges ← fieldRanges fields b start stop
    return ⟨.nested (.listed ((fields.zip ranges).map some)), some fields.length, none⟩
  | .progressiveContainer active _ fields => do
    let ranges ← fieldRanges fields b start stop
    return ⟨.nested (.listed (placeFields active (fields.zip ranges))), none, some (activeFieldsNode active)⟩
  | .compatibleUnion selectors options => do
    let selector := (b.get! start).toNat
    let option ← lookupOption selectors options selector
    return ⟨.nested (.listed [some (option, start + 1, stop)]), some 1, some (lengthNode selector)⟩

/-- The root of one listed position: its range's root, or the zero node for a gap. -/
def listedRoot (b : ByteArray) : Option (Desc × Nat × Nat) → ByteArray
  | some (d, s, e) => rootOf d b s e
  | none => zeroNode

/-- The leaves of a layout from one position to another, as nodes, with how many there are. -/
def leavesIn (b : ByteArray) (layout : EncodedLayout) (first last : Nat) : ByteArray × Nat :=
  let last := min last layout.count
  let count := last - first
  match layout.leaves with
  | .packed nodes _ => (nodes.extract (32 * first) (32 * last), count)
  | .nested (.stride element start width _) =>
    -- Plain elements are rooted together, as columns.
    if plain element then (chunkedRoots element b (start + width * first) width count, count)
    else
      (joinNodes ((List.range count).map fun i =>
        rootOf element b (start + width * (first + i)) (start + width * (first + i + 1))), count)
  | .nested (.listed slots) =>
    (joinNodes (((slots.drop first).take count).map (listedRoot b)), count)

mutual

/--
The root of the node at a generalized index of the tree of a valid range of an encoding.

The budget bounds the walk exactly as the specification's does.
-/
def nodeRootAt : Nat → Desc → ByteArray → Nat → Nat → Nat → Except Err ByteArray
  | 0, _, _, _, _, _ => .error .proofIncomplete
  | budget + 1, d, b, start, stop, index => do
    if index < 1 then throw (.notAGindex index)
    -- The root sits on no branch, but it is still a node.
    if index == 1 then return rootOf d b start stop
    let layout ← layoutOf d b start stop
    let full ← gindexLength index
    -- A mixed-in word is the right child, which puts the contents one level down on the left.
    let depth := if layout.mixin.isSome then full - 1 else full
    match layout.mixin with
    | some word =>
      if gindexBit index depth then
        -- A word is one leaf, so a turn below it descends into something with no parts.
        if depth != 0 then throw .pathIntoMixin
        return word
    | none => pure ()
    match layout.limit with
    | some capacity => boundedNode budget b layout index depth 0 capacity
    | none => progressiveNode budget b layout index depth 0 1
termination_by budget => (budget, 0)

/-- The root of a node of a bounded subtree, or of a node inside one of its leaves. -/
def boundedNode (budget : Nat) (b : ByteArray) (layout : EncodedLayout)
    (index depth leavesFrom capacity : Nat) : Except Err ByteArray := do
  let width := nextPow2 capacity
  let treeDepth := Nat.log2 width
  if depth ≤ treeDepth then
    -- Each turn halves the run of leaves a node spans.
    let span := width >>> depth
    let first := leavesFrom + gindexBelow index depth * span
    let (nodes, count) := leavesIn b layout first (first + span)
    return merkleizeDepth nodes count (depthFor span)
  else
    -- Past the bottom of this subtree, the remaining turns are read inside one leaf.
    let below := depth - treeDepth
    let leaf := leavesFrom + gindexBelow (index >>> below) treeDepth
    match layout.leaves with
    | .packed _ _ => throw .pathIntoPacked
    | .nested slots =>
      match slots.at leaf with
      | some (some (d, s, e)) => nodeRootAt budget d b s e (gindexRebase index below)
      | _ => throw .pathIntoGap
termination_by (budget, 1)

/-- A progressive walk reads either a bounded level or the remaining spine. -/
def progressiveNode (budget : Nat) (b : ByteArray) (layout : EncodedLayout)
    (index depth start capacity : Nat) : Except Err ByteArray := do
  let stop ← spineWalk layout.count index depth start capacity
  if stop.turnedLeft then boundedNode budget b layout index stop.depth stop.leavesFrom stop.capacity
  else
    -- Stopping on the spine covers the whole remaining suffix, zero terminator included.
    let (nodes, count) := leavesIn b layout stop.leavesFrom layout.count
    return merkleizeProgressive nodes count stop.capacity
termination_by (budget, 2)

end

/-- The root of the node at a generalized index of the value an encoding holds. -/
def nodeRoot (d : Desc) (b : ByteArray) (index : Nat) : Except Err ByteArray := do
  validate d b
  nodeRootAt (d.nesting + index) d b 0 b.size index

/-- The branch that authenticates one generalized index of the value an encoding holds. -/
def buildProof (d : Desc) (b : ByteArray) (index : Nat) : Except Err (List ByteArray) := do
  validate d b
  (← getBranchIndices index).mapM fun node => nodeRootAt (d.nesting + node) d b 0 b.size node

/-- The nodes that authenticate several generalized indices of the value an encoding holds. -/
def buildMultiproof (d : Desc) (b : ByteArray) (indices : List Nat) : Except Err (List ByteArray) := do
  validate d b
  (← getHelperIndices indices).mapM fun node => nodeRootAt (d.nesting + node) d b 0 b.size node

/-- Two nodes joined into their parent, on the native kernels when both are whole nodes. -/
def combine (left right : ByteArray) : ByteArray :=
  if left.size == 32 && right.size == 32 then hashColumns left 0 right 0 1
  else ⟨Ssz.combine left.data right.data⟩

/-- Refuses a hash operand that is not one whole node. -/
def checkNode (node : ByteArray) : Except Err Unit :=
  if node.size = bytesPerChunk then .ok () else .error (.count bytesPerChunk node.size)

/-- Refuses a list holding a node of the wrong width. -/
def checkNodes : List ByteArray → Except Err Unit
  | [] => .ok ()
  | node :: rest => do
    checkNode node
    checkNodes rest

/-- A node joined with each branch node in turn, from the leaf upward. -/
def climbBranch (index : Nat) : (level : Nat) → (node : ByteArray) → List ByteArray → ByteArray
  | _, node, [] => node
  | level, node, sibling :: rest =>
    -- A set bit puts this node on the right, so the branch node joins on the left.
    let parent := if gindexBit index level then combine sibling node else combine node sibling
    climbBranch index (level + 1) parent rest

/-- Whether one leaf and its branch rebuild the expected root. -/
def verifyMerkleProof (leaf : ByteArray) (proof : List ByteArray) (index : Nat) (root : ByteArray) :
    Except Err Bool := do
  -- A short node and a long one must not pass as two whole nodes.
  checkNode leaf
  checkNode root
  checkNodes proof
  let depth ← gindexLength index
  if proof.length != depth then throw (.branchLength depth proof.length)
  return climbBranch index 0 leaf proof == root

/-- The node held at an index, where one is held. -/
def nodeAt (nodes : List (Nat × ByteArray)) (index : Nat) : Option ByteArray :=
  (nodes.find? fun (tableEntry, _) => tableEntry == index).map fun (_, node) => node

/-- One level's parents and shallower nodes, kept in their original order. -/
def foldLevelNodes (depth : Nat) (nodes : List (Nat × ByteArray)) :
    List (Nat × ByteArray) → Except Err (List (Nat × ByteArray) × List (Nat × ByteArray))
  | [] => .ok ([], [])
  | (index, node) :: rest => do
    if levelOf index != depth then
      -- A shallower node waits until the walk reaches its level.
      let (parents, kept) ← foldLevelNodes depth nodes rest
      return (parents, (index, node) :: kept)
    else if index % 2 == 0 then
      -- An even index owns the pair, with the odd index on its right.
      match nodeAt nodes (index + 1) with
      | some sibling =>
        let (parents, kept) ← foldLevelNodes depth nodes rest
        return ((gindexParent index, combine node sibling) :: parents, kept)
      | none => throw .proofIncomplete
    else if (nodeAt nodes (index - 1)).isNone then throw .proofIncomplete
    else foldLevelNodes depth nodes rest

/-- A node set folded upward one level at a time, until only the root is left. -/
def foldToRoot : Nat → List (Nat × ByteArray) → Except Err ByteArray
  | 0, nodes =>
    match nodeAt nodes 1 with
    | some root => .ok root
    | none => .error .proofIncomplete
  | depth + 1, nodes => do
    let (parents, kept) ← foldLevelNodes (depth + 1) nodes nodes
    foldToRoot depth (parents ++ kept)

/-- Whether several leaves and their nodes rebuild the expected root. -/
def verifyMerkleMultiproof (leaves proof : List ByteArray) (indices : List Nat) (root : ByteArray) :
    Except Err Bool := do
  checkNode root
  checkNodes leaves
  checkNodes proof
  if leaves.length != indices.length then throw (.leafCount indices.length leaves.length)
  let helpers ← getHelperIndices indices
  if proof.length != helpers.length then throw (.proofLength helpers.length proof.length)
  let nodes := indices.zip leaves ++ helpers.zip proof
  -- No node sits below the deepest index given, so that is where the fold starts.
  let deepest := (nodes.map fun (index, _) => levelOf index).foldl max 0
  return (← foldToRoot deepest nodes) == root

end Ssz.Native
