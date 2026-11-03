import SszNative.Branch
import EthLib.Consensus.Ssz.Type.Valid

/-!
Declarations compiled once, so that each value read against them skips walking the declaration again.

A struct of fixed-size fields compiles to its width, its probes, and where each field's leaf comes from.
Its root is then a handful of copies and one hashing call per tree level.
Every other declaration keeps the general path.
-/

namespace EthLib.Consensus.Ssz.Native

open EthLib.Consensus.Ssz

/-- Where one leaf of a fixed-size struct comes from. -/
inductive Leaf where
  /-- A field that is its own root: its bytes, zero-padded to one node. -/
  | bytes (offset width : Nat)
  /-- A field with a tree of its own, rooted from its bytes. -/
  | nested (d : Desc) (offset width : Nat)

/-- The cache compiled for a fixed-size struct. -/
structure FixedStruct where
  /-- The encoding's width in bytes. -/
  width : Nat
  /-- Whether deserializing it first bounds its size by what four-byte offsets can name. -/
  composite : Bool
  /-- The bytes a value can be refused for, as runs over records, in the order deserialization reads them. -/
  runs : List ProbeRun
  /-- Each field's leaf, in order. -/
  leaves : Array Leaf
  /-- The height of the tree over the leaves. -/
  depth : Nat

/-- The leaves of a struct's fields, from an offset on. -/
def leavesOf : List Desc → Nat → List Leaf
  | [], _ => []
  | field :: rest, offset =>
    let leaf := if packsIntoNode field then Leaf.bytes offset (fixedWidth field)
      else Leaf.nested field offset (fixedWidth field)
    leaf :: leavesOf rest (offset + fixedWidth field)

/--
The cache for a declaration, when it is a struct of fixed-size fields.

It does not check that the declaration is legal.
-/
def fixedOf (d : Desc) : Option FixedStruct :=
  match d with
  | .container _ fields =>
    if plain d then
      some {
        width := fixedWidth d
        composite := composite d
        runs := runs d
        leaves := (leavesOf fields 0).toArray
        depth := depthFor fields.length }
    else none
  | _ => none

/--
A declaration with a cached plan for reading its encodings.

The cache is always the one its declaration compiles to.
A cache built by hand cannot be paired with a declaration it does not match.
-/
structure Schema where
  /-- The declaration. -/
  desc : Desc
  /-- The compiled struct, when the declaration is a struct of fixed-size fields. -/
  fixed : Option FixedStruct
  /-- The cache is the declaration's own. -/
  compiled : fixed = fixedOf desc

/--
Compiles a declaration, without checking that it is legal.

Encoding validation still agrees with deserialization for every declaration.
Roots and proofs agree with the specification only for a legal one.
-/
def Schema.compile (d : Desc) : Schema :=
  { desc := d, fixed := fixedOf d, compiled := rfl }

/--
A compiled declaration known to be legal.

Its legality is checked once, when it is built.
Reading values against it never checks the declaration again.
-/
structure Checked where
  /-- The compiled declaration. -/
  schema : Schema
  /-- The declaration is legal. -/
  sound : schema.desc.wellFormed = .ok ()

/-- Compiles a declaration after checking it is legal, or reports why it is not. -/
def Checked.compile (d : Desc) : Except Err Checked :=
  match sound : d.wellFormed with
  | .ok () => .ok { schema := Schema.compile d, sound }
  | .error e => .error e

/-- Zero nodes enough for any struct's leaves, copied rather than built for each value. -/
def zeroLeaves : ByteArray :=
  zeros (32 * 65)

/-- One record's leaves, written into a buffer of zero nodes. -/
def fillLeaves (b : ByteArray) (leaves : Array Leaf) : ByteArray :=
  -- Room for every leaf and one more node, which an odd level needs.
  let size := 32 * leaves.size + 32
  let buffer := if size ≤ zeroLeaves.size then zeroLeaves.extract 0 size else zeros size
  (leaves.foldl (fun (acc : ByteArray × Nat) leaf =>
    let (buffer, node) := acc
    match leaf with
    | .bytes offset width => (b.copySlice offset buffer (32 * node) width, node + 1)
    | .nested d offset width => ((rootsOf d b offset width 1).copySlice 0 buffer (32 * node) 32, node + 1))
    (buffer, 0)).1

/--
A short level of nodes folded the remaining levels up, from a given height.

The level is owned and has room for one more node.
An odd level therefore takes its zero tree in place, and each level is one hashing call.
-/
def foldShort (level : ByteArray) (width height : Nat) : (remaining : Nat) → ByteArray
  | 0 => if level.size == 32 then level else level.extract 0 32
  | remaining + 1 =>
    if width ≤ 1 then climb (level.extract 0 32) height (remaining + 1)
    else
      let padded := if width % 2 == 1 then (zeroRoot height).copySlice 0 level (32 * width) 32 else level
      foldShort (hashPairs padded 0 ((width + 1) / 2).toUSize) ((width + 1) / 2) (height + 1) remaining

/--
Refuses exactly the encodings deserialization refuses.

This checks encoding bytes, not whether the declaration is legal.
-/
def Schema.validate (s : Schema) (b : ByteArray) : Except Err Unit :=
  match s.fixed with
  | some f =>
    let size := b.size
    if f.composite && size ≥ 4294967296 then .error (.offsetOverflow size)
    else if size != f.width then .error (.scope f.width size)
    else checkRuns b 0 f.runs
  | none => Native.validate s.desc b

/--
Roots an encoding already accepted, without checking it.

It agrees with the specification for a legal declaration.
The encoding must also satisfy `64 * b.size + 128 < USize.size`.
-/
def Schema.rootOf (s : Schema) (b : ByteArray) : ByteArray :=
  match s.fixed with
  | some f => foldShort (fillLeaves b f.leaves) f.leaves.size 0 f.depth
  | none => Native.rootOf s.desc b 0 b.size

/--
Roots an encoding, or reports why it is refused.

It agrees with the specification for a legal declaration.
The encoding must also satisfy `64 * b.size + 128 < USize.size`.
Validating the encoding does not check either premise.
-/
def Schema.hashTreeRoot (s : Schema) (b : ByteArray) : Except Err ByteArray := do
  s.validate b
  return s.rootOf b

/-- Refuses exactly the encodings deserialization refuses. -/
@[inline] def Checked.validate (c : Checked) (b : ByteArray) : Except Err Unit :=
  c.schema.validate b

/--
Roots an encoding, or reports why it is refused.

It agrees with the specification for an encoding with `64 * b.size + 128 < USize.size`.
-/
@[inline] def Checked.hashTreeRoot (c : Checked) (b : ByteArray) : Except Err ByteArray :=
  c.schema.hashTreeRoot b

end EthLib.Consensus.Ssz.Native
