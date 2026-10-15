import Asm.Root.Spec

/-!
A hash plan: the fixed sequence of chunk and hash steps that roots one plain type.

A plan runs over a scratch area holding the encoding at offset 0.

```text
    [ encoding | zero subtrees z_0 .. z_D | chunks and parents, each written once ]
```

Every step writes one fresh 32-byte slot, so nothing a later step reads is overwritten.
-/

namespace Ssz.Asm.Root

open Ssz

/-- One step of a plan, with offsets into the scratch area. -/
inductive Step where
  /-- Copy a run of at most 32 bytes into a slot, zero-filling the rest of it. -/
  | chunk (dst src len : Nat)
  /-- Hash two 32-byte slots, left then right, into a slot. -/
  | hash (dst left right : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- The scratch area, byte by byte. -/
abbrev Scratch := Nat → UInt8

/-- The 32 bytes at an offset. -/
def readSlot (s : Scratch) (offset : Nat) : Bytes :=
  Array.ofFn (n := 32) fun i => s (offset + i.val)

/-- The slot a step writes. -/
def Step.dst : Step → Nat
  | chunk dst _ _ => dst
  | hash dst _ _ => dst

/-- What a step leaves in the scratch area. -/
def Step.run : Step → Scratch → Scratch
  | chunk dst src len, s => fun a =>
    if dst ≤ a ∧ a < dst + 32 then (if a - dst < len then s (src + (a - dst)) else 0) else s a
  | hash dst left right, s => fun a =>
    if dst ≤ a ∧ a < dst + 32 then (combine (readSlot s left) (readSlot s right))[a - dst]! else s a

/-- A whole plan, step after step. -/
def runPlan (steps : List Step) (s : Scratch) : Scratch :=
  steps.foldl (fun s step => step.run s) s

mutual

/-- Levels of tree a plain type needs, at its own node and below. -/
def treeDepth : Desc → Nat
  | .vector element n =>
    if element.isBasic then depthFor ((width element * n + 31) / 32)
    else max (depthFor n) (treeDepth element)
  | .container _ fields => max (depthFor fields.length) (treeDepthAll fields)
  | d => depthFor ((width d + 31) / 32)

/-- The most levels any of a list of types needs. -/
def treeDepthAll : List Desc → Nat
  | [] => 0
  | field :: fields => max (treeDepth field) (treeDepthAll fields)

end

/-- Steps building the zero subtrees of heights 0 to D at consecutive slots from a base. -/
def zeroSteps (zeros : Nat) : Nat → List Step
  | 0 => [.chunk zeros 0 0]
  | k + 1 => zeroSteps zeros k ++ [.hash (zeros + 32 * (k + 1)) (zeros + 32 * k) (zeros + 32 * k)]

/-- Steps folding one level of a tree: parent i of the nodes at the given offsets, at consecutive slots. -/
def pairSteps (fill : Nat) (free : Nat) : List Nat → List Step × List Nat
  | [] => ([], [])
  | [node] => ([.hash free node fill], [free])
  | left :: right :: rest =>
    (.hash free left right :: (pairSteps fill (free + 32) rest).1,
      free :: (pairSteps fill (free + 32) rest).2)

/-- Steps emitted for one node, where its root ends up, and the next free offset. -/
structure Emitted where
  /-- The steps, in order. -/
  steps : List Step
  /-- Offset of the slot holding the root. -/
  root : Nat
  /-- Next free offset. -/
  free : Nat

/-- Steps emitted for several nodes, where their roots end up, and the next free offset. -/
structure EmittedMany where
  /-- The steps, in order. -/
  steps : List Step
  /-- Offsets of the slots holding the roots, in order. -/
  roots : List Nat
  /-- Next free offset. -/
  free : Nat

/-- Steps folding a level of nodes up to the top of a tree with the given number of levels left. -/
def treeSteps (zeros : Nat) : (remaining height : Nat) → List Nat → Nat → Emitted
  | 0, height, nodes, free => ⟨[], nodes.headD (zeros + 32 * height), free⟩
  | remaining + 1, height, nodes, free =>
    let level := pairSteps (zeros + 32 * height) free nodes
    let rest := treeSteps zeros remaining (height + 1) level.2 (free + 32 * level.2.length)
    ⟨level.1 ++ rest.steps, rest.root, rest.free⟩

/-- Steps chunking packed bytes: chunk i holds bytes 32i to 32i + 31, zero-padded. -/
def chunkSteps (src size free : Nat) : List Step :=
  (List.range ((size + 31) / 32)).map fun i => .chunk (free + 32 * i) (src + 32 * i) (min 32 (size - 32 * i))

/-- Offsets of the chunks the chunk steps write. -/
def chunkSlots (size free : Nat) : List Nat :=
  (List.range ((size + 31) / 32)).map fun i => free + 32 * i

/-- Steps rooting packed bytes: chunk them, then fold the chunks into a tree just wide enough. -/
def packedSteps (zeros src size free : Nat) : Emitted :=
  let count := (size + 31) / 32
  let tree := treeSteps zeros (depthFor count) 0 (chunkSlots size free) (free + 32 * count)
  ⟨chunkSteps src size free ++ tree.steps, tree.root, tree.free⟩

mutual

/-- Steps rooting a plain type whose encoding starts at an offset. -/
def compile (zeros : Nat) : Desc → Nat → Nat → Emitted
  | .vector element n, src, free =>
    if element.isBasic then packedSteps zeros src (width element * n) free
    else
      let each := compileEach zeros element n src free
      let tree := treeSteps zeros (depthFor n) 0 each.roots each.free
      ⟨each.steps ++ tree.steps, tree.root, tree.free⟩
  | .container _ fields, src, free =>
    let each := compileFields zeros fields src free
    let tree := treeSteps zeros (depthFor fields.length) 0 each.roots each.free
    ⟨each.steps ++ tree.steps, tree.root, tree.free⟩
  | d, src, free => packedSteps zeros src (width d) free

/-- Steps rooting n consecutive elements of one type. -/
def compileEach (zeros : Nat) (element : Desc) : Nat → Nat → Nat → EmittedMany
  | 0, _, free => ⟨[], [], free⟩
  | n + 1, src, free =>
    let first := compile zeros element src free
    let rest := compileEach zeros element n (src + width element) first.free
    ⟨first.steps ++ rest.steps, first.root :: rest.roots, rest.free⟩

/-- Steps rooting consecutive fields. -/
def compileFields (zeros : Nat) : List Desc → Nat → Nat → EmittedMany
  | [], _, free => ⟨[], [], free⟩
  | field :: fields, src, free =>
    let first := compile zeros field src free
    let rest := compileFields zeros fields (src + width field) first.free
    ⟨first.steps ++ rest.steps, first.root :: rest.roots, rest.free⟩

end

/--
The plan for a plain type, the root's offset, and the scratch size it needs.

The encoding sits at offset 0, followed by the zero subtrees the plan's trees can reach.
-/
def planFor (d : Desc) : Emitted :=
  let zeros := width d
  let depth := treeDepth d
  let body := compile zeros d 0 (zeros + 32 * (depth + 1))
  ⟨zeroSteps zeros depth ++ body.steps, body.root, body.free⟩

end Ssz.Asm.Root
