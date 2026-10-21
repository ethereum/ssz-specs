import SszNative.Proofs.Root.Variable.Basics
import SszNative.Proofs.Root.Variable.Layout
import Ssz.Proofs.Merkle.Merkleize
import Ssz.Proofs.Merkle.Widths

/-! What the trees and the fixed-size roots are proved to compute, gathered as the facts the remaining roots rest on. -/

namespace Ssz.Native.RootProof

open Ssz Ssz.Native

/-- Whether an encoding is small enough that every buffer its root builds has machine-sized offsets. -/
def Small (b : ByteArray) : Prop :=
  64 * b.size + 128 < USize.size

/-- Whether each of a count of records, one stride apart, lies inside the encoding and decodes. -/
def RecordsDecode (d : Desc) (b : ByteArray) (start stride count : Nat) : Prop :=
  ∀ i < count, start + stride * i + fixedWidth d ≤ b.size ∧
    ∃ v, deserialize d (slice b (start + stride * i) (start + stride * i + fixedWidth d)) = .ok v

/-- Whether a buffer holds, node by node, the roots of a count of records one stride apart. -/
def RootsMatch (d : Desc) (b : ByteArray) (start stride count : Nat) (roots : ByteArray) : Prop :=
  roots.size = 32 * count ∧ ∀ i < count, ∀ v,
    deserialize d (slice b (start + stride * i) (start + stride * i + fixedWidth d)) = .ok v →
      Ssz.hashTreeRoot d v = .ok (roots.extract (32 * i) (32 * i + 32)).data

/-- What the trees and the fixed-size roots compute, in the specification's terms. -/
structure Facts : Prop where
  /-- A tree over nodes from an offset is the specification's perfect tree over them. -/
  merkleizeAt : ∀ (nodes : ByteArray) (offset count depth : Nat), count ≤ 2 ^ depth →
    offset + 32 * count ≤ nodes.size → (count = 0 ∨ nodes.size < USize.size) →
    (Native.merkleizeAt nodes offset count depth).data = subtreeAt (nodesFrom nodes offset count) depth 0
  /-- A progressive tree over the first nodes is the specification's progressive tree over them. -/
  progressive : ∀ (nodes : ByteArray) (count : Nat), 32 * count ≤ nodes.size →
    (count = 0 ∨ nodes.size < USize.size) →
    (Native.merkleizeProgressive nodes count).data = Ssz.merkleizeProgressive (nodesFrom nodes 0 count).toList
  /-- A count's node is the specification's length word. -/
  lengthNode : ∀ count, (lengthNode count).data = lengthWord count
  /-- A layout's node is the specification's active-fields word. -/
  activeFields : ∀ active, (activeFieldsNode active).data = activeFieldsWord active
  /-- Fixed-size records are rooted, many at a time, to the specification's roots. -/
  rootsOf : ∀ d, plain d = true → d.wellFormed = .ok () → ∀ b start stride count, Small b →
    1 ≤ count → stride = fixedWidth d → RecordsDecode d b start stride count → RootsMatch d b start stride count (rootsOf d b start stride count)
  /-- The same, a chunk of records per task. -/
  chunkedRoots : ∀ d, plain d = true → d.wellFormed = .ok () → ∀ b start stride count, Small b →
    1 ≤ count → stride = fixedWidth d → RecordsDecode d b start stride count → RootsMatch d b start stride count (chunkedRoots d b start stride count)

variable (facts : Facts)

/-- Nodes for a byte count are the specification's node count. -/
theorem nodesFor_eq (n : Nat) : nodesFor n = chunksForBytes n := by
  -- Both round a byte count up to whole 32-byte nodes.
  simp [nodesFor, chunksForBytes]

/-- Every node bytes pack into is a whole node. -/
theorem packBytes_width (data : Bytes) : ∀ chunk ∈ packBytes data, chunk.size = bytesPerChunk := by
  -- Each packed node is cut to a whole node, and padded where the data runs out.
  intro chunk member
  obtain ⟨i, within, rfl⟩ := Array.mem_iff_getElem.mp member
  exact packBytes_chunk_size data i within

/-- A bounded root over whole nodes is one node. -/
theorem bounded_size {chunks : Array Bytes} {capacity : Nat} {root : Bytes}
    (complete : ∀ chunk ∈ chunks, chunk.size = bytesPerChunk)
    (made : merkleizeBounded chunks (some capacity) = .ok root) : root.size = 32 :=
  merkleizeBounded_size complete made

/-- A buffer's size is the size of the bytes it holds. -/
theorem size_of_data {x : ByteArray} {r : Bytes} (same : x.data = r) : x.size = r.size := by
  -- A buffer's size is its data's size.
  rw [← ByteArray.size_data, same]

/-- A root hashed with the word it mixes in is the specification's mix-in. -/
theorem hashPair_mixIn {root word : ByteArray} {r w : Bytes} (hr : root.data = r) (hw : word.data = w)
    (rs : r.size = 32) (ws : w.size = 32) : (hashPair root word).data = mixIn r w := by
  -- Both hash the two 32-byte nodes joined.
  rw [hashPair_data root word (by rw [size_of_data hr, rs]) (by rw [size_of_data hw, ws]), hr, hw, mixIn]

include facts in
/-- The bounded tree over buffered nodes is the specification's bounded tree. -/
theorem bounded_root (nodes : ByteArray) (count capacity : Nat) (chunks : Array Bytes)
    (same : nodesFrom nodes 0 count = chunks) (room : count ≤ capacity) (inside : 32 * count ≤ nodes.size)
    (small : count = 0 ∨ nodes.size < USize.size) :
    merkleizeBounded chunks (some capacity) = .ok (merkleizeCapacity nodes count capacity).data := by
  -- The buffer holds exactly the count of nodes, which the capacity's tree has room for.
  have sized : chunks.size = count := by rw [← same]; simp [nodesFrom]
  have fits : count ≤ 2 ^ depthFor capacity := Nat.le_trans room (le_two_pow_depthFor capacity)
  simp only [merkleizeBounded, sized, show ¬ capacity < count by omega, if_false, Bind.bind, Except.bind,
    pure, Except.pure, merkleizeCapacity, merkleizeDepth]
  -- The native tree is the specification's tree over those nodes.
  rw [facts.merkleizeAt nodes 0 count _ fits (by omega) small, same]

include facts in
/-- The progressive tree over buffered nodes is the specification's progressive tree. -/
theorem progressive_root (nodes : ByteArray) (count : Nat) (chunks : Array Bytes)
    (same : nodesFrom nodes 0 count = chunks) (inside : 32 * count ≤ nodes.size)
    (small : count = 0 ∨ nodes.size < USize.size) :
    (Native.merkleizeProgressive nodes count).data = Ssz.merkleizeProgressive chunks.toList := by
  -- The native spine is the specification's spine over those nodes.
  rw [facts.progressive nodes count inside small, same]

end Ssz.Native.RootProof
