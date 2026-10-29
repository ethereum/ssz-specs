import SszNative.Proofs.Root.Variable.Bits
import Ssz.Proofs.Codec.DecodeFits

/-! Roots of byte lists and bit lists: packed bytes under a tree, with the count mixed in. -/

namespace Ssz.Native.RootProof

open Ssz Ssz.Native

variable (facts : Facts)

include facts in
/-- A byte list's root is the specification's. -/
theorem byteList_root (limit : Nat) (b : ByteArray) (start stop : Nat) (v : Value) (ordered : start ≤ stop)
    (inside : stop ≤ b.size) (small : Small b) (read : deserialize (.byteList limit) (slice b start stop) = .ok v) :
    Ssz.hashTreeRoot (.byteList limit) v = .ok (rootOf (.byteList limit) b start stop).data := by
  have size := slice_size b start stop inside
  -- Decoding keeps the bytes, which fit the limit.
  simp only [deserialize, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  split at read
  · cases read
  rename_i bound
  cases read
  have packed := packRange_nodes b start stop ordered inside (by unfold Small at small; omega)
  rw [hashTreeRoot_unfold]
  simp only [merkleLayout, bound, if_false, MerkleLayout.packing, leafChunks, finishLayout, Bind.bind,
    Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  -- The packed range holds the slice's nodes, within the limit's capacity.
  have room : nodesFor (stop - start) ≤ chunksForBytes limit := by
    rw [nodesFor_eq]; exact Nat.div_le_div_right (by omega)
  have tree := bounded_root facts (packRange b start stop) _ _ (packBytes (slice b start stop)) packed.1 room
    (by omega) (Or.inr (by unfold Small at small; simp only [nodesFor] at packed; omega))
  rw [tree, rootOf]
  simp only [size, nodesFor_eq limit]
  rw [hashPair_mixIn (rfl) (facts.lengthNode _) (bounded_size (packBytes_width _) tree) (by simp)]

/-- Every node of packed bits is a whole node. -/
theorem packedBits_width (bits : Array Bool) : ∀ chunk ∈ packedBits bits, chunk.size = bytesPerChunk :=
  packBytes_width _

include facts in
/-- A bit list's root is the specification's. -/
theorem bitList_root (limit : Nat) (b : ByteArray) (start stop : Nat) (v : Value) (ordered : start ≤ stop)
    (inside : stop ≤ b.size) (small : Small b) (read : deserialize (.bitList limit) (slice b start stop) = .ok v) :
    Ssz.hashTreeRoot (.bitList limit) v = .ok (rootOf (.bitList limit) b start stop).data := by
  -- Decoding recovers the bits below the closing bit.
  simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i bits decoded
  cases read
  have bound := unpackDelimited_bound decoded
  obtain ⟨counted, nodes, sized⟩ :=
    bitNodes_nodes b start stop ordered inside (by unfold Small at small; omega) _ bits decoded
  have few : bits.size ≤ 8 * (stop - start) := by
    have nonempty := (unpackDelimited_ok decoded).1
    rw [slice_size b start stop inside] at nonempty
    rw [← counted]; simp only [bitCount]; have := highest_lt (b.get! (stop - 1)); omega
  rw [hashTreeRoot_unfold]
  simp only [merkleLayout, show ¬ bits.size > limit by omega, if_false, MerkleLayout.packing, leafChunks,
    finishLayout, Bind.bind, Except.bind, pure, Except.pure]
  -- The packed bits, within the capacity the limit gives.
  have room : nodesFor ((bits.size + 7) / 8) ≤ chunksForBits limit := by
    simp only [nodesFor, chunksForBits, bytesPerChunk]; omega
  have tree := bounded_root facts (bitNodes b start bits.size) _ _ (packedBits bits) nodes room
    (by omega) (Or.inr (by unfold Small at small; simp only [nodesFor] at sized; omega))
  rw [tree, rootOf]
  simp only [counted, show (limit + 255) / 256 = chunksForBits limit by simp [chunksForBits, bytesPerChunk]]
  rw [hashPair_mixIn rfl (facts.lengthNode _) (bounded_size (packedBits_width _) tree) (by simp)]

include facts in
/-- A progressive bit list's root is the specification's. -/
theorem progressiveBitList_root (limit : Option Nat) (b : ByteArray) (start stop : Nat) (v : Value)
    (ordered : start ≤ stop) (inside : stop ≤ b.size) (small : Small b)
    (read : deserialize (.progressiveBitList limit) (slice b start stop) = .ok v) :
    Ssz.hashTreeRoot (.progressiveBitList limit) v = .ok (rootOf (.progressiveBitList limit) b start stop).data := by
  -- Decoding recovers the bits below the closing bit.
  simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i bits decoded
  cases read
  obtain ⟨counted, nodes, sized⟩ :=
    bitNodes_nodes b start stop ordered inside (by unfold Small at small; omega) _ bits decoded
  have few : bits.size ≤ 8 * (stop - start) := by
    have nonempty := (unpackDelimited_ok decoded).1
    rw [slice_size b start stop inside] at nonempty
    rw [← counted]; simp only [bitCount]; have := highest_lt (b.get! (stop - 1)); omega
  have bound := boundCheck_of_withinBound limit bits.size (unpackDelimited_within decoded)
  rw [hashTreeRoot_unfold]
  simp only [merkleLayout, bound, MerkleLayout.packing, leafChunks, finishLayout, Bind.bind, Except.bind, pure,
    Except.pure]
  -- The packed bits go on a spine.
  have tree := progressive_root facts (bitNodes b start bits.size) _ (packedBits bits) nodes (by omega)
    (Or.inr (by unfold Small at small; simp only [nodesFor] at sized; omega))
  rw [rootOf]
  simp only [counted]
  rw [hashPair_mixIn tree (facts.lengthNode _) (by simp) (by simp)]

end Ssz.Native.RootProof
