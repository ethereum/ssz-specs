import SszNative.Proofs.Branch.Walk

/-! Trees of packed bytes, as an encoding lays them out and as the decoded value does. -/

namespace Ssz.Native.BranchProof

open Ssz Ssz.Native

/-- Packed nodes of a range agree with the specification's packing of the slice. -/
theorem packRange_agrees (b : ByteArray) (s e : Nat) (o : s ≤ e) (i : e ≤ b.size) (small : RootProof.Small b) :
    LeavesAgree b (.packed (packRange b s e) (nodesFor (e - s))) (.packed (packBytes (slice b s e))) := by
  unfold RootProof.Small at small
  obtain ⟨nodes, sized⟩ := RootProof.packRange_nodes b s e o i (by omega)
  refine ⟨nodes, by omega, by rw [sized]; simp only [nodesFor]; omega⟩

/-- The nodes bytes pack into number the nodes a range's size calls for. -/
theorem packBytes_count (b : ByteArray) (s e : Nat) (i : e ≤ b.size) :
    (packBytes (slice b s e)).size = nodesFor (e - s) := by
  simp [packBytes, slice_size b s e i, nodesFor, bytesPerChunk]

/-- A packed range's node count fits machine-sized offsets. -/
theorem packed_fits (b : ByteArray) (s e : Nat) (i : e ≤ b.size) (small : RootProof.Small b) :
    32 * nodesFor (e - s) + 64 < USize.size := by
  unfold RootProof.Small at small
  simp only [nodesFor]
  omega

/-- A value that is one fixed-size leaf of packed bytes: a boolean, an integer, or a byte vector. -/
theorem fixed_agrees (d : Desc) (leaf : d = .bool ∨ (∃ w, d = .uint w) ∨ ∃ n, d = .byteVector n)
    (sound : d.wellFormed = .ok ()) (b : ByteArray) (s e : Nat) (v : Value) (o : s ≤ e) (i : e ≤ b.size)
    (small : RootProof.Small b) (read : deserialize d (slice b s e) = .ok v) :
    ∃ E L, layoutOf d b s e = .ok E ∧ merkleLayout d v = .ok L ∧ Corresponds b E L := by
  -- The value encodes back to the bytes it came from, which pack into its leaves.
  have wrote := serialize_of_deserialize d sound _ v read
  have layout : merkleLayout d v = .ok ⟨.packed (packBytes (slice b s e)), some (nodesFor (e - s)), none⟩ := by
    have fixed : merkleLayout d v = fixedLeaf d v := by
      rcases leaf with rfl | ⟨w, rfl⟩ | ⟨n, rfl⟩ <;> cases v <;> rfl
    rw [fixed, fixedLeaf, wrote]
    simp [Bind.bind, Except.bind, pure, Except.pure, MerkleLayout.packing, packBytes_count b s e i]
  have laid : layoutOf d b s e = .ok ⟨.packed (packRange b s e) (nodesFor (e - s)), some (nodesFor (e - s)), none⟩ := by
    rcases leaf with rfl | ⟨w, rfl⟩ | ⟨n, rfl⟩ <;> rfl
  exact ⟨_, _, laid, layout, ⟨packRange_agrees b s e o i small, rfl, rfl,
    by simpa [EncodedLayout.count] using packed_fits b s e i small⟩⟩

/-- A byte list: its bytes packed, under the capacity its limit gives, with its size mixed in. -/
theorem byteList_agrees (limit : Nat) (b : ByteArray) (s e : Nat) (v : Value) (o : s ≤ e) (i : e ≤ b.size)
    (small : RootProof.Small b) (read : deserialize (.byteList limit) (slice b s e) = .ok v) :
    ∃ E L, layoutOf (.byteList limit) b s e = .ok E ∧ merkleLayout (.byteList limit) v = .ok L ∧
      Corresponds b E L := by
  -- Decoding keeps the bytes, which fit the limit.
  simp only [deserialize, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i bound
  cases read
  refine ⟨_, ⟨.packed (packBytes (slice b s e)), some (chunksForBytes limit), some (lengthWord (slice b s e).size)⟩,
    rfl, ?_, ⟨packRange_agrees b s e o i small, rfl, ?_, by simpa [EncodedLayout.count] using packed_fits b s e i small⟩⟩
  · simp only [merkleLayout, bound, if_false, MerkleLayout.packing, Bind.bind, Except.bind, pure, Except.pure,
      throw, throwThe, MonadExceptOf.throw]
  · simp only [Option.map_some, slice_size b s e i, RootProof.facts_hold.lengthNode]

/-- A bit vector: its encoding packed, under the capacity its length gives. -/
theorem bitVector_agrees (length : Nat) (sound : (Desc.bitVector length).wellFormed = .ok ()) (b : ByteArray)
    (s e : Nat) (v : Value) (o : s ≤ e) (i : e ≤ b.size) (small : RootProof.Small b)
    (read : deserialize (.bitVector length) (slice b s e) = .ok v) :
    ∃ E L, layoutOf (.bitVector length) b s e = .ok E ∧ merkleLayout (.bitVector length) v = .ok L ∧
      Corresponds b E L := by
  -- The bits encode back to the bytes they came from.
  have wrote := serialize_of_deserialize _ sound _ v read
  simp only [deserialize, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure] at read
  repeat' split at read
  all_goals first | cases read | skip
  all_goals
    simp only [serialize] at wrote
    split at wrote
    · rename_i sized
      injection wrote with packed
      refine ⟨_, ⟨.packed (packBytes (slice b s e)), some (chunksForBits length), none⟩, rfl, ?_,
        ⟨packRange_agrees b s e o i small, rfl, rfl, by simpa [EncodedLayout.count] using packed_fits b s e i small⟩⟩
      simp only [merkleLayout, beq_iff_eq.mp sized, bne_self_eq_false, Bool.false_eq_true, if_false,
        MerkleLayout.packing, Bind.bind, Except.bind, pure, Except.pure, packedBits]
      rw [packed]
    · cases wrote

/-- A bit list: its bits without the closing one, packed, with the bit count mixed in. -/
theorem bitList_agrees (limit : Option Nat) (b : ByteArray) (s e : Nat) (bits : Array Bool) (o : s ≤ e)
    (i : e ≤ b.size) (small : RootProof.Small b) (read : unpackDelimited limit (slice b s e) = .ok bits) :
    LeavesAgree b (.packed (bitNodes b s (bitCount b s e)) (nodesFor ((bitCount b s e + 7) / 8)))
        (.packed (packedBits bits)) ∧
      32 * nodesFor ((bitCount b s e + 7) / 8) + 64 < USize.size ∧ bitCount b s e = bits.size := by
  unfold RootProof.Small at small
  obtain ⟨counted, nodes, sized⟩ := RootProof.bitNodes_nodes b s e o i (by omega) limit bits read
  have few : bits.size ≤ 8 * (e - s) := by
    have nonempty := (RootProof.unpackDelimited_ok read).1
    rw [slice_size b s e i] at nonempty
    rw [← counted]; simp only [bitCount]; have := RootProof.highest_lt (b.get! (e - 1)); omega
  rw [counted]
  refine ⟨⟨nodes, by omega, by rw [sized]; simp only [nodesFor]; omega⟩, by simp only [nodesFor]; omega, rfl⟩

end Ssz.Native.BranchProof
