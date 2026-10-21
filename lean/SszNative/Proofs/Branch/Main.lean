import SszNative.Proofs.Branch.Nested

/-! Nodes, branches, and multiproofs read from an encoding are the specification's, read from the value it decodes to. -/

namespace Ssz.Native.BranchProof

open Ssz Ssz.Native

/-- A bit list, bounded or progressive, lays out its tree as its encoding does. -/
theorem bits_agrees (limit : Option Nat) (b : ByteArray) (s e : Nat) (o : s ≤ e) (i : e ≤ b.size)
    (small : RootProof.Small b) (bits : Array Bool) (read : unpackDelimited limit (slice b s e) = .ok bits)
    (capacity : Option Nat) :
    Corresponds b ⟨.packed (bitNodes b s (bitCount b s e)) (nodesFor ((bitCount b s e + 7) / 8)), capacity,
      some (lengthNode (bitCount b s e))⟩ ⟨.packed (packedBits bits), capacity, some (lengthWord bits.size)⟩ := by
  obtain ⟨agree, fits, counted⟩ := bitList_agrees limit b s e bits o i small read
  exact ⟨agree, rfl, by simp only [Option.map_some, RootProof.facts_hold.lengthNode, counted],
    by simpa [EncodedLayout.count] using fits⟩

/-- Every type's encodings lay out their trees as the values they decode to do. -/
theorem laysOut (d : Desc) : LaysOut d := by
  intro sound b s e v o i small read
  match d with
  | .bool => exact fixed_agrees _ (.inl rfl) sound b s e v o i small read
  | .uint w => exact fixed_agrees _ (.inr (.inl ⟨w, rfl⟩)) sound b s e v o i small read
  | .byteVector n => exact fixed_agrees _ (.inr (.inr ⟨n, rfl⟩)) sound b s e v o i small read
  | .byteList limit => exact byteList_agrees limit b s e v o i small read
  | .bitVector length => exact bitVector_agrees length sound b s e v o i small read
  | .bitList limit =>
    simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    rename_i bits decoded
    cases read
    have bound := unpackDelimited_bound decoded
    refine ⟨_, _, rfl, ?_, bits_agrees (some limit) b s e o i small bits decoded (some (chunksForBits limit))⟩
    simp only [merkleLayout, show ¬ bits.size > limit by omega, if_false, MerkleLayout.packing, Bind.bind,
      Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | .progressiveBitList limit =>
    simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    rename_i bits decoded
    cases read
    exact ⟨_, _, rfl, rfl, bits_agrees limit b s e o i small bits decoded none⟩
  | .vector element length => exact vector_agrees element length sound b s e v o i small read
  | .list element limit => exact list_agrees element limit sound b s e v o i small read
  | .progressiveList element limit => exact progressiveList_agrees element limit sound b s e v o i small read
  | .container names fields => exact container_agrees names fields sound b s e v o i small read
  | .progressiveContainer active names fields =>
    exact progressiveContainer_agrees active names fields sound b s e v o i small read
  | .compatibleUnion selectors options => exact union_agrees selectors options sound b s e v o i small read

/-- The node at an index of an accepted encoding, read from its bytes, is the decoded value's node there. -/
theorem nodeRootAt_whole (d : Desc) (sound : d.wellFormed = .ok ()) (b : ByteArray) (small : RootProof.Small b)
    (v : Value) (read : deserialize d b.data = .ok v) (index : Nat) :
    (Native.nodeRootAt (d.nesting + index) d b 0 b.size index).map ByteArray.data =
      Ssz.nodeRoot d v index := by
  have whole : slice b 0 b.size = b.data := by simp [slice, ← ByteArray.size_data]
  exact walk laysOut _ d b 0 b.size v index sound (by omega) (Nat.zero_le _) (Nat.le_refl _) small
    (by rw [whole]; exact read)

end Ssz.Native.BranchProof

namespace Ssz.Native

open Ssz

/--
The node at a generalized index read from an encoding is the node of the value it decodes to, or the same refusal.

The type is well formed, and the encoding small enough that every buffer the walk builds has machine-sized offsets.
Every array a 64-bit machine holds is that small.
-/
theorem nodeRoot_eq (d : Desc) (sound : d.wellFormed = .ok ()) (b : ByteArray)
    (small : 64 * b.size + 128 < USize.size) (index : Nat) :
    (nodeRoot d b index).map ByteArray.data = (do let v ← deserialize d b.data; Ssz.nodeRoot d v index) := by
  -- The check refuses exactly what decoding refuses, with the same reason.
  simp only [nodeRoot, validate_eq, Bind.bind, Except.bind, Except.map]
  cases decoded : deserialize d b.data with
  | error e => rfl
  | ok v =>
    have := BranchProof.nodeRootAt_whole d sound b small v decoded index
    simpa [Except.map] using this

/-- Nodes read one by one, each the specification's node, are the specification's nodes. -/
theorem mapM_data {α : Type} (f : α → Except Err ByteArray) (g : α → Except Err Bytes)
    (same : ∀ x, (f x).map ByteArray.data = g x) :
    ∀ xs : List α, (xs.mapM f).map (·.map ByteArray.data) = xs.mapM g
  | [] => rfl
  | x :: rest => by
    have head := same x
    have tail := mapM_data f g same rest
    simp only [List.mapM_cons, Bind.bind, Except.bind, pure, Except.pure] at tail ⊢
    cases fx : f x with
    | error e => rw [fx] at head; simp only [Except.map] at head; rw [← head]; rfl
    | ok r =>
      rw [fx] at head
      simp only [Except.map] at head
      rw [← head]
      cases mr : rest.mapM f with
      | error e => rw [mr] at tail; simp only [Except.map] at tail; rw [← tail]; rfl
      | ok rs => rw [mr] at tail; simp only [Except.map] at tail; rw [← tail]; rfl

/--
The branch for a generalized index read from an encoding is the branch of the value it decodes to, or the same refusal.

The type is well formed, and the encoding small enough that every buffer the walk builds has machine-sized offsets.
-/
theorem buildProof_eq (d : Desc) (sound : d.wellFormed = .ok ()) (b : ByteArray)
    (small : 64 * b.size + 128 < USize.size) (index : Nat) :
    (buildProof d b index).map (·.map ByteArray.data) =
      (do let v ← deserialize d b.data; Ssz.buildProof d v index) := by
  simp only [buildProof, validate_eq, Bind.bind, Except.bind, Except.map]
  cases decoded : deserialize d b.data with
  | error e => rfl
  | ok v =>
    simp only [Ssz.buildProof, Bind.bind, Except.bind]
    cases getBranchIndices index with
    | error e => rfl
    | ok nodes =>
      -- Each node of the branch is read the same way, from the encoding or from the value.
      have := mapM_data _ (Ssz.nodeRoot d v) (fun node =>
        BranchProof.nodeRootAt_whole d sound b small v decoded node) nodes
      simpa [Except.map] using this

/--
The multiproof for generalized indices read from an encoding is the decoded value's multiproof, or the same refusal.

The type is well formed, and the encoding small enough that every buffer the walk builds has machine-sized offsets.
-/
theorem buildMultiproof_eq (d : Desc) (sound : d.wellFormed = .ok ()) (b : ByteArray)
    (small : 64 * b.size + 128 < USize.size) (indices : List Nat) :
    (buildMultiproof d b indices).map (·.map ByteArray.data) =
      (do let v ← deserialize d b.data; Ssz.buildMultiproof d v indices) := by
  simp only [buildMultiproof, validate_eq, Bind.bind, Except.bind, Except.map]
  cases decoded : deserialize d b.data with
  | error e => rfl
  | ok v =>
    simp only [Ssz.buildMultiproof, Bind.bind, Except.bind]
    cases getHelperIndices indices with
    | error e => rfl
    | ok nodes =>
      have := mapM_data _ (Ssz.nodeRoot d v) (fun node =>
        BranchProof.nodeRootAt_whole d sound b small v decoded node) nodes
      simpa [Except.map] using this

end Ssz.Native
