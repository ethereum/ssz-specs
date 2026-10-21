import SszNative.Proofs.Root.Variable.Struct

/-! Roots of compatible unions: the chosen option's root, with the selector mixed in. -/

namespace Ssz.Native.RootProof

open Ssz Ssz.Native

variable (facts : Facts)

/-- The option a selector decodes as is the option the specification looks up, and the one the root reads. -/
theorem option_search (b : ByteArray) (s e : Nat) :
    ∀ (selectors : List Nat) (options : List Desc) (selector : Nat) (data : Bytes) (w : Value),
      deserializeOption selectors options selector data = .ok w →
      ∃ option inner, option ∈ options ∧ lookupOption selectors options selector = .ok option ∧
        w = .union selector inner ∧ deserialize option data = .ok inner ∧
        optionRoot selectors options selector b s e = rootOf option b s e
  -- No options decode nothing.
  | [], [], _, _, _, read => by simp [deserializeOption] at read
  | chosen :: selectors, option :: options, selector, data, w, read => by
    -- The first option either matches the selector or is skipped on every side.
    simp only [deserializeOption] at read
    split at read
    -- A matching option decodes the rest of the range and is the root's choice.
    · rename_i same
      simp only [Bind.bind, Except.bind, pure, Except.pure] at read
      split at read
      · cases read
      rename_i inner decoded
      cases read
      refine ⟨option, inner, by simp, by simp [lookupOption, same], rfl, decoded, ?_⟩
      rw [optionRoot.eq_def]
      simp [same]
    -- A skipped option leaves the search to the rest, by induction.
    · rename_i other
      obtain ⟨found, inner, member, looked, eq, decoded, root⟩ :=
        option_search b s e selectors options selector data w read
      refine ⟨found, inner, by simp [member], by simp [lookupOption, other, looked], eq, decoded, ?_⟩
      rw [optionRoot.eq_def]
      simp [other, root]
  -- Selectors and options of different lengths never decode.
  | [], _ :: _, _, _, _, read => by simp [deserializeOption] at read
  | _ :: _, [], _, _, _, read => by simp [deserializeOption] at read

/-- One leaf under a capacity of one is its own root. -/
theorem bounded_single (r : Bytes) : merkleizeBounded #[r] (some 1) = .ok r := by
  -- A tree of depth zero over one leaf is that leaf.
  simp [merkleizeBounded, depthFor, subtreeAt, padded]
  rfl

include facts in
/-- A compatible union's root is the specification's. -/
theorem union_root (selectors : List Nat) (options : List Desc) (ih : ∀ option ∈ options, Agrees option)
    (sound : (Desc.compatibleUnion selectors options).wellFormed = .ok ()) (b : ByteArray) (start stop : Nat)
    (v : Value) (ordered : start ≤ stop) (inside : stop ≤ b.size) (small : Small b)
    (read : deserialize (.compatibleUnion selectors options) (slice b start stop) = .ok v) :
    Ssz.hashTreeRoot (.compatibleUnion selectors options) v =
      .ok (rootOf (.compatibleUnion selectors options) b start stop).data := by
  have size := slice_size b start stop inside
  -- Decoding refuses an empty range, so a selector byte is present.
  simp only [deserialize, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at read
  split at read
  · cases read
  rename_i nonempty
  -- The first byte selects, and the rest is the option's encoding.
  have first : (slice b start stop)[0]! = b.get! start := by
    rw [slice_getElem! b start stop 0 inside (by omega), Nat.add_zero]
  have rest : (slice b start stop).extract 1 (slice b start stop).size = slice b (start + 1) stop := by
    rw [size, slice_extract b start stop 1 _ ordered (Nat.le_refl _)]
    congr 1
    omega
  rw [first, rest] at read
  -- The selected option decodes the rest, and its root agrees by the option's own claim.
  obtain ⟨option, inner, member, looked, rfl, decoded, root⟩ :=
    option_search b (start + 1) stop selectors options _ _ v read
  have optionSound := allWellFormed_mem options (wellFormed_union sound) option member
  have rooted := ih option member optionSound b (start + 1) stop inner (by omega) inside small decoded
  have byte : (b.get! start).toNat ≤ 0xFF := by have := (b.get! start).toNat_lt; omega
  -- The specification roots the option under a capacity of one, then mixes in the selector.
  rw [hashTreeRoot_unfold]
  simp only [merkleLayout, looked, selectorWord, show ¬ (b.get! start).toNat > 0xFF by omega, if_false,
    MerkleLayout.nesting, leafChunks, List.mapM_cons, List.mapM_nil, slotRoot, rooted, finishLayout,
    Bind.bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  -- The native root does the same, with the selector as a length node.
  rw [rootOf]
  simp only [root, bounded_single]
  rw [hashPair_mixIn rfl (facts.lengthNode _) (hashTreeRoot_size _ _ _ rooted) (by simp)]

end Ssz.Native.RootProof
