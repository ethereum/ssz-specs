import SszNative.Proofs.Root.Variable.Children
import Ssz.Proofs.Codec.Admits
import Ssz.Proofs.Codec.DecodeFits
import Ssz.Proofs.Codec.RoundTrip

/-! Roots of vectors whose elements are not rooted as columns: one root per element, under a bounded tree. -/

namespace Ssz.Native.RootProof

open Ssz Ssz.Native

variable (facts : Facts)

/-- Related lists have the same length. -/
theorem Each.length_eq {α : Type} {related : α → ByteArray → Prop} :
    ∀ {as : List α} {rs : List ByteArray}, Each related as rs → as.length = rs.length
  -- Each step relates one item of each list.
  | _, _, .nil => rfl
  | _, _, .cons _ tail => by simp [Each.length_eq tail]

/-- One root per range. -/
theorem variableRoots_length (element : Desc) (b : ByteArray) :
    ∀ ranges : List (Nat × Nat), (variableRoots element b ranges).length = ranges.length
  -- Each range gives one root.
  | [] => by rw [variableRoots.eq_def]; rfl
  | (s, e) :: rest => by rw [variableRoots.eq_def]; simp [variableRoots_length element b rest]

/-- A type packing into shared nodes is rooted as columns. -/
theorem plain_of_basic {d : Desc} (basic : d.isBasic = true) : plain d = true := by
  -- Only booleans and integers are basic, and both are plain.
  cases d <;> simp_all [Desc.isBasic, plain]

/-- A vector of well-formed elements spends at least a byte per element. -/
theorem vector_count_le {element : Desc} {count : Nat} {data : Bytes} {slices : List Bytes}
    (sound : element.wellFormed = .ok ()) (read : vectorSlices element count data = .ok slices) :
    count ≤ data.size := by
  simp only [vectorSlices, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure,
    Except.pure] at read
  -- An oversized range is refused, so the vector fit.
  split at read
  · cases read
  split at read
  -- Fixed-size elements take a positive width each.
  · rename_i width fixed
    have positive := fixedSize_pos_of_wellFormed sound fixed
    split at read
    · cases read
    · rename_i same
      simp at same
      rw [same]
      exact Nat.le_mul_of_pos_left count positive
  -- Elements found through offsets take four bytes each for their offsets.
  · split at read
    · cases read
    · rename_i enough; simp [bytesPerOffset] at enough; omega

include facts in
/-- The bounded tree over joined roots is the specification's bounded tree over their bytes. -/
theorem joined_bounded (roots : List ByteArray) (sized : ∀ r ∈ roots, r.size = 32) (capacity : Nat)
    (room : roots.length ≤ capacity) (small : 32 * roots.length + 64 < USize.size) :
    merkleizeBounded (roots.map ByteArray.data).toArray (some capacity) =
      .ok (merkleizeCapacity (joinNodes roots) roots.length capacity).data := by
  -- Joined roots hold their bytes node by node, so both trees see the same leaves.
  obtain ⟨nodes, size⟩ := joinNodes_nodes roots sized
  exact bounded_root facts (joinNodes roots) _ _ _ nodes room (by omega) (Or.inr (by omega))

include facts in
/-- A vector of elements that are not rooted as columns has the specification's root. -/
theorem vector_root (element : Desc) (length : Nat) (ih : Agrees element)
    (sound : (Desc.vector element length).wellFormed = .ok ()) (notPlain : plain (.vector element length) = false)
    (b : ByteArray) (start stop : Nat) (v : Value) (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (small : Small b) (read : deserialize (.vector element length) (slice b start stop) = .ok v) :
    Ssz.hashTreeRoot (.vector element length) v = .ok (rootOf (.vector element length) b start stop).data := by
  -- Decoding cuts the elements' slices, then decodes each.
  simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i slices cut
  split at read
  · cases read
  rename_i values decoded
  cases read
  -- The check accepted ranges cutting the same slices, which the root reads its elements from.
  have agree := vectorRanges_cut element length b start stop ordered inside
  rw [cut] at agree
  cases ranged : vectorRanges element length b start stop with
  | error e => simp [ranged, Except.map, CutAgree] at agree
  | ok r =>
    simp only [ranged, Except.map, CutAgree] at agree
    obtain ⟨sliced, within⟩ := agree
    have rangesEq := elementRanges_vector element length b start stop r ranged
    subst sliced
    -- Each element's root is the specification's root of its value.
    have rooted := variableRoots_spec element ih (wellFormed_vector sound) b small r.toList values
      (fun p m => ⟨(within p m).2.1, by have := (within p m).2.2; omega⟩) decoded
    -- A vector decodes exactly its declared count of elements.
    have count : values.length = length := by
      rw [Each.length_eq rooted, variableRoots_length, ← vectorSlices_length cut]
      simp
    have sized := forall₂_size (fun _ _ h => rooted_size h) rooted
    -- A vector that is not plain has elements that are not basic, so each is a leaf of its own.
    have notBasic : element.isBasic = false := by
      cases basic : element.isBasic
      · rfl
      · simp [plain, plain_of_basic basic] at notPlain
    -- Both sides bound the tree by the vector's length, over the elements' roots.
    rw [hashTreeRoot_unfold]
    simp only [merkleLayout, count, bne_self_eq_false, Bool.false_eq_true, if_false, sequenceLayout, notBasic,
      MerkleLayout.nesting, leafChunks, finishLayout, Bind.bind, Except.bind, pure, Except.pure,
      elements_mapM element rooted]
    rw [rootOf]
    simp only [notPlain, Bool.false_eq_true, if_false, rangesEq]
    have lengths : (variableRoots element b r.toList).length = length := by
      rw [← Each.length_eq rooted, count]
    -- The vector's length fits the encoding, so its buffers stay machine-sized.
    have few := vector_count_le (wellFormed_vector sound) cut
    rw [slice_size b start stop inside] at few
    have := joined_bounded facts _ sized length (by omega) (by unfold Small at small; omega)
    rw [lengths] at this
    rw [this]

end Ssz.Native.RootProof
