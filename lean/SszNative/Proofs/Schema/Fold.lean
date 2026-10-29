import SszNative.Schema
import SszNative.Proofs.Root.Merkle

/-! The short fold a compiled struct uses is the specification's tree over its leaves. -/

namespace Ssz.Native

open Ssz

/-- A node written just past a buffer's first whole nodes sits between them and the rest of the buffer. -/
theorem pad_eq (src dest : ByteArray) (d : Nat) (wide : src.size = 32) :
    src.copySlice 0 dest d 32 = dest.extract 0 d ++ src ++ dest.extract (d + 32) dest.size := by
  -- The copy keeps the bytes before, writes all 32 of the node, and keeps the bytes after.
  apply ByteArray.ext
  have ws : src.data.size = 32 := wide
  simp only [ByteArray.copySlice, ByteArray.data_append, ByteArray.data_extract, ws, Nat.sub_zero,
    Nat.min_self, Nat.zero_add]
  rw [show src.data.extract 0 32 = src.data by rw [← ws, Array.extract_size]]
  rfl

/-- The first nodes of a prefix are the first nodes of the buffer. -/
theorem nodeOf_prefix (a : ByteArray) (d j : Nat) (inside : 32 * j + 32 ≤ d) :
    nodeOf (a.extract 0 d) 0 j = nodeOf a 0 j := by
  -- A slice of a slice from the start is the slice of the whole.
  simp only [nodeOf, Nat.zero_add, ByteArray.data_extract, Array.extract_extract]
  congr 1 <;> omega

/-- A buffer with a node written right after its first whole nodes: those nodes stay, the new one follows. -/
theorem pad_nodes (src dest : ByteArray) (width : Nat) (wide : src.size = 32) (within : 32 * width ≤ dest.size) :
    (∀ j < width, nodeOf (src.copySlice 0 dest (32 * width) 32) 0 j = nodeOf dest 0 j) ∧
      nodeOf (src.copySlice 0 dest (32 * width) 32) 0 width = src.data ∧
      (src.copySlice 0 dest (32 * width) 32).size = dest.size - 32 * width - 32 + 32 * width + 32 := by
  rw [pad_eq src dest (32 * width) wide]
  have pre : (dest.extract 0 (32 * width)).size = 32 * width := by rw [ByteArray.size_extract]; omega
  refine ⟨fun j lt => ?_, ?_, ?_⟩
  · -- An old node lies inside the kept prefix.
    rw [nodeOf_append_left _ _ _ (by rw [ByteArray.size_append, pre, wide]; omega),
      nodeOf_append_left _ _ _ (by rw [pre]; omega), nodeOf_prefix _ _ _ (by omega)]
  · -- The new node starts where the prefix ends.
    rw [nodeOf_append_left _ _ _ (by rw [ByteArray.size_append, pre, wide]; omega),
      nodeOf_append_right _ _ _ pre, nodeOf_single _ wide]
  · -- The prefix, the node, and the rest of the buffer.
    rw [ByteArray.size_append, ByteArray.size_append, pre, wide, ByteArray.size_extract]
    omega

/--
A short level of nodes folded up is the root of the tree over its leaves.

The level holds the roots of consecutive subtrees of one height, as many as the leaves need.
The level must leave room for one more node below the largest machine word.
-/
theorem foldShort_spec (leaves : Array Bytes) (r : Nat) :
    ∀ (level : ByteArray) (width h : Nat),
      leaves.size ≤ width * 2 ^ h → (width - 1) * 2 ^ h < leaves.size →
      32 * width ≤ level.size → level.size + 32 < USize.size →
      (∀ j < width, nodeOf level 0 j = subtreeAt leaves h (j * 2 ^ h)) →
      (foldShort level width h r).size = 32 ∧ (foldShort level width h r).data = subtreeAt leaves (h + r) 0 := by
  induction r with
  | zero =>
    intro level width h covers tight inside small nodes
    have one : 1 ≤ width := by
      rcases Nat.eq_zero_or_pos width with zero | pos
      · subst zero
        have : leaves.size ≤ 0 := by simpa using covers
        have : 0 < leaves.size := by simpa using tight
        omega
      · exact pos
    -- The single remaining node is the root.
    have first := nodes 0 one
    simp only [Nat.zero_mul, Nat.add_zero] at first ⊢
    simp only [foldShort]
    split
    · rename_i whole
      simp only [beq_iff_eq] at whole
      exact ⟨whole, by rw [← nodeOf_single level whole, first]⟩
    · simp only [nodeOf, Nat.mul_zero, Nat.add_zero, Nat.zero_add] at first
      exact ⟨by rw [ByteArray.size_extract]; omega, first⟩
  | succ r ih =>
    intro level width h covers tight inside small nodes
    have one : 1 ≤ width := by
      rcases Nat.eq_zero_or_pos width with zero | pos
      · subst zero
        have : leaves.size ≤ 0 := by simpa using covers
        have : 0 < leaves.size := by simpa using tight
        omega
      · exact pos
    simp only [foldShort]
    split
    · -- One node left: it climbs.
      rename_i lone
      have w1 : width = 1 := by omega
      subst w1
      have first := nodes 0 (by decide)
      simp only [nodeOf, Nat.mul_zero, Nat.add_zero, Nat.zero_mul, Nat.zero_add] at first
      exact climb_spec leaves _ h (r + 1) (by rw [ByteArray.size_extract]; omega) first (by simpa using covers)
    · -- Pad an odd level with the zero tree, hash it in one call, and go on.
      rename_i many
      let pairs := (width + 1) / 2
      let padded := if width % 2 == 1 then (zeroRoot h).copySlice 0 level (32 * width) 32 else level
      -- The padded level keeps the level's nodes and holds every pair whole.
      have keep : ∀ j < width, nodeOf padded 0 j = nodeOf level 0 j := by
        intro j lt
        simp only [padded]
        split
        · exact (pad_nodes _ _ width (zeroRoot_size h) inside).1 j lt
        · rfl
      have paddedSize : 64 * pairs ≤ padded.size ∧ padded.size < USize.size := by
        simp only [padded, pairs]
        split
        · rename_i odd
          simp only [beq_iff_eq] at odd
          rw [(pad_nodes _ _ width (zeroRoot_size h) inside).2.2]
          omega
        · rename_i even
          simp only [beq_iff_eq] at even
          omega
      have pairsSize := hashPairs_size padded 0 pairs (by omega)
      rw [show h + (r + 1) = h + 1 + r by omega]
      rw [show (0 : USize) = (0 : Nat).toUSize from rfl]
      apply ih (hashPairs padded (0 : Nat).toUSize pairs.toUSize) pairs (h + 1)
      · -- The leaves still fit the coarser level.
        rw [up_index]
        exact Nat.le_trans covers (Nat.mul_le_mul_right _ (by omega))
      · rw [up_index]
        exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) tight
      · rw [pairsSize]; omega
      · rw [pairsSize]; omega
      · intro j lt
        rw [up_index, subtreeAt_split, ← Nat.succ_mul,
          hashPairs_node padded 0 pairs j lt (by omega) paddedSize.2]
        by_cases paired : 2 * j + 1 < width
        · -- A full pair of the level's own nodes.
          rw [keep (2 * j) (by omega), keep (2 * j + 1) paired, nodes (2 * j) (by omega), nodes (2 * j + 1) paired]
        · -- The odd node out, against the zero tree of its height.
          have odd : width % 2 = 1 := by omega
          have last : 2 * j + 1 = width := by omega
          have pad : nodeOf padded 0 (2 * j + 1) = zeroSubtree h := by
            simp only [padded, odd, beq_self_eq_true, if_true]
            rw [last, (pad_nodes _ _ width (zeroRoot_size h) inside).2.1, zeroRoot_data]
          rw [keep (2 * j) (by omega), nodes (2 * j) (by omega), pad,
            subtreeAt_past leaves h ((2 * j).succ * 2 ^ h)
              (by rw [show (2 * j).succ = width by omega]; exact covers)]

end Ssz.Native
