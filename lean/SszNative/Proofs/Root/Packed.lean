import SszNative.Proofs.Root.Merkle
import SszNative.Proofs.Root.Bytes
import SszNative.Proofs.Root.Record
import SszNative.Proofs.Validate.Slices
import SszNative.Root

/-! Values packed into nodes: gathered into zero-padded blocks, then hashed level by level. -/

namespace Ssz.Native

open Ssz

/-- The tree a nonempty count of leaves needs is under twice as wide as the count. -/
theorem two_pow_depthFor_lt (n : Nat) (positive : 1 ≤ n) : 2 ^ depthFor n < 2 * n := by
  -- Induction following how the depth halves the count.
  induction n using depthFor.induct with
  | case1 n small => rw [depthFor, if_pos small]; omega
  | case2 n large ih =>
    rw [depthFor, if_neg large, Nat.pow_succ]
    have := ih (by omega)
    -- An odd count is never a power of two above one.
    rcases Nat.mod_two_eq_zero_or_one n with even | odd
    · omega
    · cases h : depthFor ((n + 1) / 2) with
      | zero => simp at this ⊢; omega
      | succ e =>
        rw [h, Nat.pow_succ] at this
        rw [Nat.pow_succ]
        omega

/-- Byte x of node j of packed bytes, or of the zero node past them. -/
theorem packBytes_node_get (data : Bytes) (j x : Nat) (lx : x < 32) :
    ((packBytes data)[j]?.getD zeroChunk)[x]! = if 32 * j + x < data.size then (data[32 * j + x]! : UInt8) else 0 := by
  -- Inside the packed nodes, a byte is the data's or the padding's.
  by_cases node : j < (packBytes data).size
  · rw [Array.getElem?_eq_getElem node, Option.getD_some,
      getElem!_pos _ x (by rw [packBytes_chunk_size _ _ node]; exact lx)]
    split
    · rename_i payload
      rw [packBytes_get data j x node lx (by simp only [bytesPerChunk]; omega), getElem!_pos data (32 * j + x) payload]
      simp only [bytesPerChunk, Nat.mul_comm j 32]
    · exact packBytes_padding data j x node lx (by simp only [bytesPerChunk]; omega)
  -- Past the packed nodes, the zero node's bytes are zero.
  · rw [Array.getElem?_eq_none (by omega), Option.getD_none, getElem!_pos _ x (by simp [zeroChunk]; exact lx)]
    simp only [packBytes_size, bytesPerChunk] at node
    rw [if_neg (by omega)]
    simp [zeroChunk]

/-- Gathered records, each zero-padded to a block of nodes, read as the nodes their bytes pack into. -/
theorem gather_nodes (b : ByteArray) (start stride width count depth : Nat)
    (hs : start < USize.size) (hd : stride < USize.size) (hw : width < USize.size) (hc : count < USize.size)
    (hl : 32 * 2 ^ depth < USize.size) (fits : width ≤ 32 * 2 ^ depth)
    (inside : ∀ i < count, start + stride * i + width ≤ b.size) :
    let slots := gather b start.toUSize stride.toUSize width.toUSize count.toUSize (32 * 2 ^ depth).toUSize
    slots.size = count * (32 * 2 ^ depth) ∧
      ∀ i < count, ∀ j < 2 ^ depth, nodeOf slots 0 (i * 2 ^ depth + j) =
        (packBytes (Native.slice b (start + stride * i) (start + stride * i + width)))[j]?.getD zeroChunk := by
  intro slots
  -- The gather writes one block of nodes per record.
  have positive : 0 < 2 ^ depth := Nat.pow_pos (by decide)
  have size : slots.size = count * (32 * 2 ^ depth) := by
    simp only [slots, gather, gatherReference_size, toUSize_toNat _ hc, toUSize_toNat _ hl]
  refine ⟨size, fun i li j lj => ?_⟩
  -- Node j of block i lies inside the gathered buffer.
  have within : 32 * (i * 2 ^ depth + j) + 32 ≤ slots.size := by
    rw [size, Nat.mul_comm count, Nat.mul_assoc 32]
    have : i * 2 ^ depth + 2 ^ depth ≤ 2 ^ depth * count := by
      rw [← Nat.succ_mul, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (by omega)
    omega
  have record := inside i li
  have cut := slice_size b (start + stride * i) (start + stride * i + width) record
  rw [show start + stride * i + width - (start + stride * i) = width by omega] at cut
  -- Compare the node with the packed node byte by byte.
  apply nodeOf_of_get _ _ _ _ (by
    by_cases node : j < (packBytes (slice b (start + stride * i) (start + stride * i + width))).size
    · rw [Array.getElem?_eq_getElem node, Option.getD_some, packBytes_chunk_size _ _ node]
    · rw [Array.getElem?_eq_none (by omega), Option.getD_none]; simp [zeroChunk]) (by omega)
  intro x lx
  rw [packBytes_node_get _ _ _ lx, cut, Nat.zero_add,
    show 32 * (i * 2 ^ depth + j) + x = (32 * 2 ^ depth) * i + (32 * j + x) by
      rw [Nat.mul_add, Nat.mul_comm i, ← Nat.mul_assoc, Nat.add_assoc]]
  -- Byte x of the node is the record's byte, or a zero past the record.
  have slot := gatherReference_get b start.toUSize stride.toUSize width.toUSize count.toUSize (32 * 2 ^ depth).toUSize
    i (32 * j + x) (by rw [toUSize_toNat _ hc]; exact li)
    (by rw [toUSize_toNat _ hl]; have := Nat.mul_le_mul_left 32 (show j + 1 ≤ 2 ^ depth by omega); omega)
    (by rw [toUSize_toNat _ hl, toUSize_toNat _ hw]; exact fits)
    (by rw [toUSize_toNat _ hs, toUSize_toNat _ hd, toUSize_toNat _ hw]; omega)
  simp only [toUSize_toNat _ hs, toUSize_toNat _ hd, toUSize_toNat _ hw, toUSize_toNat _ hl] at slot
  simp only [slots, gather]
  rw [slot]
  split
  · rename_i payload
    rw [slice_getElem! b _ _ _ record (by omega)]
  · rfl

/-- One level of aligned blocks hashed: block i's node j is now the root over twice the leaves. -/
theorem packed_levels (L0 : ByteArray) (count depth : Nat) (leaves : Nat → Array Bytes) (small : L0.size < USize.size)
    (size0 : L0.size = count * (32 * 2 ^ depth))
    (nodes0 : ∀ i < count, ∀ j < 2 ^ depth, nodeOf L0 0 (i * 2 ^ depth + j) = subtreeAt (leaves i) 0 j) :
    ∀ k ≤ depth,
      ((List.range k).foldl (fun level _ => hashPairs level 0 (level.size / 64).toUSize) L0).size =
        count * (32 * 2 ^ (depth - k)) ∧
      ∀ i < count, ∀ j < 2 ^ (depth - k),
        nodeOf ((List.range k).foldl (fun level _ => hashPairs level 0 (level.size / 64).toUSize) L0) 0
          (i * 2 ^ (depth - k) + j) = subtreeAt (leaves i) k (j * 2 ^ k) := by
  intro k
  induction k with
  -- No levels hashed leave the gathered leaves.
  | zero =>
    intro _
    simp only [List.range_zero, List.foldl_nil, Nat.sub_zero, Nat.pow_zero, Nat.mul_one]
    exact ⟨size0, nodes0⟩
  | succ k ih =>
    -- One more level hashes the pairs of the level below.
    intro le
    obtain ⟨size, nodes⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range k).foldl (fun level _ => hashPairs level 0 (level.size / 64).toUSize) L0 = L at size nodes
    obtain ⟨e, he⟩ : ∃ e, depth - k = e + 1 := ⟨depth - k - 1, by omega⟩
    rw [show depth - (k + 1) = e by omega]
    rw [he, Nat.pow_succ] at size nodes
    -- The level halves: each block's pairs stay inside the block.
    have pairs : L.size / 64 = count * 2 ^ e := by rw [size]; rw [show count * (32 * (2 ^ e * 2)) = 64 * (count * 2 ^ e) by
      rw [Nat.mul_comm (2 ^ e) 2, ← Nat.mul_assoc 32, Nat.mul_left_comm]]; omega
    have levelSmall : L.size < USize.size := by
      have : count * (32 * (2 ^ e * 2)) ≤ count * (32 * 2 ^ depth) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_left
        rw [← Nat.pow_succ]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have inside : 0 + 64 * (count * 2 ^ e) ≤ L.size := by rw [← pairs]; omega
    rw [usize_zero]
    refine ⟨by rw [pairs, hashPairs_size _ _ _ (by rw [← pairs]; omega)]; rw [Nat.mul_left_comm], fun i li j lj => ?_⟩
    -- The pair of node j lies inside block i.
    have pi : i * 2 ^ e + j < count * 2 ^ e := by
      have := Nat.mul_le_mul_right (2 ^ e) (show i + 1 ≤ count by omega)
      rw [Nat.succ_mul] at this
      omega
    rw [pairs, hashPairs_node L 0 _ _ pi inside levelSmall,
      show 2 * (i * 2 ^ e + j) = i * (2 ^ e * 2) + 2 * j by
        rw [Nat.mul_add, Nat.mul_comm 2 (i * 2 ^ e), Nat.mul_assoc],
      Nat.add_assoc (i * (2 ^ e * 2)) (2 * j) 1,
      nodes i li (2 * j) (by omega), nodes i li (2 * j + 1) (by omega), up_index, subtreeAt_split, Nat.add_one_mul (2 * j)]

/-- Records packed into nodes and hashed in blocks: each record's root is its packed root. -/
theorem packedRoots_spec (b : ByteArray) (start stride width count : Nat)
    (hs : start < USize.size) (hd : stride < USize.size) (hw : width < USize.size) (hc : count < USize.size)
    (hl : 32 * 2 ^ depthFor (nodesFor width) < USize.size)
    (blocks : count * (32 * 2 ^ depthFor (nodesFor width)) < USize.size)
    (inside : ∀ i < count, start + stride * i + width ≤ b.size) :
    (packedRoots width (nodesFor width) b start stride count).size = 32 * count ∧
      ∀ i < count, nodeOf (packedRoots width (nodesFor width) b start stride count) 0 i =
        packedRoot (Native.slice b (start + stride * i) (start + stride * i + width)) := by
  let depth := depthFor (nodesFor width)
  -- A record fits its block of nodes.
  have fits : width ≤ 32 * 2 ^ depth := by
    have := le_two_pow_depthFor (nodesFor width)
    simp only [nodesFor] at this
    have : width ≤ 32 * ((width + 31) / 32) := by omega
    exact Nat.le_trans this (Nat.mul_le_mul_left 32 (by assumption))
  obtain ⟨size0, nodes0⟩ := gather_nodes b start stride width count depth hs hd hw hc hl fits inside
  -- Hash every level of every block, down to one node per block.
  have levels := packed_levels _ count depth
    (fun i => packBytes (Native.slice b (start + stride * i) (start + stride * i + width)))
    (by rw [size0]; exact blocks) size0 (fun i li j lj => by rw [nodes0 i li j lj, subtreeAt_leaf]) depth (Nat.le_refl _)
  simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one] at levels
  refine ⟨by rw [packedRoots]; rw [levels.1]; omega, fun i li => ?_⟩
  have := levels.2 i li 0 (by decide)
  simp only [Nat.add_zero, Nat.zero_mul] at this
  rw [packedRoots]
  rw [this]
  -- The packed root merkleizes at the depth its node count needs.
  have record := inside i li
  have cut := slice_size b (start + stride * i) (start + stride * i + width) record
  rw [show start + stride * i + width - (start + stride * i) = width by omega] at cut
  simp only [packedRoot, cut, chunksForBytes, bytesPerChunk, depth, nodesFor]
  rw [show width + 32 - 1 = width + 31 by omega]

end Ssz.Native
