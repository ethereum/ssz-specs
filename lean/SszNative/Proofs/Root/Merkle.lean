import SszNative.Proofs.Root.Nodes
import Ssz.Proofs.Codec.ProgressiveProofTree
import Ssz.Proofs.Codec.Table
import Ssz.Proofs.Merkle.Merkleize

/-! Trees over node buffers are the specification's trees over arrays of nodes. -/

namespace Ssz.Native

open Ssz

/-- A buffer of exactly one node is that node. -/
theorem nodeOf_single (n : ByteArray) (wide : n.size = 32) : nodeOf n 0 0 = n.data := by
  simp only [nodeOf, Nat.mul_zero, Nat.add_zero, Nat.zero_add, ByteArray.data_extract]
  have : n.data.size = 32 := wide
  rw [← this, Array.extract_size]

/-- A leaf of a depth-zero tree is the node there, or the zero node past the data. -/
theorem subtreeAt_leaf (chunks : Array Bytes) (start : Nat) :
    subtreeAt chunks 0 start = chunks[start]?.getD zeroChunk := by
  unfold subtreeAt
  split
  · -- Past the data, the cached zero tree of height zero is the zero node.
    rw [zeroSubtree_eq, Array.getElem?_eq_none (by omega)]
    rfl
  · rfl

/-- A tree past the data is the zero tree of its height. -/
theorem subtreeAt_past (chunks : Array Bytes) (depth start : Nat) (past : chunks.size ≤ start) :
    subtreeAt chunks depth start = zeroSubtree depth := by
  unfold subtreeAt
  rw [if_pos past]

/-- A tree reads only the leaves under it. -/
theorem subtreeAt_congr (a b : Array Bytes) (depth sa sb : Nat)
    (same : ∀ i < 2 ^ depth, a[sa + i]? = b[sb + i]?) : subtreeAt a depth sa = subtreeAt b depth sb := by
  induction depth generalizing sa sb with
  | zero =>
    rw [subtreeAt_leaf, subtreeAt_leaf]
    have := same 0 (by simp)
    simp only [Nat.add_zero] at this
    rw [this]
  | succ depth ih =>
    -- Each half of the tree reads its own half of the leaves.
    rw [subtreeAt_split, subtreeAt_split]
    congr 1
    · exact ih sa sb fun i lt => same i (by rw [Nat.pow_succ]; omega)
    · exact ih _ _ fun i lt => by
        have := same (2 ^ depth + i) (by rw [Nat.pow_succ]; omega)
        rwa [← Nat.add_assoc, ← Nat.add_assoc] at this

/-- The literal arguments the code passes, as conversions of numbers. -/
private theorem hashPairs_zero_one (src : ByteArray) :
    hashPairs src 0 1 = hashPairs src (0 : Nat).toUSize (1 : Nat).toUSize := rfl

/-- The table of zero trees holds the zero tree of every height up to its own. -/
theorem zeroTable_spec (h : Nat) :
    (zeroTable h).size = 32 * (h + 1) ∧ ∀ j ≤ h, nodeOf (zeroTable h) 0 j = Ssz.zeroRoot combine zeroChunk j := by
  induction h with
  | zero =>
    refine ⟨rfl, fun j le => ?_⟩
    rw [Nat.le_zero.mp le]
    rfl
  | succ h ih =>
    obtain ⟨size, nodes⟩ := ih
    -- The new height hashes the top entry with itself.
    let below := (zeroTable h).extract (32 * h) (32 * h + 32)
    have belowSize : below.size = 32 := by
      simp only [below, ByteArray.size_extract, size]
      omega
    have belowData : below.data = Ssz.zeroRoot combine zeroChunk h := by
      rw [← nodes h (Nat.le_refl _)]
      simp [below, nodeOf]
    have twice : (below ++ below).size = 64 := by rw [ByteArray.size_append, belowSize]
    have top : (hashPairs (below ++ below) 0 1).size = 32 := by
      rw [hashPairs_zero_one, hashPairs_size _ _ _ (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
    have small : (below ++ below).size < USize.size := by
      rw [twice]
      exact Nat.lt_of_lt_of_le (by decide) USize.le_size
    simp only [zeroTable]
    refine ⟨by rw [ByteArray.size_append, size, top]; omega, fun j le => ?_⟩
    by_cases old : j ≤ h
    · rw [nodeOf_append_left _ _ _ (by rw [size]; omega), nodes j old]
    · rw [show j = h + 1 by omega, nodeOf_append_right _ _ _ (by rw [size]), hashPairs_zero_one,
        hashPairs_node _ _ _ _ (by decide) (by rw [twice]; decide) small,
        nodeOf_append_left _ _ _ (by rw [belowSize]; decide), Nat.mul_zero,
        nodeOf_append_right _ _ _ (by rw [belowSize]), nodeOf_single _ belowSize, belowData]
      rfl

/-- The zero tree of a height, as the node buffer the native trees use. -/
theorem zeroRoot_spec (h : Nat) : (zeroRoot h).size = 32 ∧ (zeroRoot h).data = zeroSubtree h := by
  -- Either table gives the same entry.
  have entry : ∀ t, h ≤ t → ((zeroTable t).extract (32 * h) (32 * h + 32)).size = 32 ∧
      ((zeroTable t).extract (32 * h) (32 * h + 32)).data = zeroSubtree h := by
    intro t le
    obtain ⟨size, nodes⟩ := zeroTable_spec t
    refine ⟨by rw [ByteArray.size_extract, size]; omega, ?_⟩
    rw [zeroSubtree_eq, ← nodes h le]
    simp [nodeOf]
  unfold zeroRoot
  split
  · rename_i covered
    simp only [zeroRoots, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_map,
      Array.getElem?_range, show h < cachedHeights + 1 by omega, if_true, Option.map_some, Option.getD_some]
    exact entry cachedHeights covered
  · exact entry h (Nat.le_refl _)

/-- A zero tree's root is one node. -/
@[simp] theorem zeroRoot_size (h : Nat) : (zeroRoot h).size = 32 := (zeroRoot_spec h).1

/-- A zero tree's root is the specification's zero subtree. -/
theorem zeroRoot_data (h : Nat) : (zeroRoot h).data = zeroSubtree h := (zeroRoot_spec h).2

/-- A single node hashed from offset zero, with its literal arguments read as machine words. -/
private theorem hashFixed_lit (src node : ByteArray) :
    hashFixed src 0 node 1 = hashFixed src (0 : Nat).toUSize node (1 : Nat).toUSize := rfl

/-- A single node hashed from an offset, with its count read as a machine word. -/
private theorem hashFixed_one (src : ByteArray) (o : USize) (node : ByteArray) :
    hashFixed src o node 1 = hashFixed src o node (1 : Nat).toUSize := rfl

/-- One fits a machine word. -/
private theorem one_small : 1 < USize.size := Nat.lt_of_lt_of_le (by decide) USize.le_size

/-- Position j of the level one up is the parent of positions 2j and 2j + 1. -/
theorem up_index (j h : Nat) : j * 2 ^ (h + 1) = 2 * j * 2 ^ h := by
  rw [Nat.pow_succ, Nat.mul_comm (2 ^ h) 2, ← Nat.mul_assoc, Nat.mul_comm j 2]

/-- A lone node climbing against zero trees is the root of a tree whose leaves all sit under it. -/
theorem climb_spec (leaves : Array Bytes) (n : ByteArray) (h k : Nat) (wide : n.size = 32)
    (root : n.data = subtreeAt leaves h 0) (narrow : leaves.size ≤ 2 ^ h) :
    (climb n h k).size = 32 ∧ (climb n h k).data = subtreeAt leaves (h + k) 0 := by
  induction k generalizing n h with
  | zero => exact ⟨wide, root⟩
  | succ k ih =>
    simp only [climb]
    -- One level up: the node on the left, an empty subtree on the right.
    have small : n.size < USize.size := by rw [wide]; exact Nat.lt_of_lt_of_le (by decide) USize.le_size
    have up := hashFixed_size n 0 1 (zeroRoot h) one_small
    have parent : (hashFixed n 0 (zeroRoot h) 1).data = subtreeAt leaves (h + 1) 0 := by
      rw [← nodeOf_single _ (by rw [hashFixed_lit, up]), hashFixed_lit,
        hashFixed_node _ _ _ _ _ (by decide) (by omega) small (zeroRoot_size h), zeroRoot_data,
        nodeOf_single _ wide, root, subtreeAt_split, Nat.zero_add,
        subtreeAt_past leaves h (2 ^ h) narrow]
    have := ih (hashFixed n 0 (zeroRoot h) 1) (h + 1) (by rw [hashFixed_lit, up]) parent
      (Nat.le_trans narrow (Nat.pow_le_pow_right (by decide) (by omega)))
    rwa [Nat.add_right_comm] at this

/--
A level of nodes folded up is the root of the tree over its leaves.

The level holds the roots of consecutive subtrees of one height, as many as the leaves need.
-/
theorem fold_spec (leaves : Array Bytes) (r : Nat) :
    ∀ (level : ByteArray) (offset width h : Nat),
      leaves.size ≤ width * 2 ^ h → (width - 1) * 2 ^ h < leaves.size →
      offset + 32 * width ≤ level.size → level.size < USize.size →
      (∀ j < width, nodeOf level offset j = subtreeAt leaves h (j * 2 ^ h)) →
      (fold level offset width h r).size = 32 ∧ (fold level offset width h r).data = subtreeAt leaves (h + r) 0 := by
  induction r with
  | zero =>
    intro level offset width h covers tight inside small nodes
    -- The single remaining node is the root.
    have one : 1 ≤ width := by
      rcases Nat.eq_zero_or_pos width with zero | pos
      · subst zero
        have : leaves.size ≤ 0 := by simpa using covers
        have : 0 < leaves.size := by simpa using tight
        omega
      · exact pos
    have := nodes 0 one
    simp only [nodeOf, Nat.mul_zero, Nat.add_zero, Nat.zero_mul] at this
    simp only [fold, Nat.add_zero]
    refine ⟨by rw [ByteArray.size_extract]; omega, this⟩
  | succ r ih =>
    intro level offset width h covers tight inside small nodes
    have one : 1 ≤ width := by
      rcases Nat.eq_zero_or_pos width with zero | pos
      · subst zero
        have : leaves.size ≤ 0 := by simpa using covers
        have : 0 < leaves.size := by simpa using tight
        omega
      · exact pos
    simp only [fold]
    split
    · -- One node left: it climbs.
      rename_i lone
      have w1 : width = 1 := by omega
      subst w1
      have := nodes 0 (by decide)
      simp only [nodeOf, Nat.mul_zero, Nat.add_zero, Nat.zero_mul] at this
      have := climb_spec leaves _ h (r + 1) (by rw [ByteArray.size_extract]; omega) this (by simpa using covers)
      exact this
    · -- Hash one level and go on.
      rename_i many
      have pairsSize := hashPairs_size level offset (width / 2) (by omega)
      have parentsSize : (parentsOf level offset width h).size = 32 * ((width + 1) / 2) := by
        simp only [parentsOf]
        split
        · rename_i even
          simp only [beq_iff_eq] at even
          rw [pairsSize]
          omega
        · rename_i odd
          simp only [beq_iff_eq] at odd
          rw [ByteArray.size_append, pairsSize, hashFixed_one, hashFixed_size _ _ _ _ one_small]
          omega
      rw [show h + (r + 1) = h + 1 + r by omega]
      apply ih (parentsOf level offset width h) 0 ((width + 1) / 2) (h + 1)
      · -- The leaves still fit the coarser level.
        rw [up_index]
        exact Nat.le_trans covers (Nat.mul_le_mul_right _ (by omega))
      · rw [up_index]
        exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) tight
      · rw [parentsSize]; omega
      · rw [parentsSize]; omega
      · intro j lt
        rw [up_index, subtreeAt_split, ← Nat.succ_mul]
        by_cases paired : j < (width / 2)
        · -- A full pair below.
          have node := hashPairs_node level offset (width / 2) j paired (by omega) small
          rw [← nodes (2 * j) (by omega), ← nodes (2 * j + 1) (by omega), ← node]
          simp only [parentsOf]
          split
          · rfl
          · rw [nodeOf_append_left _ _ _ (by rw [pairsSize]; omega)]
        · -- The odd node out, against an empty subtree.
          have odd : width % 2 = 1 := by omega
          have last : j = (width / 2) := by omega
          have tail := hashFixed_node level (offset + 32 * (width - 1)) 1 0 (zeroRoot h) (by decide)
            (by omega) small (zeroRoot_size h)
          simp only [parentsOf, odd, show (1 == 0) = false by rfl, Bool.false_eq_true, if_false]
          rw [hashFixed_one, nodeOf_append_right _ _ _ (by rw [pairsSize, last]), tail, zeroRoot_data,
            nodeOf_shift,
            Nat.add_zero, nodes (width - 1) (by omega), show width - 1 = 2 * j by omega,
            subtreeAt_past leaves h ((2 * j).succ * 2 ^ h)
              (by rw [show (2 * j).succ = width by omega]; exact covers)]

/-- Nodes appended one after another are read back in order. -/
theorem concat_nodes (f : Nat → ByteArray) (init : ByteArray) (empty : init.size = 0) (n : Nat)
    (wide : ∀ k < n, (f k).size = 32) :
    ((List.range n).foldl (fun out k => out ++ f k) init).size = 32 * n ∧
      ∀ k < n, nodeOf ((List.range n).foldl (fun out k => out ++ f k) init) 0 k = (f k).data := by
  -- No pieces leave the empty buffer.
  induction n with
  | zero => exact ⟨by simpa using empty, fun k lt => absurd lt (Nat.not_lt_zero k)⟩
  | succ n ih =>
    -- Each piece adds one node, read back from where it was appended.
    obtain ⟨size, nodes⟩ := ih fun k lt => wide k (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [ByteArray.size_append, size, wide n (by omega)]; omega, fun k lt => ?_⟩
    by_cases old : k < n
    · rw [nodeOf_append_left _ _ _ (by rw [size]; omega), nodes k old]
    · rw [show k = n by omega, nodeOf_append_right _ _ _ size, nodeOf_single _ (wide n (by omega))]

/-- Leaves read straight from a buffer are the roots of the height-zero subtrees. -/
private theorem leaves_spec (nodes : ByteArray) (offset count : Nat) :
    ∀ j < count, nodeOf nodes offset j = subtreeAt (nodesFrom nodes offset count) 0 (j * 2 ^ 0) := by
  intro j lt
  rw [Nat.pow_zero, Nat.mul_one, subtreeAt_leaf, nodesFrom_get?, if_pos lt]
  rfl

/--
The native root of a tree over a run of nodes is the specification's root over the same nodes.

The nodes must fit the depth, lie inside the buffer, and the buffer must be addressable.
-/
theorem merkleizeAt_spec (nodes : ByteArray) (offset count depth : Nat) (fits : count ≤ 2 ^ depth)
    (inside : offset + 32 * count ≤ nodes.size) (small : nodes.size < USize.size) :
    (merkleizeAt nodes offset count depth).size = 32 ∧
      (merkleizeAt nodes offset count depth).data = subtreeAt (nodesFrom nodes offset count) depth 0 := by
  unfold merkleizeAt
  simp only [taskHeight, Nat.reducePow]
  split
  · -- No nodes at all: the zero tree.
    rename_i none
    simp only [beq_iff_eq] at none
    subst none
    exact ⟨zeroRoot_size _, by rw [zeroRoot_data, subtreeAt_past _ _ _ (by simp)]⟩
  · rename_i some
    simp only [beq_iff_eq] at some
    split
    · -- A narrow or shallow tree is folded in one go.
      have := fold_spec (nodesFrom nodes offset count) depth nodes offset count 0 (by simp)
        (by simp; omega) inside small (leaves_spec nodes offset count)
      rwa [Nat.zero_add] at this
    · -- A wide tree: subtrees of a fixed height first, each a task, then the levels above them.
      rename_i wideTree
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at wideTree
      obtain ⟨wideCount, deep⟩ := wideTree
      simp only [List.foldl_map]
      let parts := (count + 2048 - 1) / 2048
      let piece := fun k => fold nodes (offset + 32 * 2048 * k) (min 2048 (count - 2048 * k)) 0 11
      -- Each subtree is the specification's subtree at its aligned position.
      have pieces : ∀ k < parts, (piece k).size = 32 ∧
          (piece k).data = subtreeAt (nodesFrom nodes offset count) 11 (k * 2 ^ 11) := by
        intro k lt
        have start : 2048 * k < count := by omega
        have := fold_spec (nodesFrom nodes (offset + 32 * 2048 * k) (min 2048 (count - 2048 * k))) 11 nodes
          (offset + 32 * 2048 * k) (min 2048 (count - 2048 * k)) 0 (by simp) (by simp; omega) (by omega) small
          (leaves_spec _ _ _)
        refine ⟨this.1, ?_⟩
        rw [this.2, Nat.zero_add]
        apply subtreeAt_congr
        intro i lt
        rw [nodesFrom_get?, nodesFrom_get?, show offset + 32 * 2048 * k = offset + 32 * (2048 * k) by omega,
          nodeOf_shift, show 2 ^ 11 = 2048 by rfl, Nat.zero_add, Nat.mul_comm k 2048]
        simp only [show 2 ^ 11 = 2048 by rfl] at lt
        by_cases here : i < min 2048 (count - 2048 * k)
        · rw [if_pos here, if_pos (by omega)]
        · rw [if_neg here, if_neg (by omega)]
      obtain ⟨rootsSize, rootsNodes⟩ := concat_nodes piece (ByteArray.emptyWithCapacity (32 * parts + 32)) rfl
        parts fun k lt => (pieces k lt).1
      have := fold_spec (nodesFrom nodes offset count) (depth - 11)
        ((List.range parts).foldl (fun out k => out ++ piece k) (ByteArray.emptyWithCapacity (32 * parts + 32)))
        0 parts 11 (by simp; omega) (by simp; omega) (by omega) (by omega)
        (fun j lt => by rw [rootsNodes j lt, (pieces j lt).2])
      rwa [show 11 + (depth - 11) = depth by omega] at this

/-- The native root over the first nodes of a buffer, at a depth. -/
theorem merkleizeDepth_spec (nodes : ByteArray) (count depth : Nat) (fits : count ≤ 2 ^ depth)
    (inside : 32 * count ≤ nodes.size) (small : nodes.size < USize.size) :
    (merkleizeDepth nodes count depth).size = 32 ∧
      (merkleizeDepth nodes count depth).data = subtreeAt (nodesFrom nodes 0 count) depth 0 :=
  merkleizeAt_spec nodes 0 count depth fits (by omega) small

/-- The native root at the depth a capacity calls for. -/
theorem merkleizeCapacity_spec (nodes : ByteArray) (count capacity : Nat) (fits : count ≤ capacity)
    (inside : 32 * count ≤ nodes.size) (small : nodes.size < USize.size) :
    (merkleizeCapacity nodes count capacity).size = 32 ∧
      (merkleizeCapacity nodes count capacity).data = subtreeAt (nodesFrom nodes 0 count) (depthFor capacity) 0 :=
  merkleizeDepth_spec nodes count (depthFor capacity) (Nat.le_trans fits (le_two_pow_depthFor capacity)) inside small

/-- The parent of two nodes, joined into one buffer first. -/
theorem hashPair_spec (a b : ByteArray) (wa : a.size = 32) (wb : b.size = 32) :
    (hashPair a b).size = 32 ∧ (hashPair a b).data = combine a.data b.data := by
  have joined : (a ++ b).size = 64 := by rw [ByteArray.size_append, wa, wb]
  have small : (a ++ b).size < USize.size := by rw [joined]; exact Nat.lt_of_lt_of_le (by decide) USize.le_size
  simp only [hashPair, hashPairs_zero_one]
  refine ⟨by rw [hashPairs_size _ _ _ one_small], ?_⟩
  rw [← nodeOf_single _ (by rw [hashPairs_size _ _ _ one_small]),
    hashPairs_node _ _ _ _ (by decide) (by omega) small, nodeOf_append_left _ _ _ (by omega),
    nodeOf_append_right _ _ _ (by rw [wa]), nodeOf_single _ wa, nodeOf_single _ wb]

/-- The spine of a progressive tree, from a start and a level, is the specification's spine over the nodes left. -/
theorem spine_spec (nodes : ByteArray) (count : Nat) (inside : 32 * count ≤ nodes.size)
    (small : nodes.size < USize.size) (fuel : Nat) :
    ∀ start level, count - start < fuel →
      (spine nodes count start (4 ^ level) fuel).size = 32 ∧
      (spine nodes count start (4 ^ level) fuel).data =
        Ssz.merkleizeProgressive ((nodesFrom nodes 0 count).toList.drop start) level := by
  induction fuel with
  | zero => intro _ _ lt; omega
  | succ fuel ih =>
    intro start level lt
    simp only [spine]
    split
    · -- Out of nodes: the closing zero node.
      rename_i done
      rw [Ssz.merkleizeProgressive]
      simp only [List.isEmpty_iff, List.drop_eq_nil_iff, Array.length_toList, nodesFrom_size, done, if_true]
      exact ⟨rfl, rfl⟩
    · rename_i more
      have positive : 0 < 4 ^ level := Nat.pow_pos (by decide)
      let here := min (4 ^ level) (count - start)
      have fits : here ≤ 2 ^ Nat.log2 (4 ^ level) := by
        rw [four_pow_eq, Nat.log2_two_pow]
        exact Nat.le_trans (Nat.min_le_left _ _) (by rw [four_pow_eq]; exact Nat.le_refl _)
      obtain ⟨leftSize, leftData⟩ :=
        merkleizeAt_spec nodes (32 * start) here (Nat.log2 (4 ^ level)) fits (by omega) small
      have rest := ih (start + 4 ^ level) (level + 1) (by omega)
      rw [show 4 * 4 ^ level = 4 ^ (level + 1) by rw [Nat.pow_succ, Nat.mul_comm]] 
      obtain ⟨size, data⟩ := hashPair_spec _ _ leftSize rest.1
      refine ⟨size, ?_⟩
      rw [data, leftData]
      conv => rhs; rw [Ssz.merkleizeProgressive]
      rw [rest.2]
      have nonempty : ((nodesFrom nodes 0 count).toList.drop start).isEmpty = false := by
        simp only [List.isEmpty_eq_false_iff, ne_eq, List.drop_eq_nil_iff, Array.length_toList, nodesFrom_size]
        omega
      rw [nonempty, if_neg (by decide)]
      dsimp only
      rw [List.drop_drop, four_pow_eq, depthFor_pow, Nat.log2_two_pow,
        ← four_pow_eq]
      congr 2
      -- The first subtree's leaves are the next nodes.
      apply Array.ext
      · simp [here]
      · intro i lt _
        simp only [List.getElem_toArray, List.getElem_take, List.getElem_drop, Array.getElem_toList, nodesFrom,
          Array.getElem_ofFn]
        rw [show 32 * start = 0 + 32 * start by omega, nodeOf_shift]

/-- The native progressive root is the specification's, as EIP-7916 defines it. -/
theorem merkleizeProgressive_spec (nodes : ByteArray) (count : Nat) (inside : 32 * count ≤ nodes.size)
    (small : nodes.size < USize.size) :
    (merkleizeProgressive nodes count).size = 32 ∧
      (merkleizeProgressive nodes count).data = Ssz.merkleizeProgressive (nodesFrom nodes 0 count).toList 0 := by
  have := spine_spec nodes count inside small (count + 1) 0 0 (by omega)
  simp only [Nat.pow_zero, List.drop_zero] at this
  exact this

/-- Byte i of a little-endian integer is its i-th base-256 digit. -/
private theorem uintBytes_get (width value i : Nat) (lt : i < width) :
    (uintBytes width value)[i]'(by rw [uintBytes_size]; exact lt) = UInt8.ofNat (value >>> (8 * i)) := by
  induction width generalizing value i with
  | zero => omega
  | succ width ih =>
    simp only [uintBytes]
    cases i with
    | zero =>
      simp
      exact UInt8.ofNat_mod_size'
    | succ i =>
      rw [Array.getElem_append_right (by simp)]
      simp only [Array.size_singleton, Nat.add_sub_cancel]
      rw [ih (value / 256) i (by omega), Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
        show 8 * (i + 1) = 8 * i + 8 by omega, Nat.pow_add, Nat.mul_comm]

/-- The native length node is the specification's length word. -/
theorem lengthNode_spec (count : Nat) : (lengthNode count).data = lengthWord count := by
  apply Array.ext
  · simp [lengthNode, lengthWord, uintBytes_size]
  · intro i _ lt
    simp only [lengthWord, uintBytes_size] at lt
    simp only [lengthNode, lengthWord, Array.getElem_map, Array.getElem_range]
    rw [uintBytes_get _ _ _ lt]

/-- Setting bits conditionally is a conditional mask. -/
private theorem or_ite (acc x : UInt8) (c : Prop) [Decidable c] :
    (if c then acc ||| x else acc) = acc ||| (if c then x else 0) := by
  split <;> simp

/-- The native active-fields node is the specification's active-fields word. -/
theorem activeFieldsNode_spec (active : List Bool) : (activeFieldsNode active).data = activeFieldsWord active := by
  apply Array.ext
  · simp [activeFieldsNode, activeFieldsWord, packBits]
  · intro i _ _
    simp only [activeFieldsNode, activeFieldsWord, packBits, packByte, Array.getElem_map, Array.getElem_range,
      Array.getElem_ofFn, List.getElem?_toArray, List.getD_eq_getElem?_getD]
    simp only [List.range, List.range.loop, List.foldl, or_ite, UInt8.zero_or]
    simp only [Nat.mul_comm 8 i]

end Ssz.Native
