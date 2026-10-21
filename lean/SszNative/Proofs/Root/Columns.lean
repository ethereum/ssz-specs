import SszNative.Proofs.Root.Merkle
import SszNative.Root
import Ssz.Proofs.Merkle.Merkleize

/-!
Trees over columns: one tree per record, built level by level across all records at once.

Column c holds, for every record, the root of that record's subtree at position c of the current level.
Hashing columns pairwise is hashing every record's level at once.
-/

namespace Ssz.Native

open Ssz

/--
Columns at a height: column c holds, for each record i, the root of its subtree of that height at position c.

Every record has the same number of leaves, and the columns cover them exactly.
-/
structure ColumnsAt (columns : List ByteArray) (count height : Nat) (leaves : Nat → Array Bytes) (base : Nat) :
    Prop where
  /-- Each column holds one node per record. -/
  sized : ∀ c (h : c < columns.length), columns[c].size = 32 * count
  /-- A column's node is the record's subtree root at the column's position. -/
  nodes : ∀ c (h : c < columns.length), ∀ i < count,
    nodeOf columns[c] 0 i = subtreeAt (leaves i) height ((base + c) * 2 ^ height)

/-- Pairs of columns hashed together are the columns one level up. -/
theorem pairUp_spec (count height n : Nat) (leaves : Nat → Array Bytes) (small : 32 * count < USize.size)
    (equal : ∀ i < count, (leaves i).size = n) :
    ∀ (columns : List ByteArray) (s : Nat), ColumnsAt columns count height leaves (2 * s) →
      n ≤ (2 * s + columns.length) * 2 ^ height →
      (columnTree.pairUp count height columns).length = (columns.length + 1) / 2 ∧
        ColumnsAt (columnTree.pairUp count height columns) count (height + 1) leaves s
  -- No columns pair up to none.
  | [], s, _, _ => ⟨rfl, ⟨fun c h => absurd h (by simp [columnTree.pairUp]),
      fun c h => absurd h (by simp [columnTree.pairUp])⟩⟩
  | [a], s, tableEntry, covers => by
    -- A single column is hashed against the empty subtree of its height.
    simp only [columnTree.pairUp]
    have aSize := tableEntry.sized 0 (by simp)
    have aNodes := tableEntry.nodes 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at aSize aNodes
    refine ⟨by simp, ⟨fun c h => ?_, fun c h i li => ?_⟩⟩
    · simp only [List.length_singleton, Nat.lt_one_iff] at h
      subst h
      rw [List.getElem_singleton, usize_zero, hashFixed_size _ _ _ _ (by omega)]
    · simp only [List.length_singleton, Nat.lt_one_iff] at h
      subst h
      -- The odd column out is hashed against the empty subtree on its right.
      have bound : (leaves i).size ≤ 2 * s * 2 ^ height + 2 ^ height := by
        rw [equal i li, ← Nat.add_one_mul]
        simpa using covers
      rw [List.getElem_singleton, usize_zero, hashFixed_node a 0 count i _ li (by omega) (by omega) (zeroRoot_size _),
        aNodes i li, zeroRoot_data]
      simp only [Nat.add_zero]
      rw [up_index, subtreeAt_split, subtreeAt_past (leaves i) height (2 * s * 2 ^ height + 2 ^ height) bound]
  | a :: b :: rest, s, tableEntry, covers => by
    -- Two columns hash into one, and the rest pair up from the next position, by induction.
    simp only [columnTree.pairUp]
    have aSize := tableEntry.sized 0 (by simp)
    have bSize := tableEntry.sized 1 (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] at aSize bSize
    have restAt : ColumnsAt rest count height leaves (2 * (s + 1)) :=
      ⟨fun c h => by have := tableEntry.sized (c + 2) (by simp; omega); simpa using this,
        fun c h i li => by
          have := tableEntry.nodes (c + 2) (by simp; omega) i li
          simp only [List.getElem_cons_succ] at this
          rw [this]; congr 2; omega⟩
    obtain ⟨len, restUp⟩ := pairUp_spec count height n leaves small equal rest (s + 1) restAt
      (by rw [show 2 * (s + 1) + rest.length = 2 * s + (a :: b :: rest).length by simp; omega]; exact covers)
    refine ⟨by simp [len]; omega, ⟨fun c h => ?_, fun c h i li => ?_⟩⟩
    -- Each paired column holds one node per record.
    · cases c with
      | zero => simp only [List.getElem_cons_zero]; rw [usize_zero, hashColumns_size _ _ _ _ _ (by omega)]
      | succ c => simp only [List.getElem_cons_succ]; exact restUp.sized c (by simp at h; omega)
    · cases c with
      | zero =>
        -- The first pair: two adjacent subtrees under one parent.
        have aN := tableEntry.nodes 0 (by simp) i li
        have bN := tableEntry.nodes 1 (by simp) i li
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at aN bN
        simp only [List.getElem_cons_zero]
        rw [usize_zero, hashColumns_node a 0 b 0 count i li (by omega) (by omega) (by omega) (by omega), aN, bN]
        simp only [Nat.add_zero]
        rw [up_index, subtreeAt_split, Nat.add_one_mul (2 * s)]
      -- The other pairs come from the rest, one position on.
      | succ c =>
        simp only [List.getElem_cons_succ]
        rw [restUp.nodes c (by simp at h; omega) i li]
        congr 2
        omega

/-- Columns paired up level after level, until one column holds every record's root. -/
theorem columnTree_spec (count n : Nat) (leaves : Nat → Array Bytes) (small : 32 * count < USize.size)
    (equal : ∀ i < count, (leaves i).size = n) :
    ∀ fuel (columns : List ByteArray) height, ColumnsAt columns count height leaves 0 → 1 ≤ columns.length →
      n ≤ columns.length * 2 ^ height → depthFor columns.length < fuel →
      (columnTree columns count height fuel).size = 32 * count ∧
        ∀ i < count, nodeOf (columnTree columns count height fuel) 0 i =
          subtreeAt (leaves i) (height + depthFor columns.length) 0
  -- Fuel never runs out before the tree is done.
  | 0, _, _, _, _, _, lt => absurd lt (Nat.not_lt_zero _)
  | fuel + 1, columns, height, tableEntry, nonempty, covers, deep => by
    match columns, tableEntry, nonempty, covers, deep with
    | [root], tableEntry, _, _, _ =>
      -- One column left: it holds the roots.
      have size := tableEntry.sized 0 (by simp)
      have nodes := tableEntry.nodes 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.zero_add, Nat.zero_mul] at size nodes
      simp only [columnTree, List.length_singleton]
      rw [show depthFor 1 = 0 by rw [depthFor]; simp, Nat.add_zero]
      exact ⟨size, nodes⟩
    | a :: b :: rest, tableEntry, _, covers, deep =>
      -- Pair the columns up and go one level higher.
      have up := pairUp_spec count height n leaves small equal (a :: b :: rest) 0 (by simpa using tableEntry)
        (by simpa using covers)
      have halve : depthFor (a :: b :: rest).length = depthFor (((a :: b :: rest).length + 1) / 2) + 1 := by
        rw [depthFor, if_neg (by simp)]
      have := columnTree_spec count n leaves small equal fuel (columnTree.pairUp count height (a :: b :: rest))
        (height + 1) (by simpa using up.2) (by rw [up.1]; simp; omega) (by
          rw [up.1, up_index]
          exact Nat.le_trans covers (Nat.mul_le_mul_right _ (by omega))) (by rw [up.1]; omega)
      simp only [columnTree]
      rw [up.1] at this
      rw [halve, show height + (depthFor (((a :: b :: rest).length + 1) / 2) + 1) =
        height + 1 + depthFor (((a :: b :: rest).length + 1) / 2) by omega]
      exact this

/-- A column of roots climbed against zero trees: each record's root of a deeper tree over the same leaves. -/
theorem climbColumn_spec (count n : Nat) (leaves : Nat → Array Bytes) (small : 32 * count < USize.size)
    (equal : ∀ i < count, (leaves i).size = n) :
    ∀ levels (column : ByteArray) height, column.size = 32 * count →
      (∀ i < count, nodeOf column 0 i = subtreeAt (leaves i) height 0) → n ≤ 2 ^ height →
      (climbColumn column count height levels).size = 32 * count ∧
        ∀ i < count, nodeOf (climbColumn column count height levels) 0 i = subtreeAt (leaves i) (height + levels) 0
  -- No levels to climb.
  | 0, column, height, size, nodes, _ => ⟨size, nodes⟩
  | levels + 1, column, height, size, nodes, narrow => by
    -- One level up against the zero tree, then the rest, by induction.
    simp only [climbColumn]
    have := climbColumn_spec count n leaves small equal levels
      (hashFixed column 0 (zeroRoot height) count.toUSize) (height + 1)
      (by rw [usize_zero, hashFixed_size _ _ _ _ (by omega)])
      (fun i li => by
        rw [usize_zero, hashFixed_node column 0 count i _ li (by omega) (by omega) (zeroRoot_size _), nodes i li,
          zeroRoot_data, subtreeAt_split, Nat.zero_add, subtreeAt_past (leaves i) height (2 ^ height)
            (by rw [equal i li]; exact narrow)])
      (Nat.le_trans narrow (Nat.pow_le_pow_right (by decide) (by omega)))
    rwa [show height + (levels + 1) = height + 1 + levels by omega]

/-- A count of levels no smaller than the count's own tree. -/
private theorem depthFor_lt_succ (m : Nat) : depthFor m < m + 1 := by
  -- A count is below the power of two above it.
  have := depthFor_le_of_le_two_pow (Nat.le_of_lt (Nat.lt_two_pow_self (n := m)))
  omega

/--
The column tree of one value per record: every record's root over its leaves, at a depth.

Column c holds leaf c of every record, and every record has one leaf per column.
-/
theorem columnTreeTo_spec (columns : List ByteArray) (count depth : Nat) (leaves : Nat → Array Bytes)
    (small : 32 * count < USize.size) (equal : ∀ i < count, (leaves i).size = columns.length)
    (nonempty : 1 ≤ columns.length) (tableEntry : ColumnsAt columns count 0 leaves 0)
    (deep : depthFor columns.length ≤ depth) :
    (columnTreeTo columns count depth).size = 32 * count ∧
      ∀ i < count, nodeOf (columnTreeTo columns count depth) 0 i = subtreeAt (leaves i) depth 0 := by
  -- The columns pair up into one column of roots, then climb to the full depth.
  have tree := columnTree_spec count columns.length leaves small equal (columns.length + 1) columns 0 tableEntry nonempty
    (by simp) (depthFor_lt_succ _)
  simp only [Nat.zero_add] at tree
  have := climbColumn_spec count columns.length leaves small equal (depth - depthFor columns.length)
    (columnRoots columns count) (depthFor columns.length) tree.1 tree.2 (le_two_pow_depthFor _)
  rw [show depthFor columns.length + (depth - depthFor columns.length) = depth by omega] at this
  exact this

end Ssz.Native
