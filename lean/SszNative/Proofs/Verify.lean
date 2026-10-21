import SszNative.Branch
import SszNative.Proofs.Reference

/-! The native verifiers answer exactly what the specification's verifiers answer. -/

namespace Ssz.Native

open Ssz.Native.Kernel

/-- Two arrays agree when their sizes and bytes agree. -/
private theorem ext_get! (a b : ByteArray) (size : a.size = b.size)
    (bytes : ∀ i < a.size, a.get! i = b.get! i) : a = b := by
  apply ByteArray.ext
  apply Array.ext size
  intro i ha hb
  have hb' : i < b.size := hb
  have := bytes i ha
  rwa [get!_eq a i ha, get!_eq b i hb'] at this

/-- A whole array, extracted from its start. -/
private theorem extract_all (a : ByteArray) (size : a.size = 32) : a.extract 0 32 = a := by
  apply ByteArray.ext
  simp [← size]

/-- The joining of two nodes the specification and the native path agree on. -/
theorem combine_eq (left right : ByteArray) : (combine left right).data = Ssz.combine left.data right.data := by
  unfold combine
  split
  · rename_i whole
    simp only [Bool.and_eq_true, beq_iff_eq] at whole
    -- One parent of one pair is the digest of the two nodes, byte for byte.
    have parent : hashColumns left 0 right 0 1 = Sha256.hash (left ++ right) := by
      apply ext_get!
      · simp only [hashColumns, hashColumnsReference_size, Sha256.hash_size, USize.toNat_one]
      · intro i within
        have bound : i < 32 := by
          simpa only [hashColumns, hashColumnsReference_size, USize.toNat_one] using within
        have := hashColumnsReference_get left 0 right 0 1 0 i (by simp) bound
        simp only [Nat.mul_zero, Nat.zero_add, USize.toNat_zero] at this
        simp only [hashColumns]
        rw [this, extract_all left whole.1, extract_all right whole.2]
    -- Appending arrays appends their bytes.
    have joined : left ++ right = ⟨left.data ++ right.data⟩ := ByteArray.ext (by simp)
    rw [parent, joined]
    rfl
  · rfl

/-- Equality of arrays is equality of their bytes. -/
theorem beq_data (a b : ByteArray) : (a == b) = (a.data == b.data) := rfl

/-- A node's width is checked as the specification checks it. -/
theorem checkNode_eq (node : ByteArray) : checkNode node = checkChunk node.data := rfl

/-- Every node's width is checked as the specification checks it. -/
theorem checkNodes_eq (nodes : List ByteArray) : checkNodes nodes = checkChunks (nodes.map (·.data)) := by
  induction nodes with
  | nil => rfl
  | cons node rest ih => simp only [checkNodes, checkChunks, List.map_cons, checkNode_eq, ih]

/-- Climbing a branch reaches the node the specification reaches. -/
theorem climbBranch_eq (index level : Nat) (node : ByteArray) (proof : List ByteArray) :
    (climbBranch index level node proof).data = Ssz.climbBranch index level node.data (proof.map (·.data)) := by
  induction proof generalizing level node with
  | nil => rfl
  | cons sibling rest ih =>
    -- Each parent is the specification's parent, so the climb goes on from the same node.
    simp only [climbBranch, Ssz.climbBranch, List.map_cons, ih]
    split <;> simp [combine_eq]

/-- One leaf and its branch are verified exactly as the specification verifies them. -/
theorem verifyMerkleProof_eq (leaf : ByteArray) (proof : List ByteArray) (index : Nat) (root : ByteArray) :
    verifyMerkleProof leaf proof index root = Ssz.verifyMerkleProof leaf.data (proof.map (·.data)) index root.data := by
  -- Both read the same checks, then compare the same climbed node.
  simp only [verifyMerkleProof, Ssz.verifyMerkleProof, calculateMerkleRoot, checkNode_eq, checkNodes_eq,
    List.length_map, beq_data, climbBranch_eq]
  -- The checks run in the same order, and only the place the comparison sits differs.
  cases checkChunk leaf.data <;> cases checkChunk root.data <;> cases checkChunks (proof.map (·.data)) <;>
    cases gindexLength index <;> try rfl
  rename_i depth
  by_cases same : proof.length = depth <;> simp [same, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw]

/-- Indexed nodes with their bytes, as the specification holds them. -/
def dataNodes (nodes : List (Nat × ByteArray)) : List (Nat × Bytes) :=
  nodes.map fun entry => (entry.1, entry.2.data)

/-- The node held at an index is the one the specification finds. -/
theorem nodeAt_eq (nodes : List (Nat × ByteArray)) (index : Nat) :
    (nodeAt nodes index).map (·.data) = Ssz.nodeAt (dataNodes nodes) index := by
  induction nodes with
  | nil => rfl
  | cons entry rest ih =>
    -- The search stops at the same entry, since it reads only the indices.
    obtain ⟨tableEntry, node⟩ := entry
    by_cases here : tableEntry = index
    · simp [nodeAt, Ssz.nodeAt, dataNodes, here]
    · simpa [nodeAt, Ssz.nodeAt, dataNodes, here] using ih

/-- One level folds into the parents and kept nodes the specification folds it into. -/
theorem foldLevelNodes_eq (depth : Nat) (nodes : List (Nat × ByteArray)) (pending : List (Nat × ByteArray)) :
    (foldLevelNodes depth nodes pending).map (fun r => (dataNodes r.1, dataNodes r.2)) =
      Ssz.foldLevelNodes depth (dataNodes nodes) (dataNodes pending) := by
  induction pending with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨index, node⟩ := entry
    have right := nodeAt_eq nodes (index + 1)
    have left := nodeAt_eq nodes (index - 1)
    have rest' : dataNodes ((index, node) :: rest) = (index, node.data) :: dataNodes rest := rfl
    rw [rest']
    simp only [foldLevelNodes, Ssz.foldLevelNodes]
    -- Each branch reads the same indices, and a parent is the specification's parent.
    by_cases level : levelOf index = depth
    · by_cases even : index % 2 = 0
      · cases found : nodeAt nodes (index + 1) with
        | none =>
          rw [found] at right
          simp [level, even, ← right, Except.map, throw, throwThe, MonadExceptOf.throw]
        | some sibling =>
          rw [found] at right
          simp only [level, even, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ← right, Option.map_some]
          cases r : foldLevelNodes depth nodes rest <;> rw [r] at ih <;> simp only [Except.map] at ih <;>
            rw [← ih] <;> simp [Except.map, bind, Except.bind, pure, Except.pure, dataNodes, combine_eq]
      · cases found : nodeAt nodes (index - 1) with
        | none =>
          rw [found] at left
          simp [level, even, ← left, Except.map, throw, throwThe, MonadExceptOf.throw]
        | some prev =>
          rw [found] at left
          simp only [level, even, ← left, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
            Option.isNone_some, Option.map_some, beq_iff_eq]
          exact ih
    · cases r : foldLevelNodes depth nodes rest <;> rw [r] at ih <;> simp only [Except.map] at ih <;>
        rw [← ih] <;> simp [level, Except.map, bind, Except.bind, pure, Except.pure, dataNodes]

/-- Folding to the root reaches the root the specification reaches. -/
theorem foldToRoot_eq (depth : Nat) (nodes : List (Nat × ByteArray)) :
    (foldToRoot depth nodes).map (·.data) = Ssz.foldToRoot depth (dataNodes nodes) := by
  induction depth generalizing nodes with
  | zero =>
    -- The root is the node held at index one, found in the same place.
    have := nodeAt_eq nodes 1
    simp only [foldToRoot, Ssz.foldToRoot]
    cases found : nodeAt nodes 1 <;> rw [found] at this <;> rw [← this] <;> rfl
  | succ depth ih =>
    -- One level folds as the specification folds it, then the climb goes on from the same nodes.
    have level := foldLevelNodes_eq (depth + 1) nodes nodes
    simp only [foldToRoot, Ssz.foldToRoot, Ssz.foldLevel]
    cases r : foldLevelNodes (depth + 1) nodes nodes <;> rw [r] at level <;> rw [← level]
    · rfl
    · rename_i folded
      have next := ih (folded.1 ++ folded.2)
      simp only [Except.map, dataNodes, List.map_append] at next ⊢
      exact next

/-- Indices paired with nodes, then with their bytes, are indices paired with bytes. -/
private theorem zip_data (indices : List Nat) (nodes : List ByteArray) :
    dataNodes (indices.zip nodes) = indices.zip (nodes.map (·.data)) := by
  induction indices generalizing nodes with
  | nil => rfl
  | cons index rest ih =>
    cases nodes with
    | nil => rfl
    | cons node more =>
      simp only [dataNodes] at ih ⊢
      simp [ih more]

/-- Several leaves and their nodes are verified exactly as the specification verifies them. -/
theorem verifyMerkleMultiproof_eq (leaves proof : List ByteArray) (indices : List Nat) (root : ByteArray) :
    verifyMerkleMultiproof leaves proof indices root =
      Ssz.verifyMerkleMultiproof (leaves.map (·.data)) (proof.map (·.data)) indices root.data := by
  simp only [verifyMerkleMultiproof, Ssz.verifyMerkleMultiproof, calculateMultiMerkleRoot, checkNode_eq,
    checkNodes_eq, List.length_map]
  -- The checks run in the same order on the same widths and counts.
  cases checkChunk root.data <;> cases checkChunks (leaves.map (·.data)) <;>
    cases checkChunks (proof.map (·.data)) <;> try rfl
  by_cases leafCount : leaves.length = indices.length
  · cases found : getHelperIndices indices with
    | error e => simp [leafCount, bind, Except.bind]
    | ok helpers =>
      by_cases proofCount : proof.length = helpers.length
      · -- The fold starts from the specification's nodes, at the same level.
        have joined : dataNodes (indices.zip leaves ++ helpers.zip proof) =
            indices.zip (leaves.map (·.data)) ++ helpers.zip (proof.map (·.data)) := by
          rw [dataNodes, List.map_append, ← dataNodes, ← dataNodes, zip_data, zip_data]
        have levels : ∀ start, (indices.zip (leaves.map (·.data)) ++ helpers.zip (proof.map (·.data))).foldl
            (fun deepest entry => max deepest (levelOf entry.1)) start =
            (indices.zip leaves ++ helpers.zip proof).foldl (fun deepest entry => max deepest (levelOf entry.1)) start := by
          intro start
          -- The deepest level reads only the indices, which the bytes leave alone.
          rw [← joined, dataNodes, List.foldl_map]
        have folded := foldToRoot_eq ((indices.zip leaves ++ helpers.zip proof).foldl
          (fun deepest entry => max deepest (levelOf entry.1)) 0) (indices.zip leaves ++ helpers.zip proof)
        rw [joined] at folded
        have depth := levels 0
        simp only [List.foldl_append] at depth folded
        simp only [leafCount, proofCount, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
          List.foldl_map, List.map_append, List.foldl_append, bind, Except.bind, pure, Except.pure]
        rw [depth, ← folded]
        -- Comparing arrays compares their bytes.
        cases foldToRoot _ _ <;> rfl
      · simp [leafCount, proofCount, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · simp [leafCount, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

end Ssz.Native
