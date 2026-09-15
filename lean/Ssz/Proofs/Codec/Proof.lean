import Ssz.Codec.Proof
import Ssz.Proofs.Merkle.Verify

/-! Laws of the node reader and the branch builder that sit directly on their definitions. -/

namespace Ssz

/-- Reading a list of nodes that all answer gives the list of what they answered. -/
theorem mapM_of_ok {alpha : Type} (node : alpha → Bytes) :
    ∀ items : List alpha,
      items.mapM (fun item => (.ok (node item) : Except Err Bytes)) = .ok (items.map node)
  | [] => rfl
  | item :: rest => by
    -- Reading the head answers, so the whole reading is the head with the rest behind it.
    simp [List.mapM_cons, mapM_of_ok node rest, Bind.bind, Except.bind, pure, Except.pure]

/-- The index naming the root reads back the value's own root, as it must. -/
theorem nodeRoot_root (shape : Desc) (value : Value) :
    nodeRoot shape value 1 = hashTreeRoot shape value := by
  -- The walk answers the root outright, before it reads anything of the shape.
  rw [nodeRoot, nodeRootAt]
  cases hashTreeRoot shape value <;> rfl

/-- Reading a finite set of successful nodes returns exactly those nodes. -/
theorem mapM_of_ok_on (node : Nat → Bytes) (read : Nat → Except Err Bytes) :
    ∀ indices : List Nat, (∀ index ∈ indices, read index = .ok (node index)) →
      indices.mapM read = .ok (indices.map node)
  | [], _ => rfl
  | index :: rest, reads => by
    -- The head and tail need success only at the positions actually requested.
    simp [List.mapM_cons, reads index List.mem_cons_self,
      mapM_of_ok_on node read rest (fun at_ member => reads at_ (List.mem_cons_of_mem _ member)),
      Bind.bind, Except.bind, pure, Except.pure]

/--
A constructed branch rebuilds the value's root if its parent equations hold.

Only the root, the claimed node, and its branch siblings must be readable.
Leaves need no children, and index zero is never required.
-/
theorem buildProof_rebuilds_root {shape : Desc} {value : Value} {index : Nat}
    {node : Nat → Bytes} {indices : List Nat}
    (indexed : getBranchIndices index = .ok indices)
    (parents : BranchConsistent node index)
    (walk : ∀ position ∈ index :: 1 :: indices,
      nodeRoot shape value position = .ok (node position))
    {branch : List Bytes} (built : buildProof shape value index = .ok branch) :
    calculateMerkleRoot (node index) branch index = hashTreeRoot shape value := by
  -- Construction reads precisely the siblings named by the index.
  have reads := mapM_of_ok_on node (nodeRoot shape value) indices
    (fun position member => walk position (by simp [member]))
  simp only [buildProof, indexed, Bind.bind, Except.bind, reads, Except.ok.injEq] at built
  subst branch
  -- The local parent equations reach the root, which the walker identifies with the value.
  rw [branch_rebuilds_root_on_path parents indexed]
  have root := walk 1 (by simp)
  simpa only [nodeRoot_root] using root.symm

/-- Zero is rejected independently of the type and value being walked. -/
theorem nodeRoot_zero (shape : Desc) (value : Value) :
    nodeRoot shape value 0 = .error (.notAGindex 0) := by
  -- Every type has positive nesting, so the walk reaches the index check.
  cases shape <;> simp [nodeRoot, Desc.nesting, nodeRootAt, Bind.bind, Except.bind] <;> rfl

end Ssz
