import SszNative.Proofs.Driver.Branch.FoldParents

/-! The multiproof verifier, restated in the steps the compiled verifier takes. -/

namespace EthLib.Consensus.Ssz.Native.Driver.BranchProof

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm

/-- A level whose pairs all join folds into the next level's node set: its parents, then the entries off it. -/
theorem foldToRoot_succ_ok (d : Nat) (N ps : List (Nat × ByteArray)) (h : levelParents (d + 1) N N = .ok ps) :
    foldToRoot (d + 1) N = foldToRoot d (ps ++ levelKept (d + 1) N) := by
  simp only [foldToRoot, foldLevelNodes_eq, h, Except.map, bind, Except.bind]

/-- A level with a pair missing a side refuses the fold. -/
theorem foldToRoot_succ_error (d : Nat) (N : List (Nat × ByteArray)) {e : Err}
    (h : levelParents (d + 1) N N = .error e) : foldToRoot (d + 1) N = .error e := by
  simp only [foldToRoot, foldLevelNodes_eq, h, Except.map, bind, Except.bind]

/-- Entries in two runs, the second right after the first. -/
theorem entriesAt_append (mem : Memory) (a n : Nat) :
    ∀ k, entriesAt mem a (n + k) = entriesAt mem a n ++ entriesAt mem (a + 40 * n) k
  | 0 => by simp [entriesAt]
  | k + 1 => by
    rw [← Nat.add_assoc, entriesAt_succ, entriesAt_append mem a n k, entriesAt_succ, List.append_assoc]
    simp only [Nat.mul_add, Nat.add_assoc]

/-- Nodes read from memory, one more: the nodes so far, then the next. -/
theorem nodesAt_succ (mem : Memory) (a n : Nat) :
    nodesAt mem a (n + 1) = nodesAt mem a n ++ [readNode mem (a + 32 * n)] := by
  simp [nodesAt, List.range_succ]

/-- Two lists zipped, each one longer, are the zipped prefixes, then the last pair. -/
theorem zip_succ {α β : Type} (xs : List α) (ys : List β) (x : α) (y : β) (h : xs.length = ys.length) :
    (xs ++ [x]).zip (ys ++ [y]) = xs.zip ys ++ [(x, y)] := by
  rw [List.zip_append h]; rfl

/-- The deepest level among some entries, folded from zero. -/
def deepestOf (N : List (Nat × ByteArray)) : Nat :=
  (N.map fun (index, _) => levelOf index).foldl max 0

/-- One more entry: the deeper of the deepest so far and its own level. -/
theorem deepestOf_append (N : List (Nat × ByteArray)) (e : Nat × ByteArray) :
    deepestOf (N ++ [e]) = max (deepestOf N) (levelOf e.1) := by
  simp [deepestOf, List.foldl_append]

/--
The verdict on a multiproof with whole nodes: counts and helper indices first, then the fold from the deepest level,
then the comparison with the root.
-/
theorem verifyMerkleMultiproof_eq (leaves proof : List ByteArray) (indices : List Nat) (root : ByteArray)
    (sizes : ∀ n ∈ leaves ++ proof, n.size = 32) :
    verifyMerkleMultiproof leaves proof indices root =
      if leaves.length ≠ indices.length then .error (.leafCount indices.length leaves.length) else
      match getHelperIndices indices with
      | .error e => .error e
      | .ok helpers =>
        if proof.length ≠ helpers.length then .error (.proofLength helpers.length proof.length) else
        (foldToRoot (deepestOf (indices.zip leaves ++ helpers.zip proof)) (indices.zip leaves ++ helpers.zip proof)).map
          fun rebuilt => decide (rebuilt = root) := by
  have leafOk := checkNodes_of leaves fun n h => sizes n (by simp [h])
  have proofOk := checkNodes_of proof fun n h => sizes n (by simp [h])
  unfold verifyMerkleMultiproof
  by_cases lc : leaves.length = indices.length
  · cases getHelperIndices indices with
    | error e => simp [lc, bind, Except.bind]
    | ok helpers =>
      by_cases pc : proof.length = helpers.length
      · simp only [lc, pc, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false,
          bind, Except.bind, pure, Except.pure, leafOk, proofOk, deepestOf, beq_eq_decide]
        cases foldToRoot _ _ <;> rfl
      · simp [lc, pc, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · simp [lc, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

end EthLib.Consensus.Ssz.Native.Driver.BranchProof
