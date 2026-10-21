import SszNative.Proofs.Root.Variable.Facts
import SszNative.Proofs.Root.Fixed
import SszNative.Proofs.Root.Merkle

/-! The trees and the fixed-size roots, as proved node by node, gathered as the facts the other roots rest on. -/

namespace Ssz.Native.RootProof

open Ssz Ssz.Native

/-- The two readings of a buffer's nodes are the same. -/
theorem nodesFrom_same (nodes : ByteArray) (offset count : Nat) :
    -- Both are the same function of the buffer.
    RootProof.nodesFrom nodes offset count = Ssz.Native.nodesFrom nodes offset count := rfl

/-- Fixed-size records the decoding accepts have, node by node, their roots. -/
theorem roots_match (f : ByteArray → Nat → Nat → Nat → ByteArray) (d : Desc) (spec : RootsSpec d f)
    (pick : ∀ b start stride count, Run b (fixedWidth d) start stride count → ∀ i < count,
      validateRange d b (start + stride * i) (start + stride * i + fixedWidth d) = .ok () →
      ∃ v, deserialize d (recordBytes b (start + stride * i) (fixedWidth d)) = .ok v ∧
        Ssz.hashTreeRoot d v = .ok (nodeOf (f b start stride count) 0 i))
    (b : ByteArray) (start count : Nat) (small : Small b) (one : 1 ≤ count)
    (records : RecordsDecode d b start (fixedWidth d) count) :
    RootsMatch d b start (fixedWidth d) count (f b start (fixedWidth d) count) := by
  -- The records form a run: inside the buffer, one width apart, and at least one of them.
  have first := (records 0 one).1
  have run : Run b (fixedWidth d) start (fixedWidth d) count :=
    ⟨by unfold Small at small; omega, one, by omega, fun _ => Nat.le_refl _, fun i h => (records i h).1⟩
  refine ⟨(spec b start (fixedWidth d) count run).1, fun i h v decoded => ?_⟩
  -- A record that decodes passes the check, so its node is its root.
  have valid : validateRange d b (start + fixedWidth d * i) (start + fixedWidth d * i + fixedWidth d) = .ok () := by
    rw [validate_sound d b _ _ (by omega) (records i h).1, decoded]
    rfl
  obtain ⟨w, read, root⟩ := pick b start (fixedWidth d) count run i h valid
  have same : w = v := by
    have : recordBytes b (start + fixedWidth d * i) (fixedWidth d) =
        slice b (start + fixedWidth d * i) (start + fixedWidth d * i + fixedWidth d) := rfl
    rw [this, decoded] at read
    cases read
    rfl
  subst same
  rw [root]
  simp [nodeOf]

/-- What the trees and the fixed-size roots compute. -/
theorem facts_hold : Facts where
  merkleizeAt nodes offset count depth fits inside small := by
    rcases small with zero | small
    · -- No nodes: the zero tree of the depth.
      subst zero
      rw [Native.merkleizeAt]
      simp only [beq_self_eq_true, if_true, zeroRoot_data]
      rw [subtreeAt_past _ _ _ (by simp [RootProof.nodesFrom])]
    · rw [nodesFrom_same]
      exact (merkleizeAt_spec nodes offset count depth fits inside small).2
  progressive nodes count inside small := by
    rcases small with zero | small
    · subst zero
      -- No nodes: the spine closes at once with a zero node.
      simp [Native.merkleizeProgressive, spine, RootProof.nodesFrom, Ssz.merkleizeProgressive, zeroNode, zeroChunk]
    · rw [nodesFrom_same]
      exact (merkleizeProgressive_spec nodes count inside small).2
  lengthNode := lengthNode_spec
  activeFields := activeFieldsNode_spec
  rootsOf d p sound b start stride count small one stride' records := by
    subst stride'
    exact roots_match (rootsOf d) d (rootsOf_spec d p sound)
      (fun b s t c run i h valid => by
        obtain ⟨v, read, root, _⟩ := rootsOf_hashTreeRoot d p sound b s t c run i h valid
        exact ⟨v, read, root⟩) b start count small one records
  chunkedRoots d p sound b start stride count small one stride' records := by
    subst stride'
    exact roots_match (chunkedRoots d) d (chunkedRoots_spec d p sound)
      (fun b s t c run i h valid => by
        obtain ⟨v, read, _, root⟩ := rootsOf_hashTreeRoot d p sound b s t c run i h valid
        exact ⟨v, read, root⟩) b start count small one records

end Ssz.Native.RootProof
