import SszNative.Proofs.Driver.Branch.VerifyBranch
import EthLib.Consensus.Proofs.Ssz.Merkle.HelperUniqueness

/-!
The index checks and helper indices of a multiproof, restated in the shape the compiled loops compute them.

A path is walked by halving until the root, a claim is checked against each of its strict ancestors, and the helper
indices are the distinct candidates, largest first.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.BranchProof

open EthLib.Consensus.Ssz

/-- Checked claims are each at least two. -/
theorem rejectClaimPaths_valid (l : List Nat) :
    ∀ claims : List Nat, rejectClaimPaths l claims = .ok () → ∀ c ∈ claims, 2 ≤ c
  | [], _ => by simp
  | c :: rest, h => by
    rw [rejectClaimPaths_cons] at h
    -- Zero and the root are refused, so a passing claim is at least two.
    by_cases zero : c = 0
    · simp [zero] at h
    by_cases one : c = 1
    · simp [one] at h
    simp only [zero, one, ite_false] at h
    split at h
    · cases h
    intro x hx
    rcases List.mem_cons.mp hx with e | e
    · omega
    · exact rejectClaimPaths_valid l rest h x e

/-- Valid claims have their paths collected one after the other. -/
theorem collectPathIndices_valid : ∀ claims : List Nat, (∀ c ∈ claims, 2 ≤ c) →
    collectPathIndices claims = .ok (claims.flatMap pathOf)
  | [], _ => rfl
  | c :: rest, h => by
    have path : getPathIndices c = .ok (pathOf c) := by
      simp [getPathIndices, gindexLength_of_two (h c (by simp)), pathOf, bind, Except.bind, pure, Except.pure]
    simp only [collectPathIndices, path, collectPathIndices_valid rest (fun x hx => h x (by simp [hx])),
      List.flatMap_cons, bind, Except.bind, pure, Except.pure]

/-- Accepted claims have their paths collected one after the other. -/
theorem collectPathIndices_eq {l : List Nat} (accepted : rejectRelated l = .ok ()) :
    collectPathIndices l = .ok (l.flatMap pathOf) := by
  rw [rejectRelated_eq] at accepted
  split at accepted
  · cases accepted
  split at accepted
  · cases accepted
  exact collectPathIndices_valid l (rejectClaimPaths_valid l l accepted)

/-- Two strictly falling lists with the same members are the same list. -/
theorem eq_of_pairwise_gt : ∀ {a b : List Nat}, a.Pairwise (· > ·) → b.Pairwise (· > ·) → (∀ x, x ∈ a ↔ x ∈ b) → a = b
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, same => absurd ((same y).mpr (by simp)) (by simp)
  | x :: _, [], _, _, same => absurd ((same x).mp (by simp)) (by simp)
  | x :: a, y :: b, ha, hb, same => by
    have ha' := List.pairwise_cons.mp ha
    have hb' := List.pairwise_cons.mp hb
    -- Each head is the largest member, so the heads agree.
    have head : x = y := by
      have xy := (same x).mp (by simp)
      have yx := (same y).mpr (by simp)
      rcases List.mem_cons.mp xy with e | e
      · exact e
      rcases List.mem_cons.mp yx with e' | e'
      · exact e'.symm
      have := hb'.1 x e
      have := ha'.1 y e'
      omega
    subst head
    -- Below the head, the members still agree, since neither tail holds the head.
    refine congrArg _ (eq_of_pairwise_gt ha'.2 hb'.2 fun z => ?_)
    constructor
    · intro hz
      have := ha'.1 z hz
      rcases List.mem_cons.mp ((same z).mp (by simp [hz])) with e | e
      · omega
      · exact e
    · intro hz
      have := hb'.1 z hz
      rcases List.mem_cons.mp ((same z).mpr (by simp [hz])) with e | e
      · omega
      · exact e

/-- The candidates for helper indices: siblings of path nodes that are no path node themselves, in path order. -/
def candidatesOf (paths : List Nat) : List Nat :=
  (paths.map fun p => p ^^^ 1).filter fun s => s ∉ paths

/--
Once the claims are accepted, the helper indices are any strictly falling list holding exactly the candidates.
-/
theorem getHelperIndices_eq {l : List Nat} (accepted : rejectRelated l = .ok ()) {S : List Nat}
    (desc : S.Pairwise (· > ·)) (members : ∀ x, x ∈ S ↔ x ∈ candidatesOf (l.flatMap pathOf)) :
    getHelperIndices l = .ok S := by
  have collected := collectPathIndices_eq accepted
  have built : getHelperIndices l = .ok (((((l.flatMap pathOf).map gindexSibling).eraseDups.filter
      fun node => !(l.flatMap pathOf).contains node)).mergeSort fun a b => decide (b ≤ a)) := by
    simp [getHelperIndices, accepted, collected, bind, Except.bind, pure, Except.pure]
  rw [built]
  congr 1
  -- The sorted helpers fall strictly, since they are sorted and distinct.
  have nodup := getHelperIndices_nodup built
  have sorted := List.pairwise_mergeSort (le := fun a b : Nat => decide (b ≤ a))
    (fun a b c h1 h2 => by simp at h1 h2 ⊢; omega) (fun a b => by simp; omega)
    ((((l.flatMap pathOf).map gindexSibling).eraseDups.filter fun node => !(l.flatMap pathOf).contains node))
  refine eq_of_pairwise_gt ?_ desc fun x => ?_
  · refine (sorted.and nodup).imp fun h => ?_
    simp at h; omega
  · rw [members, (getHelperIndices_frontier built).2.2 x]
    simp [candidatesOf, claimPaths_eq, gindexSibling]

end EthLib.Consensus.Ssz.Native.Driver.BranchProof
