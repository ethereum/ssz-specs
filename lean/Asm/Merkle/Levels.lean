import Ssz.Proofs.Flat.Bounded

/-! The levels of the upward fold, one at a time, as the routine builds them. -/

namespace Ssz.Asm.Merkle

open Ssz

/-- The root of the all-zero subtree of a height. -/
abbrev zeroAt (k : Nat) : Bytes :=
  zeroRoot combine zeroChunk k

/-- Level k of the fold: the leaves, then each level paired up into the one above it. -/
def level (leaves : List Bytes) : Nat → List Bytes
  | 0 => leaves
  | k + 1 => pairLevel combine (zeroAt k) (level leaves k)

theorem foldUpTo_level (leaves : List Bytes) (depth : Nat) :
    ∀ k, k ≤ depth →
      foldUpTo combine zeroChunk depth 0 leaves = foldUpTo combine zeroChunk (depth - k) k (level leaves k)
  | 0, _ => rfl
  | k + 1, bound => by
    -- One more level folded is one fewer left to fold, from one height higher.
    rw [foldUpTo_level leaves depth k (by omega), show depth - k = depth - (k + 1) + 1 by omega]
    rfl

/-- The root is the top level's first node, or the full-height zero subtree when there is none. -/
theorem merkleizeFlat_level (leaves : List Bytes) (depth : Nat) :
    merkleizeFlat combine zeroChunk depth leaves = (level leaves depth).headD (zeroAt depth) := by
  rw [merkleizeFlat, foldUpTo_level leaves depth depth (Nat.le_refl _), Nat.sub_self]
  rfl

/-- An empty level folds to empty levels all the way up. -/
theorem level_nil_stays {leaves : List Bytes} {k : Nat} (empty : level leaves k = []) :
    ∀ j, k ≤ j → level leaves j = [] := by
  intro j above
  induction j with
  | zero =>
    have : k = 0 := by omega
    subst this
    exact empty
  | succ j ih =>
    by_cases same : k = j + 1
    · subst same
      exact empty
    · rw [level, ih (by omega)]
      rfl

theorem level_length (leaves : List Bytes) (k : Nat) :
    (level leaves (k + 1)).length = ((level leaves k).length + 1) / 2 :=
  pairLevel_length combine _ _

/-- Parent i of a level: the hash of nodes 2i and 2i + 1, the fill standing in for a missing right node. -/
theorem pairLevel_get {fill : Bytes} :
    ∀ {nodes : List Bytes} {i : Nat} (within : i < (pairLevel combine fill nodes).length),
      (pairLevel combine fill nodes)[i] =
        combine (nodes[2 * i]'(by rw [pairLevel_length] at within; omega)) (nodes[2 * i + 1]?.getD fill)
  | [], _, within => by simp [pairLevel] at within
  | [_], i, within => by
    simp only [pairLevel, List.length_cons, List.length_nil] at within
    have : i = 0 := by omega
    subst this
    rfl
  | left :: right :: rest, i, within => by
    cases i with
    | zero => rfl
    | succ i =>
      simp only [pairLevel, List.length_cons] at within
      -- Pair i + 1 of the level is pair i of the level two nodes shorter.
      have shorter := pairLevel_get (fill := fill) (nodes := rest) (i := i) (by omega)
      simp only [pairLevel, List.getElem_cons_succ, shorter]
      congr 1

end Ssz.Asm.Merkle
