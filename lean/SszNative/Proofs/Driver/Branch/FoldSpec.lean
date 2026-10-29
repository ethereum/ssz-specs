import SszNative.Proofs.Driver.Branch.HelperIndices

/-!
One level of a multiproof's fold, restated as the two passes the compiled code makes.

The first pass builds the level's parents in order, refusing a pair with a missing side.
The second keeps the entries off the level, in order.
A node set lives in memory as 40-byte entries: an index word, then a node.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.BranchProof

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm

/-- The parents one level of a node set folds into, in order, or the first refusal. -/
def levelParents (depth : Nat) (nodes : List (Nat × ByteArray)) :
    List (Nat × ByteArray) → Except Err (List (Nat × ByteArray))
  | [] => .ok []
  | (index, node) :: rest =>
    if levelOf index != depth then levelParents depth nodes rest
    else if index % 2 == 0 then
      match nodeAt nodes (index + 1) with
      | some sibling => (levelParents depth nodes rest).map fun ps => (gindexParent index, combine node sibling) :: ps
      | none => .error .proofIncomplete
    else if (nodeAt nodes (index - 1)).isNone then .error .proofIncomplete
    else levelParents depth nodes rest

/-- The entries of a node set off one level, in order. -/
def levelKept (depth : Nat) (pending : List (Nat × ByteArray)) : List (Nat × ByteArray) :=
  pending.filter fun entry => levelOf entry.1 != depth

/-- One level folds into the parents of the first pass and the entries of the second. -/
theorem foldLevelNodes_eq (depth : Nat) (nodes : List (Nat × ByteArray)) :
    ∀ pending, foldLevelNodes depth nodes pending =
      (levelParents depth nodes pending).map fun ps => (ps, levelKept depth pending)
  | [] => rfl
  | (index, node) :: rest => by
    have ih := foldLevelNodes_eq depth nodes rest
    simp only [foldLevelNodes, levelParents, levelKept, List.filter_cons]
    by_cases level : levelOf index = depth
    · simp only [level, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      by_cases even : index % 2 = 0
      · simp only [even, beq_self_eq_true, ↓reduceIte]
        cases nodeAt nodes (index + 1) with
        | none => rfl
        | some sibling =>
          simp only
          rw [ih]
          cases levelParents depth nodes rest <;> rfl
      · simp only [show (index % 2 == 0) = false by simpa using even, Bool.false_eq_true, ↓reduceIte]
        split
        · rfl
        · rw [ih]; rfl
    · have : (levelOf index != depth) = true := by simpa using level
      simp only [this, ↓reduceIte]
      rw [ih]
      cases levelParents depth nodes rest <;> rfl

/-- Parents of two runs of entries are the first run's, then the second's. -/
theorem levelParents_append (depth : Nat) (nodes : List (Nat × ByteArray)) :
    ∀ a b, levelParents depth nodes (a ++ b) =
      (levelParents depth nodes a).bind fun ps => (levelParents depth nodes b).map fun qs => ps ++ qs
  | [], b => by
    simp only [List.nil_append, levelParents]
    cases levelParents depth nodes b <;> rfl
  | (index, node) :: rest, b => by
    have ih := levelParents_append depth nodes rest b
    simp only [List.cons_append, levelParents]
    split
    · exact ih
    split
    · split
      · rw [ih]; cases levelParents depth nodes rest <;> simp [Except.bind, Except.map] <;>
          cases levelParents depth nodes b <;> rfl
      · rfl
    split
    · rfl
    · exact ih

/-- Parents are no more than the entries they come from. -/
theorem levelParents_length (depth : Nat) (nodes : List (Nat × ByteArray)) :
    ∀ pending ps, levelParents depth nodes pending = .ok ps →
      ps.length + (levelKept depth pending).length ≤ pending.length
  | [], ps, h => by cases h; simp [levelKept]
  | (index, node) :: rest, ps, h => by
    simp only [levelParents] at h
    simp only [levelKept, List.filter_cons, List.length_cons]
    split at h
    · rename_i off
      have := levelParents_length depth nodes rest ps h
      simp only [levelKept] at this
      simp only [off, ↓reduceIte, List.length_cons]
      omega
    · rename_i on
      simp only [on, Bool.false_eq_true, ↓reduceIte]
      split at h
      · split at h
        · cases r : levelParents depth nodes rest with
          | error e => rw [r] at h; cases h
          | ok qs =>
            rw [r] at h; cases h
            have := levelParents_length depth nodes rest qs r
            simp only [levelKept] at this
            simp only [List.length_cons]
            omega
        · cases h
      · split at h
        · cases h
        · have := levelParents_length depth nodes rest ps h
          simp only [levelKept] at this
          omega

/-- The entries of a node set in memory: an index word, then a node, 40 bytes apart. -/
def entriesAt (mem : Memory) (a n : Nat) : List (Nat × ByteArray) :=
  (List.range n).map fun j => ((readLE mem (a + 40 * j) 8).toNat, readNode mem (a + 40 * j + 8))

/-- Entries read from memory, as many as asked. -/
theorem entriesAt_length (mem : Memory) (a n : Nat) : (entriesAt mem a n).length = n := by
  simp [entriesAt]

/-- One more entry is the entries so far, then the next one. -/
theorem entriesAt_succ (mem : Memory) (a n : Nat) :
    entriesAt mem a (n + 1) = entriesAt mem a n ++
      [((readLE mem (a + 40 * n) 8).toNat, readNode mem (a + 40 * n + 8))] := by
  simp [entriesAt, List.range_succ]

/-- The node held at an index is the node of the first entry the search finds, if it finds one. -/
theorem nodeAt_entriesAt (mem : Memory) (a : Nat) (key : UInt64) :
    ∀ n, nodeAt (entriesAt mem a n) key.toNat =
      if firstAt (big32 mem a 40) key n < n then some (readNode mem (a + 40 * firstAt (big32 mem a 40) key n + 8))
      else none
  | 0 => by simp [entriesAt, nodeAt, firstAt]
  | n + 1 => by
    have ih := nodeAt_entriesAt mem a key n
    simp only [nodeAt] at ih ⊢
    rw [entriesAt_succ, List.find?_append]
    simp only [firstAt]
    by_cases early : firstAt (big32 mem a 40) key n < n
    · -- The match lies among the earlier entries.
      rw [ite_eq_left early] at ih
      have found : (entriesAt mem a n).find? (fun x => x.1 == key.toNat) ≠ none := by
        intro h; rw [h] at ih; simp at ih
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp found
      rw [hx] at ih ⊢
      have lt : firstAt (big32 mem a 40) key n < n + 1 := by omega
      simp only [Option.map_some, ite_eq_left early, ite_eq_left lt] at ih ⊢
      exact ih
    · rw [ite_eq_right early] at ih
      have none_ : (entriesAt mem a n).find? (fun x => x.1 == key.toNat) = none := by
        cases h : (entriesAt mem a n).find? (fun x => x.1 == key.toNat) with
        | none => rfl
        | some x => rw [h] at ih; simp at ih
      simp only [none_, ite_eq_right early, Option.none_or, List.find?_cons, List.find?_nil]
      by_cases hit : big32 mem a 40 n = key
      · have : ((readLE mem (a + 40 * n) 8).toNat == key.toNat) = true := by
          simp only [beq_iff_eq]; rw [← hit]; rfl
        simp [this, hit]
      · have : ((readLE mem (a + 40 * n) 8).toNat == key.toNat) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]
          intro e; exact hit (UInt64.toNat_inj.mp e)
        simp [this, hit]

end EthLib.Consensus.Ssz.Native.Driver.BranchProof
