import SszNative.Proofs.Driver.Root.Range

/-!
The scratch bound of a value grows with the size of its range.

A parent roots each child in the scratch its own bound leaves, which is the child's bound at the parent's size.
A child's range is never larger than its parent's, so a bound that grows with the size covers every child.
-/

namespace Ssz.Native.Driver

open Ssz

/-! ### The fixed-size bound in the count -/

mutual

/-- No records need no scratch. -/
theorem rootsNeed_zero (d : Desc) : rootsNeed d 0 = 0 := by
  match d with
  | .vector element length =>
    have ih := rootsNeed_zero element
    simp only [rootsNeed]
    split
    · simp [packedNeed, sadd, smul, sat]
    · rw [if_neg (by decide)]
      simp [ih, sadd, smul, sat]
  | .container _ fields =>
    have most := fieldsRootsNeed_zero fields 0 rfl
    simp only [rootsNeed]
    rw [if_neg (by decide)]
    simp [most, sadd, smul, sat]
  | .bool | .uint _ | .byteVector _ | .bitVector _ | .byteList _ | .bitList _ => simp [rootsNeed, packedNeed, sadd, smul, sat]
  | .progressiveBitList _ | .list _ _ | .progressiveList _ _ | .progressiveContainer _ _ _ =>
    simp [rootsNeed, packedNeed, sadd, smul, sat]
  | .compatibleUnion _ _ => simp [rootsNeed, packedNeed, sadd, smul, sat]

/-- The most the fields need for no records is the most so far. -/
theorem fieldsRootsNeed_zero (fs : List Desc) : ∀ most, most = 0 → fieldsRootsNeed fs 0 most = 0 :=
  match fs with
  | [] => fun _ h => h
  | f :: rest => fun _ h => by
    simp only [fieldsRootsNeed]
    exact fieldsRootsNeed_zero rest _ (by rw [rootsNeed_zero f, h]; rfl)

end

mutual

/-- From two records on, the fixed-size bound grows with the count. -/
theorem rootsNeed_grow (d : Desc) {c c' : Nat} (two : 2 ≤ c) (h : c ≤ c') : rootsNeed d c ≤ rootsNeed d c' := by
  match d with
  | .vector element length =>
    have ih := rootsNeed_grow element two h
    simp only [rootsNeed]
    split
    · exact packedNeed_mono _ h
    · rw [if_neg (by omega), if_neg (by omega)]
      exact sadd_mono (sadd_mono (smul_mono (Nat.le_refl _) h)
        (smul_mono (smul_mono (Nat.le_refl _) h) (Nat.le_refl _)))
        (max_mono ih (smul_mono (smul_mono (Nat.le_refl _) h) (Nat.le_refl _)))
  | .container _ fields =>
    have most := fieldsRootsNeed_grow fields two h 0 0 (Nat.le_refl _)
    simp only [rootsNeed]
    rw [if_neg (by omega), if_neg (by omega)]
    exact sadd_mono (sadd_mono (smul_mono (Nat.le_refl _) h)
      (smul_mono (smul_mono (Nat.le_refl _) h) (Nat.le_refl _)))
      (max_mono most (smul_mono (smul_mono (Nat.le_refl _) h) (Nat.le_refl _)))
  | .bool | .uint _ | .byteVector _ | .bitVector _ | .byteList _ | .bitList _ => exact packedNeed_mono _ h
  | .progressiveBitList _ | .list _ _ | .progressiveList _ _ | .progressiveContainer _ _ _ => exact packedNeed_mono _ h
  | .compatibleUnion _ _ => exact packedNeed_mono _ h

/-- From two records on, the most the fields need grows with the count. -/
theorem fieldsRootsNeed_grow (fs : List Desc) {c c' : Nat} (two : 2 ≤ c) (h : c ≤ c') :
    ∀ most most', most ≤ most' → fieldsRootsNeed fs c most ≤ fieldsRootsNeed fs c' most' :=
  match fs with
  | [] => fun _ _ le => le
  | f :: rest => fun _ _ le => by
    simp only [fieldsRootsNeed]
    exact fieldsRootsNeed_grow rest two h _ _ (max_mono (rootsNeed_grow f two h) le)

end

/-- A list's bound on its records' roots, one record's need as a floor, grows with the node count. -/
theorem recordsNeed_mono (e : Desc) {n n' : Nat} (h : n ≤ n') :
    max (rootsNeed e 1) (rootsNeed e (min n recordsPerChunk)) ≤
      max (rootsNeed e 1) (rootsNeed e (min n' recordsPerChunk)) := by
  have hm : min n recordsPerChunk ≤ min n' recordsPerChunk := by omega
  generalize min n recordsPerChunk = a at hm
  generalize min n' recordsPerChunk = a' at hm
  rcases Nat.lt_or_ge a 2 with small | two
  · rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl
    · rw [rootsNeed_zero]; omega
    · omega
  · have := rootsNeed_grow e two hm; omega

/-! ### The scratch bound in the size -/

/-- The tree's bound grows with its node count. -/
theorem treeNeed_mono {n n' : Nat} (h : n ≤ n') : treeNeed n ≤ treeNeed n' :=
  sadd_mono (Nat.le_refl _) (smul_mono (Nat.le_refl _) h)

/-- The nodes a range packs into grow with its size. -/
theorem nodesFor_mono {s s' : Nat} (h : s ≤ s') : nodesFor s ≤ nodesFor s' := Nat.div_le_div_right (by omega)

/-- The node bound of a list grows with its size. -/
theorem nodesBound_mono (e : Desc) {s s' : Nat} (h : s ≤ s') : nodesBound e s ≤ nodesBound e s' := by
  unfold nodesBound
  apply sat_mono
  split
  · exact nodesFor_mono h
  · split
    · split
      · exact Nat.le_refl _
      · exact Nat.div_le_div_right h
    · exact Nat.div_le_div_right h

mutual

/-- The scratch bound of a value grows with the size of its range. -/
theorem varNeed_mono (d : Desc) {s s' : Nat} (h : s ≤ s') : varNeed d s ≤ varNeed d s' := by
  match d with
  | .byteList _ | .bitList _ | .progressiveBitList _ =>
    simp only [varNeed]
    exact sadd_mono (sadd_mono (Nat.le_refl _) (smul_mono (Nat.le_refl _) (nodesFor_mono h)))
      (treeNeed_mono (nodesFor_mono h))
  | .vector element length =>
    have ih := varNeed_mono element h
    simp only [varNeed]
    split
    · exact Nat.le_refl _
    · exact sadd_mono (Nat.le_refl _) (max_mono ih (Nat.le_refl _))
  | .list element _ | .progressiveList element _ =>
    have ih := varNeed_mono element h
    have nb := nodesBound_mono element h
    simp only [varNeed]
    refine sadd_mono (sadd_mono (Nat.le_refl _) (smul_mono (Nat.le_refl _) nb)) (max_mono ?_ (treeNeed_mono nb))
    split
    · exact Nat.le_refl _
    · split
      · exact recordsNeed_mono element nb
      · exact ih
  | .container names fields =>
    have most := fieldsVarNeed_mono fields h 0 0 (Nat.le_refl _)
    simp only [varNeed]
    split
    · exact Nat.le_refl _
    · exact max_mono (sadd_mono (Nat.le_refl _) most) (Nat.le_refl _)
  | .progressiveContainer _ _ fields =>
    have most := fieldsVarNeed_mono fields h 0 0 (Nat.le_refl _)
    simp only [varNeed]
    exact sadd_mono (Nat.le_refl _) (max_mono (sadd_mono (Nat.le_refl _) most) (Nat.le_refl _))
  | .compatibleUnion _ options =>
    have most := fieldsVarNeed_mono options h 0 0 (Nat.le_refl _)
    simp only [varNeed]
    exact sadd_mono (Nat.le_refl _) most
  | .bool | .uint _ | .byteVector _ | .bitVector _ => simp only [varNeed]; exact Nat.le_refl _

/-- The most several types need grows with the size. -/
theorem fieldsVarNeed_mono (fs : List Desc) {s s' : Nat} (h : s ≤ s') :
    ∀ most most', most ≤ most' → fieldsVarNeed fs s most ≤ fieldsVarNeed fs s' most' :=
  match fs with
  | [] => fun _ _ le => le
  | f :: rest => fun _ _ le => by
    simp only [fieldsVarNeed]
    exact fieldsVarNeed_mono rest h _ _ (max_mono (varNeed_mono f h) le)

end

/-- The most several types need is at least the most so far. -/
theorem fieldsVarNeed_ge : ∀ (fs : List Desc) (size most : Nat), most ≤ fieldsVarNeed fs size most
  | [], _, _ => Nat.le_refl _
  | _ :: rest, size, _ => Nat.le_trans (Nat.le_max_right _ _) (fieldsVarNeed_ge rest size _)

/-- Each of several types needs at most the most they need. -/
theorem fieldsVarNeed_mem : ∀ (fs : List Desc) (size most : Nat), ∀ f ∈ fs,
    varNeed f size ≤ fieldsVarNeed fs size most
  | [], _, _, _, mem => absurd mem (List.not_mem_nil)
  | g :: rest, size, most, f, mem => by
    simp only [fieldsVarNeed]
    rcases List.mem_cons.mp mem with eq | mem
    · subst eq
      exact Nat.le_trans (Nat.le_max_left _ _) (fieldsVarNeed_ge rest size _)
    · exact fieldsVarNeed_mem rest size _ f mem

end Ssz.Native.Driver
