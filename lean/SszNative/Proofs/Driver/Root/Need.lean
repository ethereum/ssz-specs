import SszNative.Proofs.Driver.Root.Chunked

/-!
The scratch bound of fixed-size roots covers what the roots driver uses.

Below the cap no step of the bound saturates, so each part of it is the plain sum or product it names.
A chunk of records needs at most what a full chunk does, so every chunk of a long run fits the room of a full one.
A plain type's saturated width is its width, as long as the width stays below the cap.
-/

namespace Ssz.Native.Driver

/-! ### Saturation -/

/-- The cap as a number. -/
theorem cap_eq : scratchCap = 4611686018427387904 := rfl

/-- A saturated number below the cap is the number. -/
theorem sat_of_lt {x : Nat} (h : sat x < scratchCap) : sat x = x := by
  simp only [sat] at h ⊢; omega

/-- A saturated sum below the cap is the sum. -/
theorem sadd_of_lt {a b : Nat} (h : sadd a b < scratchCap) : sadd a b = a + b := sat_of_lt h

/-- A saturated product below the cap is the product. -/
theorem smul_of_lt {a b : Nat} (h : smul a b < scratchCap) : smul a b = a * b := sat_of_lt h

/-- Saturation keeps order. -/
theorem sat_mono {x y : Nat} (h : x ≤ y) : sat x ≤ sat y := by
  simp only [sat]; omega

/-- A saturated sum grows with its terms. -/
theorem sadd_mono {a b c d : Nat} (h₁ : a ≤ c) (h₂ : b ≤ d) : sadd a b ≤ sadd c d := sat_mono (by omega)

/-- A saturated product grows with its factors. -/
theorem smul_mono {a b c d : Nat} (h₁ : a ≤ c) (h₂ : b ≤ d) : smul a b ≤ smul c d :=
  sat_mono (Nat.mul_le_mul h₁ h₂)

/-- The packed bound grows with the count. -/
theorem packedNeed_mono (width : Nat) {c c' : Nat} (h : c ≤ c') : packedNeed width c ≤ packedNeed width c' := by
  unfold packedNeed; dsimp only; split
  · exact smul_mono (Nat.le_refl _) h
  · exact sadd_mono (smul_mono (Nat.le_refl _) h) (smul_mono (smul_mono (Nat.le_refl _) h) (Nat.le_refl _))

/-- The larger of two numbers grows with both. -/
theorem max_mono {a b c d : Nat} (h₁ : a ≤ c) (h₂ : b ≤ d) : max a b ≤ max c d := by omega

/-! ### A chunk needs at most a full chunk -/

mutual

/-- The roots of at most a chunk of records need at most what a full chunk's do. -/
theorem rootsNeed_chunk (d : Desc) {c : Nat} (h : c ≤ recordsPerChunk) :
    rootsNeed d c ≤ rootsNeed d recordsPerChunk := by
  have capBig : 65536 ≤ scratchCap := by decide
  have chunk : recordsPerChunk = 1024 := rfl
  have m32 : min (32 * 1024) scratchCap = 32768 := Nat.min_eq_left (Nat.le_trans (by decide) capBig)
  have m64 : min (64 * 1024) scratchCap = 65536 := Nat.min_eq_left capBig
  match d with
  | .vector element length =>
    have ih := rootsNeed_chunk element h
    have top := rootsNeed_le element recordsPerChunk
    simp only [rootsNeed]
    split
    · exact packedNeed_mono _ h
    · by_cases one : c = 1
      · -- One record against a full chunk: every part of the full chunk's bound is linear in the length.
        subst one
        rw [if_pos rfl, if_neg (show ¬ (1024 : Nat) = 1 by decide)]
        have small : ∀ x, x ≤ recordsPerChunk → rootsNeed element x ≤ rootsNeed element recordsPerChunk :=
          fun x hx => rootsNeed_chunk element hx
        have satLen : sat length ≤ scratchCap := sat_le _
        generalize sat length = len at *
        have chunks : (if len ≤ recordsPerChunk then rootsNeed element len
            else sadd (smul 32 len) (rootsNeed element recordsPerChunk)) ≤
            sadd (smul 32 len) (rootsNeed element recordsPerChunk) := by
          split
          · exact Nat.le_trans (small len (by assumption)) (by simp only [sadd, sat]; omega)
          · exact Nat.le_refl _
        clear small ih
        generalize (if len ≤ recordsPerChunk then rootsNeed element len
          else sadd (smul 32 len) (rootsNeed element recordsPerChunk)) = K at *
        generalize rootsNeed element recordsPerChunk = R at *
        simp only [treeNeed, sadd, smul, sat, RootProgressive.spineBytes, zeroHeights, m32, m64] at chunks ⊢
        generalize scratchCap = C at *
        omega
      · rw [if_neg one, if_neg (show ¬ (1024 : Nat) = 1 by decide)]
        exact sadd_mono (sadd_mono (smul_mono (Nat.le_refl _) h)
          (smul_mono (smul_mono (Nat.le_refl _) h) (Nat.le_refl _)))
          (max_mono ih (smul_mono (smul_mono (Nat.le_refl _) h) (Nat.le_refl _)))
  | .container _ fields =>
    have most := fieldsRootsNeed_chunk fields h 0 0 (Nat.le_refl _)
    have top := fieldsRootsNeed_le fields recordsPerChunk 0 (Nat.zero_le _)
    simp only [rootsNeed]
    by_cases one : c = 1
    · -- One record against a full chunk: every part of the full chunk's bound is linear in the field count.
      subst one
      rw [if_pos rfl, if_neg (show ¬ (1024 : Nat) = 1 by decide)]
      have satLen : sat fields.length ≤ scratchCap := sat_le _
      generalize sat fields.length = n at *
      have mostLe := fieldsRootsNeed_le fields 1 0 (Nat.zero_le _)
      simp only [treeNeed, sadd, smul, sat, chunk, RootProgressive.spineBytes, zeroHeights, m32, m64] at most top mostLe ⊢
      omega
    · rw [if_neg one, if_neg (show ¬ (1024 : Nat) = 1 by decide)]
      exact sadd_mono (sadd_mono (smul_mono (Nat.le_refl _) h)
        (smul_mono (smul_mono (Nat.le_refl _) h) (Nat.le_refl _)))
        (max_mono most (smul_mono (smul_mono (Nat.le_refl _) h) (Nat.le_refl _)))
  | .bool | .uint _ | .byteVector _ | .bitVector _ | .byteList _ | .bitList _ => exact packedNeed_mono _ h
  | .progressiveBitList _ | .list _ _ | .progressiveList _ _ | .progressiveContainer _ _ _ => exact packedNeed_mono _ h
  | .compatibleUnion _ _ => exact packedNeed_mono _ h

/-- The most the fields' roots need, for at most a chunk of records, is at most that of a full chunk. -/
theorem fieldsRootsNeed_chunk (fs : List Desc) {c : Nat} (h : c ≤ recordsPerChunk) :
    ∀ most most', most ≤ most' → fieldsRootsNeed fs c most ≤ fieldsRootsNeed fs recordsPerChunk most' :=
  match fs with
  | [] => fun _ _ le => le
  | f :: rest => fun _ _ le => by
    simp only [fieldsRootsNeed]
    exact fieldsRootsNeed_chunk rest h _ _ (max_mono (rootsNeed_chunk f h) le)

end

/-! ### Each field within the most -/

/-- The most the fields need is at least the most so far. -/
theorem fieldsRootsNeed_ge : ∀ (fs : List Desc) (count most : Nat), most ≤ fieldsRootsNeed fs count most
  | [], _, _ => Nat.le_refl _
  | _ :: rest, count, _ => Nat.le_trans (Nat.le_max_right _ _) (fieldsRootsNeed_ge rest count _)

/-- Every field's roots need at most the most the fields need. -/
theorem fieldsRootsNeed_mem : ∀ (fs : List Desc) (count most : Nat), ∀ f ∈ fs,
    rootsNeed f count ≤ fieldsRootsNeed fs count most
  | [], _, _, _, mem => absurd mem (List.not_mem_nil)
  | g :: rest, count, most, f, mem => by
    simp only [fieldsRootsNeed]
    rcases List.mem_cons.mp mem with eq | mem
    · subst eq
      exact Nat.le_trans (Nat.le_max_left _ _) (fieldsRootsNeed_ge rest count _)
    · exact fieldsRootsNeed_mem rest count _ f mem

/-! ### Room for the roots -/

/-- The fixed-size roots bound leaves room for the roots themselves, one node per value. -/
theorem rootsNeed_roots (d : Desc) (count : Nat) : sat (32 * count) ≤ rootsNeed d count := by
  have packed : ∀ width, sat (32 * count) ≤ packedNeed width count := fun width => by
    unfold packedNeed; dsimp only; split
    · exact Nat.le_refl _
    · simp only [sadd, smul, sat]; omega
  cases d with
  | vector e l =>
    simp only [rootsNeed]
    split
    · exact packed _
    · split
      · rename_i one; subst one; simp only [sadd, sat]; omega
      · simp only [sadd, smul, sat]; omega
  | container _ fs =>
    simp only [rootsNeed]
    split
    · rename_i one; subst one; simp only [sadd, smul, sat]; omega
    · simp only [sadd, smul, sat]; omega
  | _ => exact packed _

/-! ### Widths of plain types -/

mutual

/-- A plain type has a fixed size, its width. -/
theorem fixedSize_plain : (d : Desc) → plain d = true → d.fixedSize = some (fixedWidth d)
  | .bool, _ | .uint _, _ | .byteVector _, _ | .bitVector _, _ => rfl
  | .vector e _, h => by
    simp only [plain] at h
    simp [Desc.fixedSize, fixedWidth, fixedSize_plain e h]
  | .container _ fs, h => by
    simp only [plain] at h
    exact fieldsFixedSize_plain fs h
  | .byteList _, h | .bitList _, h | .progressiveBitList _, h | .list _ _, h | .progressiveList _ _, h
  | .progressiveContainer _ _ _, h | .compatibleUnion _ _, h => by simp [plain] at h

/-- Plain types side by side have a fixed size, their total width. -/
theorem fieldsFixedSize_plain : (fs : List Desc) → plainAll fs = true → Desc.fieldsFixedSize fs = some (fieldsWidth fs)
  | [], _ => rfl
  | f :: rest, h => by
    simp only [plainAll, Bool.and_eq_true] at h
    simp [Desc.fieldsFixedSize, fieldsWidth, fixedSize_plain f h.1, fieldsFixedSize_plain rest h.2]

end

/-- A narrow plain type's width is below the cap. -/
theorem width_narrow (d : Desc) (pl : plain d = true) (thin : narrow d = true) : fixedWidth d < scratchCap := by
  have size := fixedSize_plain d pl
  have capv := cap_eq
  cases d with
  | bitVector n => simp only [narrow, decide_eq_true_eq] at thin; simp only [fixedWidth]; omega
  | vector e l =>
    simp only [narrow, size, Bool.and_eq_true, Option.all_some, decide_eq_true_eq] at thin; omega
  | container names fs =>
    simp only [narrow, size, Bool.and_eq_true, Option.all_some, decide_eq_true_eq] at thin; omega
  | bool => simp [fixedWidth]
  | uint n | byteVector n =>
    simp only [narrow, size, Option.all_some, decide_eq_true_eq] at thin; omega
  | _ => simp [plain] at pl

mutual

/-- A plain type's saturated width is its width, when that is below the cap. -/
theorem satWidth_plain : (d : Desc) → plain d = true → fixedWidth d < scratchCap → satWidth d = fixedWidth d
  | .bool, _, _ | .bitVector _, _, _ => rfl
  | .uint _, _, h | .byteVector _, _, h => by simp only [fixedWidth] at h; simp only [satWidth, sat, fixedWidth]; omega
  | .vector e l, pl, h => by
    simp only [plain] at pl
    simp only [fixedWidth] at h
    simp only [satWidth, fixedWidth]
    rcases Nat.eq_zero_or_pos l with z | lp
    · subst z; simp [smul, sat]
    have ew : fixedWidth e < scratchCap := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ lp) h
    rw [satWidth_plain e pl ew]
    rcases Nat.eq_zero_or_pos (fixedWidth e) with z | ep
    · rw [z]; simp [smul, sat]
    have ll : l < scratchCap := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left _ ep) h
    simp only [smul, sat]
    rw [Nat.min_eq_left (Nat.le_of_lt ll), Nat.min_eq_left (Nat.le_of_lt h)]
  | .container _ fs, pl, h => by
    simp only [plain] at pl
    simp only [fixedWidth] at h
    simp only [satWidth, fixedWidth]
    rw [satFieldsWidth_plain fs pl 0 (by omega), Nat.zero_add]
  | .byteList _, h, _ | .bitList _, h, _ | .progressiveBitList _, h, _ | .list _ _, h, _ | .progressiveList _ _, h, _
  | .progressiveContainer _ _ _, h, _ | .compatibleUnion _ _, h, _ => by simp [plain] at h

/-- Plain types' saturated total width, after a width so far, is the plain total when that is below the cap. -/
theorem satFieldsWidth_plain : (fs : List Desc) → plainAll fs = true → ∀ acc, acc + fieldsWidth fs < scratchCap →
    satFieldsWidth fs acc = acc + fieldsWidth fs
  | [], _, acc, _ => by simp [satFieldsWidth, fieldsWidth]
  | f :: rest, pl, acc, h => by
    simp only [plainAll, Bool.and_eq_true] at pl
    simp only [fieldsWidth] at h
    simp only [satFieldsWidth, fieldsWidth]
    rw [satWidth_plain f pl.1 (by omega), show sadd acc (fixedWidth f) = acc + fixedWidth f from
      by simp only [sadd, sat]; omega, satFieldsWidth_plain rest pl.2 _ (by omega), Nat.add_assoc]

end

end Ssz.Native.Driver
