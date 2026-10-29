import SszNative.Plan

/-!
A plan read back is the type it was written from, with its fields renamed by position.

Every number a plan holds must fit a word, and every union must pair its selectors with its options.
-/

namespace Ssz.Native.Plan

open Ssz

/-- Layout bits written as words and read back as flags are the bits. -/
theorem bits_roundTrip (active : List Bool) :
    (active.map fun b => if b then 1 else 0).map (· != 0) = active := by
  induction active with
  | nil => rfl
  | cons b rest ih => cases b <;> simp_all

/-- Every type's node takes at least its tag word. -/
theorem words_ne_nil (d : Desc) : 1 ≤ (words d).length := by
  cases d <;> simp [words]

mutual

/-- A type's words, read from a plan with enough fuel, are the renamed type and nothing more. -/
theorem readNode_words : ∀ (d : Desc), paired d = true → ∀ (fuel : Nat) (rest : List Nat),
    (words d).length ≤ fuel → readNode fuel (words d ++ rest) = some (rename d, rest)
  | .bool, _, fuel + 1, rest, _ => by simp [words, readNode, rename]
  | .uint _, _, fuel + 1, rest, _ => by simp [words, readNode, rename]
  | .byteVector _, _, fuel + 1, rest, _ => by simp [words, readNode, rename]
  | .byteList _, _, fuel + 1, rest, _ => by simp [words, readNode, rename]
  | .bitVector _, _, fuel + 1, rest, _ => by simp [words, readNode, rename]
  | .bitList _, _, fuel + 1, rest, _ => by simp [words, readNode, rename]
  | .progressiveBitList limit, _, fuel + 1, rest, _ => by
    cases limit <;> simp [words, readNode, rename, bound, readBound, canonicalBound]
  | .vector element length, ok, fuel + 1, rest, room => by
    have := readNode_words element (by simpa [paired] using ok) fuel rest (by simp [words] at room; omega)
    simp [words, readNode, rename, this]
  | .list element limit, ok, fuel + 1, rest, room => by
    have := readNode_words element (by simpa [paired] using ok) fuel rest (by simp [words] at room; omega)
    simp [words, readNode, rename, this]
  | .progressiveList element limit, ok, fuel + 1, rest, room => by
    have := readNode_words element (by simpa [paired] using ok) fuel rest
      (by cases limit <;> simp [words, bound] at room <;> omega)
    cases limit <;> simp [words, readNode, rename, bound, readBound, canonicalBound, this]
  | .container names fields, ok, fuel + 1, rest, room => by
    have := readNodes_words fields (by simpa [paired] using ok) fuel rest (by simp [words] at room; omega)
    simp [words, readNode, rename, this]
  | .progressiveContainer active names fields, ok, fuel + 1, rest, room => by
    have := readNodes_words fields (by simpa [paired] using ok) fuel rest (by simp [words] at room; omega)
    -- The layout is as many words as bits, then the field count.
    have take : ((active.map fun (b : Bool) => if b then 1 else 0) ++ fields.length :: (wordsAll fields ++ rest)).take
        active.length = active.map fun (b : Bool) => if b then 1 else 0 := by simp
    have drop : ((active.map fun (b : Bool) => if b then 1 else 0) ++ fields.length :: (wordsAll fields ++ rest)).drop
        active.length = fields.length :: (wordsAll fields ++ rest) := by simp
    simp only [words, List.cons_append, List.nil_append, List.append_assoc, readNode]
    rw [take, drop, bits_roundTrip]
    simp [this, rename]
  | .compatibleUnion selectors options, ok, fuel + 1, rest, room => by
    simp only [paired, Bool.and_eq_true, beq_iff_eq] at ok
    have := readNodes_words options ok.2 fuel rest (by simp [words] at room; omega)
    have take : (selectors ++ (wordsAll options ++ rest)).take options.length = selectors := by simp [← ok.1]
    have drop : (selectors ++ (wordsAll options ++ rest)).drop options.length = wordsAll options ++ rest := by
      simp [← ok.1]
    simp only [words, List.cons_append, List.nil_append, List.append_assoc, readNode]
    rw [take, drop]
    simp [this, rename]
  | d, _, 0, _, room => by
    -- Every node takes a word, so no fuel is too little.
    have := words_ne_nil d
    omega

/-- Several types' words, read with enough fuel, are the renamed types and nothing more. -/
theorem readNodes_words : ∀ (ds : List Desc), pairedAll ds = true → ∀ (fuel : Nat) (rest : List Nat),
    (wordsAll ds).length + 1 ≤ fuel → readNodes fuel ds.length (wordsAll ds ++ rest) = some (renameAll ds, rest)
  | [], _, fuel, rest, _ => by cases fuel <;> simp [readNodes, renameAll, wordsAll]
  | d :: ds, ok, fuel + 1, rest, room => by
    simp only [pairedAll, Bool.and_eq_true] at ok
    have one := words_ne_nil d
    have head := readNode_words d ok.1 fuel (wordsAll ds ++ rest) (by simp [wordsAll] at room; omega)
    have tail := readNodes_words ds ok.2 fuel rest (by simp [wordsAll] at room; omega)
    simp [wordsAll, readNodes, head, tail, renameAll]
  | _ :: _, _, 0, _, room => by simp at room

end

/-- The bytes of words, at a word's index and a byte's place in it, are that word's byte. -/
theorem flatMap_wordBytes (ws : List Nat) : ∀ i k, i < ws.length → k < 8 →
    (ws.flatMap wordBytes)[8 * i + k]? = some (UInt8.ofNat (ws[i]! >>> (8 * k))) := by
  induction ws with
  | nil => intro i k h; simp at h
  | cons w rest ih =>
    intro i k hi hk
    have len : (wordBytes w).length = 8 := by simp [wordBytes]
    cases i with
    | zero =>
      rw [List.flatMap_cons, List.getElem?_append_left (by omega)]
      simp [wordBytes, hk]
    | succ i =>
      -- Past the first word, the bytes are the rest's, eight places earlier.
      rw [List.flatMap_cons, List.getElem?_append_right (by omega), len]
      have := ih i k (by simp at hi; omega) hk
      simpa [show 8 * (i + 1) + k - 8 = 8 * i + k by omega] using this

/-- The first bytes of a word, read back little-endian, are the word modulo their range. -/
theorem digits_sum (w : Nat) (byte : Nat → UInt8) (same : ∀ k < 8, byte k = UInt8.ofNat (w >>> (8 * k))) :
    ∀ n ≤ 8, (List.range n).foldl (fun acc k => acc + (byte k).toNat * 256 ^ k) 0 = w % 256 ^ n
  | 0, _ => by simp [Nat.mod_one]
  | n + 1, room => by
    rw [List.range_succ, List.foldl_append, digits_sum w byte same n (by omega)]
    simp only [List.foldl_cons, List.foldl_nil, same n (by omega), Nat.shiftRight_eq_div_pow]
    -- One more byte is one more digit in base 256.
    rw [Nat.pow_succ, Nat.mod_mul, show 2 ^ (8 * n) = 256 ^ n by rw [Nat.pow_mul]]
    simp [Nat.mul_comm]

/-- Words that each fit 64 bits, written as bytes and read back, are the words. -/
theorem toWords_bytes (ws : List Nat) (small : ∀ w ∈ ws, w < 2 ^ 64) :
    toWords ⟨(ws.flatMap wordBytes).toArray⟩ = ws := by
  have size : (ws.flatMap wordBytes).length = 8 * ws.length := by
    induction ws with
    | nil => rfl
    | cons w rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [ih (fun v h => small v (List.mem_cons_of_mem _ h))]
      simp [wordBytes]
      omega
  apply List.ext_getElem
  · simp [toWords, ByteArray.size, size]
  · intro i hi _
    simp only [toWords, List.getElem_map, List.getElem_range]
    have inside : i < ws.length := by simp [toWords, ByteArray.size, size] at hi; omega
    have digits := digits_sum ws[i] (fun k => ByteArray.get! ⟨(ws.flatMap wordBytes).toArray⟩ (8 * i + k))
      (fun k hk => by
        have := flatMap_wordBytes ws i k inside hk
        simp only [ByteArray.get!, getElem!_def]
        simp [this, getElem!_pos ws i inside]) 8 (Nat.le_refl 8)
    rw [digits, Nat.mod_eq_of_lt (small _ (List.getElem_mem inside))]

/-- Every number a type's plan holds fits a word. -/
def Fits (d : Desc) : Prop := ∀ w ∈ words d, w < 2 ^ 64

/--
A plan read back is the type it was written from, with every field named by position.

Every number of the type must fit a word, and every union must pair its selectors with its options.
-/
theorem decode_encode (d : Desc) (ok : paired d = true) (fits : Fits d) : decode (encode d) = some (rename d) := by
  have ws : toWords (encode d) = words d := toWords_bytes (words d) fits
  have size : (encode d).size = 8 * (words d).length := by
    have := congrArg List.length ws
    simp only [toWords, List.length_map, List.length_range] at this
    have : (encode d).size = ((words d).flatMap wordBytes).length := by simp [encode, ByteArray.size]
    rw [this]
    clear this
    induction words d with
    | nil => rfl
    | cons w rest ih => simp [wordBytes] at ih ⊢; omega
  unfold decode
  rw [if_neg (by simp [size]), ws]
  have := readNode_words d ok (words d).length [] (Nat.le_refl _)
  simp only [List.append_nil] at this
  simp [this]

end Ssz.Native.Plan
