import SszNative.Proofs.Driver.Codec
import SszNative.Codec

/-!
The ranges driver writes the ranges `viewRanges` computes.

Memory holds the encoding as bytes from an address, and the output as words from another.
The output is written word by word: the count, then each range's start and stop.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Plan

/-- Memory with some of the words from an address replaced, those a test picks, by what a function gives. -/
def wordsAt (a : Nat) (f : Nat → UInt64) (written : Nat → Bool) (mem : Memory) : Memory :=
  fun x => if a ≤ x ∧ written ((x - a) / 8) then qwordByte (f ((x - a) / 8)) ((x - a) % 8) else mem x

/-- No word written leaves memory as it was. -/
theorem wordsAt_none (a : Nat) (f : Nat → UInt64) (mem : Memory) : wordsAt a f (fun _ => false) mem = mem := by
  funext x; simp [wordsAt]

/-- Storing one more of the words adds it to the words written. -/
theorem store_wordsAt (a : Nat) (f : Nat → UInt64) (written : Nat → Bool) (mem : Memory) (k : Nat) :
    store (wordsAt a f written mem) (a + 8 * k) 8 (qwordByte (f k)) =
      wordsAt a f (fun j => j == k || written j) mem := by
  funext x
  simp only [store, wordsAt]
  by_cases inside : a + 8 * k ≤ x ∧ x < a + 8 * k + 8
  · have word : (x - a) / 8 = k := by omega
    have byte : x - (a + 8 * k) = (x - a) % 8 := by omega
    simp [inside, word, byte, show a ≤ x by omega]
  · rw [ite_eq_right inside]
    by_cases above : a ≤ x
    · have other : ((x - a) / 8 == k) = false := by simp; omega
      simp [above, other]
    · simp [above]

/-- A word stored at an address and read back. -/
theorem readLE_wordsAt (a : Nat) (f : Nat → UInt64) (written : Nat → Bool) (mem : Memory) (k : Nat)
    (holds : written k = true) : readLE (wordsAt a f written mem) (a + 8 * k) 8 = f k := by
  have := readLE_store8 (wordsAt a f written mem) (a + 8 * k) (f k)
  rw [store_wordsAt] at this
  have same : (fun j => j == k || written j) = written := by
    funext j; by_cases e : j = k
    · subst e; simp [holds]
    · simp [e]
  rwa [same] at this

/-- Bytes from an address in the program's memory include every part of them. -/
theorem access_inside {w : World} {a n : Nat} (h : w.access a n) (k m : Nat) (inside : k + m ≤ n) :
    w.access (a + k) m := by
  simp only [World.access, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  omega

/-- The words of a view: the count, then each range's start and stop. -/
def viewWord (ranges : List (Nat × Nat)) (k : Nat) : UInt64 :=
  if k = 0 then ranges.length.toUInt64
  else if (k - 1) % 2 = 0 then (ranges.getD ((k - 1) / 2) (0, 0)).1.toUInt64
  else (ranges.getD ((k - 1) / 2) (0, 0)).2.toUInt64

/-- Memory after a view's words are written to an output. -/
def viewed (out : Nat) (ranges : List (Nat × Nat)) (mem : Memory) : Memory :=
  wordsAt out (viewWord ranges) (fun k => k < 1 + 2 * ranges.length) mem

/-- An encoding's bytes from an address. -/
def BytesAt (mem : Memory) (data : Nat) (b : ByteArray) : Prop :=
  ∀ k < b.size, mem (data + k) = b.get! k

/-- The driver's outcome for ranges a reference computes: the code, and the memory after. -/
def viewOutcome (out cap : Nat) (mem : Memory) : Except Err (List (Nat × Nat)) → UInt64 × Memory
  | .ok ranges => if ranges.length ≤ cap then (0, viewed out ranges mem) else (2, mem)
  | .error _ => (1, mem)

/-- A small number's word compares as the number does. -/
theorem ofNat_le_iff (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : UInt64.ofNat a ≤ UInt64.ofNat b ↔ a ≤ b := by
  rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' (lt_size ha), UInt64.toNat_ofNat_of_lt' (lt_size hb)]

/-- The word after a small number's is below another's as the number after it is. -/
theorem ofNat_succ_lt (a b : Nat) (ha : a + 1 < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNat a + 1 < UInt64.ofNat b ↔ a + 1 < b := by
  rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, ← UInt64.ofNat_add]
  exact ofNat_lt_ofNat _ _ ha hb

/-- The difference of small numbers' words is the word of their difference. -/
theorem ofNat_sub (a b : Nat) (le : b ≤ a) (ha : a < 2 ^ 64) : UInt64.ofNat a - UInt64.ofNat b = UInt64.ofNat (a - b) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ ((ofNat_le_iff b a (by omega) ha).mpr le), UInt64.toNat_ofNat_of_lt' (lt_size ha),
    UInt64.toNat_ofNat_of_lt' (lt_size (by omega)), UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]

/-- An at-most comparison holds when the first word is at most the second. -/
theorem holds_be (x y : UInt64) : Cond.holds .be (x == y) (decide (x < y)) = decide (x ≤ y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Cond.holds, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, UInt64.lt_iff_toNat_lt,
    UInt64.le_iff_toNat_le, ← UInt64.toNat_inj]
  omega

/-- Small numbers have the same word exactly when they are the same. -/
theorem ofNat_eq_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : UInt64.ofNat a = UInt64.ofNat b ↔ a = b := by
  rw [← UInt64.toNat_inj, UInt64.toNat_ofNat_of_lt' (lt_size ha), UInt64.toNat_ofNat_of_lt' (lt_size hb)]

/-- Storing the first of the words adds it to the words written. -/
theorem store_wordsAt_zero (a : Nat) (f : Nat → UInt64) (written : Nat → Bool) (mem : Memory) :
    store (wordsAt a f written mem) a 8 (qwordByte (f 0)) = wordsAt a f (fun j => j == 0 || written j) mem := by
  simpa using store_wordsAt a f written mem 0

/-- The words of a view of ranges given by index: the start and the stop of each. -/
theorem viewWord_map (g : Nat → Nat × Nat) (n i : Nat) (small : i < n) :
    viewWord ((List.range n).map g) (1 + 2 * i) = (g i).1.toUInt64 ∧
      viewWord ((List.range n).map g) (2 + 2 * i) = (g i).2.toUInt64 := by
  constructor
  · simp only [viewWord]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), show (1 + 2 * i - 1) / 2 = i by omega]
    simp [List.getD_eq_getElem?_getD, small]
  · simp only [viewWord]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), show (2 + 2 * i - 1) / 2 = i by omega]
    simp [List.getD_eq_getElem?_getD, small]

/-- The word of a view at a range's start or stop, for ranges one width apart. -/
theorem viewWord_stride (start width count i : Nat) (small : i < count) :
    viewWord (Ranges.stride start width count).toList (1 + 2 * i) = (start + i * width).toUInt64 ∧
      viewWord (Ranges.stride start width count).toList (2 + 2 * i) = (start + (i + 1) * width).toUInt64 := by
  constructor
  · simp only [viewWord]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), show (1 + 2 * i - 1) / 2 = i by omega]
    simp [Ranges.toList, List.getD_eq_getElem?_getD, small]
  · simp only [viewWord]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), show (2 + 2 * i - 1) / 2 = i by omega]
    simp [Ranges.toList, List.getD_eq_getElem?_getD, small]

set_option linter.unusedSimpArgs false in
/-- The ranges of elements one width apart: written when they fit, and nothing written otherwise. -/
theorem stride_ok (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory)
    (start width count out cap : Nat) (room : w.stackLo + 8 + 8 * strideRanges.frame ≤ sp)
    (smallCount : count < 2 ^ 64)
    (smallCap : cap < 2 ^ 64) (capacity : readLE mem out 8 = cap.toUInt64) (writable : w.access out (8 + 16 * cap)) :
    Calls m w "ssz_stride_ranges" sp [start.toUInt64, width.toUInt64, count.toUInt64, out.toUInt64] mem
      (viewOutcome out cap mem (.ok (Ranges.stride start width count).toList)).1
      (viewOutcome out cap mem (.ok (Ranges.stride start width count).toList)).2 := by
  have found : m.fns.lookup "ssz_stride_ranges" = some strideRanges :=
    linked ("ssz_stride_ranges", strideRanges) (by simp [codecFns])
  have outBound : out + 8 + 16 * cap ≤ 2 ^ 63 := by
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at writable; simp [addressBound] at writable; omega
  have lenEq : (Ranges.stride start width count).toList.length = count := by simp [Ranges.toList]
  let inner := sp - 8 - 8 * strideRanges.frame
  let args := [start.toUInt64, width.toUInt64, count.toUInt64, out.toUInt64]
  have readable : w.access out 8 := access_inside writable 0 8 (by omega)
  simp only [viewOutcome, lenEq]
  by_cases fits : count ≤ cap
  · simp only [fits, ite_true]
    let f := viewWord (Ranges.stride start width count).toList
    -- After i elements, the words of their ranges are written.
    let inv : Env → Memory → Prop := fun env cur =>
      ∃ i, i ≤ count ∧ env 0 = start.toUInt64 ∧ env 1 = width.toUInt64 ∧ env 2 = count.toUInt64 ∧
        env 3 = out.toUInt64 ∧ env 4 = 2 ∧ env 5 = i.toUInt64 ∧
        cur = wordsAt out f (fun k => 1 ≤ k ∧ k < 1 + 2 * i) mem
    have loop := Runs.loop_inv (m := m) (w := w) (sp := inner)
      (c := Expr.lt (.var 5) (.var 2))
      (body := .block [Stmt.st (Expr.var 3 + 8 + 16 * Expr.var 5) (Expr.var 0 + Expr.var 5 * Expr.var 1),
        Stmt.st (Expr.var 3 + 16 + 16 * Expr.var 5) (Expr.var 0 + (Expr.var 5 + 1) * Expr.var 1),
        .set 5 (Expr.var 5 + 1)])
      inv (fun env _ => count - (env 5).toNat)
      (fun env cur _ => ⟨_, rfl⟩)
      (by
        rintro env cur v ⟨i, within, e0, e1, e2, e3, e4, e5, hcur⟩ cond nonzero
        subst cur
        have small : i < 2 ^ 64 := by omega
        have more : i < count := by
          simp only [Expr.lt, eval, e2, e5, Cond.holds] at cond
          by_cases done : i < count
          · exact done
          · simp [ofNat_lt_iff i _ small, Nat.mod_eq_of_lt smallCount, done] at cond
            exact absurd cond.symm nonzero
        obtain ⟨wStart, wStop⟩ := viewWord_stride start width count i more
        have a1 : (UInt64.ofNat out + 8 + 16 * UInt64.ofNat i).toNat = out + 8 * (1 + 2 * i) := by
          rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
            UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
          simp; omega
        have a2 : (UInt64.ofNat out + 16 + 16 * UInt64.ofNat i).toNat = out + 8 * (2 + 2 * i) := by
          rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
            UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
          simp; omega
        have first := Runs.store m w inner env (wordsAt out f (fun k => 1 ≤ k ∧ k < 1 + 2 * i) mem) .b8
          (Expr.var 3 + 8 + 16 * Expr.var 5) (Expr.var 0 + Expr.var 5 * Expr.var 1)
          (UInt64.ofNat out + 8 + 16 * UInt64.ofNat i) (f (1 + 2 * i))
          (by simp [eval, e3, e5, aluResult])
          (by simp [eval, e0, e1, e5, aluResult, f, wStart])
          (by rw [a1]; exact access_inside writable _ 8 (by omega))
        rw [a1, Width.bytes, store_wordsAt] at first
        have second := Runs.store m w inner env
          (wordsAt out f (fun j => j == 1 + 2 * i || decide (1 ≤ j ∧ j < 1 + 2 * i)) mem) .b8
          (Expr.var 3 + 16 + 16 * Expr.var 5) (Expr.var 0 + (Expr.var 5 + 1) * Expr.var 1)
          (UInt64.ofNat out + 16 + 16 * UInt64.ofNat i) (f (2 + 2 * i))
          (by simp [eval, e3, e5, aluResult])
          (by simp [eval, e0, e1, e5, aluResult, f, wStop])
          (by rw [a2]; exact access_inside writable _ 8 (by omega))
        rw [a2, Width.bytes, store_wordsAt] at second
        have grown : (fun j => j == 2 + 2 * i || (j == 1 + 2 * i || decide (1 ≤ j ∧ j < 1 + 2 * i))) =
            (fun k => decide (1 ≤ k ∧ k < 1 + 2 * (i + 1))) := by
          funext j
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
          omega
        rw [grown] at second
        have next := Runs.set m w inner env (wordsAt out f (fun k => decide (1 ≤ k ∧ k < 1 + 2 * (i + 1))) mem) 5
          (Expr.var 5 + 1) (i + 1).toUInt64 (by simp [eval, e5, aluResult])
        refine ⟨_, _, Runs.block_cons first (Runs.block_cons second next),
          ⟨i + 1, more, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩, ?_⟩
        all_goals simp [assign, e0, e1, e2, e3, e4, e5, toNat_toUInt64 _ small,
          Nat.mod_eq_of_lt (show i + 1 < 2 ^ 64 by omega)]
        all_goals omega)
    have r2 := Runs.set m w inner (entryEnv args) mem 4 (.lit 2) 2 rfl
    let env₁ := assign (entryEnv args) 4 2
    have check : eval w env₁ mem (Expr.le (.var 2) (.load .b8 (.var 3))) = some 1 := by
      simp [env₁, args, eval, Expr.le, assign, entryEnv, Cond.holds, capacity, Width.bytes,
        toNat_toUInt64 out (by omega), readable]
      simp [ofNat_lt_ofNat _ _ smallCount smallCap, ofNat_lt_ofNat _ _ smallCap smallCount,
        ofNat_eq_ofNat _ _ smallCount smallCap, ofNat_le_iff _ _ smallCap smallCount]
      omega
    have i0 := Runs.set m w inner env₁ mem 5 (.lit 0) 0 rfl
    have none : wordsAt out f (fun k => decide (1 ≤ k ∧ k < 1 + 2 * 0)) mem = mem := by
      have empty : (fun k => decide (1 ≤ k ∧ k < 1 + 2 * 0)) = (fun _ => false) := by
        funext k; simp; omega
      rw [empty, wordsAt_none]
    obtain ⟨env', mem', runs, ⟨i, within, e0, e1, e2, e3, e4, e5, hmem⟩, exit⟩ :=
      loop (assign env₁ 5 0) mem ⟨0, Nat.zero_le _, by simp [env₁, assign, args, entryEnv],
        by simp [env₁, assign, args, entryEnv], by simp [env₁, assign, args, entryEnv],
        by simp [env₁, assign, args, entryEnv], by simp [env₁, assign], by simp [assign], none.symm⟩
    subst mem'
    -- The loop stops once every element's range is written.
    have done : i = count := by
      have small : i < 2 ^ 64 := by omega
      simp only [Expr.lt, eval, e2, e5, Cond.holds] at exit
      simp [ofNat_lt_iff i _ small, Nat.mod_eq_of_lt smallCount] at exit
      omega
    subst done
    -- The count goes in the first word.
    have countWord : f 0 = i.toUInt64 := by simp [f, viewWord, lenEq]
    have stored := Runs.store m w inner env' (wordsAt out f (fun k => decide (1 ≤ k ∧ k < 1 + 2 * i)) mem) .b8
      (.var 3) (.var 2) out.toUInt64 (f 0) (by simp [eval, e3]) (by simp [eval, e2, countWord])
      (by rw [toNat_toUInt64 out (by omega)]; exact readable)
    rw [toNat_toUInt64 out (by omega), Width.bytes, store_wordsAt_zero] at stored
    have whole : (fun j => j == 0 || decide (1 ≤ j ∧ j < 1 + 2 * i)) = (fun k => decide (k < 1 + 2 * i)) := by
      funext j
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      omega
    rw [whole] at stored
    have r0 := Runs.set m w inner env' (wordsAt out f (fun k => decide (k < 1 + 2 * i)) mem) 4 (.lit 0) 0 rfl
    have final : viewed out (Ranges.stride start width i).toList mem =
        wordsAt out f (fun k => decide (k < 1 + 2 * i)) mem := by
      simp only [viewed, lenEq]; rfl
    rw [final]
    refine Calls.fn (env' := assign env' 4 0) found room rfl ?_ (by simp [strideRanges, Stride.r, eval, assign])
    exact Runs.block_cons r2 (Runs.block_cons (Runs.ite_true 1 check (by decide)
      (Runs.block_cons i0 (Runs.block_cons runs (Runs.block_cons stored r0)))) (Runs.block_nil _ _ _ _ _))
  · simp only [fits, ite_false]
    have r2 := Runs.set m w inner (entryEnv args) mem 4 (.lit 2) 2 rfl
    have check : eval w (assign (entryEnv args) 4 2) mem (Expr.le (.var 2) (.load .b8 (.var 3))) = some 0 := by
      simp [args, eval, Expr.le, assign, entryEnv, Cond.holds, capacity, Width.bytes,
        toNat_toUInt64 out (by omega), readable]
      simp [ofNat_lt_ofNat _ _ smallCount smallCap, ofNat_lt_ofNat _ _ smallCap smallCount,
        ofNat_eq_ofNat _ _ smallCount smallCap, ofNat_le_iff _ _ smallCap smallCount]
      omega
    refine Calls.fn (env' := assign (entryEnv args) 4 2) found room rfl ?_
      (by simp [strideRanges, Stride.r, eval, assign])
    exact Runs.block_cons r2 (Runs.block_cons (Runs.ite_false check (Runs.block_nil _ _ _ _ _))
      (Runs.block_nil _ _ _ _ _))

/-- Where a body opened by an offset table ends: at the next offset, or at the end of the scope. -/
def nextOffset (offsets : List Nat) (scope i : Nat) : Nat :=
  (offsets ++ [scope]).getD (i + 1) 0

/-- A table whose offsets each reach no further than where their body ends opens the bodies between them. -/
theorem offsetSpans_ordered (start scope : Nat) : ∀ (offsets : List Nat),
    (∀ i (h : i < offsets.length), offsets[i] ≤ nextOffset offsets scope i) →
    ∃ spans, offsetSpans offsets scope = .ok spans ∧
      bodies start offsets spans =
        (List.range offsets.length).map fun i => (start + offsets.getD i 0, start + nextOffset offsets scope i)
  | [], _ => ⟨[], by simp [offsetSpans, bodies]⟩
  | [o], ordered => by
    have := ordered 0 (by simp)
    simp [nextOffset] at this
    refine ⟨[scope - o], by simp [offsetSpans, show ¬ scope < o by omega], ?_⟩
    simp [bodies, nextOffset]
    omega
  | o :: next :: rest, ordered => by
    have first := ordered 0 (by simp)
    simp [nextOffset] at first
    obtain ⟨spans, read, cut⟩ := offsetSpans_ordered start scope (next :: rest) (fun i h => by
      have := ordered (i + 1) (by simp at h ⊢; omega)
      simpa [nextOffset] using this)
    refine ⟨(next - o) :: spans, by simp [offsetSpans, show ¬ next < o by omega, read, Bind.bind, Except.bind,
      pure, Except.pure], ?_⟩
    have whole : bodies start (o :: next :: rest) ((next - o) :: spans) =
        (start + o, start + next) :: bodies start (next :: rest) spans := by
      simp only [bodies, List.zip_cons_cons, List.map_cons]
      congr 2
      omega
    rw [whole, cut]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    cases i with
    | zero => simp [nextOffset]
    | succ i => simp [nextOffset]

/-- A table with an offset past where its body ends is refused. -/
theorem offsetSpans_unordered (scope : Nat) : ∀ (offsets : List Nat),
    (∃ i, ∃ h : i < offsets.length, nextOffset offsets scope i < offsets[i]) →
    ∃ e, offsetSpans offsets scope = .error e
  | [], ⟨i, h, _⟩ => by simp at h
  | [o], ⟨i, h, past⟩ => by
    simp at h
    subst h
    simp [nextOffset] at past
    exact ⟨.offsetPastScope, by simp [offsetSpans, past]⟩
  | o :: next :: rest, ⟨i, h, past⟩ => by
    by_cases early : next < o
    · exact ⟨.offsetUnordered, by simp [offsetSpans, early]⟩
    · cases i with
      | zero => simp [nextOffset] at past; omega
      | succ i =>
        obtain ⟨e, read⟩ := offsetSpans_unordered scope (next :: rest)
          ⟨i, by simp at h ⊢; omega, by simpa [nextOffset] using past⟩
        exact ⟨e, by simp [offsetSpans, early, read, Bind.bind, Except.bind]⟩

/-- The four bytes of an offset, read from memory holding an encoding. -/
theorem readLE_offset (mem : Memory) (data : Nat) (b : ByteArray) (bytes : BytesAt mem data b) (x : Nat)
    (inside : x + 4 ≤ b.size) : readLE mem (data + x) 4 = (offsetAt b x).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [readLE_toNat _ _ _ (by decide)]
  have small : offsetAt b x < 2 ^ 64 := by
    have := (b.get! x).toNat_lt; have := (b.get! (x + 1)).toNat_lt; have := (b.get! (x + 2)).toNat_lt
    have := (b.get! (x + 3)).toNat_lt
    simp only [offsetAt]; omega
  rw [toNat_toUInt64 _ small]
  simp only [bytesNat, offsetAt, Nat.add_assoc, bytes x (by omega), bytes (x + 1) (by omega),
    bytes (x + 2) (by omega), bytes (x + 3) (by omega)]
  omega

/-- Memory away from the words written reads as before. -/
theorem wordsAt_far (a : Nat) (f : Nat → UInt64) (written : Nat → Bool) (mem : Memory) (n x : Nat)
    (bounded : ∀ k, written k = true → k < n) (far : x < a ∨ a + 8 * n ≤ x) : wordsAt a f written mem x = mem x := by
  simp only [wordsAt]
  rw [ite_eq_right]
  rintro ⟨above, holds⟩
  have := bounded _ holds
  omega

/-- The ranges an offset table opens, as the reference computes them. -/
def tableRanges (b : ByteArray) (start stop count : Nat) : Except Err (List (Nat × Nat)) :=
  let offsets := (List.range count).map fun i => offsetAt b (start + i * bytesPerOffset)
  do
    let spans ← offsetSpans offsets (stop - start)
    return bodies start offsets spans

/-- Where the drivers' inputs sit: an encoding's bytes, and an output of a capacity apart from them. -/
structure ViewMemory (w : World) (mem : Memory) (data : Nat) (b : ByteArray) (out cap : Nat) : Prop where
  /-- The encoding's bytes are in memory. -/
  bytes : BytesAt mem data b
  /-- The program may read them. -/
  readable : w.access data b.size
  /-- The output's first word holds its capacity. -/
  capacity : readLE mem out 8 = cap.toUInt64
  /-- The capacity is a word. -/
  smallCap : cap < 2 ^ 64
  /-- The program may write the output. -/
  writable : w.access out (8 + 16 * cap)
  /-- The output misses the encoding. -/
  apart : data + b.size ≤ out ∨ out + 8 + 16 * cap ≤ data

/-- Words written to the output leave the encoding's bytes in place. -/
theorem ViewMemory.wordsAt {w : World} {mem : Memory} {data : Nat} {b : ByteArray} {out cap : Nat}
    (h : ViewMemory w mem data b out cap) (f : Nat → UInt64) (written : Nat → Bool)
    (bounded : ∀ k, written k = true → k < 1 + 2 * cap) : BytesAt (wordsAt out f written mem) data b := by
  intro k small
  rw [wordsAt_far out f written mem (1 + 2 * cap) (data + k) bounded (by have := h.apart; omega)]
  exact h.bytes k small

/-- An offset loaded from the encoding, at an index an expression gives. -/
theorem eval_offset {w : World} {env : Env} {cur : Memory} {data start j : Nat} {b : ByteArray} (idx : Expr)
    (bytes : BytesAt cur data b) (readable : w.access data b.size) (e0 : env 0 = data.toUInt64)
    (e1 : env 1 = start.toUInt64) (hidx : eval w env cur idx = some j.toUInt64)
    (inside : start + j * 4 + 4 ≤ b.size) :
    eval w env cur (Expr.ld4 (Expr.var 0 + Expr.var 1 + 4 * idx)) = some (offsetAt b (start + j * 4)).toUInt64 := by
  have bound : data + b.size ≤ 2 ^ 63 := by
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at readable; simp [addressBound] at readable; omega
  have addr : (UInt64.ofNat data + UInt64.ofNat start + 4 * UInt64.ofNat j).toNat = data + (start + j * 4) := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
      UInt64.toNat_ofNat_of_lt' (lt_size (by omega)), UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
    simp; omega
  have acc : w.access (data + (start + j * 4)) 4 := access_inside readable _ 4 (by omega)
  simp [eval, Expr.ld4, e0, e1, hidx, aluResult, Width.bytes, addr, acc,
    readLE_offset cur data b bytes (start + j * 4) inside]

/-- The loop of the offsets driver that checks the table. -/
def offsetCheck : Stmt :=
  match offsetRanges.body with
  | .seq _ (.seq _ (.seq _ (.seq _ (.seq loop _)))) => loop
  | _ => .skip

/-- The loop of the offsets driver that writes the ranges. -/
def offsetWrite : Stmt :=
  match offsetRanges.body with
  | .seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.ite _ (.seq _ (.ite _ (.seq _ (.seq loop _)) _)) _))))) => loop
  | _ => .skip

/-- A loop's condition. -/
def loopCond : Stmt → Expr
  | .loop c _ => c
  | _ => .lit 0

/-- A loop's body. -/
def loopBody : Stmt → Stmt
  | .loop _ body => body
  | _ => .skip

/-- The offsets driver: its size, refusal code, flag and index set, the check, then the write if it passes. -/
theorem offsetRanges_body : offsetRanges.body =
    .seq (.set 10 (.op .sub (.var 2) (.var 1))) (.seq (.set 5 (.lit 1)) (.seq (.set 7 (.lit 1)) (.seq (.set 6 (.lit 0))
      (.seq (.loop (loopCond offsetCheck) (loopBody offsetCheck))
        (.ite (.var 7) (.seq (.set 5 (.lit 2)) (.ite (Expr.le (.var 3) (.load .b8 (.var 4)))
          (.seq (.set 6 (.lit 0)) (.seq (.loop (loopCond offsetWrite) (loopBody offsetWrite))
            (.seq (.store .b8 (.var 4) (.var 3)) (.set 5 (.lit 0))))) .skip)) .skip))))) := rfl

/-- The check runs while offsets are left and all are in order so far. -/
theorem offsetCheck_cond : loopCond offsetCheck = .op .and (Expr.lt (.var 6) (.var 3)) (.var 7) := rfl

/-- The check reads an offset and where its body ends, notes when they are out of order, and moves on. -/
theorem offsetCheck_body : loopBody offsetCheck =
    .block [.set 8 (Expr.ld4 (Expr.var 0 + Expr.var 1 + 4 * Expr.var 6)),
      .ite (Expr.lt (.var 6 + 1) (.var 3))
        (.block [.set 9 (Expr.ld4 (Expr.var 0 + Expr.var 1 + 4 * (Expr.var 6 + 1)))]) (.block [.set 9 (.var 10)]),
      .ite (Expr.lt (.var 9) (.var 8)) (.block [.set 7 0]) .skip, .set 6 (.var 6 + 1)] := rfl

/-- The write loop runs while ranges are left. -/
theorem offsetWrite_cond : loopCond offsetWrite = Expr.lt (.var 6) (.var 3) := rfl

/-- The write loop reads an offset and where its body ends, and writes the body's range. -/
theorem offsetWrite_body : loopBody offsetWrite =
    .block [.set 8 (Expr.ld4 (Expr.var 0 + Expr.var 1 + 4 * Expr.var 6)),
      .ite (Expr.lt (.var 6 + 1) (.var 3))
        (.block [.set 9 (Expr.ld4 (Expr.var 0 + Expr.var 1 + 4 * (Expr.var 6 + 1)))]) (.block [.set 9 (.var 10)]),
      Stmt.st (Expr.var 4 + 8 + 16 * Expr.var 6) (Expr.var 1 + Expr.var 8),
      Stmt.st (Expr.var 4 + 16 + 16 * Expr.var 6) (Expr.var 1 + Expr.var 9), .set 6 (.var 6 + 1)] := rfl

set_option linter.unusedSimpArgs false in
/-- The bodies an offset table opens: written when the table is ordered and they fit, refused otherwise. -/
theorem offsets_ok (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory)
    (data start stop count out cap : Nat) (b : ByteArray) (room : w.stackLo + 8 + 8 * offsetRanges.frame ≤ sp)
    (at_ : ViewMemory w mem data b out cap) (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (table : count * 4 ≤ stop - start) :
    Calls m w "ssz_offset_ranges" sp [data.toUInt64, start.toUInt64, stop.toUInt64, count.toUInt64, out.toUInt64]
      mem (viewOutcome out cap mem (tableRanges b start stop count)).1
      (viewOutcome out cap mem (tableRanges b start stop count)).2 := by
  have found : m.fns.lookup "ssz_offset_ranges" = some offsetRanges :=
    linked ("ssz_offset_ranges", offsetRanges) (by simp [codecFns])
  have dataBound : data + b.size ≤ 2 ^ 63 := by
    have := at_.readable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have outBound : out + 8 + 16 * cap ≤ 2 ^ 63 := by
    have := at_.writable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have smallCount : count < 2 ^ 64 := by omega
  have outReadable : w.access out 8 := by simpa using access_inside at_.writable 0 8 (by omega)
  let inner := sp - 8 - 8 * offsetRanges.frame
  let args := [data.toUInt64, start.toUInt64, stop.toUInt64, count.toUInt64, out.toUInt64]
  let size := stop - start
  let offs (i : Nat) : Nat := offsetAt b (start + i * 4)
  let offsets := (List.range count).map fun i => offsetAt b (start + i * bytesPerOffset)
  have getOffs : ∀ i, i < count → offsets.getD i 0 = offs i := by
    intro i small; simp [offsets, offs, List.getD_eq_getElem?_getD, small]
  have lenOffs : offsets.length = count := by simp [offsets]
  let nxt (i : Nat) : Nat := nextOffset offsets size i
  have nxtEq : ∀ i, i < count → nxt i = if i + 1 < count then offs (i + 1) else size := by
    intro i small
    simp only [nxt, nextOffset, List.getD_eq_getElem?_getD]
    by_cases more : i + 1 < count
    · rw [ite_eq_left more, List.getElem?_append_left (by simp [lenOffs]; omega)]
      simp [offsets, offs, more]
    · rw [ite_eq_right more, List.getElem?_append_right (by simp [lenOffs]; omega)]
      simp [lenOffs, show i + 1 - count = 0 by omega]
  have offsSmall : ∀ i, offs i < 2 ^ 32 := by
    intro i
    have := (b.get! (start + i * 4)).toNat_lt; have := (b.get! (start + i * 4 + 1)).toNat_lt
    have := (b.get! (start + i * 4 + 2)).toNat_lt; have := (b.get! (start + i * 4 + 3)).toNat_lt
    simp only [offs, offsetAt]; omega
  have nxtSmall : ∀ i, i < count → nxt i < 2 ^ 64 := by
    intro i small; rw [nxtEq i small]; split
    · have := offsSmall (i + 1); omega
    · omega
  -- The constant part of the variables, from the start of the check.
  let Fixed (env : Env) : Prop := env 0 = data.toUInt64 ∧ env 1 = start.toUInt64 ∧ env 2 = stop.toUInt64 ∧
    env 3 = count.toUInt64 ∧ env 4 = out.toUInt64 ∧ env 10 = size.toUInt64
  -- Each offset is read where the table holds it.
  have readAt : ∀ env cur i, Fixed env → BytesAt cur data b → i < count → ∀ idx : Expr,
      eval w env cur idx = some i.toUInt64 →
      eval w env cur (Expr.ld4 (Expr.var 0 + Expr.var 1 + 4 * idx)) = some (offs i).toUInt64 := by
    intro env cur i fixed bytes small idx hidx
    exact eval_offset idx bytes at_.readable fixed.1 fixed.2.1 hidx (by omega)
  -- One pass reads an offset and where its body ends.
  have ending : ∀ env cur i, Fixed env → BytesAt cur data b → i < count → env 6 = i.toUInt64 →
      Runs m w inner (assign env 8 (offs i).toUInt64) cur
        (.ite (Expr.lt (.var 6 + 1) (.var 3))
          (.block [.set 9 (Expr.ld4 (Expr.var 0 + Expr.var 1 + 4 * (Expr.var 6 + 1)))]) (.block [.set 9 (.var 10)]))
        (assign (assign env 8 (offs i).toUInt64) 9 (nxt i).toUInt64) cur := by
    intro env cur i fixed bytes small e6
    have e3 := fixed.2.2.2.1
    have e10 := fixed.2.2.2.2.2
    by_cases more : i + 1 < count
    · refine Runs.ite_true 1 (by simp [eval, Expr.lt, assign, e6, e3, Cond.holds, aluResult,
        ofNat_succ_lt i count (by omega) smallCount, more]) (by decide) ?_
      refine Runs.set _ _ _ _ _ 9 _ _ ?_
      rw [nxtEq i small, ite_eq_left more]
      exact readAt _ cur (i + 1) (by simp [Fixed, assign] at fixed ⊢; exact fixed) bytes more _
        (by simp [eval, assign, e6, aluResult])
    · refine Runs.ite_false (by simp [eval, Expr.lt, assign, e6, e3, Cond.holds, aluResult,
        ofNat_succ_lt i count (by omega) smallCount, more]) ?_
      refine Runs.set _ _ _ _ _ 9 _ _ ?_
      rw [nxtEq i small, ite_eq_right more]
      simp [eval, assign, e10]
  -- After i offsets, the flag says whether every one so far ends no earlier than it starts.
  let inv₁ : Env → Memory → Prop := fun env cur =>
    cur = mem ∧ Fixed env ∧ env 5 = 1 ∧ ∃ i, i ≤ count ∧ env 6 = i.toUInt64 ∧
      ((env 7 = 1 ∧ ∀ j, j < i → offs j ≤ nxt j) ∨ (env 7 = 0 ∧ ∃ j, j < count ∧ nxt j < offs j))
  have check := Runs.loop_inv (m := m) (w := w) (sp := inner) (c := loopCond offsetCheck)
    (body := loopBody offsetCheck) inv₁
    (fun env _ => count - (env 6).toNat) (fun env cur _ => ⟨_, rfl⟩)
    (by
      rintro env cur v ⟨hcur, fixed, e5, i, within, e6, flag⟩ cond nonzero
      subst cur
      have e3 := fixed.2.2.2.1
      have small : i < 2 ^ 64 := by omega
      -- The condition holds, so another offset is left and all so far are in order.
      have go : i < count ∧ env 7 = 1 := by
        rw [offsetCheck_cond] at cond
        rcases flag with ⟨e7, -⟩ | ⟨e7, -⟩
        · refine ⟨?_, e7⟩
          by_cases done : i < count
          · exact done
          · simp [eval, Expr.lt, e6, e3, e7, Cond.holds, aluResult, ofNat_lt_ofNat i count small smallCount,
              done] at cond
            exact absurd cond.symm nonzero
        · simp [eval, Expr.lt, e6, e3, e7, Cond.holds, aluResult] at cond
          exact absurd cond.symm nonzero
      have sofar : ∀ j, j < i → offs j ≤ nxt j := by
        rcases flag with ⟨-, h⟩ | ⟨e7, -⟩
        · exact h
        · rw [e7] at go; exact absurd go.2 (by decide)
      have readO := readAt env mem i fixed at_.bytes go.1 (.var 6) (by simp [eval, e6])
      have s1 := Runs.set m w inner env mem 8 _ _ readO
      have s2 := ending env mem i fixed at_.bytes go.1 e6
      let env₂ := assign (assign env 8 (offs i).toUInt64) 9 (nxt i).toUInt64
      have nSmall := nxtSmall i go.1
      have oSmall : offs i < 2 ^ 64 := by have := offsSmall i; omega
      by_cases bad : nxt i < offs i
      · -- Out of order: the flag drops, and the table is refused.
        have s3 : Runs m w inner env₂ mem (.ite (Expr.lt (.var 9) (.var 8)) (.block [.set 7 0]) .skip)
            (assign env₂ 7 0) mem := by
          refine Runs.ite_true 1 (by simp [env₂, eval, Expr.lt, assign, Cond.holds,
            ofNat_lt_ofNat _ _ nSmall oSmall, bad]) (by decide) ?_
          exact Runs.set _ _ _ _ _ 7 _ _ rfl
        have s4 := Runs.set m w inner (assign env₂ 7 0) mem 6 (.var 6 + 1) (i + 1).toUInt64
          (by simp [env₂, eval, assign, e6, aluResult])
        rw [offsetCheck_body]
        refine ⟨_, _, Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons s3 s4)),
          ⟨rfl, ?_, ?_, i + 1, go.1, ?_, Or.inr ⟨?_, i, go.1, bad⟩⟩, ?_⟩
        · simp only [Fixed, env₂, assign] at fixed ⊢; simpa using fixed
        · simp [env₂, assign, e5]
        · simp [env₂, assign]
        · simp [env₂, assign]
        · simp [env₂, assign, e6, toNat_toUInt64 _ small, Nat.mod_eq_of_lt (show i + 1 < 2 ^ 64 by omega)]
          omega
      · -- In order: the flag stays up.
        have s3 : Runs m w inner env₂ mem (.ite (Expr.lt (.var 9) (.var 8)) (.block [.set 7 0]) .skip)
            env₂ mem := by
          refine Runs.ite_false (by simp [env₂, eval, Expr.lt, assign, Cond.holds,
            ofNat_lt_ofNat _ _ nSmall oSmall, bad]) (Runs.skip _ _ _ _ _)
        have s4 := Runs.set m w inner env₂ mem 6 (.var 6 + 1) (i + 1).toUInt64
          (by simp [env₂, eval, assign, e6, aluResult])
        rw [offsetCheck_body]
        refine ⟨_, _, Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons s3 s4)),
          ⟨rfl, ?_, ?_, i + 1, go.1, ?_, Or.inl ⟨?_, fun j small => ?_⟩⟩, ?_⟩
        · simp only [Fixed, env₂, assign] at fixed ⊢; simpa using fixed
        · simp [env₂, assign, e5]
        · simp [env₂, assign]
        · simp [env₂, assign, go.2]
        · by_cases last : j = i
          · subst last; omega
          · exact sofar j (by omega)
        · simp [env₂, assign, e6, toNat_toUInt64 _ small, Nat.mod_eq_of_lt (show i + 1 < 2 ^ 64 by omega)]
          omega)
  -- The table's own exit: in order, or refused.
  have init₁ : inv₁ (assign (assign (assign (assign (entryEnv args) 10 size.toUInt64) 5 1) 7 1) 6 0) mem :=
    ⟨rfl, by simp [Fixed, assign, args, entryEnv, size, ofNat_sub _ _ ordered (by omega)], by simp [assign], 0, Nat.zero_le _,
      by simp [assign], Or.inl ⟨by simp [assign], fun j h => absurd h (Nat.not_lt_zero _)⟩⟩
  have s10 := Runs.set m w inner (entryEnv args) mem 10 (.op .sub (.var 2) (.var 1)) size.toUInt64
    (by simp [eval, args, entryEnv, aluResult, size, ofNat_sub _ _ ordered (by omega)])
  have s5 := Runs.set m w inner (assign (entryEnv args) 10 size.toUInt64) mem 5 (.lit 1) 1 rfl
  have s7 := Runs.set m w inner (assign (assign (entryEnv args) 10 size.toUInt64) 5 1) mem 7 (.lit 1) 1 rfl
  have s6 := Runs.set m w inner (assign (assign (assign (entryEnv args) 10 size.toUInt64) 5 1) 7 1) mem 6
    (.lit 0) 0 rfl
  obtain ⟨env₁, mem₁, runs₁, ⟨hmem, fixed₁, e5, i, within, e6, flag⟩, exit₁⟩ := check _ _ init₁
  subst mem₁
  have e3 := fixed₁.2.2.2.1
  have e4 := fixed₁.2.2.2.2.1
  -- Joins the setup, the check and what follows into the driver's whole run.
  have whole : ∀ (tail : Stmt) env' mem', tail = (.ite (.var 7) (.seq (.set 5 (.lit 2))
        (.ite (Expr.le (.var 3) (.load .b8 (.var 4))) (.seq (.set 6 (.lit 0))
          (.seq (.loop (loopCond offsetWrite) (loopBody offsetWrite))
            (.seq (.store .b8 (.var 4) (.var 3)) (.set 5 (.lit 0))))) .skip)) .skip) →
      Runs m w inner env₁ mem tail env' mem' → env' 5 = (viewOutcome out cap mem (tableRanges b start stop count)).1 →
      mem' = (viewOutcome out cap mem (tableRanges b start stop count)).2 →
      Calls m w "ssz_offset_ranges" sp args mem (viewOutcome out cap mem (tableRanges b start stop count)).1
        (viewOutcome out cap mem (tableRanges b start stop count)).2 := by
    rintro tail env' mem' rfl rest answer rfl
    refine Calls.fn (env' := env') found room rfl ?_ (by simp [offsetRanges, Offsets.r, eval, answer])
    rw [offsetRanges_body]
    exact Runs.seq s10 (Runs.seq s5 (Runs.seq s7 (Runs.seq s6 (Runs.seq runs₁ rest))))
  by_cases sorted : ∀ j, j < count → offs j ≤ nxt j
  · -- Every offset is in order: the flag is up and the whole table was read.
    have up : env₁ 7 = 1 ∧ i = count := by
      rcases flag with ⟨e7, -⟩ | ⟨-, j, small, bad⟩
      · refine ⟨e7, ?_⟩
        rw [offsetCheck_cond] at exit₁
        by_cases more : i < count
        · simp [eval, Expr.lt, e6, e3, e7, Cond.holds, aluResult,
            ofNat_lt_ofNat i count (by omega) smallCount, more] at exit₁
        · omega
      · exact absurd (sorted j small) (by omega)
    obtain ⟨e7, rfl⟩ := up
    let rs := (List.range i).map fun j => (start + offs j, start + nxt j)
    have accepted : tableRanges b start stop i = .ok rs := by
      obtain ⟨spans, read, cut⟩ := offsetSpans_ordered start size offsets (fun j h => by
        have g := getOffs j (by simpa [lenOffs] using h)
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some] at g
        rw [g]; exact sorted j (by simpa [lenOffs] using h))
      have read' : offsetSpans ((List.range i).map fun j => offsetAt b (start + j * bytesPerOffset))
          (stop - start) = .ok spans := read
      have cut' : bodies start ((List.range i).map fun j => offsetAt b (start + j * bytesPerOffset)) spans = rs := by
        rw [show ((List.range i).map fun j => offsetAt b (start + j * bytesPerOffset)) = offsets from rfl, cut,
          lenOffs]
        apply List.map_congr_left
        intro j member
        rw [getOffs j (List.mem_range.mp member)]
      simp [tableRanges, read', cut', Bind.bind, Except.bind, pure, Except.pure]
    have rsLen : rs.length = i := by simp [rs]
    have r2 := Runs.set m w inner env₁ mem 5 (.lit 2) 2 rfl
    let env₂ := assign env₁ 5 2
    by_cases fits : i ≤ cap
    · -- The ranges fit: the write loop writes them, then the count.
      have fitCheck : eval w env₂ mem (Expr.le (.var 3) (.load .b8 (.var 4))) = some 1 := by
        simp [env₂, eval, Expr.le, assign, e3, e4, Cond.holds, at_.capacity, Width.bytes,
          toNat_toUInt64 out (by omega), outReadable,
          ofNat_lt_ofNat _ _ smallCount at_.smallCap, ofNat_eq_ofNat _ _ smallCount at_.smallCap]
        omega
      let f := viewWord rs
      have words : ∀ j, j < i → f (1 + 2 * j) = (start + offs j).toUInt64 ∧ f (2 + 2 * j) = (start + nxt j).toUInt64 :=
        fun j small => viewWord_map _ i j small
      have fixed₂ : Fixed env₂ := by simp only [Fixed, env₂, assign] at fixed₁ ⊢; simpa using fixed₁
      -- After j ranges, their words are written.
      let inv₂ : Env → Memory → Prop := fun env cur =>
        Fixed env ∧ env 5 = 2 ∧ ∃ j, j ≤ i ∧ env 6 = j.toUInt64 ∧
          cur = wordsAt out f (fun k => 1 ≤ k ∧ k < 1 + 2 * j) mem
      have write := Runs.loop_inv (m := m) (w := w) (sp := inner) (c := loopCond offsetWrite)
        (body := loopBody offsetWrite) inv₂
        (fun env _ => i - (env 6).toNat) (fun env cur _ => ⟨_, rfl⟩)
        (by
          rintro env cur v ⟨fixed, e5, j, within, e6, hcur⟩ cond nonzero
          subst cur
          have e3 := fixed.2.2.2.1
          have e1 := fixed.2.1
          have e4 := fixed.2.2.2.2.1
          have small : j < 2 ^ 64 := by omega
          have more : j < i := by
            rw [offsetWrite_cond] at cond
            by_cases done : j < i
            · exact done
            · simp [eval, Expr.lt, e6, e3, Cond.holds, ofNat_lt_ofNat j i small smallCount, done] at cond
              exact absurd cond.symm nonzero
          have bytes := at_.wordsAt f (fun k => 1 ≤ k ∧ k < 1 + 2 * j) (by intro k h; simp at h; omega)
          have readO := readAt env _ j fixed bytes more (.var 6) (by simp [eval, e6])
          have s1 := Runs.set m w inner env _ 8 _ _ readO
          have s2 := ending env _ j fixed bytes more e6
          let env₃ := assign (assign env 8 (offs j).toUInt64) 9 (nxt j).toUInt64
          obtain ⟨wStart, wStop⟩ := words j more
          have a1 : (UInt64.ofNat out + 8 + 16 * UInt64.ofNat j).toNat = out + 8 * (1 + 2 * j) := by
            rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
              UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
            simp; omega
          have a2 : (UInt64.ofNat out + 16 + 16 * UInt64.ofNat j).toNat = out + 8 * (2 + 2 * j) := by
            rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
              UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
            simp; omega
          have s3 := Runs.store m w inner env₃ (wordsAt out f (fun k => 1 ≤ k ∧ k < 1 + 2 * j) mem) .b8
            (Expr.var 4 + 8 + 16 * Expr.var 6) (Expr.var 1 + Expr.var 8)
            (UInt64.ofNat out + 8 + 16 * UInt64.ofNat j) (f (1 + 2 * j))
            (by simp [env₃, eval, assign, e4, e6, aluResult])
            (by simp [env₃, eval, assign, e1, aluResult, wStart])
            (by rw [a1]; exact access_inside at_.writable _ 8 (by omega))
          rw [a1, Width.bytes, store_wordsAt] at s3
          have s4 := Runs.store m w inner env₃
            (wordsAt out f (fun k => k == 1 + 2 * j || decide (1 ≤ k ∧ k < 1 + 2 * j)) mem) .b8
            (Expr.var 4 + 16 + 16 * Expr.var 6) (Expr.var 1 + Expr.var 9)
            (UInt64.ofNat out + 16 + 16 * UInt64.ofNat j) (f (2 + 2 * j))
            (by simp [env₃, eval, assign, e4, e6, aluResult])
            (by simp [env₃, eval, assign, e1, aluResult, wStop])
            (by rw [a2]; exact access_inside at_.writable _ 8 (by omega))
          rw [a2, Width.bytes, store_wordsAt] at s4
          have grown : (fun k => k == 2 + 2 * j || (k == 1 + 2 * j || decide (1 ≤ k ∧ k < 1 + 2 * j))) =
              (fun k => decide (1 ≤ k ∧ k < 1 + 2 * (j + 1))) := by
            funext k
            apply Bool.eq_iff_iff.mpr
            simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
            omega
          rw [grown] at s4
          have s5 := Runs.set m w inner env₃ (wordsAt out f (fun k => decide (1 ≤ k ∧ k < 1 + 2 * (j + 1))) mem) 6
            (Expr.var 6 + 1) (j + 1).toUInt64 (by simp [env₃, eval, assign, e6, aluResult])
          rw [offsetWrite_body]
          refine ⟨_, _, Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons s3 (Runs.block_cons s4 s5))),
            ⟨?_, ?_, j + 1, more, ?_, rfl⟩, ?_⟩
          · simp only [Fixed, env₃, assign] at fixed ⊢; simpa using fixed
          · simp [env₃, assign, e5]
          · simp [env₃, assign]
          · simp [env₃, assign, e6, toNat_toUInt64 _ small, Nat.mod_eq_of_lt (show j + 1 < 2 ^ 64 by omega)]
            omega)
      have i0 := Runs.set m w inner env₂ mem 6 (.lit 0) 0 rfl
      have none : wordsAt out f (fun k => decide (1 ≤ k ∧ k < 1 + 2 * 0)) mem = mem := by
        have empty : (fun k => decide (1 ≤ k ∧ k < 1 + 2 * 0)) = (fun _ => false) := by
          funext k; simp; omega
        rw [empty, wordsAt_none]
      obtain ⟨env₄, mem₄, runs₂, ⟨fixed₄, e5', j, within', e6', hmem⟩, exit₂⟩ :=
        write (assign env₂ 6 0) mem ⟨by simp only [Fixed, assign] at fixed₂ ⊢; simpa using fixed₂,
          by simp [env₂, assign], 0, Nat.zero_le _, by simp [assign], none.symm⟩
      subst mem₄
      have done : j = i := by
        have small : j < 2 ^ 64 := by omega
        rw [offsetWrite_cond] at exit₂
        simp [eval, Expr.lt, e6', fixed₄.2.2.2.1, Cond.holds, ofNat_lt_ofNat j i small smallCount] at exit₂
        omega
      subst done
      have countWord : f 0 = j.toUInt64 := by simp [f, viewWord, rsLen]
      have stored := Runs.store m w inner env₄ (wordsAt out f (fun k => decide (1 ≤ k ∧ k < 1 + 2 * j)) mem) .b8
        (.var 4) (.var 3) out.toUInt64 (f 0) (by simp [eval, fixed₄.2.2.2.2.1])
        (by simp [eval, fixed₄.2.2.2.1, countWord])
        (by rw [toNat_toUInt64 out (by omega)]; exact outReadable)
      rw [toNat_toUInt64 out (by omega), Width.bytes, store_wordsAt_zero] at stored
      have full : (fun k => k == 0 || decide (1 ≤ k ∧ k < 1 + 2 * j)) = (fun k => decide (k < 1 + 2 * j)) := by
        funext k
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
        omega
      rw [full] at stored
      have r0 := Runs.set m w inner env₄ (wordsAt out f (fun k => decide (k < 1 + 2 * j)) mem) 5 (.lit 0) 0 rfl
      have final : viewed out rs mem = wordsAt out f (fun k => decide (k < 1 + 2 * j)) mem := by
        simp only [viewed, rsLen]; rfl
      exact whole _ _ _ rfl (Runs.ite_true 1 (by simp [eval, e7]) (by decide)
        (Runs.seq r2 (Runs.ite_true 1 fitCheck (by decide)
          (Runs.seq i0 (Runs.seq runs₂ (Runs.seq stored r0))))))
        (by simp [viewOutcome, accepted, rsLen, fits, assign]) (by simp [viewOutcome, accepted, rsLen, fits, final])
    · -- The ranges do not fit: nothing is written.
      have check : eval w env₂ mem (Expr.le (.var 3) (.load .b8 (.var 4))) = some 0 := by
        simp [env₂, eval, Expr.le, assign, e3, e4, Cond.holds, at_.capacity, Width.bytes,
          toNat_toUInt64 out (by omega), outReadable,
          ofNat_lt_ofNat _ _ smallCount at_.smallCap, ofNat_eq_ofNat _ _ smallCount at_.smallCap]
        omega
      exact whole _ env₂ mem rfl (Runs.ite_true 1 (by simp [eval, e7]) (by decide)
        (Runs.seq r2 (Runs.ite_false check (Runs.skip _ _ _ _ _))))
        (by simp [env₂, viewOutcome, accepted, rsLen, fits, assign]) (by simp [viewOutcome, accepted, rsLen, fits])
  · -- Some offset is out of order: the flag is down, and the table is refused.
    have down : env₁ 7 = 0 := by
      rcases flag with ⟨e7, all⟩ | ⟨e7, -⟩
      · exfalso
        have done : i = count := by
          rw [offsetCheck_cond] at exit₁
          by_cases more : i < count
          · simp [eval, Expr.lt, e6, e3, e7, Cond.holds, aluResult,
              ofNat_lt_ofNat i count (by omega) smallCount, more] at exit₁
          · omega
        subst done
        exact sorted all
      · exact e7
    obtain ⟨j, hj⟩ := Classical.not_forall.mp sorted
    have small := (Classical.not_imp.mp hj).1
    have bad := Nat.lt_of_not_le (Classical.not_imp.mp hj).2
    have refused : ∃ e, tableRanges b start stop count = .error e := by
      obtain ⟨e, read⟩ := offsetSpans_unordered size offsets ⟨j, by simp [lenOffs]; exact small, by
          have g := getOffs j small
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < offsets.length by omega),
            Option.getD_some] at g
          rw [g]; exact bad⟩
      have read' : offsetSpans ((List.range count).map fun i => offsetAt b (start + i * bytesPerOffset))
          (stop - start) = .error e := read
      exact ⟨e, by simp [tableRanges, read', Bind.bind, Except.bind]⟩
    obtain ⟨e, read⟩ := refused
    exact whole _ env₁ mem rfl (Runs.ite_false (by simp [eval, down]) (Runs.skip _ _ _ _ _))
      (by simp [viewOutcome, e5, read]) (by simp [viewOutcome, read])

/-- The stack a sequence view needs below its own frame: a width walk, then the ranges it writes. -/
def seqRoom (element : Desc) : Nat :=
  (widthLevel + walkLevel) * element.nesting + (8 + 8 * strideRanges.frame) + (8 + 8 * offsetRanges.frame)

/-- The ranges a vector's variable elements open, once the table's width and first offset are checked. -/
theorem vector_table (element : Desc) (length : Nat) (b : ByteArray) (start stop : Nat) (varies : element.fixedSize = none)
    (small : stop - start < offsetBound) (fits : length * bytesPerOffset ≤ stop - start) (some_ : length ≠ 0)
    (first : offsetAt b start = length * bytesPerOffset) :
    (vectorRanges element length b start stop).map Ranges.toList = tableRanges b start stop length := by
  have nz : (length == 0) = false := by simpa using some_
  have head : ((List.range length).map fun i => offsetAt b (start + i * bytesPerOffset))[0]! = offsetAt b start := by
    rw [getElem!_pos _ 0 (by simp; omega)]; simp
  simp only [vectorRanges, tableRanges, varies, show ¬ (stop - start ≥ offsetBound) by omega, ite_false,
    show ¬ (stop - start < length * bytesPerOffset) by omega, nz, Bool.false_eq_true, head, first, bne_self_eq_false,
    throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure]
  cases offsetSpans ((List.range length).map fun i => offsetAt b (start + i * bytesPerOffset)) (stop - start) <;> rfl

/-- A driver's body after its first two statements. -/
def afterTwo (body : Stmt) : Stmt :=
  match body with
  | .seq _ (.seq _ main) => main
  | _ => .skip

/-- The vector view sets its size and its refusal code, then does the rest. -/
theorem vectorView_body : vectorView.body =
    .seq (.set 7 (.op .sub (.var 3) (.var 2))) (.seq (.set 6 (.lit 1)) (afterTwo vectorView.body)) := rfl

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- A vector's view: the driver writes the ranges `vectorRanges` computes, or refuses as it does. -/
theorem vector_ok (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory) (element : Desc)
    (length data start stop out cap e : Nat) (b : ByteArray) (sound : element.wellFormed = .ok ())
    (thin : narrow (.vector element length) = true) (plan : PlanAt w mem e (words element))
    (at_ : ViewMemory w mem data b out cap) (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (smallLength : length < 2 ^ 62) (room : w.stackLo + 8 + 8 * vectorView.frame + seqRoom element ≤ sp) :
    Calls m w "ssz_vector_ranges" sp
      [e.toUInt64, data.toUInt64, start.toUInt64, stop.toUInt64, length.toUInt64, out.toUInt64] mem
      (viewOutcome out cap mem ((vectorRanges element length b start stop).map Ranges.toList)).1
      (viewOutcome out cap mem ((vectorRanges element length b start stop).map Ranges.toList)).2 := by
  have found : m.fns.lookup "ssz_vector_ranges" = some vectorView :=
    linked ("ssz_vector_ranges", vectorView) (by simp [codecFns])
  have dataBound : data + b.size ≤ 2 ^ 63 := by
    have := at_.readable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have outBound : out + 8 + 16 * cap ≤ 2 ^ 63 := by
    have := at_.writable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have eBound : e < 2 ^ 63 := by have := plan.1; simp [addressBound] at this; have := words_length_pos element; omega
  simp only [narrow, Bool.and_eq_true] at thin
  obtain ⟨vecThin, elemThin⟩ := thin
  let inner := sp - 8 - 8 * vectorView.frame
  let args := [e.toUInt64, data.toUInt64, start.toUInt64, stop.toUInt64, length.toUInt64, out.toUInt64]
  let size := stop - start
  have sizeEq : stop.toUInt64 - start.toUInt64 = size.toUInt64 := by
    simp [size, ofNat_sub _ _ ordered (by omega)]
  have s7 := Runs.set m w inner (entryEnv args) mem 7 (.op .sub (.var 3) (.var 2)) size.toUInt64
    (by simp [eval, args, entryEnv, aluResult, size, ofNat_sub _ _ ordered (by omega)])
  have s6 := Runs.set m w inner (assign (entryEnv args) 7 size.toUInt64) mem 6 (.lit 1) 1 rfl
  let env₁ := assign (assign (entryEnv args) 7 size.toUInt64) 6 1
  have r₁ : Runs m w inner (entryEnv args) mem (.seq (.set 7 (.op .sub (.var 3) (.var 2))) (.set 6 (.lit 1))) env₁ mem :=
    Runs.seq s7 s6
  -- Finishes the driver from a run of its main branch.
  have finish : ∀ env' mem' (r : UInt64),
      Runs m w inner env₁ mem (afterTwo vectorView.body) env' mem' → env' 6 = r →
      Calls m w "ssz_vector_ranges" sp args mem r mem' := by
    intro env' mem' r main answer
    refine Calls.fn (env' := env') found (by unfold seqRoom at room; omega) rfl ?_
      (by simp [vectorView, SeqV.r, eval, answer])
    rw [vectorView_body]
    exact Runs.seq s7 (Runs.seq s6 main)
  have main : afterTwo vectorView.body = .ite (Expr.lt (.var 7) (.lit (offsetLimit : Nat).toUInt64))
      (.seq (.call "ssz_plan_width" [.var 0] 8)
        (.ite (Expr.ne (.var 8) (.lit (none64 : Nat).toUInt64))
          (.ite (Expr.eq (.var 7) (.var 8 * .var 4)) (.call "ssz_stride_ranges" [.var 2, .var 8, .var 4, .var 5] 6) .skip)
          (.ite (Expr.le (.var 4 * 4) (.var 7))
            (.ite (Expr.eq (.var 4) 0) (.call "ssz_stride_ranges" [.var 2, 0, 0, .var 5] 6)
              (.ite (Expr.eq (Expr.ld4 (.var 1 + .var 2)) (.var 4 * 4))
                (.call "ssz_offset_ranges" [.var 1, .var 2, .var 3, .var 4, .var 5] 6) .skip)) .skip))) .skip := rfl
  have sizeSmall : size < 2 ^ 64 := by omega
  have outReadable : w.access out 8 := by simpa using access_inside at_.writable 0 8 (by omega)
  have e1 : env₁ 1 = data.toUInt64 := by simp [env₁, assign, args, entryEnv]
  have e2 : env₁ 2 = start.toUInt64 := by simp [env₁, assign, args, entryEnv]
  have e3 : env₁ 3 = stop.toUInt64 := by simp [env₁, assign, args, entryEnv]
  have e4 : env₁ 4 = length.toUInt64 := by simp [env₁, assign, args, entryEnv]
  have e5 : env₁ 5 = out.toUInt64 := by simp [env₁, assign, args, entryEnv]
  have e7 : env₁ 7 = size.toUInt64 := by simp [env₁, assign]
  have e6 : env₁ 6 = 1 := by simp [env₁, assign]
  by_cases big : size ≥ offsetBound
  · -- Too big for four-byte offsets: refused before anything else.
    have refused : ∃ err, vectorRanges element length b start stop = .error err :=
      ⟨.offsetOverflow (stop - start), by simp [vectorRanges, show stop - start ≥ offsetBound from big, throw,
        throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]⟩
    obtain ⟨err, read⟩ := refused
    rw [read]
    refine finish env₁ mem 1 ?_ e6
    rw [main]
    refine Runs.ite_false ?_ (Runs.skip _ _ _ _ _)
    simp [eval, Expr.lt, e7, Cond.holds, ofNat_lt_ofNat size 4294967296 sizeSmall (by decide)]
    simp [offsetBound] at big; omega
  have small : size < offsetBound := by omega
  have sr : seqRoom element = (widthLevel + walkLevel) * element.nesting + (8 + 8 * strideRanges.frame) +
      (8 + 8 * offsetRanges.frame) := rfl
  have deep : (widthLevel + walkLevel) * element.nesting + w.stackLo ≤ inner := by
    simp only [inner]; omega
  have measured := width_ok m w linked element sound elemThin inner mem e plan (by omega)
  have ranWidth := Runs.call (m := m) (w := w) (sp := inner) (env := env₁) (args := [.var 0]) (dst := 8)
    (values := [e.toUInt64]) (by simp [env₁, eval, assign, args, entryEnv]) measured
  let env₂ := assign env₁ 8 (widthWord element)
  have strideRoom : w.stackLo + 8 + 8 * strideRanges.frame ≤ inner := by
    simp only [inner]; omega
  have offsetRoom : w.stackLo + 8 + 8 * offsetRanges.frame ≤ inner := by
    simp only [inner]; omega
  let rest : Stmt := .ite (Expr.ne (.var 8) (.lit (none64 : Nat).toUInt64))
    (.ite (Expr.eq (.var 7) (.var 8 * .var 4)) (.call "ssz_stride_ranges" [.var 2, .var 8, .var 4, .var 5] 6) .skip)
    (.ite (Expr.le (.var 4 * 4) (.var 7))
      (.ite (Expr.eq (.var 4) 0) (.call "ssz_stride_ranges" [.var 2, 0, 0, .var 5] 6)
        (.ite (Expr.eq (Expr.ld4 (.var 1 + .var 2)) (.var 4 * 4))
          (.call "ssz_offset_ranges" [.var 1, .var 2, .var 3, .var 4, .var 5] 6) .skip)) .skip)
  -- The size fits four-byte offsets, so the element's width is measured and the rest runs.
  have go : ∀ env' mem', Runs m w inner env₂ mem rest env' mem' →
      Runs m w inner env₁ mem (afterTwo vectorView.body) env' mem' := by
    intro env' mem' ran
    rw [main]
    refine Runs.ite_true 1 ?_ (by decide) (Runs.seq ranWidth ran)
    simp [eval, Expr.lt, e7, Cond.holds, ofNat_lt_ofNat size 4294967296 sizeSmall (by decide)]
    simp [offsetBound] at small; omega
  have f2 : env₂ 2 = start.toUInt64 := by simp [env₂, assign, e2]
  have f4 : env₂ 4 = length.toUInt64 := by simp [env₂, assign, e4]
  have f5 : env₂ 5 = out.toUInt64 := by simp [env₂, assign, e5]
  have f7 : env₂ 7 = size.toUInt64 := by simp [env₂, assign, e7]
  have f8 : env₂ 8 = widthWord element := by simp [env₂, assign]
  have f6 : env₂ 6 = 1 := by simp [env₂, assign, e6]
  have sizeLe : ¬ size ≥ offsetBound := by omega
  have notBig : ¬ offsetBound ≤ stop - start := by omega
  cases fixed : element.fixedSize with
  | some width =>
    have wSmall := narrow_width element elemThin width fixed
    have totalSmall : width * length < 2 ^ 62 := by
      simp [Desc.fixedSize, fixed] at vecThin; exact vecThin
    have word : widthWord element = width.toUInt64 := by simp [widthWord, fixed]
    have notNone : widthWord element ≠ 18446744073709551615 := by
      simpa using widthWord_none element width fixed wSmall
    have product : UInt64.ofNat width * UInt64.ofNat length = UInt64.ofNat (width * length) := by simp
    by_cases exact : size = width * length
    · -- The size is the declared count of widths: the elements sit one width apart.
      have hwl : ¬ (width * length ≥ offsetBound) := by rw [← exact]; exact sizeLe
      have accepted : vectorRanges element length b start stop = .ok (.stride start width length) := by
        simp [vectorRanges, hwl, fixed, show stop - start = width * length from exact, throw, throwThe,
          MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure]
      have strided := stride_ok m w linked inner mem start width length out cap strideRoom (by omega) at_.smallCap
        at_.capacity at_.writable
      rw [accepted]
      refine finish _ _ _ (go _ _ (Runs.ite_true 1 (by simp [eval, Expr.ne, f8, Cond.holds, notNone]) (by decide)
        (Runs.ite_true 1 ?_ (by decide) (Runs.call (values := [start.toUInt64, width.toUInt64, length.toUInt64,
          out.toUInt64]) (by simp [eval, f2, f4, f5, f8, word]) strided)))) (by simp [assign]; rfl)
      simp only [eval, Expr.eq, f7, f8, f4, word, aluResult, Nat.toUInt64_eq, product, Bind.bind, Option.bind]
      rw [show size = width * length from exact]
      simp [Cond.holds]
    · -- Any other size is refused.
      have refused : vectorRanges element length b start stop = .error (.scope (width * length) size) := by
        simp [vectorRanges, sizeLe, fixed, show stop - start ≠ width * length from exact, throw, throwThe,
          MonadExceptOf.throw, Bind.bind, Except.bind, size]
      rw [refused]
      refine finish _ _ _ (go _ _ (Runs.ite_true 1 (by simp [eval, Expr.ne, f8, Cond.holds, notNone]) (by decide)
        (Runs.ite_false ?_ (Runs.skip _ _ _ _ _)))) (by simp [viewOutcome, f6, Except.map])
      have differ : UInt64.ofNat size ≠ UInt64.ofNat (width * length) :=
        fun same => exact ((ofNat_eq_ofNat _ _ sizeSmall (by omega)).mp same)
      simp only [eval, Expr.eq, f7, f8, f4, word, aluResult, Nat.toUInt64_eq, product, Bind.bind, Option.bind]
      simp only [pure, Cond.holds, beq_iff_eq, differ, decide_false, ite_false]
  | none =>
    have word : widthWord element = 18446744073709551615 := by simp [widthWord, fixed]
    have tableWord : UInt64.ofNat length * 4 = UInt64.ofNat (length * 4) := by simp
    -- Variable elements: the width is the word for a variable size, so the table is read.
    have skipWidth : ∀ (s : Stmt) env' mem', Runs m w inner env₂ mem s env' mem' →
        Runs m w inner env₂ mem (.ite (Expr.ne (.var 8) (.lit (none64 : Nat).toUInt64))
          (.ite (Expr.eq (.var 7) (.var 8 * .var 4)) (.call "ssz_stride_ranges" [.var 2, .var 8, .var 4, .var 5] 6)
            .skip) s) env' mem' :=
      fun s env' mem' ran => Runs.ite_false (by simp [eval, Expr.ne, f8, word, Cond.holds]) ran
    by_cases fits : length * 4 ≤ size
    · have tableCheck : eval w env₂ mem (Expr.le (.var 4 * 4) (.var 7)) = some 1 := by
        simp only [eval, Expr.le, f4, f7, aluResult, tableWord, Bind.bind, Option.bind, pure, holds_be,
          ofNat_le_iff _ _ (show length * 4 < 2 ^ 64 by omega) sizeSmall, fits, decide_true, ite_true]
      by_cases empty : length = 0
      · -- No elements: no ranges, written as such.
        subst empty
        have accepted : vectorRanges element 0 b start stop = .ok (.listed []) := by
          simp [vectorRanges, notBig, fixed, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind,
            pure, Except.pure]
        have strided := stride_ok m w linked inner mem start 0 0 out cap strideRoom (by decide) at_.smallCap
          at_.capacity at_.writable
        have none_ : (Ranges.stride start 0 0).toList = (Ranges.listed []).toList := by simp [Ranges.toList]
        rw [none_] at strided
        rw [accepted]
        refine finish _ _ _ (go _ _ (skipWidth _ _ _ (Runs.ite_true 1 tableCheck (by decide)
          (Runs.ite_true 1 (by simp [eval, Expr.eq, f4, Cond.holds]) (by decide)
            (Runs.call (values := [start.toUInt64, 0, 0, out.toUInt64]) (by simp [eval, f2, f5]) strided)))))
          (by simp [assign]; rfl)
      · have readFirst : eval w env₂ mem (Expr.ld4 (.var 1 + .var 2)) = some (offsetAt b start).toUInt64 := by
          have addr : (UInt64.ofNat data + UInt64.ofNat start).toNat = data + start := by
            rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
              UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
            omega
          have acc : w.access (data + start) 4 := access_inside at_.readable _ 4 (by omega)
          simp [env₂, eval, Expr.ld4, assign, e1, e2, aluResult, Width.bytes, addr, acc,
            readLE_offset mem data b at_.bytes start (by omega)]
        have firstSmall : offsetAt b start < 2 ^ 64 := by
          have := (b.get! start).toNat_lt; have := (b.get! (start + 1)).toNat_lt
          have := (b.get! (start + 2)).toNat_lt; have := (b.get! (start + 3)).toNat_lt
          simp only [offsetAt]; omega
        have nonzero : eval w env₂ mem (Expr.eq (.var 4) 0) = some 0 := by
          have lnz : UInt64.ofNat length ≠ 0 := fun h => empty ((ofNat_eq_ofNat length 0 (by omega) (by decide)).mp h)
          simp [eval, Expr.eq, f4, Cond.holds, lnz]
        by_cases first : offsetAt b start = length * 4
        · -- The first offset is the table's width: the offsets give the ranges.
          have viewed_ := vector_table element length b start stop fixed small (by simpa using fits) empty
            (by simpa using first)
          have tabled := offsets_ok m w linked inner mem data start stop length out cap b offsetRoom at_ ordered
            inside (by omega)
          rw [viewed_]
          refine finish _ _ _ (go _ _ (skipWidth _ _ _ (Runs.ite_true 1 tableCheck (by decide)
            (Runs.ite_false nonzero (Runs.ite_true 1 ?_ (by decide)
              (Runs.call (values := [data.toUInt64, start.toUInt64, stop.toUInt64, length.toUInt64, out.toUInt64])
                (by simp [env₂, eval, assign, e1, e2, e3, e4, e5]) tabled))))))
            (by simp [assign])
          simp only [eval, Expr.eq, readFirst, f4, aluResult, tableWord, Bind.bind, Option.bind, pure, Cond.holds,
            first]
          simp
        · -- Any other first offset is refused.
          have refused : ∃ err, vectorRanges element length b start stop = .error err := by
            have head : ((List.range length).map fun i => offsetAt b (start + i * bytesPerOffset))[0]! =
                offsetAt b start := by
              rw [getElem!_pos _ 0 (by simp; omega)]; simp
            have nz : (length == 0) = false := by simpa using empty
            exact ⟨.firstOffset (length * bytesPerOffset) (offsetAt b start), by simp [vectorRanges, notBig, fixed, show ¬ stop - start < length * bytesPerOffset by
              simp [bytesPerOffset]; omega, nz, head, show offsetAt b start ≠ length * bytesPerOffset by
              simpa using first, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]⟩
          obtain ⟨err, read⟩ := refused
          rw [read]
          have differ : UInt64.ofNat (offsetAt b start) ≠ UInt64.ofNat (length * 4) :=
            fun same => first ((ofNat_eq_ofNat _ _ firstSmall (by omega)).mp same)
          refine finish _ _ _ (go _ _ (skipWidth _ _ _ (Runs.ite_true 1 tableCheck (by decide)
            (Runs.ite_false nonzero (Runs.ite_false ?_ (Runs.skip _ _ _ _ _))))))
            (by simp [viewOutcome, f6, Except.map])
          simp only [eval, Expr.eq, readFirst, f4, aluResult, tableWord, Bind.bind, Option.bind, pure, Cond.holds,
            beq_iff_eq, Nat.toUInt64_eq, differ, decide_false, ite_false]

    · -- Too small for the table: refused.
      have refused : ∃ err, vectorRanges element length b start stop = .error err :=
        ⟨.scopeTooSmall (length * bytesPerOffset) (stop - start), by simp [vectorRanges, notBig, fixed,
          show stop - start < length * bytesPerOffset by
          simp [bytesPerOffset]; omega, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]⟩
      obtain ⟨err, read⟩ := refused
      rw [read]
      refine finish _ _ _ (go _ _ (skipWidth _ _ _ (Runs.ite_false ?_ (Runs.skip _ _ _ _ _))))
        (by simp [viewOutcome, f6, Except.map])
      simp only [eval, Expr.le, f4, f7, aluResult, tableWord, Bind.bind, Option.bind, pure, holds_be,
        ofNat_le_iff _ _ (show length * 4 < 2 ^ 64 by omega) sizeSmall, fits, decide_false, Bool.false_eq_true,
        ite_false]

/-- An optional bound as the drivers read it: the bound, or the word for none. -/
def limitWord : Option Nat → Nat
  | some bound => bound
  | none => none64

/-- The list view sets its size and its refusal code, then does the rest. -/
theorem listView_body : listView.body =
    .seq (.set 7 (.op .sub (.var 3) (.var 2))) (.seq (.set 6 (.lit 1)) (afterTwo listView.body)) := rfl

/-- The rest of the list view: an empty range, or the elements' width and then their ranges. -/
theorem listView_main : afterTwo listView.body = .ite (Expr.lt (.var 7) (.lit (offsetLimit : Nat).toUInt64))
    (.ite (Expr.eq (.var 7) 0) (.call "ssz_stride_ranges" [.var 2, 0, 0, .var 5] 6)
      (.seq (.call "ssz_plan_width" [.var 0] 8)
        (.ite (Expr.ne (.var 8) (.lit (none64 : Nat).toUInt64))
          (.ite (Expr.ne (.var 8) 0) (.ite (Expr.eq (.mod (.var 7) (.var 8)) 0)
            (.seq (.set 10 (.div (.var 7) (.var 8)))
              (.ite (Expr.le (.var 10) (.var 4)) (.call "ssz_stride_ranges" [.var 2, .var 8, .var 10, .var 5] 6) .skip))
            .skip) .skip)
          (.ite (Expr.le 4 (.var 7))
            (.seq (.set 9 (Expr.ld4 (.var 1 + .var 2)))
              (.ite (.op .and (.op .and (Expr.le 4 (.var 9)) (Expr.eq (.mod (.var 9) 4) 0)) (Expr.le (.var 9) (.var 7)))
                (.seq (.set 10 (.div (.var 9) 4))
                  (.ite (Expr.le (.var 10) (.var 4))
                    (.call "ssz_offset_ranges" [.var 1, .var 2, .var 3, .var 10, .var 5] 6) .skip)) .skip)) .skip))))
    .skip := rfl

/-- A reference that refuses leaves the code for a refused encoding and memory as it was. -/
theorem viewOutcome_refused (out cap : Nat) (mem : Memory) (r : Except Err (List (Nat × Nat)))
    (refused : ∀ x, r ≠ .ok x) : viewOutcome out cap mem r = (1, mem) := by
  cases r with
  | error _ => rfl
  | ok x => exact absurd rfl (refused x)

/-- A refused range of a sequence is refused as ranges too. -/
theorem map_refused (r : Except Err Ranges) (refused : ∀ x, r ≠ .ok x) : ∀ x, r.map Ranges.toList ≠ .ok x := by
  intro x h
  cases r with
  | error _ => simp [Except.map] at h
  | ok y => exact refused y rfl

/-- The quotient of small numbers' words is the word of their quotient. -/
theorem ofNat_quotient (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNat a / UInt64.ofNat b = UInt64.ofNat (a / b) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' (lt_size ha), UInt64.toNat_ofNat_of_lt' (lt_size hb),
    UInt64.toNat_ofNat_of_lt' (lt_size (by have := Nat.div_le_self a b; omega))]

/-- The remainder of small numbers' words is the word of their remainder. -/
theorem ofNat_mod (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNat a % UInt64.ofNat b = UInt64.ofNat (a % b) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_mod, UInt64.toNat_ofNat_of_lt' (lt_size ha), UInt64.toNat_ofNat_of_lt' (lt_size hb),
    UInt64.toNat_ofNat_of_lt' (lt_size (by have := Nat.mod_le a b; omega))]

/-- A remainder of words, the divisor not zero. -/
theorem eval_remainder {w : World} {env : Env} {mem : Memory} {a b : Expr} {x y : UInt64} (ha : eval w env mem a = some x)
    (hb : eval w env mem b = some y) (nz : y ≠ 0) : eval w env mem (.mod a b) = some (x % y) := by
  simp [eval, ha, hb, nz, pure]

/-- A quotient of words, the divisor not zero. -/
theorem eval_quotient {w : World} {env : Env} {mem : Memory} {a b : Expr} {x y : UInt64} (ha : eval w env mem a = some x)
    (hb : eval w env mem b = some y) (nz : y ≠ 0) : eval w env mem (.div a b) = some (x / y) := by
  simp [eval, ha, hb, nz, pure]

/-- A comparison of words. -/
theorem eval_cmp {w : World} {env : Env} {mem : Memory} {a b : Expr} {x y : UInt64} (c : Cond)
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (.cmp c a b) = some (if c.holds (x == y) (x < y) then 1 else 0) := by
  simp [eval, ha, hb]

/-- A comparison word, as its condition. -/
theorem cmp_word (p : Prop) [Decidable p] : ((if p then (1 : UInt64) else 0) ≠ 0) = p := by
  by_cases h : p <;> simp [h]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 1000000 in
/-- A list's view: the driver writes the ranges `listRanges` computes, or refuses as it does. -/
theorem list_ok (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory) (element : Desc)
    (limit : Option Nat) (data start stop out cap e : Nat) (b : ByteArray) (sound : element.wellFormed = .ok ())
    (thin : narrow element = true) (plan : PlanAt w mem e (words element))
    (at_ : ViewMemory w mem data b out cap) (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (smallLimit : limitWord limit < 2 ^ 64) (room : w.stackLo + 8 + 8 * listView.frame + seqRoom element ≤ sp) :
    Calls m w "ssz_list_ranges" sp
      [e.toUInt64, data.toUInt64, start.toUInt64, stop.toUInt64, (limitWord limit).toUInt64, out.toUInt64] mem
      (viewOutcome out cap mem ((listRanges element limit b start stop).map Ranges.toList)).1
      (viewOutcome out cap mem ((listRanges element limit b start stop).map Ranges.toList)).2 := by
  have found : m.fns.lookup "ssz_list_ranges" = some listView :=
    linked ("ssz_list_ranges", listView) (by simp [codecFns])
  have dataBound : data + b.size ≤ 2 ^ 63 := by
    have := at_.readable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have eBound : e < 2 ^ 63 := by have := plan.1; simp [addressBound] at this; have := words_length_pos element; omega
  let inner := sp - 8 - 8 * listView.frame
  let args := [e.toUInt64, data.toUInt64, start.toUInt64, stop.toUInt64, (limitWord limit).toUInt64, out.toUInt64]
  let size := stop - start
  have sizeSmall : size < 2 ^ 64 := by omega
  have s7 := Runs.set m w inner (entryEnv args) mem 7 (.op .sub (.var 3) (.var 2)) size.toUInt64
    (by simp [eval, args, entryEnv, aluResult, size, ofNat_sub _ _ ordered (by omega)])
  have s6 := Runs.set m w inner (assign (entryEnv args) 7 size.toUInt64) mem 6 (.lit 1) 1 rfl
  let env₁ := assign (assign (entryEnv args) 7 size.toUInt64) 6 1
  have sr : seqRoom element = (widthLevel + walkLevel) * element.nesting + (8 + 8 * strideRanges.frame) +
      (8 + 8 * offsetRanges.frame) := rfl
  have finish : ∀ env' mem' (r : UInt64),
      Runs m w inner env₁ mem (afterTwo listView.body) env' mem' → env' 6 = r →
      Calls m w "ssz_list_ranges" sp args mem r mem' := by
    intro env' mem' r main answer
    refine Calls.fn (env' := env') found (by omega) rfl ?_ (by simp [listView, SeqV.r, eval, answer])
    rw [listView_body]
    exact Runs.seq s7 (Runs.seq s6 main)
  have e1 : env₁ 1 = data.toUInt64 := by simp [env₁, assign, args, entryEnv]
  have e2 : env₁ 2 = start.toUInt64 := by simp [env₁, assign, args, entryEnv]
  have e3 : env₁ 3 = stop.toUInt64 := by simp [env₁, assign, args, entryEnv]
  have e4 : env₁ 4 = (limitWord limit).toUInt64 := by simp [env₁, assign, args, entryEnv]
  have e5 : env₁ 5 = out.toUInt64 := by simp [env₁, assign, args, entryEnv]
  have e7 : env₁ 7 = size.toUInt64 := by simp [env₁, assign]
  have e6 : env₁ 6 = 1 := by simp [env₁, assign]
  have strideRoom : w.stackLo + 8 + 8 * strideRanges.frame ≤ inner := by simp only [inner]; omega
  have offsetRoom : w.stackLo + 8 + 8 * offsetRanges.frame ≤ inner := by simp only [inner]; omega
  -- A refusal leaves the code for a refused encoding.
  have refuse : ∀ env', Runs m w inner env₁ mem (afterTwo listView.body) env' mem → env' 6 = 1 →
      (∀ x, listRanges element limit b start stop ≠ .ok x) →
      Calls m w "ssz_list_ranges" sp args mem
        (viewOutcome out cap mem ((listRanges element limit b start stop).map Ranges.toList)).1
        (viewOutcome out cap mem ((listRanges element limit b start stop).map Ranges.toList)).2 := by
    intro env' ran answer refused
    rw [viewOutcome_refused out cap mem _ (map_refused _ refused)]
    exact finish env' mem 1 ran answer
  by_cases big : offsetBound ≤ size
  · refine refuse env₁ ?_ e6 (fun x h => by simp [listRanges, show offsetBound ≤ stop - start from big, throw,
      throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h)
    rw [listView_main]
    refine Runs.ite_false ?_ (Runs.skip _ _ _ _ _)
    simp [eval, Expr.lt, e7, Cond.holds, ofNat_lt_ofNat size 4294967296 sizeSmall (by decide)]
    simp [offsetBound] at big; omega
  have notBig : ¬ offsetBound ≤ stop - start := big
  have fitsWords : eval w env₁ mem (Expr.lt (.var 7) (.lit (offsetLimit : Nat).toUInt64)) = some 1 := by
    simp [eval, Expr.lt, e7, Cond.holds, ofNat_lt_ofNat size 4294967296 sizeSmall (by decide)]
    simp [offsetBound] at big; omega
  by_cases empty : size = 0
  · -- No bytes: no elements.
    have accepted : listRanges element limit b start stop = .ok (.listed []) := by
      simp [listRanges, notBig, show stop - start = 0 from empty, throw, throwThe, MonadExceptOf.throw, Bind.bind,
        Except.bind, pure, Except.pure]
    have strided := stride_ok m w linked inner mem start 0 0 out cap strideRoom (by decide) at_.smallCap
      at_.capacity at_.writable
    have none_ : (Ranges.stride start 0 0).toList = (Ranges.listed []).toList := by simp [Ranges.toList]
    rw [none_] at strided
    rw [accepted]
    refine finish _ _ _ (by
      rw [listView_main]
      exact Runs.ite_true 1 fitsWords (by decide) (Runs.ite_true 1 (by simp [eval, Expr.eq, e7, Cond.holds, empty])
        (by decide) (Runs.call (values := [start.toUInt64, 0, 0, out.toUInt64]) (by simp [eval, e2, e5]) strided)))
      (by simp [assign]; rfl)
  have nonEmpty : ¬ (stop - start = 0) := empty
  have sizeNz : UInt64.ofNat size ≠ 0 := fun h => empty ((ofNat_eq_ofNat size 0 sizeSmall (by decide)).mp h)
  have deep : (widthLevel + walkLevel) * element.nesting + w.stackLo ≤ inner := by simp only [inner]; omega
  have measured := width_ok m w linked element sound thin inner mem e plan (by omega)
  have ranWidth := Runs.call (m := m) (w := w) (sp := inner) (env := env₁) (args := [.var 0]) (dst := 8)
    (values := [e.toUInt64]) (by simp [env₁, eval, assign, args, entryEnv]) measured
  let env₂ := assign env₁ 8 (widthWord element)
  let rest : Stmt := .ite (Expr.ne (.var 8) (.lit (none64 : Nat).toUInt64))
    (.ite (Expr.ne (.var 8) 0) (.ite (Expr.eq (.mod (.var 7) (.var 8)) 0)
      (.seq (.set 10 (.div (.var 7) (.var 8)))
        (.ite (Expr.le (.var 10) (.var 4)) (.call "ssz_stride_ranges" [.var 2, .var 8, .var 10, .var 5] 6) .skip))
      .skip) .skip)
    (.ite (Expr.le 4 (.var 7))
      (.seq (.set 9 (Expr.ld4 (.var 1 + .var 2)))
        (.ite (.op .and (.op .and (Expr.le 4 (.var 9)) (Expr.eq (.mod (.var 9) 4) 0)) (Expr.le (.var 9) (.var 7)))
          (.seq (.set 10 (.div (.var 9) 4))
            (.ite (Expr.le (.var 10) (.var 4))
              (.call "ssz_offset_ranges" [.var 1, .var 2, .var 3, .var 10, .var 5] 6) .skip)) .skip)) .skip)
  have go : ∀ env' mem', Runs m w inner env₂ mem rest env' mem' →
      Runs m w inner env₁ mem (afterTwo listView.body) env' mem' := by
    intro env' mem' ran
    rw [listView_main]
    exact Runs.ite_true 1 fitsWords (by decide) (Runs.ite_false (by simp [eval, Expr.eq, e7, Cond.holds, sizeNz])
      (Runs.seq ranWidth ran))
  have f2 : env₂ 2 = start.toUInt64 := by simp [env₂, assign, e2]
  have f4 : env₂ 4 = (limitWord limit).toUInt64 := by simp [env₂, assign, e4]
  have f5 : env₂ 5 = out.toUInt64 := by simp [env₂, assign, e5]
  have f7 : env₂ 7 = size.toUInt64 := by simp [env₂, assign, e7]
  have f8 : env₂ 8 = widthWord element := by simp [env₂, assign]
  have f6 : env₂ 6 = 1 := by simp [env₂, assign, e6]
  have f1 : env₂ 1 = data.toUInt64 := by simp [env₂, assign, e1]
  have f3 : env₂ 3 = stop.toUInt64 := by simp [env₂, assign, e3]
  -- A count within the bound the type declares, where it declares one.
  have withinLimit : ∀ count, count < 2 ^ 64 →
      (count ≤ limitWord limit ↔ ∀ bound, limit = some bound → count ≤ bound) := by
    intro count small
    cases limit with
    | none => simp [limitWord, none64]; omega
    | some bound => simp [limitWord]
  cases fixed : element.fixedSize with
  | some width =>
    have wSmall := narrow_width element thin width fixed
    have word : widthWord element = width.toUInt64 := by simp [widthWord, fixed]
    have notNone : widthWord element ≠ 18446744073709551615 := by
      simpa using widthWord_none element width fixed wSmall
    have pickFixed : ∀ (s : Stmt) env' mem', Runs m w inner env₂ mem s env' mem' →
        Runs m w inner env₂ mem (.ite (Expr.ne (.var 8) (.lit (none64 : Nat).toUInt64)) s
          (.ite (Expr.le 4 (.var 7))
            (.seq (.set 9 (Expr.ld4 (.var 1 + .var 2)))
              (.ite (.op .and (.op .and (Expr.le 4 (.var 9)) (Expr.eq (.mod (.var 9) 4) 0)) (Expr.le (.var 9) (.var 7)))
                (.seq (.set 10 (.div (.var 9) 4))
                  (.ite (Expr.le (.var 10) (.var 4))
                    (.call "ssz_offset_ranges" [.var 1, .var 2, .var 3, .var 10, .var 5] 6) .skip)) .skip)) .skip))
          env' mem' :=
      fun s env' mem' ran => Runs.ite_true 1 (by simp [eval, Expr.ne, f8, Cond.holds, notNone]) (by decide) ran
    by_cases zero : width = 0
    · -- Elements of no width are refused.
      subst zero
      refine refuse env₂ (go _ _ (pickFixed _ _ _ (Runs.ite_false (by simp [eval, Expr.ne, f8, word, Cond.holds])
        (Runs.skip _ _ _ _ _)))) f6 (fun x h => ?_)
      simp [listRanges, notBig, nonEmpty, fixed, throw, throwThe, MonadExceptOf.throw, Bind.bind,
        Except.bind] at h
    have wordNz : UInt64.ofNat width ≠ 0 := fun h => zero ((ofNat_eq_ofNat width 0 (by omega) (by decide)).mp h)
    have pickWidth : ∀ (s : Stmt) env' mem', Runs m w inner env₂ mem s env' mem' →
        Runs m w inner env₂ mem (.ite (Expr.ne (.var 8) 0) s .skip) env' mem' :=
      fun s env' mem' ran => Runs.ite_true 1 (by simp [eval, Expr.ne, f8, word, Cond.holds, wordNz]) (by decide) ran
    have remainder : UInt64.ofNat size % UInt64.ofNat width = UInt64.ofNat (size % width) :=
      ofNat_mod _ _ sizeSmall (by omega)
    have remSmall : size % width < 2 ^ 64 := by have := Nat.mod_le size width; omega
    by_cases uneven : size % width ≠ 0
    · -- A size that is no whole number of elements is refused.
      have remNz : UInt64.ofNat (size % width) ≠ 0 :=
        fun h => uneven ((ofNat_eq_ofNat _ 0 remSmall (by decide)).mp h)
      refine refuse env₂ (go _ _ (pickFixed _ _ _ (pickWidth _ _ _ (Runs.ite_false
        (by
          rw [Expr.eq, eval_cmp .e (eval_remainder (x := UInt64.ofNat size) (y := UInt64.ofNat width) (by simp [eval, f7]) (by simp [eval, f8, word]) wordNz) rfl, remainder]
          simp [Cond.holds, remNz])
        (Runs.skip _ _ _ _ _))))) f6 (fun x h => ?_)
      simp [listRanges, notBig, nonEmpty, fixed, zero, show (stop - start) % width ≠ 0 from uneven, throw, throwThe,
        MonadExceptOf.throw, Bind.bind, Except.bind] at h
    have even : size % width = 0 := by omega
    let count := size / width
    have countSmall : count < 2 ^ 64 := by have := Nat.div_le_self size width; omega
    have quotient : UInt64.ofNat size / UInt64.ofNat width = UInt64.ofNat count :=
      ofNat_quotient _ _ sizeSmall (by omega)
    let env₃ := assign env₂ 10 (UInt64.ofNat count)
    have s10 := Runs.set m w inner env₂ mem 10 (.div (.var 7) (.var 8)) (UInt64.ofNat count)
      (by rw [eval_quotient (x := UInt64.ofNat size) (y := UInt64.ofNat width) (by simp [eval, f7]) (by simp [eval, f8, word]) wordNz, quotient])
    have remZero : eval w env₂ mem (Expr.eq (.mod (.var 7) (.var 8)) 0) = some 1 := by
      rw [Expr.eq, eval_cmp .e (eval_remainder (x := UInt64.ofNat size) (y := UInt64.ofNat width) (by simp [eval, f7]) (by simp [eval, f8, word]) wordNz) rfl, remainder]
      simp [Cond.holds, even]
    by_cases over : count ≤ limitWord limit
    · -- Within the bound: the elements sit one width apart.
      have within := (withinLimit count countSmall).mp over
      have accepted : listRanges element limit b start stop = .ok (.stride start width count) := by
        cases limit with
        | none => simp [listRanges, notBig, nonEmpty, fixed, zero, show (stop - start) % width = 0 from even,
            throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure, count, size]
        | some bound =>
          have := within bound rfl
          simp [listRanges, notBig, nonEmpty, fixed, zero, show (stop - start) % width = 0 from even,
            show ¬ (stop - start) / width > bound by simp only [count, size] at this; omega, throw, throwThe,
            MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure, count, size]
      have strided := stride_ok m w linked inner mem start width count out cap strideRoom countSmall at_.smallCap
        at_.capacity at_.writable
      rw [accepted]
      refine finish _ _ _ (go _ _ (pickFixed _ _ _ (pickWidth _ _ _ (Runs.ite_true 1 remZero (by decide)
        (Runs.seq s10 (Runs.ite_true 1 ?_ (by decide)
          (Runs.call (values := [start.toUInt64, width.toUInt64, count.toUInt64, out.toUInt64])
            (by simp [env₃, eval, assign, f2, f5, f8, word]) strided))))))) (by simp [assign]; rfl)
      simp only [env₃, eval, Expr.le, assign, f4, aluResult, Bind.bind, Option.bind, pure, holds_be]
      simp [ofNat_le_iff _ _ countSmall smallLimit, over]
    · -- Over the bound: refused.
      refine refuse _ (go _ _ (pickFixed _ _ _ (pickWidth _ _ _ (Runs.ite_true 1 remZero (by decide)
        (Runs.seq s10 (Runs.ite_false ?_ (Runs.skip _ _ _ _ _))))))) (by simp [env₃, assign, f6]) (fun x h => ?_)
      · simp only [env₃, eval, Expr.le, assign, f4, aluResult, Bind.bind, Option.bind, pure, holds_be]
        simp [ofNat_le_iff _ _ countSmall smallLimit, over]
      · cases limit with
        | none => simp [limitWord, none64] at over; omega
        | some bound =>
          simp [limitWord] at over
          simp [listRanges, notBig, nonEmpty, fixed, zero, show (stop - start) % width = 0 from even,
            show (stop - start) / width > bound by simp only [count, size] at over; omega, throw, throwThe,
            MonadExceptOf.throw, Bind.bind, Except.bind] at h
  | none =>
    have word : widthWord element = 18446744073709551615 := by simp [widthWord, fixed]
    have pickVar : ∀ (s : Stmt) env' mem', Runs m w inner env₂ mem s env' mem' →
        Runs m w inner env₂ mem (.ite (Expr.ne (.var 8) (.lit (none64 : Nat).toUInt64))
          (.ite (Expr.ne (.var 8) 0) (.ite (Expr.eq (.mod (.var 7) (.var 8)) 0)
            (.seq (.set 10 (.div (.var 7) (.var 8)))
              (.ite (Expr.le (.var 10) (.var 4)) (.call "ssz_stride_ranges" [.var 2, .var 8, .var 10, .var 5] 6) .skip))
            .skip) .skip) s) env' mem' :=
      fun s env' mem' ran => Runs.ite_false (by simp [eval, Expr.ne, f8, word, Cond.holds]) ran
    by_cases short : size < 4
    · -- Too small for one offset: refused.
      refine refuse _ (go _ _ (pickVar _ _ _ (Runs.ite_false ?_ (Runs.skip _ _ _ _ _)))) f6 (fun x h => ?_)
      · simp only [Expr.le]
        rw [eval_cmp .be (x := 4) (y := UInt64.ofNat size) rfl (by simp [eval, f7]),
          show (4 : UInt64) = UInt64.ofNat 4 from rfl]
        simp only [holds_be, ofNat_le_iff 4 size (by decide) sizeSmall, decide_eq_true_eq]
        simp; omega
      · simp [listRanges, notBig, nonEmpty, fixed, show stop - start < bytesPerOffset by simp [bytesPerOffset]; omega,
          throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
    have room4 : eval w env₂ mem (Expr.le 4 (.var 7)) = some 1 := by
      simp only [Expr.le]
      rw [eval_cmp .be (x := 4) (y := UInt64.ofNat size) rfl (by simp [eval, f7]),
        show (4 : UInt64) = UInt64.ofNat 4 from rfl]
      simp only [holds_be, ofNat_le_iff 4 size (by decide) sizeSmall, decide_eq_true_eq]
      simp; omega
    let first := offsetAt b start
    have firstSmall : first < 2 ^ 32 := by
      have := (b.get! start).toNat_lt; have := (b.get! (start + 1)).toNat_lt
      have := (b.get! (start + 2)).toNat_lt; have := (b.get! (start + 3)).toNat_lt
      simp only [first, offsetAt]; omega
    have readFirst : eval w env₂ mem (Expr.ld4 (.var 1 + .var 2)) = some (UInt64.ofNat first) := by
      have addr : (UInt64.ofNat data + UInt64.ofNat start).toNat = data + start := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
          UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
        omega
      have acc : w.access (data + start) 4 := access_inside at_.readable _ 4 (by omega)
      simp [eval, Expr.ld4, f1, f2, aluResult, Width.bytes, addr, acc,
        readLE_offset mem data b at_.bytes start (by omega), first]
    have s9 := Runs.set m w inner env₂ mem 9 (Expr.ld4 (.var 1 + .var 2)) _ readFirst
    let env₃ := assign env₂ 9 (UInt64.ofNat first)
    have g9 : eval w env₃ mem (.var 9) = some (UInt64.ofNat first) := by simp [env₃, eval, assign]
    have rem4 : UInt64.ofNat first % 4 = UInt64.ofNat (first % 4) := ofNat_mod first 4 (by omega) (by decide)
    -- The first offset is checked: past the table's first entry, aligned, and inside the range.
    have tableOk : eval w env₃ mem (.op .and (.op .and (Expr.le 4 (.var 9)) (Expr.eq (.mod (.var 9) 4) 0))
        (Expr.le (.var 9) (.var 7))) =
        some (if 4 ≤ first ∧ first % 4 = 0 ∧ first ≤ size then 1 else 0) := by
      have c1 : eval w env₃ mem (Expr.le 4 (.var 9)) = some (if 4 ≤ first then 1 else 0) := by
        simp only [Expr.le]
        rw [eval_cmp .be (x := 4) (y := UInt64.ofNat first) rfl g9, show (4 : UInt64) = UInt64.ofNat 4 from rfl]
        simp only [holds_be, ofNat_le_iff 4 first (by decide) (by omega), decide_eq_true_eq]
      have c2 : eval w env₃ mem (Expr.eq (.mod (.var 9) 4) 0) = some (if first % 4 = 0 then 1 else 0) := by
        simp only [Expr.eq]
        rw [eval_cmp .e (eval_remainder (x := UInt64.ofNat first) (y := 4) g9 rfl (by decide)) rfl, rem4]
        simp [Cond.holds, ← ofNat_eq_ofNat (first % 4) 0 (by omega) (by decide)]
      have c3 : eval w env₃ mem (Expr.le (.var 9) (.var 7)) = some (if first ≤ size then 1 else 0) := by
        simp only [Expr.le]
        rw [eval_cmp .be (x := UInt64.ofNat first) (y := UInt64.ofNat size) g9
          (by simp [env₃, eval, assign, f7])]
        simp only [holds_be, ofNat_le_iff first size (by omega) sizeSmall, decide_eq_true_eq]
      simp only [eval, c1, c2, c3, aluResult, Bind.bind, Option.bind, pure]
      by_cases h1 : 4 ≤ first <;> by_cases h2 : first % 4 = 0 <;> by_cases h3 : first ≤ size <;> simp [h1, h2, h3]
    by_cases good : 4 ≤ first ∧ first % 4 = 0 ∧ first ≤ size
    · let count := first / 4
      have quotient : UInt64.ofNat first / 4 = UInt64.ofNat count := ofNat_quotient first 4 (by omega) (by decide)
      have s10 := Runs.set m w inner env₃ mem 10 (.div (.var 9) 4) (UInt64.ofNat count)
        (by rw [eval_quotient (x := UInt64.ofNat first) (y := 4) g9 rfl (by decide), quotient])
      let env₄ := assign env₃ 10 (UInt64.ofNat count)
      have countSmall : count < 2 ^ 64 := by omega
      have under := withinLimit count countSmall
      have limitCheck : eval w env₄ mem (Expr.le (.var 10) (.var 4)) =
          some (if count ≤ limitWord limit then 1 else 0) := by
        simp only [Expr.le]
        rw [eval_cmp .be (x := UInt64.ofNat count) (y := UInt64.ofNat (limitWord limit))
          (by simp [env₄, eval, assign]) (by simp [env₄, env₃, eval, assign, f4])]
        simp only [holds_be, ofNat_le_iff _ _ countSmall smallLimit, decide_eq_true_eq]
      have firstBits : offsetAt b start % bytesPerOffset = 0 ∧ ¬ offsetAt b start < bytesPerOffset ∧
          ¬ offsetAt b start > stop - start := by
        simp only [bytesPerOffset, first, size] at good ⊢; omega
      by_cases over : count ≤ limitWord limit
      · -- Within the bound: the offsets give the ranges.
        have within := under.mp over
        have viewed_ : (listRanges element limit b start stop).map Ranges.toList = tableRanges b start stop count := by
          have shape : ∀ (r : Except Err (List Nat)), (do
              let spans ← r
              return Ranges.listed (bodies start ((List.range count).map fun i =>
                offsetAt b (start + i * bytesPerOffset)) spans)).map Ranges.toList =
              (do let spans ← r; return bodies start ((List.range count).map fun i =>
                offsetAt b (start + i * bytesPerOffset)) spans) := by
            intro r; cases r <;> rfl
          cases limit with
          | none =>
            simp only [listRanges, notBig, nonEmpty, fixed, show ¬ stop - start < bytesPerOffset by
              simp [bytesPerOffset]; omega, ite_false, beq_iff_eq, bne_iff_ne, ne_eq, firstBits.1,
              firstBits.2.1, firstBits.2.2, not_true, throw, throwThe, MonadExceptOf.throw, Bind.bind,
              Except.bind, pure, Except.pure, decide_false, Bool.false_eq_true, ite_false]
            exact shape _
          | some bound =>
            have := within bound rfl
            simp only [listRanges, notBig, nonEmpty, fixed, show ¬ stop - start < bytesPerOffset by
              simp [bytesPerOffset]; omega, ite_false, beq_iff_eq, bne_iff_ne, ne_eq, firstBits.1,
              firstBits.2.1, firstBits.2.2, not_true, show ¬ offsetAt b start / bytesPerOffset > bound by
              simp only [bytesPerOffset, count, first] at this ⊢; omega, throw, throwThe, MonadExceptOf.throw, Bind.bind,
              Except.bind, pure, Except.pure, decide_false, Bool.false_eq_true, ite_false]
            exact shape _
        have tabled := offsets_ok m w linked inner mem data start stop count out cap b offsetRoom at_ ordered
          inside (by omega)
        rw [viewed_]
        refine finish _ _ _ (go _ _ (pickVar _ _ _ (Runs.ite_true 1 room4 (by decide)
          (Runs.seq s9 (Runs.ite_true 1 (by rw [tableOk]; simp [good]) (by decide)
            (Runs.seq s10 (Runs.ite_true 1 (by rw [limitCheck]; simp [over]) (by decide)
              (Runs.call (values := [data.toUInt64, start.toUInt64, stop.toUInt64, count.toUInt64, out.toUInt64])
                (by simp [env₄, env₃, eval, assign, f1, f2, f3, f5]) tabled)))))))) (by simp [assign] <;> rfl)
      · -- Over the bound: refused.
        refine refuse _ (go _ _ (pickVar _ _ _ (Runs.ite_true 1 room4 (by decide)
          (Runs.seq s9 (Runs.ite_true 1 (by rw [tableOk]; simp [good]) (by decide)
            (Runs.seq s10 (Runs.ite_false (by rw [limitCheck]; simp [over]) (Runs.skip _ _ _ _ _))))))))
          (by simp [env₄, env₃, assign, f6]) (fun x h => ?_)
        cases limit with
        | none => simp [limitWord, none64] at over; omega
        | some bound =>
          simp only [limitWord] at over
          simp [listRanges, notBig, nonEmpty, fixed, show ¬ stop - start < bytesPerOffset by
            simp [bytesPerOffset]; omega, firstBits.1, firstBits.2.1, firstBits.2.2,
            show offsetAt b start / bytesPerOffset > bound by simp only [bytesPerOffset, count, first] at over ⊢; omega,
            throw, throwThe,
            MonadExceptOf.throw, Bind.bind, Except.bind] at h
    · -- A first offset inside the table, unaligned, or past the range is refused.
      refine refuse _ (go _ _ (pickVar _ _ _ (Runs.ite_true 1 room4 (by decide)
        (Runs.seq s9 (Runs.ite_false ?_ (Runs.skip _ _ _ _ _)))))) (by simp [env₃, assign, f6]) (fun x h => ?_)
      · rw [tableOk]; simp [good]
      · by_cases below : first < 4
        · simp [listRanges, notBig, nonEmpty, fixed, show ¬ stop - start < bytesPerOffset by
            simp [bytesPerOffset]; omega, show offsetAt b start < bytesPerOffset by
            simp [bytesPerOffset]; omega, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
        by_cases unaligned : first % 4 ≠ 0
        · simp [listRanges, notBig, nonEmpty, fixed, show ¬ stop - start < bytesPerOffset by
            simp [bytesPerOffset]; omega, show ¬ offsetAt b start < bytesPerOffset by
            simp [bytesPerOffset]; omega, show offsetAt b start % bytesPerOffset ≠ 0 by
            simp [bytesPerOffset]; omega, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
        have past : first > size := by omega
        simp [listRanges, notBig, nonEmpty, fixed, show ¬ stop - start < bytesPerOffset by
          simp [bytesPerOffset]; omega, show ¬ offsetAt b start < bytesPerOffset by
          simp [bytesPerOffset]; omega, show offsetAt b start % bytesPerOffset = 0 by
          simp [bytesPerOffset]; omega, show stop - start < offsetAt b start by
            simp only [size] at past; omega, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h

end EthLib.Consensus.Ssz.Native.Driver
