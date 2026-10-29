import SszNative.Proofs.Driver.Validate.Delimited

/-!
A table of offsets, checked as a whole: each offset no earlier than the one before, and the last within the size.
-/

namespace Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open Ssz Ssz.Native Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Ir.Stmt Ssz.Native.Ir.Expr

/-- An offset fits below 2^32. -/
theorem offsetAt_lt (b : ByteArray) (i : Nat) : offsetAt b i < 2 ^ 32 := by
  have := (b.get! i).toNat_lt; have := (b.get! (i + 1)).toNat_lt
  have := (b.get! (i + 2)).toNat_lt; have := (b.get! (i + 3)).toNat_lt
  simp only [offsetAt]; omega

/-- Four bytes of the encoding, read at their address as the offset they hold. -/
theorem DataAt.offset {w : World} {mem : Memory} {base : Nat} {b : ByteArray} (h : DataAt w mem base b) (i : Nat)
    (hi : i + 4 ≤ b.size) : readLE mem (base + i) 4 = UInt64.ofNat (offsetAt b i) := by
  apply u64_eq
  rw [readLE_toNat _ _ _ (by omega)]
  have byte : ∀ k, k < 4 → (mem (base + i + k)).toNat = (b.get! (i + k)).toNat := by
    intro k hk
    rw [show base + i + k = base + (i + k) by omega, h.2 (i + k) (by omega)]
    simp [ByteArray.get!, show i + k < b.size by omega]; rfl
  have lt : offsetAt b i < 2 ^ 64 := Nat.lt_of_lt_of_le (offsetAt_lt b i) (by decide)
  have b0 := byte 0 (by omega); have b1 := byte 1 (by omega); have b2 := byte 2 (by omega)
  have b3 := byte 3 (by omega)
  simp only [Nat.add_zero] at b0
  rw [toNat_ofNat_lt lt]
  simp only [bytesNat, offsetAt, Nat.add_assoc] at b1 b2 b3 ⊢
  rw [b0, b1, b2, b3]
  rfl

/-- Four bytes of the encoding are readable. -/
theorem DataAt.offsetOk {w : World} {mem : Memory} {base : Nat} {b : ByteArray} (h : DataAt w mem base b) (i : Nat)
    (hi : i + 4 ≤ b.size) : w.access (base + i) 4 = true :=
  access_sub h.1 (by omega) (by omega)

/-- A table's check, without the spans it computes. -/
def spansOutcome (offsets : List Nat) (size : Nat) : Except Err Unit := (offsetSpans offsets size).map fun _ => ()

/-- Offsets in order up to a position: each from the second on no earlier than the one before. -/
def OrdUpTo (l : List Nat) (i : Nat) : Prop := ∀ k, 0 < k → k < i → k < l.length → l[k - 1]! ≤ l[k]!

/-- An entry past the first of a list is an entry of its rest. -/
theorem cons_getElem! (a : Nat) (l : List Nat) (k : Nat) (hk : 0 < k) : (a :: l)[k]! = l[k - 1]! := by
  rw [show k = (k - 1) + 1 by omega]; simp

/-- A table checks its first pair, then the rest. -/
theorem spans_cons_cons (s n : Nat) (rest : List Nat) (size : Nat) :
    spansOutcome (s :: n :: rest) size =
      if n < s then .error .offsetUnordered else spansOutcome (n :: rest) size := by
  simp only [spansOutcome, offsetSpans]
  split
  · rfl
  · cases offsetSpans (n :: rest) size <;> rfl

/-- The first pair out of order refuses the table as unordered. -/
theorem spans_unordered : ∀ (l : List Nat) (size i : Nat), 0 < i → i < l.length → OrdUpTo l i → l[i]! < l[i - 1]! →
    spansOutcome l size = .error .offsetUnordered
  | [], _, _, _, h, _, _ => by simp at h
  | [_], _, i, pos, h, _, _ => by simp at h; omega
  | s :: n :: rest, size, i, pos, h, ord, lt => by
    rw [spans_cons_cons]
    by_cases i1 : i = 1
    · subst i1; simp at lt; simp [lt]
    · have sn : s ≤ n := by have := ord 1 (by omega) (by omega) (by simp); simpa using this
      rw [if_neg (by omega)]
      refine spans_unordered (n :: rest) size (i - 1) (by omega) (by simp at h ⊢; omega) ?_ ?_
      · intro k kp ki kl
        have := ord (k + 1) (by omega) (by omega) (by simp at kl ⊢; omega)
        rw [show k + 1 - 1 = k by omega, cons_getElem! _ _ k kp] at this
        simpa using this
      · have e1 : (s :: n :: rest)[i]! = (n :: rest)[i - 1]! := by
          rw [show i = (i - 1) + 1 by omega]; simp
        have e2 : (s :: n :: rest)[i - 1]! = (n :: rest)[i - 1 - 1]! := by
          rw [show i - 1 = (i - 1 - 1) + 1 by omega]; simp
        rw [← e1, ← e2]; exact lt

/-- Offsets all in order leave only the last one's bound to check. -/
theorem spans_ordered : ∀ (l : List Nat) (size : Nat), OrdUpTo l l.length →
    spansOutcome l size = if l ≠ [] ∧ size < l[l.length - 1]! then .error .offsetPastScope else .ok ()
  | [], _, _ => by simp [spansOutcome, offsetSpans, Except.map]
  | [s], size, _ => by
    simp only [spansOutcome, offsetSpans]
    by_cases h : size < s <;> simp [h, Except.map]
  | s :: n :: rest, size, ord => by
    rw [spans_cons_cons]
    have sn : s ≤ n := by have := ord 1 (by omega) (by simp) (by simp); simpa using this
    rw [if_neg (by omega), spans_ordered (n :: rest) size ?_]
    · simp
    · intro k kp ki kl
      have := ord (k + 1) (by omega) (by simp at ki ⊢; omega) (by simp at kl ⊢; omega)
      rw [show k + 1 - 1 = k by omega, cons_getElem! _ _ k kp] at this
      simpa using this

/-- The offsets of a table: a count of four-byte words from a start. -/
def tableOffsets (b : ByteArray) (start count : Nat) : List Nat :=
  (List.range count).map fun i => offsetAt b (start + i * bytesPerOffset)

/-- A table holds its count of offsets. -/
theorem tableOffsets_length (b : ByteArray) (start count : Nat) : (tableOffsets b start count).length = count := by
  simp [tableOffsets]

/-- Each offset of a table is the four bytes at its slot. -/
theorem tableOffsets_get (b : ByteArray) (start count k : Nat) (hk : k < count) :
    (tableOffsets b start count)[k]! = offsetAt b (start + 4 * k) := by
  simp [tableOffsets, hk, Nat.mul_comm]

set_option maxHeartbeats 1000000 in
/-- Checking a table of offsets as a whole refuses exactly as the Lean check does. -/
theorem spans_calls {m : Module} {w : World} (hm : Loaded m) (mem : Memory) (base : Nat) (b : ByteArray)
    (start count size err sp : Nat) (inside : start + 4 * count ≤ b.size) (hsize : size < 2 ^ 32)
    (hd : DataAt w mem base b) (ok : w.access err 32 = true) (room : Room w sp 0 2) :
    Calls m w "ssz_validate_spans" sp [UInt64.ofNat (base + start), UInt64.ofNat count, UInt64.ofNat size,
      UInt64.ofNat err] mem
      (res (spansOutcome (tableOffsets b start count) size))
      (after mem err (spansOutcome (tableOffsets b start count) size)) := by
  have db := hd.bound
  have eb : err + 32 ≤ 2 ^ 63 := by
    have := ok; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  have len := tableOffsets_length b start count
  refine Calls.body 13 hm.spans rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [spansFn]
  wsteps []
  refine Wp.loop (wp_loop (fun env mem' => ∃ i, 1 ≤ i ∧ i ≤ max count 1 ∧ env 5 = UInt64.ofNat i ∧
      env 0 = UInt64.ofNat (base + start) ∧ env 1 = UInt64.ofNat count ∧ env 2 = UInt64.ofNat size ∧
      env 3 = UInt64.ofNat err ∧
      ((env 4 = 0 ∧ mem' = mem ∧ OrdUpTo (tableOffsets b start count) i) ∨
       (env 4 = 1 ∧ mem' = wrote mem err .offsetUnordered ∧
        spansOutcome (tableOffsets b start count) size = .error .offsetUnordered)))
    (fun env _ => max count 1 - (env 5).toNat)
    ⟨1, Nat.le_refl _, by omega, by wfin [], by wfin [], by wfin [], by wfin [], by wfin [],
      Or.inl ⟨by wfin [], rfl, fun k kp ki _ => absurd ki (by omega)⟩⟩ ?_)
  rintro env mem' ⟨i, i1, im, h5, h0, h1, h2, h3, st⟩
  rcases st with ⟨h4, hmem, ord⟩ | ⟨h4, hmem, bad⟩
  · subst mem'
    refine ⟨_, by wev [h5, h1, h4], fun nz => ?_, fun z => ?_⟩
    · have hic : i < count := by
        rcases Nat.lt_or_ge i count with h | h
        · exact h
        · simp [show ¬ i < count by omega] at nz
      have r1 := hd.offset (start + 4 * (i - 1)) (by omega)
      have a1 := hd.offsetOk (start + 4 * (i - 1)) (by omega)
      have r2 := hd.offset (start + 4 * i) (by omega)
      have a2 := hd.offsetOk (start + 4 * i) (by omega)
      rw [← Nat.add_assoc] at r1 a1 r2 a2
      have o1 := offsetAt_lt b (start + 4 * (i - 1))
      have o2 := offsetAt_lt b (start + 4 * i)
      have g1 := tableOffsets_get b start count (i - 1) (by omega)
      have g2 := tableOffsets_get b start count i hic
      wsteps [h0, h5, r1, a1]
      by_cases lt : offsetAt b (start + 4 * i) < offsetAt b (start + 4 * (i - 1))
      · wsteps [h0, h5, r2, a2, lt]
        wfail [h3]
        wsteps [h5]
        refine ⟨⟨i + 1, by omega, by omega, by wfin [], by wfin [h0], by wfin [h1], by wfin [h2], by wfin [h3],
          Or.inr ⟨by wfin [], by simp [wrote_eq], ?_⟩⟩, by wfin [h5]⟩
        exact spans_unordered _ size i (by omega) (by omega) ord (by rw [g1, g2]; exact lt)
      · wsteps [h0, h5, r2, a2, lt]
        refine ⟨⟨i + 1, by omega, by omega, by wfin [], by wfin [h0], by wfin [h1], by wfin [h2], by wfin [h3],
          Or.inl ⟨by wfin [h4], trivial, ?_⟩⟩, by wfin [h5]⟩
        intro k kp ki kl
        rcases Nat.lt_or_ge k i with h | h
        · exact ord k kp h kl
        · rw [show k = i by omega, g1, g2]; omega
    · have hic : count ≤ i := by
        rcases Nat.lt_or_ge i count with h | h
        · simp [h] at z
        · exact h
      have ordall : OrdUpTo (tableOffsets b start count) count := fun k kp ki kl => ord k kp (by omega) kl
      rw [spans_ordered _ size (by rw [len]; exact ordall)]
      by_cases c0 : count = 0
      · wsteps [h4, h1, c0]
        wfin [h4, tableOffsets, c0, res, after]
      · have rl := hd.offset (start + 4 * (count - 1)) (by omega)
        have al := hd.offsetOk (start + 4 * (count - 1)) (by omega)
        rw [← Nat.add_assoc] at rl al
        have ol := offsetAt_lt b (start + 4 * (count - 1))
        have gl := tableOffsets_get b start count (count - 1) (by omega)
        have ne : tableOffsets b start count ≠ [] := by
          intro e; have := congrArg List.length e; simp [len] at this; omega
        by_cases past : size < offsetAt b (start + 4 * (count - 1))
        · wsteps [h4, h1, c0, h0, h2, rl, al, past]
          wfail [h3]
          wsteps []
          wfin [len, gl, ne, past, res, after, wrote_eq]
        · wsteps [h4, h1, c0, h0, h2, rl, al, past]
          wfin [h4, len, gl, ne, past, res, after]
  · subst mem'
    refine ⟨_, by wev [h5, h1, h4], fun nz => absurd (by wonly []) nz, fun _ => ?_⟩
    wsteps [h4]
    wfin [bad, res, after]

end Ssz.Native.Driver.Validate
