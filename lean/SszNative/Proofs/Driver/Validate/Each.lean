import SszNative.Proofs.Driver.Validate.Spans

/-!
Each body a checked table of offsets opens, checked in order against the element's type.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr

/-- What checking a range against a node computes. -/
def RangeOk (m : Module) (w : World) (d : Desc) : Prop :=
  fitsNative d = true → ∀ (p sp : Nat) (mem : Memory) (base : Nat) (b : ByteArray) (start stop err : Nat),
    PlanAt w mem p (Plan.words d) → Clear err p (8 * (Plan.words d).length) →
    DataAt w mem base b → Clear err base b.size → w.access err 32 = true →
    start ≤ stop → stop ≤ b.size → b.size < 2 ^ 60 → Room w sp d.nesting 4 →
    Calls m w "ssz_validate_range" sp [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (base + stop),
      UInt64.ofNat err] mem (res (validateRange d b start stop)) (after mem err (validateRange d b start stop))

/-- Ranges checked one after the other. -/
theorem validateEach_append (e : Desc) (b : ByteArray) :
    ∀ l₁ l₂ : List (Nat × Nat), validateEach e b (l₁ ++ l₂) = (do validateEach e b l₁; validateEach e b l₂)
  | [], l₂ => by rw [List.nil_append, validateEach]; rfl
  | (s, t) :: l₁, l₂ => by
    rw [List.cons_append, validateEach, validateEach, validateEach_append e b l₁ l₂]
    cases validateRange e b s t <;> simp [Bind.bind, Except.bind]

/-- The body the table's i-th offset opens: to the next offset, or to the size for the last. -/
def bodyRange (l : List Nat) (size start i : Nat) : Nat × Nat :=
  (start + l[i]!, start + (if i + 1 < l.length then l[i + 1]! else size))

/-- The positions up to a count, the first apart. -/
theorem range_succ_map {α : Type} (f : Nat → α) (n : Nat) :
    (List.range (n + 1)).map f = f 0 :: (List.range n).map (fun i => f (i + 1)) := by
  rw [List.range_succ_eq_map]; simp

/-- A table in order, its last offset within the size, gives spans whose bodies run offset to offset. -/
theorem offsetSpans_ok (start : Nat) : ∀ (l : List Nat) (size : Nat), OrdUpTo l l.length →
    (l ≠ [] → l[l.length - 1]! ≤ size) →
    ∃ spans, offsetSpans l size = .ok spans ∧ bodies start l spans = (List.range l.length).map (bodyRange l size start)
  | [], _, _, _ => ⟨[], by simp [offsetSpans], by simp [bodies]⟩
  | [s], size, _, last => ⟨[size - s], by
      have := last (by simp); simp at this; simp [offsetSpans]; omega, by
      have := last (by simp); simp at this
      simp [bodies, bodyRange]; omega⟩
  | s :: n :: rest, size, ord, last => by
    have sn : s ≤ n := by have := ord 1 (by omega) (by simp) (by simp); simpa using this
    obtain ⟨spans, hs, hb⟩ := offsetSpans_ok start (n :: rest) size (by
      intro k kp ki kl
      have := ord (k + 1) (by omega) (by simp at ki ⊢; omega) (by simp at kl ⊢; omega)
      rw [show k + 1 - 1 = k by omega, cons_getElem! _ _ k kp] at this
      simpa using this) (fun _ => by
      have := last (by simp)
      simpa [show (rest.length + 1 + 1 - 1) = rest.length + 1 by omega] using this)
    refine ⟨(n - s) :: spans, ?_, ?_⟩
    · simp only [offsetSpans, show ¬ n < s by omega, ite_false, hs]; rfl
    · simp only [bodies, List.zip_cons_cons, List.map_cons] at hb ⊢
      rw [show (s :: n :: rest).length = (n :: rest).length + 1 by simp, range_succ_map]
      rw [hb]
      congr 1
      · simp [bodyRange]; omega
      · apply List.map_congr_left
        intro i hi
        simp only [List.mem_range] at hi
        simp only [bodyRange, List.length_cons]
        rw [cons_getElem! s (n :: rest) (i + 1) (by omega), cons_getElem! s (n :: rest) (i + 1 + 1) (by omega)]
        simp only [Nat.add_sub_cancel]
        congr 2
        by_cases h : i + 1 < rest.length + 1
        · simp [h, show i + 1 + 1 < rest.length + 1 + 1 by omega]
        · simp [h, show ¬ (i + 1 + 1 < rest.length + 1 + 1) by omega]

/-- The positions up to a count, split around one of them. -/
theorem range_map_split {α : Type} (f : Nat → α) (c j : Nat) (hj : j < c) :
    (List.range c).map f = (List.range j).map f ++ f j :: (List.range (c - j - 1)).map (fun i => f (j + 1 + i)) := by
  have h := @List.range_add (j + 1) (c - j - 1)
  rw [show j + 1 + (c - j - 1) = c by omega] at h
  rw [h, List.map_append, List.range_succ, List.map_append, List.map_map, List.append_assoc]
  rfl

/-- The positions up to a count and one more. -/
theorem range_map_succ {α : Type} (f : Nat → α) (j : Nat) :
    (List.range (j + 1)).map f = (List.range j).map f ++ [f j] := by
  rw [List.range_succ, List.map_append]; rfl

set_option maxHeartbeats 1000000 in
/-- Checking each body of a checked table in order refuses exactly as the Lean check does. -/
theorem each_calls {m : Module} {w : World} (hm : Loaded m) (e : Desc) (ih : RangeOk m w e)
    (fit : fitsNative e = true) (p sp : Nat) (mem : Memory) (base : Nat) (b : ByteArray) (start count size err : Nat)
    (hp : PlanAt w mem p (Plan.words e)) (cp : Clear err p (8 * (Plan.words e).length))
    (hd : DataAt w mem base b) (cd : Clear err base b.size) (ok : w.access err 32 = true)
    (inside : start + size ≤ b.size) (table : 4 * count ≤ size) (small : b.size < 2 ^ 60)
    (ord : OrdUpTo (tableOffsets b start count) count)
    (last : count ≠ 0 → (tableOffsets b start count)[count - 1]! ≤ size) (room : Room w sp e.nesting 5) :
    Calls m w "ssz_validate_each" sp [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat count,
      UInt64.ofNat size, UInt64.ofNat err] mem
      (res (validateEach e b ((List.range count).map (bodyRange (tableOffsets b start count) size start))))
      (after mem err (validateEach e b ((List.range count).map (bodyRange (tableOffsets b start count) size start)))) := by
  have db := hd.bound
  have eb : err + 32 ≤ 2 ^ 63 := by
    have := ok; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  have len := tableOffsets_length b start count
  -- Every offset lies within the size, the table in order and its last offset within it.
  have within : ∀ k, k < count → (tableOffsets b start count)[k]! ≤ size := by
    intro k hk
    have chain : ∀ d, k + d < count → (tableOffsets b start count)[k]! ≤ (tableOffsets b start count)[k + d]! := by
      intro d
      induction d with
      | zero => intro _; exact Nat.le_refl _
      | succ d ihd =>
        intro hkd
        have := ord (k + d + 1) (by omega) hkd (by omega)
        rw [show k + d + 1 - 1 = k + d by omega] at this
        have := ihd (by omega)
        rw [show k + (d + 1) = k + d + 1 by omega]; omega
    have := chain (count - 1 - k) (by omega)
    rw [show k + (count - 1 - k) = count - 1 by omega] at this
    have := last (by omega); omega
  generalize hX : validateEach e b ((List.range count).map (bodyRange (tableOffsets b start count) size start)) = X
  refine Calls.body 13 hm.each rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [eachFn]
  wsteps []
  refine Wp.loop (wp_loop (fun env mem' => ∃ j, j ≤ count ∧ env 6 = UInt64.ofNat j ∧
      env 0 = UInt64.ofNat p ∧ env 1 = UInt64.ofNat (base + start) ∧ env 2 = UInt64.ofNat count ∧
      env 3 = UInt64.ofNat size ∧ env 4 = UInt64.ofNat err ∧
      ((env 5 = 0 ∧ mem' = mem ∧
          validateEach e b ((List.range j).map (bodyRange (tableOffsets b start count) size start)) = .ok ()) ∨
       (env 5 = 1 ∧ ∃ x, X = .error x ∧ mem' = wrote mem err x)))
    (fun env _ => count - (env 6).toNat)
    ⟨0, Nat.zero_le _, by wfin [], by wfin [], by wfin [], by wfin [], by wfin [], by wfin [],
      Or.inl ⟨by wfin [], rfl, by simp [validateEach]⟩⟩ ?_)
  rintro env mem' ⟨j, hj, h6, h0, h1, h2, h3, h4, st⟩
  rcases st with ⟨h5, hmem, sofar⟩ | ⟨h5, x, fails, hmem⟩
  · subst mem'
    refine ⟨_, by wev [h6, h2, h5], fun nz => ?_, fun z => ?_⟩
    · have hjc : j < count := by
        rcases Nat.lt_or_ge j count with h | h
        · exact h
        · simp [show ¬ j < count by omega] at nz
      have r1 := hd.offset (start + 4 * j) (by omega)
      have a1 := hd.offsetOk (start + 4 * j) (by omega)
      rw [← Nat.add_assoc] at r1 a1
      have g1 := tableOffsets_get b start count j hjc
      have w1 := within j hjc
      have o1 := offsetAt_lt b (start + 4 * j)
      -- The body's end: the next offset, or the size.
      obtain ⟨next, hnext, wn, ge⟩ : ∃ next, (if j + 1 < count then (tableOffsets b start count)[j + 1]! else size) = next ∧
          next ≤ size ∧ (tableOffsets b start count)[j]! ≤ next := by
        refine ⟨_, rfl, ?_, ?_⟩
        · split
          · exact within (j + 1) (by omega)
          · exact Nat.le_refl _
        · split
          · have := ord (j + 1) (by omega) (by omega) (by omega); simpa using this
          · exact w1
      have step := ih fit p (sp - 8 - 8 * 13) mem base b (start + offsetAt b (start + 4 * j)) (start + next) err
        hp cp hd cd ok (by rw [g1] at ge; omega) (by omega) small (by simp only [Room] at room ⊢; omega)
      have range_j : bodyRange (tableOffsets b start count) size start j =
          (start + offsetAt b (start + 4 * j), start + next) := by
        simp only [bodyRange, len, g1, hnext]
      by_cases more : j + 1 < count
      · have r2 := hd.offset (start + 4 * j + 4) (by omega)
        have a2 := hd.offsetOk (start + 4 * j + 4) (by omega)
        simp only [← Nat.add_assoc] at r2 a2
        have g2 := tableOffsets_get b start count (j + 1) more
        have o2 := offsetAt_lt b (start + 4 * j + 4)
        have nx : next = offsetAt b (start + 4 * j + 4) := by
          rw [← hnext, ite_eq_left more, g2]; congr 1
        subst nx
        wsteps [h6, h2, more, h1, r2, a2]
        rcases hR : validateRange e b (start + offsetAt b (start + 4 * j)) (start + offsetAt b (start + 4 * j + 4))
          with x | u
        · rw [hR] at step
          wcall step [h0, h1, h4, h6, r1, a1]
          wsteps [h6]
          refine ⟨⟨j + 1, by omega, by wfin [], by wfin [h0], by wfin [h1], by wfin [h2], by wfin [h3], by wfin [h4],
            Or.inr ⟨by wfin [res], x, ?_, rfl⟩⟩, by wfin [h6]⟩
          rw [← hX, range_map_split _ count j hjc, validateEach_append, sofar, range_j, validateEach, hR]
          first | rfl | simp [validateEach, Bind.bind, Except.bind]
        · rw [hR] at step
          wcall step [h0, h1, h4, h6, r1, a1]
          wsteps [h6]
          refine ⟨⟨j + 1, by omega, by wfin [], by wfin [h0], by wfin [h1], by wfin [h2], by wfin [h3], by wfin [h4],
            Or.inl ⟨by wfin [res], rfl, ?_⟩⟩, by wfin [h6]⟩
          rw [range_map_succ, validateEach_append, sofar, range_j, validateEach, hR]
          first | rfl | simp [validateEach, Bind.bind, Except.bind]
      · have nx : size = next := by rw [← hnext, ite_eq_right more]
        subst nx
        wsteps [h6, h2, more, h3]
        rcases hR : validateRange e b (start + offsetAt b (start + 4 * j)) (start + size) with x | u
        · rw [hR] at step
          wcall step [h0, h1, h4, h6, r1, a1]
          wsteps [h6]
          refine ⟨⟨j + 1, by omega, by wfin [], by wfin [h0], by wfin [h1], by wfin [h2], by wfin [h3], by wfin [h4],
            Or.inr ⟨by wfin [res], x, ?_, rfl⟩⟩, by wfin [h6]⟩
          rw [← hX, range_map_split _ count j hjc, validateEach_append, sofar, range_j, validateEach, hR]
          first | rfl | simp [validateEach, Bind.bind, Except.bind]
        · rw [hR] at step
          wcall step [h0, h1, h4, h6, r1, a1]
          wsteps [h6]
          refine ⟨⟨j + 1, by omega, by wfin [], by wfin [h0], by wfin [h1], by wfin [h2], by wfin [h3], by wfin [h4],
            Or.inl ⟨by wfin [res], rfl, ?_⟩⟩, by wfin [h6]⟩
          rw [range_map_succ, validateEach_append, sofar, range_j, validateEach, hR]
          first | rfl | simp [validateEach, Bind.bind, Except.bind]
    · have hjc : j = count := by
        rcases Nat.lt_or_ge j count with h | h
        · simp [h] at z
        · omega
      subst hjc
      rw [hX] at sofar
      exact Wp.done ⟨by wonly [h5, sofar, res], by simp [after, sofar]⟩
  · subst mem'
    refine ⟨_, by wev [h6, h2, h5], fun nz => absurd (by wonly []) nz, fun _ => ?_⟩
    exact Wp.done ⟨by wonly [h5, fails, res], by simp [after, fails]⟩

end EthLib.Consensus.Ssz.Native.Driver.Validate
