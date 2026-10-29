import SszNative.Proofs.Driver.Validate.Struct

/-!
The option a union selector names, found by walking the selectors and the options side by side.
-/

namespace Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open Ssz Ssz.Native Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Ir.Stmt Ssz.Native.Ir.Expr

/-- Passing a selector that does not match moves on to the next option. -/
theorem validateOption_skip (s : Nat) (sels : List Nat) (o : Desc) (opts : List Desc) (sel : Nat) (b : ByteArray)
    (start stop : Nat) (ne : s ≠ sel) :
    validateOption (s :: sels) (o :: opts) sel b start stop = validateOption sels opts sel b start stop := by
  rw [validateOption]; simp [ne]

/-- The first matching selector checks the selector's range, then its option. -/
theorem validateOption_hit (s : Nat) (sels : List Nat) (o : Desc) (opts : List Desc) (sel : Nat) (b : ByteArray)
    (start stop : Nat) (eq : s = sel) :
    validateOption (s :: sels) (o :: opts) sel b start stop =
      if 1 ≤ sel ∧ sel ≤ 127 then validateRange o b start stop else .error (.unionSelectorRange sel 1 127) := by
  rw [validateOption]
  simp only [eq, beq_self_eq_true, if_true, checkSelector, minSelector, maxSelector]
  split <;> simp [Bind.bind, Except.bind]

set_option maxHeartbeats 8000000 in
/-- Checking the option a selector names natively refuses exactly as the Lean check does. -/
theorem option_calls {m : Module} {w : World} (hm : Loaded m) (sels : List Nat) (opts : List Desc)
    (ih : ∀ f ∈ opts, RangeOk m w f) (fit : allFitNative opts = true) (len : sels.length = opts.length)
    (sfit : ∀ s ∈ sels, s < 2 ^ 64) (sel : Nat) (hsel : sel < 256) (q sp : Nat) (mem : Memory) (base : Nat)
    (b : ByteArray) (start stop err : Nat)
    (hq : PlanAt w mem q (sels ++ Plan.wordsAll opts)) (cq : Clear err q (8 * (sels ++ Plan.wordsAll opts).length))
    (hd : DataAt w mem base b) (cd : Clear err base b.size) (ok : w.access err 32 = true)
    (hle : start ≤ stop) (hs : stop ≤ b.size) (small : b.size < 2 ^ 60)
    (room : Room w sp (Desc.deepestNesting opts + 1) 2) :
    Calls m w "ssz_validate_option" sp [UInt64.ofNat q, UInt64.ofNat opts.length, UInt64.ofNat sel,
      UInt64.ofNat (base + start), UInt64.ofNat (base + stop), UInt64.ofNat err] mem
      (res (validateOption sels opts sel b start stop)) (after mem err (validateOption sels opts sel b start stop)) := by
  have hb := hq.bound
  have db := hd.bound
  have hl := length_le_wordsAll opts
  have eb : err + 32 ≤ 2 ^ 63 := by
    have := ok; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  simp only [List.length_append] at hb cq
  have ho : PlanAt w mem (q + 8 * opts.length) (Plan.wordsAll opts) := by
    have := hq.right; rwa [len] at this
  have co : Clear err (q + 8 * opts.length) (8 * (Plan.wordsAll opts).length) := by
    unfold Clear at cq ⊢; omega
  generalize hX : validateOption sels opts sel b start stop = X
  refine Calls.body 15 hm.option rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [optionFn]
  wsteps []
  refine Wp.loop (wp_loop (fun env mem' => mem' = mem ∧ ∃ i, i ≤ opts.length ∧ env 8 = UInt64.ofNat i ∧
      env 7 = UInt64.ofNat (q + 8 * opts.length + 8 * (Plan.wordsAll (opts.take i)).length) ∧
      env 0 = UInt64.ofNat q ∧ env 1 = UInt64.ofNat opts.length ∧ env 2 = UInt64.ofNat sel ∧
      env 3 = UInt64.ofNat (base + start) ∧ env 4 = UInt64.ofNat (base + stop) ∧ env 5 = UInt64.ofNat err ∧
      env 6 = 0 ∧
      ((env 9 = 0 ∧ X = validateOption (sels.drop i) (opts.drop i) sel b start stop) ∨
       (env 9 = 1 ∧ ∃ (h : i < opts.length), sels[i]'(by omega) = sel ∧
          X = validateOption (sels.drop i) (opts.drop i) sel b start stop)))
    (fun env _ => opts.length - (env 8).toNat + (if env 9 = 0 then 1 else 0))
    ⟨rfl, 0, Nat.zero_le _, by wfin [], by wfin [Plan.wordsAll], by wfin [], by wfin [], by wfin [], by wfin [],
      by wfin [], by wfin [], by wfin [], Or.inl ⟨by wfin [], by simp [hX]⟩⟩ ?_)
  rintro env mem' ⟨hmem, i, hi, h8, h7, h0, h1, h2, h3, h4, h5, h6, st⟩
  subst mem'
  have hil := wordsAll_take_le opts i
  rcases st with ⟨h9, rest⟩ | ⟨h9, hlt, hit, rest⟩
  · refine ⟨_, by wev [h8, h1, h9], fun nz => ?_, fun z => ?_⟩
    · have hio : i < opts.length := by
        rcases Nat.lt_or_ge i opts.length with h | h
        · exact h
        · simp [show ¬ i < opts.length by omega] at nz
      have r := hq.read (8 * i) (by omega) (by simp; omega)
      have a := hq.readable (8 * i) (by omega) (by simp; omega)
      have si : (sels ++ Plan.wordsAll opts)[8 * i / 8]! = sels[i]'(by omega) := by
        rw [show 8 * i / 8 = i by omega, getElem!_pos _ i (by simp; omega)]
        simp [List.getElem_append_left (show i < sels.length by omega)]
      rw [si] at r
      have sl := sfit _ (List.getElem_mem (show i < sels.length by omega))
      have dsel : sels.drop i = sels[i]'(by omega) :: sels.drop (i + 1) := List.drop_eq_getElem_cons (by omega)
      have dopt := drop_cons opts i hio
      by_cases m : sels[i]'(by omega) = sel
      · wsteps [h0, h8, r, a, h2, m]
        refine ⟨⟨trivial, i, hi, by wfin [h8], by wfin [h7], by wfin [h0], by wfin [h1], by wfin [h2], by wfin [h3],
          by wfin [h4], by wfin [h5], by wfin [h6], Or.inr ⟨by wfin [], hio, m, rest⟩⟩, by wfin [h8, h9]⟩
      · obtain ⟨_, hpj, slen⟩ := fieldAt ho i hio
        have fitj := fits_getElem opts fit i hio
        have nest := nesting_le_deepest opts opts[i] (List.getElem_mem hio)
        have skip := skip_calls hm opts[i] fitj _ (sp - 8 - 8 * 15) mem hpj (by simp only [Room] at room ⊢; omega)
        wsteps [h0, h8, r, a, h2, m]
        wcall skip [h7]
        wsteps [h8]
        refine ⟨⟨trivial, i + 1, by omega, by wfin [], ?_, by wfin [h0], by wfin [h1], by wfin [h2], by wfin [h3],
          by wfin [h4], by wfin [h5], by wfin [h6], Or.inl ⟨by wfin [h9], ?_⟩⟩, by wfin [h8, h9]⟩
        · wfin [take_succ_append opts i hio, wordsAll_append, Plan.wordsAll]
        · rw [rest, dsel, dopt, validateOption_skip _ _ _ _ _ _ _ _ m]
    · have hio : i = opts.length := by
        rcases Nat.lt_or_ge i opts.length with h | h
        · simp [h] at z
        · omega
      subst hio
      rw [List.drop_length, ← len, List.drop_length, validateOption] at rest
      wsteps [h9]
      wfail [h5, h2]
      wsteps []
      wfin [rest, res, after, wrote_eq]
  · refine ⟨_, by wev [h8, h1, h9], fun nz => absurd (by wonly []) nz, fun _ => ?_⟩
    have dsel : sels.drop i = sels[i]'(by omega) :: sels.drop (i + 1) := List.drop_eq_getElem_cons (by omega)
    rw [dsel, drop_cons opts i hlt, validateOption_hit _ _ _ _ _ _ _ _ hit] at rest
    by_cases rng : 1 ≤ sel ∧ sel ≤ 127
    · rw [if_pos rng] at rest
      obtain ⟨_, hpj, slen⟩ := fieldAt ho i hlt
      have cpj : Clear err (q + 8 * opts.length + 8 * (Plan.wordsAll (opts.take i)).length)
          (8 * (Plan.words opts[i]).length) := by unfold Clear at co ⊢; omega
      have fitj := fits_getElem opts fit i hlt
      have nest := nesting_le_deepest opts opts[i] (List.getElem_mem hlt)
      have step := ih opts[i] (List.getElem_mem hlt) fitj _ (sp - 8 - 8 * 15) mem base b start stop err hpj cpj hd
        cd ok hle hs small (by simp only [Room] at room ⊢; omega)
      have n1 : ¬ sel < 1 := by omega
      have n2 : ¬ 127 < sel := by omega
      wsteps [h9, h2, n1, n2]
      wcall step [h7, h3, h4, h5]
      wsteps []
      wfin [rest]
    · rw [if_neg rng] at rest
      have c : sel < 1 ∨ 127 < sel := by omega
      rcases c with c | c
      · wsteps [h9, h2, c]
        wfail [h5, h2]
        wsteps []
        wfin [rest, res, after, wrote_eq]
      · wsteps [h9, h2, c]
        wfail [h5, h2]
        wsteps []
        wfin [rest, res, after, wrote_eq]

end Ssz.Native.Driver.Validate
