import SszNative.Proofs.Driver.Validate.Skip
import SszNative.Proofs.Validate.Plan

/-!
The fixed width of a type, read from its plan.

A type with no fixed width reads as the word that no width reaches.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr

/-- The word standing for no width. -/
abbrev noWidth : Nat := 18446744073709551615

/-- A type's width as the native check computes it: its fixed width, or the word standing for none. -/
def widthWord (d : Desc) : Nat := if hasWidth d then fixedWidth d else noWidth

/-- A list of fields' total width as the native check computes it. -/
def fieldsWord (fs : List Desc) : Nat := if allHaveWidth fs then fieldsWidth fs else noWidth

/-! Widths of lists. -/

/-- Two lists of fields are fixed exactly when each is. -/
theorem allHaveWidth_append : ∀ a b : List Desc, allHaveWidth (a ++ b) = (allHaveWidth a && allHaveWidth b)
  | [], _ => by simp [allHaveWidth]
  | d :: a, b => by simp [allHaveWidth, allHaveWidth_append a b, Bool.and_assoc]

/-- Two lists of fixed fields are as wide as both. -/
theorem fieldsWidth_append : ∀ a b : List Desc, fieldsWidth (a ++ b) = fieldsWidth a + fieldsWidth b
  | [], _ => by simp [fieldsWidth]
  | d :: a, b => by simp [fieldsWidth, fieldsWidth_append a b, Nat.add_assoc]

/-- Two lists of fields take as much of the fixed part as both. -/
theorem leadingWidth_append : ∀ a b : List Desc,
    Desc.leadingWidth (a ++ b) = Desc.leadingWidth a + Desc.leadingWidth b
  | [], _ => by simp [Desc.leadingWidth]
  | d :: a, b => by simp [Desc.leadingWidth, leadingWidth_append a b, Nat.add_assoc]

/-- A fixed field's slot in the fixed part is its width, and a variable field's an offset. -/
theorem leadingWidth_cons (f : Desc) (fs : List Desc) :
    Desc.leadingWidth (f :: fs) = (if hasWidth f then fixedWidth f else 4) + Desc.leadingWidth fs := by
  simp only [Desc.leadingWidth, fixedSize_eq f]
  split <;> rfl

/-- Fixed fields take exactly their widths in the fixed part. -/
theorem leadingWidth_of_all : ∀ fs : List Desc, allHaveWidth fs = true → Desc.leadingWidth fs = fieldsWidth fs
  | [], _ => rfl
  | f :: fs, h => by
    simp only [allHaveWidth, Bool.and_eq_true] at h
    rw [leadingWidth_cons, ite_eq_left h.1, leadingWidth_of_all fs h.2, fieldsWidth]

/-- The first fields, and one more. -/
theorem take_succ_append (fs : List Desc) (j : Nat) (hj : j < fs.length) : fs.take (j + 1) = fs.take j ++ [fs[j]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl

/-- The first fields take no more of the fixed part than all of them. -/
theorem leadingWidth_take_le (fs : List Desc) (j : Nat) : Desc.leadingWidth (fs.take j) ≤ Desc.leadingWidth fs := by
  conv => rhs; rw [← List.take_append_drop j fs]
  rw [leadingWidth_append]; omega

/-- A fitting type's fixed width fits below 2^32. -/
theorem fixedWidth_lt (d : Desc) : fitsNative d = true → hasWidth d = true → fixedWidth d < 2 ^ 32 := by
  intro fit has
  cases d with
  | bool => simp [fixedWidth]
  | uint w | byteVector w => simp [fitsNative] at fit; simpa [fixedWidth] using fit
  | bitVector n => simp [fitsNative] at fit; simp [fixedWidth]; omega
  | vector e n =>
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at fit
    simp only [hasWidth] at has
    simp only [fixedWidth]
    rcases fit.2 with h | h
    · simp [h] at has
    · exact h
  | container _ fs | progressiveContainer _ _ fs =>
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
    simp only [hasWidth] at has
    simp only [fixedWidth]
    rw [← leadingWidth_of_all fs has]; exact fit.2
  | _ => simp [hasWidth] at has

/-- A field of a list that fits fits. -/
theorem fits_getElem (fs : List Desc) (fit : allFitNative fs = true) (j : Nat) (hj : j < fs.length) :
    fitsNative fs[j] = true := allFitNative_mem fs fit _ (List.getElem_mem hj)

/-- What reading a node's width computes. -/
def WidthOk (m : Module) (w : World) (d : Desc) : Prop :=
  fitsNative d = true → ∀ (p sp : Nat) (mem : Memory), PlanAt w mem p (Plan.words d) → Room w sp d.nesting 2 →
    Calls m w "ssz_validate_width" sp [UInt64.ofNat p] mem (UInt64.ofNat (widthWord d)) mem

/-- Summing a count of fields' widths, stopping at the first variable one. -/
theorem fieldsWidth_calls {m : Module} {w : World} (hm : Loaded m) (fs : List Desc)
    (ih : ∀ f ∈ fs, WidthOk m w f) (fit : allFitNative fs = true) (lead : Desc.leadingWidth fs < 2 ^ 32)
    (p sp : Nat) (mem : Memory) (hp : PlanAt w mem p (Plan.wordsAll fs))
    (room : Room w sp (Desc.deepestNesting fs + 1) 1) :
    Calls m w "ssz_validate_fields_width" sp [UInt64.ofNat p, UInt64.ofNat fs.length] mem
      (UInt64.ofNat (fieldsWord fs)) mem := by
  have hb := hp.bound
  have hl := length_le_wordsAll fs
  refine Calls.body 5 hm.fieldsWidth rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [fieldsWidthFn]
  apply Wp.set (by wev [])
  refine Wp.loop (wp_loop (fun env mem' => mem' = mem ∧
      ((∃ j, j ≤ fs.length ∧ allHaveWidth (fs.take j) = true ∧
        env 0 = UInt64.ofNat (p + 8 * (Plan.wordsAll (fs.take j)).length) ∧
        env 1 = UInt64.ofNat (fs.length - j) ∧ env 2 = UInt64.ofNat (fieldsWidth (fs.take j))) ∨
      (env 1 = 0 ∧ env 2 = UInt64.ofNat noWidth ∧ allHaveWidth fs = false)))
    (fun env _ => (env 1).toNat) ⟨rfl, Or.inl ⟨0, Nat.zero_le _, by simp [allHaveWidth],
      by simp [entryEnv, Asm.assign, Plan.wordsAll], by simp [entryEnv, Asm.assign],
      by simp [Asm.assign, fieldsWidth]⟩⟩ ?_)
  rintro env mem' ⟨hmem, inv⟩
  subst hmem
  rcases inv with ⟨j, hj, all, h0, h1, h2⟩ | ⟨h1, h2, none⟩
  · have hjl := wordsAll_take_le fs j
    refine ⟨if fs.length - j = 0 then 0 else 1, by wonly [h1], fun nz => ?_, fun z => ?_⟩
    · have hjf : j < fs.length := by
        rcases Nat.lt_or_ge j fs.length with h | h
        · exact h
        · simp [show fs.length - j = 0 by omega] at nz
      have split := wordsAll_split fs j hjf
      have slen := congrArg List.length split
      simp only [List.length_append] at slen
      have hpj : PlanAt w mem' (p + 8 * (Plan.wordsAll (fs.take j)).length) (Plan.words fs[j]) := by
        rw [split] at hp; exact hp.left.right
      have nest := nesting_le_deepest fs fs[j] (List.getElem_mem hjf)
      have hroom : Room w (sp - 8 - 8 * 5) fs[j].nesting 2 := by
        simp only [Room] at room ⊢
        omega
      have step := ih fs[j] (List.getElem_mem hjf) (fits_getElem fs fit j hjf) _ _ mem' hpj hroom
      have hroom' : Room w (sp - 8 - 8 * 5) fs[j].nesting 2 := hroom
      have skip := skip_calls hm fs[j] (fits_getElem fs fit j hjf) _ _ mem' hpj (by simp only [Room] at hroom' ⊢; omega)
      have lt := leadingWidth_take_le fs (j + 1)
      rw [take_succ_append fs j hjf, leadingWidth_append] at lt
      simp only [Desc.leadingWidth, Nat.add_zero] at lt
      by_cases has : hasWidth fs[j] = true
      · have fw := fixedWidth_lt fs[j] (fits_getElem fs fit j hjf) has
        have lw : Desc.leadingWidth (fs.take j) = fieldsWidth (fs.take j) := leadingWidth_of_all _ all
        rw [fixedSize_eq, ite_eq_left has] at lt
        simp only [Option.getD_some] at lt
        simp only [widthWord, ite_eq_left has] at step
        have hne : fixedWidth fs[j] ≠ 18446744073709551615 := by omega
        wcall step [h0]
        wsteps [h0, h1, h2, hne]
        wcall skip [h0]
        wsteps [h1]
        refine ⟨⟨trivial, Or.inl ⟨j + 1, by omega, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
        · rw [take_succ_append fs j hjf, allHaveWidth_append]; simp [all, allHaveWidth, has]
        · wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
        · wfin []
        · wfin [take_succ_append fs j hjf, fieldsWidth_append, fieldsWidth, h2]
        · wfin [h1]
      · simp only [widthWord, ite_eq_right has] at step
        wcall step [h0]
        wsteps [h0, h1, h2]
        refine ⟨⟨trivial, Or.inr ⟨by wfin [], by wfin [], ?_⟩⟩, ?_⟩
        · rw [← List.take_append_drop j fs, ← List.take_append_drop 1 (fs.drop j)]
          simp only [allHaveWidth_append, List.take_one, List.drop_eq_getElem_cons hjf, List.head?_cons,
            Option.toList_some]
          simp [allHaveWidth, has]
        · wfin [h1]
    · have hjk : j = fs.length := by
        rcases Nat.lt_or_ge j fs.length with h | h
        · simp [show fs.length - j ≠ 0 by omega] at z
        · omega
      subst hjk
      simp only [List.take_length] at all h2
      exact Wp.done ⟨by wonly [fieldsWord, all, h2], rfl⟩
  · refine ⟨0, by wonly [h1], fun nz => absurd rfl nz, fun _ => Wp.done ⟨by wonly [fieldsWord, none, h2], rfl⟩⟩

set_option hygiene false in
/-- Opens a proof about one node: the plan's bound, and the node's tag word read and readable. -/
macro "node_open" : tactic => `(tactic| (
  intro fit p sp mem hp room
  have hb := hp.bound
  have r0 := hp.read0 (words_length_pos _)
  have a0 := hp.readable0 (words_length_pos _)
  simp [Plan.words] at r0 a0 hb))

set_option hygiene false in
/-- Reads a node's second word too. -/
macro "node_word" : tactic => `(tactic| (
  have r1 := hp.read 8 rfl (by simp [Plan.words] <;> omega)
  have a1 := hp.readable 8 rfl (by simp [Plan.words] <;> omega)
  simp [Plan.words] at r1))

/-- Reading a node's width gives its fixed width, or the word standing for none. -/
theorem width_calls {m : Module} {w : World} (hm : Loaded m) (d : Desc) : WidthOk m w d := by
  induction d using Desc.rec (motive_2 := fun fs => ∀ f ∈ fs, WidthOk m w f) with
  | nil => rename_i h; simp at h
  | cons f fs ihf ihfs =>
    rename_i g h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ihf
    · exact ihfs g h
  | bool =>
    node_open
    refine Calls.body 9 hm.width rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [widthFn]
    wsteps [r0, a0]
    wfin [widthWord, hasWidth, fixedWidth]
  | uint _ | byteVector _ | bitVector _ =>
    node_open
    node_word
    simp [fitsNative] at fit
    refine Calls.body 9 hm.width rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [widthFn]
    wsteps [r0, a0, r1, a1]
    wfin [widthWord, hasWidth, fixedWidth]
  | byteList _ | bitList _ | list _ _ _ | progressiveList _ _ _ | compatibleUnion _ _ _ =>
    node_open
    node_word
    refine Calls.body 9 hm.width rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [widthFn]
    wsteps [r0, a0, r1, a1]
    wfin [widthWord, hasWidth, fixedWidth]
  | progressiveBitList _ =>
    node_open
    node_word
    refine Calls.body 9 hm.width rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [widthFn]
    wsteps [r0, a0, r1, a1]
    wfin [widthWord, hasWidth, fixedWidth]
  | vector e n ih =>
    node_open
    node_word
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at fit
    have he : PlanAt w mem (p + 16) (Plan.words e) := by
      have := hp.right (a := [7, n]) (b := Plan.words e); simpa using this
    have step := ih fit.1.1 (p + 16) (sp - 8 - 8 * 9) mem he (by simp only [Room, Desc.nesting] at room ⊢; omega)
    refine Calls.body 9 hm.width rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [widthFn]
    wsteps [r0, a0, r1, a1]
    by_cases has : hasWidth e = true
    · have fw := fixedWidth_lt e fit.1.1 has
      have prod : fixedWidth e * n < 2 ^ 32 := by
        rcases fit.2 with h | h
        · simp [h] at has
        · exact h
      have hne : fixedWidth e ≠ 18446744073709551615 := by omega
      simp only [widthWord, ite_eq_left has] at step
      wcall step []
      wsteps [r1, a1, hne]
      wfin [widthWord, hasWidth, fixedWidth, has]
    · simp only [widthWord, ite_eq_right has] at step
      wcall step []
      wsteps [r1, a1]
      wfin [widthWord, hasWidth, fixedWidth, has]
  | container names fs ih =>
    node_open
    node_word
    have hf : PlanAt w mem (p + 16) (Plan.wordsAll fs) := by
      have := hp.right (a := [10, fs.length]) (b := Plan.wordsAll fs); simpa using this
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
    have step := fieldsWidth_calls hm fs ih fit.1.1 fit.2 (p + 16) (sp - 8 - 8 * 9) mem hf
      (by simp only [Room, Desc.nesting] at room ⊢; omega)
    refine Calls.body 9 hm.width rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [widthFn]
    wsteps [r0, a0, r1, a1]
    wcall step [r1, a1]
    wsteps []
    wfin [widthWord, hasWidth, fixedWidth, fieldsWord]
    all_goals congr 1
  | progressiveContainer active names fs ih =>
    node_open
    node_word
    have r2 := hp.read (16 + 8 * active.length) (by omega) (by simp [Plan.words]; omega)
    have a2 := hp.readable (16 + 8 * active.length) (by omega) (by simp [Plan.words]; omega)
    rw [← Nat.add_assoc] at r2 a2
    have r2' : readLE mem (p + 16 + 8 * active.length) 8 = UInt64.ofNat fs.length := by
      rw [r2, show (16 + 8 * active.length) / 8 = active.length + 2 by omega]
      simp only [Plan.words, getElem!_def, List.append_assoc]
      rw [List.getElem?_append_right (by simp)]
      simp
    have hf : PlanAt w mem (p + 24 + 8 * active.length) (Plan.wordsAll fs) := by
      have e : Plan.words (.progressiveContainer active names fs) =
          ([11, active.length] ++ active.map (fun b => if b then 1 else 0) ++ [fs.length]) ++ Plan.wordsAll fs := by
        simp [Plan.words]
      rw [e] at hp
      refine hp.right.at_eq ?_
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]
      omega
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
    have step := fieldsWidth_calls hm fs ih fit.1.1 fit.2 (p + 24 + 8 * active.length) (sp - 8 - 8 * 9) mem hf
      (by simp only [Room, Desc.nesting] at room ⊢; omega)
    refine Calls.body 9 hm.width rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [widthFn]
    wsteps [r0, a0, r1, a1, r2', a2]
    wcall step [r1, a1, r2', a2]
    wsteps []
    wfin [widthWord, hasWidth, fixedWidth, fieldsWord]
    all_goals congr 1

/-- The width of a struct's fixed part, an offset standing for each variable field. -/
theorem leading_calls {m : Module} {w : World} (hm : Loaded m) (fs : List Desc) (fit : allFitNative fs = true)
    (p sp : Nat) (mem : Memory) (hp : PlanAt w mem p (Plan.wordsAll fs))
    (room : Room w sp (Desc.deepestNesting fs + 1) 1) :
    Calls m w "ssz_validate_leading" sp [UInt64.ofNat p, UInt64.ofNat fs.length] mem
      (UInt64.ofNat (Desc.leadingWidth fs)) mem := by
  have hb := hp.bound
  have hl := length_le_wordsAll fs
  refine Calls.body 5 hm.leading rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [leadingFn]
  apply Wp.set (by wev [])
  refine Wp.loop (wp_loop (fun env mem' => mem' = mem ∧
      ∃ j, j ≤ fs.length ∧ env 0 = UInt64.ofNat (p + 8 * (Plan.wordsAll (fs.take j)).length) ∧
        env 1 = UInt64.ofNat (fs.length - j) ∧ env 2 = UInt64.ofNat (Desc.leadingWidth (fs.take j)))
    (fun env _ => (env 1).toNat) ⟨rfl, 0, Nat.zero_le _, by simp [entryEnv, Asm.assign, Plan.wordsAll],
      by simp [entryEnv, Asm.assign], by simp [Asm.assign, Desc.leadingWidth]⟩ ?_)
  rintro env mem' ⟨hmem, j, hj, h0, h1, h2⟩
  subst hmem
  have hjl := wordsAll_take_le fs j
  refine ⟨if fs.length - j = 0 then 0 else 1, by wonly [h1], fun nz => ?_, fun z => ?_⟩
  · have hjf : j < fs.length := by
      rcases Nat.lt_or_ge j fs.length with h | h
      · exact h
      · simp [show fs.length - j = 0 by omega] at nz
    have split := wordsAll_split fs j hjf
    have slen := congrArg List.length split
    simp only [List.length_append] at slen
    have hpj : PlanAt w mem' (p + 8 * (Plan.wordsAll (fs.take j)).length) (Plan.words fs[j]) := by
      rw [split] at hp; exact hp.left.right
    have nest := nesting_le_deepest fs fs[j] (List.getElem_mem hjf)
    have hroom : Room w (sp - 8 - 8 * 5) fs[j].nesting 2 := by
      simp only [Room] at room ⊢
      omega
    have step := width_calls hm fs[j] (fits_getElem fs fit j hjf) _ _ mem' hpj hroom
    have skip := skip_calls hm fs[j] (fits_getElem fs fit j hjf) _ _ mem' hpj hroom
    have lt := leadingWidth_take_le fs (j + 1)
    rw [take_succ_append fs j hjf, leadingWidth_append, leadingWidth_cons] at lt
    simp only [Desc.leadingWidth, Nat.add_zero] at lt
    have next : Desc.leadingWidth (fs.take (j + 1)) =
        Desc.leadingWidth (fs.take j) + (if hasWidth fs[j] then fixedWidth fs[j] else 4) := by
      rw [take_succ_append fs j hjf, leadingWidth_append, leadingWidth_cons]; simp [Desc.leadingWidth]
    by_cases has : hasWidth fs[j] = true
    · have fw := fixedWidth_lt fs[j] (fits_getElem fs fit j hjf) has
      have hne : fixedWidth fs[j] ≠ 18446744073709551615 := by omega
      simp only [widthWord, ite_eq_left has] at step
      simp only [ite_eq_left has] at lt next
      wcall step [h0]
      wsteps [h0, h1, h2, hne]
      wcall skip [h0]
      wsteps [h1]
      refine ⟨⟨trivial, j + 1, by omega, ?_, ?_, ?_⟩, ?_⟩
      · wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
      · wfin []
      · wfin [next, h2]
      · wfin [h1]
    · simp only [widthWord, ite_eq_right has] at step
      simp only [ite_eq_right has] at lt next
      wcall step [h0]
      wsteps [h0, h1, h2]
      wcall skip [h0]
      wsteps [h1]
      refine ⟨⟨trivial, j + 1, by omega, ?_, ?_, ?_⟩, ?_⟩
      · wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
      · wfin []
      · wfin [next, h2]
      · wfin [h1]
  · have hjk : j = fs.length := by
      rcases Nat.lt_or_ge j fs.length with h | h
      · simp [show fs.length - j ≠ 0 by omega] at z
      · omega
    subst hjk
    simp only [List.take_length] at h2
    exact Wp.done ⟨by wonly [h2], rfl⟩

end EthLib.Consensus.Ssz.Native.Driver.Validate
