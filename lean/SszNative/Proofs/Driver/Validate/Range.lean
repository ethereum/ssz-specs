import SszNative.Proofs.Driver.Validate.Option

/-!
One range against one type, read from its plan: the check the whole native check is made of.

Each kind of type hands the range to the function for its kind, which comes back here for the types inside it.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr

/-- A fixed-size type's range: the size checks, then its probes. -/
theorem validateRange_fixed (d : Desc) (b : ByteArray) (start stop : Nat) (has : hasWidth d = true) :
    validateRange d b start stop =
      if composite d = true ∧ 2 ^ 32 ≤ stop - start then .error (.offsetOverflow (stop - start))
      else if stop - start ≠ fixedWidth d then .error (.scope (fixedWidth d) (stop - start))
      else checkProbes b start (plan d) := by
  rw [validateRange, ite_eq_left has, validateFixed, checkRuns_runs]
  by_cases c : composite d = true ∧ 2 ^ 32 ≤ stop - start
  · have h1 : (composite d && decide (stop - start ≥ 2 ^ (8 * bytesPerOffset))) = true := by
      simp [c.1, bytesPerOffset]; omega
    rw [ite_eq_left c]; simp only [h1, ite_true]; rfl
  · rw [ite_eq_right c]
    have h1 : (composite d && decide (stop - start ≥ 2 ^ (8 * bytesPerOffset))) = false := by
      cases hc : composite d
      · rfl
      · simp only [hc, true_and] at c; simp [bytesPerOffset]; omega
    by_cases s : stop - start ≠ fixedWidth d
    · have h2 : (stop - start != fixedWidth d) = true := by simpa using s
      simp [h1, h2, s, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    · have h2 : (stop - start != fixedWidth d) = false := by simpa using s
      rw [ite_eq_right s]
      simp only [h1, h2, Bool.false_eq_true, ite_false]

/-- A variable-size type's range, by its kind. -/
theorem validateRange_var (d : Desc) (b : ByteArray) (start stop : Nat) (has : hasWidth d = false) :
    validateRange d b start stop = validateVariable d b start stop := by
  rw [validateRange, ite_eq_right (by simp [has])]

/-- A node's first word is its tag. -/
theorem words_head (d : Desc) : (Plan.words d)[0]! = Plan.tag d := by
  cases d <;> simp [Plan.words, Plan.tag]

/-- Tags run up to twelve. -/
theorem tag_le (d : Desc) : Plan.tag d ≤ 12 := by cases d <;> simp [Plan.tag]

/-- A fixed-size type is composite exactly when its tag is a byte vector's, a vector's, or a struct's. -/
theorem composite_tag (d : Desc) (has : hasWidth d = true) :
    composite d = true ↔ (Plan.tag d = 2 ∨ Plan.tag d = 7 ∨ Plan.tag d = 10 ∨ Plan.tag d = 11) := by
  cases d <;> simp_all [composite, Plan.tag, hasWidth]

set_option maxHeartbeats 4000000 in
/-- A fixed-size type's range checked natively: the size checks, then the probes. -/
theorem range_fixed_calls {m : Module} {w : World} (hm : Loaded m) (d : Desc) (has : hasWidth d = true)
    (fit : fitsNative d = true) (p sp : Nat) (mem : Memory) (base : Nat) (b : ByteArray) (start stop err : Nat)
    (hp : PlanAt w mem p (Plan.words d)) (cp : Clear err p (8 * (Plan.words d).length))
    (hd : DataAt w mem base b) (cd : Clear err base b.size) (ok : w.access err 32 = true)
    (hle : start ≤ stop) (hs : stop ≤ b.size) (room : Room w sp d.nesting 4) :
    Calls m w "ssz_validate_range" sp [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (base + stop),
      UInt64.ofNat err] mem (res (validateRange d b start stop)) (after mem err (validateRange d b start stop)) := by
  have hb := hp.bound
  have db := hd.bound
  have eb : err + 32 ≤ 2 ^ 63 := by
    have := ok; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  have r0 := hp.read0 (words_length_pos _)
  have a0 := hp.readable0 (words_length_pos _)
  rw [words_head] at r0
  have tl := tag_le d
  have hsz : base + stop - (base + start) = stop - start := by omega
  have width := width_calls hm d fit p (sp - 8 - 8 * 15) mem hp (by simp only [Room] at room ⊢; omega)
  simp only [widthWord, ite_eq_left has] at width
  have fw := fixedWidth_lt d fit has
  have hne : fixedWidth d ≠ 18446744073709551615 := by omega
  rw [validateRange_fixed d b start stop has]
  refine Calls.body 15 hm.range rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [rangeFn]
  wsteps [hsz]
  wcall width []
  wsteps [r0, a0, hne]
  have ct := composite_tag d has
  -- The overflow test: a composite type's tag and a size past four-byte offsets.
  by_cases o : composite d = true ∧ 2 ^ 32 ≤ stop - start
  · have o' : 4294967296 ≤ stop - start := o.2
    have tg := ct.mp o.1
    rcases tg with t | t | t | t <;>
    · wsteps [hsz, t, o']
      wfail []
      wsteps []
      wfin [o, res, after, wrote_eq]
  · have cases : (Plan.tag d ≠ 2 ∧ Plan.tag d ≠ 7 ∧ Plan.tag d ≠ 10 ∧ Plan.tag d ≠ 11) ∨
        ¬ 4294967296 ≤ stop - start := by
      by_cases c : composite d = true
      · right; intro h; exact o ⟨c, h⟩
      · left; rw [ct] at c; omega
    by_cases sc : stop - start ≠ fixedWidth d
    · rcases cases with ⟨t2, t7, t10, t11⟩ | small'
      · wsteps [hsz, t2, t7, t10, t11, sc]
        wfail []
        wsteps []
        wfin [o, sc, res, after, wrote_eq]
      · wsteps [hsz, small', sc]
        wfail []
        wsteps []
        wfin [o, sc, res, after, wrote_eq]
    · simp only [ne_eq, Decidable.not_not] at sc
      have hfw4 : ¬ 4294967296 ≤ fixedWidth d := by omega
      have pr := probe_calls hm d fit has p (sp - 8 - 8 * 15) mem base b start err hp cp hd cd ok (by omega)
        (by simp only [Room] at room ⊢; omega)
      rcases cases with ⟨t2, t7, t10, t11⟩ | small'
      · wsteps [hsz, t2, t7, t10, t11, sc, hfw4]
        wcall pr []
        wsteps []
        wfin [o, sc, hfw4]
      · wsteps [hsz, small', sc, hfw4]
        wcall pr []
        wsteps []
        wfin [o, sc, hfw4]

set_option hygiene false in
/-- Opens a proof about one range against a variable-size node. -/
macro "range_open" : tactic => `(tactic| (
  intro fit p sp mem base b start stop err hp cp hd cd ok hle hs small room
  have hb := hp.bound
  have db := hd.bound
  have eb : err + 32 ≤ 2 ^ 63 := by
    have := ok; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  have r0 := hp.read0 (words_length_pos _)
  have a0 := hp.readable0 (words_length_pos _)
  rw [words_head] at r0
  simp only [Plan.tag] at r0
  simp [Plan.words] at hb a0
  have hsz : base + stop - (base + start) = stop - start := by omega))

set_option hygiene false in
/-- Reads a variable-size node's second word. -/
macro "range_word" : tactic => `(tactic| (
  have r1 := hp.read 8 rfl (by simp [Plan.words] <;> omega)
  have a1 := hp.readable 8 rfl (by simp [Plan.words] <;> omega)
  simp [Plan.words] at r1))

set_option hygiene false in
/-- Enters the range function on a variable-size node, past its width. -/
macro "range_enter" : tactic => `(tactic| (
  have width := width_calls hm _ fit p (sp - 8 - 8 * 15) mem hp (by simp only [Room] at room ⊢; omega)
  simp only [widthWord, hasWidth, Bool.false_eq_true, ite_false] at width
  refine Calls.body 15 hm.range rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [rangeFn]
  wsteps [hsz]
  wcall width []
  wsteps [r0, a0]))

set_option maxHeartbeats 16000000 in
/-- Checking a range against any type that fits natively refuses exactly as the Lean check does. -/
theorem range_calls {m : Module} {w : World} (hm : Loaded m) (d : Desc) : RangeOk m w d := by
  induction d using Desc.rec (motive_2 := fun fs => ∀ f ∈ fs, RangeOk m w f) with
  | nil => rename_i h; simp at h
  | cons f fs ihf ihfs =>
    rename_i g h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ihf
    · exact ihfs g h
  | bool | uint _ | byteVector _ | bitVector _ =>
    intro fit p sp mem base b start stop err hp cp hd cd ok hle hs _ room
    exact range_fixed_calls hm _ rfl fit p sp mem base b start stop err hp cp hd cd ok hle hs room
  | byteList limit =>
    range_open
    range_word
    rw [validateRange_var _ _ _ _ rfl, validateVariable]
    have fl := fit
    simp only [fitsNative, decide_eq_true_eq] at fl
    range_enter
    have ob : offsetBound = 4294967296 := rfl
    by_cases o : 4294967296 ≤ stop - start
    · wsteps [hsz, o]
      wfail []
      wsteps []
      wfin [ob, o, res, after, wrote_eq, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    · by_cases ol : limit < stop - start
      · wsteps [hsz, o, r1, a1, ol]
        wfail [r1, a1]
        wsteps []
        wfin [ob, o, ol, res, after, wrote_eq, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
      · wsteps [hsz, o, r1, a1, ol]
        wfin [ob, o, ol, res, after, pure, Except.pure]
  | bitList limit =>
    range_open
    range_word
    rw [validateRange_var _ _ _ _ rfl, validateVariable]
    have fl := fit
    simp only [fitsNative, decide_eq_true_eq] at fl
    have dl := delimited_calls hm mem base b start stop 1 limit err (sp - 8 - 8 * 15) hle hs small (by decide) fl hd ok
      (by simp only [Room] at room ⊢; omega)
    range_enter
    wcall dl [r1, a1]
    wsteps []
    wfin [delimitedOutcome, Plan.readBound, discard]
  | progressiveBitList l =>
    range_open
    range_word
    have r2 := hp.read 16 rfl (by simp [Plan.words])
    have a2 := hp.readable 16 rfl (by simp [Plan.words])
    simp [Plan.words] at r2
    rw [validateRange_var _ _ _ _ rfl, validateVariable]
    have fl := fit
    simp only [fitsNative] at fl
    cases l with
    | none =>
      simp [Plan.bound] at r1 r2
      have dl := delimited_calls hm mem base b start stop 0 0 err (sp - 8 - 8 * 15) hle hs small (by decide)
        (by decide) hd ok (by simp only [Room] at room ⊢; omega)
      range_enter
      wcall dl [r1, a1, r2, a2]
      wsteps []
      wfin [delimitedOutcome, Plan.readBound, discard]
    | some v =>
      simp [Plan.bound] at r1 r2 fl
      have dl := delimited_calls hm mem base b start stop 1 v err (sp - 8 - 8 * 15) hle hs small (by decide)
        fl hd ok (by simp only [Room] at room ⊢; omega)
      range_enter
      wcall dl [r1, a1, r2, a2]
      wsteps []
      wfin [delimitedOutcome, Plan.readBound, discard]
  | vector e n ih =>
    range_open
    by_cases he : hasWidth e = true
    · exact range_fixed_calls hm _ (by simpa [hasWidth] using he) fit p sp mem base b start stop err hp cp hd cd ok
        hle hs room
    · simp only [Bool.not_eq_true] at he
      rw [validateRange_var _ _ _ _ (by simpa [hasWidth] using he), validateVariable]
      have vc := vector_calls hm e n ih fit he p (sp - 8 - 8 * 15) mem base b start stop err hp cp hd cd ok hle hs small
        (by simp only [Room, Desc.nesting] at room ⊢; omega)
      have width := width_calls hm _ fit p (sp - 8 - 8 * 15) mem hp (by simp only [Room] at room ⊢; omega)
      simp only [widthWord, hasWidth, he, Bool.false_eq_true, ite_false] at width
      refine Calls.body 15 hm.range rfl (by simp only [Room] at room; omega) rfl ?_
      simp only [rangeFn]
      wsteps [hsz]
      wcall width []
      wsteps [r0, a0]
      wcall vc []
      wsteps []
      wfin []
  | list e limit ih =>
    range_open
    range_word
    rw [validateRange_var _ _ _ _ rfl, validateVariable]
    have fl := fit
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fl
    have he : PlanAt w mem (p + 16) (Plan.words e) := by
      have := hp.right (a := [8, limit]) (b := Plan.words e); simpa using this
    have ce : Clear err (p + 16) (8 * (Plan.words e).length) := by
      simp [Plan.words] at cp; unfold Clear at cp ⊢; omega
    have lc := list_calls hm e ih fl.1 1 limit (by decide) fl.2 (p + 16) (sp - 8 - 8 * 15) mem base b start stop err
      he ce hd cd ok hle hs small (by simp only [Room, Desc.nesting] at room ⊢; omega)
    simp only [Plan.readBound] at lc
    range_enter
    wcall lc [r1, a1]
    wsteps []
    wfin []
  | progressiveList e l ih =>
    range_open
    range_word
    have r2 := hp.read 16 rfl (by simp [Plan.words]; omega)
    have a2 := hp.readable 16 rfl (by simp [Plan.words]; omega)
    simp [Plan.words] at r2
    rw [validateRange_var _ _ _ _ rfl, validateVariable]
    have fl := fit
    simp only [fitsNative, Bool.and_eq_true] at fl
    have he : PlanAt w mem (p + 24) (Plan.words e) := by
      have := hp.right (a := 9 :: Plan.bound l) (b := Plan.words e); simpa using this
    have ce : Clear err (p + 24) (8 * (Plan.words e).length) := by
      simp [Plan.words] at cp; unfold Clear at cp ⊢; omega
    cases l with
    | none =>
      simp [Plan.bound] at r1 r2
      have lc := list_calls hm e ih fl.1 0 0 (by decide) (by decide) (p + 24) (sp - 8 - 8 * 15) mem base b start stop
        err he ce hd cd ok hle hs small (by simp only [Room, Desc.nesting] at room ⊢; omega)
      simp only [Plan.readBound] at lc
      range_enter
      wcall lc [r1, a1, r2, a2]
      wsteps []
      wfin []
    | some v =>
      simp [Plan.bound] at r1 r2 fl
      have lc := list_calls hm e ih fl.1 1 v (by decide) fl.2 (p + 24) (sp - 8 - 8 * 15) mem base b start stop
        err he ce hd cd ok hle hs small (by simp only [Room, Desc.nesting] at room ⊢; omega)
      simp only [Plan.readBound] at lc
      range_enter
      wcall lc [r1, a1, r2, a2]
      wsteps []
      wfin []
  | container names fs ih =>
    range_open
    by_cases all : allHaveWidth fs = true
    · exact range_fixed_calls hm _ (by simpa [hasWidth] using all) fit p sp mem base b start stop err hp cp hd cd ok
        hle hs room
    · simp only [Bool.not_eq_true] at all
      range_word
      rw [validateRange_var _ _ _ _ (by simpa [hasWidth] using all), validateVariable]
      have fl := fit
      simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fl
      have hf : PlanAt w mem (p + 16) (Plan.wordsAll fs) := by
        have := hp.right (a := [10, fs.length]) (b := Plan.wordsAll fs); simpa using this
      have cf : Clear err (p + 16) (8 * (Plan.wordsAll fs).length) := by
        simp [Plan.words] at cp; unfold Clear at cp ⊢; omega
      have sc := struct_calls hm fs ih fl.1.1 fl.2 (p + 16) (sp - 8 - 8 * 15) mem base b start stop err hf cf hd cd ok
        hle hs small (by simp only [Room, Desc.nesting] at room ⊢; omega)
      have width := width_calls hm _ fit p (sp - 8 - 8 * 15) mem hp (by simp only [Room] at room ⊢; omega)
      simp only [widthWord, hasWidth, all, Bool.false_eq_true, ite_false] at width
      refine Calls.body 15 hm.range rfl (by simp only [Room] at room; omega) rfl ?_
      simp only [rangeFn]
      wsteps [hsz]
      wcall width []
      wsteps [r0, a0]
      wcall sc [r1, a1]
      wsteps []
      wfin []
  | progressiveContainer active names fs ih =>
    range_open
    by_cases all : allHaveWidth fs = true
    · exact range_fixed_calls hm _ (by simpa [hasWidth] using all) fit p sp mem base b start stop err hp cp hd cd ok
        hle hs room
    · simp only [Bool.not_eq_true] at all
      range_word
      have r2 := hp.read (16 + 8 * active.length) (by omega) (by simp [Plan.words]; omega)
      have a2 := hp.readable (16 + 8 * active.length) (by omega) (by simp [Plan.words]; omega)
      rw [← Nat.add_assoc] at r2 a2
      have r2' : readLE mem (p + 16 + 8 * active.length) 8 = UInt64.ofNat fs.length := by
        rw [r2, show (16 + 8 * active.length) / 8 = active.length + 2 by omega]
        simp only [Plan.words, getElem!_def, List.append_assoc]
        rw [List.getElem?_append_right (by simp)]
        simp
      have e : Plan.words (.progressiveContainer active names fs) =
          ([11, active.length] ++ active.map (fun b => if b then 1 else 0) ++ [fs.length]) ++ Plan.wordsAll fs := by
        simp [Plan.words]
      have hf : PlanAt w mem (p + 24 + 8 * active.length) (Plan.wordsAll fs) := by
        have hp' := hp; rw [e] at hp'
        refine hp'.right.at_eq ?_
        simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]
        omega
      have cf : Clear err (p + 24 + 8 * active.length) (8 * (Plan.wordsAll fs).length) := by
        have cp' := cp; rw [e] at cp'; simp at cp'; unfold Clear at cp' ⊢; omega
      rw [validateRange_var _ _ _ _ (by simpa [hasWidth] using all), validateVariable]
      have fl := fit
      simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fl
      have sc := struct_calls hm fs ih fl.1.1 fl.2 (p + 24 + 8 * active.length) (sp - 8 - 8 * 15) mem base b start
        stop err hf cf hd cd ok hle hs small (by simp only [Room, Desc.nesting] at room ⊢; omega)
      have width := width_calls hm _ fit p (sp - 8 - 8 * 15) mem hp (by simp only [Room] at room ⊢; omega)
      simp only [widthWord, hasWidth, all, Bool.false_eq_true, ite_false] at width
      refine Calls.body 15 hm.range rfl (by simp only [Room] at room; omega) rfl ?_
      simp only [rangeFn]
      wsteps [hsz]
      wcall width []
      wsteps [r0, a0, r1, a1]
      wcall sc [r1, a1, r2', a2]
      wsteps []
      wfin []
  | compatibleUnion sels opts ih =>
    range_open
    range_word
    rw [validateRange_var _ _ _ _ rfl, validateVariable]
    have fl := fit
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at fl
    have hq : PlanAt w mem (p + 16) (sels ++ Plan.wordsAll opts) := by
      have := hp.right (a := [12, opts.length]) (b := sels ++ Plan.wordsAll opts); simpa [Plan.words] using this
    have cq : Clear err (p + 16) (8 * (sels ++ Plan.wordsAll opts).length) := by
      simp [Plan.words] at cp; simp; unfold Clear at cp ⊢; omega
    have ob : offsetBound = 4294967296 := rfl
    by_cases z : stop - start = 0
    · range_enter
      wsteps [hsz, z]
      wfail []
      wsteps []
      wfin [z, res, after, wrote_eq, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    · have rb := hd.byteAt start (by omega)
      have ab := hd.byteOk start (by omega)
      have hbyte := (b.get! start).toNat_lt
      have oc := option_calls hm sels opts ih fl.1.1.1 fl.1.2 (fun s hs => by simpa using fl.2 s hs)
        (b.get! start).toNat hbyte (p + 16) (sp - 8 - 8 * 15) mem base b (start + 1) stop err hq cq hd cd ok
        (by omega) hs small (by simp only [Room, Desc.nesting] at room ⊢; omega)
      range_enter
      wsteps [hsz, z]
      have z' : ¬ stop - start < 1 := by omega
      wcall oc [r1, a1, rb, ab]
      wsteps []
      wfin [z, z']

end EthLib.Consensus.Ssz.Native.Driver.Validate
