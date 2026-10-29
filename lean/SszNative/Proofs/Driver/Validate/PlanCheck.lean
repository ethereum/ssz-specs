import SszNative.Proofs.Driver.Validate.Range

/-!
The plan's own check, on the plan of a legal type: it reads back to its end, every rule met.

A type's fields are named by position in a plan, so the check judges the type with those names.
Every pair of a union's options is judged by the compatibility routine; what that routine answers is taken here as a
premise, stated on its own, and proved where the routine is.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr

mutual

/-- Whether every struct of a type names its fields as a plan names them: by ordinal, or by layout position. -/
def named : Desc → Bool
  | .container names fields => names == Plan.positionNames fields.length && namedAll fields
  | .progressiveContainer active names fields => names == Plan.layoutNames active && namedAll fields
  | .vector element _ | .list element _ | .progressiveList element _ => named element
  | .compatibleUnion _ options => namedAll options
  | _ => true

/-- Whether every type of a list names its fields by position. -/
def namedAll : List Desc → Bool
  | [] => true
  | d :: rest => named d && namedAll rest

end

mutual

/-- Whether a type holds a union anywhere in it. -/
def hasUnion : Desc → Bool
  | .compatibleUnion _ _ => true
  | .vector element _ | .list element _ | .progressiveList element _ => hasUnion element
  | .container _ fields | .progressiveContainer _ _ fields => hasUnionAll fields
  | _ => false

/-- Whether any type of a list holds a union. -/
def hasUnionAll : List Desc → Bool
  | [] => false
  | d :: rest => hasUnion d || hasUnionAll rest

end

/-- A type of a list holding a union makes the list hold one. -/
theorem hasUnionAll_mem : ∀ (fs : List Desc) (f : Desc), f ∈ fs → hasUnion f = true → hasUnionAll fs = true
  | [], _, h, _ => by simp at h
  | g :: rest, f, h, u => by
    simp only [List.mem_cons] at h
    simp only [hasUnionAll, Bool.or_eq_true]
    rcases h with rfl | h
    · exact Or.inl u
    · exact Or.inr (hasUnionAll_mem rest f h u)

/-- Each type of a list named by position is named by position. -/
theorem namedAll_mem : ∀ (fs : List Desc), namedAll fs = true → ∀ f ∈ fs, named f = true
  | [], _, _, h => by simp at h
  | g :: rest, h, f, hf => by
    simp only [namedAll, Bool.and_eq_true] at h
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact h.1
    · exact namedAll_mem rest h.2 f hf

/-- Two checks one after the other accept exactly when both do. -/
theorem bind_unit_ok (x y : Except Err Unit) : (do x; y) = .ok () ↔ x = .ok () ∧ y = .ok () := by
  cases x <;> simp [Bind.bind, Except.bind]

/-- A refusal never accepts. -/
theorem throw_ok (e : Err) : (throw e : Except Err Unit) = .ok () ↔ False := by
  simp [throw, throwThe, MonadExceptOf.throw]

/-- A choice of checks accepts exactly when the chosen one does. -/
theorem ite_ok (c : Prop) [Decidable c] (A B : Except Err Unit) :
    (if c then A else B) = .ok () ↔ (c → A = .ok ()) ∧ (¬c → B = .ok ()) := by
  by_cases h : c <;> simp [h]

/-- Each type of a legal list is legal. -/
theorem allWellFormed_mem : ∀ (fs : List Desc), Desc.allWellFormed fs = .ok () → ∀ f ∈ fs, f.wellFormed = .ok ()
  | [], _, _, h => by simp at h
  | g :: rest, h, f, hf => by
    rw [Desc.allWellFormed, bind_unit_ok] at h
    simp only [List.mem_cons] at hf
    rcases hf with rfl | hf
    · exact h.1
    · exact allWellFormed_mem rest h.2 f hf

/-- What the compatibility routine is taken to answer: one, for the options of a legal union. -/
def PairsOk (m : Module) (w : World) : Prop :=
  ∀ (sels : List Nat) (opts : List Desc) (p sp : Nat) (mem : Memory),
    Desc.optionsCompatible sels opts = .ok () → allFitNative opts = true → namedAll opts = true →
    Desc.allWellFormed opts = .ok () → PlanAt w mem p (Plan.wordsAll opts) →
    Room w sp (2 * (Desc.deepestNesting opts + 1)) 1 →
    Calls m w "ssz_validate_pairs" sp [UInt64.ofNat p, UInt64.ofNat opts.length] mem 1 mem

/-- What checking a node of the plan computes, for a legal type: the address past its words. -/
def PlanOk (m : Module) (w : World) (d : Desc) : Prop :=
  (hasUnion d = true → PairsOk m w) → d.wellFormed = .ok () → fitsNative d = true → named d = true →
    ∀ (p stop sp : Nat) (mem : Memory), PlanAt w mem p (Plan.words d) → p + 8 * (Plan.words d).length ≤ stop →
      stop ≤ 2 ^ 63 → Room w sp (2 * d.nesting) 2 →
      Calls m w "ssz_validate_plan" sp [UInt64.ofNat p, UInt64.ofNat stop] mem
        (UInt64.ofNat (p + 8 * (Plan.words d).length)) mem

set_option maxHeartbeats 4000000 in
/-- Checking a count of legal nodes reads past all of them. -/
theorem planAll_calls {m : Module} {w : World} (hm : Loaded m) (fs : List Desc) (ih : ∀ f ∈ fs, PlanOk m w f)
    (pairs : hasUnionAll fs = true → PairsOk m w)
    (wf : Desc.allWellFormed fs = .ok ()) (fit : allFitNative fs = true) (nm : namedAll fs = true)
    (p stop sp : Nat) (mem : Memory) (hp : PlanAt w mem p (Plan.wordsAll fs))
    (hs : p + 8 * (Plan.wordsAll fs).length ≤ stop) (hstop : stop ≤ 2 ^ 63)
    (room : Room w sp (2 * (Desc.deepestNesting fs + 1)) 1) :
    Calls m w "ssz_validate_plan_all" sp [UInt64.ofNat p, UInt64.ofNat fs.length, UInt64.ofNat stop] mem
      (UInt64.ofNat (p + 8 * (Plan.wordsAll fs).length)) mem := by
  have hb := hp.bound
  have hl := length_le_wordsAll fs
  refine Calls.body 5 hm.planAll rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [planAllFn]
  refine Wp.single (Wp.loop (wp_loop (fun env mem' => mem' = mem ∧ ∃ j, j ≤ fs.length ∧
      env 0 = UInt64.ofNat (p + 8 * (Plan.wordsAll (fs.take j)).length) ∧ env 1 = UInt64.ofNat (fs.length - j) ∧
      env 2 = UInt64.ofNat stop)
    (fun env _ => (env 1).toNat) ⟨rfl, 0, Nat.zero_le _, by wfin [Plan.wordsAll], by wfin [], by wfin []⟩ ?_))
  rintro env mem' ⟨hmem, j, hj, h0, h1, h2⟩
  subst mem'
  have hjl := wordsAll_take_le fs j
  have ne : p + 8 * (Plan.wordsAll (fs.take j)).length ≠ 18446744073709551615 := by omega
  refine ⟨_, by wev [h0, h1, ne], fun nz => ?_, fun z => ?_⟩
  · have hjf : j < fs.length := by
      rcases Nat.lt_or_ge j fs.length with h | h
      · exact h
      · simp [show fs.length - j = 0 by omega] at nz
    obtain ⟨_, hpj, slen⟩ := fieldAt hp j hjf
    have nest := nesting_le_deepest fs fs[j] (List.getElem_mem hjf)
    have step := ih fs[j] (List.getElem_mem hjf)
      (fun u => pairs (hasUnionAll_mem fs fs[j] (List.getElem_mem hjf) u)) (allWellFormed_mem fs wf _ (List.getElem_mem hjf))
      (fits_getElem fs fit j hjf) (namedAll_mem fs nm _ (List.getElem_mem hjf)) _ stop (sp - 8 - 8 * 5) mem hpj
      (by omega) hstop (by simp only [Room] at room ⊢; omega)
    wcall step [h0, h2]
    wsteps [h1]
    refine ⟨⟨trivial, j + 1, by omega, ?_, by wfin [], by wfin [h2]⟩, by wfin [h1]⟩
    wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
  · have hjk : j = fs.length := by
      rcases Nat.lt_or_ge j fs.length with h | h
      · simp [show fs.length - j ≠ 0 by omega] at z
      · omega
    subst hjk
    exact Wp.done ⟨by wonly [h0, List.take_length], rfl⟩

/-- What a legal union declares: options, each under its own selector in range, every two compatible. -/
theorem wf_union (sels : List Nat) (opts : List Desc) (h : (Desc.compatibleUnion sels opts).wellFormed = .ok ()) :
    sels ≠ [] ∧ sels.length = opts.length ∧ firstDuplicate sels = none ∧ (∀ s ∈ sels, 1 ≤ s ∧ s ≤ 127) ∧
      Desc.allWellFormed opts = .ok () ∧ Desc.optionsCompatible sels opts = .ok () := by
  simp only [Desc.wellFormed] at h
  by_cases e : (sels.isEmpty || opts.isEmpty) = true
  · simp [e, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
  simp only [e, Bool.false_eq_true, ite_false] at h
  by_cases l : (sels.length != opts.length) = true
  · simp [l, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
  simp only [l, Bool.false_eq_true, ite_false] at h
  cases hd : firstDuplicate sels with
  | some s => simp [hd, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
  | none =>
    simp only [hd] at h
    split at h
    · simp [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
    · rename_i hf
      simp only [bind_unit_ok] at h
      simp only [Bool.or_eq_true, List.isEmpty_iff, not_or] at e
      simp only [bne_iff_ne, ne_eq, Decidable.not_not] at l
      refine ⟨e.1, l, rfl, fun s hs => ?_, h.1, h.2⟩
      have := List.find?_eq_none.mp hf s hs
      simp [minSelector, maxSelector] at this
      omega

/-- A list with no first duplicate repeats no entry. -/
theorem firstDuplicate_none : ∀ (l : List Nat), firstDuplicate l = none →
    ∀ i j (hi : i < l.length) (hj : j < l.length), j < i → l[j] ≠ l[i]
  | [], _, _, _, hi, _, _ => by simp at hi
  | x :: rest, h, i, j, hi, hj, lt => by
    simp only [firstDuplicate] at h
    split at h
    · cases h
    · rename_i nc
      cases j with
      | zero =>
        cases i with
        | zero => omega
        | succ i =>
          simp only [List.getElem_cons_zero, List.getElem_cons_succ]
          intro eq
          apply nc
          simp only [List.contains_iff_mem, eq]
          exact List.getElem_mem _
      | succ j =>
        cases i with
        | zero => omega
        | succ i =>
          simp only [List.getElem_cons_succ]
          exact firstDuplicate_none rest h i j (by simp at hi; omega) (by simp at hj; omega) (by omega)

set_option hygiene false in
/-- Opens a proof about one node of the plan's check. -/
macro "plan_open" : tactic => `(tactic| (
  intro pairs wf fit nm p stop sp mem hp hs hstop room
  have hb := hp.bound
  have r0 := hp.read0 (words_length_pos _)
  have a0 := hp.readable0 (words_length_pos _)
  rw [words_head] at r0
  simp only [Plan.tag] at r0
  simp [Plan.words] at hb a0 hs
  have s8 : p + 8 ≤ stop := by omega
  refine Calls.body 15 hm.plan rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [planFn]))

set_option hygiene false in
/-- Reads a plan node's second word. -/
macro "plan_word" : tactic => `(tactic| (
  have r1 := hp.read 8 rfl (by simp [Plan.words] <;> omega)
  have a1 := hp.readable 8 rfl (by simp [Plan.words] <;> omega)
  simp [Plan.words] at r1))

set_option maxHeartbeats 16000000 in
/-- Checking the plan of a legal type reads past its words, given what the compatibility routine answers. -/
theorem plan_calls {m : Module} {w : World} (hm : Loaded m) (d : Desc) : PlanOk m w d := by
  induction d using Desc.rec (motive_2 := fun fs => ∀ f ∈ fs, PlanOk m w f) with
  | nil => rename_i h; simp at h
  | cons f fs ihf ihfs =>
    rename_i g h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ihf
    · exact ihfs g h
  | bool =>
    plan_open
    wsteps [r0, a0, s8]
    wfin [Plan.words]
  | uint width =>
    plan_open
    plan_word
    have s16 : p + 16 ≤ stop := by omega
    simp [Desc.wellFormed] at wf
    have : width = 1 ∨ width = 2 ∨ width = 4 ∨ width = 8 ∨ width = 16 ∨ width = 32 := by omega
    rcases this with h | h | h | h | h | h <;> subst h <;>
    · wsteps [r0, a0, s8, r1, a1, s16]
      wfin [Plan.words]
  | byteVector n | bitVector n =>
    plan_open
    plan_word
    have s16 : p + 16 ≤ stop := by omega
    simp [Desc.wellFormed] at wf
    simp [fitsNative] at fit
    have n32 : n < 4294967296 := fit
    wsteps [r0, a0, s8, r1, a1, s16, wf, n32]
    wfin [Plan.words]
  | byteList _ | bitList _ =>
    plan_open
    plan_word
    have s16 : p + 16 ≤ stop := by omega
    wsteps [r0, a0, s8, r1, a1, s16]
    wfin [Plan.words]
  | progressiveBitList l =>
    plan_open
    have s24 : p + 24 ≤ stop := by omega
    -- The bound is two zeros or a one then the value.
    have r1 := hp.read 8 rfl (by cases l <;> simp [Plan.words, Plan.bound])
    have a1 := hp.readable 8 rfl (by cases l <;> simp [Plan.words, Plan.bound])
    have r2 := hp.read 16 rfl (by cases l <;> simp [Plan.words, Plan.bound])
    have a2 := hp.readable 16 rfl (by cases l <;> simp [Plan.words, Plan.bound])
    cases l with
    | none =>
      simp [Plan.words, Plan.bound] at r1 r2
      wsteps [r0, a0, s8, s24, r1, a1, r2, a2, canonicalBound]
      wfin [Plan.words, Plan.bound]
    | some v =>
      have v64 : v < 2 ^ 64 := by simpa [fitsNative] using fit
      simp [Plan.words, Plan.bound] at r1 r2
      wsteps [r0, a0, s8, s24, r1, a1, r2, a2, canonicalBound, v64]
      wfin [Plan.words, Plan.bound]
  | list e limit ih | progressiveList e limit ih =>
    plan_open
    have fe : fitsNative e = true := by simp [fitsNative] at fit; exact fit.1
    have we : e.wellFormed = .ok () := by simpa [Desc.wellFormed] using wf
    have ne : named e = true := by simpa [named] using nm
    first
    | (have he : PlanAt w mem (p + 16) (Plan.words e) := by
          have := hp.right (a := [8, limit]) (b := Plan.words e); simpa using this
       have step := ih (fun u => pairs (by simpa [hasUnion] using u)) we fe ne (p + 16) stop (sp - 8 - 8 * 15) mem he (by omega) hstop
          (by simp only [Room, Desc.nesting] at room ⊢; omega)
       have s16 : p + 16 ≤ stop := by omega
       wsteps [r0, a0, s8, s16]
       wcall step []
       wsteps []
       wfin [Plan.words])
    | (have he : PlanAt w mem (p + 24) (Plan.words e) := by
          have := hp.right (a := 9 :: Plan.bound limit) (b := Plan.words e); simpa using this
       have step := ih (fun u => pairs (by simpa [hasUnion] using u)) we fe ne (p + 24) stop (sp - 8 - 8 * 15) mem he (by omega) hstop
          (by simp only [Room, Desc.nesting] at room ⊢; omega)
       have s24 : p + 24 ≤ stop := by omega
       -- The bound is two zeros or a one then the value.
       have r1 := hp.read 8 rfl (by cases limit <;> simp [Plan.words, Plan.bound])
       have a1 := hp.readable 8 rfl (by cases limit <;> simp [Plan.words, Plan.bound])
       have r2 := hp.read 16 rfl (by cases limit <;> simp [Plan.words, Plan.bound])
       have a2 := hp.readable 16 rfl (by cases limit <;> simp [Plan.words, Plan.bound])
       cases limit with
       | none =>
         simp [Plan.words, Plan.bound] at r1 r2
         wsteps [r0, a0, s8, s24, r1, a1, r2, a2, canonicalBound]
         wcall step []
         wsteps []
         wfin [Plan.words, Plan.bound]
       | some v =>
         have v64 : v < 2 ^ 64 := by simp [fitsNative] at fit; exact fit.2
         simp [Plan.words, Plan.bound] at r1 r2
         wsteps [r0, a0, s8, s24, r1, a1, r2, a2, canonicalBound, v64]
         wcall step []
         wsteps []
         wfin [Plan.words, Plan.bound])
  | vector e n ih =>
    plan_open
    plan_word
    simp [Desc.wellFormed, ite_ok, throw_ok, bind_unit_ok] at wf
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at fit
    have ne : named e = true := by simpa [named] using nm
    have he : PlanAt w mem (p + 16) (Plan.words e) := by
      have := hp.right (a := [7, n]) (b := Plan.words e); simpa using this
    have step := ih (fun u => pairs (by simpa [hasUnion] using u)) (wf.2 wf.1) fit.1.1 ne (p + 16) stop (sp - 8 - 8 * 15) mem he (by omega) hstop
      (by simp only [Room, Desc.nesting] at room ⊢; omega)
    have width := width_calls hm e fit.1.1 (p + 16) (sp - 8 - 8 * 15) mem he
      (by simp only [Room, Desc.nesting] at room ⊢; omega)
    have s16 : p + 16 ≤ stop := by omega
    have n32 : n < 4294967296 := fit.1.2
    have qne : p + 16 + 8 * (Plan.words e).length ≠ 18446744073709551615 := by omega
    by_cases has : hasWidth e = true
    · simp only [widthWord, ite_eq_left has] at width
      have fw := fixedWidth_lt e fit.1.1 has
      have hne : fixedWidth e ≠ 18446744073709551615 := by omega
      have prod : fixedWidth e * n < 4294967296 := by
        rcases fit.2 with h | h
        · simp [h] at has
        · exact h
      wsteps [r0, a0, s8, r1, a1, s16, wf.1, n32]
      wcall step []
      wsteps [qne]
      wcall width []
      wsteps [hne, prod]
      wfin [Plan.words]
    · simp only [widthWord, ite_eq_right has] at width
      wsteps [r0, a0, s8, r1, a1, s16, wf.1, n32]
      wcall step []
      wsteps [qne]
      wcall width []
      wsteps []
      wfin [Plan.words]
  | container names fs ih =>
    plan_open
    plan_word
    simp [Desc.wellFormed, ite_ok, throw_ok, bind_unit_ok] at wf
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
    simp only [named, Bool.and_eq_true] at nm
    have hf : PlanAt w mem (p + 16) (Plan.wordsAll fs) := by
      have := hp.right (a := [10, fs.length]) (b := Plan.wordsAll fs); simpa using this
    have wfs : Desc.allWellFormed fs = .ok () := (wf.2 wf.1).1 (wf.2 wf.1).2 |>.2 ((wf.2 wf.1).1 (wf.2 wf.1).2).1
    have pa := planAll_calls hm fs ih (fun u => pairs (by simpa [hasUnion] using u)) wfs fit.1.1 nm.2 (p + 16) stop (sp - 8 - 8 * 15) mem hf (by omega) hstop
      (by simp only [Room, Desc.nesting] at room ⊢; omega)
    have lc := leading_calls hm fs fit.1.1 (p + 16) (sp - 8 - 8 * 15) mem hf
      (by simp only [Room, Desc.nesting] at room ⊢; omega)
    have s16 : p + 16 ≤ stop := by omega
    have n0 : fs.length ≠ 0 := by intro h; exact wf.1 (List.eq_nil_of_length_eq_zero h)
    have n32 : fs.length < 4294967296 := fit.1.2
    have l32 : Desc.leadingWidth fs < 4294967296 := fit.2
    have qne : p + 16 + 8 * (Plan.wordsAll fs).length ≠ 18446744073709551615 := by omega
    wsteps [r0, a0, s8, r1, a1, s16, n0, n32]
    wcall pa [r1, a1]
    wsteps [qne]
    wcall lc [r1, a1]
    wsteps [l32]
    wfin [Plan.words]
  | progressiveContainer active names fs ih =>
    plan_open
    plan_word
    simp [Desc.wellFormed, ite_ok, throw_ok, bind_unit_ok, maxActiveFields] at wf
    obtain ⟨ane, wf⟩ := wf
    obtain ⟨last, wf⟩ := wf ane
    obtain ⟨a256, wf⟩ := wf last
    obtain ⟨fne, wf⟩ := wf a256
    obtain ⟨wf, cnt⟩ := wf fne
    obtain ⟨wf, nlen⟩ := wf cnt
    have wfs : Desc.allWellFormed fs = .ok () := (wf nlen).2 (wf nlen).1
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
    simp only [named, Bool.and_eq_true] at nm
    have k0 : active.length ≠ 0 := by intro h; exact ane (List.eq_nil_of_length_eq_zero h)
    have e : Plan.words (.progressiveContainer active names fs) =
        ([11, active.length] ++ active.map (fun b => if b then 1 else 0) ++ [fs.length]) ++ Plan.wordsAll fs := by
      simp [Plan.words]
    have hlen : (Plan.words (.progressiveContainer active names fs)).length =
        active.length + 3 + (Plan.wordsAll fs).length := by
      rw [e]; simp; omega
    have hf : PlanAt w mem (p + 24 + 8 * active.length) (Plan.wordsAll fs) := by
      have hp' := hp; rw [e] at hp'
      refine hp'.right.at_eq ?_
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]
      omega
    -- The words of the layout: each position's bit, the last one set, then the field count.
    have bit : ∀ i, i < active.length → readLE mem (p + 16 + 8 * i) 8 =
        UInt64.ofNat (if active[i]! then 1 else 0) := by
      intro i hi
      have := hp.read (16 + 8 * i) (by omega) (by rw [hlen]; omega)
      rw [Nat.add_assoc, this, show (16 + 8 * i) / 8 = i + 2 by omega, e]
      simp only [getElem!_def, List.append_assoc]
      rw [List.getElem?_append_right (by simp), List.getElem?_append_left (by simp; omega)]
      simp [show i + 2 - 2 = i by omega, hi]
    have bitOk : ∀ i, i < active.length → w.access (p + 16 + 8 * i) 8 = true := by
      intro i hi
      have := hp.readable (16 + 8 * i) (by omega) (by rw [hlen]; omega)
      rwa [← Nat.add_assoc] at this
    have rn : readLE mem (p + 16 + 8 * active.length) 8 = UInt64.ofNat fs.length := by
      have := hp.read (16 + 8 * active.length) (by omega) (by rw [hlen]; omega)
      rw [Nat.add_assoc, this, show (16 + 8 * active.length) / 8 = active.length + 2 by omega, e]
      simp only [getElem!_def, List.append_assoc]
      rw [List.getElem?_append_right (by simp)]
      simp
    have an : w.access (p + 16 + 8 * active.length) 8 = true := by
      have := hp.readable (16 + 8 * active.length) (by omega) (by rw [hlen]; omega)
      rwa [← Nat.add_assoc] at this
    have rl : readLE mem (p + 8 + 8 * active.length) 8 = 1 := by
      have := bit (active.length - 1) (by omega)
      rw [show p + 16 + 8 * (active.length - 1) = p + 8 + 8 * active.length by omega] at this
      rw [this]
      have : active[active.length - 1]! = true := by
        rw [getElem!_pos active (active.length - 1) (by omega)]
        rw [List.getLast?_eq_getElem?] at last
        simp [getElem?_pos active (active.length - 1) (by omega)] at last
        exact last
      simp [this]
    have al : w.access (p + 8 + 8 * active.length) 8 = true := by
      have := bitOk (active.length - 1) (by omega)
      rwa [show p + 16 + 8 * (active.length - 1) = p + 8 + 8 * active.length by omega] at this
    have pa := planAll_calls hm fs ih (fun u => pairs (by simpa [hasUnion] using u)) wfs fit.1.1 nm.2 (p + 24 + 8 * active.length) stop (sp - 8 - 8 * 15) mem hf
      (by omega) hstop (by simp only [Room, Desc.nesting] at room ⊢; omega)
    have lc := leading_calls hm fs fit.1.1 (p + 24 + 8 * active.length) (sp - 8 - 8 * 15) mem hf
      (by simp only [Room, Desc.nesting] at room ⊢; omega)
    have s16 : p + 16 ≤ stop := by omega
    have s24 : p + 24 + 8 * active.length ≤ stop := by omega
    have l32 : Desc.leadingWidth fs < 4294967296 := fit.2
    have qne : p + 24 + 8 * active.length + 8 * (Plan.wordsAll fs).length ≠ 18446744073709551615 := by omega
    wsteps [r0, a0, s8, r1, a1, s16, k0, a256, s24]
    refine Wp.loop (wp_loop (fun env mem' => mem' = mem ∧ ∃ i, i ≤ active.length ∧ env 7 = UInt64.ofNat i ∧
        env 8 = UInt64.ofNat ((active.take i).countP (fun x => x)) ∧ env 0 = UInt64.ofNat p ∧
        env 1 = UInt64.ofNat stop ∧ env 4 = UInt64.ofNat active.length ∧ env 3 = 18446744073709551615 ∧ env 9 = 1)
      (fun env _ => active.length - (env 7).toNat)
      ⟨rfl, 0, Nat.zero_le _, by wfin [], by wfin [], by wfin [], by wfin [], by wfin [], by wfin [], by wfin []⟩ ?_)
    rintro env mem' ⟨hmem, i, hi, h7, h8, h0, h1, h4, h3, h9⟩
    subst mem'
    have ct := List.countP_le_length (p := fun x => x) (l := active.take i)
    simp only [List.length_take] at ct
    refine ⟨_, by wev [h7, h4], fun nz => ?_, fun z => ?_⟩
    · have hia : i < active.length := by
        rcases Nat.lt_or_ge i active.length with h | h
        · exact h
        · simp [show ¬ i < active.length by omega] at nz
      have rb := bit i hia
      have ab := bitOk i hia
      have succ : (active.take (i + 1)).countP (fun x => x) =
          (active.take i).countP (fun x => x) + (if active[i]! then 1 else 0) := by
        rw [List.take_add_one, List.getElem?_eq_getElem hia, getElem!_pos active i hia]
        cases active[i] <;> simp
      -- Each bit is zero or one, so the flag for a wrong bit stays up.
      cases hb : active[i]! <;> simp only [hb, ite_true, Bool.false_eq_true, ite_false, Nat.add_zero] at rb succ
      all_goals
        wsteps [h0, h7, h8, rb, ab, h9]
        exact ⟨⟨trivial, i + 1, by omega, by wfin [], by wfin [h8, succ], by wfin [h0], by wfin [h1], by wfin [h4],
          by wfin [h3], by wfin [h9]⟩, by wfin [h7]⟩
    · have hia : i = active.length := by
        rcases Nat.lt_or_ge i active.length with h | h
        · simp [h] at z
        · omega
      subst hia
      simp only [List.take_length] at h8
      have cq : List.countP (fun x => x) active = fs.length := by simpa using cnt
      rw [cq] at h8
      wsteps [h0, h4, rl, al, rn, an, h8, h9]
      wcall pa [h0, h4, h1, h8]
      wsteps [qne]
      wcall lc [h0, h4, h8]
      wsteps [l32]
      wfin [Plan.words, hlen, h3]
  | compatibleUnion sels opts ih =>
    plan_open
    plan_word
    obtain ⟨sne, lens, dup, rng, wfs, comp⟩ := wf_union sels opts wf
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at fit
    simp only [named] at nm
    obtain ⟨⟨⟨fa, n32⟩, slen⟩, sfit⟩ := fit
    have e : Plan.words (.compatibleUnion sels opts) = ([12, opts.length] ++ sels) ++ Plan.wordsAll opts := by
      simp [Plan.words]
    have hlen : (Plan.words (.compatibleUnion sels opts)).length = 2 + opts.length + (Plan.wordsAll opts).length := by
      rw [e]; simp [slen]; omega
    have hf : PlanAt w mem (p + 16 + 8 * opts.length) (Plan.wordsAll opts) := by
      have hp' := hp; rw [e] at hp'
      refine hp'.right.at_eq ?_
      simp [slen]; omega
    have sel : ∀ i (hi : i < opts.length), readLE mem (p + 16 + 8 * i) 8 = UInt64.ofNat (sels[i]'(by omega)) := by
      intro i hi
      have := hp.read (16 + 8 * i) (by omega) (by rw [hlen]; omega)
      rw [Nat.add_assoc, this, show (16 + 8 * i) / 8 = i + 2 by omega, e]
      simp only [getElem!_def, List.append_assoc]
      rw [List.getElem?_append_right (by simp), List.getElem?_append_left (by simp; omega)]
      simp [show i + 2 - 2 = i by omega, List.getElem?_eq_getElem (show i < sels.length by omega)]
    have selOk : ∀ i, i < opts.length → w.access (p + 16 + 8 * i) 8 = true := by
      intro i hi
      have := hp.readable (16 + 8 * i) (by omega) (by rw [hlen]; omega)
      rwa [← Nat.add_assoc] at this
    have distinct := firstDuplicate_none sels dup
    have s16 : p + 16 ≤ stop := by omega
    have n0 : opts.length ≠ 0 := by intro h; exact sne (List.eq_nil_of_length_eq_zero (by omega))
    have sn : p + 16 + 8 * opts.length ≤ stop := by omega
    have pa := planAll_calls hm opts ih (fun _ => pairs rfl) wfs fa nm (p + 16 + 8 * opts.length) stop
      (sp - 8 - 8 * 15) mem hf (by omega) hstop (by simp only [Room, Desc.nesting] at room ⊢; omega)
    have pr := pairs rfl sels opts (p + 16 + 8 * opts.length) (sp - 8 - 8 * 15) mem comp fa nm wfs hf
      (by simp only [Room, Desc.nesting] at room ⊢; omega)
    have qne : p + 16 + 8 * opts.length + 8 * (Plan.wordsAll opts).length ≠ 18446744073709551615 := by omega
    wsteps [r0, a0, s8, r1, a1, s16, n0, n32, sn]
    refine Wp.loop (wp_loop (fun env mem' => mem' = mem ∧ ∃ i, i ≤ opts.length ∧ env 7 = UInt64.ofNat i ∧
        env 8 = 1 ∧ env 0 = UInt64.ofNat p ∧ env 1 = UInt64.ofNat stop ∧ env 4 = UInt64.ofNat opts.length ∧
        env 3 = 18446744073709551615)
      (fun env _ => opts.length - (env 7).toNat)
      ⟨rfl, 0, Nat.zero_le _, by wfin [], by wfin [], by wfin [], by wfin [], by wfin [], by wfin []⟩ ?_)
    rintro env mem' ⟨hmem, i, hi, h7, h8, h0, h1, h4, h3⟩
    subst mem'
    refine ⟨_, by wev [h7, h4], fun nz => ?_, fun z => ?_⟩
    · have hio : i < opts.length := by
        rcases Nat.lt_or_ge i opts.length with h | h
        · exact h
        · simp [show ¬ i < opts.length by omega] at nz
      have ri := sel i hio
      have ai := selOk i hio
      have r := rng _ (List.getElem_mem (show i < sels.length by omega))
      have sl := sfit _ (List.getElem_mem (show i < sels.length by omega))
      have lo : ¬ sels[i]'(by omega) < 1 := by omega
      have hi' : ¬ 127 < sels[i]'(by omega) := by omega
      wsteps [h0, h7, ri, ai, lo, hi']
      refine Wp.loop (wp_loop (fun env' mem' => mem' = mem ∧ ∃ j, j ≤ i ∧ env' 10 = UInt64.ofNat j ∧
          env' 7 = UInt64.ofNat i ∧ env' 9 = UInt64.ofNat (sels[i]'(by omega)) ∧
          env' 8 = 1 ∧ env' 0 = UInt64.ofNat p ∧ env' 1 = UInt64.ofNat stop ∧ env' 4 = UInt64.ofNat opts.length ∧
          env' 3 = 18446744073709551615)
        (fun env' _ => i - (env' 10).toNat)
        ⟨rfl, 0, Nat.zero_le _, by wfin [], by wfin [h7], by wfin [], by wfin [h8], by wfin [h0], by wfin [h1],
          by wfin [h4], by wfin [h3]⟩ ?_)
      rintro env' mem' ⟨hmem', j, hj, g10, g7, g9, g8, g0, g1, g4, g3⟩
      subst mem'
      refine ⟨_, by wev [g10, g7], fun nz' => ?_, fun z' => ?_⟩
      · have hji : j < i := by
          rcases Nat.lt_or_ge j i with h | h
          · exact h
          · simp [show ¬ j < i by omega] at nz'
        have rj := sel j (by omega)
        have aj := selOk j (by omega)
        have dj := distinct i j (by omega) (by omega) hji
        have slj := sfit _ (List.getElem_mem (show j < sels.length by omega))
        wsteps [g0, g10, rj, aj, g9, dj]
        exact ⟨⟨trivial, j + 1, by omega, by wfin [], by wfin [g7], by wfin [g9], by wfin [g8], by wfin [g0],
          by wfin [g1], by wfin [g4], by wfin [g3]⟩, by wfin [g10]⟩
      · have hji : j = i := by
          rcases Nat.lt_or_ge j i with h | h
          · simp [h] at z'
          · omega
        subst hji
        wsteps [g7]
        exact ⟨⟨trivial, j + 1, by omega, by wfin [], by wfin [g8], by wfin [g0], by wfin [g1], by wfin [g4],
          by wfin [g3]⟩, by wfin [g7, h7]⟩
    · have hio : i = opts.length := by
        rcases Nat.lt_or_ge i opts.length with h | h
        · simp [h] at z
        · omega
      subst hio
      wsteps [h8, h0, h4]
      wcall pa [h0, h4, h1]
      wsteps [qne]
      wcall pr [h0, h4]
      wsteps []
      wfin [hlen, h3]

end EthLib.Consensus.Ssz.Native.Driver.Validate
