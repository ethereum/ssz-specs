import SszNative.Proofs.Driver.Validate.Compat

/-!
The compatibility check of a union's options, on the plans of legal types named as a plan names them.

Equality compares two nodes' words, which for such types is equality of the types.
Compatibility walks both nodes as the Lean check does, with no budget: past the left type's nesting the budget never
changes the answer.
So the options of a legal union pass, and the options of a union whose options clash do not.
-/

namespace Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open Ssz Ssz.Native Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Ir.Stmt Ssz.Native.Ir.Expr

/-- What the native check assumes of a type it compares: legal, named as a plan names it, fitting its sizes. -/
structure Sound (d : Desc) : Prop where
  /-- The type is legal. -/
  wf : d.wellFormed = .ok ()
  /-- Its fields are named as a plan names them. -/
  named : named d = true
  /-- Its sizes fit the native check. -/
  fits : fitsNative d = true

/-- Each word of a sound type's plan fits a word. -/
theorem Sound.small {d : Desc} (h : Sound d) : ∀ x ∈ Plan.words d, x < 2 ^ 64 := words_lt d h.wf h.fits

/-- Two lists as long as each other agree one entry further exactly when they agree so far and on that entry. -/
theorem take_succ_eq {l r : List Nat} (len : l.length = r.length) {i : Nat} (hi : i < l.length) :
    l.take (i + 1) = r.take (i + 1) ↔ l.take i = r.take i ∧ l[i]! = r[i]! := by
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (show i < r.length by omega), getElem!_pos l i hi,
    getElem!_pos r i (by omega)]
  constructor
  · intro h
    -- The prefixes have one length, so the appended entries line up.
    have := List.append_inj h (by simp [len])
    simp only [Option.toList_some, List.cons.injEq, and_true] at this
    exact this
  · rintro ⟨h, e⟩; rw [h, e]

set_option maxHeartbeats 4000000 in
/-- Comparing two sound nodes' words answers whether the types are equal. -/
theorem eq_calls {m : Module} {w : World} (hm : Loaded m) {a b : Desc} (sa : Sound a) (sb : Sound b)
    (pa pb level sp : Nat) (mem : Memory) (ha : PlanAt w mem pa (Plan.words a)) (hb : PlanAt w mem pb (Plan.words b))
    (da : a.nesting ≤ level) (db : b.nesting ≤ level) (room : Room w sp level 3) :
    Calls m w "ssz_validate_eq" sp [UInt64.ofNat pa, UInt64.ofNat pb] mem (if a == b then 1 else 0) mem := by
  have ba := ha.bound
  have bb := hb.bound
  have ka := skip_calls hm a sa.fits pa (sp - 8 - 8 * 11) mem ha (by simp only [Room] at room ⊢; omega)
  have kb := skip_calls hm b sb.fits pb (sp - 8 - 8 * 11) mem hb (by simp only [Room] at room ⊢; omega)
  refine Calls.body 11 hm.eq rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [eqFn]
  wcall ka []
  wcall kb []
  wsteps []
  have la := sa.small
  have lb := sb.small
  by_cases hl : (Plan.words a).length = (Plan.words b).length
  · have h8 : 8 * (Plan.words a).length / 8 = (Plan.words a).length := by omega
    wsteps [hl, Nat.add_sub_cancel_left, h8]
    -- After i words, the result says whether the first i words agree.
    refine Wp.loop (wp_loop (fun env mem' => mem' = mem ∧ ∃ i, i ≤ (Plan.words a).length ∧ env 6 = UInt64.ofNat i ∧
        env 2 = (if (Plan.words a).take i = (Plan.words b).take i then 1 else 0) ∧ env 0 = UInt64.ofNat pa ∧
        env 1 = UInt64.ofNat pb ∧ env 5 = UInt64.ofNat (Plan.words a).length)
      (fun env _ => (Plan.words a).length - (env 6).toNat)
      ⟨rfl, 0, Nat.zero_le _, by wfin [], by wfin [], by wfin [], by wfin [], by wfin [h8]⟩ ?_)
    rintro env mem' ⟨hmem, i, hi, h6, h2, h0, h1, h5⟩
    subst mem'
    by_cases agree : (Plan.words a).take i = (Plan.words b).take i
    · rw [if_pos agree] at h2
      refine ⟨_, by wev [h6, h5, h2], fun nz => ?_, fun z => ?_⟩
      · have hia : i < (Plan.words a).length := by
          rcases Nat.lt_or_ge i (Plan.words a).length with h | h
          · exact h
          · simp [show ¬ i < (Plan.words a).length by omega] at nz
        have ra : readLE mem (pa + 8 * i) 8 = UInt64.ofNat (Plan.words a)[i]! := by
          have := ha.read (8 * i) (by omega) (by omega); rwa [show 8 * i / 8 = i by omega] at this
        have rb : readLE mem (pb + 8 * i) 8 = UInt64.ofNat (Plan.words b)[i]! := by
          have := hb.read (8 * i) (by omega) (by omega); rwa [show 8 * i / 8 = i by omega] at this
        have aa := ha.readable (8 * i) (by omega) (by omega)
        have ab := hb.readable (8 * i) (by omega) (by omega)
        have xa : (Plan.words a)[i]! < 2 ^ 64 := la _ (by rw [getElem!_pos _ i hia]; exact List.getElem_mem hia)
        have xb : (Plan.words b)[i]! < 2 ^ 64 :=
          lb _ (by rw [getElem!_pos _ i (by omega)]; exact List.getElem_mem (by omega))
        have step := take_succ_eq hl hia
        by_cases e : (Plan.words a)[i]! = (Plan.words b)[i]!
        · wsteps [h0, h1, h6, ra, rb, aa, ab, e, xa, xb]
          exact ⟨⟨trivial, i + 1, by omega, by wfin [], by wfin [h2, step.mpr ⟨agree, e⟩], by wfin [h0],
            by wfin [h1], by wfin [h5]⟩, by wfin [h6]⟩
        · have nstep : ¬ (Plan.words a).take (i + 1) = (Plan.words b).take (i + 1) := fun h => e (step.mp h).2
          wsteps [h0, h1, h6, ra, rb, aa, ab, e, xa, xb]
          exact ⟨⟨trivial, i + 1, by omega, by wfin [], by wfin [nstep], by wfin [h0],
            by wfin [h1], by wfin [h5]⟩, by wfin [h6]⟩
      · -- Every word agreed, so the types are equal.
        have hia : i = (Plan.words a).length := by
          rcases Nat.lt_or_ge i (Plan.words a).length with h | h
          · simp [h] at z
          · omega
        subst hia
        rw [List.take_length, hl, List.take_length] at agree
        have := eq_of_words sa.named sb.named sa.fits sb.fits agree
        subst this
        exact Wp.done ⟨by wfin [h2], rfl⟩
    · rw [if_neg agree] at h2
      -- A word disagreed, so the types differ.
      have differ : (a == b) = false := by
        simp only [beq_eq_false_iff_ne]
        rintro rfl
        exact agree rfl
      refine ⟨_, by wev [h6, h5, h2], fun nz => ?_, fun _ => Wp.done ⟨by wfin [h2, differ], rfl⟩⟩
      simp at nz
  · -- Different lengths, so the types differ.
    have differ : (a == b) = false := by
      simp only [beq_eq_false_iff_ne]
      rintro rfl
      exact hl rfl
    have ne8 : ¬ 8 * (Plan.words a).length = 8 * (Plan.words b).length := by omega
    wsteps [Nat.add_sub_cancel_left, ne8]
    wfin [differ]

/-- A sequence of anything but integers spells no byte array. -/
theorem byteCode_seq {e : Desc} (te : Plan.tag e ≠ 1) (n : Nat) :
    byteCode (.vector e n) = 0 ∧ byteCode (.list e n) = 0 := by
  cases e <;> simp_all [Plan.tag, byteCode, Desc.byteSequence]

/-- A sequence of integers wider than a byte spells no byte array. -/
theorem byteCode_wide {width : Nat} (one : width ≠ 1) (n : Nat) :
    byteCode (.vector (.uint width) n) = 0 ∧ byteCode (.list (.uint width) n) = 0 := by
  constructor <;> (unfold byteCode Desc.byteSequence; split <;> simp_all)

set_option maxHeartbeats 4000000 in
/-- Reading a sound node's byte-array spelling gives its code. -/
theorem bytes_calls {m : Module} {w : World} (hm : Loaded m) {d : Desc} (sd : Sound d) (p sp : Nat) (mem : Memory)
    (hp : PlanAt w mem p (Plan.words d)) (room : Room w sp 0 1) :
    Calls m w "ssz_validate_bytes" sp [UInt64.ofNat p] mem (UInt64.ofNat (byteCode d)) mem := by
  have hb := hp.bound
  have r0 := hp.read0 (words_length_pos _)
  have a0 := hp.readable0 (words_length_pos _)
  rw [words_head] at r0
  refine Calls.body 5 hm.bytes rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [bytesFn]
  cases d with
  | vector e n | list e n =>
    simp only [Plan.tag] at r0
    have small := sd.small
    -- The element's tag sits in the third word, and an integer's width in the fourth.
    have r2 : readLE mem (p + 16) 8 = UInt64.ofNat (Plan.tag e) := by
      rw [hp.read 16 rfl (by simp [Plan.words]; have := words_length_pos e; omega), ← words_head e]
      simp [Plan.words]
    have a2 := hp.readable 16 rfl (by simp [Plan.words]; have := words_length_pos e; omega)
    by_cases te : Plan.tag e = 1
    · obtain ⟨width, rfl⟩ : ∃ width, e = .uint width := by cases e <;> simp [Plan.tag] at te ⊢
      have r3 := hp.read 24 rfl (by simp [Plan.words])
      have a3 := hp.readable 24 rfl (by simp [Plan.words])
      simp [Plan.words] at r3 hb
      by_cases one : width = 1
      · subst one
        wsteps [r0, a0, r2, a2, r3, a3]
        wfin [byteCode, Desc.byteSequence]
      · have lt : width < 2 ^ 64 := small width (by simp [Plan.words])
        wsteps [r0, a0, r2, a2, r3, a3, te, one, lt]
        wfin [byteCode_wide one]
    · have lt : Plan.tag e < 2 ^ 64 := by have := tag_le e; omega
      wsteps [r0, a0, r2, a2, te, lt]
      wfin [byteCode_seq te]
  | _ =>
    simp only [Plan.tag] at r0
    wsteps [r0, a0]
    wfin [byteCode, Desc.byteSequence]

/-! Compatibility. -/

/-- What comparing two sound nodes computes: whether the types are compatible, at the left type's nesting. -/
def CompatOk (m : Module) (w : World) (a : Desc) : Prop :=
  Sound a → ∀ (b : Desc), Sound b → ∀ (pa pb level sp : Nat) (mem : Memory),
    PlanAt w mem pa (Plan.words a) → PlanAt w mem pb (Plan.words b) →
    a.nesting ≤ level → b.nesting ≤ level → Room w sp (2 * level) 3 →
    Calls m w "ssz_validate_compat" sp [UInt64.ofNat pa, UInt64.ofNat pb] mem
      (if compatibleAt a.nesting a b then 1 else 0) mem

/-- The part of the compatibility routine past equality and byte arrays, which walks the two shapes. -/
def compatShape : List Stmt :=
  let a : Var := ⟨0⟩
  let b : Var := ⟨1⟩
  let r : Var := ⟨2⟩
  let t : Var := ⟨5⟩
  [t ::= ld a,
    when (eq t (ld b))
    [ifElse (eq t 0) [r ::= 1]
    [ifElse (le t 5) [r ::= both (ne t 2) (both (ne t 3) (eq (word a 1) (word b 1)))]
    [ifElse (eq t 6) [r ::= 1]
    [ifElse (le t 8) [when (eq (word a 1) (word b 1)) [callInto r "ssz_validate_compat" [a + 16, b + 16]]]
    [ifElse (eq t 9) [callInto r "ssz_validate_compat" [a + 24, b + 24]]
    [ifElse (eq t 10)
      [when (eq (word a 1) (word b 1)) [callInto r "ssz_validate_compat_all" [a + 16, b + 16, word a 1]]]
    [ifElse (eq t 11) [callInto r "ssz_validate_layouts" [a, b]]
    [callInto r "ssz_validate_options_agree" [a + 16 + 8 * word a 1, word a 1, b + 16 + 8 * word b 1, word b 1]]]]]]]]]]

/-- What the walk of the two shapes computes, for two different types neither spelling a byte array. -/
def ShapeOk (m : Module) (w : World) (a : Desc) : Prop :=
  Sound a → ∀ (b : Desc), Sound b → (a == b) = false → byteCode a = 0 → byteCode b = 0 →
    ∀ (pa pb level sp : Nat) (mem : Memory) (env : Env),
    PlanAt w mem pa (Plan.words a) → PlanAt w mem pb (Plan.words b) →
    a.nesting ≤ level → b.nesting ≤ level → Room w sp (2 * level) 2 →
    env 0 = UInt64.ofNat pa → env 1 = UInt64.ofNat pb → env 2 = 0 →
    Wp m w sp (.block compatShape) env mem
      (fun env' mem' => eval w env' mem' compatFn.result = some (if compatibleAt a.nesting a b then 1 else 0) ∧
        mem' = mem)

/-- A budget of one more than none is a successor, for unfolding. -/
theorem nesting_succ (d : Desc) : d.nesting = (d.nesting - 1) + 1 := by
  have := Desc.nesting_pos d; omega

/-- Two types, equal or one spelling a byte array, compare as the Lean check's first two rules say. -/
theorem compatibleAt_head (k : Nat) (a b : Desc) :
    compatibleAt (k + 1) a b =
      if a == b then true
      else if byteCode a ≠ 0 ∨ byteCode b ≠ 0 then a.byteSequence == b.byteSequence
      else compatibleAt (k + 1) a b := by
  by_cases e : (a == b) = true
  · simp only [e, if_true]; rw [compatibleAt.eq_def]; simp [e]
  · simp only [e, Bool.false_eq_true, if_false]
    split
    · rename_i some_
      rw [compatibleAt.eq_def]
      simp only [e, Bool.false_eq_true, if_false]
      unfold byteCode at some_
      cases ha : a.byteSequence <;> cases hb : b.byteSequence <;> simp_all
    · rfl

/-- A type spelling a byte array has a second word. -/
theorem words_two {d : Desc} (h : byteCode d ≠ 0) : 1 < (Plan.words d).length := by
  unfold byteCode at h
  cases e : d.byteSequence with
  | none => simp [e] at h
  | some s =>
    have := words_one_of_byteSequence e
    exact (List.getElem?_eq_some_iff.mp this).1

/-- A word of a sound type's plan, read at its place. -/
theorem Sound.word {d : Desc} (sd : Sound d) {w : World} {mem : Memory} {p : Nat} (hp : PlanAt w mem p (Plan.words d))
    (i : Nat) (hi : i < (Plan.words d).length) :
    readLE mem (p + 8 * i) 8 = UInt64.ofNat (Plan.words d)[i]! ∧ w.access (p + 8 * i) 8 = true ∧
      (Plan.words d)[i]! < 2 ^ 64 := by
  have := hp.read (8 * i) (by omega) (by omega)
  rw [show 8 * i / 8 = i by omega] at this
  exact ⟨this, hp.readable (8 * i) (by omega) (by omega),
    sd.small _ (by rw [getElem!_pos _ i hi]; exact List.getElem_mem hi)⟩

set_option maxHeartbeats 4000000 in
/-- The whole routine computes compatibility once its walk of the shapes does. -/
theorem compat_of_shape {m : Module} {w : World} (hm : Loaded m) (a : Desc) (shape : ShapeOk m w a) :
    CompatOk m w a := by
  intro sa b sb pa pb level sp mem ha hb da db room
  have ba := ha.bound
  have bb := hb.bound
  have e := eq_calls hm sa sb pa pb level (sp - 8 - 8 * 11) mem ha hb da db
    (by simp only [Room] at room ⊢; have := Desc.nesting_pos a; omega)
  have ca := bytes_calls hm sa pa (sp - 8 - 8 * 11) mem ha (by simp only [Room] at room ⊢; omega)
  have cb := bytes_calls hm sb pb (sp - 8 - 8 * 11) mem hb (by simp only [Room] at room ⊢; omega)
  refine Calls.body 11 hm.compat rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [compatFn]
  rw [nesting_succ a, compatibleAt_head]
  wcall e []
  by_cases same : (a == b) = true
  · simp only [same, if_true]
    wsteps []
    wfin []
  have ne : (a == b) = false := by simpa using same
  simp only [ne, Bool.false_eq_true, if_false]
  wsteps []
  wcall ca []
  wcall cb []
  by_cases codes : byteCode a ≠ 0 ∨ byteCode b ≠ 0
  · -- One spells a byte array: the spellings must match, size and all.
    simp only [codes, if_true]
    rw [byteSequence_beq codes]
    have ca' : byteCode a < 2 ^ 64 := by unfold byteCode; split <;> omega
    have cb' : byteCode b < 2 ^ 64 := by unfold byteCode; split <;> omega
    by_cases kk : byteCode a = byteCode b
    · have nz : byteCode a ≠ 0 := by omega
      have two_a := words_two nz
      have two_b := words_two (show byteCode b ≠ 0 by omega)
      obtain ⟨ra, aa, xa⟩ := sa.word ha 1 two_a
      obtain ⟨rb, ab, xb⟩ := sb.word hb 1 two_b
      have nzb : byteCode b ≠ 0 := by omega
      have one : ((Plan.words a)[1]? == (Plan.words b)[1]?) = ((Plan.words a)[1]! == (Plan.words b)[1]!) := by
        rw [getElem?_pos _ 1 two_a, getElem?_pos _ 1 two_b, getElem!_pos _ 1 two_a, getElem!_pos _ 1 two_b]
        simp
      simp only [Nat.mul_one] at ra aa rb ab
      wsteps [nz, nzb, kk, ra, aa, rb, ab, xa, xb, ca', cb']
      wfin [kk, one]
    · rcases codes with c | c <;> wsteps [c, kk, ca', cb'] <;> wfin [kk] <;> exact fun h => absurd h kk
  · simp only [codes, if_false]
    rw [← nesting_succ a]
    simp only [not_or, Decidable.not_not] at codes
    wsteps [codes.1, codes.2]
    exact shape sa b sb ne codes.1 codes.2 pa pb level _ mem _ ha hb da db
      (by simp only [Room] at room ⊢; omega) (by wfin []) (by wfin []) (by wfin [])

/-- Field lists compare pair by pair, so two lists split at one length compare as their two parts do. -/
theorem fieldsCompatible_append (B : Nat) (l2 r2 : List Desc) : ∀ l1 r1 : List Desc, l1.length = r1.length →
    fieldsCompatible B (l1 ++ l2) (r1 ++ r2) = (fieldsCompatible B l1 r1 && fieldsCompatible B l2 r2)
  | [], [], _ => by simp [fieldsCompatible]
  | x :: l1, y :: r1, h => by
    simp only [List.cons_append, fieldsCompatible, fieldsCompatible_append B l2 r2 l1 r1 (by simpa using h),
      Bool.and_assoc]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

set_option maxHeartbeats 4000000 in
/-- Comparing two counts of sound nodes pair by pair answers whether the field lists are compatible. -/
theorem compatAll_calls {m : Module} {w : World} (hm : Loaded m) (fs gs : List Desc) (ih : ∀ f ∈ fs, CompatOk m w f)
    (sf : ∀ f ∈ fs, Sound f) (sg : ∀ g ∈ gs, Sound g) (len : fs.length = gs.length) (B : Nat)
    (deep : Desc.deepestNesting fs ≤ B) (pa pb level sp : Nat) (mem : Memory)
    (ha : PlanAt w mem pa (Plan.wordsAll fs)) (hb : PlanAt w mem pb (Plan.wordsAll gs))
    (df : Desc.deepestNesting fs ≤ level) (dg : Desc.deepestNesting gs ≤ level) (room : Room w sp (2 * level + 1) 3) :
    Calls m w "ssz_validate_compat_all" sp [UInt64.ofNat pa, UInt64.ofNat pb, UInt64.ofNat fs.length] mem
      (if fieldsCompatible B fs gs then 1 else 0) mem := by
  have ba := ha.bound
  have bb := hb.bound
  have la := length_le_wordsAll fs
  have lb := length_le_wordsAll gs
  refine Calls.body 7 hm.compatAll rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [compatAllFn]
  wsteps []
  -- After j pairs, both nodes stand past them and the result says whether the first j pairs are compatible.
  refine Wp.loop (wp_loop (fun env mem' => mem' = mem ∧ ∃ j, j ≤ fs.length ∧
      env 0 = UInt64.ofNat (pa + 8 * (Plan.wordsAll (fs.take j)).length) ∧
      env 1 = UInt64.ofNat (pb + 8 * (Plan.wordsAll (gs.take j)).length) ∧
      env 2 = UInt64.ofNat (fs.length - j) ∧
      env 3 = (if fieldsCompatible B (fs.take j) (gs.take j) then 1 else 0))
    (fun env _ => (env 2).toNat)
    ⟨rfl, 0, Nat.zero_le _, by wfin [Plan.wordsAll], by wfin [Plan.wordsAll], by wfin [], by wfin [fieldsCompatible]⟩
    ?_)
  rintro env mem' ⟨hmem, j, hj, h0, h1, h2, h3⟩
  subst mem'
  have hja := wordsAll_take_le fs j
  have hjb := wordsAll_take_le gs j
  by_cases ok : fieldsCompatible B (fs.take j) (gs.take j) = true
  · rw [if_pos ok] at h3
    refine ⟨_, by wev [h2, h3], fun nz => ?_, fun z => ?_⟩
    · have hjf : j < fs.length := by
        rcases Nat.lt_or_ge j fs.length with h | h
        · exact h
        · simp [show fs.length - j = 0 by omega] at nz
      have hjg : j < gs.length := by omega
      obtain ⟨_, hpa, _⟩ := fieldAt ha j hjf
      obtain ⟨_, hpb, _⟩ := fieldAt hb j hjg
      have mf := List.getElem_mem hjf
      have mg := List.getElem_mem hjg
      have nf := nesting_le_deepest fs fs[j] mf
      have ng := nesting_le_deepest gs gs[j] mg
      have c := ih fs[j] mf (sf _ mf) gs[j] (sg _ mg) _ _ level (sp - 8 - 8 * 7) mem hpa hpb (by omega) (by omega)
        (by simp only [Room] at room ⊢; omega)
      have ka := skip_calls hm fs[j] (sf _ mf).fits _ (sp - 8 - 8 * 7) mem hpa
        (by simp only [Room] at room ⊢; generalize fs[j].nesting = x at nf ⊢; omega)
      have kb := skip_calls hm gs[j] (sg _ mg).fits _ (sp - 8 - 8 * 7) mem hpb
        (by simp only [Room] at room ⊢; generalize gs[j].nesting = x at ng ⊢; omega)
      -- The pair's own budget answers as the shared one does.
      rw [compatibleAt_stable _ B _ _ (Nat.le_refl _) (by omega)] at c
      have step : fieldsCompatible B (fs.take (j + 1)) (gs.take (j + 1)) = compatibleAt B fs[j] gs[j] := by
        rw [take_succ_append fs j hjf, take_succ_append gs j hjg,
          fieldsCompatible_append _ _ _ _ _ (by simp; omega), ok]
        simp [fieldsCompatible]
      have hl2 : fs.length - j ≠ 0 := by omega
      wcall c [h0, h1]
      wcall ka [h0]
      wcall kb [h1]
      wsteps [h2, hl2]
      refine ⟨⟨trivial, j + 1, by omega, ?_, ?_, by wfin [h2], by wfin [step]⟩, by wfin [h2]⟩
      · wfin [wordsAll_take_succ fs j hjf]
      · wfin [wordsAll_take_succ gs j hjg]
    · have hjk : j = fs.length := by
        rcases Nat.lt_or_ge j fs.length with h | h
        · simp [show fs.length - j ≠ 0 by omega] at z
        · omega
      subst hjk
      rw [List.take_length, len, List.take_length] at ok
      exact Wp.done ⟨by wfin [h3, ok], rfl⟩
  · rw [if_neg ok] at h3
    -- Some pair among the first j clashes, so the whole lists do.
    have bad : fieldsCompatible B fs gs = false := by
      rw [← List.take_append_drop j fs, ← List.take_append_drop j gs,
        fieldsCompatible_append _ _ _ _ _ (by simp; omega)]
      simp [ok]
    refine ⟨_, by wev [h2, h3], fun nz => ?_, fun _ => Wp.done ⟨by wfin [h3, bad], rfl⟩⟩
    simp at nz

/-- One option checked against two parts of a list is checked against each. -/
theorem optionAgainstAll_append (B : Nat) (x : Desc) (l2 : List Desc) : ∀ l1 : List Desc,
    optionAgainstAll B x (l1 ++ l2) = (optionAgainstAll B x l1 && optionAgainstAll B x l2)
  | [] => by simp [optionAgainstAll]
  | y :: l1 => by simp only [List.cons_append, optionAgainstAll, optionAgainstAll_append B x l2 l1, Bool.and_assoc]

/-- Two parts of a union's options agree with another's when each part does. -/
theorem unionOptionsAgree_append (B : Nat) (r : List Desc) (l2 : List Desc) : ∀ l1 : List Desc,
    unionOptionsAgree B (l1 ++ l2) r = (unionOptionsAgree B l1 r && unionOptionsAgree B l2 r)
  | [] => by simp [unionOptionsAgree]
  | y :: l1 => by
    simp only [List.cons_append, unionOptionsAgree, unionOptionsAgree_append B r l2 l1, Bool.and_assoc]

set_option maxHeartbeats 8000000 in
/-- Comparing every option of one union with every option of another answers whether the options agree. -/
theorem optionsAgree_calls {m : Module} {w : World} (hm : Loaded m) (os qs : List Desc)
    (ih : ∀ f ∈ os, CompatOk m w f) (so : ∀ f ∈ os, Sound f) (sq : ∀ g ∈ qs, Sound g) (B : Nat)
    (deep : Desc.deepestNesting os ≤ B) (pa pb level sp : Nat) (mem : Memory)
    (ha : PlanAt w mem pa (Plan.wordsAll os)) (hb : PlanAt w mem pb (Plan.wordsAll qs))
    (df : Desc.deepestNesting os ≤ level) (dg : Desc.deepestNesting qs ≤ level) (room : Room w sp (2 * level + 1) 3) :
    Calls m w "ssz_validate_options_agree" sp
      [UInt64.ofNat pa, UInt64.ofNat os.length, UInt64.ofNat pb, UInt64.ofNat qs.length] mem
      (if unionOptionsAgree B os qs then 1 else 0) mem := by
  have ba := ha.bound
  have bb := hb.bound
  have la := length_le_wordsAll os
  have lb := length_le_wordsAll qs
  refine Calls.body 9 hm.optionsAgree rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [optionsAgreeFn]
  wsteps []
  -- After i options of the first union, the result says whether they agree with every option of the second.
  refine Wp.loop (wp_loop (fun env mem' => mem' = mem ∧ ∃ i, i ≤ os.length ∧
      env 0 = UInt64.ofNat (pa + 8 * (Plan.wordsAll (os.take i)).length) ∧
      env 1 = UInt64.ofNat (os.length - i) ∧ env 2 = UInt64.ofNat pb ∧ env 3 = UInt64.ofNat qs.length ∧
      env 4 = (if unionOptionsAgree B (os.take i) qs then 1 else 0))
    (fun env _ => (env 1).toNat)
    ⟨rfl, 0, Nat.zero_le _, by wfin [Plan.wordsAll], by wfin [], by wfin [], by wfin [], by wfin [unionOptionsAgree]⟩
    ?_)
  rintro env mem' ⟨hmem, i, hi, h0, h1, h2, h3, h4⟩
  subst mem'
  have hia := wordsAll_take_le os i
  by_cases ok : unionOptionsAgree B (os.take i) qs = true
  · rw [if_pos ok] at h4
    refine ⟨_, by wev [h1, h4], fun nz => ?_, fun z => ?_⟩
    · have hio : i < os.length := by
        rcases Nat.lt_or_ge i os.length with h | h
        · exact h
        · simp [show os.length - i = 0 by omega] at nz
      obtain ⟨_, hpa, _⟩ := fieldAt ha i hio
      have mo := List.getElem_mem hio
      have no := nesting_le_deepest os os[i] mo
      have ka := skip_calls hm os[i] (so _ mo).fits _ (sp - 8 - 8 * 9) mem hpa
        (by simp only [Room] at room ⊢; generalize os[i].nesting = x at no ⊢; omega)
      have hl1 : os.length - i ≠ 0 := by omega
      wsteps [h1, h2, h3, h4, hl1]
      -- After k options of the second union, the result says whether this option fits each of them.
      refine Wp.loop (wp_loop (fun env' mem' => mem' = mem ∧ ∃ k, k ≤ qs.length ∧
          env' 5 = UInt64.ofNat (pb + 8 * (Plan.wordsAll (qs.take k)).length) ∧
          env' 6 = UInt64.ofNat (qs.length - k) ∧
          env' 4 = (if optionAgainstAll B os[i] (qs.take k) then 1 else 0) ∧
          env' 0 = UInt64.ofNat (pa + 8 * (Plan.wordsAll (os.take i)).length) ∧
          env' 1 = UInt64.ofNat (os.length - i) ∧ env' 2 = UInt64.ofNat pb ∧ env' 3 = UInt64.ofNat qs.length)
        (fun env' _ => (env' 6).toNat)
        ⟨rfl, 0, Nat.zero_le _, by wfin [Plan.wordsAll], by wfin [h3], by wfin [optionAgainstAll], by wfin [h0],
          by wfin [h1], by wfin [h2], by wfin [h3]⟩ ?_)
      rintro env' mem' ⟨hmem', k, hk, g5, g6, g4, g0, g1, g2, g3⟩
      subst mem'
      have hkb := wordsAll_take_le qs k
      by_cases fits : optionAgainstAll B os[i] (qs.take k) = true
      · rw [if_pos fits] at g4
        refine ⟨_, by wev [g6, g4], fun nz' => ?_, fun z' => ?_⟩
        · have hkq : k < qs.length := by
            rcases Nat.lt_or_ge k qs.length with h | h
            · exact h
            · simp [show qs.length - k = 0 by omega] at nz'
          obtain ⟨_, hpb, _⟩ := fieldAt hb k hkq
          have mq := List.getElem_mem hkq
          have nq := nesting_le_deepest qs qs[k] mq
          have c := ih os[i] mo (so _ mo) qs[k] (sq _ mq) _ _ level (sp - 8 - 8 * 9) mem hpa hpb (by omega) (by omega)
            (by simp only [Room] at room ⊢; omega)
          have kb := skip_calls hm qs[k] (sq _ mq).fits _ (sp - 8 - 8 * 9) mem hpb
            (by simp only [Room] at room ⊢; generalize qs[k].nesting = x at nq ⊢; omega)
          rw [compatibleAt_stable _ B _ _ (Nat.le_refl _) (by omega)] at c
          have step : optionAgainstAll B os[i] (qs.take (k + 1)) = compatibleAt B os[i] qs[k] := by
            rw [take_succ_append qs k hkq, optionAgainstAll_append, fits]
            simp [optionAgainstAll]
          have hl6 : qs.length - k ≠ 0 := by omega
          wcall c [g0, g5]
          wcall kb [g5]
          wsteps [g6, hl6]
          refine ⟨⟨trivial, k + 1, by omega, ?_, by wfin [g6], by wfin [step], by wfin [g0], by wfin [g1],
            by wfin [g2], by wfin [g3]⟩, by wfin [g6]⟩
          wfin [wordsAll_take_succ qs k hkq]
        · -- The option fits every option of the second union.
          have hkq : k = qs.length := by
            rcases Nat.lt_or_ge k qs.length with h | h
            · simp [show qs.length - k ≠ 0 by omega] at z'
            · omega
          subst hkq
          rw [List.take_length] at fits
          have step : unionOptionsAgree B (os.take (i + 1)) qs = true := by
            rw [take_succ_append os i hio, unionOptionsAgree_append, ok]
            simp [unionOptionsAgree, fits]
          wcall ka [g0]
          wsteps [g1, hl1]
          refine ⟨⟨trivial, i + 1, by omega, ?_, by wfin [g1], by wfin [g2], by wfin [g3], by wfin [g4, step]⟩,
            by wfin [g1, h1]⟩
          wfin [wordsAll_take_succ os i hio]
      · rw [if_neg fits] at g4
        -- The option clashes with one of the second union's, so the options do not agree.
        have bad0 : optionAgainstAll B os[i] qs = false := by
          have e := optionAgainstAll_append B os[i] (qs.drop k) (qs.take k)
          rw [List.take_append_drop] at e
          simp [e, fits]
        have bad : unionOptionsAgree B (os.take (i + 1)) qs = false := by
          rw [take_succ_append os i hio, unionOptionsAgree_append, ok]
          simp [unionOptionsAgree, bad0]
        refine ⟨_, by wev [g6, g4], fun nz' => ?_, fun _ => ?_⟩
        · simp at nz'
        · wcall ka [g0]
          wsteps [g1, hl1]
          refine ⟨⟨trivial, i + 1, by omega, ?_, by wfin [g1], by wfin [g2], by wfin [g3], by wfin [g4, bad]⟩,
            by wfin [g1, h1]⟩
          wfin [wordsAll_take_succ os i hio]
    · have hio : i = os.length := by
        rcases Nat.lt_or_ge i os.length with h | h
        · simp [show os.length - i ≠ 0 by omega] at z
        · omega
      subst hio
      rw [List.take_length] at ok
      exact Wp.done ⟨by wfin [h4, ok], rfl⟩
  · rw [if_neg ok] at h4
    -- Some option among the first i clashes, so the unions' options do not agree.
    have bad : unionOptionsAgree B os qs = false := by
      rw [← List.take_append_drop i os, unionOptionsAgree_append]
      simp [ok]
    refine ⟨_, by wev [h1, h4], fun nz => ?_, fun _ => Wp.done ⟨by wfin [h4, bad], rfl⟩⟩
    simp at nz

/-! Layouts. -/

/-- One more position counts its bit. -/
theorem setBefore_succ (active : List Bool) (i : Nat) (hi : i < active.length) :
    setBefore active (i + 1) = setBefore active i + (if active[i]! then 1 else 0) := by
  unfold setBefore
  rw [List.take_add_one, List.getElem?_eq_getElem hi, getElem!_pos active i hi]
  cases active[i] <;> simp

/-- A set position has fewer set bits before it than the layout has. -/
theorem setBefore_lt (active : List Bool) (i : Nat) (hi : i < active.length) (set : active[i]! = true) :
    setBefore active i < active.countP (· == true) := by
  have := setBefore_succ active i hi
  have le : setBefore active (i + 1) ≤ active.countP (· == true) := (List.take_sublist _ _).countP_le
  simp only [set, if_true] at this
  omega

/-- What a sound progressive container's plan holds: its width, its bits, then its fields. -/
theorem progressive_at {active : List Bool} {names : List String} {fs : List Desc}
    (sd : Sound (.progressiveContainer active names fs)) {w : World} {mem : Memory} {p : Nat}
    (hp : PlanAt w mem p (Plan.words (.progressiveContainer active names fs))) :
    readLE mem (p + 8) 8 = UInt64.ofNat active.length ∧ w.access (p + 8) 8 = true ∧ active.length ≤ 256 ∧
      (∀ i, i < active.length → readLE mem (p + 16 + 8 * i) 8 = UInt64.ofNat (if active[i]! then 1 else 0) ∧
        w.access (p + 16 + 8 * i) 8 = true) ∧
      PlanAt w mem (p + 24 + 8 * active.length) (Plan.wordsAll fs) ∧ fs.length = active.countP (· == true) := by
  have e : Plan.words (.progressiveContainer active names fs) =
      ([11, active.length] ++ active.map (fun b => if b then 1 else 0) ++ [fs.length]) ++ Plan.wordsAll fs := by
    simp [Plan.words]
  have hlen : (Plan.words (.progressiveContainer active names fs)).length =
      active.length + 3 + (Plan.wordsAll fs).length := by
    rw [e]; simp; omega
  obtain ⟨_, _, wide, _, count, _, _, _⟩ := (wellFormed_progressiveContainer_iff active names fs).mp sd.wf
  refine ⟨?_, ?_, by simpa [maxActiveFields] using wide, fun i hi => ⟨?_, ?_⟩, ?_, count.symm⟩
  · have := hp.read 8 rfl (by rw [hlen]; omega)
    rw [this, e]; simp
  · exact hp.readable 8 rfl (by rw [hlen]; omega)
  · have := hp.read (16 + 8 * i) (by omega) (by rw [hlen]; omega)
    rw [Nat.add_assoc, this, show (16 + 8 * i) / 8 = i + 2 by omega, e]
    simp only [getElem!_def, List.append_assoc]
    rw [List.getElem?_append_right (by simp), List.getElem?_append_left (by simp; omega)]
    simp [show i + 2 - 2 = i by omega, hi]
  · have := hp.readable (16 + 8 * i) (by omega) (by rw [hlen]; omega)
    rwa [← Nat.add_assoc] at this
  · have hp' := hp; rw [e] at hp'
    refine hp'.right.at_eq ?_
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]
    omega

/-- Whether every position below a bound that both layouts set holds compatible fields. -/
def sharedUpTo (B : Nat) (la lb : List Bool) (fa fb : List Desc) (i : Nat) : Bool :=
  (List.range i).all fun k => !(la[k]! && lb[k]!) || sharedAgree B la lb fa fb k

/-- Two layouts named by position agree exactly when the positions below both widths do. -/
theorem layoutsAgree_upTo (B : Nat) (la lb : List Bool) (fa fb : List Desc) :
    layoutsAgree B la (Plan.layoutNames la) fa lb (Plan.layoutNames lb) fb =
      sharedUpTo B la lb fa fb (min la.length lb.length) := by
  apply Bool.eq_iff_iff.mpr
  rw [layoutsAgree_named]
  simp only [sharedUpTo, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff]
  constructor
  · intro all k hk
    by_cases ha : la[k]! = true
    · by_cases hb : lb[k]! = true
      · right
        refine all k ?_ ?_
        · rw [List.getElem?_eq_getElem (by omega)]; rw [getElem!_pos la k (by omega)] at ha; simp [ha]
        · rw [List.getElem?_eq_getElem (by omega)]; rw [getElem!_pos lb k (by omega)] at hb; simp [hb]
      · left; right; simpa using hb
    · left; left; simpa using ha
  · intro all k ha hb
    have ka := (List.getElem?_eq_some_iff.mp ha).1
    have kb := (List.getElem?_eq_some_iff.mp hb).1
    rcases all k (by omega) with (h | h) | h
    · rw [getElem!_pos la k ka] at h; simp [List.getElem?_eq_getElem ka] at ha; simp [ha] at h
    · rw [getElem!_pos lb k kb] at h; simp [List.getElem?_eq_getElem kb] at hb; simp [hb] at h
    · exact h

/-- The positions below one more. -/
theorem sharedUpTo_succ (B : Nat) (la lb : List Bool) (fa fb : List Desc) (i : Nat) :
    sharedUpTo B la lb fa fb (i + 1) =
      (sharedUpTo B la lb fa fb i && (!(la[i]! && lb[i]!) || sharedAgree B la lb fa fb i)) := by
  simp [sharedUpTo, List.range_succ, List.all_append]

set_option maxHeartbeats 16000000 in
/-- Walking two sound progressive containers' layouts answers whether they agree. -/
theorem layouts_calls {m : Module} {w : World} (hm : Loaded m) (la lb : List Bool) (fa fb : List Desc)
    (ih : ∀ f ∈ fa, CompatOk m w f)
    (sa : Sound (.progressiveContainer la (Plan.layoutNames la) fa))
    (sb : Sound (.progressiveContainer lb (Plan.layoutNames lb) fb)) (B : Nat)
    (deep : Desc.deepestNesting fa ≤ B) (pa pb level sp : Nat) (mem : Memory)
    (ha : PlanAt w mem pa (Plan.words (.progressiveContainer la (Plan.layoutNames la) fa)))
    (hb : PlanAt w mem pb (Plan.words (.progressiveContainer lb (Plan.layoutNames lb) fb)))
    (df : Desc.deepestNesting fa ≤ level) (dg : Desc.deepestNesting fb ≤ level) (room : Room w sp (2 * level + 1) 3) :
    Calls m w "ssz_validate_layouts" sp [UInt64.ofNat pa, UInt64.ofNat pb] mem
      (if layoutsAgree B la (Plan.layoutNames la) fa lb (Plan.layoutNames lb) fb then 1 else 0) mem := by
  have ba := ha.bound
  have bb := hb.bound
  obtain ⟨ra, aa, wa, bitA, hfa, ca⟩ := progressive_at sa ha
  obtain ⟨rb, ab, wb, bitB, hfb, cb⟩ := progressive_at sb hb
  have fitA : allFitNative fa = true := by have := sa.fits; simp only [fitsNative, Bool.and_eq_true] at this; exact this.1.1
  have fitB : allFitNative fb = true := by have := sb.fits; simp only [fitsNative, Bool.and_eq_true] at this; exact this.1.1
  have wfA : Desc.allWellFormed fa = .ok () := ((wellFormed_progressiveContainer_iff _ _ _).mp sa.wf).2.2.2.2.2.2.2
  have wfB : Desc.allWellFormed fb = .ok () := ((wellFormed_progressiveContainer_iff _ _ _).mp sb.wf).2.2.2.2.2.2.2
  have nmA : namedAll fa = true := by have := sa.named; simp only [named, Bool.and_eq_true] at this; exact this.2
  have nmB : namedAll fb = true := by have := sb.named; simp only [named, Bool.and_eq_true] at this; exact this.2
  have soA : ∀ f ∈ fa, Sound f := fun f hf =>
    ⟨allWellFormed_mem fa wfA f hf, namedAll_mem fa nmA f hf, allFitNative_mem fa fitA f hf⟩
  have soB : ∀ f ∈ fb, Sound f := fun f hf =>
    ⟨allWellFormed_mem fb wfB f hf, namedAll_mem fb nmB f hf, allFitNative_mem fb fitB f hf⟩
  have lwa := length_le_wordsAll fa
  have lwb := length_le_wordsAll fb
  have bfa := hfa.bound
  have bfb := hfb.bound
  refine Calls.body 11 hm.layouts rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [layoutsFn]
  rw [layoutsAgree_upTo]
  wsteps []
  -- After i positions, the ordinals count the set bits before it, and the result says whether the shared positions
  -- so far hold compatible fields.
  refine Wp.loop (wp_loop (fun env mem' => mem' = mem ∧ ∃ i, i ≤ la.length ∧ i ≤ lb.length ∧
      env 3 = UInt64.ofNat i ∧ env 4 = UInt64.ofNat (setBefore la i) ∧ env 5 = UInt64.ofNat (setBefore lb i) ∧
      env 2 = (if sharedUpTo B la lb fa fb i then 1 else 0) ∧ env 0 = UInt64.ofNat pa ∧ env 1 = UInt64.ofNat pb)
    (fun env _ => la.length - (env 3).toNat)
    ⟨rfl, 0, Nat.zero_le _, Nat.zero_le _, by wfin [], by wfin [setBefore], by wfin [setBefore],
      by wfin [sharedUpTo], by wfin [], by wfin []⟩ ?_)
  rintro env mem' ⟨hmem, i, hia, hib, h3, h4, h5, h2, h0, h1⟩
  subst mem'
  have sa_le : setBefore la i ≤ i := by
    have := List.countP_le_length (p := (· == true)) (l := la.take i); simp only [setBefore]; simp at this ⊢; omega
  have sb_le : setBefore lb i ≤ i := by
    have := List.countP_le_length (p := (· == true)) (l := lb.take i); simp only [setBefore]; simp at this ⊢; omega
  by_cases ok : sharedUpTo B la lb fa fb i = true
  · rw [if_pos ok] at h2
    refine ⟨_, by wev [h3, h0, h1, ra, aa, rb, ab, h2], fun nz => ?_, fun z => ?_⟩
    · have hi : i < la.length ∧ i < lb.length := by
        by_cases x : i < la.length
        · by_cases y : i < lb.length
          · exact ⟨x, y⟩
          · simp [y] at nz
        · by_cases y : i < lb.length <;> simp [x, y] at nz
      obtain ⟨rai, aai⟩ := bitA i hi.1
      obtain ⟨rbi, abi⟩ := bitB i hi.2
      have sa1 := setBefore_succ la i hi.1
      have sb1 := setBefore_succ lb i hi.2
      have step := sharedUpTo_succ B la lb fa fb i
      rw [ok, Bool.true_and] at step
      cases ea : la[i]! <;> cases eb : lb[i]!
      all_goals simp only [ea, eb, Bool.false_and, Bool.and_false, Bool.not_false, Bool.true_or, Bool.not_true,
        Bool.false_or, Bool.true_and, if_true] at rai rbi sa1 sb1 step
      · wsteps [h0, h1, h3, h4, h5, rai, aai, rbi, abi]
        exact ⟨⟨trivial, i + 1, by omega, by omega, by wfin [], by wfin [sa1], by wfin [sb1], by wfin [step],
          by wfin [h0], by wfin [h1]⟩, by wfin [h3]⟩
      · wsteps [h0, h1, h3, h4, h5, rai, aai, rbi, abi]
        exact ⟨⟨trivial, i + 1, by omega, by omega, by wfin [], by wfin [sa1], by wfin [sb1, h5], by wfin [step],
          by wfin [h0], by wfin [h1]⟩, by wfin [h3]⟩
      · wsteps [h0, h1, h3, h4, h5, rai, aai, rbi, abi]
        exact ⟨⟨trivial, i + 1, by omega, by omega, by wfin [], by wfin [sa1, h4], by wfin [sb1], by wfin [step],
          by wfin [h0], by wfin [h1]⟩, by wfin [h3]⟩
      · -- Both layouts set this position: compare the fields placed there.
        have oa := setBefore_lt la i hi.1 ea
        have ob := setBefore_lt lb i hi.2 eb
        rw [← ca] at oa
        rw [← cb] at ob
        obtain ⟨_, hpa, _⟩ := fieldAt hfa _ oa
        obtain ⟨_, hpb, _⟩ := fieldAt hfb _ ob
        have mf := List.getElem_mem oa
        have mg := List.getElem_mem ob
        have nf := nesting_le_deepest fa _ mf
        have ng := nesting_le_deepest fb _ mg
        have ka := skipAll_calls hm fa (fun f _ => skip_calls hm f) fitA (setBefore la i) _ (sp - 8 - 8 * 11) mem
          (by omega) hfa (by simp only [Room] at room ⊢; omega)
        have kb := skipAll_calls hm fb (fun f _ => skip_calls hm f) fitB (setBefore lb i) _ (sp - 8 - 8 * 11) mem
          (by omega) hfb (by simp only [Room] at room ⊢; omega)
        have c := ih _ mf (soA _ mf) _ (soB _ mg) _ _ level (sp - 8 - 8 * 11) mem hpa hpb (by omega) (by omega)
          (by simp only [Room] at room ⊢; omega)
        rw [compatibleAt_stable _ B _ _ (Nat.le_refl _) (by omega)] at c
        have shared : sharedAgree B la lb fa fb i = compatibleAt B fa[setBefore la i] fb[setBefore lb i] := by
          simp [sharedAgree, List.getElem?_eq_getElem oa, List.getElem?_eq_getElem ob]
        rw [shared] at step
        wsteps [h0, h1, h3, h4, h5, rai, aai, rbi, abi, ra, aa, rb, ab]
        wcall ka [h0, h4, ra, aa]
        wcall kb [h1, h5, rb, ab]
        wcall c []
        wsteps [h0, h1, h3, rai, aai, rbi, abi]
        exact ⟨⟨trivial, i + 1, by omega, by omega, by wfin [], by wfin [sa1, h4], by wfin [sb1, h5], by wfin [step],
          by wfin [h0], by wfin [h1]⟩, by wfin [h3]⟩
    · -- One layout ends here, and no position past it is set in both.
      have hi : i = min la.length lb.length := by
        by_cases x : i < la.length <;> by_cases y : i < lb.length
        · simp [x, y] at z
        all_goals omega
      subst hi
      exact Wp.done ⟨by wfin [h2, ok], rfl⟩
  · rw [if_neg ok] at h2
    -- A shared position already clashed, and positions further on change nothing.
    have bad : sharedUpTo B la lb fa fb (min la.length lb.length) = false := by
      have e : min la.length lb.length = i + (min la.length lb.length - i) := by omega
      rw [e]
      simp only [Bool.not_eq_true] at ok
      generalize min la.length lb.length - i = d
      induction d with
      | zero => exact ok
      | succ d ihd => rw [← Nat.add_assoc, sharedUpTo_succ, ihd, Bool.false_and]
    refine ⟨_, by wev [h3, h0, h1, ra, aa, rb, ab, h2], fun nz => ?_, fun _ => Wp.done ⟨by wfin [h2, bad], rfl⟩⟩
    simp at nz

/-! The walk of the two shapes. -/

/-- The routine's result is its third variable. -/
theorem compatFn_result : compatFn.result = .var 2 := rfl

/-- A type coded as spelling no byte array spells none. -/
theorem byteSequence_none {d : Desc} (h : byteCode d = 0) : d.byteSequence = none := by
  unfold byteCode at h
  split at h <;> simp_all

/-- Two different types of different kinds, neither spelling a byte array, are not compatible. -/
theorem compatibleAt_tags (k : Nat) (a b : Desc) (ne : (a == b) = false) (ca : byteCode a = 0) (cb : byteCode b = 0)
    (t : Plan.tag b ≠ Plan.tag a) : compatibleAt (k + 1) a b = false := by
  rw [compatibleAt.eq_def]
  simp only [ne, Bool.false_eq_true, if_false, byteSequence_none ca, byteSequence_none cb]
  cases a <;> cases b <;> simp_all [Plan.tag]

set_option maxHeartbeats 4000000 in
/-- The walk of the two shapes refuses two kinds that differ; only the same kind is left to prove. -/
theorem shape_of_same {m : Module} {w : World} (a : Desc)
    (same : Sound a → ∀ (b : Desc), Sound b → (a == b) = false → byteCode a = 0 → byteCode b = 0 →
      Plan.tag b = Plan.tag a → ∀ (pa pb level sp : Nat) (mem : Memory) (env : Env),
      PlanAt w mem pa (Plan.words a) → PlanAt w mem pb (Plan.words b) →
      a.nesting ≤ level → b.nesting ≤ level → Room w sp (2 * level) 2 →
      env 0 = UInt64.ofNat pa → env 1 = UInt64.ofNat pb → env 2 = 0 →
      Wp m w sp (.block compatShape) env mem
        (fun env' mem' => eval w env' mem' compatFn.result = some (if compatibleAt a.nesting a b then 1 else 0) ∧
          mem' = mem)) :
    ShapeOk m w a := by
  intro sa b sb ne ca cb pa pb level sp mem env ha hb da db room h0 h1 h2
  by_cases tb : Plan.tag b = Plan.tag a
  · exact same sa b sb ne ca cb tb pa pb level sp mem env ha hb da db room h0 h1 h2
  have r0 := ha.read0 (words_length_pos _)
  have a0 := ha.readable0 (words_length_pos _)
  have s0 := hb.read0 (words_length_pos _)
  have b0 := hb.readable0 (words_length_pos _)
  rw [words_head] at r0 s0
  have ta := tag_le a
  have tb' := tag_le b
  simp only [compatShape, compatFn_result]
  rw [nesting_succ a, compatibleAt_tags _ a b ne ca cb tb]
  have tne : ¬ Plan.tag a = Plan.tag b := fun e => tb e.symm
  have ba := ha.bound
  have bb := hb.bound
  wsteps [h0, h1, r0, a0, s0, b0, tne]
  wfin [h2]

/-- Each type of a list of legal, named, fitting types is sound. -/
theorem sound_mem {fs : List Desc} (wf : Desc.allWellFormed fs = .ok ()) (nm : namedAll fs = true)
    (fit : allFitNative fs = true) : ∀ f ∈ fs, Sound f :=
  fun f hf => ⟨allWellFormed_mem fs wf f hf, namedAll_mem fs nm f hf, allFitNative_mem fs fit f hf⟩

set_option hygiene false in
/-- Opens the walk of two shapes of one kind: the second node is of the first one's kind, both tags read. -/
macro "shape_open" : tactic => `(tactic| (
  refine compat_of_shape hm _ (shape_of_same _ ?_)
  intro sa b sb ne ca cb tb pa pb level sp mem env ha hb da db room h0 h1 h2
  have ba := ha.bound
  have bb := hb.bound
  have r0 := ha.read0 (words_length_pos _)
  have a0 := ha.readable0 (words_length_pos _)
  have s0 := hb.read0 (words_length_pos _)
  have b0 := hb.readable0 (words_length_pos _)
  rw [words_head] at r0 s0
  simp only [compatShape, compatFn_result]
  generalize hspec : compatibleAt _ _ b = spec
  rw [nesting_succ, compatibleAt.eq_def] at hspec
  simp only [ne, Bool.false_eq_true, if_false, byteSequence_none ca, byteSequence_none cb] at hspec
  cases b <;> (try simp [Plan.tag] at tb)
  all_goals simp only [Plan.tag] at r0 s0
  all_goals simp only [Desc.nesting, Nat.add_sub_cancel] at hspec
  all_goals subst hspec))

set_option maxHeartbeats 16000000 in
/-- Comparing two sound nodes answers whether the types are compatible, at the left type's nesting. -/
theorem compat_calls {m : Module} {w : World} (hm : Loaded m) (d : Desc) : CompatOk m w d := by
  induction d using Desc.rec (motive_2 := fun fs => ∀ f ∈ fs, CompatOk m w f) with
  | nil => rename_i h; simp at h
  | cons f fs ihf ihfs =>
    rename_i g h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ihf
    · exact ihfs g h
  | bool =>
    shape_open
    simp at ne
  | byteVector n | byteList n =>
    refine compat_of_shape hm _ (shape_of_same _ ?_)
    intro _ _ _ _ ca
    simp [byteCode, Desc.byteSequence] at ca
  | uint x | bitVector x | bitList x =>
    shape_open
    rename_i y
    obtain ⟨r1, a1, x1⟩ := sa.word ha 1 (by simp [Plan.words])
    obtain ⟨s1, b1, y1⟩ := sb.word hb 1 (by simp [Plan.words])
    simp [Plan.words] at r1 s1 x1 y1
    have xy : ¬ x = y := by simpa using ne
    wsteps [h0, h1, r0, a0, s0, b0, r1, a1, s1, b1, xy, x1, y1]
    wfin [xy]
  | progressiveBitList l =>
    shape_open
    wsteps [h0, h1, r0, a0, s0, b0]
    wfin []
  | vector e n ih | list e n ih =>
    shape_open
    rename_i e' n'
    have fa := sa.fits
    have fb := sb.fits
    simp only [fitsNative, Bool.and_eq_true] at fa fb
    have se : Sound e := ⟨by first | exact wellFormed_vector_element sa.wf | simpa [Desc.wellFormed] using sa.wf,
      by simpa [named] using sa.named, by first | exact fa.1.1 | exact fa.1⟩
    have se' : Sound e' := ⟨by first | exact wellFormed_vector_element sb.wf | simpa [Desc.wellFormed] using sb.wf,
      by simpa [named] using sb.named, by first | exact fb.1.1 | exact fb.1⟩
    have he : PlanAt w mem (pa + 16) (Plan.words e) := by
      have := ha.right (a := [_, n]) (b := Plan.words e); simpa using this
    have he' : PlanAt w mem (pb + 16) (Plan.words e') := by
      have := hb.right (a := [_, n']) (b := Plan.words e'); simpa using this
    simp only [Desc.nesting] at da db
    have c := ih se e' se' (pa + 16) (pb + 16) (level - 1) sp mem he he' (by omega) (by omega)
      (by simp only [Room] at room ⊢; omega)
    obtain ⟨r1, a1, x1⟩ := sa.word ha 1 (by simp [Plan.words])
    obtain ⟨s1, b1, y1⟩ := sb.word hb 1 (by simp [Plan.words])
    simp [Plan.words] at r1 s1 x1 y1
    by_cases nn : n = n'
    · subst nn
      wsteps [h0, h1, r0, a0, s0, b0, r1, a1, s1, b1]
      wcall c [h0, h1]
      wsteps []
      wfin []
    · wsteps [h0, h1, r0, a0, s0, b0, r1, a1, s1, b1, nn, x1, y1]
      wfin [h2, nn]
      exact fun h => absurd h nn
  | progressiveList e l ih =>
    shape_open
    rename_i e' l'
    have fa := sa.fits
    have fb := sb.fits
    simp only [fitsNative, Bool.and_eq_true] at fa fb
    have se : Sound e := ⟨by simpa [Desc.wellFormed] using sa.wf, by simpa [named] using sa.named, fa.1⟩
    have se' : Sound e' := ⟨by simpa [Desc.wellFormed] using sb.wf, by simpa [named] using sb.named, fb.1⟩
    have he : PlanAt w mem (pa + 24) (Plan.words e) := by
      have := ha.right (a := 9 :: Plan.bound l) (b := Plan.words e); simpa using this
    have he' : PlanAt w mem (pb + 24) (Plan.words e') := by
      have := hb.right (a := 9 :: Plan.bound l') (b := Plan.words e'); simpa using this
    simp only [Desc.nesting] at da db
    have c := ih se e' se' (pa + 24) (pb + 24) (level - 1) sp mem he he' (by omega) (by omega)
      (by simp only [Room] at room ⊢; omega)
    wsteps [h0, h1, r0, a0, s0, b0]
    wcall c [h0, h1]
    wsteps []
    wfin []
  | container names fs ih =>
    shape_open
    rename_i names' gs
    have fa := sa.fits
    have fb := sb.fits
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fa fb
    have na := sa.named
    have nb := sb.named
    simp only [named, Bool.and_eq_true, beq_iff_eq] at na nb
    have wa := ((wellFormed_container_iff _ _).mp sa.wf).2.2.2
    have wb := ((wellFormed_container_iff _ _).mp sb.wf).2.2.2
    have hf : PlanAt w mem (pa + 16) (Plan.wordsAll fs) := by
      have := ha.right (a := [10, fs.length]) (b := Plan.wordsAll fs); simpa using this
    have hg : PlanAt w mem (pb + 16) (Plan.wordsAll gs) := by
      have := hb.right (a := [10, gs.length]) (b := Plan.wordsAll gs); simpa using this
    simp only [Desc.nesting] at da db
    obtain ⟨r1, a1, x1⟩ := sa.word ha 1 (by simp [Plan.words])
    obtain ⟨s1, b1, y1⟩ := sb.word hb 1 (by simp [Plan.words])
    simp [Plan.words] at r1 s1 x1 y1
    rw [na.1, nb.1]
    by_cases len : fs.length = gs.length
    · have c := compatAll_calls hm fs gs ih (sound_mem wa na.2 fa.1.1) (sound_mem wb nb.2 fb.1.1) len
        (Desc.deepestNesting fs) (Nat.le_refl _) (pa + 16) (pb + 16) (level - 1) sp mem hf hg (by omega) (by omega)
        (by simp only [Room] at room ⊢; omega)
      wsteps [h0, h1, r0, a0, s0, b0, r1, a1, s1, b1, len]
      wcall c [h0, h1, r1, a1, len]
      wsteps []
      wfin [len]
    · have bad : fieldsCompatible (Desc.deepestNesting fs) fs gs = false := by
        cases h : fieldsCompatible (Desc.deepestNesting fs) fs gs
        · rfl
        · exact absurd (fieldsCompatible_length _ _ h) len
      wsteps [h0, h1, r0, a0, s0, b0, r1, a1, s1, b1, len, x1, y1]
      wfin [h2, bad]
  | progressiveContainer la names fa ih =>
    shape_open
    rename_i lb names' fb
    have na := sa.named
    have nb := sb.named
    simp only [named, Bool.and_eq_true, beq_iff_eq] at na nb
    obtain ⟨rfl, _⟩ := na
    obtain ⟨rfl, _⟩ := nb
    simp only [Desc.nesting] at da db
    have c := layouts_calls hm la lb fa fb ih sa sb (Desc.deepestNesting fa) (Nat.le_refl _) pa pb (level - 1) sp mem
      ha hb (by omega) (by omega) (by simp only [Room] at room ⊢; omega)
    wsteps [h0, h1, r0, a0, s0, b0]
    wcall c [h0, h1]
    wsteps []
    wfin []
  | compatibleUnion sels os ih =>
    shape_open
    rename_i sels' qs
    have fa := sa.fits
    have fb := sb.fits
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at fa fb
    have na : namedAll os = true := by simpa [named] using sa.named
    have nb : namedAll qs = true := by simpa [named] using sb.named
    have wa := (wf_union _ _ sa.wf).2.2.2.2.1
    have wb := (wf_union _ _ sb.wf).2.2.2.2.1
    have hf : PlanAt w mem (pa + 16 + 8 * os.length) (Plan.wordsAll os) := by
      have e : Plan.words (.compatibleUnion sels os) = ([12, os.length] ++ sels) ++ Plan.wordsAll os := by
        simp [Plan.words]
      have hp' := ha; rw [e] at hp'
      refine hp'.right.at_eq ?_
      simp [fa.1.2]; omega
    have hg : PlanAt w mem (pb + 16 + 8 * qs.length) (Plan.wordsAll qs) := by
      have e : Plan.words (.compatibleUnion sels' qs) = ([12, qs.length] ++ sels') ++ Plan.wordsAll qs := by
        simp [Plan.words]
      have hp' := hb; rw [e] at hp'
      refine hp'.right.at_eq ?_
      simp [fb.1.2]; omega
    simp only [Desc.nesting] at da db
    obtain ⟨r1, a1, x1⟩ := sa.word ha 1 (by simp [Plan.words])
    obtain ⟨s1, b1, y1⟩ := sb.word hb 1 (by simp [Plan.words])
    simp [Plan.words] at r1 s1 x1 y1
    have c := optionsAgree_calls hm os qs ih (sound_mem wa na fa.1.1.1) (sound_mem wb nb fb.1.1.1)
      (Desc.deepestNesting os) (Nat.le_refl _) _ _ (level - 1) sp mem hf hg (by omega) (by omega)
      (by simp only [Room] at room ⊢; omega)
    wsteps [h0, h1, r0, a0, s0, b0]
    wcall c [h0, h1, r1, a1, s1, b1]
    wsteps []
    wfin []

/-! Every pair of a union's options. -/

/-- Whether each of the first options is compatible with every option after it. -/
def pairsUpTo (os : List Desc) (i : Nat) : Bool :=
  (List.range i).all fun k => (os.drop (k + 1)).all (compatibleAt os[k]!.nesting os[k]!)

/-- Every option checked against the ones after it is every pair checked. -/
theorem pairsUpTo_length : ∀ os : List Desc, pairsUpTo os os.length = allPairs os
  | [] => rfl
  | o :: rest => by
    simp only [allPairs]
    rw [← pairsUpTo_length rest]
    simp only [pairsUpTo, List.length_cons]
    rw [List.range_succ_eq_map, List.all_cons, List.all_map]
    simp [Function.comp_def]

/-- One more option checked. -/
theorem pairsUpTo_succ (os : List Desc) (i : Nat) :
    pairsUpTo os (i + 1) = (pairsUpTo os i && (os.drop (i + 1)).all (compatibleAt os[i]!.nesting os[i]!)) := by
  simp [pairsUpTo, List.range_succ, List.all_append]

/-- The options after one, a count of them taken, then one more. -/
theorem take_drop_succ (os : List Desc) (i k : Nat) (h : i + 1 + k < os.length) :
    (os.drop (i + 1)).take (k + 1) = (os.drop (i + 1)).take k ++ [os[i + 1 + k]] := by
  rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem h]
  rfl

set_option maxHeartbeats 16000000 in
/-- Checking every pair of a union's sound options answers whether each is compatible with every later one. -/
theorem pairs_calls {m : Module} {w : World} (hm : Loaded m) (os : List Desc) (so : ∀ f ∈ os, Sound f)
    (p sp : Nat) (mem : Memory) (hp : PlanAt w mem p (Plan.wordsAll os))
    (room : Room w sp (2 * (Desc.deepestNesting os + 1)) 1) :
    Calls m w "ssz_validate_pairs" sp [UInt64.ofNat p, UInt64.ofNat os.length] mem
      (if allPairs os then 1 else 0) mem := by
  have bp := hp.bound
  have lw := length_le_wordsAll os
  have ih := fun f (_ : f ∈ os) => compat_calls (m := m) (w := w) hm f
  refine Calls.body 9 hm.pairs rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [pairsFn]
  rw [← pairsUpTo_length]
  wsteps []
  -- After i options, the result says whether each of them is compatible with every later one.
  refine Wp.loop (wp_loop (fun env mem' => mem' = mem ∧ ∃ i, i ≤ os.length ∧
      env 0 = UInt64.ofNat (p + 8 * (Plan.wordsAll (os.take i)).length) ∧ env 1 = UInt64.ofNat (os.length - i) ∧
      env 2 = (if pairsUpTo os i then 1 else 0))
    (fun env _ => (env 1).toNat)
    ⟨rfl, 0, Nat.zero_le _, by wfin [Plan.wordsAll], by wfin [], by wfin [pairsUpTo]⟩ ?_)
  rintro env mem' ⟨hmem, i, hi, h0, h1, h2⟩
  subst mem'
  have hia := wordsAll_take_le os i
  by_cases ok : pairsUpTo os i = true
  · rw [if_pos ok] at h2
    refine ⟨_, by wev [h1, h2], fun nz => ?_, fun z => ?_⟩
    · have hio : i < os.length := by
        rcases Nat.lt_or_ge i os.length with h | h
        · exact h
        · simp [show os.length - i = 0 by omega] at nz
      obtain ⟨_, hpa, _⟩ := fieldAt hp i hio
      have mo := List.getElem_mem hio
      have no := nesting_le_deepest os os[i] mo
      have ka := skip_calls hm os[i] (so _ mo).fits _ (sp - 8 - 8 * 9) mem hpa
        (by simp only [Room] at room ⊢; generalize os[i].nesting = x at no ⊢; omega)
      have next := wordsAll_take_succ os i hio
      have hl1 : os.length - i ≠ 0 := by omega
      have sub : os.length - i - 1 < 2 ^ 64 := by omega
      wcall ka [h0]
      wsteps [h1, hl1, sub]
      -- After k later options, the result says whether this option is compatible with each of them.
      refine Wp.loop (wp_loop (fun env' mem' => mem' = mem ∧ ∃ k, i + 1 + k ≤ os.length ∧
          env' 3 = UInt64.ofNat (p + 8 * (Plan.wordsAll (os.take (i + 1 + k))).length) ∧
          env' 4 = UInt64.ofNat (os.length - i - 1 - k) ∧
          env' 2 = (if ((os.drop (i + 1)).take k).all (compatibleAt os[i].nesting os[i]) then 1 else 0) ∧
          env' 0 = UInt64.ofNat (p + 8 * (Plan.wordsAll (os.take i)).length) ∧
          env' 5 = UInt64.ofNat (p + 8 * (Plan.wordsAll (os.take (i + 1))).length) ∧
          env' 1 = UInt64.ofNat (os.length - i))
        (fun env' _ => (env' 4).toNat)
        ⟨rfl, 0, by omega, by wfin [next], by wfin [], by wfin [h2], by wfin [h0], by wfin [next], by wfin [h1]⟩ ?_)
      rintro env' mem' ⟨hmem', k, hk, g3, g4, g2, g0, g5, g1⟩
      subst mem'
      have hkb := wordsAll_take_le os (i + 1 + k)
      by_cases fits : ((os.drop (i + 1)).take k).all (compatibleAt os[i].nesting os[i]) = true
      · rw [if_pos fits] at g2
        refine ⟨_, by wev [g4, g2], fun nz' => ?_, fun z' => ?_⟩
        · have hko : i + 1 + k < os.length := by
            rcases Nat.lt_or_ge (i + 1 + k) os.length with h | h
            · exact h
            · simp [show os.length - i - 1 - k = 0 by omega] at nz'
          obtain ⟨_, hpb, _⟩ := fieldAt hp (i + 1 + k) hko
          have mq := List.getElem_mem hko
          have nq := nesting_le_deepest os _ mq
          have c := ih os[i] mo (so _ mo) _ (so _ mq) _ _ (Desc.deepestNesting os) (sp - 8 - 8 * 9) mem hpa hpb
            (by omega) (by omega) (by simp only [Room] at room ⊢; omega)
          have kb := skip_calls hm os[i + 1 + k] (so _ mq).fits _ (sp - 8 - 8 * 9) mem hpb
            (by simp only [Room] at room ⊢; generalize os[i + 1 + k].nesting = x at nq ⊢; omega)
          have step : ((os.drop (i + 1)).take (k + 1)).all (compatibleAt os[i].nesting os[i]) =
              compatibleAt os[i].nesting os[i] os[i + 1 + k] := by
            rw [take_drop_succ os i k hko, List.all_append, fits]
            simp
          have hl4 : os.length - i - 1 - k ≠ 0 := by omega
          wcall c [g0, g3]
          wcall kb [g3]
          wsteps [g4, hl4]
          refine ⟨⟨trivial, k + 1, by omega, ?_, by wfin [g4], by wfin [step], by wfin [g0], by wfin [g5],
            by wfin [g1]⟩, by wfin [g4]⟩
          wfin [show i + 1 + (k + 1) = (i + 1 + k) + 1 by omega, wordsAll_take_succ os (i + 1 + k) hko]
        · -- This option is compatible with every later one.
          have hko : i + 1 + k = os.length := by
            rcases Nat.lt_or_ge (i + 1 + k) os.length with h | h
            · simp [show os.length - i - 1 - k ≠ 0 by omega] at z'
            · omega
          have all : (os.drop (i + 1)).take k = os.drop (i + 1) := List.take_of_length_le (by simp; omega)
          rw [all] at fits
          have step : pairsUpTo os (i + 1) = true := by
            rw [pairsUpTo_succ, ok, getElem!_pos os i hio]
            simpa using fits
          wsteps [g1, hl1]
          refine ⟨⟨trivial, i + 1, by omega, by wfin [g5], by wfin [g1], by wfin [g2, step]⟩, by wfin [g1, h1]⟩
      · rw [if_neg fits] at g2
        -- This option clashes with a later one.
        have bad : pairsUpTo os (i + 1) = false := by
          rw [pairsUpTo_succ, ok, getElem!_pos os i hio, Bool.true_and]
          have e := List.take_append_drop k (os.drop (i + 1))
          rw [← e, List.all_append]
          simp [fits]
        refine ⟨_, by wev [g4, g2], fun nz' => ?_, fun _ => ?_⟩
        · simp at nz'
        · wsteps [g1, hl1]
          refine ⟨⟨trivial, i + 1, by omega, by wfin [g5], by wfin [g1], by wfin [g2, bad]⟩, by wfin [g1, h1]⟩
    · have hio : i = os.length := by
        rcases Nat.lt_or_ge i os.length with h | h
        · simp [show os.length - i ≠ 0 by omega] at z
        · omega
      subst hio
      exact Wp.done ⟨by wfin [h2, ok], rfl⟩
  · rw [if_neg ok] at h2
    -- Some option among the first i clashes with a later one.
    have bad : pairsUpTo os os.length = false := by
      have e : os.length = i + (os.length - i) := by omega
      rw [e]
      simp only [Bool.not_eq_true] at ok
      generalize os.length - i = d
      induction d with
      | zero => exact ok
      | succ d ihd => rw [← Nat.add_assoc, pairsUpTo_succ, ihd, Bool.false_and]
    refine ⟨_, by wev [h1, h2], fun nz => ?_, fun _ => Wp.done ⟨by wfin [h2, bad], rfl⟩⟩
    simp at nz

/-- The compatibility routine answers one for the options of a legal union, named as a plan names them. -/
theorem pairsOk {m : Module} {w : World} (hm : Loaded m) : PairsOk m w := by
  intro sels opts p sp mem comp fit nm wf hp room
  have := pairs_calls hm opts (sound_mem wf nm fit) p sp mem hp room
  rwa [(optionsCompatible_iff sels opts).mp comp, if_pos rfl] at this

end Ssz.Native.Driver.Validate
