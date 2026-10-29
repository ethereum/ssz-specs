import SszNative.Proofs.Driver.Validate.Converse
import SszNative.Proofs.Plan.Names

/-!
The check of one plan node, read backward.

When the check of a node returns anything but the word for none, the words from the node are a sound type's words,
and it returned the address past them.
The words may be anything: each one the check reads, it reads from a readable region that ends where the plan ends.
-/

namespace Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open Ssz Ssz.Native Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Ir.Stmt Ssz.Native.Ir.Expr

/-! Stepping through a run that happened. -/

/--
Takes one step of a block every run of which is to meet a condition: an assignment, or a branch whose condition
evaluates to a constant either way.
-/
macro "pstep" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    try show Ssz.Native.Ir.Pc _ _ _ (Ssz.Native.Ir.Stmt.block _) _ _ _
    first
    | (refine Ssz.Native.Ir.Pc.set_of (v := ?v) ?h ?k
       case h => ((wev [$args,*]); done))
    | (refine Ssz.Native.Ir.Pc.ifElse_f ?h ?k
       case h => ((wonly [$args,*]); done))
    | (refine Ssz.Native.Ir.Pc.ifElse_t (v := ?v) ?h ?nz ?k
       case h => ((wev [$args,*]); done)
       case nz => ((wonly [$args,*]); done))
    | (refine Ssz.Native.Ir.Pc.when_f ?h ?k
       case h => ((wonly [$args,*]); done))
    | (refine Ssz.Native.Ir.Pc.when_t (v := ?v) ?h ?nz ?k
       case h => ((wev [$args,*]); done)
       case nz => ((wonly [$args,*]); done))
    | refine Ssz.Native.Ir.Pc.done ?_))

/-- Takes steps of a block for as long as one can be taken. -/
macro "psteps" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| repeat (pstep [$args,*]; try simp only [List.cons_append, List.nil_append, List.append_nil]))

/-- Takes a call at the head of a block, its arguments evaluated, leaving what it returns to the proof. -/
macro "pcall" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    try show Ssz.Native.Ir.Pc _ _ _ (Ssz.Native.Ir.Stmt.block _) _ _ _
    refine Ssz.Native.Ir.Pc.call_of (values := ?vs) ?hv ?k
    case hv => ((wev [$args,*]); done)))

/-! Words in memory. -/

/-- Words at an address followed by words past them are the words of both, in a readable region. -/
theorem PlanAt.append {w : World} {mem : Memory} {p : Nat} {a b : List Nat} (ha : PlanAt w mem p a)
    (hb : PlanAt w mem (p + 8 * a.length) b) (acc : w.access p (8 * (a.length + b.length)) = true) :
    PlanAt w mem p (a ++ b) := by
  refine ⟨by simpa using acc, fun i hi => ?_⟩
  by_cases lt : i < a.length
  · rw [List.getElem_append_left lt]; exact ha.2 i lt
  · rw [List.getElem_append_right (by omega)]
    have := hb.2 (i - a.length) (by simp at hi; omega)
    rwa [show p + 8 * a.length + 8 * (i - a.length) = p + 8 * i by omega] at this

/-- A word read back as a number below 2^64 sits at its address as that number. -/
theorem planAt_one {w : World} {mem : Memory} {p x : Nat} (acc : w.access p 8 = true)
    (h : readLE mem p 8 = UInt64.ofNat x) : PlanAt w mem p [x] :=
  ⟨by simpa using acc, fun i hi => by
    have : i = 0 := by simpa using hi
    subst this
    simpa using h⟩

/-- Each type of a list of sound types is sound together. -/
theorem sound_all : ∀ {fs : List Desc}, (∀ f ∈ fs, Sound f) →
    Desc.allWellFormed fs = .ok () ∧ allFitNative fs = true ∧ namedAll fs = true
  | [], _ => ⟨rfl, rfl, rfl⟩
  | f :: rest, h => by
    obtain ⟨a, b, c⟩ := sound_all (fs := rest) (fun g hg => h g (List.mem_cons_of_mem _ hg))
    have s := h f List.mem_cons_self
    refine ⟨?_, ?_, ?_⟩
    · rw [Desc.allWellFormed, bind_unit_ok]; exact ⟨s.wf, a⟩
    · simp [allFitNative, s.fits, b]
    · simp [namedAll, s.named, c]

/-! What a check that happened returned. -/

/-- The word for none. -/
abbrev noneWord : UInt64 := 18446744073709551615

/-- What a check of one node may return: the word for none, or the address past a sound type's words there. -/
def PlanRes (w : World) (mem : Memory) (p stop : Nat) (r : UInt64) : Prop :=
  r = noneWord ∨ ∃ d, Sound d ∧ PlanAt w mem p (Plan.words d) ∧ p + 8 * (Plan.words d).length ≤ stop ∧
    r = UInt64.ofNat (p + 8 * (Plan.words d).length)

/-- What a check of one node that happened returned, when the region from the node to the plan's end is readable. -/
def PlanBack (m : Module) (w : World) (p stop : Nat) : Prop :=
  p ≤ stop → w.access p (stop - p) = true →
    ∀ sp mem r mem', Calls m w "ssz_validate_plan" sp [UInt64.ofNat p, UInt64.ofNat stop] mem r mem' →
      PlanRes w mem p stop r

/-- What a check of one node returns, as the condition every run of its body meets. -/
abbrev PlanPost (w : World) (p stop : Nat) (mem : Memory) : Env → Memory → Prop :=
  fun env k => ∀ r, eval w env k planFn.result = some r → PlanRes w mem p stop r

/-- A check that holds the word for none returns it. -/
theorem post_none {w : World} {p stop : Nat} {mem : Memory} {env : Env} {k : Memory} (h : env 3 = noneWord) :
    PlanPost w p stop mem env k := by
  intro r hr
  left
  simp only [planFn] at hr
  rw [← Option.some.inj hr, ← h]

/-- A check that holds the address past a sound type's words returns it. -/
theorem post_some {w : World} {p stop : Nat} {mem : Memory} {env : Env} {k : Memory} (d : Desc) (sd : Sound d)
    (hp : PlanAt w mem p (Plan.words d)) (hs : p + 8 * (Plan.words d).length ≤ stop)
    (h : env 3 = UInt64.ofNat (p + 8 * (Plan.words d).length)) : PlanPost w p stop mem env k := by
  intro r hr
  right
  simp only [planFn] at hr
  refine ⟨d, sd, hp, hs, ?_⟩
  rw [← Option.some.inj hr, ← h]

/-- What a check of one node that happened returned, its tag read and the nodes past it checked as it goes. -/
def TagBack (m : Module) (w : World) (k : Nat) : Prop :=
  ∀ (p stop sp : Nat) (mem : Memory) (r : UInt64) (mem' : Memory), p ≤ stop → w.access p (stop - p) = true →
    readLE mem p 8 = UInt64.ofNat k → (∀ q, p < q → PlanBack m w q stop) →
    Calls m w "ssz_validate_plan" sp [UInt64.ofNat p, UInt64.ofNat stop] mem r mem' → PlanRes w mem p stop r

set_option hygiene false in
/-- Opens a check of one node that happened, its tag known, up to its branch; a node past the end returns none. -/
macro "back_open" : tactic => `(tactic| (
  intro p stop sp mem r mem' hps hacc tag ih call
  have s63 : stop ≤ 2 ^ 63 := by
    simp only [World.access, addressBound, Bool.and_eq_true, decide_eq_true_eq] at hacc; omega
  refine Calls.of_pc (P := fun r _ => PlanRes w mem p stop r) 15 hm.plan rfl ?_ call
  simp only [planFn]
  by_cases s8 : p + 8 ≤ stop
  case neg =>
    psteps [s8]
    exact post_none (by wfin [])
  have a0 : w.access p 8 = true := access_sub hacc (Nat.le_refl _) (by omega)
  psteps [s8, tag, a0]))

/-- A boolean node checked backward. -/
theorem tag0_back {m : Module} {w : World} (hm : Loaded m) : TagBack m w 0 := by
  back_open
  exact post_some .bool ⟨rfl, rfl, rfl⟩ (planAt_one a0 tag) (by simp [Plan.words]; omega) (by wfin [Plan.words])

/-- Every word in memory is some number below 2^64. -/
theorem word_of (mem : Memory) (a : Nat) : ∃ n, n < 2 ^ 64 ∧ readLE mem a 8 = UInt64.ofNat n :=
  ⟨_, UInt64.toNat_lt _, UInt64.ofNat_toNat.symm⟩

/-- A word, then words past it, in a readable region. -/
theorem PlanAt.cons {w : World} {mem : Memory} {p x : Nat} {rest : List Nat} (acc : w.access p 8 = true)
    (h : readLE mem p 8 = UInt64.ofNat x) (hr : PlanAt w mem (p + 8) rest)
    (all : w.access p (8 * (1 + rest.length)) = true) : PlanAt w mem p (x :: rest) :=
  PlanAt.append (a := [x]) (planAt_one acc h) (by simpa using hr) (by simpa using all)

set_option hygiene false in
/-- Reads the node's second word, past a check that it fits; a node past the end returns none. -/
macro "back_word" : tactic => `(tactic| (
  by_cases s16 : p + 16 ≤ stop
  case neg =>
    psteps [s16]
    exact post_none (by wfin [])
  have a1 : w.access (p + 8) 8 = true := access_sub hacc (by omega) (by omega)
  obtain ⟨n, n64, rn⟩ := word_of mem (p + 8)
  have two : PlanAt w mem p [_, n] :=
    PlanAt.cons a0 tag (planAt_one a1 rn) (access_sub hacc (Nat.le_refl _) (by simp; omega))
  psteps [s16, a1, rn]))

/-- An integer node checked backward: one of six widths. -/
theorem tag1_back {m : Module} {w : World} (hm : Loaded m) : TagBack m w 1 := by
  back_open
  back_word
  by_cases hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 ∨ n = 16 ∨ n = 32
  · have wf : (Desc.uint n).wellFormed = .ok () := by
      rcases hn with h | h | h | h | h | h <;> subst h <;> rfl
    have fit : fitsNative (.uint n) = true := by simp [fitsNative]; omega
    rcases hn with h | h | h | h | h | h <;> subst h <;>
    · psteps []
      exact post_some (.uint _) ⟨wf, rfl, fit⟩ two (by simp [Plan.words]; omega) (by wfin [Plan.words])
  · simp only [not_or] at hn
    obtain ⟨h1, h2, h4, h8, h16, h32⟩ := hn
    psteps [h1, h2, h4, h8, h16, h32]
    exact post_none (by wfin [])

set_option hygiene false in
/-- Settles a fixed count read from the node's second word: at least one and below 2^32. -/
macro "back_count" d:term : tactic => `(tactic| (
  by_cases ok : n ≠ 0 ∧ n < 2 ^ 32
  · psteps [ok.1, ok.2]
    exact post_some $d ⟨by simp [Desc.wellFormed, ok.1], rfl, by simp [fitsNative]; omega⟩ two
      (by simp [Plan.words]; omega) (by wfin [Plan.words])
  · by_cases z : n = 0
    · psteps [z]
      exact post_none (by wfin [])
    · have big : ¬ n < 4294967296 := by omega
      psteps [z, big]
      exact post_none (by wfin [])))

set_option hygiene false in
/-- Settles a limit read from the node's second word: any word. -/
macro "back_limit" d:term : tactic => `(tactic| (
  psteps []
  exact post_some $d ⟨rfl, rfl, by simp [fitsNative]; omega⟩ two (by simp [Plan.words]; omega) (by wfin [Plan.words])))

/-- A byte vector node checked backward: a length of at least one and below 2^32. -/
theorem tag2_back {m : Module} {w : World} (hm : Loaded m) : TagBack m w 2 := by
  back_open
  back_word
  back_count (.byteVector n)

/-- A byte list node checked backward: any limit. -/
theorem tag3_back {m : Module} {w : World} (hm : Loaded m) : TagBack m w 3 := by
  back_open
  back_word
  back_limit (.byteList n)

/-- A bit vector node checked backward: a length of at least one and below 2^32. -/
theorem tag4_back {m : Module} {w : World} (hm : Loaded m) : TagBack m w 4 := by
  back_open
  back_word
  back_count (.bitVector n)

/-- A bit list node checked backward: any limit. -/
theorem tag5_back {m : Module} {w : World} (hm : Loaded m) : TagBack m w 5 := by
  back_open
  back_word
  back_limit (.bitList n)

set_option hygiene false in
/-- Reads the node's bound, past a check that it fits; a node past the end returns none. -/
macro "back_bound" : tactic => `(tactic| (
  by_cases s24 : p + 24 ≤ stop
  case neg =>
    psteps [s24]
    exact post_none (by wfin [])
  have a1 : w.access (p + 8) 8 = true := access_sub hacc (by omega) (by omega)
  have a2 : w.access (p + 16) 8 = true := access_sub hacc (by omega) (by omega)
  obtain ⟨h, h64, rh⟩ := word_of mem (p + 8)
  obtain ⟨v, v64, rv⟩ := word_of mem (p + 16)
  have three : PlanAt w mem p [_, h, v] :=
    PlanAt.cons a0 tag (PlanAt.cons a1 rh (planAt_one (by simpa [Nat.add_assoc] using a2)
      (by simpa [Nat.add_assoc] using rv)) (access_sub hacc (by omega) (by simp; omega)))
      (access_sub hacc (Nat.le_refl _) (by simp; omega))
  psteps [s24, a1, a2]))

/-- A progressive bit list node checked backward: a bound spelled as a plan writes one. -/
theorem tag6_back {m : Module} {w : World} (hm : Loaded m) : TagBack m w 6 := by
  back_open
  back_bound
  by_cases c1 : h = 1
  · subst c1
    psteps [rh, rv, a1, a2, canonicalBound]
    exact post_some (.progressiveBitList (some v)) ⟨rfl, rfl, by simp [fitsNative]; omega⟩
      (by simpa [Plan.words, Plan.bound] using three) (by simp [Plan.words, Plan.bound]; omega)
      (by wfin [Plan.words, Plan.bound])
  · by_cases c0 : h = 0 ∧ v = 0
    · obtain ⟨rfl, rfl⟩ := c0
      psteps [rh, rv, a1, a2, canonicalBound]
      exact post_some (.progressiveBitList none) ⟨rfl, rfl, rfl⟩
        (by simpa [Plan.words, Plan.bound] using three) (by simp [Plan.words, Plan.bound]; omega)
        (by wfin [Plan.words, Plan.bound])
    · by_cases h0 : h = 0
      · subst h0
        have v0 : v ≠ 0 := by omega
        psteps [rh, rv, a1, a2, canonicalBound, v0]
        exact post_none (by wfin [])
      · psteps [rh, rv, a1, a2, canonicalBound, c1, h0]
        exact post_none (by wfin [])

/-- A list node checked backward: a limit and an element. -/
theorem tag8_back {m : Module} {w : World} (hm : Loaded m) : TagBack m w 8 := by
  back_open
  back_word
  pcall []
  intro q mem'' hc
  have keep := Calls.keeps hm.keeps (by simp [planNames]) hc
  subst mem''
  rcases ih (p + 16) (by omega) (by omega) (access_sub hacc (by omega) (by omega)) _ _ _ _ hc with
    rfl | ⟨e, se, he, hs, rfl⟩
  · psteps []
    exact post_none (by wfin [])
  · psteps []
    exact post_some (.list e n) ⟨by simpa [Desc.wellFormed] using se.wf, by simpa [named] using se.named,
        by simp [fitsNative, se.fits]; omega⟩
      (PlanAt.append two (by simpa using he) (access_sub hacc (Nat.le_refl _) (by simp; omega)))
      (by simp [Plan.words]; omega) (by wfin [Plan.words])

set_option hygiene false in
/-- Refuses a fixed count read from the node's second word that is zero or reaches 2^32. -/
macro "back_count_bad" : tactic => `(tactic| (
  by_cases z : n = 0
  · psteps [z]
    exact post_none (by wfin [])
  · have big : ¬ n < 4294967296 := by omega
    psteps [z, big]
    exact post_none (by wfin [])))

/-- A vector node checked backward: a length, an element, and a width that fits. -/
theorem tag7_back {m : Module} {w : World} (hm : Loaded m) : TagBack m w 7 := by
  back_open
  back_word
  by_cases ok : n ≠ 0 ∧ n < 2 ^ 32
  case neg => back_count_bad
  psteps [ok.1, ok.2]
  pcall []
  intro q mem'' hc
  have keep := Calls.keeps hm.keeps (by simp [planNames]) hc
  subst mem''
  rcases ih (p + 16) (by omega) (by omega) (access_sub hacc (by omega) (by omega)) _ _ _ _ hc with
    rfl | ⟨e, se, he, hs, rfl⟩
  · psteps []
    exact post_none (by wfin [])
  have qne : p + 16 + 8 * (Plan.words e).length ≠ 18446744073709551615 := by omega
  psteps [qne]
  pcall []
  intro wv mem'' hw
  obtain ⟨rfl, keep⟩ := width_agree hm se.fits he hw
  subst mem''
  have he' : PlanAt w mem p (Plan.words (.vector e n)) :=
    PlanAt.append two (by simpa using he) (access_sub hacc (Nat.le_refl _) (by simp; omega))
  have wf : (Desc.vector e n).wellFormed = .ok () := by simp [Desc.wellFormed, ok.1, se.wf]
  by_cases has : hasWidth e = true
  · have fw := fixedWidth_lt e se.fits has
    have hne : fixedWidth e ≠ 18446744073709551615 := by omega
    simp only [widthWord, if_pos has]
    by_cases prod : fixedWidth e * n < 2 ^ 32
    · psteps [hne, prod]
      exact post_some (.vector e n) ⟨wf, by simpa [named] using se.named,
          by simp [fitsNative, se.fits, has]; omega⟩ he'
        (by simp [Plan.words]; omega) (by wfin [Plan.words])
    · have prod' : ¬ fixedWidth e * n < 4294967296 := prod
      have p64 : fixedWidth e * n < 2 ^ 64 :=
        Nat.lt_of_lt_of_le (Nat.mul_lt_mul'' fw ok.2) (by decide)
      psteps [hne, prod']
      exact post_none (by wfin [])
  · simp only [widthWord, if_neg has]
    psteps []
    exact post_some (.vector e n) ⟨wf, by simpa [named] using se.named,
        by simp [fitsNative, se.fits, has]; omega⟩ he'
      (by simp [Plan.words]; omega) (by wfin [Plan.words])

set_option hygiene false in
/-- Checks the element past a progressive list's bound and settles the list, its bound given. -/
macro "back_element" lim:term : tactic => `(tactic| (
  pcall []
  intro q mem'' hc
  have keep := Calls.keeps hm.keeps (by simp [planNames]) hc
  subst mem''
  rcases ih (p + 24) (by omega) (by omega) (access_sub hacc (by omega) (by omega)) _ _ _ _ hc with
    rfl | ⟨e, se, he, hs, rfl⟩
  · psteps []
    exact post_none (by wfin [])
  · psteps []
    exact post_some (.progressiveList e $lim) ⟨by simpa [Desc.wellFormed] using se.wf,
        by simpa [named] using se.named, by simp [fitsNative, se.fits] <;> omega⟩
      (by simpa [Plan.words, Plan.bound] using
        PlanAt.append three (by simpa using he) (access_sub hacc (Nat.le_refl _) (by simp; omega)))
      (by simp [Plan.words, Plan.bound]; omega) (by wfin [Plan.words, Plan.bound])))

/-- A progressive list node checked backward: a bound spelled as a plan writes one, and an element. -/
theorem tag9_back {m : Module} {w : World} (hm : Loaded m) : TagBack m w 9 := by
  back_open
  back_bound
  by_cases c1 : h = 1
  · subst c1
    psteps [rh, rv, a1, a2, canonicalBound]
    back_element (some v)
  · by_cases c0 : h = 0 ∧ v = 0
    · obtain ⟨rfl, rfl⟩ := c0
      psteps [rh, rv, a1, a2, canonicalBound]
      back_element none
    · by_cases h0 : h = 0
      · subst h0
        have v0 : v ≠ 0 := by omega
        psteps [rh, rv, a1, a2, canonicalBound, v0]
        exact post_none (by wfin [])
      · psteps [rh, rv, a1, a2, canonicalBound, c1, h0]
        exact post_none (by wfin [])

/-! A count of nodes. -/

/-- What a check of a count of nodes may return: the word for none, or the address past that many sound types. -/
def AllRes (w : World) (mem : Memory) (p n stop : Nat) (r : UInt64) : Prop :=
  r = noneWord ∨ ∃ fs : List Desc, fs.length = n ∧ (∀ f ∈ fs, Sound f) ∧ PlanAt w mem p (Plan.wordsAll fs) ∧
    p + 8 * (Plan.wordsAll fs).length ≤ stop ∧ r = UInt64.ofNat (p + 8 * (Plan.wordsAll fs).length)

set_option maxHeartbeats 4000000 in
/-- What a check of a count of nodes that happened returned, each node's check read backward. -/
theorem planAll_back {m : Module} {w : World} (hm : Loaded m) {p n stop sp : Nat} {mem mem' : Memory} {r : UInt64}
    (hps : p ≤ stop) (hacc : w.access p (stop - p) = true) (n64 : n < 2 ^ 64)
    (ih : ∀ q, p ≤ q → PlanBack m w q stop)
    (call : Calls m w "ssz_validate_plan_all" sp [UInt64.ofNat p, UInt64.ofNat n, UInt64.ofNat stop] mem r mem') :
    AllRes w mem p n stop r := by
  have s63 : stop ≤ 2 ^ 63 := by
    simp only [World.access, addressBound, Bool.and_eq_true, decide_eq_true_eq] at hacc; omega
  refine Calls.of_pc (P := fun r _ => AllRes w mem p n stop r) 5 hm.planAll rfl ?_ call
  simp only [planAllFn]
  -- So far, the nodes checked are sound and the walk stands past them, or it holds the word for none.
  refine Pc.loop_inv (fun env k => k = mem ∧ env 2 = UInt64.ofNat stop ∧
      ((∃ fs : List Desc, fs.length ≤ n ∧ (∀ f ∈ fs, Sound f) ∧ PlanAt w mem p (Plan.wordsAll fs) ∧
        p + 8 * (Plan.wordsAll fs).length ≤ stop ∧ env 0 = UInt64.ofNat (p + 8 * (Plan.wordsAll fs).length) ∧
        env 1 = UInt64.ofNat (n - fs.length)) ∨ env 0 = noneWord))
    ⟨rfl, by wfin [], Or.inl ⟨[], Nat.zero_le _, by simp,
      ⟨by simpa [Plan.wordsAll] using access_sub (k := 0) hacc (Nat.le_refl p) (by omega), by simp [Plan.wordsAll]⟩,
      by simp [Plan.wordsAll]; omega, by wfin [Plan.wordsAll], by wfin []⟩⟩ ?_ ?_
  · rintro env k v ⟨rfl, h2, ⟨fs, hn, sf, hf, hs, h0, h1⟩ | h0⟩ hv nz
    · have q63 : p + 8 * (Plan.wordsAll fs).length ≠ 18446744073709551615 := by omega
      have more : n - fs.length ≠ 0 := by
        intro z
        have : eval w env k (both (ne (Var.mk 1 : Expr) 0) (ne (Var.mk 0 : Expr) none_)) = some 0 := by
          wev [h0, h1, z]
        rw [this] at hv
        exact nz (Option.some.inj hv).symm
      pcall [h0, h2]
      intro q mem'' hc
      have keep := Calls.keeps hm.keeps (by simp [planNames]) hc
      subst mem''
      rcases ih _ (by omega) (by omega) (access_sub hacc (by omega) (by omega)) _ _ _ _ hc with
        rfl | ⟨d, sd, hd, hds, rfl⟩
      · psteps [h1]
        exact ⟨trivial, by wfin [h2], Or.inr (by wfin [])⟩
      · psteps [h1, more]
        refine ⟨trivial, by wfin [h2], Or.inl ⟨fs ++ [d], by simp; omega, ?_, ?_, ?_, ?_, ?_⟩⟩
        · intro f hf'
          simp only [List.mem_append, List.mem_singleton] at hf'
          rcases hf' with hf' | rfl
          · exact sf f hf'
          · exact sd
        · rw [wordsAll_append]
          refine PlanAt.append hf (by simpa [Plan.wordsAll] using hd) (access_sub hacc (Nat.le_refl _) ?_)
          simp [Plan.wordsAll]
          omega
        · simp [wordsAll_append, Plan.wordsAll]; omega
        · wfin [wordsAll_append, Plan.wordsAll]
        · wfin [h1]
    · have : eval w env k (both (ne (Var.mk 1 : Expr) 0) (ne (Var.mk 0 : Expr) none_)) = some 0 := by
        wev [h0]
      rw [this] at hv
      exact absurd (Option.some.inj hv).symm nz
  · rintro env k ⟨rfl, h2, ⟨fs, hn, sf, hf, hs, h0, h1⟩ | h0⟩ hc r hr
    · have q63 : p + 8 * (Plan.wordsAll fs).length ≠ 18446744073709551615 := by omega
      have done : n - fs.length = 0 := by
        rcases Nat.eq_zero_or_pos (n - fs.length) with z | pos
        · exact z
        have more : n - fs.length ≠ 0 := by omega
        have : eval w env k (both (ne (Var.mk 1 : Expr) 0) (ne (Var.mk 0 : Expr) none_)) = some 1 := by
          wev [h0, h1, more, q63]
        rw [this] at hc
        cases hc
      right
      refine ⟨fs, by omega, sf, hf, hs, ?_⟩
      rw [← Option.some.inj hr]
      wfin [h0]
    · left
      rw [← Option.some.inj hr]
      wfin [h0]

/-! Structs. -/

/-- Fields that fit the native check take below 2^32 bytes each of the fixed part. -/
theorem leadingWidth_le : ∀ fs : List Desc, allFitNative fs = true → Desc.leadingWidth fs ≤ 2 ^ 32 * fs.length
  | [], _ => by simp [Desc.leadingWidth]
  | f :: rest, fit => by
    simp only [allFitNative, Bool.and_eq_true] at fit
    rw [leadingWidth_cons]
    have := leadingWidth_le rest fit.2
    have one : (if hasWidth f then fixedWidth f else 4) ≤ 2 ^ 32 := by
      split
      · have := fixedWidth_lt f fit.1 (by assumption); omega
      · omega
    simp only [List.length_cons, Nat.mul_succ]
    omega

/-- Sound fields fit together, with their leading width read below 2^64. -/
theorem fields_small {fs : List Desc} (sf : ∀ f ∈ fs, Sound f) (n32 : fs.length < 2 ^ 32) :
    Desc.leadingWidth fs < 2 ^ 64 := by
  have := leadingWidth_le fs (sound_all sf).2.1
  have : 2 ^ 32 * fs.length < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_left n32 (by decide)
  omega

/-- Names by position are as many as the count. -/
theorem length_positionNames (n : Nat) : (Plan.positionNames n).length = n := by simp [Plan.positionNames]

set_option maxHeartbeats 4000000 in
/-- A container node checked backward: fields, as many as it declares, with a fixed part that fits. -/
theorem tag10_back {m : Module} {w : World} (hm : Loaded m) : TagBack m w 10 := by
  back_open
  back_word
  by_cases ok : n ≠ 0 ∧ n < 2 ^ 32
  case neg => back_count_bad
  psteps [ok.1, ok.2]
  pcall []
  intro q mem'' hc
  have keep := Calls.keeps hm.keeps (by simp [planNames]) hc
  subst mem''
  rcases planAll_back hm (by omega) (access_sub hacc (by omega) (by omega)) n64 (fun q hq => ih q (by omega)) hc with
    rfl | ⟨fs, rfl, sf, hf, hs, rfl⟩
  · psteps []
    exact post_none (by wfin [])
  have qne : p + 16 + 8 * (Plan.wordsAll fs).length ≠ 18446744073709551615 := by omega
  psteps [qne]
  pcall []
  intro lw mem'' hl
  obtain ⟨rfl, keep⟩ := leading_agree hm (sound_all sf).2.1 hf hl
  subst mem''
  have l64 := fields_small sf ok.2
  by_cases l32 : Desc.leadingWidth fs < 2 ^ 32
  · have l32' : Desc.leadingWidth fs < 4294967296 := l32
    psteps [l32']
    obtain ⟨wfs, fit, nm⟩ := sound_all sf
    have ne : fs ≠ [] := fun h => ok.1 (by simp [h])
    exact post_some (.container (Plan.positionNames fs.length) fs)
      ⟨(wellFormed_container_iff _ _).mpr ⟨ne, length_positionNames _,
          Ssz.firstDuplicate_of_nodup _ (Plan.positionNames_nodup _), wfs⟩,
        by simp [named, nm], by simp [fitsNative, fit]; omega⟩
      (PlanAt.append two (by simpa using hf) (access_sub hacc (Nat.le_refl _) (by simp; omega)))
      (by simp [Plan.words]; omega) (by wfin [Plan.words])
  · have l32' : ¬ Desc.leadingWidth fs < 4294967296 := l32
    psteps [l32']
    exact post_none (by wfin [])

/-! Progressive containers. -/

/-- Layout words of zero or one, read as flags and written back as words, are the words. -/
theorem bits_back : ∀ (bits : List Nat), (∀ b ∈ bits, b ≤ 1) →
    (bits.map (· != 0)).map (fun b => if b then 1 else 0) = bits
  | [], _ => rfl
  | b :: rest, small => by
    have hb := small b List.mem_cons_self
    have := bits_back rest (fun x hx => small x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, this⟩
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> rfl

/-- The flags set among layout words are the words other than zero. -/
theorem countP_bits : ∀ (bits : List Nat), (bits.map (· != 0)).countP (· == true) = bits.countP (· != 0)
  | [] => rfl
  | b :: rest => by
    simp only [List.map_cons, List.countP_cons, countP_bits rest]
    cases b <;> simp

/-- The words of a layout, each from where the layout's words begin. -/
theorem planAt_words {w : World} {mem : Memory} {p : Nat} (ws : List Nat)
    (acc : w.access p (8 * ws.length) = true)
    (h : ∀ i (hi : i < ws.length), readLE mem (p + 8 * i) 8 = UInt64.ofNat ws[i]) : PlanAt w mem p ws :=
  ⟨acc, fun i hi => by simpa using h i hi⟩

set_option maxHeartbeats 16000000 in
/-- A progressive container node checked backward: a layout of bits ending on a field, and its fields. -/
theorem tag11_back {m : Module} {w : World} (hm : Loaded m) : TagBack m w 11 := by
  back_open
  back_word
  by_cases ok : n ≠ 0 ∧ n ≤ 256 ∧ p + 24 + 8 * n ≤ stop
  case neg =>
    by_cases z : n = 0
    · psteps [z]
      exact post_none (by wfin [])
    by_cases big : n ≤ 256
    · have far : ¬ p + 24 + 8 * n ≤ stop := by omega
      psteps [z, big, far]
      exact post_none (by wfin [])
    · psteps [z, big]
      exact post_none (by wfin [])
  obtain ⟨n0, n256, sn⟩ := ok
  psteps [n0, n256, sn]
  -- The layout's words, one per position.
  let bits := (List.range n).map fun i => (readLE mem (p + 16 + 8 * i) 8).toNat
  have blen : bits.length = n := by simp [bits]
  have rbit : ∀ i (hi : i < n), readLE mem (p + 16 + 8 * i) 8 = UInt64.ofNat (bits[i]'(by omega)) := by
    intro i hi; simp [bits]
  have abit : ∀ i, i < n → w.access (p + 16 + 8 * i) 8 = true := fun i hi =>
    access_sub hacc (by omega) (by omega)
  have sbit : ∀ i (hi : i < n), bits[i]'(by omega) < 2 ^ 64 := fun i hi => by
    simpa [bits] using UInt64.toNat_lt (readLE mem (p + 16 + 8 * i) 8)
  have take_succ : ∀ i (hi : i < n), bits.take (i + 1) = bits.take i ++ [bits[i]'(by omega)] := fun i hi => by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]; rfl
  -- After i positions: the positions set so far, and whether every word so far is a bit.
  refine Pc.loop (fun env k => k = mem ∧ ∃ i, i ≤ n ∧ env 7 = UInt64.ofNat i ∧
      env 8 = UInt64.ofNat ((bits.take i).countP (· != 0)) ∧
      env 9 = (if (bits.take i).all (fun b => decide (b ≤ 1)) then 1 else 0) ∧ env 0 = UInt64.ofNat p ∧
      env 1 = UInt64.ofNat stop ∧ env 4 = UInt64.ofNat n ∧ env 3 = noneWord)
    ⟨rfl, 0, Nat.zero_le _, by wfin [], by wfin [], by wfin [], by wfin [], by wfin [], by wfin [], by wfin []⟩
    ?_ ?_
  · rintro env k v ⟨hk, i, hi, h7, h8, h9, h0, h1, h4, h3⟩ hv nz
    subst k
    have hin : i < n := by
      rcases Nat.lt_or_ge i n with h | h
      · exact h
      · have : eval w env mem (lt (Var.mk 7 : Expr) (Var.mk 4 : Expr)) = some 0 := by
          wev [h7, h4, show ¬ i < n by omega]
        rw [this] at hv
        exact absurd (Option.some.inj hv).symm nz
    have ct := List.countP_le_length (p := fun x => x != 0) (l := bits.take i)
    simp only [List.length_take] at ct
    have rb := rbit i hin
    have ab := abit i hin
    have sb := sbit i hin
    have cnt : (bits.take (i + 1)).countP (· != 0) =
        (bits.take i).countP (· != 0) + (if bits[i]'(by omega) = 0 then 0 else 1) := by
      rw [take_succ i hin, List.countP_append]
      by_cases z : bits[i]'(by omega) = 0 <;> simp [z]
    have all : (bits.take (i + 1)).all (fun b => decide (b ≤ 1)) =
        ((bits.take i).all (fun b => decide (b ≤ 1)) && decide (bits[i]'(by omega) ≤ 1)) := by
      rw [take_succ i hin, List.all_append]; simp
    by_cases b0 : bits[i]'(by omega) = 0
    · have b1 : ¬ 1 < bits[i]'(by omega) := by omega
      psteps [h0, h7, rb, ab, b0, b1]
      refine ⟨trivial, i + 1, by omega, by wfin [h7], by wfin [h8, cnt, b0], ?_, by wfin [h0], by wfin [h1],
        by wfin [h4], by wfin [h3]⟩
      rw [all]; simp [Asm.assign, h9, b0]
    · by_cases b1 : 1 < bits[i]'(by omega)
      · psteps [h0, h7, rb, ab, b0, b1, h8]
        refine ⟨trivial, i + 1, by omega, by wfin [h7], by wfin [h8, cnt, b0], ?_, by wfin [h0], by wfin [h1],
          by wfin [h4], by wfin [h3]⟩
        simp only [all, show decide (bits[i]'(by omega) ≤ 1) = false by simp; omega, Bool.and_false]
        simp [Asm.assign]
      · psteps [h0, h7, rb, ab, b0, b1, h8]
        refine ⟨trivial, i + 1, by omega, by wfin [h7], by wfin [h8, cnt, b0], ?_, by wfin [h0], by wfin [h1],
          by wfin [h4], by wfin [h3]⟩
        rw [all]; simp [Asm.assign, h9, show bits[i]'(by omega) ≤ 1 by omega]
  · rintro env k ⟨hk, i, hi, h7, h8, h9, h0, h1, h4, h3⟩ hv
    subst k
    have hin : i = n := by
      rcases Nat.lt_or_ge i n with h | h
      · have : eval w env mem (lt (Var.mk 7 : Expr) (Var.mk 4 : Expr)) = some 1 := by
          wev [h7, h4, h]
        rw [this] at hv
        cases hv
      · omega
    subst hin
    rw [List.take_of_length_le (by omega)] at h8 h9
    obtain ⟨c, hcdef⟩ : ∃ c, bits.countP (· != 0) = c := ⟨_, rfl⟩
    rw [hcdef] at h8
    have cn := List.countP_le_length (p := fun x => x != 0) (l := bits)
    -- The last position's word, and the field count after the layout.
    have rl : readLE mem (p + 8 + 8 * i) 8 = UInt64.ofNat (bits[i - 1]'(by omega)) := by
      have := rbit (i - 1) (by omega)
      rwa [show p + 16 + 8 * (i - 1) = p + 8 + 8 * i by omega] at this
    have al : w.access (p + 8 + 8 * i) 8 = true := access_sub hacc (by omega) (by omega)
    have sl := sbit (i - 1) (by omega)
    have ac : w.access (p + 16 + 8 * i) 8 = true := access_sub hacc (by omega) (by omega)
    obtain ⟨cw, cw64, rc⟩ := word_of mem (p + 16 + 8 * i)
    by_cases good : bits.all (fun b => decide (b ≤ 1)) = true ∧ bits[i - 1]'(by omega) ≠ 0 ∧ cw = c
    case neg =>
      by_cases f1 : bits.all (fun b => decide (b ≤ 1)) = true
      · by_cases f2 : bits[i - 1]'(by omega) = 0
        · psteps [h9, f1, h0, h4, rl, al, f2, rc, ac, h8]
          exact post_none (by wfin [h3])
        · have f3 : cw ≠ c := fun e => good ⟨f1, f2, e⟩
          psteps [h9, f1, h0, h4, rl, al, f2, rc, ac, h8, f3]
          exact post_none (by wfin [h3])
      · psteps [h9, f1, h0, h4, rl, al, rc, ac, h8]
        exact post_none (by wfin [h3])
    obtain ⟨f1, f2, rfl⟩ := good
    psteps [h9, f1, h0, h4, rl, al, f2, rc, ac, h8]
    have c256 : cw ≤ 256 := by omega
    pcall [h0, h4, h8, h1]
    intro q mem'' hc
    have keep := Calls.keeps hm.keeps (by simp [planNames]) hc
    subst mem''
    rcases planAll_back hm (by omega) (access_sub hacc (by omega) (by omega)) (by omega)
      (fun q hq => ih q (by omega)) hc with rfl | ⟨fs, hlen, sf, hf, hs, rfl⟩
    · psteps []
      exact post_none (by wfin [h3])
    subst hlen
    have qne : p + 24 + 8 * i + 8 * (Plan.wordsAll fs).length ≠ 18446744073709551615 := by omega
    psteps [qne]
    pcall [h0, h4, h8]
    intro lw mem'' hl
    obtain ⟨rfl, keep⟩ := leading_agree hm (sound_all sf).2.1 hf hl
    subst mem''
    have l64 := fields_small sf (by omega)
    by_cases l32 : Desc.leadingWidth fs < 2 ^ 32
    case neg =>
      have l32' : ¬ Desc.leadingWidth fs < 4294967296 := l32
      psteps [l32']
      exact post_none (by wfin [h3])
    have l32' : Desc.leadingWidth fs < 4294967296 := l32
    psteps [l32']
    obtain ⟨wfs, fit, nm⟩ := sound_all sf
    -- The layout read as flags, written back as the words read.
    have small : ∀ b ∈ bits, b ≤ 1 := by simpa using f1
    have back := bits_back bits small
    have alen : (bits.map (· != 0)).length = i := by simp [blen]
    have count : (bits.map (· != 0)).countP (· == true) = fs.length := by rw [countP_bits, hcdef]
    have last : (bits.map (· != 0)).getLast! = true := by
      rw [List.getLast!_eq_getElem!, alen, getElem!_pos _ _ (by simp [blen]; omega)]
      simp [f2]
    have fne : fs ≠ [] := by
      intro h
      have : 0 < bits.countP (· != 0) :=
        List.countP_pos_iff.mpr ⟨bits[i - 1]'(by omega), List.getElem_mem _, by simpa using f2⟩
      rw [hcdef, h] at this
      simp at this
    have e : Plan.words (.progressiveContainer (bits.map (· != 0)) (Plan.layoutNames (bits.map (· != 0))) fs) =
        11 :: i :: (bits ++ fs.length :: Plan.wordsAll fs) := by
      simp [Plan.words, back, alen]
    have hcount : PlanAt w mem (p + 16 + 8 * bits.length) (fs.length :: Plan.wordsAll fs) := by
      rw [blen]
      exact PlanAt.cons ac rc (hf.at_eq (by omega)) (access_sub hacc (by omega) (by omega))
    have hbits : PlanAt w mem (p + 16) bits :=
      planAt_words bits (access_sub hacc (by omega) (by simp [blen]; omega)) (fun j hj => rbit j (by omega))
    have hd : PlanAt w mem p (Plan.words (.progressiveContainer (bits.map (· != 0))
        (Plan.layoutNames (bits.map (· != 0))) fs)) := by
      rw [e]
      refine PlanAt.cons a0 tag (PlanAt.cons a1 rn ((PlanAt.append hbits hcount ?_).at_eq (by omega)) ?_) ?_
      · exact access_sub hacc (by omega) (by simp [blen]; omega)
      · exact access_sub hacc (by omega) (by simp [blen]; omega)
      · exact access_sub hacc (Nat.le_refl _) (by simp [blen]; omega)
    refine post_some (.progressiveContainer (bits.map (· != 0)) (Plan.layoutNames (bits.map (· != 0))) fs)
      ⟨(wellFormed_progressiveContainer_iff _ _ _).mpr ⟨fun h => by simp [h] at alen; omega, last, by simp [maxActiveFields]; omega, fne,
          count, by rw [Plan.layoutNames, List.length_map, Plan.length_layoutPositions, count],
          Ssz.firstDuplicate_of_nodup _ (Plan.layoutNames_nodup _), wfs⟩,
        by simp [named, nm], by simp [fitsNative, fit]; omega⟩ hd ?_ ?_
    · rw [e]; simp [blen]; omega
    · wfin [e, blen]

/-! Unions. -/

/-- A list whose entries all differ reports no duplicate. -/
theorem firstDuplicate_of_distinct : ∀ (l : List Nat), (∀ a < l.length, ∀ b < a, l[b]! ≠ l[a]!) →
    firstDuplicate l = none
  | [], _ => rfl
  | x :: rest, h => by
    simp only [firstDuplicate]
    rw [if_neg]
    · exact firstDuplicate_of_distinct rest fun a ha b hb => by
        simpa using h (a + 1) (by simp; omega) (b + 1) (by omega)
    · intro hc
      obtain ⟨k, hk, hx⟩ := List.getElem_of_mem (List.contains_iff_mem.mp hc)
      have := h (k + 1) (by simp; omega) 0 (by omega)
      simp only [getElem!_pos (x :: rest) 0 (by simp), getElem!_pos (x :: rest) (k + 1) (by simp; omega),
        List.getElem_cons_zero, List.getElem_cons_succ, hx] at this
      exact this rfl

/-- Every two of a union's selectors differ, and each lies in the reserved range, for the first so many. -/
def SelsOk (sels : List Nat) (i : Nat) : Prop :=
  (∀ k < i, 1 ≤ sels[k]! ∧ sels[k]! ≤ 127) ∧ ∀ a < i, ∀ b < a, sels[b]! ≠ sels[a]!

/-- One more selector is fine exactly when it lies in range and differs from every earlier one. -/
theorem selsOk_succ (sels : List Nat) (i : Nat) :
    SelsOk sels (i + 1) ↔ SelsOk sels i ∧ (1 ≤ sels[i]! ∧ sels[i]! ≤ 127) ∧ ∀ b < i, sels[b]! ≠ sels[i]! := by
  constructor
  · rintro ⟨r, d⟩
    exact ⟨⟨fun k hk => r k (by omega), fun a ha b hb => d a (by omega) b hb⟩, r i (by omega),
      fun b hb => d i (by omega) b hb⟩
  · rintro ⟨⟨r, d⟩, ri, di⟩
    refine ⟨fun k hk => ?_, fun a ha b hb => ?_⟩
    · rcases Nat.lt_or_ge k i with h | h
      · exact r k h
      · rw [show k = i by omega]; exact ri
    · rcases Nat.lt_or_ge a i with h | h
      · exact d a h b hb
      · rw [show a = i by omega]; exact di b (by omega)

/-- A union node checked backward: selectors in range and distinct, options compatible two by two. -/
theorem tag12_back {m : Module} {w : World} (hm : Loaded m) : TagBack m w 12 := by
  back_open
  back_word
  by_cases ok : n ≠ 0 ∧ n < 2 ^ 32 ∧ p + 16 + 8 * n ≤ stop
  case neg =>
    by_cases z : n = 0
    · psteps [z]
      exact post_none (by wfin [])
    by_cases big : n < 2 ^ 32
    · have far : ¬ p + 16 + 8 * n ≤ stop := by omega
      have big' : n < 4294967296 := big
      psteps [z, big', far]
      exact post_none (by wfin [])
    · have big' : ¬ n < 4294967296 := big
      psteps [z, big']
      exact post_none (by wfin [])
  obtain ⟨n0, n32, sn⟩ := ok
  have n32' : n < 4294967296 := n32
  psteps [n0, n32', sn]
  -- The selectors, one word each.
  let sels := (List.range n).map fun i => (readLE mem (p + 16 + 8 * i) 8).toNat
  have slen : sels.length = n := by simp [sels]
  have rsel : ∀ i, i < n → readLE mem (p + 16 + 8 * i) 8 = UInt64.ofNat sels[i]! := by
    intro i hi; rw [getElem!_pos sels i (by omega)]; simp [sels]
  have asel : ∀ i, i < n → w.access (p + 16 + 8 * i) 8 = true := fun i hi =>
    access_sub hacc (by omega) (by omega)
  have ssel : ∀ i, i < n → sels[i]! < 2 ^ 64 := fun i hi => by
    rw [getElem!_pos sels i (by omega)]
    simpa [sels] using UInt64.toNat_lt (readLE mem (p + 16 + 8 * i) 8)
  -- After i selectors, the flag stands exactly when they are all fine.
  refine Pc.loop (fun env k => k = mem ∧ ∃ i, i ≤ n ∧ env 7 = UInt64.ofNat i ∧
      (env 8 ≠ 0 → SelsOk sels i) ∧ (SelsOk sels i → env 8 = 1) ∧ env 0 = UInt64.ofNat p ∧
      env 1 = UInt64.ofNat stop ∧ env 4 = UInt64.ofNat n ∧ env 3 = noneWord)
    ⟨rfl, 0, Nat.zero_le _, by wfin [], fun _ => ⟨fun k hk => absurd hk (Nat.not_lt_zero _),
      fun a ha => absurd ha (Nat.not_lt_zero _)⟩, fun _ => by wfin [], by wfin [], by wfin [], by wfin [],
      by wfin []⟩ ?_ ?_
  · rintro env k v ⟨hk, i, hi, h7, c1, c2, h0, h1, h4, h3⟩ hv nz
    subst k
    have hin : i < n := by
      rcases Nat.lt_or_ge i n with h | h
      · exact h
      · have : eval w env mem (lt (Var.mk 7 : Expr) (Var.mk 4 : Expr)) = some 0 := by
          wev [h7, h4, show ¬ i < n by omega]
        rw [this] at hv
        exact absurd (Option.some.inj hv).symm nz
    have ri := rsel i hin
    have ai := asel i hin
    have si := ssel i hin
    pstep [h0, h7, ri, ai]
    -- After the range check, the flag stands exactly when the selectors so far and this one are fine.
    refine Pc.cut (fun e k => k = mem ∧ e 9 = UInt64.ofNat sels[i]! ∧ e 7 = UInt64.ofNat i ∧
        e 0 = UInt64.ofNat p ∧ e 1 = UInt64.ofNat stop ∧ e 4 = UInt64.ofNat n ∧ e 3 = noneWord ∧
        (e 8 ≠ 0 → SelsOk sels i ∧ 1 ≤ sels[i]! ∧ sels[i]! ≤ 127) ∧
        (SelsOk sels i ∧ 1 ≤ sels[i]! ∧ sels[i]! ≤ 127 → e 8 = 1)) ?_ ?_
    · refine Pc.ite fun v hv => ⟨fun nz => ?_, fun z => ?_⟩
      · by_cases hR : 1 ≤ sels[i]! ∧ sels[i]! ≤ 127
        · have lo : ¬ sels[i]! < 1 := by omega
          have hi' : ¬ 127 < sels[i]! := by omega
          have : eval w (Asm.assign env 9 (UInt64.ofNat sels[i]!)) mem
              (either (lt (Var.mk 9 : Expr) 1) (lt 127 (Var.mk 9 : Expr))) = some 0 := by wev [lo, hi']
          rw [this] at hv
          exact absurd (Option.some.inj hv).symm nz
        · psteps []
          exact ⟨trivial, by wfin [], by wfin [h7], by wfin [h0], by wfin [h1], by wfin [h4], by wfin [h3],
            fun h => (h (by simp [Asm.assign])).elim, fun h => absurd h.2 hR⟩
      · by_cases hR : 1 ≤ sels[i]! ∧ sels[i]! ≤ 127
        · refine Pc.done ⟨rfl, by wfin [], by wfin [h7], by wfin [h0], by wfin [h1], by wfin [h4], by wfin [h3],
            fun h => ⟨c1 (by simpa [Asm.assign] using h), hR⟩, fun h => by wfin [c2 h.1]⟩
        · have bad : sels[i]! < 1 ∨ 127 < sels[i]! := by omega
          have : eval w (Asm.assign env 9 (UInt64.ofNat sels[i]!)) mem
              (either (lt (Var.mk 9 : Expr) 1) (lt 127 (Var.mk 9 : Expr))) = some 1 := by
            rcases bad with b | b
            · wev [b]
            · wev [b]
          rw [this] at hv
          cases hv
          simp at z
    rintro e k ⟨hk, g9, g7, g0, g1, g4, g3, d1, d2⟩
    subst k
    pstep []
    -- After j earlier selectors, the flag stands exactly when all so far are fine and none of the j equals this one.
    refine Pc.loop (fun e k => k = mem ∧ ∃ j, j ≤ i ∧ e 10 = UInt64.ofNat j ∧ e 9 = UInt64.ofNat sels[i]! ∧
        e 7 = UInt64.ofNat i ∧ e 0 = UInt64.ofNat p ∧ e 1 = UInt64.ofNat stop ∧ e 4 = UInt64.ofNat n ∧
        e 3 = noneWord ∧
        (e 8 ≠ 0 → SelsOk sels i ∧ (1 ≤ sels[i]! ∧ sels[i]! ≤ 127) ∧ ∀ b < j, sels[b]! ≠ sels[i]!) ∧
        (SelsOk sels i ∧ (1 ≤ sels[i]! ∧ sels[i]! ≤ 127) ∧ (∀ b < j, sels[b]! ≠ sels[i]!) → e 8 = 1))
      ⟨rfl, 0, Nat.zero_le _, by wfin [], by wfin [g9], by wfin [g7], by wfin [g0], by wfin [g1], by wfin [g4],
        by wfin [g3], fun h => ⟨(d1 (by simpa [Asm.assign] using h)).1, (d1 (by simpa [Asm.assign] using h)).2,
          fun b hb => absurd hb (Nat.not_lt_zero _)⟩, fun h => by wfin [d2 ⟨h.1, h.2.1⟩]⟩ ?_ ?_
    · rintro e k v ⟨hk, j, hj, f10, f9, f7, f0, f1, f4, f3, e1, e2⟩ hv nz
      subst k
      have hji : j < i := by
        rcases Nat.lt_or_ge j i with h | h
        · exact h
        · have : eval w e mem (lt (Var.mk 10 : Expr) (Var.mk 7 : Expr)) = some 0 := by
            wev [f10, f7, show ¬ j < i by omega]
          rw [this] at hv
          exact absurd (Option.some.inj hv).symm nz
      have rj := rsel j (by omega)
      have aj := asel j (by omega)
      have sj := ssel j (by omega)
      by_cases dj : sels[j]! = sels[i]!
      · psteps [f0, f10, rj, aj, f9, dj]
        exact ⟨trivial, j + 1, by omega, by wfin [f10], by wfin [f9], by wfin [f7], by wfin [f0], by wfin [f1],
          by wfin [f4], by wfin [f3], fun h => (h (by simp [Asm.assign])).elim,
          fun h => absurd dj (h.2.2 j (by omega))⟩
      · psteps [f0, f10, rj, aj, f9, dj]
        refine ⟨trivial, j + 1, by omega, by wfin [f10], by wfin [f9], by wfin [f7], by wfin [f0], by wfin [f1],
          by wfin [f4], by wfin [f3], fun h => ?_, fun h => ?_⟩
        · obtain ⟨a, b, c⟩ := e1 (by simpa [Asm.assign] using h)
          refine ⟨a, b, fun b' hb' => ?_⟩
          rcases Nat.lt_or_ge b' j with h' | h'
          · exact c b' h'
          · rw [show b' = j by omega]; exact dj
        · simpa [Asm.assign] using e2 ⟨h.1, h.2.1, fun b' hb' => h.2.2 b' (by omega)⟩
    · rintro e k ⟨hk, j, hj, f10, f9, f7, f0, f1, f4, f3, e1, e2⟩ hv
      subst k
      have hji : j = i := by
        rcases Nat.lt_or_ge j i with h | h
        · have : eval w e mem (lt (Var.mk 10 : Expr) (Var.mk 7 : Expr)) = some 1 := by
            wev [f10, f7, h]
          rw [this] at hv
          cases hv
        · omega
      subst hji
      psteps [f7]
      refine ⟨trivial, j + 1, by omega, by wfin [f7], fun h => ?_, fun h => ?_, by wfin [f0], by wfin [f1],
        by wfin [f4], by wfin [f3]⟩
      · exact (selsOk_succ sels j).mpr (e1 (by simpa [Asm.assign] using h))
      · simpa [Asm.assign] using e2 ((selsOk_succ sels j).mp h)
  · rintro env k ⟨hk, i, hi, h7, c1, c2, h0, h1, h4, h3⟩ hv
    subst k
    have hin : i = n := by
      rcases Nat.lt_or_ge i n with h | h
      · have : eval w env mem (lt (Var.mk 7 : Expr) (Var.mk 4 : Expr)) = some 1 := by
          wev [h7, h4, h]
        rw [this] at hv
        cases hv
      · omega
    subst hin
    by_cases G : SelsOk sels i
    case neg =>
      have c0 : env 8 = 0 := by
        by_cases h : env 8 = 0
        · exact h
        · exact absurd (c1 h) G
      psteps [c0]
      exact post_none (by wfin [h3])
    have c8 := c2 G
    psteps [c8]
    pcall [h0, h4, h1]
    intro q mem'' hc
    have keep := Calls.keeps hm.keeps (by simp [planNames]) hc
    subst mem''
    rcases planAll_back hm (by omega) (access_sub hacc (by omega) (by omega)) (by omega)
      (fun q hq => ih q (by omega)) hc with rfl | ⟨opts, hlen, sf, hf, hs, rfl⟩
    · psteps []
      exact post_none (by wfin [h3])
    have qne : p + 16 + 8 * i + 8 * (Plan.wordsAll opts).length ≠ 18446744073709551615 := by omega
    psteps [qne]
    rw [← hlen] at h4
    pcall [h0, h4]
    intro pv mem'' hpv
    obtain ⟨rfl, keep⟩ := pairs_agree hm sf (hf.at_eq (by rw [hlen])) hpv
    subst mem''
    by_cases ap : allPairs opts = true
    case neg =>
      psteps [ap]
      exact post_none (by wfin [h3])
    psteps [ap]
    obtain ⟨wfs, fit, nm⟩ := sound_all sf
    have mem_sel : ∀ s ∈ sels, (1 ≤ s ∧ s ≤ 127) ∧ s < 2 ^ 64 := by
      intro s hs
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hs
      have r := G.1 k (by omega)
      have b := ssel k (by omega)
      rw [getElem!_pos sels k hk] at r b
      exact ⟨r, b⟩
    have hsels : PlanAt w mem (p + 16) sels :=
      planAt_words sels (access_sub hacc (by omega) (by simp [slen]; omega))
        (fun j hj => by have := rsel j (by omega); rwa [getElem!_pos sels j hj] at this)
    have e : Plan.words (.compatibleUnion sels opts) = 12 :: opts.length :: (sels ++ Plan.wordsAll opts) := by
      simp [Plan.words]
    refine post_some (.compatibleUnion sels opts)
      ⟨(Ssz.wellFormed_compatibleUnion_iff sels opts).mpr ⟨fun h => by simp [h] at slen; omega,
          fun h => by simp [h] at hlen; omega, by omega,
          firstDuplicate_of_distinct sels (fun a ha b hb => G.2 a (by omega) b hb),
          List.find?_eq_none.mpr (fun s hs => by
            have := (mem_sel s hs).1
            simp [minSelector, maxSelector]; omega),
          wfs, (optionsCompatible_iff sels opts).mpr ap⟩,
        by simp [named, nm],
        by simp only [fitsNative, fit, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true]
           exact ⟨⟨⟨trivial, by omega⟩, by omega⟩, fun s hs => (mem_sel s hs).2⟩⟩ ?_ ?_ ?_
    · rw [e]
      refine PlanAt.cons a0 tag (PlanAt.cons a1 (by rw [hlen]; exact rn)
        ((PlanAt.append hsels ?_ ?_).at_eq (by omega)) ?_) ?_
      · exact hf.at_eq (by rw [slen])
      · exact access_sub hacc (by omega) (by simp [slen]; omega)
      · exact access_sub hacc (by omega) (by simp [slen]; omega)
      · exact access_sub hacc (Nat.le_refl _) (by simp [slen]; omega)
    · rw [e]; simp [slen]; omega
    · wfin [e, slen]

/-! Any node. -/

/-- A node with no known tag is refused. -/
theorem tagOther_back {m : Module} {w : World} (hm : Loaded m) (k : Nat) (big : 13 ≤ k) (k64 : k < 2 ^ 64) :
    TagBack m w k := by
  back_open
  have t0 : k ≠ 0 := by omega
  have t5 : ¬ k ≤ 5 := by omega
  have t6 : k ≠ 6 := by omega
  have t7 : k ≠ 7 := by omega
  have t8 : k ≠ 8 := by omega
  have t9 : k ≠ 9 := by omega
  have t10 : k ≠ 10 := by omega
  have t11 : k ≠ 11 := by omega
  have t12 : k ≠ 12 := by omega
  psteps [tag, t0, t5, t6, t7, t8, t9, t10, t11, t12]
  exact post_none (by wfin [])

/-- A check of one node that happened returned the word for none, or the address past a sound type's words there. -/
theorem plan_back {m : Module} {w : World} (hm : Loaded m) (stop : Nat) : ∀ p, PlanBack m w p stop := by
  intro p
  induction h : stop - p using Nat.strongRecOn generalizing p with
  | _ n ih =>
    intro hps hacc sp mem r mem' call
    have next : ∀ q, p < q → PlanBack m w q stop := fun q hq hqs hacc' =>
      ih (stop - q) (by omega) q rfl hqs hacc'
    obtain ⟨t, t64, rt⟩ := word_of mem p
    have go : TagBack m w t := by
      rcases (show t ≤ 12 ∨ 13 ≤ t by omega) with small | big
      · rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨
            t = 11 ∨ t = 12 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact tag0_back hm
        · exact tag1_back hm
        · exact tag2_back hm
        · exact tag3_back hm
        · exact tag4_back hm
        · exact tag5_back hm
        · exact tag6_back hm
        · exact tag7_back hm
        · exact tag8_back hm
        · exact tag9_back hm
        · exact tag10_back hm
        · exact tag11_back hm
        · exact tag12_back hm
      · exact tagOther_back hm t big t64
    exact go p stop sp mem r mem' hps hacc rt next call

end Ssz.Native.Driver.Validate
