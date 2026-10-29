import SszNative.Proofs.Driver.Validate.Main
import SszNative.Proofs.Ir.Partial

/-!
The plan's own check, read backward: what it accepts is the plan of a legal type.

The plan's check and every routine it calls only read memory, and call only one another.
So a call of one of them that happened returns what the forward proof of that call says, whatever stack it had.
-/

namespace Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open Ssz Ssz.Native Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Ir.Stmt Ssz.Native.Ir.Expr

/-- The routines the plan's check reaches. -/
def planNames : List String :=
  ["ssz_check_plan", "ssz_validate_depth", "ssz_validate_depth_all", "ssz_validate_plan", "ssz_validate_plan_all",
    "ssz_validate_width", "ssz_validate_fields_width", "ssz_validate_leading", "ssz_validate_skip",
    "ssz_validate_skip_all", "ssz_validate_pairs", "ssz_validate_compat", "ssz_validate_compat_all",
    "ssz_validate_eq", "ssz_validate_bytes", "ssz_validate_options_agree", "ssz_validate_layouts"]

/-- Each routine the plan's check reaches writes nothing and calls only routines it reaches. -/
theorem planNames_keep : planNames.all (fun f => match fns.lookup f with
    | some fn => !fn.body.stores && fn.body.callees.all (planNames.contains ·)
    | none => false) = true := by decide +kernel

/-- A name found in a list of pairs is paired there with what it finds. -/
theorem mem_of_lookup {α : Type} : ∀ (l : List (String × α)) (f : String) (a : α), l.lookup f = some a → (f, a) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (g, b) :: rest, f, a, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i e
      simp only [Option.some.injEq] at h
      have : f = g := by simpa using e
      subst this h
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_of_lookup rest f a h)

/-- The routines the plan's check reaches keep memory, in a module holding the check. -/
theorem Loaded.keeps {m : Module} (hm : Loaded m) : Keeps m planNames := by
  intro f hf
  have all := List.all_eq_true.mp planNames_keep f hf
  cases look : fns.lookup f with
  | none => simp [look] at all
  | some fn =>
    simp only [look, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.contains_iff_mem] at all
    exact ⟨fn, hm _ (mem_of_lookup fns f fn look), all.1, all.2⟩

/-! What a call that happened returned, from the forward proofs. -/

/-- A width read that happened returned the type's width word. -/
theorem width_agree {m : Module} {w : World} (hm : Loaded m) {e : Desc} (fit : fitsNative e = true) {p sp : Nat}
    {mem mem' : Memory} {r : UInt64} (hp : PlanAt w mem p (Plan.words e))
    (c : Calls m w "ssz_validate_width" sp [UInt64.ofNat p] mem r mem') :
    r = UInt64.ofNat (widthWord e) ∧ mem' = mem :=
  Calls.agree hm.keeps.closed (by simp [planNames]) c
    (width_calls hm e fit p (w.stackLo + e.nesting * 5120 + 2 * 160) mem hp (Nat.le_refl _))

/-- A leading-width read that happened returned the fields' leading width. -/
theorem leading_agree {m : Module} {w : World} (hm : Loaded m) {fs : List Desc} (fit : allFitNative fs = true)
    {p sp : Nat} {mem mem' : Memory} {r : UInt64} (hp : PlanAt w mem p (Plan.wordsAll fs))
    (c : Calls m w "ssz_validate_leading" sp [UInt64.ofNat p, UInt64.ofNat fs.length] mem r mem') :
    r = UInt64.ofNat (Desc.leadingWidth fs) ∧ mem' = mem :=
  Calls.agree hm.keeps.closed (by simp [planNames]) c
    (leading_calls hm fs fit p (w.stackLo + (Desc.deepestNesting fs + 1) * 5120 + 1 * 160) mem hp (Nat.le_refl _))

/-- A check of every pair of options that happened answered whether each fits every later one. -/
theorem pairs_agree {m : Module} {w : World} (hm : Loaded m) {os : List Desc} (so : ∀ f ∈ os, Sound f)
    {p sp : Nat} {mem mem' : Memory} {r : UInt64} (hp : PlanAt w mem p (Plan.wordsAll os))
    (c : Calls m w "ssz_validate_pairs" sp [UInt64.ofNat p, UInt64.ofNat os.length] mem r mem') :
    r = (if allPairs os then 1 else 0) ∧ mem' = mem :=
  Calls.agree hm.keeps.closed (by simp [planNames]) c
    (pairs_calls hm os so p (w.stackLo + (2 * (Desc.deepestNesting os + 1)) * 5120 + 1 * 160) mem hp (Nat.le_refl _))

/-! The nesting walk of a type nested deeper than its budget. -/

/-- The word the nesting walk returns for a plan nested too deeply. -/
abbrev tooDeep : Nat := 18446744073709551614

/-- The first of a list's types nested deeper than a budget, when the deepest is. -/
theorem first_deep : ∀ (fs : List Desc) (b : Nat), b < Desc.deepestNesting fs →
    ∃ j, ∃ hj : j < fs.length, b < fs[j].nesting ∧ ∀ i (hi : i < j), fs[i].nesting ≤ b
  | [], _, h => by simp [Desc.deepestNesting] at h
  | f :: rest, b, h => by
    simp only [Desc.deepestNesting] at h
    by_cases hf : b < f.nesting
    · exact ⟨0, by simp, hf, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · obtain ⟨j, hj, deep, before⟩ := first_deep rest b (by omega)
      refine ⟨j + 1, by simp; omega, by simpa using deep, fun i hi => ?_⟩
      cases i with
      | zero => simp; omega
      | succ i => simpa using before i (by omega)

/-- What the nesting walk of a node computes, for a legal type nested deeper than its budget: the word for too deep. -/
def DeepOk (m : Module) (w : World) (d : Desc) : Prop :=
  d.wellFormed = .ok () → fitsNative d = true →
    ∀ (p stop b sp : Nat) (mem : Memory), PlanAt w mem p (Plan.words d) → p + 8 * (Plan.words d).length ≤ stop →
      stop ≤ 2 ^ 63 → b < d.nesting → b < 2 ^ 64 → Room w sp (2 * b + 2) 2 →
      Calls m w "ssz_validate_depth" sp [UInt64.ofNat p, UInt64.ofNat stop, UInt64.ofNat b] mem
        (UInt64.ofNat tooDeep) mem

set_option maxHeartbeats 4000000 in
/-- The nesting walk of a count of legal nodes, one nested deeper than the budget, returns the word for too deep. -/
theorem depthAll_deep {m : Module} {w : World} (hm : Loaded m) (fs : List Desc) (ihd : ∀ f ∈ fs, DepthOk m w f)
    (ihx : ∀ f ∈ fs, DeepOk m w f) (wf : Desc.allWellFormed fs = .ok ()) (fit : allFitNative fs = true)
    (p stop b sp : Nat) (mem : Memory) (hp : PlanAt w mem p (Plan.wordsAll fs))
    (hs : p + 8 * (Plan.wordsAll fs).length ≤ stop) (hstop : stop ≤ 2 ^ 63) (deep : b < Desc.deepestNesting fs)
    (b64 : b < 2 ^ 64) (room : Room w sp (2 * b + 3) 1) :
    Calls m w "ssz_validate_depth_all" sp [UInt64.ofNat p, UInt64.ofNat fs.length, UInt64.ofNat stop, UInt64.ofNat b]
      mem (UInt64.ofNat tooDeep) mem := by
  have hb := hp.bound
  have hl := length_le_wordsAll fs
  obtain ⟨j, hj, jdeep, before⟩ := first_deep fs b deep
  refine Calls.body 7 hm.depthAll rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [depthAllFn]
  -- Before the deep node the walk stands past the nodes so far; after it, it holds the word for too deep.
  refine Wp.single (Wp.loop (wp_loop (fun env mem' => mem' = mem ∧ env 2 = UInt64.ofNat stop ∧
      env 3 = UInt64.ofNat b ∧
      ((∃ i, i ≤ j ∧ env 0 = UInt64.ofNat (p + 8 * (Plan.wordsAll (fs.take i)).length) ∧
        env 1 = UInt64.ofNat (fs.length - i)) ∨
       (env 0 = UInt64.ofNat tooDeep ∧ ∃ k, k < fs.length ∧ env 1 = UInt64.ofNat k)))
    (fun env _ => (env 1).toNat)
    ⟨rfl, by wfin [], by wfin [], Or.inl ⟨0, Nat.zero_le _, by wfin [Plan.wordsAll], by wfin []⟩⟩ ?_))
  rintro env mem' ⟨hmem, h2, h3, ⟨i, hi, h0, h1⟩ | ⟨h0, k, hk, h1⟩⟩
  · subst mem'
    have hil := wordsAll_take_le fs i
    have inside : p + 8 * (Plan.wordsAll (fs.take i)).length ≤ stop := by omega
    refine ⟨_, by wev [h0, h1, h2, inside, show fs.length - i ≠ 0 by omega], fun _ => ?_, fun z => ?_⟩
    · obtain ⟨_, hpi, slen⟩ := fieldAt hp i (by omega)
      rcases Nat.lt_or_ge i j with lt | ge
      · have nest := before i lt
        have step := ihd fs[i] (List.getElem_mem _) (allWellFormed_mem fs wf _ (List.getElem_mem _))
          (fits_getElem fs fit i (by omega)) _ stop b (sp - 8 - 8 * 7) mem hpi (by omega) hstop nest b64
          (by simp only [Room] at room ⊢; omega)
        wcall step [h0, h2, h3]
        wsteps [h1]
        refine ⟨⟨trivial, by wfin [h2], by wfin [h3], Or.inl ⟨i + 1, by omega, ?_, by wfin []⟩⟩, by wfin [h1]⟩
        wfin [take_succ_append fs i (by omega), wordsAll_append, Plan.wordsAll]
      · have eij : i = j := by omega
        subst eij
        have step := ihx fs[i] (List.getElem_mem _) (allWellFormed_mem fs wf _ (List.getElem_mem _))
          (fits_getElem fs fit i (by omega)) _ stop b (sp - 8 - 8 * 7) mem hpi (by omega) hstop jdeep b64
          (by simp only [Room] at room ⊢; omega)
        wcall step [h0, h2, h3]
        wsteps [h1]
        exact ⟨⟨trivial, by wfin [h2], by wfin [h3], Or.inr ⟨by wfin [], fs.length - i - 1, by omega, by wfin []⟩⟩,
          by wfin [h1]⟩
    · cases z
  · subst mem'
    have big : ¬ 18446744073709551614 ≤ stop := by omega
    refine ⟨_, by wev [h0, h1, h2, big, tooDeep], fun nz => ?_, fun _ => ?_⟩
    · simp at nz
    · exact Wp.done ⟨by wonly [h0], rfl⟩

set_option hygiene false in
/-- Opens a proof about one node of the nesting walk, past its budget. -/
macro "deep_open" : tactic => `(tactic| (
  intro wf fit p stop b sp mem hp hs hstop deep b64 room
  have hb := hp.bound
  have r0 := hp.read0 (words_length_pos _)
  have a0 := hp.readable0 (words_length_pos _)
  rw [words_head] at r0
  simp only [Plan.tag] at r0
  simp [Plan.words] at hb a0 hs
  have s8 : p + 8 ≤ stop := by omega
  refine Calls.body 11 hm.depth rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [depthFn]))

set_option hygiene false in
/-- Settles a node of the nesting walk whose budget is spent. -/
macro "deep_spent" : tactic => `(tactic| (
  wsteps [r0, a0, s8]
  refine Wp.single ?_
  wsteps [deep_]
  wfin [tooDeep]))

set_option maxHeartbeats 16000000 in
/-- The nesting walk of a legal type's plan, nested deeper than its budget, returns the word for too deep. -/
theorem depth_deep {m : Module} {w : World} (hm : Loaded m) (d : Desc) : DeepOk m w d := by
  induction d using Desc.rec (motive_2 := fun fs => ∀ f ∈ fs, DeepOk m w f) with
  | nil => rename_i h; simp at h
  | cons f fs ihf ihfs =>
    rename_i g h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ihf
    · exact ihfs g h
  | bool | uint _ | byteVector _ | byteList _ | bitVector _ | bitList _ | progressiveBitList _ =>
    deep_open
    have b0 : b = 0 := by simp only [Desc.nesting] at deep; omega
    subst b0
    deep_spent
  | vector e _ ih | list e _ ih =>
    deep_open
    rcases Nat.eq_zero_or_pos b with b0 | bpos
    · subst b0; deep_spent
    have we : e.wellFormed = .ok () := by
      first
      | (simp [Desc.wellFormed, ite_ok, throw_ok, bind_unit_ok] at wf; exact wf.2 wf.1)
      | simpa [Desc.wellFormed] using wf
    have fe : fitsNative e = true := by
      simp only [fitsNative, Bool.and_eq_true] at fit
      first | exact fit.1.1 | exact fit.1
    have he : PlanAt w mem (p + 16) (Plan.words e) := by
      first
      | (have := hp.right (a := [7, _]) (b := Plan.words e); simpa using this)
      | (have := hp.right (a := [8, _]) (b := Plan.words e); simpa using this)
    have step := ih we fe (p + 16) stop (b - 1) (sp - 8 - 8 * 11) mem he (by omega) hstop
      (by simp only [Desc.nesting] at deep; omega) (by omega) (by simp only [Room] at room ⊢; omega)
    have s16 : p + 16 ≤ stop := by omega
    have b0 : b ≠ 0 := by omega
    wsteps [r0, a0, s8, b0, s16]
    wcall step []
    wsteps []
    wfin []
  | progressiveList e limit ih =>
    deep_open
    rcases Nat.eq_zero_or_pos b with b0 | bpos
    · subst b0; deep_spent
    have we : e.wellFormed = .ok () := by simpa [Desc.wellFormed] using wf
    have fe : fitsNative e = true := by simp [fitsNative] at fit; exact fit.1
    have he : PlanAt w mem (p + 24) (Plan.words e) := by
      have := hp.right (a := 9 :: Plan.bound limit) (b := Plan.words e); simpa using this
    have step := ih we fe (p + 24) stop (b - 1) (sp - 8 - 8 * 11) mem he (by omega) hstop
      (by simp only [Desc.nesting] at deep; omega) (by omega) (by simp only [Room] at room ⊢; omega)
    have s24 : p + 24 ≤ stop := by omega
    have b0 : b ≠ 0 := by omega
    wsteps [r0, a0, s8, b0, s24]
    wcall step []
    wsteps []
    wfin []
  | container names fs ih =>
    deep_open
    rcases Nat.eq_zero_or_pos b with b0 | bpos
    · subst b0; deep_spent
    have r1 := hp.read 8 rfl (by simp [Plan.words] <;> omega)
    have a1 := hp.readable 8 rfl (by simp [Plan.words] <;> omega)
    simp [Plan.words] at r1
    simp [Desc.wellFormed, ite_ok, throw_ok, bind_unit_ok] at wf
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
    have hf : PlanAt w mem (p + 16) (Plan.wordsAll fs) := by
      have := hp.right (a := [10, fs.length]) (b := Plan.wordsAll fs); simpa using this
    have wfs : Desc.allWellFormed fs = .ok () := (wf.2 wf.1).1 (wf.2 wf.1).2 |>.2 ((wf.2 wf.1).1 (wf.2 wf.1).2).1
    have pa := depthAll_deep hm fs (fun f _ => depth_calls hm f) ih wfs fit.1.1 (p + 16) stop (b - 1)
      (sp - 8 - 8 * 11) mem hf (by omega) hstop (by simp only [Desc.nesting] at deep; omega) (by omega)
      (by simp only [Room] at room ⊢; omega)
    have s16 : p + 16 ≤ stop := by omega
    have b0 : b ≠ 0 := by omega
    wsteps [r0, a0, s8, b0, s16]
    wcall pa [r1, a1]
    wsteps []
    wfin []
  | progressiveContainer active names fs ih =>
    deep_open
    rcases Nat.eq_zero_or_pos b with b0 | bpos
    · subst b0; deep_spent
    have r1 := hp.read 8 rfl (by simp [Plan.words] <;> omega)
    have a1 := hp.readable 8 rfl (by simp [Plan.words] <;> omega)
    simp [Plan.words] at r1
    simp [Desc.wellFormed, ite_ok, throw_ok, bind_unit_ok, maxActiveFields] at wf
    obtain ⟨ane, wf⟩ := wf
    obtain ⟨last, wf⟩ := wf ane
    obtain ⟨a256, wf⟩ := wf last
    obtain ⟨fne, wf⟩ := wf a256
    obtain ⟨wf, cnt⟩ := wf fne
    obtain ⟨wf, nlen⟩ := wf cnt
    have wfs : Desc.allWellFormed fs = .ok () := (wf nlen).2 (wf nlen).1
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
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
    have rn : readLE mem (p + 16 + 8 * active.length) 8 = UInt64.ofNat fs.length := by
      have := hp.read (16 + 8 * active.length) (by omega) (by rw [hlen]; omega)
      rw [Nat.add_assoc, this, show (16 + 8 * active.length) / 8 = active.length + 2 by omega, e]
      simp only [getElem!_def, List.append_assoc]
      rw [List.getElem?_append_right (by simp)]
      simp
    have an : w.access (p + 16 + 8 * active.length) 8 = true := by
      have := hp.readable (16 + 8 * active.length) (by omega) (by rw [hlen]; omega)
      rwa [← Nat.add_assoc] at this
    have pa := depthAll_deep hm fs (fun f _ => depth_calls hm f) ih wfs fit.1.1 (p + 24 + 8 * active.length) stop
      (b - 1) (sp - 8 - 8 * 11) mem hf (by omega) hstop
      (by simp only [Desc.nesting] at deep; omega) (by omega) (by simp only [Room] at room ⊢; omega)
    have s16 : p + 16 ≤ stop := by omega
    have s24 : p + 24 + 8 * active.length ≤ stop := by omega
    have k32 : active.length < 4294967296 := by omega
    have b0 : b ≠ 0 := by omega
    wsteps [r0, a0, s8, b0, r1, a1, s16, k32, s24]
    wcall pa [rn, an]
    wsteps []
    wfin []
  | compatibleUnion sels opts ih =>
    deep_open
    rcases Nat.eq_zero_or_pos b with b0 | bpos
    · subst b0; deep_spent
    have r1 := hp.read 8 rfl (by simp [Plan.words] <;> omega)
    have a1 := hp.readable 8 rfl (by simp [Plan.words] <;> omega)
    simp [Plan.words] at r1
    obtain ⟨_, lens, _, _, wfs, _⟩ := wf_union sels opts wf
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at fit
    obtain ⟨⟨⟨fa, n32⟩, slen⟩, _⟩ := fit
    have e : Plan.words (.compatibleUnion sels opts) = ([12, opts.length] ++ sels) ++ Plan.wordsAll opts := by
      simp [Plan.words]
    have hlen : (Plan.words (.compatibleUnion sels opts)).length = 2 + opts.length + (Plan.wordsAll opts).length := by
      rw [e]; simp [slen]; omega
    have hf : PlanAt w mem (p + 16 + 8 * opts.length) (Plan.wordsAll opts) := by
      have hp' := hp; rw [e] at hp'
      refine hp'.right.at_eq ?_
      simp [slen]; omega
    have pa := depthAll_deep hm opts (fun f _ => depth_calls hm f) ih wfs fa (p + 16 + 8 * opts.length) stop (b - 1)
      (sp - 8 - 8 * 11) mem hf (by omega) hstop (by simp only [Desc.nesting] at deep; omega) (by omega)
      (by simp only [Room] at room ⊢; omega)
    have s16 : p + 16 ≤ stop := by omega
    have sn : p + 16 + 8 * opts.length ≤ stop := by omega
    have b0 : b ≠ 0 := by omega
    wsteps [r0, a0, s8, b0, r1, a1, s16, n32, sn]
    wcall pa []
    wsteps []
    wfin []

end Ssz.Native.Driver.Validate
