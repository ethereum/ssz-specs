import SszNative.Proofs.Driver.Validate.Width

/-!
Whether a type leaves probes, read from its plan.

A type whose values decode from any bytes of their width needs no byte of them looked at.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr

/-- One when a type leaves probes, and zero otherwise. -/
def probeBit (d : Desc) : Nat := if plan d = [] then 0 else 1

/-- One when any of a list of fields leaves probes. -/
def anyBit (fs : List Desc) : Nat := if ∀ f ∈ fs, plan f = [] then 0 else 1

/-- Moving probes leaves none exactly when there were none. -/
theorem shiftAll_eq_nil (off : Nat) (ps : List Probe) : shiftAll off ps = [] ↔ ps = [] := by
  cases ps <;> simp [shiftAll]

/-- Repeating probes leaves none exactly when there were none or no records. -/
theorem repeatProbes_eq_nil (ps : List Probe) (w : Nat) :
    ∀ i n, repeatProbes ps w i n = [] ↔ ps = [] ∨ n = 0
  | _, 0 => by simp [repeatProbes]
  | i, n + 1 => by
    simp only [repeatProbes, List.append_eq_nil_iff, shiftAll_eq_nil, repeatProbes_eq_nil ps w (i + 1) n]
    constructor
    · rintro ⟨h, _⟩; exact Or.inl h
    · rintro (h | h)
      · exact ⟨h, Or.inl h⟩
      · simp at h

/-- A struct leaves no probes exactly when none of its fields does. -/
theorem fieldsPlan_eq_nil : ∀ (fs : List Desc) (off : Nat), fieldsPlan fs off = [] ↔ ∀ f ∈ fs, plan f = []
  | [], _ => by simp [fieldsPlan]
  | f :: fs, off => by
    rw [fieldsPlan_cons]
    simp only [List.append_eq_nil_iff, shiftAll_eq_nil, fieldsPlan_eq_nil fs, List.mem_cons, forall_eq_or_imp]

/-- What reading whether a node leaves probes computes. -/
def ProbesOk (m : Module) (w : World) (d : Desc) : Prop :=
  fitsNative d = true → ∀ (p sp : Nat) (mem : Memory), PlanAt w mem p (Plan.words d) → Room w sp d.nesting 2 →
    Calls m w "ssz_validate_has_probes" sp [UInt64.ofNat p] mem (UInt64.ofNat (probeBit d)) mem

/-- Whether any of a count of fields leaves probes, stopping at the first that does. -/
theorem anyProbes_calls {m : Module} {w : World} (hm : Loaded m) (fs : List Desc)
    (ih : ∀ f ∈ fs, ProbesOk m w f) (fit : allFitNative fs = true)
    (p sp : Nat) (mem : Memory) (hp : PlanAt w mem p (Plan.wordsAll fs))
    (room : Room w sp (Desc.deepestNesting fs + 1) 1) :
    Calls m w "ssz_validate_any_probes" sp [UInt64.ofNat p, UInt64.ofNat fs.length] mem
      (UInt64.ofNat (anyBit fs)) mem := by
  have hb := hp.bound
  have hl := length_le_wordsAll fs
  refine Calls.body 5 hm.anyProbes rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [anyProbesFn]
  apply Wp.set (by wev [])
  refine Wp.loop (wp_loop (fun env mem' => mem' = mem ∧
      ((∃ j, j ≤ fs.length ∧ (∀ f ∈ fs.take j, plan f = []) ∧
        env 0 = UInt64.ofNat (p + 8 * (Plan.wordsAll (fs.take j)).length) ∧
        env 1 = UInt64.ofNat (fs.length - j) ∧ env 2 = 0) ∨
      (env 1 = 0 ∧ env 2 = 1 ∧ ¬ ∀ f ∈ fs, plan f = [])))
    (fun env _ => (env 1).toNat) ⟨rfl, Or.inl ⟨0, Nat.zero_le _, by simp,
      by simp [entryEnv, Asm.assign, Plan.wordsAll], by simp [entryEnv, Asm.assign], by simp [Asm.assign]⟩⟩ ?_)
  rintro env mem' ⟨hmem, inv⟩
  subst hmem
  rcases inv with ⟨j, hj, none, h0, h1, h2⟩ | ⟨h1, h2, some⟩
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
      have skip := skip_calls hm fs[j] (fits_getElem fs fit j hjf) _ _ mem' hpj hroom
      by_cases has : plan fs[j] = []
      · simp only [probeBit, ite_eq_left has] at step
        wcall step [h0]
        wsteps [h0, h1, h2]
        wcall skip [h0]
        wsteps [h1]
        refine ⟨⟨trivial, Or.inl ⟨j + 1, by omega, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
        · rw [take_succ_append fs j hjf]
          intro f hf
          simp only [List.mem_append, List.mem_singleton] at hf
          rcases hf with hf | rfl
          · exact none f hf
          · exact has
        · wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
        · wfin []
        · wfin []
        · wfin [h1]
      · simp only [probeBit, ite_eq_right has] at step
        wcall step [h0]
        wsteps [h0, h1, h2]
        refine ⟨⟨trivial, Or.inr ⟨by wfin [], by wfin [], fun all => has (all _ (List.getElem_mem hjf))⟩⟩, ?_⟩
        wfin [h1]
    · have hjk : j = fs.length := by
        rcases Nat.lt_or_ge j fs.length with h | h
        · simp [show fs.length - j ≠ 0 by omega] at z
        · omega
      subst hjk
      simp only [List.take_length] at none
      exact Wp.done ⟨by simp only [anyBit, ite_eq_left none]; wonly [h2], rfl⟩
  · refine ⟨0, by wonly [h1], fun nz => absurd rfl nz, fun _ => Wp.done ⟨by wonly [anyBit, some, h2], rfl⟩⟩

/-- Reading whether a node leaves probes gives one exactly when it does. -/
theorem hasProbes_calls {m : Module} {w : World} (hm : Loaded m) (d : Desc) : ProbesOk m w d := by
  induction d using Desc.rec (motive_2 := fun fs => ∀ f ∈ fs, ProbesOk m w f) with
  | nil => rename_i h; simp at h
  | cons f fs ihf ihfs =>
    rename_i g h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ihf
    · exact ihfs g h
  | bool =>
    node_open
    refine Calls.body 7 hm.hasProbes rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [hasProbesFn]
    wsteps [r0, a0]
    wfin [probeBit, plan]
  | uint _ | byteVector _ | byteList _ | bitList _ | progressiveBitList _ | list _ _ _ | progressiveList _ _ _
  | compatibleUnion _ _ _ =>
    node_open
    refine Calls.body 7 hm.hasProbes rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [hasProbesFn]
    wsteps [r0, a0]
    wfin [probeBit, plan]
  | bitVector n =>
    node_open
    node_word
    simp [fitsNative] at fit
    refine Calls.body 7 hm.hasProbes rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [hasProbesFn]
    wsteps [r0, a0, r1, a1]
    by_cases h : n % 8 = 0
    · have bit : probeBit (.bitVector n) = 0 := by simp [probeBit, plan, h]
      rw [bit]; wfin [h]
    · have : 0 < (n + 7) / 8 := by omega
      have bit : probeBit (.bitVector n) = 1 := by simp [probeBit, plan, h, this]
      rw [bit]; wfin [h]
  | vector e n ih =>
    node_open
    node_word
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
    have he : PlanAt w mem (p + 16) (Plan.words e) := by
      have := hp.right (a := [7, n]) (b := Plan.words e); simpa using this
    refine Calls.body 7 hm.hasProbes rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [hasProbesFn]
    wsteps [r0, a0, r1, a1]
    by_cases hn : n = 0
    · subst hn
      wsteps [r1, a1]
      wfin [probeBit, plan_vector, repeatProbes_eq_nil]
    · have step := ih fit.1.1 (p + 16) (sp - 8 - 8 * 7) mem he (by simp only [Room, Desc.nesting] at room ⊢; omega)
      wsteps [r1, a1, hn]
      wcall step []
      wsteps []
      wfin [probeBit, plan_vector, repeatProbes_eq_nil, hn]
  | container names fs ih =>
    node_open
    node_word
    have hf : PlanAt w mem (p + 16) (Plan.wordsAll fs) := by
      have := hp.right (a := [10, fs.length]) (b := Plan.wordsAll fs); simpa using this
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
    have step := anyProbes_calls hm fs ih fit.1.1 (p + 16) (sp - 8 - 8 * 7) mem hf
      (by simp only [Room, Desc.nesting] at room ⊢; omega)
    refine Calls.body 7 hm.hasProbes rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [hasProbesFn]
    wsteps [r0, a0, r1, a1]
    wcall step [r1, a1]
    wsteps []
    wfin [probeBit, anyBit, plan, fieldsPlan_eq_nil]
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
    have step := anyProbes_calls hm fs ih fit.1.1 (p + 24 + 8 * active.length) (sp - 8 - 8 * 7) mem hf
      (by simp only [Room, Desc.nesting] at room ⊢; omega)
    refine Calls.body 7 hm.hasProbes rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [hasProbesFn]
    wsteps [r0, a0, r1, a1, r2', a2]
    wcall step [r1, a1, r2', a2]
    wsteps []
    wfin [probeBit, anyBit, plan, fieldsPlan_eq_nil]
    all_goals congr 1

end EthLib.Consensus.Ssz.Native.Driver.Validate
