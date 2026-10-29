import SszNative.Proofs.Driver.Validate.PlanCheck

/-!
The walk that bounds a plan's nesting, on the plan of a legal type nested no deeper than its budget: it reads past the
type's words.

The plan's own check then runs only on plans this walk accepts, so every walk of an accepted plan nests at most the
deepest a plan may be, and its stack is bounded by a constant.
-/

namespace Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open Ssz Ssz.Native Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Ir.Stmt Ssz.Native.Ir.Expr

/-- The nesting walk of one node is loaded. -/
theorem Loaded.depth {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_depth" = some depthFn :=
  hm ("ssz_validate_depth", depthFn) (by simp [fns])

/-- The nesting walk of a count of nodes is loaded. -/
theorem Loaded.depthAll {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_depth_all" = some depthAllFn :=
  hm ("ssz_validate_depth_all", depthAllFn) (by simp [fns])

/-- The plan's check alone is loaded. -/
theorem Loaded.checkPlan {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_check_plan" = some checkPlanFn :=
  hm ("ssz_check_plan", checkPlanFn) (by simp [fns])

/-- What the nesting walk of a node computes, for a legal type within its budget: the address past its words. -/
def DepthOk (m : Module) (w : World) (d : Desc) : Prop :=
  d.wellFormed = .ok () → fitsNative d = true →
    ∀ (p stop b sp : Nat) (mem : Memory), PlanAt w mem p (Plan.words d) → p + 8 * (Plan.words d).length ≤ stop →
      stop ≤ 2 ^ 63 → d.nesting ≤ b → b < 2 ^ 64 → Room w sp (2 * d.nesting) 2 →
      Calls m w "ssz_validate_depth" sp [UInt64.ofNat p, UInt64.ofNat stop, UInt64.ofNat b] mem
        (UInt64.ofNat (p + 8 * (Plan.words d).length)) mem

set_option maxHeartbeats 4000000 in
/-- The nesting walk of a count of legal nodes within the budget reads past all of them. -/
theorem depthAll_calls {m : Module} {w : World} (hm : Loaded m) (fs : List Desc) (ih : ∀ f ∈ fs, DepthOk m w f)
    (wf : Desc.allWellFormed fs = .ok ()) (fit : allFitNative fs = true)
    (p stop b sp : Nat) (mem : Memory) (hp : PlanAt w mem p (Plan.wordsAll fs))
    (hs : p + 8 * (Plan.wordsAll fs).length ≤ stop) (hstop : stop ≤ 2 ^ 63) (deep : Desc.deepestNesting fs ≤ b)
    (hb64 : b < 2 ^ 64) (room : Room w sp (2 * (Desc.deepestNesting fs + 1)) 1) :
    Calls m w "ssz_validate_depth_all" sp [UInt64.ofNat p, UInt64.ofNat fs.length, UInt64.ofNat stop, UInt64.ofNat b]
      mem (UInt64.ofNat (p + 8 * (Plan.wordsAll fs).length)) mem := by
  have hb := hp.bound
  have hl := length_le_wordsAll fs
  refine Calls.body 7 hm.depthAll rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [depthAllFn]
  -- After j nodes, the walk stands past their words, with the rest to go.
  refine Wp.single (Wp.loop (wp_loop (fun env mem' => mem' = mem ∧ ∃ j, j ≤ fs.length ∧
      env 0 = UInt64.ofNat (p + 8 * (Plan.wordsAll (fs.take j)).length) ∧ env 1 = UInt64.ofNat (fs.length - j) ∧
      env 2 = UInt64.ofNat stop ∧ env 3 = UInt64.ofNat b)
    (fun env _ => (env 1).toNat)
    ⟨rfl, 0, Nat.zero_le _, by wfin [Plan.wordsAll], by wfin [], by wfin [], by wfin []⟩ ?_))
  rintro env mem' ⟨hmem, j, hj, h0, h1, h2, h3⟩
  subst mem'
  have hjl := wordsAll_take_le fs j
  have inside : p + 8 * (Plan.wordsAll (fs.take j)).length ≤ stop := by omega
  refine ⟨_, by wev [h0, h1, h2, inside], fun nz => ?_, fun z => ?_⟩
  · have hjf : j < fs.length := by
      rcases Nat.lt_or_ge j fs.length with h | h
      · exact h
      · simp [show fs.length - j = 0 by omega] at nz
    obtain ⟨_, hpj, slen⟩ := fieldAt hp j hjf
    have nest := nesting_le_deepest fs fs[j] (List.getElem_mem hjf)
    have step := ih fs[j] (List.getElem_mem hjf) (allWellFormed_mem fs wf _ (List.getElem_mem hjf))
      (fits_getElem fs fit j hjf) _ stop b (sp - 8 - 8 * 7) mem hpj (by omega) hstop (by omega) hb64
      (by simp only [Room] at room ⊢; omega)
    wcall step [h0, h2, h3]
    wsteps [h1]
    refine ⟨⟨trivial, j + 1, by omega, ?_, by wfin [], by wfin [h2], by wfin [h3]⟩, by wfin [h1]⟩
    wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
  · have hjk : j = fs.length := by
      rcases Nat.lt_or_ge j fs.length with h | h
      · simp [show fs.length - j ≠ 0 by omega] at z
      · omega
    subst hjk
    wfin []
    rw [h0, List.take_length, UInt64.ofNat_add, UInt64.ofNat_mul]
    rfl

set_option hygiene false in
/-- Opens a proof about one node of the nesting walk. -/
macro "depth_open" : tactic => `(tactic| (
  intro wf fit p stop b sp mem hp hs hstop deep hb64 room
  have hb := hp.bound
  have r0 := hp.read0 (words_length_pos _)
  have a0 := hp.readable0 (words_length_pos _)
  rw [words_head] at r0
  simp only [Plan.tag] at r0
  simp [Plan.words] at hb a0 hs
  have s8 : p + 8 ≤ stop := by omega
  have b0 : b ≠ 0 := by simp only [Desc.nesting] at deep; omega
  refine Calls.body 11 hm.depth rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [depthFn]))

set_option maxHeartbeats 16000000 in
/-- The nesting walk of a legal type's plan within its budget reads past its words. -/
theorem depth_calls {m : Module} {w : World} (hm : Loaded m) (d : Desc) : DepthOk m w d := by
  induction d using Desc.rec (motive_2 := fun fs => ∀ f ∈ fs, DepthOk m w f) with
  | nil => rename_i h; simp at h
  | cons f fs ihf ihfs =>
    rename_i g h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ihf
    · exact ihfs g h
  | bool =>
    depth_open
    wsteps [r0, a0, s8, b0]
    wfin [Plan.words]
  | uint _ | byteVector _ | byteList _ | bitVector _ | bitList _ =>
    depth_open
    have s16 : p + 16 ≤ stop := by omega
    wsteps [r0, a0, s8, b0, s16]
    wfin [Plan.words]
  | progressiveBitList l =>
    depth_open
    have s24 : p + 24 ≤ stop := by omega
    wsteps [r0, a0, s8, b0, s24]
    wfin [Plan.words]
  | vector e _ ih | list e _ ih =>
    depth_open
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
      (by simp only [Desc.nesting] at deep; omega) (by omega) (by simp only [Room, Desc.nesting] at room ⊢; omega)
    have s16 : p + 16 ≤ stop := by omega
    wsteps [r0, a0, s8, b0, s16]
    wcall step []
    wsteps []
    wfin [Plan.words]
  | progressiveList e limit ih =>
    depth_open
    have we : e.wellFormed = .ok () := by simpa [Desc.wellFormed] using wf
    have fe : fitsNative e = true := by simp [fitsNative] at fit; exact fit.1
    have he : PlanAt w mem (p + 24) (Plan.words e) := by
      have := hp.right (a := 9 :: Plan.bound limit) (b := Plan.words e); simpa using this
    have step := ih we fe (p + 24) stop (b - 1) (sp - 8 - 8 * 11) mem he (by omega) hstop
      (by simp only [Desc.nesting] at deep; omega) (by omega) (by simp only [Room, Desc.nesting] at room ⊢; omega)
    have s24 : p + 24 ≤ stop := by omega
    wsteps [r0, a0, s8, b0, s24]
    wcall step []
    wsteps []
    wfin [Plan.words]
  | container names fs ih =>
    depth_open
    have r1 := hp.read 8 rfl (by simp [Plan.words] <;> omega)
    have a1 := hp.readable 8 rfl (by simp [Plan.words] <;> omega)
    simp [Plan.words] at r1
    simp [Desc.wellFormed, ite_ok, throw_ok, bind_unit_ok] at wf
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
    have hf : PlanAt w mem (p + 16) (Plan.wordsAll fs) := by
      have := hp.right (a := [10, fs.length]) (b := Plan.wordsAll fs); simpa using this
    have wfs : Desc.allWellFormed fs = .ok () := (wf.2 wf.1).1 (wf.2 wf.1).2 |>.2 ((wf.2 wf.1).1 (wf.2 wf.1).2).1
    have pa := depthAll_calls hm fs ih wfs fit.1.1 (p + 16) stop (b - 1) (sp - 8 - 8 * 11) mem hf (by omega) hstop
      (by simp only [Desc.nesting] at deep; omega) (by omega) (by simp only [Room, Desc.nesting] at room ⊢; omega)
    have s16 : p + 16 ≤ stop := by omega
    wsteps [r0, a0, s8, b0, s16]
    wcall pa [r1, a1]
    wsteps []
    wfin [Plan.words]
  | progressiveContainer active names fs ih =>
    depth_open
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
    -- The field count follows the layout's bits.
    have rn : readLE mem (p + 16 + 8 * active.length) 8 = UInt64.ofNat fs.length := by
      have := hp.read (16 + 8 * active.length) (by omega) (by rw [hlen]; omega)
      rw [Nat.add_assoc, this, show (16 + 8 * active.length) / 8 = active.length + 2 by omega, e]
      simp only [getElem!_def, List.append_assoc]
      rw [List.getElem?_append_right (by simp)]
      simp
    have an : w.access (p + 16 + 8 * active.length) 8 = true := by
      have := hp.readable (16 + 8 * active.length) (by omega) (by rw [hlen]; omega)
      rwa [← Nat.add_assoc] at this
    have pa := depthAll_calls hm fs ih wfs fit.1.1 (p + 24 + 8 * active.length) stop (b - 1) (sp - 8 - 8 * 11) mem
      hf (by omega) hstop (by simp only [Desc.nesting] at deep; omega) (by omega)
      (by simp only [Room, Desc.nesting] at room ⊢; omega)
    have s16 : p + 16 ≤ stop := by omega
    have s24 : p + 24 + 8 * active.length ≤ stop := by omega
    have k32 : active.length < 4294967296 := by omega
    wsteps [r0, a0, s8, b0, r1, a1, s16, k32, s24]
    wcall pa [rn, an]
    wsteps []
    wfin [hlen]
  | compatibleUnion sels opts ih =>
    depth_open
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
    have pa := depthAll_calls hm opts ih wfs fa (p + 16 + 8 * opts.length) stop (b - 1) (sp - 8 - 8 * 11) mem hf
      (by omega) hstop (by simp only [Desc.nesting] at deep; omega) (by omega)
      (by simp only [Room, Desc.nesting] at room ⊢; omega)
    have s16 : p + 16 ≤ stop := by omega
    have sn : p + 16 + 8 * opts.length ≤ stop := by omega
    wsteps [r0, a0, s8, b0, r1, a1, s16, n32, sn]
    wcall pa []
    wsteps []
    wfin [hlen]

end Ssz.Native.Driver.Validate
