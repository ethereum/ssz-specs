import SszNative.Proofs.Driver.Validate.Basic

namespace EthLib.Consensus.Ssz.Native.Driver.Validate

set_option maxRecDepth 20000
open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr

/-- What skipping a node computes: the address past its words, with memory untouched. -/
def SkipOk (m : Module) (w : World) (d : Desc) : Prop :=
  fitsNative d = true → ∀ (p sp : Nat) (mem : Memory), PlanAt w mem p (Plan.words d) → Room w sp d.nesting 2 →
    Calls m w "ssz_validate_skip" sp [UInt64.ofNat p] mem (UInt64.ofNat (p + 8 * (Plan.words d).length)) mem

/-- Every type takes at least one word. -/
theorem length_le_wordsAll : ∀ fs : List Desc, fs.length ≤ (Plan.wordsAll fs).length
  | [] => by simp
  | d :: fs => by
    have := length_le_wordsAll fs; have := words_length_pos d
    simp [Plan.wordsAll]; omega

/-- The first types' words are no more than all of them. -/
theorem wordsAll_take_le (fs : List Desc) (k : Nat) :
    (Plan.wordsAll (fs.take k)).length ≤ (Plan.wordsAll fs).length := by
  conv => rhs; rw [← List.take_append_drop k fs]
  rw [wordsAll_append]; simp

/-- Each type of a list that fits fits. -/
theorem allFitNative_mem : ∀ (fs : List Desc), allFitNative fs = true → ∀ f ∈ fs, fitsNative f = true
  | [], _, _, h => by simp at h
  | g :: rest, fit, f, h => by
    simp only [allFitNative, Bool.and_eq_true] at fit
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact fit.1
    · exact allFitNative_mem rest fit.2 f h

/-- Skipping a count of nodes lands past their words. -/
theorem skipAll_calls {m : Module} {w : World} (hm : Loaded m) (fs : List Desc) (ih : ∀ f ∈ fs, SkipOk m w f)
    (fit : allFitNative fs = true) (k p sp : Nat) (mem : Memory) (hk : k ≤ fs.length) (hp : PlanAt w mem p (Plan.wordsAll fs))
    (room : Room w sp (Desc.deepestNesting fs + 1) 1) :
    Calls m w "ssz_validate_skip_all" sp [UInt64.ofNat p, UInt64.ofNat k] mem
      (UInt64.ofNat (p + 8 * (Plan.wordsAll (fs.take k)).length)) mem := by
  have hb := hp.bound
  have hl := length_le_wordsAll fs
  refine Calls.body 3 hm.skipAll rfl (by omega) rfl ?_
  simp only [skipAllFn]
  refine wp_loop (fun env mem' => mem' = mem ∧ ∃ j, j ≤ k ∧
      env 0 = UInt64.ofNat (p + 8 * (Plan.wordsAll (fs.take j)).length) ∧ env 1 = UInt64.ofNat (k - j))
    (fun env _ => (env 1).toNat) ⟨rfl, 0, Nat.zero_le _, by simp [entryEnv, Plan.wordsAll], by simp [entryEnv]⟩ ?_
  rintro env mem' ⟨hmem, j, hj, h0, h1⟩
  subst hmem

  have hjl := wordsAll_take_le fs j
  refine ⟨if k - j = 0 then 0 else 1, by wsimp [h1], fun nz => ?_, fun z => ?_⟩
  · have hjk : j < k := by
      rcases Nat.lt_or_ge j k with h | h
      · exact h
      · simp [show k - j = 0 by omega] at nz
    have hjf : j < fs.length := by omega
    have split := wordsAll_split fs j hjf
    have hpj : PlanAt w mem' (p + 8 * (Plan.wordsAll (fs.take j)).length) (Plan.words fs[j]) := by
      rw [split] at hp; exact hp.left.right
    have nest := nesting_le_deepest fs fs[j] (List.getElem_mem hjf)
    have hroom : Room w (sp - 8 - 8 * 3) fs[j].nesting 2 := by
      simp only [Room] at room ⊢
      generalize fs[j].nesting = a at nest ⊢
      omega
    have step := ih fs[j] (List.getElem_mem hjf) (allFitNative_mem fs fit _ (List.getElem_mem hjf)) _ (sp - 8 - 8 * 3) mem' hpj hroom
    wsimp [h0, h1]
    refine ⟨_, _, step, ⟨rfl, j + 1, by omega, ?_, by omega⟩, by omega⟩
    rw [wordsAll_take_succ fs j hjf]; simp [Nat.mul_add, Nat.add_assoc]
  · have hjk : j = k := by
      rcases Nat.lt_or_ge j k with h | h
      · simp [show k - j ≠ 0 by omega] at z
      · omega
    subst hjk
    wsimp [h0]

set_option maxHeartbeats 1000000 in
/-- Skipping a node of a type that fits the native check lands past its words. -/
theorem skip_calls {m : Module} {w : World} (hm : Loaded m) (d : Desc) : SkipOk m w d := by
  induction d using Desc.rec (motive_2 := fun fs => ∀ f ∈ fs, SkipOk m w f) with
  | nil => rename_i h; simp at h
  | cons f fs ihf ihfs =>
    rename_i g h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ihf
    · exact ihfs g h
  | bool | uint _ | byteVector _ | byteList _ | bitVector _ | bitList _ | progressiveBitList _ =>
    intro _ p sp mem hp room
    have hb := hp.bound
    have r0 := hp.read0 (words_length_pos _)
    have a0 := hp.readable0 (words_length_pos _)
    refine Calls.body 7 hm.skip rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [skipFn]
    simp [Plan.words] at r0 a0 hb
    wsteps [r0, a0]
    wfin [Plan.words]
  | vector e n ih | list e n ih =>
    intro fit p sp mem hp room
    have hb := hp.bound
    have r0 := hp.read0 (words_length_pos _)
    have a0 := hp.readable0 (words_length_pos _)
    simp [Plan.words] at r0 a0 hb
    have he : PlanAt w mem (p + 16) (Plan.words e) := by
      have := hp.right (a := [_, n]) (b := Plan.words e); simpa using this
    have step := ih (by simp [fitsNative] at fit; first | exact fit.1.1 | exact fit.1) (p + 16) (sp - 8 - 8 * 7) mem he
      (by simp only [Room, Desc.nesting] at room ⊢; omega)
    refine Calls.body 7 hm.skip rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [skipFn]
    wsteps [r0, a0]
    wcall step []
    wsteps []
    wfin [Plan.words]
  | progressiveList e l ih =>
    intro fit p sp mem hp room
    have hb := hp.bound
    have r0 := hp.read0 (words_length_pos _)
    have a0 := hp.readable0 (words_length_pos _)
    simp [Plan.words] at r0 a0 hb
    have he : PlanAt w mem (p + 24) (Plan.words e) := by
      have := hp.right (a := 9 :: Plan.bound l) (b := Plan.words e); simpa using this
    have step := ih (by simp [fitsNative] at fit; exact fit.1) (p + 24) (sp - 8 - 8 * 7) mem he
      (by simp only [Room, Desc.nesting] at room ⊢; omega)
    refine Calls.body 7 hm.skip rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [skipFn]
    wsteps [r0, a0]
    wcall step []
    wsteps []
    wfin [Plan.words]
  | container names fs ih =>
    intro fit p sp mem hp room
    have hb := hp.bound
    have r0 := hp.read0 (words_length_pos _)
    have a0 := hp.readable0 (words_length_pos _)
    have r1 := hp.read 8 rfl (by simp [Plan.words])
    have a1 := hp.readable 8 rfl (by simp [Plan.words])
    simp [Plan.words] at r0 a0 hb r1
    have hf : PlanAt w mem (p + 16) (Plan.wordsAll fs) := by
      have := hp.right (a := [10, fs.length]) (b := Plan.wordsAll fs); simpa using this
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
    have step := skipAll_calls hm fs ih fit.1.1 fs.length (p + 16) (sp - 8 - 8 * 7) mem (Nat.le_refl _) hf
      (by simp only [Room, Desc.nesting] at room ⊢; omega)
    refine Calls.body 7 hm.skip rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [skipFn]
    wsteps [r0, a0, r1, a1]
    wcall step [r1, a1]
    wsteps []
    wfin [Plan.words, List.take_length]
  | progressiveContainer active names fs ih =>
    intro fit p sp mem hp room
    have hb := hp.bound
    have r0 := hp.read0 (words_length_pos _)
    have a0 := hp.readable0 (words_length_pos _)
    have r1 := hp.read 8 rfl (by simp [Plan.words])
    have a1 := hp.readable 8 rfl (by simp [Plan.words])
    have r2 := hp.read (16 + 8 * active.length) (by omega) (by simp [Plan.words]; omega)
    have a2 := hp.readable (16 + 8 * active.length) (by omega) (by simp [Plan.words]; omega)
    simp [Plan.words] at r0 a0 hb r1
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
    have step := skipAll_calls hm fs ih fit.1.1 fs.length (p + 24 + 8 * active.length) (sp - 8 - 8 * 7) mem
      (Nat.le_refl _) hf (by simp only [Room, Desc.nesting] at room ⊢; omega)
    refine Calls.body 7 hm.skip rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [skipFn]
    wsteps [r0, a0, r1, a1, r2', a2]
    wcall step [r1, a1, r2', a2]
    wsteps []
    wfin [Plan.words, List.take_length]
  | compatibleUnion sels opts ih =>
    intro fit p sp mem hp room
    have hb := hp.bound
    have r0 := hp.read0 (words_length_pos _)
    have a0 := hp.readable0 (words_length_pos _)
    have r1 := hp.read 8 rfl (by simp [Plan.words])
    have a1 := hp.readable 8 rfl (by simp [Plan.words])
    simp [Plan.words] at r0 a0 hb r1
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at fit
    have hl : sels.length = opts.length := fit.1.2
    have hf : PlanAt w mem (p + 16 + 8 * opts.length) (Plan.wordsAll opts) := by
      have e : Plan.words (.compatibleUnion sels opts) = ([12, opts.length] ++ sels) ++ Plan.wordsAll opts := by
        simp [Plan.words]
      rw [e] at hp
      refine hp.right.at_eq ?_
      simp only [List.length_append, List.length_cons, List.length_nil, hl]
      omega
    have step := skipAll_calls hm opts ih fit.1.1.1 opts.length (p + 16 + 8 * opts.length) (sp - 8 - 8 * 7)
      mem (Nat.le_refl _) hf (by simp only [Room, Desc.nesting] at room ⊢; omega)
    refine Calls.body 7 hm.skip rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [skipFn]
    wsteps [r0, a0, r1, a1]
    wcall step [r1, a1]
    wsteps []
    wfin [Plan.words, List.take_length, hl]

end EthLib.Consensus.Ssz.Native.Driver.Validate
