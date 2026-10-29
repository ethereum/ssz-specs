import SszNative.Driver.Prove
import SszNative.Proofs.Driver.Root

/-!
The prover's scratch bound, computed by its drivers, is the Lean bound.

The path's bound walks the type's plan like the root's scratch bound does, one child after another.
-/

namespace Ssz.Native.Driver

open Ssz Ssz.Native.Ir Ssz.Native.Ir.Expr Ssz.Native.Ir.Stmt Ssz.Native.Asm

variable {m : Module} {w : World}

set_option maxRecDepth 8000

/-- The path's bound is at most the cap. -/
theorem deepNeed_le (d : Desc) : deepNeed d ≤ scratchCap := by
  cases d <;> simp only [deepNeed] <;> first | exact sadd_le _ _ | exact rootsNeed_le _ _

/-- The most several types spend is at most the cap, from a most at most the cap. -/
theorem deepMost_le : ∀ (fs : List Desc) (most : Nat), most ≤ scratchCap → deepMost fs most ≤ scratchCap
  | [], _, h => h
  | f :: rest, _, h => deepMost_le rest _ (Nat.max_le.mpr ⟨deepNeed_le f, h⟩)

/-- The path's bound's frame holds thirteen words. -/
theorem proveDeepFrame : ProveDeep.fn.frame = 13 := by decide

/-- The scratch bound's frame holds seven words. -/
theorem proveScratchFrame : ProveScratch.fn.frame = 7 := by decide

/-- The loop over child types in the path's bound. -/
abbrev deepLoop : Stmt :=
  while_ (lt ProveDeep.i ProveDeep.k) [callInto ProveDeep.x "ssz_prove_deep" [ProveDeep.q],
    maxIn ProveDeep.t ProveDeep.x ProveDeep.t, callInto ProveDeep.q "ssz_plan_next" [ProveDeep.q],
    ProveDeep.i ::= ProveDeep.i + 1]

/-- The tail: the node's own root bound, a node per child, and the children's most, added. -/
theorem deep_tail (sp : Nat) (mem : Memory) {d : Desc} {a N T : Nat} {E : Env}
    (roots : Calls m w "ssz_scratch_roots" sp [a.toUInt64, (1 : Nat).toUInt64] mem (rootsNeed d 1).toUInt64 mem)
    (h0 : E 0 = a.toUInt64) (h5 : E 5 = N.toUInt64) (hN : N < 2 ^ 64) (h3 : E 3 = T.toUInt64)
    (hT : T ≤ scratchCap) :
    ∃ E', Runs m w sp E mem (.block ProveDeep.tail) E' mem ∧
      E' 2 = (sadd (sadd (rootsNeed d 1) (smul 32 (sat N))) T).toUInt64 := by
  have R := rootsNeed_le d 1
  have S := sat_le N
  let E1 := Asm.assign E 2 (rootsNeed d 1).toUInt64
  have c1 : Runs m w sp E mem (callInto ProveDeep.r "ssz_scratch_roots" [ProveDeep.p, 1]) E1 mem :=
    Runs.call (by simp [eval, h0]) roots
  have s2 := satIn_runs (m := m) (w := w) (sp := sp) (mem := mem) ProveDeep.n (env := E1) (x := N)
    (by simp [E1, Asm.assign, h5]) hN
  have s3 := smulIn_runs (m := m) (w := w) (sp := sp) (mem := mem) ProveDeep.x
    (env := Asm.assign E1 5 (sat N).toUInt64) (a := (32 : Expr)) (b := (ProveDeep.n : Expr)) (x := 32) (y := sat N)
    (by simp [eval]) (by simp [eval, Asm.assign]) (by decide) S
  have s4 := saddIn_runs (m := m) (w := w) (sp := sp) (mem := mem) ProveDeep.r
    (env := Asm.assign (Asm.assign E1 5 (sat N).toUInt64) 4 (smul 32 (sat N)).toUInt64)
    (a := (ProveDeep.r : Expr)) (b := (ProveDeep.x : Expr)) (x := rootsNeed d 1) (y := smul 32 (sat N))
    (by simp [eval, E1, Asm.assign]) (by simp [eval, Asm.assign]) R (smul_le _ _)
  have s5 := saddIn_runs (m := m) (w := w) (sp := sp) (mem := mem) ProveDeep.r
    (env := Asm.assign (Asm.assign (Asm.assign E1 5 (sat N).toUInt64) 4 (smul 32 (sat N)).toUInt64) 2
      (sadd (rootsNeed d 1) (smul 32 (sat N))).toUInt64)
    (a := (ProveDeep.r : Expr)) (b := (ProveDeep.t : Expr)) (x := sadd (rootsNeed d 1) (smul 32 (sat N))) (y := T)
    (by simp [eval, Asm.assign]) (by simp [eval, E1, Asm.assign, h3]) (sadd_le _ _) hT
  exact ⟨_, Runs.block_append (Runs.block_append
    (Runs.block_cons c1 (Runs.block_cons s2 (Runs.block_cons s3 (Runs.block_nil _ _ _ _ _)))) s4) s5,
    by simp [Asm.assign]⟩

set_option maxHeartbeats 4000000 in
mutual

/-- The path's bound function returns the path's bound of a well-formed type. -/
theorem deep_calls (hf : PlanFns m) (hd : m.fns.lookup "ssz_prove_deep" = some ProveDeep.fn) (d : Desc)
    (a sp : Nat) (mem : Memory) (hw : WordsAt w mem a (Plan.words d)) (fits : Fits (Plan.words d))
    (hp : d.wellFormed = .ok ()) (stack : w.stackLo + 256 * (d.nesting + 2) ≤ sp) :
    Calls m w "ssz_prove_deep" sp [a.toUInt64] mem (deepNeed d).toUInt64 mem := by
  have one := nesting_pos d
  have room' : w.stackLo + 8 + 8 * 13 ≤ sp := by omega
  have inner : w.stackLo + 256 * d.nesting + 256 ≤ sp - 8 - 8 * 13 := by omega
  have roots := scratchRoots_calls hf d a 1 (sp - 8 - 8 * ProveDeep.fn.frame) mem hw fits hp (by decide)
    (by rw [proveDeepFrame]; omega)
  have tagRead := eval_tag (w := w) (env := entryEnv [a.toUInt64]) (mem := mem) (e := .var 0) hw
    (by simp [eval, entryEnv])
  let E0 := Asm.assign (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1 (Plan.tag d).toUInt64) 3 0) 5 0
  have pre : Runs m w (sp - 8 - 8 * ProveDeep.fn.frame) (entryEnv [a.toUInt64]) mem
      (.block [ProveDeep.tag ::= ld ProveDeep.p, ProveDeep.t ::= 0, ProveDeep.n ::= 0]) E0 mem :=
    Runs.block_cons (Runs.set' tagRead) (Runs.block_cons (Runs.set' (by simp [eval]))
      (Runs.block_cons (Runs.set' (by simp [eval])) (Runs.block_nil _ _ _ _ _)))
  have e0 : E0 0 = a.toUInt64 := by simp [E0, Asm.assign, entryEnv]
  -- The head leaves the children's count and most, and the tail adds them to the node's own bound.
  suffices head : ∃ E N T, Runs m w (sp - 8 - 8 * ProveDeep.fn.frame) E0 mem
      (.block [ProveDeep.kinds]) E mem ∧ E 0 = a.toUInt64 ∧
      E 5 = N.toUInt64 ∧ N < 2 ^ 64 ∧ E 3 = T.toUInt64 ∧ T ≤ scratchCap ∧
      deepNeed d = sadd (sadd (rootsNeed d 1) (smul 32 (sat N))) T by
    obtain ⟨E, N, T, run, h0, h5, hN, h3, hT, eq⟩ := head
    obtain ⟨E', tl, r2⟩ := deep_tail (sp - 8 - 8 * ProveDeep.fn.frame) mem roots h0 h5 hN h3 hT
    refine Calls.fn hd (proveDeepFrame ▸ room') rfl
      (Runs.block_append (Runs.block_append pre run) tl) ?_
    simp [ProveDeep.fn, eval, r2, eq]
  have t1 : E0 1 = (Plan.tag d).toUInt64 := by simp [E0, Asm.assign]
  have hisp : w.stackLo + 256 * d.nesting + 256 ≤ sp - 8 - 8 * ProveDeep.fn.frame := by
    rw [proveDeepFrame]; exact inner
  generalize sp - 8 - 8 * ProveDeep.fn.frame = isp at hisp pre roots ⊢
  have R := rootsNeed_le d 1
  -- A node with no children: every kind test fails.
  have leaf : (Plan.tag d ≠ 7 ∧ Plan.tag d ≠ 8 ∧ Plan.tag d ≠ 9 ∧ Plan.tag d ≠ 10 ∧ Plan.tag d ≠ 11 ∧
      Plan.tag d ≠ 12) → deepNeed d = rootsNeed d 1 → ∃ E N T, Runs m w isp E0 mem (.block [ProveDeep.kinds]) E mem ∧
      E 0 = a.toUInt64 ∧ E 5 = N.toUInt64 ∧ N < 2 ^ 64 ∧ E 3 = T.toUInt64 ∧ T ≤ scratchCap ∧
      deepNeed d = sadd (sadd (rootsNeed d 1) (smul 32 (sat N))) T := fun ⟨n7, n8, n9, n10, n11, n12⟩ eq => by
    have tl : Plan.tag d < 2 ^ 64 := by have := tag_lt d; omega
    have f : ∀ k < 2 ^ 64, Plan.tag d ≠ k → ¬ UInt64.ofNat (Plan.tag d) = UInt64.ofNat k := fun k hk hne h => hne (by
      have := congrArg UInt64.toNat h; simp only [UInt64.toNat_ofNat'] at this; omega)
    have g7 : ¬ UInt64.ofNat (Plan.tag d) = 7 := f 7 (by decide) n7
    have g8 : ¬ UInt64.ofNat (Plan.tag d) = 8 := f 8 (by decide) n8
    have g9 : ¬ UInt64.ofNat (Plan.tag d) = 9 := f 9 (by decide) n9
    have g10 : ¬ UInt64.ofNat (Plan.tag d) = 10 := f 10 (by decide) n10
    have g11 : ¬ UInt64.ofNat (Plan.tag d) = 11 := f 11 (by decide) n11
    have g12 : ¬ UInt64.ofNat (Plan.tag d) = 12 := f 12 (by decide) n12
    refine ⟨E0, 0, 0, Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, t1, g7, g8])
      (Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, t1, g9])
        (Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, t1, g10])
          (Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, t1, g11])
            (Runs.block_cons (Runs.when_false (by simp [eval, Cond.holds, t1, g12])) (Runs.block_nil _ _ _ _ _)))
            (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _)))
      (Runs.block_nil _ _ _ _ _), e0, by simp [E0, Asm.assign], by decide, by simp [E0, Asm.assign], by decide, ?_⟩
    rw [eq]; simp only [sadd, smul, sat]; omega
  -- The children loop, run from the first child's node with the most at zero.
  have kids : ∀ (fs : List Desc) (E : Env), fs.length < 2 ^ 64 → E 0 = a.toUInt64 → E 6 = fs.length.toUInt64 →
      (∃ E', Runs m w isp (Asm.assign (Asm.assign E 5 fs.length.toUInt64) 8 0) mem deepLoop E' mem ∧
        E' 3 = (deepMost fs 0).toUInt64 ∧
        ∀ v, v ≠ 3 → v ≠ 4 → v ≠ 7 → v ≠ 8 → E' v = Asm.assign (Asm.assign E 5 fs.length.toUInt64) 8 0 v) →
      ∃ E', Runs m w isp E mem (.block ProveDeep.children) E' mem ∧
        E' 0 = a.toUInt64 ∧ E' 5 = fs.length.toUInt64 ∧ fs.length < 2 ^ 64 ∧ E' 3 = (deepMost fs 0).toUInt64 :=
    fun fs E hN h0 h6 ⟨E', lp, m3, keep⟩ => by
      refine ⟨E', Runs.block_cons (Runs.set' (by simp [eval, h6]))
        (Runs.block_cons (Runs.set' (by simp [eval])) (Runs.block_cons lp (Runs.block_nil _ _ _ _ _))),
        by rw [keep 0 (by decide) (by decide) (by decide) (by decide)]; simp [Asm.assign, h0],
        by rw [keep 5 (by decide) (by decide) (by decide) (by decide)]; simp [Asm.assign], hN, m3⟩
  cases d with
  | bool => exact leaf (by simp [Plan.tag]) rfl
  | uint _ => exact leaf (by simp [Plan.tag]) rfl
  | byteVector _ => exact leaf (by simp [Plan.tag]) rfl
  | byteList _ => exact leaf (by simp [Plan.tag]) rfl
  | bitVector _ => exact leaf (by simp [Plan.tag]) rfl
  | bitList _ => exact leaf (by simp [Plan.tag]) rfl
  | progressiveBitList _ => exact leaf (by simp [Plan.tag]) rfl
  | vector e l | list e l =>
    simp only [Plan.words] at hw fits
    obtain ⟨_, he⟩ := wordsAt_split hw
    obtain ⟨_, fe⟩ := fits_split fits
    first | replace hp := wellFormed_vector hp | replace hp := wellFormed_list hp
    simp only [Desc.nesting] at hisp
    have he' : WordsAt w mem (a + 16) (Plan.words e) := by simpa using he
    have recur := deep_calls hf hd e (a + 16) isp mem he' fe hp (by omega)
    refine ⟨_, 1, deepNeed e, Runs.block_cons (Runs.ifElse_true 1 (by simp [eval, Cond.holds, t1, Plan.tag])
      (by decide) (Runs.block_cons (Runs.set' (v := 1) rfl)
        (Runs.block_cons (Runs.call (values := [(a + 16).toUInt64]) (by simp [eval, E0, Asm.assign, entryEnv]) recur) (Runs.block_nil _ _ _ _ _))))
      (Runs.block_nil _ _ _ _ _), by simp [E0, Asm.assign, entryEnv], by simp [Asm.assign], by decide,
      by simp [Asm.assign], deepNeed_le e, by rw [show smul 32 (sat 1) = 32 from by decide]; simp only [deepNeed]⟩
  | progressiveList e l =>
    have hlen : (9 :: Plan.bound l).length = 3 := by cases l <;> rfl
    simp only [Plan.words] at hw fits
    obtain ⟨_, he⟩ := wordsAt_split hw
    obtain ⟨_, fe⟩ := fits_split fits
    replace hp := wellFormed_progressiveList hp
    simp only [Desc.nesting] at hisp
    have he' : WordsAt w mem (a + 24) (Plan.words e) := by rw [hlen] at he; simpa using he
    have recur := deep_calls hf hd e (a + 24) isp mem he' fe hp (by omega)
    refine ⟨_, 1, deepNeed e, Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, t1, Plan.tag])
      (Runs.block_cons (Runs.ifElse_true 1 (by simp [eval, Cond.holds, t1, Plan.tag]) (by decide)
        (Runs.block_cons (Runs.set' (v := 1) rfl)
          (Runs.block_cons (Runs.call (values := [(a + 24).toUInt64]) (by simp [eval, E0, Asm.assign, entryEnv]) recur) (Runs.block_nil _ _ _ _ _))))
        (Runs.block_nil _ _ _ _ _)))
      (Runs.block_nil _ _ _ _ _), by simp [E0, Asm.assign, entryEnv], by simp [Asm.assign], by decide,
      by simp [Asm.assign], deepNeed_le e, by rw [show smul 32 (sat 1) = 32 from by decide]; simp only [deepNeed]⟩
  | container names fs =>
    simp only [Plan.words] at hw fits
    obtain ⟨hh, hfs⟩ := wordsAt_split hw
    obtain ⟨_, ffs⟩ := fits_split fits
    replace hp := wellFormed_container hp
    simp only [Desc.nesting] at hisp
    have hq : WordsAt w mem (a + 16) (Plan.wordsAll fs) := by simpa using hfs
    let E1 := Asm.assign (Asm.assign E0 6 fs.length.toUInt64) 7 (a + 16).toUInt64
    obtain ⟨E', run, h0, h5, hN, h3⟩ := kids fs E1 (fields_small hq) (by simp [E1, Asm.assign, e0]) (by simp [E1, Asm.assign])
      (deep_loop hf hd fs (a + 16) 0 fs.length isp 0 _ mem hq ffs hp (by decide) (by simp [E1, Asm.assign])
        (by simp [Asm.assign]) (by simp [E1, Asm.assign]) (by simp [E1, E0, Asm.assign]) (fields_small hq) (by simp)
        (by omega))
    refine ⟨E', fs.length, deepMost fs 0,
      Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, t1, Plan.tag])
      (Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, t1, Plan.tag])
        (Runs.block_cons (Runs.ifElse_true 1 (by simp [eval, Cond.holds, t1, Plan.tag]) (by decide)
          (Runs.block_append (Runs.block_cons (Runs.set' (v := fs.length.toUInt64)
              (eval_word hh 1 (by simp) (by simp [eval, E0, Asm.assign, entryEnv])))
            (Runs.block_cons (Runs.set' (v := (a + 16).toUInt64) (by simp [eval, Asm.assign, E0, entryEnv]))
              (Runs.block_nil _ _ _ _ _))) run))
          (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _)))
      (Runs.block_nil _ _ _ _ _), h0, h5, hN, h3, deepMost_le fs 0 (by decide), by simp [deepNeed]⟩
  | progressiveContainer active names fs =>
    simp only [Plan.words] at hw fits
    obtain ⟨hpre, hfs⟩ := wordsAt_split hw
    obtain ⟨hpre, hn⟩ := wordsAt_split hpre
    obtain ⟨hh, _⟩ := wordsAt_split hpre
    obtain ⟨_, ffs⟩ := fits_split fits
    replace hp := wellFormed_progressiveContainer hp
    simp only [Desc.nesting] at hisp
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hn hfs
    rw [show a + 8 * (0 + 1 + 1 + active.length) = a + 16 + 8 * active.length by omega] at hn
    have hfs' : WordsAt w mem (a + 16 + 8 * active.length + 8) (Plan.wordsAll fs) := by
      rw [show a + 16 + 8 * active.length + 8 = a + 8 * (0 + 1 + 1 + active.length + (0 + 1)) by omega]
      exact hfs
    let E1 := Asm.assign (Asm.assign (Asm.assign (Asm.assign E0 9 active.length.toUInt64) 7
      (a + 16 + 8 * active.length).toUInt64) 6 fs.length.toUInt64) 7 (a + 16 + 8 * active.length + 8).toUInt64
    obtain ⟨E', run, h0, h5, hN, h3⟩ := kids fs E1 (fields_small hfs') (by simp [E1, Asm.assign, e0]) (by simp [E1, Asm.assign])
      (deep_loop hf hd fs (a + 16 + 8 * active.length + 8) 0 fs.length isp 0 _ mem hfs' ffs hp (by decide) (by simp [E1, Asm.assign])
        (by simp [Asm.assign]) (by simp [E1, Asm.assign]) (by simp [E1, E0, Asm.assign]) (fields_small hfs') (by simp)
        (by omega))
    refine ⟨E', fs.length, deepMost fs 0,
      Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, t1, Plan.tag])
      (Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, t1, Plan.tag])
        (Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, t1, Plan.tag])
          (Runs.block_cons (Runs.ifElse_true 1 (by simp [eval, Cond.holds, t1, Plan.tag]) (by decide)
            (Runs.block_append (Runs.block_cons (Runs.set' (v := active.length.toUInt64)
                (eval_word hh 1 (by simp) (by simp [eval, E0, Asm.assign, entryEnv])))
              (Runs.block_cons (Runs.set' (v := (a + 16 + 8 * active.length).toUInt64)
                  (by simp [eval, Asm.assign, E0, entryEnv]))
                (Runs.block_cons (Runs.set' (v := fs.length.toUInt64)
                    (eval_word hn 0 (by simp) (by simp [eval, Asm.assign])))
                  (Runs.block_cons (Runs.set' (v := (a + 16 + 8 * active.length + 8).toUInt64)
                      (by simp [eval, Asm.assign]))
                    (Runs.block_nil _ _ _ _ _))))) run))
            (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _)))
      (Runs.block_nil _ _ _ _ _), h0, h5, hN, h3, deepMost_le fs 0 (by decide), by simp [deepNeed]⟩
  | compatibleUnion sel opts =>
    have paired := wellFormed_union_paired hp
    simp only [Plan.words] at hw fits
    obtain ⟨hpre, hos⟩ := wordsAt_split hw
    obtain ⟨hh, _⟩ := wordsAt_split hpre
    obtain ⟨_, fos⟩ := fits_split fits
    replace hp := wellFormed_union hp
    simp only [Desc.nesting] at hisp
    simp only [List.length_append, List.length_cons, List.length_nil] at hos
    rw [show a + 8 * (0 + 1 + 1 + sel.length) = a + 16 + 8 * opts.length by omega] at hos
    let E1 := Asm.assign (Asm.assign E0 6 opts.length.toUInt64) 7 (a + 16 + 8 * opts.length).toUInt64
    obtain ⟨E', run, h0, h5, hN, h3⟩ := kids opts E1 (fields_small hos) (by simp [E1, Asm.assign, e0]) (by simp [E1, Asm.assign])
      (deep_loop hf hd opts (a + 16 + 8 * opts.length) 0 opts.length isp 0 _ mem hos fos hp (by decide) (by simp [E1, Asm.assign])
        (by simp [Asm.assign]) (by simp [E1, Asm.assign]) (by simp [E1, E0, Asm.assign]) (fields_small hos) (by simp)
        (by omega))
    refine ⟨E', opts.length, deepMost opts 0,
      Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, t1, Plan.tag])
      (Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, t1, Plan.tag])
        (Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, t1, Plan.tag])
          (Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, t1, Plan.tag])
            (Runs.block_cons (Runs.when_true 1 (by simp [eval, Cond.holds, t1, Plan.tag]) (by decide)
              (Runs.block_append (Runs.block_cons (Runs.set' (v := opts.length.toUInt64)
                  (eval_word hh 1 (by simp) (by simp [eval, E0, Asm.assign, entryEnv])))
                (Runs.block_cons (Runs.set' (v := (a + 16 + 8 * opts.length).toUInt64)
                    (by simp [eval, Asm.assign, E0, entryEnv]))
                  (Runs.block_nil _ _ _ _ _))) run)) (Runs.block_nil _ _ _ _ _)))
            (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _)))
      (Runs.block_nil _ _ _ _ _), h0, h5, hN, h3, deepMost_le opts 0 (by decide), by simp [deepNeed]⟩

/-- The loop over child types keeps the most any child spends, and leaves every other variable alone. -/
theorem deep_loop (hf : PlanFns m) (hd : m.fns.lookup "ssz_prove_deep" = some ProveDeep.fn) (fs : List Desc)
    (a j N sp most : Nat) (env : Env) (mem : Memory) (hw : WordsAt w mem a (Plan.wordsAll fs))
    (fits : Fits (Plan.wordsAll fs)) (hp : Desc.allWellFormed fs = .ok ()) (hmost : most ≤ scratchCap)
    (h7 : env 7 = a.toUInt64) (h8 : env 8 = j.toUInt64) (h6 : env 6 = N.toUInt64) (h3 : env 3 = most.toUInt64)
    (hN : N < 2 ^ 64) (hj : j + fs.length = N) (stack : w.stackLo + 256 * (Desc.deepestNesting fs + 2) ≤ sp) :
    ∃ env', Runs m w sp env mem deepLoop env' mem ∧ env' 3 = (deepMost fs most).toUInt64 ∧
      ∀ v, v ≠ 3 → v ≠ 4 → v ≠ 7 → v ≠ 8 → env' v = env v := by
  match fs with
  | [] =>
    refine ⟨env, Runs.loop_exit _ _ _ _ _ _ _ ?_, by simp [h3, deepMost], fun _ _ _ _ _ => rfl⟩
    simp at hj
    simp [eval, Cond.holds, h8, h6, hj]
  | f :: rest =>
    simp only [Plan.wordsAll] at hw fits
    obtain ⟨hf1, hrest⟩ := wordsAt_split hw
    obtain ⟨ff, frest⟩ := fits_split fits
    have hp := allWellFormed_cons hp
    simp only [Desc.deepestNesting] at stack
    have s1 : w.stackLo + 256 * (f.nesting + 2) ≤ sp := by
      have := Nat.le_max_left f.nesting (Desc.deepestNesting rest); omega
    have s2 : w.stackLo + 256 * (Desc.deepestNesting rest + 2) ≤ sp := by
      have := Nat.le_max_right f.nesting (Desc.deepestNesting rest); omega
    have need := deep_calls hf hd f a sp mem hf1 ff hp.1 s1
    have skip := next_ok m w hf.codec f hp.1 sp mem a hf1 (by rw [walkLevel_eq]; omega)
    have big := maxIn_runs (m := m) (w := w) (sp := sp) (mem := mem) ProveDeep.t
      (env := Asm.assign env 4 (deepNeed f).toUInt64) (a := (ProveDeep.x : Expr))
      (b := (ProveDeep.t : Expr)) (x := deepNeed f) (y := most) (by simp [eval, Asm.assign])
      (by simp [eval, Asm.assign, h3]) (lt64 (deepNeed_le f)) (lt64 hmost)
    obtain ⟨env', run, h3', keep⟩ := deep_loop hf hd rest (a + 8 * (Plan.words f).length) (j + 1) N sp
      (max (deepNeed f) most)
      (Asm.assign (Asm.assign (Asm.assign (Asm.assign env 4 (deepNeed f).toUInt64) 3
        (max (deepNeed f) most).toUInt64) 7 (a + 8 * (Plan.words f).length).toUInt64) 8 (j.toUInt64 + 1))
      mem hrest frest hp.2 (Nat.max_le.mpr ⟨deepNeed_le f, hmost⟩) (by simp [Asm.assign])
      (by simp [Asm.assign]) (by simp [Asm.assign, h6]) (by simp [Asm.assign]) hN (by simp at hj; omega) s2
    refine ⟨env', Runs.loop_step 1 ?_ (by decide)
      (Runs.block_cons (Runs.call (by simp [eval, h7]) need)
        (Runs.block_cons big
          (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, h7]) skip)
            (Runs.set' (by simp [eval, Asm.assign, h8]))))) run, ?_, fun v a b c d => ?_⟩
    · -- One more child remains, so the count is still below the total.
      simp at hj
      have lt : j.toUInt64 < N.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, addr_toNat (by omega), addr_toNat hN]; omega
      simp [eval, Cond.holds, h8, h6, lt]
    · rw [h3']; simp [deepMost]
    · rw [keep v a b c d]; simp [Asm.assign, a, b, c, d]

end

/-- The prover's scratch bound is at most the cap. -/
theorem proveScratch_le (d : Desc) (size : Nat) : proveScratch d size ≤ scratchCap := sadd_le _ _

/-- The prover's scratch bound function returns the Lean bound of a well-formed type, for a word-sized size. -/
theorem prove_scratch_calls (hf : PlanFns m) (hd : m.fns.lookup "ssz_prove_deep" = some ProveDeep.fn)
    (hs : m.fns.lookup "ssz_prove_scratch" = some ProveScratch.fn) (d : Desc) (a size sp : Nat) (mem : Memory)
    (hw : WordsAt w mem a (Plan.words d)) (fits : Fits (Plan.words d)) (hp : d.wellFormed = .ok ())
    (hsz : size < 2 ^ 64) (stack : w.stackLo + 64 + 256 * (d.nesting + 2) ≤ sp) :
    Calls m w "ssz_prove_scratch" sp [a.toUInt64, size.toUInt64] mem (proveScratch d size).toUInt64 mem := by
  have room : w.stackLo + 8 + 8 * ProveScratch.fn.frame ≤ sp := by rw [proveScratchFrame]; omega
  have inner : w.stackLo + 256 * (d.nesting + 2) ≤ sp - 8 - 8 * ProveScratch.fn.frame := by
    rw [proveScratchFrame]; omega
  have rootC := rootScratch_exact hf d a size _ mem hw fits hp hsz inner
  have deepC := deep_calls hf hd d a _ mem hw fits hp inner
  have V : rootScratch d size ≤ scratchCap := varNeed_le d size
  have D := deepNeed_le d
  have Mle : max (rootScratch d size) (deepNeed d) ≤ scratchCap := Nat.max_le.mpr ⟨V, D⟩
  have S := sat_le size
  let E1 := Asm.assign (entryEnv [a.toUInt64, size.toUInt64]) 2 (rootScratch d size).toUInt64
  let E2 := Asm.assign E1 3 (deepNeed d).toUInt64
  let M := max (rootScratch d size) (deepNeed d)
  let E3 := Asm.assign E2 2 M.toUInt64
  let E4 := Asm.assign E3 2 (sadd M M).toUInt64
  let E5 := Asm.assign E4 1 (sat size).toUInt64
  let E6 := Asm.assign E5 3 (smul 32 (sat size)).toUInt64
  let E7 := Asm.assign E6 2 (sadd (sadd M M) (smul 32 (sat size))).toUInt64
  have c1 : Runs m w (sp - 8 - 8 * ProveScratch.fn.frame) (entryEnv [a.toUInt64, size.toUInt64]) mem
      (callInto ProveScratch.r "ssz_root_scratch" [ProveScratch.p, ProveScratch.size]) E1 mem :=
    Runs.call (by simp [eval, entryEnv]) rootC
  have c2 : Runs m w (sp - 8 - 8 * ProveScratch.fn.frame) E1 mem (callInto ProveScratch.t "ssz_prove_deep" [ProveScratch.p]) E2 mem :=
    Runs.call (by simp [eval, E1, Asm.assign, entryEnv]) deepC
  have c3 : Runs m w (sp - 8 - 8 * ProveScratch.fn.frame) E2 mem (maxIn ProveScratch.r ProveScratch.r ProveScratch.t) E3 mem :=
    maxIn_runs ProveScratch.r (by simp [eval, E2, E1, Asm.assign]) (by simp [eval, E2, Asm.assign]) (lt64 V) (lt64 D)
  have c4 : Runs m w (sp - 8 - 8 * ProveScratch.fn.frame) E3 mem (.block (saddIn ProveScratch.r ProveScratch.r ProveScratch.r)) E4 mem :=
    saddIn_runs ProveScratch.r (by simp [eval, E3, Asm.assign]) (by simp [eval, E3, Asm.assign]) Mle Mle
  have c5 : Runs m w (sp - 8 - 8 * ProveScratch.fn.frame) E4 mem (satIn ProveScratch.size) E5 mem :=
    satIn_runs ProveScratch.size (by simp [E4, E3, E2, E1, Asm.assign, entryEnv]) hsz
  have c6 : Runs m w (sp - 8 - 8 * ProveScratch.fn.frame) E5 mem (smulIn ProveScratch.t 32 ProveScratch.size) E6 mem :=
    smulIn_runs ProveScratch.t (x := 32) (by simp [eval]) (by simp [eval, E5, Asm.assign]) (by decide) S
  have c7 : Runs m w (sp - 8 - 8 * ProveScratch.fn.frame) E6 mem (.block (saddIn ProveScratch.r ProveScratch.r ProveScratch.t)) E7 mem :=
    saddIn_runs ProveScratch.r (by simp [eval, E6, E5, E4, Asm.assign]) (by simp [eval, E6, Asm.assign])
      (sadd_le _ _) (smul_le _ _)
  have c8 := saddIn_runs (m := m) (w := w) (sp := sp - 8 - 8 * ProveScratch.fn.frame) (mem := mem) (env := E7) ProveScratch.r
    (a := (ProveScratch.r : Expr)) (b := ((2 ^ 20 : Nat) : Expr)) (x := sadd (sadd M M) (smul 32 (sat size)))
    (y := 2 ^ 20) (by simp [eval, E7, Asm.assign]) (by simp [eval]) (sadd_le _ _) (by decide)
  refine Calls.fn hs room rfl (Runs.block_append (Runs.block_append (Runs.block_append (Runs.block_append
    (Runs.block_cons c1 (Runs.block_cons c2 (Runs.block_cons c3 (Runs.block_nil _ _ _ _ _)))) c4)
    (Runs.block_cons c5 (Runs.block_cons c6 (Runs.block_nil _ _ _ _ _)))) c7) c8) ?_
  simp [ProveScratch.fn, eval, Asm.assign, proveScratch, M]

end Ssz.Native.Driver
