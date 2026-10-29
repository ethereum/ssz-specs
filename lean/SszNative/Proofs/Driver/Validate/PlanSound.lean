import SszNative.Proofs.Driver.Validate.PlanBack

/-!
The plan's own check accepts exactly the plans of legal types.

When it returns zero for readable bytes, those bytes are the plan of a type that is legal, fits the native check,
names its fields by position, and nests no deeper than a plan may be.
With room on the stack for the deepest plan, it returns zero for every such plan.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr

/-! Words back to bytes. -/

/-- Bytes that spell a number, little-endian, are its base-256 digits. -/
theorem bytesNat_byte (f : Nat → UInt8) : ∀ (a n x : Nat), bytesNat f a n = x →
    ∀ k < n, (f (a + k)).toNat = x / 256 ^ k % 256
  | _, 0, _, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | a, n + 1, x, h, k, hk => by
    simp only [bytesNat] at h
    have lt := (f a).toNat_lt
    cases k with
    | zero => simp; omega
    | succ k =>
      have := bytesNat_byte f (a + 1) n (x / 256) (by omega) k (by omega)
      rw [show a + (k + 1) = a + 1 + k by omega, this, Nat.div_div_eq_div_mul, ← Nat.pow_succ']

/-- A word's bytes in memory, each as the plan writes it. -/
theorem byte_of_word {w : World} {mem : Memory} {p : Nat} {ws : List Nat} (hp : PlanAt w mem p ws)
    (small : ∀ x ∈ ws, x < 2 ^ 64) (j k : Nat) (hj : j < ws.length) (hk : k < 8) :
    mem (p + (8 * j + k)) = UInt8.ofNat (ws[j] >>> (8 * k)) := by
  have r := hp.2 j hj
  have lt := small _ (List.getElem_mem hj)
  have bn : bytesNat mem (p + 8 * j) 8 = ws[j] := by
    rw [← readLE_toNat _ _ _ (by omega), r]
    simp; omega
  have := bytesNat_byte mem _ 8 _ bn k hk
  apply UInt8.toNat_inj.mp
  rw [← Nat.add_assoc, this]
  simp [Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- A plan's words in memory are its bytes, when each word fits one. -/
theorem planBytes_of_planAt {w : World} {mem : Memory} {p : Nat} {d : Desc} (hp : PlanAt w mem p (Plan.words d))
    (small : ∀ x ∈ Plan.words d, x < 2 ^ 64) : PlanBytes w mem p d := by
  refine ⟨by rw [encode_size]; exact hp.1, fun i hi => ?_⟩
  have hi' := hi
  rw [encode_size] at hi'
  obtain ⟨j, k, hk, rfl⟩ : ∃ j k, k < 8 ∧ i = 8 * j + k := ⟨i / 8, i % 8, by omega, by omega⟩
  rw [byte_of_word hp small j k (by omega) hk]
  simp only [Plan.encode]
  show _ = (((Plan.words d).flatMap Plan.wordBytes).toArray)[8 * j + k]'_
  simp only [List.getElem_toArray, flatMap_wordBytes_get (Plan.words d) j k (by omega) hk]

/-! The whole check, read backward. -/

/-- A check that holds anything but zero does not return zero. -/
theorem check_post_skip {w : World} {env : Env} {k : Memory} {P : Prop} (h : env 2 ≠ 0) :
    ∀ r, eval w env k checkPlanFn.result = some r → r = 0 → P := by
  intro r hr h0
  simp only [checkPlanFn] at hr
  exact absurd ((Option.some.inj hr).trans h0) h

set_option maxHeartbeats 4000000 in
/--
What the plan's own check accepts: when it returns zero for a readable plan, the plan's bytes are the plan of a type
that is legal, fits the native check, names its fields by position, and nests no deeper than a plan may be.

The check leaves memory as it was.
-/
theorem checkPlan_sound {m : Module} {w : World} (hm : Loaded m) (plan len sp : Nat) (mem mem' : Memory)
    (acc : w.access plan len = true)
    (call : Calls m w "ssz_check_plan" sp [UInt64.ofNat plan, UInt64.ofNat len] mem 0 mem') :
    mem' = mem ∧ ∃ d, d.wellFormed = .ok () ∧ fitsNative d = true ∧ named d = true ∧ d.nesting ≤ maxNesting ∧
      PlanBytes w mem plan d ∧ (Plan.encode d).size = len := by
  have keep := Calls.keeps hm.keeps (by simp [planNames]) call
  refine ⟨keep, ?_⟩
  have s63 : plan + len ≤ 2 ^ 63 := by
    simp only [World.access, addressBound, Bool.and_eq_true, decide_eq_true_eq] at acc; omega
  -- What the body establishes: a sound type's words fill the plan, nested no deeper than a plan may be.
  suffices h : ∃ d, Sound d ∧ d.nesting ≤ maxNesting ∧ PlanAt w mem plan (Plan.words d) ∧
      8 * (Plan.words d).length = len by
    obtain ⟨d, sd, deep, hp, hl⟩ := h
    exact ⟨d, sd.wf, sd.fits, sd.named, deep, planBytes_of_planAt hp sd.small, by rw [encode_size]; exact hl⟩
  refine Calls.of_pc (P := fun r _ => r = 0 → ∃ d, Sound d ∧ d.nesting ≤ maxNesting ∧
    PlanAt w mem plan (Plan.words d) ∧ 8 * (Plan.words d).length = len) 7 hm.checkPlan rfl ?_ call rfl
  simp only [checkPlanFn]
  by_cases l8 : len % 8 = 0
  case neg =>
    psteps [l8]
    exact check_post_skip (by wfin [])
  psteps [l8]
  pcall []
  intro q m1 hq
  have k1 := Calls.keeps hm.keeps (by simp [planNames]) hq
  subst m1
  by_cases qd : q = 18446744073709551614
  · psteps [qd, deep_]
    exact check_post_skip (by wfin [])
  by_cases qe : q = UInt64.ofNat (plan + len)
  case neg =>
    psteps [qd, qe, deep_]
    exact check_post_skip (by wfin [])
  subst qe
  have ne : plan + len ≠ 18446744073709551614 := by omega
  psteps [ne, deep_]
  pcall []
  intro q2 m2 hc
  have k2 := Calls.keeps hm.keeps (by simp [planNames]) hc
  subst m2
  rcases plan_back hm (plan + len) plan (by omega) (by simpa using acc) _ _ _ _ hc with rfl | ⟨d, sd, hp, hs, rfl⟩
  · have nn : ¬ 18446744073709551615 = plan + len := by omega
    psteps [nn]
    exact check_post_skip (by wfin [])
  by_cases eqd : plan + 8 * (Plan.words d).length = plan + len
  case neg =>
    psteps [eqd]
    exact check_post_skip (by wfin [])
  psteps [eqd]
  intro r _ _
  refine ⟨d, sd, ?_, hp, by omega⟩
  -- A type nested deeper would have made the nesting walk answer too deep.
  rcases Nat.lt_or_ge maxNesting d.nesting with deep | ok
  · have walk := depth_deep hm d sd.wf sd.fits plan (plan + len) maxNesting
      (w.stackLo + (2 * maxNesting + 2) * 5120 + 2 * 160) mem hp (by omega) s63 deep (by decide) (Nat.le_refl _)
    have := (Calls.agree hm.keeps.closed (by simp [planNames]) hq walk).1
    exact absurd this (by simp only [tooDeep]; intro h; exact qd (by rw [h]; rfl))
  · exact ok

/--
The plan's own check, both ways: for readable bytes, with room on the stack for the deepest plan, it returns zero
exactly when the bytes are the plan of a type that is legal, fits the native check, names its fields by position,
and nests no deeper than a plan may be.
-/
theorem checkPlan_iff {m : Module} {w : World} (hm : Loaded m) (plan len sp : Nat) (mem : Memory)
    (acc : w.access plan len = true) (room : Room w sp (2 * maxNesting) 3) :
    (∃ mem', Calls m w "ssz_check_plan" sp [UInt64.ofNat plan, UInt64.ofNat len] mem 0 mem') ↔
      ∃ d, d.wellFormed = .ok () ∧ fitsNative d = true ∧ named d = true ∧ d.nesting ≤ maxNesting ∧
        PlanBytes w mem plan d ∧ (Plan.encode d).size = len := by
  constructor
  · rintro ⟨mem', call⟩
    exact (checkPlan_sound hm plan len sp mem mem' acc call).2
  · rintro ⟨d, wf, fit, nm, deep, bytes, size⟩
    refine ⟨mem, ?_⟩
    have := checkPlan_calls hm d wf fit nm deep plan sp mem bytes (by simp only [Room] at room ⊢; omega)
    rwa [size] at this

end EthLib.Consensus.Ssz.Native.Driver.Validate
