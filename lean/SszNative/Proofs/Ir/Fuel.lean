import SszNative.Ir.Semantics

/-!
More fuel never changes what a run means.
-/

namespace Ssz.Native.Ir

open Ssz.Native.Asm

/-- A run that has a meaning with some fuel has the same meaning with one more. -/
theorem exec_succ (m : Module) (w : World) :
    ∀ (fuel sp : Nat) (env : Env) (mem : Memory) (stmt : Stmt) (r : Env × Memory),
      exec m w fuel sp env mem stmt = some r → exec m w (fuel + 1) sp env mem stmt = some r := by
  intro fuel
  induction fuel with
  | zero => intro sp env mem stmt r h; simp [exec] at h
  | succ n ih =>
    intro sp env mem stmt r h
    cases stmt with
    | skip => simpa [exec] using h
    | set x e => simpa [exec] using h
    | store wd a v => simpa [exec] using h
    | seq a b =>
      rw [exec] at h ⊢; simp only [bind, Option.bind] at h ⊢
      cases ha : exec m w n sp env mem a with
      | none => simp [ha] at h
      | some p => simp only [ha] at h; rw [ih _ _ _ _ _ ha]; exact ih _ _ _ _ _ h
    | ite c t e =>
      rw [exec] at h ⊢; simp only [bind, Option.bind] at h ⊢
      cases hc : eval w env mem c with
      | none => simp [hc] at h
      | some v =>
        simp only [hc] at h ⊢
        by_cases hv : (v != 0) = true
        · simp only [hv, if_true] at h ⊢; exact ih _ _ _ _ _ h
        · simp only [hv, Bool.false_eq_true, if_false] at h ⊢; exact ih _ _ _ _ _ h
    | loop c body =>
      rw [exec] at h ⊢; simp only [bind, Option.bind] at h ⊢
      cases hc : eval w env mem c with
      | none => simp [hc] at h
      | some v =>
        simp only [hc] at h ⊢
        by_cases hz : (v == 0) = true
        · simp only [hz, if_true] at h ⊢; exact h
        · simp only [hz, Bool.false_eq_true, if_false] at h ⊢
          cases hb : exec m w n sp env mem body with
          | none => simp [hb] at h
          | some p => simp only [hb] at h; rw [ih _ _ _ _ _ hb]; exact ih _ _ _ _ _ h
    | call f args dst =>
      rw [exec] at h ⊢; simp only [bind, Option.bind] at h ⊢
      cases hv : args.mapM (eval w env mem) with
      | none => simp [hv] at h
      | some values =>
        simp only [hv] at h ⊢
        cases hf : m.fns.lookup f with
        | none => simp only [hf] at h ⊢; exact h
        | some fn =>
          simp only [hf] at h ⊢
          by_cases room : (decide (w.stackLo + 8 + 8 * fn.frame ≤ sp) && values.length == fn.params) = true
          · simp only [room, if_true] at h ⊢
            cases hb : exec m w n (sp - 8 - 8 * fn.frame) (entryEnv values) mem fn.body with
            | none => simp [hb] at h
            | some p => simp only [hb] at h; rw [ih _ _ _ _ _ hb]; exact h
          · simp only [room, Bool.false_eq_true, if_false] at h; simp at h

/-- More fuel never takes a meaning away. -/
theorem exec_mono (m : Module) (w : World) (fuel more sp : Nat) (env : Env) (mem : Memory) (stmt : Stmt)
    (r : Env × Memory) (h : exec m w fuel sp env mem stmt = some r) : exec m w (fuel + more) sp env mem stmt = some r := by
  induction more with
  | zero => exact h
  | succ k ih => exact exec_succ m w _ _ _ _ _ _ ih

end Ssz.Native.Ir
