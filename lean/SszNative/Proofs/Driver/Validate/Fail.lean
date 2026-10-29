import SszNative.Proofs.Driver.Validate.Probes
import SszNative.Proofs.Ir.Frame

/-!
Writing a refusal, and the memory it leaves alone.

A refusal is written once, at its own four words, which the plan and the encoding never share.
-/

namespace Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open Ssz Ssz.Native Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Ir.Stmt Ssz.Native.Ir.Expr

/-- A byte away from the four words is the byte before. -/
theorem wrote4_far (mem : Memory) (err : Nat) (a b c d : UInt64) (x : Nat) (far : x < err ∨ err + 32 ≤ x) :
    wrote4 mem err a b c d x = mem x := by
  simp only [wrote4, Asm.store]
  split <;> (try omega)
  split <;> (try omega)
  split <;> (try omega)
  split <;> (try omega)
  rfl

/-- Words of a plan clear of the refusal read the same after it. -/
theorem PlanAt.wrote4 {w : World} {mem : Memory} {p : Nat} {ws : List Nat} (h : PlanAt w mem p ws) (err : Nat)
    (clear : Clear err p (8 * ws.length)) (a b c d : UInt64) :
    PlanAt w (Validate.wrote4 mem err a b c d) p ws := by
  refine ⟨h.1, fun i hi => ?_⟩
  rw [← h.2 i hi]
  apply readLE_congr
  intro k hk
  apply wrote4_far
  unfold Clear at clear; omega

/-- Bytes of an encoding clear of the refusal read the same after it. -/
theorem DataAt.wrote4 {w : World} {mem : Memory} {base : Nat} {b : ByteArray} (h : DataAt w mem base b) (err : Nat)
    (clear : Clear err base b.size) (a c d e : UInt64) :
    DataAt w (Validate.wrote4 mem err a c d e) base b := by
  refine ⟨h.1, fun i hi => ?_⟩
  rw [← h.2 i hi]
  apply wrote4_far
  unfold Clear at clear; omega

/-- Writing four words at an address readable for 32 bytes: arguments the address, then the words. -/
theorem fail_calls {m : Module} {w : World} (hm : Loaded m) (err sp : Nat) (mem : Memory)
    (ok : w.access err 32 = true) (room : w.stackLo + 64 ≤ sp) (a b c d : UInt64) :
    Calls m w "ssz_validate_fail" sp [UInt64.ofNat err, a, b, c, d] mem 1 (wrote4 mem err a b c d) := by
  have bound : err + 32 ≤ 2 ^ 63 := by
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at ok; exact ok.1
  have acc : ∀ k, k + 8 ≤ 32 → w.access (err + k) 8 = true := fun k hk => access_sub ok (by omega) (by omega)
  refine Calls.body 7 hm.fail rfl (by omega) rfl ?_
  simp only [failFn]
  refine Wp.store (x := UInt64.ofNat err) (y := a) (by wev []) (by wev []) (by have := acc 0 (by omega); simp only [Nat.add_zero] at this; wonly [this]) ?_
  refine Wp.store (x := UInt64.ofNat (err + 8)) (y := b) (by wev []) (by wev []) (by wonly [acc 8 (by omega)]) ?_
  refine Wp.store (x := UInt64.ofNat (err + 16)) (y := c) (by wev []) (by wev []) (by wonly [acc 16 (by omega)]) ?_
  refine Wp.store (x := UInt64.ofNat (err + 24)) (y := d) (by wev []) (by wev []) (by wonly [acc 24 (by omega)]) ?_
  refine Wp.done ⟨rfl, ?_⟩
  simp only [wrote4, Width.bytes]
  wonly []

set_option hygiene false in
/--
Takes a refusal at the head of a block: four words written, and one returned.

The proof's context names the module's loading `hm`, the refusal's room `ok`, and the stack's room `room`.
-/
macro "wfail" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    try show Ssz.Native.Ir.Wp _ _ _ (Ssz.Native.Ir.Stmt.block _) _ _ _
    refine Ssz.Native.Ir.Wp.call ?_ (fail_calls hm _ _ _ ok ?_ ?_ ?_ ?_ ?_) ?_
    first | focus ((wev [$args,*]); done) | skip
    focus (simp only [Room] at room; omega)))

end Ssz.Native.Driver.Validate
