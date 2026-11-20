import SszNative.Driver.Prove
import SszNative.Proofs.Driver.Root.Progressive
import SszNative.Proofs.Driver.Branch.Small

/-!
The compiled spine driver writes the Lean progressive root of a run of nodes whose first subtree is a power of four wide.

It runs the same subtree loop and fold as the progressive tree driver, from a later first level.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.ProveProof

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr

/-- Where the spine driver keeps each part of its state. -/
def proveVars : SpineVars where
  slot
    | .nodes => 0 | .count => 1 | .width => 2 | .out => 3 | .scratch => 4 | .ctx => 5 | .k => 6 | .start => 7
    | .lg => 8 | .here => 9 | .sink => 10 | .i => 11
  apart a b h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- The spine driver's frame holds nineteen words. -/
theorem spineFrame : ProveSpine.fn.frame = 19 := by decide

set_option maxHeartbeats 2000000 in
/--
The spine driver writes the Lean progressive root of a run of nodes, from a first subtree 4^j wide.

Memory changes only at the output, in the scratch, and in the padding area.
-/
theorem spine_calls {m : Module} {w : World} (hash : HashingOk m w)
    (hf : m.fns.lookup "ssz_prove_spine" = some ProveSpine.fn)
    (hl : m.fns.lookup "ssz_branch_level" = some Level.fn) {sp : Nat}
    (room : w.stackLo + 8 + 8 * ProveSpine.fn.frame + treeStack ≤ sp) {mem : Memory}
    {nodes count out scratch ctx table zeros pad : Nat} {mask : UInt64} {x : ByteArray}
    (pre : ProgPre w mem nodes count out scratch ctx table zeros pad mask x) {j : Nat} (jle : j ≤ 30) :
    ∃ mem', Calls m w "ssz_prove_spine" sp [UInt64.ofNat nodes, UInt64.ofNat count, UInt64.ofNat (4 ^ j),
        UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx] mem 0 mem' ∧
      nodeAt mem' out = (merkleizeProgressive x count (4 ^ j)).data ∧ RootReady w ctx table zeros pad mask mem' ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (scratch ≤ a ∧ a < scratch + progressiveSpan count) →
        ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a := by
  have span : progressiveSpan count = 4608 + 32 * count := rfl
  have bs := access_bound pre.sAcc
  have bo := access_bound pre.oAcc
  have bound : addressBound = 2 ^ 63 := rfl
  have xin := pre.inside
  have xs := pre.small
  have few := pre.few
  have treeH : treeStack = 160 + hashStack := rfl
  let sp' := sp - 8 - 8 * ProveSpine.fn.frame
  have room' : w.stackLo + treeStack ≤ sp' := by simp only [sp', spineFrame] at room ⊢; omega
  have wide := level_wide' (show j ≤ 31 by omega)
  have wv : (UInt64.ofNat (4 ^ j)).toNat = 4 ^ j := ofNat_toNat (by omega)
  have lv : Nat.log2 (4 ^ j) = 2 * j := by rw [four_pow_eq, Nat.log2_two_pow]
  let E0 := entryEnv [UInt64.ofNat nodes, UInt64.ofNat count, UInt64.ofNat (4 ^ j), UInt64.ofNat out,
    UInt64.ofNat scratch, UInt64.ofNat ctx]
  have ev0 : SpineEnv proveVars E0 nodes count out scratch ctx := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have s1 := Runs.set' (m := m) (w := w) (sp := sp') (env := E0) (mem := mem) (x := 6) (eval_lit 0)
  let E1 := Asm.assign E0 6 (UInt64.ofNat 0)
  have s2 := Runs.set' (m := m) (w := w) (sp := sp') (env := E1) (mem := mem) (x := 7) (eval_lit 0)
  let E2 := Asm.assign E1 7 (UInt64.ofNat 0)
  have s3 := Runs.call (m := m) (sp := sp') (env := E2) (mem := mem) (dst := 8) (args := [ProveSpine.width])
    (values := [UInt64.ofNat (4 ^ j)]) rfl (BranchProof.level_calls (w := w) hl (by omega) (UInt64.ofNat (4 ^ j)) mem)
  let E3 := Asm.assign E2 8 (Nat.log2 (UInt64.ofNat (4 ^ j)).toNat).toUInt64
  have at0 : SpineAt proveVars j mem nodes count out scratch ctx pad x E3 mem 0 :=
    ⟨((ev0.write .k _).write .start _).write .lg _, rfl, by rw [spineStart, Nat.mul_zero]; rfl,
      by rw [Nat.add_zero]; rfl,
      by show (Nat.log2 (UInt64.ofNat (4 ^ j)).toNat).toUInt64 = _; rw [wv, lv, Nat.add_zero],
      Or.inl rfl, fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ _ => rfl⟩
  obtain ⟨e1, mm1, run1, k, ⟨ev, hk, hs, -, -, lev, roots, frame⟩, done⟩ :=
    spineLoop_ends hash room' pre proveVars jle at0
  have k31 := levelsFrom_le jle few lev
  have ready1 := pre.ready.within (o := scratch) (n := progressiveSpan count) pre.sCtx pre.sTable pre.sZeros
    fun a o pd => frame a o pd
  have c := eval_eq (w := w) (env := e1) (mem := mm1) (a := ProveSpine.k) (b := 0) (eval_var hk) (eval_lit 0)
    (by omega) (by decide)
  have lead : ∀ {r : List Stmt} {e' : Env} {mm' : Memory}, Runs m w sp' e1 mm1 (.block r) e' mm' →
      Runs m w sp' E0 mem (.block ([ProveSpine.k ::= 0, ProveSpine.start ::= 0,
        callInto ProveSpine.lg "ssz_branch_level" [ProveSpine.width], spineLoop proveVars] ++ r)) e' mm' :=
    fun h => Runs.block_append (Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons s3
      (Runs.block_cons run1 (Runs.block_nil _ _ _ _ _))))) h
  by_cases empty : k = 0
  · -- No subtree: the root is the zero node.
    subst empty
    rw [ite_eq_left rfl] at c
    have z := zero32_at (m := m) (sp := sp') (env := e1) (mem := mm1) (dst := ProveSpine.out)
      (fun _ => eval_var ev.out) pre.oAcc
    have body : Runs m w sp' E0 mem ProveSpine.fn.body e1 (zeroed mm1 out) :=
      lead (Runs.block_cons (Runs.ifElse_true 1 c (by decide) z) (Runs.block_nil _ _ _ _ _))
    have none : count = 0 := by simp only [spineStart] at done; omega
    refine ⟨_, Calls.fn hf (by rw [spineFrame] at room ⊢; omega) rfl body rfl, ?_, ?_, fun a o s pd => ?_⟩
    · rw [nodeAt_zeroed, merkleizeProgressive_spineFromAt, spineFromAt_done j x (by omega) (by omega)]
    · exact ready1.within (o := out) (n := 32) pre.oCtx pre.oTable pre.oZeros fun a o _ => zeroed_outside o
    · rw [zeroed_outside o]; exact frame a s pd
  · -- The spine closes with a zero node, then folds from the last pair up.
    rw [ite_eq_right (by omega)] at c
    have less : ∀ l < k, 4 ^ j * spineStart l < count := fun l hl => by
      rcases lev with h | h
      · omega
      · exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (spineStart_mono (by omega))) h
    have kc : k ≤ count := by have := le_startFrom j (k - 1); have := less (k - 1) (by omega); omega
    have z := zero32_at (m := m) (sp := sp') (env := e1) (mem := mm1)
      (dst := ProveSpine.scratch + 64 * ProveSpine.k - 32) (a := scratch + 64 * k - 32)
      (fun _ => eval_sub (eval_add (eval_var ev.scratch) (eval_mul (eval_lit 64) (eval_var hk))) (eval_lit 32)
        (by omega)) (access_sub pre.sAcc (by omega) (by omega))
    have si := Runs.set' (m := m) (w := w) (sp := sp') (env := e1) (mem := zeroed mm1 (scratch + 64 * k - 32))
      (x := 11) (eval_sub (eval_var hk) (eval_lit 1) (by omega))
    have fold0 : SpineFoldAt proveVars j mem nodes count out scratch ctx pad x
        (Asm.assign e1 11 (UInt64.ofNat (k - 1))) (zeroed mm1 (scratch + 64 * k - 32)) k (k - 1) := by
      refine ⟨ev.write .i _, assign_eq, by omega, fun l hl => ?_, ?_, fun a o pd => ?_⟩
      · rw [nodeAt_congr (m₂ := mm1) fun q hq => zeroed_outside (by omega)]; exact roots l hl
      · rw [show scratch + 64 * (k - 1) + 32 = scratch + 64 * k - 32 by omega, nodeAt_zeroed,
          show k - 1 + 1 = k by omega, spineFromAt_done j x kc done]
      · rw [zeroed_outside (by omega)]; exact frame a o pd
    obtain ⟨e2, mm2, run2, ⟨ev2, -, -, roots2, right2, frame2⟩⟩ := spineFold_ends hash (sp := sp')
      (by omega) pre proveVars (by omega) less fold0
    have ready2 := pre.ready.within (o := scratch) (n := progressiveSpan count) pre.sCtx pre.sTable pre.sZeros
      fun a o pd => frame2 a o pd
    obtain ⟨mm3, call, node, keep⟩ := pairInto_runs (m := m) (w := w) hash (sp := sp') (by omega) (env := e2)
      (mem := mm2) (dst := 10) (out := out) (left := scratch)
      (args := [ProveSpine.out, ProveSpine.scratch, ProveSpine.scratch + 32, 1, ProveSpine.ctx])
      ready2 (access_sub pre.sAcc (by omega) (by omega)) (by omega) pre.oAcc
      (apart_sub pre.sO (by omega) (by omega)) (apart_sub pre.sPad (by omega) (by omega)) pre.oPad pre.oCtx
      pre.oTable
      (by
        have eo : e2 3 = UInt64.ofNat out := ev2.out
        have es : e2 4 = UInt64.ofNat scratch := ev2.scratch
        have ec : e2 5 = UInt64.ofNat ctx := ev2.ctx
        simp only [List.mapM_cons, List.mapM_nil, eval_var eo, eval_var es, eval_add (eval_var es) (eval_lit 32),
          eval_var ec]
        rfl)
    have body : Runs m w sp' E0 mem ProveSpine.fn.body (Asm.assign e2 10 0) mm3 :=
      lead (Runs.block_cons (Runs.ifElse_false c (Runs.block_append z (Runs.block_cons si (Runs.block_cons run2
        (Runs.block_cons call (Runs.block_nil _ _ _ _ _)))))) (Runs.block_nil _ _ _ _ _))
    refine ⟨_, Calls.fn hf (by rw [spineFrame] at room ⊢; omega) rfl body rfl, ?_, ?_, fun a o s pd => ?_⟩
    · have r0 := roots2 0 (by omega)
      simp only [Nat.mul_zero, Nat.add_zero] at r0 right2
      rw [node, r0, right2, merkleizeProgressive_spineFromAt, spineFromAt_step j x (less 0 (by omega)),
        RootProof.hashPair_data _ _ (spineTreeAt_size xin xs j (less 0 (by omega)))
          (spineFromAt_size xin xs j (by omega))]
    · exact ready2.within (o := out) (n := 32) pre.oCtx pre.oTable pre.oZeros fun a o pd => keep a o pd
    · rw [keep a o pd]; exact frame2 a s pd

end EthLib.Consensus.Ssz.Native.Driver.ProveProof
