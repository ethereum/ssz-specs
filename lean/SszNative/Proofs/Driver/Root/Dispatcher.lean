import SszNative.Proofs.Driver.Root.Sequence

/-!
The dispatcher writes the Lean root of a range, by the driver its type's tag names.

A type rooted as fixed-size records is rooted as a column of one, into the scratch, then copied to the output.
Every other type is passed to its own driver, whose call is a hypothesis here.
-/

namespace Ssz.Native.Driver

open Ssz Ssz.Native.Ir Ssz.Native.Ir.Expr Ssz.Native.Ir.Stmt Ssz.Native.Asm

/-- The driver the dispatcher passes a type to when the type is not rooted as fixed-size records. -/
def rangeDriver : Desc → String
  | .byteList _ => "ssz_root_bytes"
  | .bitList _ | .progressiveBitList _ => "ssz_root_bits"
  | .list _ _ | .progressiveList _ _ => "ssz_root_list"
  | .vector _ _ => "ssz_root_vector"
  | .container _ _ => "ssz_root_container"
  | .progressiveContainer _ _ _ => "ssz_root_progressive_container"
  | .compatibleUnion _ _ => "ssz_root_union"
  | _ => "ssz_roots_of"

/-- The dispatcher's frame holds seventeen words. -/
theorem rootOfFrame : RootOf.fn.frame = 17 := by decide

/-- A type rooted as fixed-size records has the bound of one record. -/
theorem varNeed_plain {d : Desc} (pl : plain d = true) (size : Nat) : varNeed d size = rootsNeed d 1 := by
  cases d <;> simp_all [varNeed, plain]

/-- A range of a type rooted as fixed-size records that decodes is exactly one record wide. -/
theorem plain_width {d : Desc} (pl : plain d = true) {b : ByteArray} {start stop : Nat} (inside : stop ≤ b.size)
    (accepted : ∃ v, deserialize d (slice b start stop) = .ok v) : stop - start = fixedWidth d := by
  obtain ⟨v, read⟩ := accepted
  have fixed := RootProof.hasWidth_of_plain d pl
  have size := slice_size b start stop inside
  have head := deserialize_head d (slice b start stop) fixed
  by_cases huge : composite d = true ∧ (slice b start stop).size ≥ offsetBound
  · have := head.1 huge; simp [read, Except.map] at this
  · by_cases wrong : (slice b start stop).size ≠ fixedWidth d
    · have := head.2 huge wrong; simp [read, Except.map] at this
    · omega

/-- A call passing every argument on to a named driver is that driver's call. -/
theorem pass_runs {m : Module} {w : World} {name : String} {d : Desc} (ok : RangeOk m w name d) {sp : Nat}
    (room : w.stackLo + rootStack d ≤ sp) {mem : Memory} {p base start stop out scratch ctx table zeros pad : Nat}
    {mask : UInt64} {b : ByteArray} (pre : RangePre w mem d p base start stop out scratch ctx table zeros pad mask b)
    {env : Env} (ev : RangeEnv env p (base + start) (stop - start) out scratch ctx) :
    ∃ mem', Runs m w sp env mem (RootOf.pass name) (Asm.assign env 9 0) mem' ∧
      RangePost w mem mem' out scratch (varNeed d (stop - start)) ctx table zeros pad mask (rootOf d b start stop) := by
  obtain ⟨mem', call, post⟩ := ok sp mem p base start stop out scratch ctx table zeros pad mask b (by omega) pre
  refine ⟨mem', Runs.call (by
    simp only [List.mapM_cons, List.mapM_nil, eval_var ev.p, eval_var ev.src, eval_var ev.size, eval_var ev.out,
      eval_var ev.scratch, eval_var ev.ctx]
    rfl) call, post⟩

set_option maxHeartbeats 2000000 in
/-- A type rooted as fixed-size records is rooted as one record into the scratch, then copied to the output. -/
theorem single_runs {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RangeFns m)
    {d : Desc} (pl : plain d = true) {sp : Nat} (room : w.stackLo + rootStack d ≤ sp) {mem : Memory}
    {p base start stop out scratch ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : RangePre w mem d p base start stop out scratch ctx table zeros pad mask b)
    {env : Env} (ev : RangeEnv env p (base + start) (stop - start) out scratch ctx) :
    ∃ env' mem', Runs m w sp env mem (.block RootOf.single) env' mem' ∧
      RangePost w mem mem' out scratch (varNeed d (stop - start)) ctx table zeros pad mask (rootOf d b start stop) := by
  have one := nesting_pos d
  have wide := width_narrow d pl pre.thin
  have exact := plain_width pl pre.inside pre.accepted
  have need := varNeed_plain pl (stop - start)
  have capv := cap_eq
  have bound : addressBound = 2 ^ 63 := rfl
  have sAcc := pre.sAcc
  have sSlack := pre.sSlack
  have sB := pre.sB
  have sPad := pre.sPad
  have sCtx := pre.sCtx
  have sTable := pre.sTable
  have sZeros := pre.sZeros
  have sPlan := pre.sPlan
  have sOut := pre.sOut
  have below := pre.below
  rw [need] at sAcc sSlack sB sPad sCtx sTable sZeros sPlan sOut below
  have spread := pre.spread
  have inside := pre.inside
  -- The width, then the record's root into the scratch.
  have width := planWidth_calls fns.roots.plan d p sp mem pre.plan pre.sound pre.thin (by
    simp only [rootStack] at room; omega)
  have r1 := Runs.call (m := m) (sp := sp) (env := env) (mem := mem) (dst := 8) (args := [RootOf.p])
    (by simp only [List.mapM_cons, List.mapM_nil, eval_var ev.p]; rfl) width
  have ordered := pre.ordered
  have insideR : ∀ i < 1, start + fixedWidth d * i + fixedWidth d ≤ b.size := fun i hi => by
    obtain rfl : i = 0 := by omega
    omega
  have spreadR : base + start + fixedWidth d * 1 + fixedWidth d ≤ addressBound := by
    have := pre.ordered
    omega
  have rpre : RootsPre w mem d p base start (fixedWidth d) 1 scratch ctx table zeros pad mask b :=
    { ready := pre.ready, plan := pre.plan, holds := pre.holds, bAcc := pre.bAcc, gap := Nat.le_refl _,
      strideSmall := by omega, pos := Nat.le_refl _, inside := insideR, spread := spreadR, below := below, acc := sAcc, slack := sSlack, oB := sB, oPad := sPad, oCtx := sCtx,
      oTable := sTable, oZeros := sZeros, oPlan := sPlan, bPad := pre.bPad, planPad := pre.planPad,
      usize := pre.usize }
  obtain ⟨mem1, call1, held1, ready1, keep1⟩ := rootsOf_ok hash gmod fns.roots d ⟨pl, pre.sound, pre.thin⟩ sp mem p
    base start (fixedWidth d) 1 scratch ctx table zeros pad mask b (by
      simp only [rootStack, rootsStack, columnsStack, hashStack] at room ⊢; omega) rpre
  have ev1 := ev.write (x := 8) (fixedWidth d).toUInt64 (by decide)
  have r2 := Runs.call (m := m) (sp := sp) (env := Asm.assign env 8 (fixedWidth d).toUInt64) (mem := mem) (dst := 9)
    (args := [RootOf.p, RootOf.src, RootOf.w, 1, RootOf.scratch, RootOf.ctx])
    (by
      simp only [List.mapM_cons, List.mapM_nil, eval_var ev1.p, eval_var ev1.src,
        eval_var (show Asm.assign env 8 (fixedWidth d).toUInt64 8 = UInt64.ofNat (fixedWidth d) from assign_eq),
        eval_var ev1.scratch, eval_var ev1.ctx]
      rfl) call1
  have ev2 := ev1.write (x := 9) 0 (by decide)
  -- The root, copied to the output.
  have rootsSize : (rootsOf d b start (fixedWidth d) 1).size = 32 :=
    (rpre.sized ⟨pl, pre.sound, pre.thin⟩)
  have r3 := copy32_runs (m := m) (sp := sp) (env := Asm.assign (Asm.assign env 8 (fixedWidth d).toUInt64) 9 0)
    (mem := mem1) (dst := RootOf.out) (src := RootOf.scratch) (fun _ => eval_var ev2.out)
    (fun _ => eval_var ev2.scratch) pre.oAcc (access_sub sAcc (by omega) (by
      have := rootsNeed_roots d 1; simp only [sat] at this; omega)) (apart_comm (apart_sub sOut (by omega) (by
      have := rootsNeed_roots d 1; simp only [sat] at this; omega)))
  have frame : ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (scratch ≤ a ∧ a < scratch + varNeed d (stop - start)) →
      ¬ (pad ≤ a ∧ a < pad + 1536) → copied mem1 out scratch 32 a = mem a := fun a o s pd => by
    rw [copied_out o]
    exact keep1 a (by rw [need] at s; exact s) pd
  refine ⟨_, _, Runs.block_cons r1 (Runs.block_cons r2 r3), ?_, pre.readyAfter frame, frame⟩
  rw [nodeAt_copied, RootProof.rootOf_plain d pl]
  have := nodeAt_of_holds held1 (i := 0) (by rw [rootsSize]; omega)
  simp only [Nat.mul_zero, Nat.add_zero] at this
  rw [this, nodeOf_single _ rootsSize]


/-- The dispatcher's branches on the tag. -/
abbrev dispatchChain : Stmt :=
  ifElse (eq RootOf.tag 3) [RootOf.pass "ssz_root_bytes"] [
  ifElse (eq RootOf.tag 5 ||| eq RootOf.tag 6) [RootOf.pass "ssz_root_bits"] [
  ifElse (eq RootOf.tag 8 ||| eq RootOf.tag 9) [RootOf.pass "ssz_root_list"] [
  ifElse (eq RootOf.tag 11) [RootOf.pass "ssz_root_progressive_container"] [
  ifElse (eq RootOf.tag 12) [RootOf.pass "ssz_root_union"] [
  ifElse (eq RootOf.tag 7 ||| eq RootOf.tag 10)
    [callInto RootOf.pl "ssz_plan_plain" [RootOf.p],
      ifElse RootOf.pl RootOf.single
        [ifElse (eq RootOf.tag 7) [RootOf.pass "ssz_root_vector"] [RootOf.pass "ssz_root_container"]]]
    RootOf.single]]]]]

/-- The dispatcher reads the tag, then branches on it. -/
theorem rootOf_body : RootOf.fn.body = .block [RootOf.tag ::= ld RootOf.p, dispatchChain] := rfl

/-- Decides one of the dispatcher's branch conditions on a known tag. -/
macro "tag_eval" h:term : tactic => `(tactic| simp [eval, Cond.holds, $h:term, Plan.tag, aluResult])

set_option maxHeartbeats 4000000 in
/--
The dispatcher writes the Lean root of a range of any type, given what the driver its type is passed to does.

A type rooted as fixed-size records needs no driver of its own.
-/
theorem rootOf_dispatch {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RangeFns m)
    (d : Desc) (sub : plain d = false → RangeOk m w (rangeDriver d) d) : RootOfOk m w d := by
  intro sp mem p base start stop out scratch ctx table zeros pad mask b room pre
  have room' : w.stackLo + rootStack d ≤ sp - 8 - 8 * RootOf.fn.frame := by rw [rootOfFrame]; omega
  generalize hsp : sp - 8 - 8 * RootOf.fn.frame = sp' at room'
  have ev := rangeEnv_entry p (base + start) (stop - start) out scratch ctx
  have tagE := eval_tag (e := RootOf.p) pre.plan (eval_var ev.p)
  have s1 := Runs.set' (m := m) (w := w) (sp := sp') (x := 6) tagE
  have ev1 := ev.write (x := 6) (Plan.tag d).toUInt64 (by decide)
  have t1 : Asm.assign (entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (stop - start),
      UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx]) 6 (Plan.tag d).toUInt64 6 = (Plan.tag d).toUInt64 :=
    assign_eq
  generalize Asm.assign (entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (stop - start),
    UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx]) 6 (Plan.tag d).toUInt64 = E1 at s1 ev1 t1
  suffices chain : ∃ E' mem', Runs m w sp' E1 mem dispatchChain E' mem' ∧
      RangePost w mem mem' out scratch (varNeed d (stop - start)) ctx table zeros pad mask (rootOf d b start stop) by
    obtain ⟨E', mem', run, post⟩ := chain
    refine ⟨mem', Calls.fn (env' := E') fns.rootOf (by rw [rootOfFrame]; omega) rfl ?_ rfl, post⟩
    rw [rootOf_body, hsp]
    exact Runs.block_cons s1 (Runs.block_cons run (Runs.block_nil _ _ _ _ _))
  have pass := fun (h : plain d = false) => pass_runs (sub h) room' pre ev1
  have single := fun (h : plain d = true) => single_runs hash gmod fns h room' pre ev1
  cases d with
  | byteList l =>
    obtain ⟨mem', run, post⟩ := pass rfl
    exact ⟨_, mem', Runs.ifElse_true 1 (by tag_eval t1) (by decide) (Runs.block_cons run (Runs.block_nil _ _ _ _ _)),
      post⟩
  | bitList l =>
    obtain ⟨mem', run, post⟩ := pass rfl
    exact ⟨_, mem', (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_true 1 (by tag_eval t1) (by decide) (Runs.block_cons run (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))), post⟩
  | progressiveBitList l =>
    obtain ⟨mem', run, post⟩ := pass rfl
    exact ⟨_, mem', (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_true 1 (by tag_eval t1) (by decide) (Runs.block_cons run (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))), post⟩
  | list e l =>
    obtain ⟨mem', run, post⟩ := pass rfl
    exact ⟨_, mem', (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_true 1 (by tag_eval t1) (by decide) (Runs.block_cons run (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))), post⟩
  | progressiveList e l =>
    obtain ⟨mem', run, post⟩ := pass rfl
    exact ⟨_, mem', (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_true 1 (by tag_eval t1) (by decide) (Runs.block_cons run (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))), post⟩
  | progressiveContainer a n fs =>
    obtain ⟨mem', run, post⟩ := pass rfl
    exact ⟨_, mem', (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_true 1 (by tag_eval t1) (by decide) (Runs.block_cons run (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))), post⟩
  | compatibleUnion s os =>
    obtain ⟨mem', run, post⟩ := pass rfl
    exact ⟨_, mem', (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_true 1 (by tag_eval t1) (by decide) (Runs.block_cons run (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))), post⟩
  | bool =>
    obtain ⟨E', mem', run, post⟩ := single rfl
    exact ⟨_, mem', (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) run) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))), post⟩
  | uint n =>
    obtain ⟨E', mem', run, post⟩ := single rfl
    exact ⟨_, mem', (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) run) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))), post⟩
  | byteVector n =>
    obtain ⟨E', mem', run, post⟩ := single rfl
    exact ⟨_, mem', (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) run) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))), post⟩
  | bitVector n =>
    obtain ⟨E', mem', run, post⟩ := single rfl
    exact ⟨_, mem', (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) run) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))), post⟩
  | vector e l =>
    have planRun := planPlain_calls fns.roots.plan _ p sp' mem pre.plan pre.sound (by
      simp only [rootStack] at room'; omega)
    have r1 := Runs.call (m := m) (sp := sp') (env := E1) (mem := mem) (dst := 7) (args := [RootOf.p])
      (by simp only [List.mapM_cons, List.mapM_nil, eval_var ev1.p]; rfl) planRun
    have ev2 := ev1.write (x := 7) (bitOf (plain (.vector e l))) (by decide)
    cases hp : plain (.vector e l)
    · obtain ⟨mem', run, post⟩ := pass_runs (sub hp) room' pre ev2
      have inner := Runs.ifElse_false (c := RootOf.pl) (yes := RootOf.single)
        (no := [ifElse (eq RootOf.tag 7) [RootOf.pass "ssz_root_vector"] [RootOf.pass "ssz_root_container"]])
        (by simp [eval, Asm.assign, bitOf, hp])
        (Runs.block_cons (Runs.ifElse_true 1 (by simp [eval, Cond.holds, Asm.assign, t1, Plan.tag]) (by decide) (Runs.block_cons run (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))
      exact ⟨_, mem', (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_true 1 (by tag_eval t1) (by decide) (Runs.block_cons r1 (Runs.block_cons inner (Runs.block_nil _ _ _ _ _)))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))), post⟩
    · obtain ⟨E', mem', run, post⟩ := single_runs hash gmod fns hp room' pre ev2
      have inner := Runs.ifElse_true (c := RootOf.pl) (yes := RootOf.single)
        (no := [ifElse (eq RootOf.tag 7) [RootOf.pass "ssz_root_vector"] [RootOf.pass "ssz_root_container"]]) 1
        (by simp [eval, Asm.assign, bitOf, hp]) (by decide) run
      exact ⟨_, mem', (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_true 1 (by tag_eval t1) (by decide) (Runs.block_cons r1 (Runs.block_cons inner (Runs.block_nil _ _ _ _ _)))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))), post⟩
  | container n fs =>
    have planRun := planPlain_calls fns.roots.plan _ p sp' mem pre.plan pre.sound (by
      simp only [rootStack] at room'; omega)
    have r1 := Runs.call (m := m) (sp := sp') (env := E1) (mem := mem) (dst := 7) (args := [RootOf.p])
      (by simp only [List.mapM_cons, List.mapM_nil, eval_var ev1.p]; rfl) planRun
    have ev2 := ev1.write (x := 7) (bitOf (plain (.container n fs))) (by decide)
    cases hp : plain (.container n fs)
    · obtain ⟨mem', run, post⟩ := pass_runs (sub hp) room' pre ev2
      have inner := Runs.ifElse_false (c := RootOf.pl) (yes := RootOf.single)
        (no := [ifElse (eq RootOf.tag 7) [RootOf.pass "ssz_root_vector"] [RootOf.pass "ssz_root_container"]])
        (by simp [eval, Asm.assign, bitOf, hp])
        (Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, Asm.assign, t1, Plan.tag]) (Runs.block_cons run (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))
      exact ⟨_, mem', (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_true 1 (by tag_eval t1) (by decide) (Runs.block_cons r1 (Runs.block_cons inner (Runs.block_nil _ _ _ _ _)))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))), post⟩
    · obtain ⟨E', mem', run, post⟩ := single_runs hash gmod fns hp room' pre ev2
      have inner := Runs.ifElse_true (c := RootOf.pl) (yes := RootOf.single)
        (no := [ifElse (eq RootOf.tag 7) [RootOf.pass "ssz_root_vector"] [RootOf.pass "ssz_root_container"]]) 1
        (by simp [eval, Asm.assign, bitOf, hp]) (by decide) run
      exact ⟨_, mem', (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_false (by tag_eval t1) (Runs.block_cons (Runs.ifElse_true 1 (by tag_eval t1) (by decide) (Runs.block_cons r1 (Runs.block_cons inner (Runs.block_nil _ _ _ _ _)))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))), post⟩

end Ssz.Native.Driver
