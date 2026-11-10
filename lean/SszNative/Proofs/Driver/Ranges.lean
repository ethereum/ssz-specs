import SszNative.Proofs.Driver.Fields

/-!
The ranges driver `ssz_ranges` answers what `viewRanges` answers.

It reads the type's tag from the plan and hands the composite to its own view.
A union is cut here: the selector byte, then the rest.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Plan

/-- The bounds the ranges driver needs beyond a narrow, well-formed type: the words it hands on fit. -/
def viewSmall : Desc → Prop
  | .vector _ length => length < 2 ^ 62
  | .list _ limit => limit < 2 ^ 64
  | .progressiveList _ limit => limitWord limit < 2 ^ 64
  | .container _ fields => Desc.leadingWidth fields < 2 ^ 62
  | .progressiveContainer _ _ fields => Desc.leadingWidth fields < 2 ^ 62
  | _ => True

/-- The stack the ranges driver needs below its own frame: the view it calls, with that view's own needs. -/
def viewRoom : Desc → Nat
  | .vector element _ => 8 + 8 * vectorView.frame + seqRoom element
  | .list element _ => 8 + 8 * listView.frame + seqRoom element
  | .progressiveList element _ => 8 + 8 * listView.frame + seqRoom element
  | .container _ fields => 8 + 8 * fieldsView.frame + fieldsRoom fields
  | .progressiveContainer _ _ fields => 8 + 8 * fieldsView.frame + fieldsRoom fields
  | _ => 0

/--
What the ranges driver answers, and the memory after.

Bounds out of order or past the buffer are refused.
A type with no parts gets code three; a composite gets its view's outcome.
-/
def rangesOutcome (out cap : Nat) (mem : Memory) (d : Desc) (b : ByteArray) (start stop : Nat) : UInt64 × Memory :=
  if start ≤ stop ∧ stop ≤ b.size then
    if 7 ≤ tag d then viewOutcome out cap mem (viewRanges d b start stop) else (3, mem)
  else (1, mem)

/-- The ranges driver after its bounds check, its tag read, and its code for a type with no parts. -/
def viewDispatch : Stmt :=
  match view.body with
  | .seq _ (.ite _ (.seq _ (.seq _ rest)) _) => rest
  | _ => .skip

/-- The ranges driver sets its refusal code, checks the bounds, reads the tag, then dispatches. -/
theorem view_body : view.body =
    .seq (.set 6 1) (.ite (.op .and (.cmp .be (.var 3) (.var 4)) (.cmp .be (.var 4) (.var 2)))
      (.seq (.set 7 (.load .b8 (.var 0))) (.seq (.set 6 3) viewDispatch)) .skip) := rfl

/-- A union's two ranges, written word by word with the count last, are its view. -/
theorem union_written (out start stop : Nat) (mem : Memory) :
    store (store (store (store (store mem (out + 8) 8 (qwordByte start.toUInt64)) (out + 16) 8
      (qwordByte (start + 1).toUInt64)) (out + 24) 8 (qwordByte (start + 1).toUInt64)) (out + 32) 8
      (qwordByte stop.toUInt64)) out 8 (qwordByte 2) =
      viewed out [(start, start + 1), (start + 1, stop)] mem := by
  let f := viewWord [(start, start + 1), (start + 1, stop)]
  have w1 := store_wordsAt out f (fun _ => false) mem 1
  have w2 := store_wordsAt out f (fun j => j == 1 || false) mem 2
  have w3 := store_wordsAt out f (fun j => j == 2 || (j == 1 || false)) mem 3
  have w4 := store_wordsAt out f (fun j => j == 3 || (j == 2 || (j == 1 || false))) mem 4
  have w0 := store_wordsAt_zero out f (fun j => j == 4 || (j == 3 || (j == 2 || (j == 1 || false)))) mem
  rw [wordsAt_none] at w1
  rw [← w1] at w2; rw [← w2] at w3; rw [← w3] at w4; rw [← w4] at w0
  have v0 : f 0 = 2 := rfl
  have v1 : f 1 = start.toUInt64 := rfl
  have v2 : f 2 = (start + 1).toUInt64 := rfl
  have v3 : f 3 = (start + 1).toUInt64 := rfl
  have v4 : f 4 = stop.toUInt64 := rfl
  simp only [v0, v1, v2, v3, v4, Nat.reduceMul] at w0
  rw [w0, viewed]
  congr 1
  funext k
  -- The five words written are the first five, the count and two ranges.
  match k with
  | 0 | 1 | 2 | 3 | 4 => rfl
  | k + 5 =>
    have big : ¬ (k + 5 < 1 + 2 * [(start, start + 1), (start + 1, stop)].length) := by simp
    simp only [big, decide_false]
    simp

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
/-- The ranges driver: the outcome of the composite's view, or the code for a type with no parts. -/
theorem ranges_ok (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory) (d : Desc)
    (data start stop out cap p : Nat) (b : ByteArray) (sound : d.wellFormed = .ok ()) (thin : narrow d = true)
    (small : viewSmall d) (plan : PlanAt w mem p (words d))
    (planApart : p + 8 * (words d).length ≤ out ∨ out + 8 * (1 + 2 * cap) ≤ p)
    (at_ : ViewMemory w mem data b out cap) (startSmall : start < 2 ^ 64) (stopSmall : stop < 2 ^ 64)
    (room : w.stackLo + 8 + 8 * view.frame + viewRoom d ≤ sp) :
    Calls m w "ssz_ranges" sp
      [p.toUInt64, data.toUInt64, b.size.toUInt64, start.toUInt64, stop.toUInt64, out.toUInt64] mem
      (rangesOutcome out cap mem d b start stop).1 (rangesOutcome out cap mem d b start stop).2 := by
  have found : m.fns.lookup "ssz_ranges" = some view := linked ("ssz_ranges", view) (by simp [codecFns])
  have dataBound : data + b.size ≤ 2 ^ 63 := by
    have := at_.readable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have outBound : out + 8 + 16 * cap ≤ 2 ^ 63 := by
    have := at_.writable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have planBound : p + 8 * (words d).length ≤ 2 ^ 63 := by have := plan.1; simpa [addressBound] using this
  have outReadable : w.access out 8 := by simpa using access_inside at_.writable 0 8 (by omega)
  let inner := sp - 8 - 8 * view.frame
  let args := [p.toUInt64, data.toUInt64, b.size.toUInt64, start.toUInt64, stop.toUInt64, out.toUInt64]
  have finish : ∀ env' mem' (r : UInt64), Runs m w inner (entryEnv args) mem view.body env' mem' → env' 6 = r →
      Calls m w "ssz_ranges" sp args mem r mem' := by
    intro env' mem' r main answer
    exact Calls.fn (env' := env') found (by omega) rfl main (by simp [view, View.r, eval, answer])
  let env₁ := assign (entryEnv args) 6 1
  have bounds : eval w env₁ mem (.op .and (.cmp .be (.var 3) (.var 4)) (.cmp .be (.var 4) (.var 2))) =
      some (if start ≤ stop ∧ stop ≤ b.size then 1 else 0) := by
    simp only [eval, env₁, assign, entryEnv, args]
    simp [holds_be, ofNat_le_iff start stop startSmall stopSmall, ofNat_le_iff stop b.size stopSmall (by omega),
      aluResult, Bind.bind, Option.bind]
    by_cases h1 : start ≤ stop <;> by_cases h2 : stop ≤ b.size <;> simp [h1, h2]
  by_cases inb : start ≤ stop ∧ stop ≤ b.size
  case neg =>
    rw [rangesOutcome, ite_eq_right inb]
    refine finish _ _ _ ?_ (show assign (entryEnv args) 6 1 6 = 1 by simp [assign])
    rw [view_body]
    exact Runs.seq (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_false (by rw [bounds]; simp [inb]) (Runs.skip _ _ _ _ _))
  rw [rangesOutcome, ite_eq_left inb]
  have t := plan.2 0 (words_length_pos _)
  have tagWord : (words d)[0]'(words_length_pos _) = tag d := by cases d <;> rfl
  have t0 : w.access p 8 = true ∧ readLE mem p 8 = (tag d).toUInt64 := by simpa [tagWord] using t
  let env₂ := assign (assign env₁ 7 (tag d).toUInt64) 6 3
  have dispatch : ∀ env' mem' (r : UInt64), Runs m w inner env₂ mem viewDispatch env' mem' → env' 6 = r →
      Calls m w "ssz_ranges" sp args mem r mem' := by
    intro env' mem' r ran answer
    refine finish _ _ _ ?_ answer
    rw [view_body]
    refine Runs.seq (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_true 1 (by rw [bounds]; simp [inb]) (by decide)
      (Runs.seq (Runs.set _ _ _ _ _ 7 _ _ ?_) (Runs.seq (Runs.set _ _ _ _ _ 6 _ _ rfl) ran)))
    simp [eval, env₁, assign, entryEnv, args, Width.bytes, toNat_toUInt64 p (by omega), t0.1, t0.2]
  have e0 : env₂ 0 = p.toUInt64 := by simp [env₂, env₁, assign, entryEnv, args]
  have e1 : env₂ 1 = data.toUInt64 := by simp [env₂, env₁, assign, entryEnv, args]
  have e3 : env₂ 3 = start.toUInt64 := by simp [env₂, env₁, assign, entryEnv, args]
  have e4 : env₂ 4 = stop.toUInt64 := by simp [env₂, env₁, assign, entryEnv, args]
  have e5 : env₂ 5 = out.toUInt64 := by simp [env₂, env₁, assign, entryEnv, args]
  have e7 : env₂ 7 = (tag d).toUInt64 := by simp [env₂, env₁, assign]
  have e6 : env₂ 6 = 3 := by simp [env₂, assign]
  cases d with
  | vector element length =>
    rw [ite_eq_left (by simp [tag])]
    simp only [narrow, Bool.and_eq_true] at thin
    have t1 := plan.2 1 (by simp [words])
    have elementPlan : PlanAt w mem (p + 16) (words element) := by
      simpa using (show PlanAt w mem p ([7, length] ++ words element) from plan).right
    simp only [viewRoom, seqRoom] at room
    have callee := vector_ok m w linked inner mem element length data start stop out cap (p + 16) b
      (wellFormed_vector sound) (by simp [narrow, thin.1, thin.2]) elementPlan at_ inb.1 inb.2 small
      (by simp only [inner, seqRoom]; omega)
    have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by simp [words] at planBound; omega))]; simp
      simp [words] at planBound; omega
    simp [words] at t1
    refine dispatch (assign env₂ 6 (viewOutcome out cap mem (viewRanges (.vector element length) b start stop)).1)
      _ _ ?_ (by simp [assign])
    unfold viewDispatch view
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, View.tag, View.plan, View.k,
      View.r, View.out, View.start, View.stop, View.data, View.len]
    branches [e7, tag]
    exact Runs.call (values := [(p + 16).toUInt64, data.toUInt64, start.toUInt64, stop.toUInt64, length.toUInt64,
      out.toUInt64]) (by evaluate [e0, e1, e3, e4, e5, a8, t1.1, t1.2]) callee
  | list element limit =>
    rw [ite_eq_left (by simp [tag])]
    simp only [narrow] at thin
    have t1 := plan.2 1 (by simp [words])
    have elementPlan : PlanAt w mem (p + 16) (words element) := by
      simpa using (show PlanAt w mem p ([8, limit] ++ words element) from plan).right
    simp only [viewRoom, seqRoom] at room
    have callee := list_ok m w linked inner mem element (some limit) data start stop out cap (p + 16) b
      (wellFormed_list sound) thin elementPlan at_ inb.1 inb.2 small (by simp only [inner, seqRoom]; omega)
    have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by simp [words] at planBound; omega))]; simp
      simp [words] at planBound; omega
    simp [words] at t1
    refine dispatch (assign env₂ 6 (viewOutcome out cap mem (viewRanges (.list element limit) b start stop)).1)
      _ _ ?_ (by simp [assign])
    unfold viewDispatch view
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, View.tag, View.plan, View.k,
      View.r, View.out, View.start, View.stop, View.data, View.len]
    branches [e7, tag]
    exact Runs.call (values := [(p + 16).toUInt64, data.toUInt64, start.toUInt64, stop.toUInt64,
      (limitWord (some limit)).toUInt64, out.toUInt64]) (by evaluate [e0, e1, e3, e4, e5, a8, t1.1, t1.2, limitWord])
      callee
  | progressiveList element limit =>
    rw [ite_eq_left (by simp [tag])]
    simp only [narrow] at thin
    have t1 := plan.2 1 (by simp [words, bound_length]; omega)
    have t2 := plan.2 2 (by simp [words, bound_length]; omega)
    have elementPlan : PlanAt w mem (p + 24) (words element) := by
      simpa [bound_length] using (show PlanAt w mem p ((9 :: bound limit) ++ words element) from plan).right
    simp only [viewRoom, seqRoom] at room
    have callee := list_ok m w linked inner mem element limit data start stop out cap (p + 24) b
      (wellFormed_progressiveList sound) thin elementPlan at_ inb.1 inb.2 small (by simp only [inner, seqRoom]; omega)
    have pSmall : p + 24 ≤ 2 ^ 63 := by simp [words, bound_length] at planBound; omega
    have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; simp; omega
    have a16 : (UInt64.ofNat p + 16).toNat = p + 16 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; simp; omega
    refine dispatch (assign (assign env₂ 8 (limitWord limit).toUInt64) 6
      (viewOutcome out cap mem (viewRanges (.progressiveList element limit) b start stop)).1)
      _ _ ?_ (by simp [assign])
    unfold viewDispatch view
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, View.tag, View.plan, View.k,
      View.r, View.out, View.start, View.stop, View.data, View.len]
    branches [e7, tag]
    refine Runs.seq ?_ (Runs.call (values := [(p + 24).toUInt64, data.toUInt64, start.toUInt64, stop.toUInt64,
      (limitWord limit).toUInt64, out.toUInt64]) (by evaluate [e0, e1, e3, e4, e5]) callee)
    cases limit with
    | none =>
      simp [words, bound] at t1
      exact Runs.ite_true 1 (by evaluate [e0, a8, t1.1, t1.2]) (by decide)
        (Runs.set _ _ _ _ _ 8 _ _ (by evaluate [limitWord]))
    | some bound_ =>
      simp [words, bound] at t1 t2
      exact Runs.ite_false (by evaluate [e0, a8, t1.1, t1.2])
        (Runs.set _ _ _ _ _ 8 _ _ (by evaluate [e0, a16, t2.1, t2.2, limitWord]))
  | container names fields =>
    rw [ite_eq_left (by simp [tag])]
    simp only [narrow, Bool.and_eq_true] at thin
    have t1 := plan.2 1 (by simp [words])
    have fieldsPlan : PlanAt w mem (p + 16) (wordsAll fields) := by
      simpa using (show PlanAt w mem p ([10, fields.length] ++ wordsAll fields) from plan).right
    simp only [viewRoom] at room
    have callee := fields_ok m w linked inner mem fields data start stop out cap (p + 16) b
      (allWellFormed_mem _ (wellFormed_container sound)) (narrow_mem _ thin.2)
      (fun width fixed => by simpa [Desc.fixedSize, fixed] using thin.1) small fieldsPlan
      (by simp [words] at planApart; omega) at_ inb.1 inb.2 (by simp only [inner]; omega)
    have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by simp [words] at planBound; omega))]; simp
      simp [words] at planBound; omega
    simp [words] at t1
    refine dispatch (assign env₂ 6 (viewOutcome out cap mem (viewRanges (.container names fields) b start stop)).1)
      _ _ ?_ (by simp [assign])
    unfold viewDispatch view
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, View.tag, View.plan, View.k,
      View.r, View.out, View.start, View.stop, View.data, View.len]
    branches [e7, tag]
    exact Runs.call (values := [(p + 16).toUInt64, data.toUInt64, start.toUInt64, stop.toUInt64,
      fields.length.toUInt64, out.toUInt64]) (by evaluate [e0, e1, e3, e4, e5, a8, t1.1, t1.2]) callee
  | progressiveContainer active names fields =>
    rw [ite_eq_left (by simp [tag])]
    simp only [narrow, Bool.and_eq_true] at thin
    let a := active.length
    let pre : List Nat := [11, a] ++ active.map (fun b => if b then 1 else 0) ++ [fields.length]
    have split : words (.progressiveContainer active names fields) = pre ++ wordsAll fields := rfl
    have preLen : pre.length = 3 + a := by simp [pre, a]; omega
    rw [split] at plan planApart planBound
    simp only [List.length_append, preLen] at planApart planBound
    have t1 := plan.2 1 (by simp only [List.length_append, preLen]; omega)
    have tn := plan.2 (2 + a) (by simp only [List.length_append, preLen]; omega)
    have g1 : (pre ++ wordsAll fields)[1]'(by simp only [List.length_append, preLen]; omega) = a := by
      rw [List.getElem_append_left (by omega)]; simp [pre]
    have gn : (pre ++ wordsAll fields)[2 + a]'(by simp only [List.length_append, preLen]; omega) = fields.length := by
      rw [List.getElem_append_left (by omega)]
      simp only [pre]
      rw [List.getElem_append_right (by simp [a]; omega)]
      simp [a]
    rw [g1] at t1
    rw [gn] at tn
    have fieldsPlan : PlanAt w mem (p + 8 * (3 + a)) (wordsAll fields) := by
      have := plan.right; rwa [preLen] at this
    simp only [viewRoom] at room
    have callee := fields_ok m w linked inner mem fields data start stop out cap (p + 8 * (3 + a)) b
      (allWellFormed_mem _ (wellFormed_progressiveContainer sound)) (narrow_mem _ thin.2)
      (fun width fixed => by simpa [Desc.fixedSize, fixed] using thin.1) small fieldsPlan
      (by omega) at_ inb.1 inb.2 (by simp only [inner]; omega)
    have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; simp; omega
    have q24 : UInt64.ofNat p + 24 + 8 * UInt64.ofNat a = UInt64.ofNat (p + 8 * (3 + a)) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
        UInt64.toNat_ofNat_of_lt' (lt_size (by omega)), UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
      simp; omega
    have q16 : (UInt64.ofNat p + 16 + 8 * UInt64.ofNat a).toNat = p + 8 * (2 + a) := by
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
        UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
      simp; omega
    simp only [Nat.mul_one] at t1
    refine dispatch (assign (assign env₂ 8 a.toUInt64) 6
      (viewOutcome out cap mem (viewRanges (.progressiveContainer active names fields) b start stop)).1)
      _ _ ?_ (by simp [assign])
    unfold viewDispatch view
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, View.tag, View.plan, View.k,
      View.r, View.out, View.start, View.stop, View.data, View.len]
    branches [e7, tag]
    exact Runs.seq (Runs.set _ _ _ _ _ 8 _ _ (by evaluate [e0, a8, t1.1, t1.2]))
      (Runs.call (values := [(p + 8 * (3 + a)).toUInt64, data.toUInt64, start.toUInt64, stop.toUInt64,
        fields.length.toUInt64, out.toUInt64]) (by evaluate [e0, e1, e3, e4, e5, q24, q16, tn.1, tn.2]) callee)
  | compatibleUnion selectors options =>
    rw [ite_eq_left (by simp [tag])]
    have less : eval w (assign env₂ 6 1) mem (Expr.lt (.var 3) (.var 4)) =
        some (if start < stop then 1 else 0) := by
      simp [Expr.lt, eval, assign, e3, e4, Cond.holds, ofNat_lt_ofNat start stop startSmall stopSmall]
    by_cases empty : stop - start < 1
    · -- No selector byte: refused.
      have none_ : ¬ start < stop := by omega
      simp only [viewRanges, empty, ite_true, viewOutcome]
      refine dispatch (assign env₂ 6 1) mem 1 ?_ (by simp [assign])
      unfold viewDispatch view
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, View.tag, View.plan, View.k,
        View.r, View.out, View.start, View.stop, View.data, View.len]
      branches [e7, tag]
      exact Runs.seq (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_false (by rw [less]; simp [none_]) (Runs.skip _ _ _ _ _))
    have some_ : start < stop := by omega
    simp only [viewRanges, empty, ite_false, viewOutcome, List.length]
    let env₃ := assign (assign env₂ 6 1) 6 2
    have capWord : eval w (assign (assign env₂ 6 1) 6 2) mem (Expr.le 2 (Expr.ld (.var 5))) =
        some (if 2 ≤ cap then 1 else 0) := by
      have le : (2 : UInt64) ≤ UInt64.ofNat cap ↔ 2 ≤ cap := ofNat_le_iff 2 cap (by decide) at_.smallCap
      simp [Expr.le, Expr.ld, eval, assign, e5, Width.bytes, toNat_toUInt64 out (by omega), outReadable,
        at_.capacity, holds_be, le]
    by_cases fits : 0 + 1 + 1 ≤ cap
    · -- The selector byte and the rest are written, then the count.
      simp only [fits, ite_true]
      rw [← union_written out start stop mem]
      have put : ∀ env cur (a v : Expr) (addr : Nat) (y : UInt64), eval w env cur a = some addr.toUInt64 →
          addr < 2 ^ 64 → eval w env cur v = some y → w.access addr 8 →
          Runs m w inner env cur (.store .b8 a v) env (store cur addr 8 (qwordByte y)) := by
        intro env cur a v addr y ha small hv acc
        have := Runs.store m w inner env cur .b8 a v addr.toUInt64 y ha hv (by rw [toNat_toUInt64 _ small]; exact acc)
        rwa [toNat_toUInt64 _ small, Width.bytes] at this
      have acc : ∀ k, k ≤ 4 → w.access (out + 8 * k) 8 := fun k hk => access_inside at_.writable _ 8 (by omega)
      have plus : ∀ x c : Nat, x + c < 2 ^ 64 → UInt64.ofNat x + UInt64.ofNat c = UInt64.ofNat (x + c) := by
        intro x c _; simp
      refine dispatch (assign env₃ 6 0) _ 0 ?_ (by simp [assign])
      unfold viewDispatch view
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, View.tag, View.plan, View.k,
        View.r, View.out, View.start, View.stop, View.data, View.len]
      branches [e7, tag]
      refine Runs.seq (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_true 1 (by rw [less]; simp [some_]) (by decide)
        (Runs.seq (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_true 1 (by rw [capWord]; simp [show 2 ≤ cap by omega])
          (by decide) ?_)))
      refine Runs.seq (put _ _ _ _ (out + 8) start.toUInt64 (by simp [eval, env₃, assign, e5, aluResult]) (by omega)
        (by simp [eval, env₃, assign, e3, aluResult]) (by simpa using acc 1 (by omega))) ?_
      refine Runs.seq (put _ _ _ _ (out + 16) (start + 1).toUInt64 (by simp [eval, env₃, assign, e5, aluResult]) (by omega)
        (by simp [eval, env₃, assign, e3, aluResult]) (by simpa using acc 2 (by omega))) ?_
      refine Runs.seq (put _ _ _ _ (out + 24) (start + 1).toUInt64 (by simp [eval, env₃, assign, e5, aluResult]) (by omega)
        (by simp [eval, env₃, assign, e3, aluResult]) (by simpa using acc 3 (by omega))) ?_
      refine Runs.seq (put _ _ _ _ (out + 32) stop.toUInt64 (by simp [eval, env₃, assign, e5, aluResult]) (by omega)
        (by simp [eval, env₃, assign, e4, aluResult]) (by simpa using acc 4 (by omega))) ?_
      exact Runs.seq (put _ _ _ _ out 2 (by simp [eval, env₃, assign, e5, aluResult]) (by omega)
        (by simp [eval]) outReadable) (Runs.set _ _ _ _ _ 6 _ _ rfl)
    · -- No room for two ranges.
      simp only [fits, ite_false]
      refine dispatch env₃ mem 2 ?_ (by simp [env₃, assign])
      unfold viewDispatch view
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, View.tag, View.plan, View.k,
        View.r, View.out, View.start, View.stop, View.data, View.len]
      branches [e7, tag]
      exact Runs.seq (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_true 1 (by rw [less]; simp [some_]) (by decide)
        (Runs.seq (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_false (by rw [capWord]; simp; omega)
          (Runs.skip _ _ _ _ _))))
  | _ =>
    rw [ite_eq_right (by simp [tag])]
    refine dispatch env₂ mem 3 ?_ e6
    unfold viewDispatch view
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, View.tag, View.plan, View.k,
      View.r, View.out, View.start, View.stop, View.data, View.len]
    branches [e7, tag]
    exact Runs.skip _ _ _ _ _

end EthLib.Consensus.Ssz.Native.Driver
