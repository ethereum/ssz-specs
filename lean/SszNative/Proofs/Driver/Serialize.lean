import SszNative.Proofs.Driver.LayRun

/-!
The assembly driver `ssz_assemble` answers what `assemble` answers, and what `assembleBits` answers for a bit list.

It reads the type's tag from the plan and hands the parts to the driver for that kind of type.
A type with no parts to lay out gets the code for a type assembly does not cover.
-/

namespace Ssz.Native.Driver

open Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Plan

/-- A bit list type's optional limit, or none for any other type. -/
def bitsLimit : Desc → Option (Option Nat)
  | .bitList limit => some (some limit)
  | .progressiveBitList limit => some limit
  | _ => none

/-- The bounds the assembly driver needs beyond a narrow, well-formed type: the words it compares fit. -/
def assembleSmall : Desc → Prop
  | .byteList limit => limit < 2 ^ 64
  | .bitList limit => limit < 2 ^ 64
  | .progressiveBitList limit => limitWord limit < 2 ^ 64
  | .vector _ length => length < 2 ^ 64
  | .list _ limit => limit < 2 ^ 64
  | .progressiveList _ limit => limitWord limit < 2 ^ 64
  | _ => True

/-- The stack the assembly driver needs below its own frame: the driver it calls, with that driver's own needs. -/
def assembleRoom : Desc → Nat
  | .byteVector _ | .byteList _ => 8 + 8 * joinBytes.frame + (8 + 8 * copyBytes.frame)
  | .bitList _ | .progressiveBitList _ => 8 + 8 * bitsParts.frame + (8 + 8 * copyBytes.frame)
  | .vector element _ | .list element _ | .progressiveList element _ => 8 + 8 * layParts.frame + layRoom element.nesting
  | .container _ fields | .progressiveContainer _ _ fields =>
    8 + 8 * layParts.frame + layRoom (Desc.deepestNesting fields)
  | .compatibleUnion _ options => 8 + 8 * unionParts.frame + unionRoom options
  | _ => 0

/-- The assembly driver after its tag read and its code for a type it does not cover. -/
def assembleDispatch : Stmt :=
  match assembleParts.body with
  | .seq _ (.seq _ rest) => rest
  | _ => .skip

/-- The assembly driver reads the tag, sets its refusal code, then dispatches. -/
theorem assembleParts_body : assembleParts.body =
    .seq (.set 6 (.load .b8 (.var 0))) (.seq (.set 5 (.lit (codeType : Nat).toUInt64)) assembleDispatch) := rfl

/-- A plan address a few words past a node's start, as a word, when the node fits below the address bound. -/
theorem plan_addr (p c : Nat) (small : p + c < 2 ^ 64) : (UInt64.ofNat p + UInt64.ofNat c).toNat = p + c := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)), UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
  simp; omega

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
/--
The assembly driver, for any type but a bit list: the outcome of the driver for that kind of type.

A type with no parts to lay out gets the code for a type assembly does not cover, as `assemble` refuses it.
-/
theorem assemble_ok (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory) (d : Desc)
    (p parts out cap : Nat) (ps : List ByteArray) (ptrs : List Nat) (sound : d.wellFormed = .ok ())
    (thin : narrow d = true) (small : assembleSmall d) (notBits : bitsLimit d = none)
    (plan : PlanAt w mem p (words d)) (planApart : p + 8 * (words d).length ≤ out ∨ out + cap ≤ p)
    (at_ : PartsAt w mem parts ps ptrs) (to : OutAt w parts ps ptrs out cap)
    (room : w.stackLo + 8 + 8 * assembleParts.frame + assembleRoom d ≤ sp) :
    Calls m w "ssz_assemble" sp [p.toUInt64, parts.toUInt64, ps.length.toUInt64, out.toUInt64, cap.toUInt64] mem
      (assembleOutcome out cap mem (assemble d ps)).1 (assembleOutcome out cap mem (assemble d ps)).2 := by
  have found : m.fns.lookup "ssz_assemble" = some assembleParts :=
    linked ("ssz_assemble", assembleParts) (by simp [codecFns])
  have tableBound : parts + 16 * ps.length ≤ 2 ^ 63 := by
    have := at_.table
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have planBound : p + 8 * (words d).length ≤ 2 ^ 63 := by have := plan.1; simpa [addressBound] using this
  have lenSmall : ps.length < 2 ^ 64 := by omega
  let inner := sp - 8 - 8 * assembleParts.frame
  let args := [p.toUInt64, parts.toUInt64, ps.length.toUInt64, out.toUInt64, cap.toUInt64]
  have finish : ∀ env' mem' (r : UInt64), Runs m w inner (entryEnv args) mem assembleParts.body env' mem' →
      env' 5 = r → Calls m w "ssz_assemble" sp args mem r mem' := by
    intro env' mem' r main answer
    exact Calls.fn (env' := env') found (by omega) rfl main (by simp [assembleParts, Assemble.r, eval, answer])
  have t := plan.2 0 (words_length_pos _)
  have tagWord : (words d)[0]'(words_length_pos _) = tag d := by cases d <;> rfl
  have t0 : w.access p 8 = true ∧ readLE mem p 8 = (tag d).toUInt64 := by simpa [tagWord] using t
  let env₂ := assign (assign (entryEnv args) 6 (tag d).toUInt64) 5 (codeType : Nat).toUInt64
  have dispatch : ∀ env' mem' (r : UInt64), Runs m w inner env₂ mem assembleDispatch env' mem' → env' 5 = r →
      Calls m w "ssz_assemble" sp args mem r mem' := by
    intro env' mem' r ran answer
    refine finish _ _ _ ?_ answer
    rw [assembleParts_body]
    refine Runs.seq (Runs.set _ _ _ _ _ 6 _ _ ?_) (Runs.seq (Runs.set _ _ _ _ _ 5 _ _ rfl) ran)
    simp [eval, entryEnv, args, Width.bytes, toNat_toUInt64 p (by omega), t0.1, t0.2]
  have e0 : env₂ 0 = p.toUInt64 := by simp [env₂, assign, entryEnv, args]
  have e1 : env₂ 1 = parts.toUInt64 := by simp [env₂, assign, entryEnv, args]
  have e2 : env₂ 2 = ps.length.toUInt64 := by simp [env₂, assign, entryEnv, args]
  have e3 : env₂ 3 = out.toUInt64 := by simp [env₂, assign, entryEnv, args]
  have e4 : env₂ 4 = cap.toUInt64 := by simp [env₂, assign, entryEnv, args]
  have e6 : env₂ 6 = (tag d).toUInt64 := by simp [env₂, assign]
  have e5 : env₂ 5 = (codeType : Nat).toUInt64 := by simp [env₂, assign]
  -- The word one past the tag, for the types that have one.
  have pmod : p % 18446744073709551616 = p := Nat.mod_eq_of_lt (by omega)
  have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := plan_addr p 8 (by omega)
  have word1 : ∀ v : Nat, 2 ≤ (words d).length → (words d)[1]? = some v →
      w.access (p + 8) 8 = true ∧ readLE mem (p + 8) 8 = v.toUInt64 := by
    intro v two hv
    have t1 := plan.2 1 (by omega)
    rw [List.getElem?_eq_getElem (by omega)] at hv
    simp only [Option.some.injEq] at hv
    rw [hv] at t1
    simpa using t1
  cases d with
  | byteVector n =>
    have smallN : n < 2 ^ 64 := by
      have := narrow_width _ thin n (by simp [Desc.fixedSize]); omega
    simp only [assembleRoom] at room
    have callee := join_ok m w linked inner mem parts out cap n true ps ptrs at_ to smallN (by simp only [inner]; omega)
    refine dispatch (assign env₂ 5 (assembleOutcome out cap mem (assemble (.byteVector n) ps)).1) _ _ ?_
      (by simp [assign])
    have w1 := word1 n (by simp [words]) (by simp [words])
    unfold assembleDispatch assembleParts
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
      Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
    branches [e6, tag]
    exact Runs.call (values := [parts.toUInt64, ps.length.toUInt64, n.toUInt64, 1, out.toUInt64, cap.toUInt64])
      (by evaluate [e0, e1, e2, e3, e4, a8, w1.1, w1.2]) callee
  | byteList n =>
    simp only [assembleSmall] at small
    simp only [assembleRoom] at room
    have callee := join_ok m w linked inner mem parts out cap n false ps ptrs at_ to small (by simp only [inner]; omega)
    refine dispatch (assign env₂ 5 (assembleOutcome out cap mem (assemble (.byteList n) ps)).1) _ _ ?_
      (by simp [assign])
    have w1 := word1 n (by simp [words]) (by simp [words])
    unfold assembleDispatch assembleParts
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
      Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
    branches [e6, tag]
    exact Runs.call (values := [parts.toUInt64, ps.length.toUInt64, n.toUInt64, 0, out.toUInt64, cap.toUInt64])
      (by evaluate [e0, e1, e2, e3, e4, a8, w1.1, w1.2]) callee
  | bitList _ => simp [bitsLimit] at notBits
  | progressiveBitList _ => simp [bitsLimit] at notBits
  | compatibleUnion selectors options =>
    simp only [assembleRoom] at room
    have callee := union_ok m w linked inner mem selectors options p parts out cap ps ptrs sound thin plan at_ to
      (by simp only [inner]; omega)
    refine dispatch (assign env₂ 5 (assembleOutcome out cap mem (assemble (.compatibleUnion selectors options)
      ps)).1) _ _ ?_ (by simp [assign])
    unfold assembleDispatch assembleParts
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
      Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
    branches [e6, tag]
    exact Runs.call (values := [p.toUInt64, parts.toUInt64, ps.length.toUInt64, out.toUInt64, cap.toUInt64])
      (by evaluate [e0, e1, e2, e3, e4]) callee
  | vector element length =>
    simp only [narrow, Bool.and_eq_true] at thin
    simp only [assembleSmall] at small
    simp only [assembleRoom] at room
    have w1 := word1 length (by simp [words]) (by simp [words])
    have elementPlan : PlanAt w mem (p + 16) (words element) := by
      simpa using (show PlanAt w mem p ([7, length] ++ words element) from plan).right
    have eqIff : UInt64.ofNat ps.length = UInt64.ofNat length ↔ ps.length = length :=
      ofNat_eq_ofNat _ _ lenSmall small
    by_cases same : ps.length = length
    · -- The count the type allows: the parts are laid out as a sequence.
      have callee := lay_seq m w linked inner mem element (p + 16) parts out cap ps ptrs (wellFormed_vector sound)
        thin.2 elementPlan (by simp [words] at planApart; omega) at_ to (by simp only [inner]; omega)
      have ref : assemble (.vector element length) ps = layOut (List.replicate ps.length element) ps := by
        simp [assemble, same]
      rw [ref]
      refine dispatch (assign env₂ 5 (assembleOutcome out cap mem (layOut (List.replicate ps.length element)
        ps)).1) _ _ ?_ (by simp [assign])
      unfold assembleDispatch assembleParts
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
        Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
      branches [e6, tag, e0, e2, a8, w1.1, w1.2, same]
      exact Runs.call (values := [(p + 16).toUInt64, 1, parts.toUInt64, ps.length.toUInt64, out.toUInt64,
        cap.toUInt64]) (by evaluate [e0, e1, e2, e3, e4]) callee
    · -- Any other count is refused.
      have ref : assemble (.vector element length) ps = .error (.scope length ps.length) := by
        simp [assemble, same]
      rw [ref]
      refine dispatch (assign env₂ 5 (codeCount : Nat).toUInt64) mem _ ?_
        (by simp [assign, assembleOutcome, errCode])
      unfold assembleDispatch assembleParts
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
        Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
      branches [e6, tag, e0, e2, a8, w1.1, w1.2, eqIff, same]
      exact Runs.set _ _ _ _ _ 5 _ _ rfl
  | list element limit =>
    simp only [narrow] at thin
    simp only [assembleSmall] at small
    simp only [assembleRoom] at room
    have w1 := word1 limit (by simp [words]) (by simp [words])
    have elementPlan : PlanAt w mem (p + 16) (words element) := by
      simpa using (show PlanAt w mem p ([8, limit] ++ words element) from plan).right
    have ltIff : UInt64.ofNat limit < UInt64.ofNat ps.length ↔ limit < ps.length :=
      ofNat_lt_ofNat _ _ small lenSmall
    by_cases over : limit < ps.length
    · -- More parts than the limit is refused.
      have ref : assemble (.list element limit) ps = .error (.overLimit limit ps.length) := by
        simp [assemble, over]
      rw [ref]
      refine dispatch (assign env₂ 5 (codeCount : Nat).toUInt64) mem _ ?_
        (by simp [assign, assembleOutcome, errCode])
      unfold assembleDispatch assembleParts
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
        Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
      branches [e6, tag, e0, e2, a8, w1.1, w1.2, ltIff, over]
      exact Runs.set _ _ _ _ _ 5 _ _ rfl
    · -- The parts are laid out as a sequence.
      have callee := lay_seq m w linked inner mem element (p + 16) parts out cap ps ptrs (wellFormed_list sound)
        thin elementPlan (by simp [words] at planApart; omega) at_ to (by simp only [inner]; omega)
      have ref : assemble (.list element limit) ps = layOut (List.replicate ps.length element) ps := by
        simp [assemble]; omega
      rw [ref]
      refine dispatch (assign env₂ 5 (assembleOutcome out cap mem (layOut (List.replicate ps.length element)
        ps)).1) _ _ ?_ (by simp [assign])
      unfold assembleDispatch assembleParts
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
        Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
      branches [e6, tag, e0, e2, a8, w1.1, w1.2, ltIff, over]
      exact Runs.call (values := [(p + 16).toUInt64, 1, parts.toUInt64, ps.length.toUInt64, out.toUInt64,
        cap.toUInt64]) (by evaluate [e0, e1, e2, e3, e4]) callee
  | progressiveList element limit =>
    simp only [narrow] at thin
    simp only [assembleSmall] at small
    simp only [assembleRoom] at room
    have elementPlan : PlanAt w mem (p + 24) (words element) := by
      simpa [bound_length] using (show PlanAt w mem p ((9 :: bound limit) ++ words element) from plan).right
    have t2 := plan.2 2 (by simp [words, bound_length]; omega)
    have pSmall : p + 24 ≤ 2 ^ 63 := by simp [words, bound_length] at planBound; omega
    have a16 : (UInt64.ofNat p + 16).toNat = p + 16 := plan_addr p 16 (by omega)
    -- The bound read from its two words.
    let env₃ := assign env₂ 7 (limitWord limit).toUInt64
    have bounded : Runs m w inner env₂ mem
        (.ite (Expr.eq (Expr.ld (Expr.var 0 + ((8 * 1 : Nat) : Expr))) 0) (.set 7 (.lit (none64 : Nat).toUInt64))
          (.set 7 (Expr.ld (Expr.var 0 + ((8 * 2 : Nat) : Expr))))) env₃ mem := by
      cases limit with
      | none =>
        have w1 := word1 0 (by simp [words, bound]) (by simp [words, bound])
        exact Runs.ite_true 1 (by evaluate [e0, a8, w1.1, w1.2]) (by decide)
          (Runs.set _ _ _ _ _ 7 _ _ (by evaluate [limitWord]))
      | some b =>
        have w1 := word1 1 (by simp [words, bound]) (by simp [words, bound])
        simp [words, bound] at t2
        exact Runs.ite_false (by evaluate [e0, a8, w1.1, w1.2])
          (Runs.set _ _ _ _ _ 7 _ _ (by evaluate [e0, a16, t2.1, t2.2, limitWord]))
    have ltIff : UInt64.ofNat (limitWord limit) < UInt64.ofNat ps.length ↔ limitWord limit < ps.length :=
      ofNat_lt_ofNat _ _ small lenSmall
    have f7 : env₃ 7 = (limitWord limit).toUInt64 := by simp [env₃, assign]
    have f2 : env₃ 2 = ps.length.toUInt64 := by simp [env₃, assign, e2]
    -- The reference refuses past the limit, and the word for no limit is past any count.
    have refEq : assemble (.progressiveList element limit) ps =
        if limitWord limit < ps.length then .error (.overLimit (limitWord limit) ps.length)
        else layOut (List.replicate ps.length element) ps := by
      cases limit with
      | none =>
        have : ¬ (limitWord none < ps.length) := by simp [limitWord]; omega
        simp [assemble, boundCheck, this, Bind.bind, Except.bind]
      | some b =>
        by_cases over : b < ps.length
        · simp [assemble, boundCheck, limitWord, over, Bind.bind, Except.bind, show ¬ ps.length ≤ b by omega]
        · simp [assemble, boundCheck, limitWord, over, Bind.bind, Except.bind, show ps.length ≤ b by omega]
    rw [refEq]
    by_cases over : limitWord limit < ps.length
    · rw [if_pos over]
      refine dispatch (assign env₃ 5 (codeCount : Nat).toUInt64) mem _ ?_
        (by simp [assign, assembleOutcome, errCode])
      unfold assembleDispatch assembleParts
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
        Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
      branches [e6, tag]
      refine Runs.seq bounded (Runs.ite_true 1 (by evaluate [f7, f2, ltIff, over]) (by decide)
        (Runs.set _ _ _ _ _ 5 _ _ rfl))
    · rw [if_neg over]
      have callee := lay_seq m w linked inner mem element (p + 24) parts out cap ps ptrs
        (wellFormed_progressiveList sound) thin elementPlan
        (by simp [words, bound_length] at planApart; omega) at_ to (by simp only [inner]; omega)
      refine dispatch (assign env₃ 5 (assembleOutcome out cap mem (layOut (List.replicate ps.length element)
        ps)).1) _ _ ?_ (by simp [assign])
      unfold assembleDispatch assembleParts
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
        Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
      branches [e6, tag]
      refine Runs.seq bounded (Runs.ite_false (by evaluate [f7, f2, ltIff, over])
        (Runs.call (values := [(p + 24).toUInt64, 1, parts.toUInt64, ps.length.toUInt64, out.toUInt64,
          cap.toUInt64]) (by evaluate [env₃, e0, e1, e2, e3, e4]) callee))
  | container names fields =>
    simp only [narrow, Bool.and_eq_true] at thin
    simp only [assembleRoom] at room
    have w1 := word1 fields.length (by simp [words]) (by simp [words])
    have fieldsPlan : PlanAt w mem (p + 16) (wordsAll fields) := by
      simpa using (show PlanAt w mem p ([10, fields.length] ++ wordsAll fields) from plan).right
    have fieldsSmall : fields.length < 2 ^ 64 := by
      have := wordsAll_length_ge fields
      simp [words] at planBound; omega
    have eqIff : UInt64.ofNat ps.length = UInt64.ofNat fields.length ↔ ps.length = fields.length :=
      ofNat_eq_ofNat _ _ lenSmall fieldsSmall
    by_cases same : ps.length = fields.length
    · -- One part per field: the parts are laid out as a struct.
      have callee := lay_fields m w linked inner mem fields (p + 16) parts out cap ps ptrs
        (allWellFormed_mem _ (wellFormed_container sound)) (narrow_mem _ thin.2) fieldsPlan
        (by simp [words] at planApart; omega) same.symm at_ to (by simp only [inner]; omega)
      have ref : assemble (.container names fields) ps = layOut fields ps := by simp [assemble, same]
      rw [ref]
      refine dispatch (assign env₂ 5 (assembleOutcome out cap mem (layOut fields ps)).1) _ _ ?_ (by simp [assign])
      unfold assembleDispatch assembleParts
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
        Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
      branches [e6, tag, e0, e2, a8, w1.1, w1.2, same]
      exact Runs.call (values := [(p + 16).toUInt64, 0, parts.toUInt64, ps.length.toUInt64, out.toUInt64,
        cap.toUInt64]) (by evaluate [e0, e1, e2, e3, e4]) callee
    · -- Any other count is refused.
      have ref : assemble (.container names fields) ps = .error (.scope fields.length ps.length) := by
        simp [assemble, same]
      rw [ref]
      refine dispatch (assign env₂ 5 (codeCount : Nat).toUInt64) mem _ ?_
        (by simp [assign, assembleOutcome, errCode])
      unfold assembleDispatch assembleParts
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
        Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
      branches [e6, tag, e0, e2, a8, w1.1, w1.2, eqIff, same]
      exact Runs.set _ _ _ _ _ 5 _ _ rfl
  | progressiveContainer active names fields =>
    simp only [narrow, Bool.and_eq_true] at thin
    simp only [assembleRoom] at room
    let a := active.length
    let pre : List Nat := [11, a] ++ active.map (fun b => if b then 1 else 0) ++ [fields.length]
    have split : words (.progressiveContainer active names fields) = pre ++ wordsAll fields := rfl
    have preLen : pre.length = 3 + a := by simp [pre, a]; omega
    have w1 := word1 a (by rw [split]; simp only [List.length_append, preLen]; omega)
      (by rw [split, List.getElem?_append_left (by omega)]; simp [pre])
    rw [split] at plan planApart planBound
    simp only [List.length_append, preLen] at planApart planBound
    have tn := plan.2 (2 + a) (by simp only [List.length_append, preLen]; omega)
    have gn : (pre ++ wordsAll fields)[2 + a]'(by simp only [List.length_append, preLen]; omega) = fields.length := by
      rw [List.getElem_append_left (by omega)]
      simp only [pre]
      rw [List.getElem_append_right (by simp [a]; omega)]
      simp [a]
    rw [gn] at tn
    have fieldsPlan : PlanAt w mem (p + 8 * (3 + a)) (wordsAll fields) := by
      have := plan.right; rwa [preLen] at this
    have fieldsSmall : fields.length < 2 ^ 64 := by
      have := wordsAll_length_ge fields
      omega
    have q24 : UInt64.ofNat p + 24 + 8 * UInt64.ofNat a = UInt64.ofNat (p + 8 * (3 + a)) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
        UInt64.toNat_ofNat_of_lt' (lt_size (by omega)), UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
      simp; omega
    have q16 : (UInt64.ofNat p + 16 + 8 * UInt64.ofNat a).toNat = p + 8 * (2 + a) := by
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
        UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
      simp; omega
    let env₃ := assign env₂ 7 a.toUInt64
    have setK : Runs m w inner env₂ mem (.set 7 (Expr.ld (Expr.var 0 + ((8 * 1 : Nat) : Expr)))) env₃ mem :=
      Runs.set _ _ _ _ _ 7 _ _ (by evaluate [e0, a8, w1.1, w1.2])
    have eqIff : UInt64.ofNat ps.length = UInt64.ofNat fields.length ↔ ps.length = fields.length :=
      ofNat_eq_ofNat _ _ lenSmall fieldsSmall
    by_cases same : ps.length = fields.length
    · -- One part per field: the parts are laid out as a struct.
      have callee := lay_fields m w linked inner mem fields (p + 8 * (3 + a)) parts out cap ps ptrs
        (allWellFormed_mem _ (wellFormed_progressiveContainer sound)) (narrow_mem _ thin.2) fieldsPlan
        (by omega) same.symm at_ to (by simp only [inner]; omega)
      have ref : assemble (.progressiveContainer active names fields) ps = layOut fields ps := by
        simp [assemble, same]
      rw [ref]
      refine dispatch (assign env₃ 5 (assembleOutcome out cap mem (layOut fields ps)).1) _ _ ?_ (by simp [assign])
      unfold assembleDispatch assembleParts
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
        Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
      branches [e6, tag]
      refine Runs.seq setK (Runs.ite_false (by evaluate [env₃, e0, e2, q16, tn.1, tn.2, same])
        (Runs.call (values := [(p + 8 * (3 + a)).toUInt64, 0, parts.toUInt64, ps.length.toUInt64, out.toUInt64,
          cap.toUInt64]) (by evaluate [env₃, e0, e1, e2, e3, e4, q24]) callee))
    · -- Any other count is refused.
      have ref : assemble (.progressiveContainer active names fields) ps =
          .error (.scope fields.length ps.length) := by
        simp [assemble, same]
      rw [ref]
      refine dispatch (assign env₃ 5 (codeCount : Nat).toUInt64) mem _ ?_
        (by simp [assign, assembleOutcome, errCode])
      unfold assembleDispatch assembleParts
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
        Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
      branches [e6, tag]
      exact Runs.seq setK (Runs.ite_true 1 (by evaluate [env₃, e0, e2, q16, tn.1, tn.2, eqIff, same]) (by decide)
        (Runs.set _ _ _ _ _ 5 _ _ rfl))
  | _ =>
    -- A type with no parts to lay out: the code stays.
    refine dispatch env₂ mem _ ?_ (by simp [e5, assemble, assembleOutcome, errCode])
    unfold assembleDispatch assembleParts
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
      Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
    branches [e6, tag]
    exact Runs.skip _ _ _ _ _

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/-- The assembly driver, for a bit list: its packed bits closed as `assembleBits` closes them, given its bit count. -/
theorem assemble_bits_ok (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory) (d : Desc)
    (limit : Option Nat) (p parts out cap count : Nat) (packed : ByteArray) (ptr : Nat)
    (bits : bitsLimit d = some limit) (small : assembleSmall d) (smallCount : count < 2 ^ 64)
    (plan : PlanAt w mem p (words d)) (at_ : PartsAt w mem parts [packed] [ptr])
    (to : OutAt w parts [packed] [ptr] out cap) (room : w.stackLo + 8 + 8 * assembleParts.frame + assembleRoom d ≤ sp) :
    Calls m w "ssz_assemble" sp [p.toUInt64, parts.toUInt64, count.toUInt64, out.toUInt64, cap.toUInt64] mem
      (assembleOutcome out cap mem (assembleBits limit count packed)).1
      (assembleOutcome out cap mem (assembleBits limit count packed)).2 := by
  have found : m.fns.lookup "ssz_assemble" = some assembleParts :=
    linked ("ssz_assemble", assembleParts) (by simp [codecFns])
  have planBound : p + 8 * (words d).length ≤ 2 ^ 63 := by have := plan.1; simpa [addressBound] using this
  let inner := sp - 8 - 8 * assembleParts.frame
  let args := [p.toUInt64, parts.toUInt64, count.toUInt64, out.toUInt64, cap.toUInt64]
  have t := plan.2 0 (words_length_pos _)
  have tagWord : (words d)[0]'(words_length_pos _) = tag d := by cases d <;> rfl
  have t0 : w.access p 8 = true ∧ readLE mem p 8 = (tag d).toUInt64 := by simpa [tagWord] using t
  let env₂ := assign (assign (entryEnv args) 6 (tag d).toUInt64) 5 (codeType : Nat).toUInt64
  have dispatch : ∀ env' mem' (r : UInt64), Runs m w inner env₂ mem assembleDispatch env' mem' → env' 5 = r →
      Calls m w "ssz_assemble" sp args mem r mem' := by
    intro env' mem' r ran answer
    refine Calls.fn (env' := env') found (by omega) rfl ?_ (by simp [assembleParts, Assemble.r, eval, answer])
    rw [assembleParts_body]
    refine Runs.seq (Runs.set _ _ _ _ _ 6 _ _ ?_) (Runs.seq (Runs.set _ _ _ _ _ 5 _ _ rfl) ran)
    simp [eval, entryEnv, args, Width.bytes, toNat_toUInt64 p (by omega), t0.1, t0.2]
  have e0 : env₂ 0 = p.toUInt64 := by simp [env₂, assign, entryEnv, args]
  have e1 : env₂ 1 = parts.toUInt64 := by simp [env₂, assign, entryEnv, args]
  have e2 : env₂ 2 = count.toUInt64 := by simp [env₂, assign, entryEnv, args]
  have e3 : env₂ 3 = out.toUInt64 := by simp [env₂, assign, entryEnv, args]
  have e4 : env₂ 4 = cap.toUInt64 := by simp [env₂, assign, entryEnv, args]
  have e6 : env₂ 6 = (tag d).toUInt64 := by simp [env₂, assign]
  have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := plan_addr p 8 (by omega)
  cases d with
  | bitList bound_ =>
    simp only [bitsLimit, Option.some.injEq] at bits
    subst bits
    simp only [assembleSmall] at small
    simp only [assembleRoom] at room
    have t1 := plan.2 1 (by simp [words])
    simp [words] at t1
    have callee := bits_ok m w linked inner mem parts out cap count (some bound_) packed ptr at_ to smallCount small
      (by simp only [inner]; omega)
    refine dispatch (assign env₂ 5 (assembleOutcome out cap mem (assembleBits (some bound_) count packed)).1) _ _ ?_
      (by simp [assign])
    unfold assembleDispatch assembleParts
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
      Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
    branches [e6, tag]
    exact Runs.call (values := [parts.toUInt64, count.toUInt64, bound_.toUInt64, out.toUInt64, cap.toUInt64])
      (by evaluate [e0, e1, e2, e3, e4, a8, t1.1, t1.2]) callee
  | progressiveBitList bound_ =>
    simp only [bitsLimit, Option.some.injEq] at bits
    subst bits
    simp only [assembleSmall] at small
    simp only [assembleRoom] at room
    have t1 := plan.2 1 (by simp [words, bound_length])
    have t2 := plan.2 2 (by simp [words, bound_length])
    have a16 : (UInt64.ofNat p + 16).toNat = p + 16 := plan_addr p 16 (by simp [words, bound_length] at planBound; omega)
    have callee := bits_ok m w linked inner mem parts out cap count bound_ packed ptr at_ to smallCount small
      (by simp only [inner]; omega)
    refine dispatch (assign (assign env₂ 7 (limitWord bound_).toUInt64) 5
      (assembleOutcome out cap mem (assembleBits bound_ count packed)).1) _ _ ?_ (by simp [assign])
    unfold assembleDispatch assembleParts
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Assemble.tag, Assemble.plan,
      Assemble.k, Assemble.r, Assemble.out, Assemble.parts, Assemble.count, Assemble.cap]
    branches [e6, tag]
    -- The bound read from its two words, then the bit list's driver.
    refine Runs.seq ?_ (Runs.call (values := [parts.toUInt64, count.toUInt64, (limitWord bound_).toUInt64,
      out.toUInt64, cap.toUInt64]) (by evaluate [e1, e2, e3, e4]) callee)
    cases bound_ with
    | none =>
      simp [words, bound] at t1
      exact Runs.ite_true 1 (by evaluate [e0, a8, t1.1, t1.2]) (by decide)
        (Runs.set _ _ _ _ _ 7 _ _ (by evaluate [limitWord]))
    | some b =>
      simp [words, bound] at t1 t2
      exact Runs.ite_false (by evaluate [e0, a8, t1.1, t1.2])
        (Runs.set _ _ _ _ _ 7 _ _ (by evaluate [e0, a16, t2.1, t2.2, limitWord]))
  | _ => simp [bitsLimit] at bits

/--
What the assembly driver computes, from a type, its parts, and its count.

A bit list's one part is its packed bits, and the count is its bit count.
Any other type's count is its number of parts.
-/
def assembleReference (d : Desc) (ps : List ByteArray) (count : Nat) : Except Err ByteArray :=
  match bitsLimit d, ps with
  | some limit, [packed] => assembleBits limit count packed
  | _, _ => assemble d ps

/--
The assembly driver `ssz_assemble` answers what `assembleReference` computes, and writes it to the output.

The answer is the encoding's size with its bytes at the output, or a refusal's code with memory unchanged.
A bit list takes exactly one part and its bit count; any other type takes its number of parts as the count.
-/
theorem ssz_assemble_correct (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory) (d : Desc)
    (p parts out cap count : Nat) (ps : List ByteArray) (ptrs : List Nat) (sound : d.wellFormed = .ok ())
    (thin : narrow d = true) (small : assembleSmall d) (smallCount : count < 2 ^ 64)
    (counted : bitsLimit d = none → count = ps.length) (single : bitsLimit d ≠ none → ps.length = 1)
    (plan : PlanAt w mem p (words d)) (planApart : p + 8 * (words d).length ≤ out ∨ out + cap ≤ p)
    (at_ : PartsAt w mem parts ps ptrs) (to : OutAt w parts ps ptrs out cap)
    (room : w.stackLo + 8 + 8 * assembleParts.frame + assembleRoom d ≤ sp) :
    Calls m w "ssz_assemble" sp [p.toUInt64, parts.toUInt64, count.toUInt64, out.toUInt64, cap.toUInt64] mem
      (assembleOutcome out cap mem (assembleReference d ps count)).1
      (assembleOutcome out cap mem (assembleReference d ps count)).2 := by
  cases bits : bitsLimit d with
  | none =>
    rw [counted bits]
    have same : assembleReference d ps ps.length = assemble d ps := by simp [assembleReference, bits]
    rw [same]
    exact assemble_ok m w linked sp mem d p parts out cap ps ptrs sound thin small bits plan planApart at_ to room
  | some limit =>
    -- A bit list: one part, and one start for it.
    obtain ⟨packed, rfl⟩ : ∃ packed, ps = [packed] := by
      match ps, single (by simp [bits]) with
      | [packed], _ => exact ⟨packed, rfl⟩
    obtain ⟨ptr, rfl⟩ : ∃ ptr, ptrs = [ptr] := by
      match ptrs, at_.count with
      | [ptr], _ => exact ⟨ptr, rfl⟩
    have same : assembleReference d [packed] count = assembleBits limit count packed := by
      simp [assembleReference, bits]
    rw [same]
    exact assemble_bits_ok m w linked sp mem d limit p parts out cap count packed ptr bits small smallCount plan at_
      to room

end Ssz.Native.Driver
