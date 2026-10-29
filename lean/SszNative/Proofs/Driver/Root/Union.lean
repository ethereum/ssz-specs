import SszNative.Proofs.Driver.Root.Sequence
import SszNative.Proofs.Driver.Root.BitList
import SszNative.Proofs.Driver.Validate.PlanCheck

/-!
The union driver writes the Lean root of a compatible union: the root of the option its selector names, with the
selector mixed in.

The driver walks the selectors and the option plans together, and roots the value with the first option whose
selector matches.
Decoding found that option the same way, so the walk never runs past the options.
-/

namespace Ssz.Native.Driver

open Ssz Ssz.Native.Ir Ssz.Native.Ir.Expr Ssz.Native.Ir.Stmt Ssz.Native.Asm

/-- A member of narrow types is narrow. -/
theorem narrowAll_mem : ∀ (fs : List Desc), narrowAll fs = true → ∀ f ∈ fs, narrow f = true
  | [], _, _, h => by simp at h
  | g :: rest, h, f, hf => by
    simp only [narrowAll, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hf with rfl | hf
    · exact h.1
    · exact narrowAll_mem rest h.2 f hf

/-- The union driver's frame holds nineteen words. -/
theorem unionFrame : RootUnion.fn.frame = 19 := by decide

/-- The union driver's search for the selected option. -/
abbrev unionLoop : Stmt :=
  while_ (lt RootUnion.i RootUnion.n &&& eq RootUnion.found 0) [
    ifElse (eq (ld (RootUnion.p + 16 + 8 * RootUnion.i)) RootUnion.sel)
      [callInto RootUnion.sink "ssz_root_of" [RootUnion.q, RootUnion.src + 1, RootUnion.size - 1, RootUnion.scratch,
        RootUnion.scratch + 64, RootUnion.ctx], RootUnion.found ::= 1]
      [callInto RootUnion.q "ssz_plan_next" [RootUnion.q], RootUnion.i ::= RootUnion.i + 1]]

/-- The union driver's body, in its parts. -/
theorem rootUnion_body_eq : RootUnion.fn.body = .block ([RootUnion.n ::= ld (RootUnion.p + 8),
    RootUnion.sel ::= ld1 RootUnion.src, RootUnion.q ::= RootUnion.p + 16 + 8 * RootUnion.n, RootUnion.i ::= 0,
    RootUnion.found ::= 0, unionLoop, when (eq RootUnion.found 0) (zero32 RootUnion.scratch)] ++
    (lengthNodeAt (Expr.var 4 + 32) (Expr.var 7) ++
      [.call "ssz_hash_pairs" [Expr.var 3, Expr.var 4, Expr.var 4 + 32, 1, Expr.var 5] 11])) := rfl

/-- Two words that are one or zero, joined by a bitwise and. -/
theorem bit_and (a c : Bool) : ((if a then 1 else 0 : UInt64) &&& (if c then 1 else 0)) = if a && c then 1 else 0 := by
  cases a <;> cases c <;> decide

/-- The stack a range call needs, by the nesting. -/
abbrev rootStack' (n : Nat) : Nat := 12288 + 1024 * n

/-- A child one level down finds its stack below a parent's frame of at most 160 bytes. -/
theorem child_room {lo sp n D : Nat} (hn : n ≤ D) (h : lo + (12288 + 1024 * (D + 1)) + 0 ≤ sp) :
    lo + rootStack' n + 256 ≤ sp - 160 ∧ lo + 112 * n ≤ sp - 160 := by
  simp only [rootStack']; omega

/-- A parent's frame of 160 bytes leaves a hashing call its stack. -/
theorem frame_room {lo sp sp' D : Nat} (h : lo + (12288 + 1024 * (D + 1)) + 0 ≤ sp) (e : sp' = sp - 160) :
    lo + hashStack ≤ sp' ∧ lo + 8 + 8 * 19 ≤ sp ∧ sp - 8 - 8 * 19 = sp' := by
  have hs : hashStack = 10392 := rfl
  rw [hs, e]
  rw [Nat.add_zero, Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, ← Nat.add_assoc] at h
  omega

set_option maxHeartbeats 16000000 in
/-- The union driver writes the Lean root of a compatible union's range. -/
theorem rootUnion_ok {m : Module} {w : World} (hash : HashingOk m w) (fns : RangeFns m) {selectors : List Nat}
    {options : List Desc} (ih : ∀ o ∈ options, RootOfOk m w o) :
    RangeOk m w "ssz_root_union" (.compatibleUnion selectors options) := by
  intro sp mem p base start stop out scratch ctx table zeros pad mask b room pre
  have usize := pre.usize
  have small := pre.small
  unfold RootProof.Small at small
  rw [usize] at small
  have ordered := pre.ordered
  have inside := pre.inside
  have spread := pre.spread
  have bound : addressBound = 2 ^ 63 := rfl
  have capv := cap_eq
  obtain ⟨-, lens, -, rng, wfs, -⟩ := Validate.wf_union selectors options pre.sound
  have thinAll : narrowAll options = true := by have := pre.thin; simpa [narrow] using this
  -- What decoding gives: a selector byte, and the options' search from it.
  obtain ⟨v, read⟩ := pre.accepted
  have size := slice_size b start stop inside
  simp only [deserialize, throw, throwThe, MonadExceptOf.throw] at read
  split at read
  · cases read
  rename_i nonempty
  rw [size] at nonempty
  generalize hsel : ((slice b start stop)[0]!).toNat = sel at read
  have selByte : sel = (b.get! start).toNat := by
    rw [← hsel, slice_getElem! b start stop 0 inside (by omega), Nat.add_zero]
  rw [slice_extract b start stop 1 _ ordered (by rw [size]; exact Nat.le_refl _), size,
    show start + (stop - start) = stop by omega] at read
  have selSmall : sel < 256 := by rw [selByte]; exact (b.get! start).toNat_lt
  -- The plan: the tag, the count, the selectors, then the options' plans.
  have words : Plan.words (.compatibleUnion selectors options) =
      [12, options.length] ++ selectors ++ Plan.wordsAll options := by rw [Plan.words]
  have planAll := pre.plan
  rw [words] at planAll
  obtain ⟨planHead, planOpts⟩ := wordsAt_split planAll
  obtain ⟨planTag, planSels⟩ := wordsAt_split planHead
  simp only [List.length_cons, List.length_nil] at planSels planOpts
  have fitsAll := pre.fits
  rw [words] at fitsAll
  obtain ⟨fitsHead, fitsOpts⟩ := fits_split fitsAll
  obtain ⟨fitsTag, fitsSels⟩ := fits_split fitsHead
  have nSmall : options.length < 2 ^ 64 := fitsTag _ (by simp)
  -- The scratch: the option's root, the selector's node, then the option's scratch.
  obtain ⟨F, hF⟩ : ∃ F, fieldsVarNeed options (stop - start) 0 = F := ⟨_, rfl⟩
  have need : varNeed (.compatibleUnion selectors options) (stop - start) = 64 + F := by
    have below := pre.below
    simp only [varNeed, hF] at below ⊢
    simp only [sadd, sat] at below ⊢
    omega
  have sAcc := pre.sAcc
  have sSlack := pre.sSlack
  have sB := pre.sB
  have sPad := pre.sPad
  have sCtx := pre.sCtx
  have sTable := pre.sTable
  have sZeros := pre.sZeros
  have sOut := pre.sOut
  have sPlan := pre.sPlan
  have below := pre.below
  rw [need] at sAcc sSlack sB sPad sCtx sTable sZeros sOut sPlan below
  have as := access_bound sAcc
  have planLen : 8 * (Plan.words (.compatibleUnion selectors options)).length =
      16 + 8 * selectors.length + 8 * (Plan.wordsAll options).length := by
    rw [words]; simp; omega
  rw [planLen] at sPlan
  -- The stack.
  have stackU : rootStack (.compatibleUnion selectors options) = 12288 + 1024 * (Desc.deepestNesting options + 1) := by
    simp [rootStack, Desc.nesting]
  have frameEq : sp - 8 - 8 * RootUnion.fn.frame = sp - 160 := by rw [unionFrame]; omega
  generalize hsp' : sp - 8 - 8 * RootUnion.fn.frame = sp' at frameEq
  clear hsp'
  rw [stackU] at room
  obtain ⟨hashRoom, unionRoom, spEq⟩ := frame_room room frameEq
  have room' : ∀ o ∈ options, w.stackLo + rootStack o + 256 ≤ sp' ∧ w.stackLo + walkLevel * o.nesting ≤ sp' := by
    intro o mo
    rw [walkLevel_eq, frameEq]
    exact child_room (Validate.nesting_le_deepest options o mo) room
  have ab := access_bound pre.bAcc
  -- The selected option's root is one node.
  obtain ⟨chosen, inner, chosenMem, -, -, chosenRead, chosenRoot⟩ :=
    RootProof.option_search b (start + 1) stop selectors options sel _ v read
  have chosenSound := Validate.allWellFormed_mem options wfs chosen chosenMem
  have rootSize : (optionRoot selectors options sel b (start + 1) stop).size = 32 := by
    rw [chosenRoot]; exact rootOf_size chosenSound (by omega) inside pre.small ⟨inner, chosenRead⟩
  -- The plan of option i starts after the plans of the options before it.
  let qa : Nat → Nat := fun i => p + 16 + 8 * options.length + 8 * (Plan.wordsAll (options.take i)).length
  have planAt : ∀ i, WordsAt w mem (qa i) (Plan.wordsAll (options.drop i)) := by
    intro i
    have := planOpts
    rw [← List.take_append_drop i options, Validate.wordsAll_append] at this
    have := (wordsAt_split this).2
    simp only [List.length_append, List.length_cons, List.length_nil, lens] at this
    have e : p + 8 * (0 + 1 + 1 + options.length) + 8 * (Plan.wordsAll (List.take i options)).length = qa i := by
      simp only [qa]; omega
    rw [e] at this
    exact this
  have planIn : ∀ i, p ≤ qa i ∧ qa i + 8 * (Plan.wordsAll (options.drop i)).length ≤
      p + (16 + 8 * selectors.length + 8 * (Plan.wordsAll options).length) := by
    intro i
    have := congrArg List.length (Validate.wordsAll_append (options.take i) (options.drop i))
    rw [List.take_append_drop, List.length_append] at this
    simp only [qa, lens]; omega
  have ev0 := rangeEnv_entry p (base + start) (stop - start) out scratch ctx
  -- The option count, the selector, the first option's plan, and the search's state.
  have nw : eval w (entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (stop - start),
      UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx]) mem (ld (RootUnion.p + 8)) =
      some (UInt64.ofNat options.length) :=
    eval_word planTag 1 (by simp) (e := RootUnion.p + 8) (eval_add (eval_var ev0.p) (eval_lit 8))
  have s1 := Runs.set' (m := m) (w := w) (sp := sp') (x := 6) nw
  have ev1 := ev0.write (x := 6) (UInt64.ofNat options.length) (by decide)
  have n1 : Asm.assign (entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (stop - start),
      UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx]) 6 (UInt64.ofNat options.length) 6 =
      UInt64.ofNat options.length := assign_eq
  generalize Asm.assign (entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (stop - start),
    UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx]) 6 (UInt64.ofNat options.length) = E1 at s1 ev1 n1
  have selE : eval w E1 mem (ld1 RootUnion.src) = some (UInt64.ofNat sel) := by
    rw [eval_ld1_of (eval_var ev1.src) (access_sub pre.bAcc (by omega) (by omega)), readLE_byte,
      pre.holds start (by omega), selByte]
  have s2 := Runs.set' (m := m) (w := w) (sp := sp') (x := 7) selE
  have s3 := Runs.set' (m := m) (w := w) (sp := sp') (env := Asm.assign E1 7 (UInt64.ofNat sel)) (mem := mem) (x := 8)
    (eval_add (eval_add (eval_var (show Asm.assign E1 7 (UInt64.ofNat sel) 0 = UInt64.ofNat p by
        rw [assign_ne (by decide)]; exact ev1.p)) (eval_lit 16))
      (eval_mul (eval_lit 8) (eval_var (show Asm.assign E1 7 (UInt64.ofNat sel) 6 = UInt64.ofNat options.length by
        rw [assign_ne (by decide)]; exact n1))))
  let E3 := Asm.assign (Asm.assign E1 7 (UInt64.ofNat sel)) 8 (UInt64.ofNat (p + 16 + 8 * options.length))
  have s4 := Runs.set' (m := m) (w := w) (sp := sp') (env := E3) (mem := mem) (x := 9) (eval_lit 0)
  have s5 := Runs.set' (m := m) (w := w) (sp := sp') (env := Asm.assign E3 9 (UInt64.ofNat 0)) (mem := mem) (x := 10)
    (eval_lit 0)
  -- The search: still looking at option i, or done with the option's root at the scratch.
  let Keep : Env → Prop := fun e => RangeEnv e p (base + start) (stop - start) out scratch ctx ∧
    e 6 = UInt64.ofNat options.length ∧ e 7 = UInt64.ofNat sel
  let inv : Env → Memory → Prop := fun e mm => Keep e ∧
    ((∃ i, i ≤ options.length ∧ e 8 = UInt64.ofNat (qa i) ∧ e 9 = UInt64.ofNat i ∧ e 10 = UInt64.ofNat 0 ∧
        mm = mem ∧ (∃ w', deserializeOption (selectors.drop i) (options.drop i) sel (slice b (start + 1) stop) =
          .ok w') ∧ optionRoot selectors options sel b (start + 1) stop =
          optionRoot (selectors.drop i) (options.drop i) sel b (start + 1) stop) ∨
      (∃ i, i ≤ options.length ∧ e 9 = UInt64.ofNat i ∧ e 10 = UInt64.ofNat 1 ∧
        nodeAt mm scratch = (optionRoot selectors options sel b (start + 1) stop).data ∧
        ∀ a, ¬ (scratch ≤ a ∧ a < scratch + (64 + F)) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm a = mem a))
  have keepW : ∀ e x v, Keep e → 8 ≤ x → Keep (Asm.assign e x v) := fun e x v k h =>
    ⟨k.1.write v (by omega), by rw [assign_ne (by omega)]; exact k.2.1, by rw [assign_ne (by omega)]; exact k.2.2⟩
  have start0 : inv (Asm.assign (Asm.assign E3 9 (UInt64.ofNat 0)) 10 (UInt64.ofNat 0)) mem := by
    refine ⟨keepW _ _ _ (keepW _ _ _ (keepW _ _ _ ⟨ev1.write _ (by decide), by rw [assign_ne (by decide)]; exact n1,
      assign_eq⟩ (by decide)) (by decide)) (by decide), .inl ⟨0, Nat.zero_le _, ?_, ?_, assign_eq, rfl,
      ⟨v, by simpa using read⟩, by simp⟩⟩
    · rw [assign_ne (by decide), assign_ne (by decide)]; simp only [E3]; rw [assign_eq]; congr 1
    · rw [assign_ne (by decide), assign_eq]
  -- A search still looking has an option and a selector left.
  have left : ∀ i, (∃ w', deserializeOption (selectors.drop i) (options.drop i) sel (slice b (start + 1) stop) =
      .ok w') → ∃ c sr o or, selectors.drop i = c :: sr ∧ options.drop i = o :: or := by
    intro i ⟨w', h⟩
    cases hs : selectors.drop i with
    | nil => cases ho : options.drop i <;> simp [hs, ho, deserializeOption] at h
    | cons c sr =>
      cases ho : options.drop i with
      | nil => simp [hs, ho, deserializeOption] at h
      | cons o or => exact ⟨c, sr, o, or, rfl, rfl⟩
  have condEval : ∀ e mm, inv e mm → ∃ i, i ≤ options.length ∧ e 9 = UInt64.ofNat i ∧
      eval w e mm (lt RootUnion.i RootUnion.n &&& eq RootUnion.found 0) =
        some ((if i < options.length then 1 else 0) &&& (if e 10 = 0 then 1 else 0)) := by
    rintro e mm ⟨k, h | h⟩
    · obtain ⟨i, hi, -, h9, h10, -⟩ := h
      exact ⟨i, hi, h9, by
        rw [eval_and (eval_lt (eval_var h9) (eval_var k.2.1) (by omega) nSmall) (eval_eq (eval_var h10) (eval_lit 0)
          (by decide) (by decide))]; simp [h10]⟩
    · obtain ⟨i, hi, h9, h10, -⟩ := h
      exact ⟨i, hi, h9, by
        rw [eval_and (eval_lt (eval_var h9) (eval_var k.2.1) (by omega) nSmall) (eval_eq (eval_var h10) (eval_lit 0)
          (by decide) (by decide))]; simp [h10]⟩
  have optWords : ∀ o ∈ options, ∀ x ∈ Plan.words o, x ∈ Plan.wordsAll options := by
    intro o mo x hx
    obtain ⟨as, bs, rfl⟩ := List.append_of_mem mo
    rw [Validate.wordsAll_append]; simp [Plan.wordsAll, hx]
  obtain ⟨E6, mem6, run6, ⟨k6, h6⟩, exit⟩ := Ends.loop (m := m) (w := w) (sp := sp')
    (env := Asm.assign (Asm.assign E3 9 (UInt64.ofNat 0)) 10 (UInt64.ofNat 0)) (mem := mem)
    (c := lt RootUnion.i RootUnion.n &&& eq RootUnion.found 0)
    (body := .block [ifElse (eq (ld (RootUnion.p + 16 + 8 * RootUnion.i)) RootUnion.sel)
      [callInto RootUnion.sink "ssz_root_of" [RootUnion.q, RootUnion.src + 1, RootUnion.size - 1, RootUnion.scratch,
        RootUnion.scratch + 64, RootUnion.ctx], RootUnion.found ::= 1]
      [callInto RootUnion.q "ssz_plan_next" [RootUnion.q], RootUnion.i ::= RootUnion.i + 1]])
    inv (fun e _ => (options.length + 1 - (e 9).toNat) + (if e 10 = 0 then 1 else 0)) start0
    (fun e mm h => by obtain ⟨i, _, _, hc⟩ := condEval e mm h; exact ⟨_, hc⟩)
    (by
      rintro e mm vv ⟨k, h⟩ hv nz
      rcases h with h | h
      · obtain ⟨i, hi, h8, h9, h10, rfl, dec, req⟩ := h
        obtain ⟨c, sr, o, or, hs, ho⟩ := left i dec
        have hio : i < options.length := by
          have := congrArg List.length ho; simp at this; omega
        have mo : o ∈ options := List.mem_of_mem_drop (by rw [ho]; simp)
        have soundO := Validate.allWellFormed_mem options wfs o mo
        have hci : selectors[i]? = some c := by
          have := congrArg (·[0]?) hs; simpa [List.getElem?_drop] using this
        have his : i < selectors.length := by omega
        have hci' : selectors[i] = c := by
          rw [List.getElem?_eq_getElem his] at hci; exact Option.some.inj hci
        have cSmall : c < 2 ^ 64 := fitsSels c (by rw [← hci']; exact List.getElem_mem _)
        have wordE : eval w e mm (ld (RootUnion.p + 16 + 8 * RootUnion.i)) = some (UInt64.ofNat c) := by
          have := eval_word (w := w) (env := e) (mem := mm) planSels i his (e := RootUnion.p + 16 + 8 * RootUnion.i)
            (by
              rw [show p + 8 * (0 + 1 + 1) + 8 * i = p + 16 + 8 * i by omega]
              exact eval_add (eval_add (eval_var k.1.p) (eval_lit 16)) (eval_mul (eval_lit 8) (eval_var h9)))
          rw [this, hci']
        have cmp := eval_eq (w := w) (env := e) (mem := mm) wordE (eval_var k.2.2) cSmall (by omega)
        have planDrop := planAt i
        rw [ho, show Plan.wordsAll (o :: or) = Plan.words o ++ Plan.wordsAll or from rfl] at planDrop
        have planO := (wordsAt_split planDrop).1
        have oIn : p ≤ qa i ∧ qa i + 8 * (Plan.words o).length ≤
            p + (16 + 8 * selectors.length + 8 * (Plan.wordsAll options).length) := by
          have := planIn i
          rw [ho, show Plan.wordsAll (o :: or) = Plan.words o ++ Plan.wordsAll or from rfl, List.length_append] at this
          omega
        by_cases hcs : c = sel
        · -- The selected option: its root, into the scratch.
          rw [if_pos hcs] at cmp
          have dec' := dec
          obtain ⟨w', dec'⟩ := dec'
          rw [hs, ho] at dec'
          simp only [deserializeOption, hcs, beq_self_eq_true, if_true] at dec'
          obtain ⟨_, _, dec''⟩ := checksPassed dec'
          simp only [Bind.bind, Except.bind, pure, Except.pure] at dec''
          split at dec''
          · cases dec''
          rename_i innerO decO
          have rootEqO : optionRoot selectors options sel b (start + 1) stop = rootOf o b (start + 1) stop := by
            rw [req, hs, ho, optionRoot.eq_def]; simp [hcs]
          have grow := varNeed_mono o (show stop - (start + 1) ≤ stop - start by omega)
          have mem' := fieldsVarNeed_mem options (stop - start) 0 o mo
          rw [hF] at mem'
          have childPre : RangePre w mm o (qa i) base (start + 1) stop scratch (scratch + 64) ctx table zeros pad mask b :=
            rangePre_of pre.ready planO (fun x hx => fitsOpts x (optWords o mo x hx)) pre.holds pre.bAcc (by omega)
              inside pre.small spread soundO (narrowAll_mem options thinAll o mo) ⟨innerO, decO⟩ (by omega) sAcc sSlack
              sB sPad sCtx sTable sZeros (apart_sub' sPlan oIn.1 oIn.2) pre.bPad
              (apart_comm (apart_sub' (apart_comm (by rw [← planLen]; exact pre.planPad)) oIn.1 oIn.2))
              ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by simp only [Apart]; omega) usize
          obtain ⟨mm', call, root, -, keep⟩ := ih o mo sp' mm (qa i) base (start + 1) stop scratch (scratch + 64) ctx table
            zeros pad mask b (room' o mo).1 childPre
          have r1 := Runs.call (m := m) (sp := sp') (env := e) (mem := mm) (dst := 11)
            (args := [RootUnion.q, RootUnion.src + 1, RootUnion.size - 1, RootUnion.scratch, RootUnion.scratch + 64,
              RootUnion.ctx])
            (by
              rw [show base + (start + 1) = base + start + 1 by omega, show stop - (start + 1) = stop - start - 1 by omega]
              simp only [List.mapM_cons, List.mapM_nil, eval_var h8, eval_add (eval_var k.1.src) (eval_lit 1),
                eval_sub (eval_var k.1.size) (eval_lit 1) (show 1 ≤ stop - start by omega), eval_var k.1.scratch,
                eval_add (eval_var k.1.scratch) (eval_lit 64), eval_var k.1.ctx]
              rfl) call
          have r2 := Runs.set' (m := m) (w := w) (sp := sp') (env := Asm.assign e 11 0) (mem := mm') (x := 10)
            (eval_lit 1)
          refine ⟨_, mm', Runs.block_cons (Runs.ifElse_true 1 cmp (by decide) (Runs.block_cons r1 (Runs.block_cons r2
            (Runs.block_nil _ _ _ _ _)))) (Runs.block_nil _ _ _ _ _),
            ⟨keepW _ _ _ (keepW _ _ _ k (by decide)) (by decide), .inr ⟨i, hi, ?_, assign_eq, ?_, fun a o' pd => ?_⟩⟩, ?_⟩
          · rw [assign_ne (by decide), assign_ne (by decide)]; exact h9
          · rw [root, rootEqO]
          · exact keep a (fun h => o' ⟨by omega, by omega⟩) (fun h => o' ⟨by omega, by omega⟩) pd
          · show options.length + 1 - (Asm.assign (Asm.assign e 11 0) 10 (UInt64.ofNat 1) 9).toNat +
                (if Asm.assign (Asm.assign e 11 0) 10 (UInt64.ofNat 1) 10 = 0 then 1 else 0) <
              options.length + 1 - (e 9).toNat + (if e 10 = 0 then 1 else 0)
            rw [assign_ne (by decide), assign_ne (by decide), assign_eq, h9, h10, ofNat_toNat (by omega)]
            simp
        · -- Another option: its plan is skipped.
          rw [if_neg hcs] at cmp
          have next := next_ok m w fns.roots.plan.codec o soundO sp' mm (qa i) planO (room' o mo).2
          have r1 := Runs.call (m := m) (sp := sp') (env := e) (mem := mm) (dst := 8) (args := [RootUnion.q])
            (by simp only [List.mapM_cons, List.mapM_nil, eval_var h8]; rfl) next
          have r2 := Runs.set' (m := m) (w := w) (sp := sp')
            (env := Asm.assign e 8 (qa i + 8 * (Plan.words o).length).toUInt64) (mem := mm) (x := 9)
            (eval_add (eval_var (show Asm.assign e 8 (qa i + 8 * (Plan.words o).length).toUInt64 9 = UInt64.ofNat i by
              rw [assign_ne (by decide)]; exact h9)) (eval_lit 1))
          have qnext : qa (i + 1) = qa i + 8 * (Plan.words o).length := by
            have oi : options[i] = o := by
              have := congrArg (·[0]?) ho; simp [List.getElem?_drop] at this
              rw [List.getElem?_eq_getElem hio] at this; exact Option.some.inj this
            simp only [qa]
            rw [List.take_add_one, List.getElem?_eq_getElem hio, oi, Validate.wordsAll_append]
            simp [Plan.wordsAll]; omega
          have dropS : ∀ {α : Type} (l : List α) (x : α) (r : List α), l.drop i = x :: r → l.drop (i + 1) = r :=
            fun l x r h => by rw [← List.drop_drop, h]; rfl
          refine ⟨_, mm, Runs.block_cons (Runs.ifElse_false cmp (Runs.block_cons r1 (Runs.block_cons r2
            (Runs.block_nil _ _ _ _ _)))) (Runs.block_nil _ _ _ _ _),
            ⟨keepW _ _ _ (keepW _ _ _ k (by decide)) (by decide), .inl ⟨i + 1, hio, ?_, assign_eq, ?_, rfl, ?_, ?_⟩⟩,
            ?_⟩
          · rw [assign_ne (by decide), assign_eq, qnext]
          · rw [assign_ne (by decide), assign_ne (by decide)]; exact h10
          · obtain ⟨w', d'⟩ := dec
            rw [hs, ho] at d'
            simp only [deserializeOption, beq_iff_eq, hcs, if_false] at d'
            exact ⟨w', by rw [dropS selectors c sr hs, dropS options o or ho]; exact d'⟩
          · rw [req, hs, ho, dropS selectors c sr hs, dropS options o or ho, optionRoot.eq_def]
            simp [hcs]
          · simp only [assign_eq, h9, h10]
            rw [assign_ne (by decide), assign_ne (by decide), h10, ofNat_toNat (by omega), ofNat_toNat (by omega)]
            simp; omega
      · -- A search that found its option has stopped.
        obtain ⟨i', _, h9', hc⟩ := condEval e mm ⟨k, .inr h⟩
        obtain ⟨_, _, _, h10, _⟩ := h
        rw [hc, h10] at hv
        simp at hv
        exact absurd hv.symm nz)
  -- The search found the option: the still-looking state has an option left, so it would go on.
  obtain ⟨i, hi, h9, h10, root6, frame6⟩ : ∃ i, i ≤ options.length ∧ E6 9 = UInt64.ofNat i ∧
      E6 10 = UInt64.ofNat 1 ∧ nodeAt mem6 scratch = (optionRoot selectors options sel b (start + 1) stop).data ∧
      ∀ a, ¬ (scratch ≤ a ∧ a < scratch + (64 + F)) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem6 a = mem a := by
    rcases h6 with h | h
    · obtain ⟨i', _, h9', hc⟩ := condEval E6 mem6 ⟨k6, .inl h⟩
      obtain ⟨i, hi, -, h9, h10, -, dec, -⟩ := h
      obtain ⟨c, sr, o, or, -, ho⟩ := left i dec
      have hio : i < options.length := by have := congrArg List.length ho; simp at this; omega
      have : i' = i := by
        rw [h9] at h9'; exact ((ofNat_inj (by omega) (by omega)).mp h9').symm
      subst this
      rw [hc, h10] at exit
      simp [hio] at exit
    · exact h
  have c0 := eval_eq (w := w) (env := E6) (mem := mem6) (a := RootUnion.found) (b := 0) (eval_var h10) (eval_lit 0)
    (by decide) (by decide)
  rw [if_neg (by decide)] at c0
  have ready6 := pre.ready.within (o := scratch) (n := 64 + F) sCtx sTable sZeros frame6
  obtain ⟨E7, mem7, run7, root7, ready7, keep7⟩ := mixin_ends hash (sp := sp') hashRoom
    ready6 k6.1.scratch k6.1.out k6.1.ctx (cnt := Expr.var 7) (n := sel) (fun _ => eval_var k6.2.2) (by omega)
    (access_sub sAcc (by omega) (by omega)) (by omega) pre.oAcc (apart_sub sOut (by omega) (by omega))
    (apart_sub sPad (by omega) (by omega)) (apart_sub sCtx (by omega) (by omega))
    (apart_sub sTable (by omega) (by omega)) (apart_sub sZeros (by omega) (by omega)) pre.oPad pre.oCtx pre.oTable
    pre.oZeros 11
  have body : Runs m w sp' (entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (stop - start),
      UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx]) mem RootUnion.fn.body E7 mem7 := by
    rw [rootUnion_body_eq]
    exact Runs.block_append (Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons s3 (Runs.block_cons s4
      (Runs.block_cons s5 (Runs.block_cons run6 (Runs.block_cons (Runs.when_false c0)
        (Runs.block_nil _ _ _ _ _)))))))) run7
  rw [← spEq, ← unionFrame] at body
  refine ⟨mem7, Calls.fn fns.union (by rw [unionFrame]; exact unionRoom) rfl body rfl, ?_, ready7, fun a o s pd => ?_⟩
  · rw [root7, root6]
    have code : rootOf (.compatibleUnion selectors options) b start stop =
        hashPair (optionRoot selectors options sel b (start + 1) stop) (lengthNode sel) := by
      rw [rootOf, selByte]
    rw [code, RootProof.hashPair_data _ _ rootSize (by simp [lengthNode, ByteArray.size])]
  · rw [need] at s
    rw [keep7 a (fun h => s ⟨by omega, by omega⟩) o pd]
    exact frame6 a s pd

end Ssz.Native.Driver
