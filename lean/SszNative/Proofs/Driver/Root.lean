import SszNative.Driver.Root
import SszNative.Proofs.Ir.Logic
import EthLib.Consensus.Proofs.Ssz.Merkle.Merkleize
import SszNative.Plan
import SszNative.Proofs.Driver.Codec
import SszNative.Proofs.Driver.Hash

/-!
The root drivers compute the Lean root computation.

Each driver function is proved against the Lean definition it mirrors, as a call that runs to the right result.

The plan readers here give a type's width, and say whether it has a fixed size and whether it is plain.
They step past a field with the codec's walk past one node, and hold for every well-formed type, given enough stack
for the type's nesting.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Asm

/-! ### Notation as constructors -/

section Notation
variable (a b : Expr)

/-- A sum is the add operation. -/
@[simp] theorem add_eq : a + b = .op .add a b := rfl
/-- A difference is the sub operation. -/
@[simp] theorem sub_eq : a - b = .op .sub a b := rfl
/-- A product is the mul operation. -/
@[simp] theorem mul_eq : a * b = .op .mul a b := rfl
/-- A quotient is the division. -/
@[simp] theorem div_eq : a / b = .div a b := rfl
/-- A remainder is the remainder operation. -/
@[simp] theorem mod_eq : a % b = .mod a b := rfl
/-- A bitwise and is the and operation. -/
@[simp] theorem and_eq : (a &&& b) = .op .and a b := rfl
/-- A bitwise or is the or operation. -/
@[simp] theorem or_eq : (a ||| b) = .op .or a b := rfl
/-- A bitwise exclusive or is the xor operation. -/
@[simp] theorem xor_eq : (a ^^^ b) = .op .xor a b := rfl
/-- A numeral is a constant. -/
@[simp] theorem ofNat_eq (n : Nat) : (OfNat.ofNat n : Expr) = .lit (OfNat.ofNat n) := rfl
/-- A computed constant is a constant. -/
@[simp] theorem natCast_eq (n : Nat) : (n : Expr) = .lit n.toUInt64 := rfl

/-- Below is the unsigned below comparison. -/
@[simp] theorem lt_eq' : Expr.lt a b = .cmp .b a b := rfl
/-- At most is the unsigned below-or-equal comparison. -/
@[simp] theorem le_eq' : Expr.le a b = .cmp .be a b := rfl
/-- Equality is the equal comparison. -/
@[simp] theorem eq_eq' : Expr.eq a b = .cmp .e a b := rfl
/-- Inequality is the not-equal comparison. -/
@[simp] theorem ne_eq' : Expr.ne a b = .cmp .ne a b := rfl
/-- An eight-byte load. -/
@[simp] theorem ld_eq : ld a = .load .b8 a := rfl
/-- A one-byte load. -/
@[simp] theorem ld1_eq : ld1 a = .load .b1 a := rfl
/-- A four-byte load. -/
@[simp] theorem ld4_eq : ld4 a = .load .b4 a := rfl

end Notation


/-! ### Depth -/

/-- Halving rounded up is the sum of the half and the remainder. -/
private theorem half_up (n : Nat) : (n + 1) / 2 = n / 2 + n % 2 := by omega

/-- A depth step: more than one leaf takes one level more than half of them, rounded up. -/
private theorem depthFor_step {n : Nat} (big : 1 < n) : depthFor n = depthFor (n / 2 + n % 2) + 1 := by
  rw [depthFor, ite_eq_right (by omega), half_up]

/-- At most one leaf needs no level. -/
private theorem depthFor_small {n : Nat} (small : n ≤ 1) : depthFor n = 0 := by
  rw [depthFor, ite_eq_left small]

/-- The depth for any count a word holds is at most 64. -/
theorem depthFor_word (n : UInt64) : depthFor n.toNat ≤ 64 :=
  depthFor_le_of_le_two_pow (Nat.le_of_lt n.toNat_lt)

/-- The depth function computes the depth for its argument, and leaves memory alone. -/
theorem depthFor_calls {m : Module} {w : World} (hf : m.fns.lookup "ssz_depth_for" = some DepthFor.fn)
    {sp : Nat} (room : w.stackLo + 8 + 8 * DepthFor.fn.frame ≤ sp) (n : UInt64) (mem : Memory) :
    Calls m w "ssz_depth_for" sp [n] mem (depthFor n.toNat).toUInt64 mem := by
  -- The loop keeps the depth so far plus the depth still to come equal to the answer.
  let inv : Env → Memory → Prop := fun env mem' =>
    mem' = mem ∧ (env 1).toNat + depthFor (env 0).toNat = depthFor n.toNat
  obtain ⟨env', mem', loop, ⟨same, total⟩, exit⟩ :=
    Runs.loop_inv (m := m) (w := w) (sp := sp - 8 - 8 * DepthFor.fn.frame) (c := lt 1 DepthFor.n)
      (body := .block [DepthFor.n ::= DepthFor.n / 2 + DepthFor.n % 2, DepthFor.d ::= DepthFor.d + 1])
      inv (fun env _ => (env 0).toNat)
      (fun env mem _ => ⟨_, by simp [eval, Cond.holds]; rfl⟩)
      (by
        intro env mem v ⟨same, total⟩ hv nz
        simp [eval, Cond.holds] at hv
        have big : 1 < (env 0).toNat := by
          by_cases h : 1 < env 0
          · exact UInt64.lt_iff_toNat_lt.mp h
          · simp [h] at hv; exact absurd hv.symm nz
        refine ⟨_, _, Runs.block_cons (Runs.set _ _ _ _ _ _ _ _ (by simp [eval, aluResult]; rfl))
          (Runs.set _ _ _ _ _ _ _ _ (by simp [eval, aluResult]; rfl)), ⟨same, ?_⟩, ?_⟩
        all_goals
          have step := depthFor_step big
          have bound := depthFor_word n
          have halve : (env 0 / 2 + env 0 % 2).toNat = (env 0).toNat / 2 + (env 0).toNat % 2 := by
            have := (env 0).toNat_lt
            simp only [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod]
            simp; omega
          have bump : (env 1 + 1).toNat = (env 1).toNat + 1 := by
            simp only [UInt64.toNat_add]; simp; omega
          simp only [Asm.assign]
          simp [halve, bump]
          omega)
      (Asm.assign (entryEnv [n]) 1 0) mem ⟨rfl, by simp [Asm.assign, entryEnv]⟩
  subst same
  refine Calls.fn hf room rfl (Runs.block_cons (Runs.set _ _ _ _ _ _ _ _ rfl)
    (show Runs _ _ _ _ _ (Stmt.block [while_ _ _]) _ _ from loop)) ?_
  -- The loop stops at one leaf or none, which needs no level more.
  have small : (env' 0).toNat ≤ 1 := by
    simp [eval, Cond.holds] at exit
    have := UInt64.le_iff_toNat_le.mp exit
    simpa using this
  rw [depthFor_small small] at total
  simp only [DepthFor.fn, DepthFor.d, eval]
  congr 1
  apply UInt64.toNat_inj.mp
  simp [← total]

/-! ### Plans in memory -/

/-- Words at an address: the codec's plan predicate, under the name these proofs use. -/
abbrev WordsAt (w : World) (mem : Memory) (a : Nat) (ws : List Nat) : Prop := PlanAt w mem a ws

/-- Words at an address split at the end of a first part. -/
theorem wordsAt_split {w : World} {mem : Memory} {a : Nat} {xs ys : List Nat} (h : WordsAt w mem a (xs ++ ys)) :
    WordsAt w mem a xs ∧ WordsAt w mem (a + 8 * xs.length) ys :=
  ⟨h.left, h.right⟩

/-- A list of types whose plans fit in memory has fewer types than a word counts. -/
theorem fields_small {w : World} {mem : Memory} {a : Nat} {fs : List Desc} (h : WordsAt w mem a (Plan.wordsAll fs)) :
    fs.length < 2 ^ 64 := by
  have := wordsAll_length_ge fs
  have := h.1
  simp only [addressBound] at this
  omega

/-- A list of types each of which is well formed: its first, and the rest. -/
theorem allWellFormed_cons {f : Desc} {rest : List Desc} (h : Desc.allWellFormed (f :: rest) = .ok ()) :
    f.wellFormed = .ok () ∧ Desc.allWellFormed rest = .ok () := by
  cases hf : f.wellFormed <;> simp_all [Desc.allWellFormed, Bind.bind, Except.bind]

/-- Every type nests at least one level. -/
theorem nesting_pos (d : Desc) : 1 ≤ d.nesting := by
  cases d <;> simp [Desc.nesting]

/-- One level of the plan walk takes 112 bytes of stack, more than any plan reader's frame. -/
theorem walkLevel_eq : walkLevel = 112 := by decide

/-! ### Evaluating expressions one constructor at a time -/

section EvalSteps
variable {w : World} {env : Env} {mem : Memory}

/-- A constant's value. -/
theorem eval_lit' (n : UInt64) : eval w env mem (.lit n) = some n := rfl

/-- A variable's value. -/
theorem eval_var' (x : Nat) : eval w env mem (.var x) = some (env x) := rfl

/-- An operation's value, from its operands'. -/
theorem eval_op' (o : Alu) (a b : Expr) : eval w env mem (.op o a b) =
    (eval w env mem a).bind fun x => (eval w env mem b).bind fun y => some (aluResult o x y).1 := rfl

/-- A quotient's value, from its operands', with no value for a zero divisor. -/
theorem eval_div' (a b : Expr) : eval w env mem (.div a b) =
    (eval w env mem a).bind fun x => (eval w env mem b).bind fun y => if y == 0 then none else some (x / y) := rfl

/-- A remainder's value, from its operands', with no value for a zero divisor. -/
theorem eval_mod' (a b : Expr) : eval w env mem (.mod a b) =
    (eval w env mem a).bind fun x => (eval w env mem b).bind fun y => if y == 0 then none else some (x % y) := rfl

/-- A comparison's value, from its operands'. -/
theorem eval_cmp' (c : Cond) (a b : Expr) : eval w env mem (.cmp c a b) =
    (eval w env mem a).bind fun x => (eval w env mem b).bind fun y =>
      some (if c.holds (x == y) (x < y) then 1 else 0) := rfl

end EvalSteps

/-! ### Running statements -/

section Steps
variable {m : Module} {w : World} {sp : Nat} {env env' : Env} {mem mem' : Memory}

/-- An assignment runs to the variables with its value. -/
theorem Runs.set' {x : Nat} {e : Expr} {v : UInt64} (h : eval w env mem e = some v) :
    Runs m w sp env mem (.set x e) (Asm.assign env x v) mem :=
  Runs.set m w sp env mem x e v h

/-- A two-way branch with a nonzero condition runs its first statements. -/
theorem Runs.ifElse_true {c : Expr} {yes no : List Stmt} (v : UInt64) (hc : eval w env mem c = some v) (nz : v ≠ 0)
    (h : Runs m w sp env mem (.block yes) env' mem') : Runs m w sp env mem (ifElse c yes no) env' mem' :=
  Runs.ite_true v hc nz h

/-- A two-way branch with a zero condition runs its second statements. -/
theorem Runs.ifElse_false {c : Expr} {yes no : List Stmt} (hc : eval w env mem c = some 0)
    (h : Runs m w sp env mem (.block no) env' mem') : Runs m w sp env mem (ifElse c yes no) env' mem' :=
  Runs.ite_false hc h

end Steps

/-- A word naming an address below two to the 64 reads back as that address. -/
theorem addr_toNat {a : Nat} (h : a < 2 ^ 64) : a.toUInt64.toNat = a := by
  simp; omega

/-- Bytes the program may use end below the address bound. -/
theorem access_end {w : World} {a n : Nat} (h : w.access a n = true) : a + n ≤ 2 ^ 63 := by
  simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- An eight-byte load from an address the program may read. -/
theorem eval_ld_of {w : World} {env : Env} {mem : Memory} {e : Expr} {a : Nat}
    (he : eval w env mem e = some a.toUInt64) (ha : a < 2 ^ 64) (acc : w.access a 8 = true) :
    eval w env mem (ld e) = some (readLE mem a 8) := by
  simp [eval, he, Width.bytes, addr_toNat ha, acc]

section Alu
variable (a b : UInt64)
/-- The sum's word. -/
@[simp] theorem alu_add : (aluResult .add a b).1 = a + b := rfl
/-- The difference's word. -/
@[simp] theorem alu_sub : (aluResult .sub a b).1 = a - b := rfl
/-- The product's word. -/
@[simp] theorem alu_mul : (aluResult .mul a b).1 = a * b := rfl
/-- The bitwise and's word. -/
@[simp] theorem alu_and : (aluResult .and a b).1 = (a &&& b) := rfl
/-- The bitwise or's word. -/
@[simp] theorem alu_or : (aluResult .or a b).1 = (a ||| b) := rfl
/-- The bitwise exclusive or's word. -/
@[simp] theorem alu_xor : (aluResult .xor a b).1 = (a ^^^ b) := rfl
end Alu

/-- The first word of a type's plan is its tag. -/
theorem words_head (d : Desc) : ∃ rest, Plan.words d = Plan.tag d :: rest := by
  cases d <;> simp [Plan.words, Plan.tag]

/-- Reading the first word of a type's plan gives its tag. -/
theorem eval_tag {w : World} {env : Env} {mem : Memory} {d : Desc} {a : Nat} {e : Expr}
    (hw : WordsAt w mem a (Plan.words d)) (he : eval w env mem e = some a.toUInt64) :
    eval w env mem (ld e) = some (Plan.tag d).toUInt64 := by
  obtain ⟨rest, hr⟩ := words_head d
  rw [hr] at hw
  obtain ⟨acc, rd⟩ := hw.read 0 (by simp)
  simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at acc rd
  rw [← rd]
  exact eval_ld_of he (by have := access_end acc; omega) acc

/-- A word of a plan read through an expression naming its address. -/
theorem eval_word {w : World} {env : Env} {mem : Memory} {a : Nat} {ws : List Nat} (h : WordsAt w mem a ws)
    (k : Nat) (hk : k < ws.length) {e : Expr} (he : eval w env mem e = some (a + 8 * k).toUInt64) :
    eval w env mem (ld e) = some ws[k].toUInt64 := by
  obtain ⟨acc, rd⟩ := h.read k hk
  rw [← rd]
  exact eval_ld_of he (by have := access_end acc; omega) acc

/-- Decides a branch condition on the tag. -/
macro "tag_cond" : term => `(by simp [eval, Cond.holds, Asm.assign, Plan.tag])

/-! ### Rounding up -/

/--
The quotient by a byte's 8 bits, a node's 32 bytes or a node's 256 bits, rounded up, evaluates to the rounded-up quotient of the
operand's value, with no overflow.
-/
theorem eval_ceilDiv {w : World} {env : Env} {mem : Memory} {a : Expr} {x : UInt64} (ha : eval w env mem a = some x)
    (k : Nat) (hk : k = 8 ∨ k = 32 ∨ k = 256) :
    eval w env mem (ceilDiv a k) = some ((x.toNat + k - 1) / k).toUInt64 := by
  have kn : (k.toUInt64).toNat = k := addr_toNat (by omega)
  have nz : UInt64.ofNat k ≠ 0 := by
    intro h; have := congrArg UInt64.toNat h; simp at this; omega
  have shape : eval w env mem (ceilDiv a k) =
      some (x / k.toUInt64 + if x % k.toUInt64 = 0 then 0 else 1) := by
    simp only [ceilDiv, div_eq, add_eq, mod_eq, ne_eq', natCast_eq, ofNat_eq, eval_op', eval_div', eval_mod',
      eval_cmp', ha, eval_lit']
    by_cases r : x % k.toUInt64 = 0 <;> simp [r, Cond.holds, nz]
  rw [shape]
  congr 1
  apply UInt64.toNat_inj.mp
  have xs := x.toNat_lt
  have rn : (x % k.toUInt64).toNat = x.toNat % k := by rw [UInt64.toNat_mod, kn]
  -- The quotient by a literal is something the arithmetic decision procedure handles.
  by_cases r : x % k.toUInt64 = 0
  · have r0 : x.toNat % k = 0 := by rw [← rn, r]; rfl
    simp only [r, ite_true, UInt64.add_zero, UInt64.toNat_div, kn]
    rw [UInt64.toNat_ofNat_of_lt' (by rw [UInt64.size]; rcases hk with rfl | rfl | rfl <;> omega)]
    rcases hk with rfl | rfl | rfl <;> omega
  · have r1 : x.toNat % k ≠ 0 := by
      intro h; apply r; apply UInt64.toNat_inj.mp; rw [rn, h]; rfl
    simp only [r, ite_false, UInt64.toNat_add, UInt64.toNat_div, kn, UInt64.toNat_one]
    rw [UInt64.toNat_ofNat_of_lt' (by rw [UInt64.size]; rcases hk with rfl | rfl | rfl <;> omega)]
    rcases hk with rfl | rfl | rfl <;> omega

/-! ### Widths -/

section Steps
variable {m : Module} {w : World} {sp : Nat} {env env' : Env} {mem mem' : Memory}

/-- A guarded block with a nonzero condition runs its statements. -/
theorem Runs.when_true {c : Expr} {body : List Stmt} (v : UInt64) (hc : eval w env mem c = some v) (nz : v ≠ 0)
    (h : Runs m w sp env mem (.block body) env' mem') : Runs m w sp env mem (when c body) env' mem' :=
  Runs.ite_true v hc nz h

/-- A guarded block with a zero condition does nothing. -/
theorem Runs.when_false {c : Expr} {body : List Stmt} (hc : eval w env mem c = some 0) :
    Runs m w sp env mem (when c body) env mem :=
  Runs.ite_false hc (Runs.skip m w sp env mem)

end Steps

/-- The width function's frame holds eleven words. -/
theorem widthFrame : PlanWidth.fn.frame = 11 := by decide

/-- The loop over fields in the width function. -/
abbrev widthLoop : Stmt :=
  while_ (lt PlanWidth.i PlanWidth.n) [callInto PlanWidth.x "ssz_plan_fixed_width" [PlanWidth.q],
    PlanWidth.w ::= PlanWidth.w + PlanWidth.x, callInto PlanWidth.q "ssz_plan_next" [PlanWidth.q],
    PlanWidth.i ::= PlanWidth.i + 1]

/-- The functions the plan readers call, each under its name. -/
structure PlanFns (m : Module) : Prop where
  /-- The plan walk, and the rest of the codec. -/
  codec : HasCodec m
  /-- The width function. -/
  width : m.fns.lookup "ssz_plan_fixed_width" = some PlanWidth.fn
  /-- The fixed-size test. -/
  fixed : m.fns.lookup "ssz_plan_fixed" = some PlanFixed.fn
  /-- The plain test. -/
  plain : m.fns.lookup "ssz_plan_plain" = some PlanPlain.fn
  /-- The depth for a count of leaves. -/
  depth : m.fns.lookup "ssz_depth_for" = some DepthFor.fn
  /-- The saturated width. -/
  scratchWidth : m.fns.lookup "ssz_scratch_width" = some ScratchWidth.fn
  /-- The packed part of the scratch bound. -/
  scratchPacked : m.fns.lookup "ssz_scratch_packed" = some ScratchPacked.fn
  /-- The scratch bound of fixed-size roots. -/
  scratchRoots : m.fns.lookup "ssz_scratch_roots" = some ScratchRoots.fn
  /-- The scratch bound of a value's root. -/
  rootScratch : m.fns.lookup "ssz_root_scratch" = some RootScratch.fn

variable {m : Module} {w : World}

mutual

/-- The width function returns a well-formed type's width, wrapped to a word. -/
theorem planWidth_calls (hf : PlanFns m) (d : Desc) (a sp : Nat) (mem : Memory) (hw : WordsAt w mem a (Plan.words d))
    (hp : d.wellFormed = .ok ()) (thin : narrow d = true) (stack : w.stackLo + 112 * d.nesting ≤ sp) :
    Calls m w "ssz_plan_fixed_width" sp [a.toUInt64] mem (fixedWidth d).toUInt64 mem := by
  have one := nesting_pos d
  have room : w.stackLo + 8 + 8 * PlanWidth.fn.frame ≤ sp := by rw [widthFrame]; omega
  have inner : w.stackLo + 112 * (d.nesting - 1) ≤ sp - 8 - 8 * PlanWidth.fn.frame := by rw [widthFrame]; omega
  have tagRead := eval_tag (w := w) (env := entryEnv [a.toUInt64]) (mem := mem) (e := .var 0) hw
    (by simp [eval, entryEnv])
  have tag0 := Runs.set' (m := m) (sp := sp - 8 - 8 * PlanWidth.fn.frame) (x := 1) tagRead
  have w0 := Runs.set' (m := m) (w := w) (v := 0) (sp := sp - 8 - 8 * PlanWidth.fn.frame) (x := 2) (e := (0 : Expr))
    (env := Asm.assign (entryEnv [a.toUInt64]) 1 (Plan.tag d).toUInt64) (mem := mem) rfl
  cases d with
  | bool =>
    refine Calls.fn hf.width room rfl (Runs.block_cons tag0 (Runs.block_cons w0
      (Runs.ifElse_true 1 tag_cond (by decide) (Runs.set' rfl)))) ?_
    simp [PlanWidth.fn, eval, Asm.assign, fixedWidth]
  | uint n | byteVector n =>
    simp only [Plan.words] at hw
    refine Calls.fn hf.width room rfl (Runs.block_cons tag0 (Runs.block_cons w0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_true 1 tag_cond (by decide)
        (Runs.set' (eval_word hw 1 (by simp) (by simp [eval, Asm.assign, entryEnv]))))))) ?_
    simp [PlanWidth.fn, eval, Asm.assign, fixedWidth]
  | bitVector n =>
    simp only [Plan.words] at hw
    simp only [narrow, decide_eq_true_eq] at thin
    have hld : eval w (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1 (Plan.tag (.bitVector n)).toUInt64) 2 0) mem
        (.load .b8 (.op .add (.var 0) (.lit 8))) = some n.toUInt64 :=
      eval_word hw 1 (by simp) (by simp [eval, Asm.assign, entryEnv])
    refine Calls.fn hf.width room rfl (Runs.block_cons tag0 (Runs.block_cons w0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_false tag_cond (Runs.ifElse_true 1 tag_cond (by decide)
        (Runs.set' (eval_ceilDiv hld 8 (by simp)))))))) ?_
    simp only [PlanWidth.fn, eval, Asm.assign, fixedWidth]
    simp only [ite_true]
    congr 2
    rw [addr_toNat (by omega)]
    omega
  | byteList _ | bitList _ | progressiveBitList _ | list _ _ | progressiveList _ _ | compatibleUnion _ _ =>
    refine Calls.fn hf.width room rfl (Runs.block_cons tag0 (Runs.block_cons w0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond
        (Runs.when_false tag_cond))))))) ?_
    simp [PlanWidth.fn, eval, Asm.assign, fixedWidth]
  | vector e l =>
    simp only [Plan.words] at hw
    obtain ⟨hh, he⟩ := wordsAt_split hw
    replace hp := wellFormed_vector hp
    simp only [Desc.nesting] at inner
    simp only [narrow, Bool.and_eq_true] at thin
    have call := planWidth_calls hf e (a + 16) (sp - 8 - 8 * PlanWidth.fn.frame) mem (by simpa using he) hp thin.2
      (by omega)
    have hld : eval w (Asm.assign (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
        (Plan.tag (.vector e l)).toUInt64) 2 0) 2 (fixedWidth e).toUInt64) mem
        (.load .b8 (.op .add (.var 0) (.lit 8))) = some l.toUInt64 :=
      eval_word hh 1 (by simp) (by simp [eval, Asm.assign, entryEnv])
    refine Calls.fn hf.width room rfl (Runs.block_cons tag0 (Runs.block_cons w0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond (Runs.ifElse_true 1 tag_cond (by decide)
        (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, entryEnv]) call)
          (Runs.set' (by simp only [mul_eq, ld_eq, add_eq, ofNat_eq, eval_op', eval_var', hld]; rfl))))))))) ?_
    simp [PlanWidth.fn, eval, Asm.assign, fixedWidth]
  | container names fs =>
    simp only [Plan.words] at hw
    obtain ⟨hh, hfs⟩ := wordsAt_split hw
    replace hp := wellFormed_container hp
    simp only [Desc.nesting] at inner
    have hN : fs.length < 2 ^ 64 := fields_small hfs
    obtain ⟨env', run, h2'⟩ := planWidth_loop hf fs (a + 16) 0 fs.length (sp - 8 - 8 * PlanWidth.fn.frame) 0
      (Asm.assign (Asm.assign (Asm.assign (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
        (Plan.tag (.container names fs)).toUInt64) 2 0) 3 fs.length.toUInt64) 4 (a + 16).toUInt64) 6 0) mem
      (by simpa using hfs) hp (by simp only [narrow, Bool.and_eq_true] at thin; exact thin.2)
      (by simp [Asm.assign]) (by simp [Asm.assign]) (by simp [Asm.assign])
      (by simp [Asm.assign]) hN (by simp) (by omega)
    refine Calls.fn hf.width room rfl (Runs.block_cons tag0 (Runs.block_cons w0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond
        (Runs.when_true 1 tag_cond (by decide)
          (Runs.block_cons (Runs.ifElse_true 1 tag_cond (by decide)
            (Runs.block_cons (Runs.set' (eval_word hh 1 (by simp) (by simp [eval, Asm.assign, entryEnv])))
              (Runs.set' (by simp [eval, Asm.assign, entryEnv]))))
            (Runs.block_cons (Runs.set' rfl) run))))))))) ?_
    simp [PlanWidth.fn, eval, h2', fixedWidth]
  | progressiveContainer active names fs =>
    simp only [Plan.words] at hw
    obtain ⟨hpre, hfs⟩ := wordsAt_split hw
    obtain ⟨hpre, hn⟩ := wordsAt_split hpre
    obtain ⟨hh, _⟩ := wordsAt_split hpre
    replace hp := wellFormed_progressiveContainer hp
    simp only [Desc.nesting] at inner
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hn hfs
    have hN : fs.length < 2 ^ 64 := fields_small hfs
    rw [show a + 8 * (0 + 1 + 1 + active.length) = a + 16 + 8 * active.length by omega] at hn
    have hk : eval w (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
        (Plan.tag (.progressiveContainer active names fs)).toUInt64) 2 0) mem
        (.load .b8 (.op .add (.var 0) (.lit 8))) = some active.length.toUInt64 := by
      have := eval_word hh 1 (by simp) (e := .op .add (.var 0) (.lit 8))
        (env := Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
          (Plan.tag (.progressiveContainer active names fs)).toUInt64) 2 0) (mem := mem)
        (by simp [eval, Asm.assign, entryEnv])
      simpa using this
    have hq : eval w (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
        (Plan.tag (.progressiveContainer active names fs)).toUInt64) 2 0) mem
        (PlanWidth.p + 16 + 8 * ld (PlanWidth.p + 8)) = some (a + 16 + 8 * active.length).toUInt64 := by
      simp only [mul_eq, ld_eq, add_eq, ofNat_eq, eval_op', eval_var', hk, eval_lit']
      simp [Asm.assign, entryEnv]
    obtain ⟨env', run, h2'⟩ := planWidth_loop hf fs (a + 16 + 8 * active.length + 8) 0 fs.length
      (sp - 8 - 8 * PlanWidth.fn.frame) 0
      (Asm.assign (Asm.assign (Asm.assign (Asm.assign (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
        (Plan.tag (.progressiveContainer active names fs)).toUInt64) 2 0) 4 (a + 16 + 8 * active.length).toUInt64)
        3 fs.length.toUInt64) 4 (a + 16 + 8 * active.length + 8).toUInt64) 6 0) mem
      (by rw [show a + 16 + 8 * active.length + 8 = a + 8 * (0 + 1 + 1 + active.length + (0 + 1)) by omega]
          exact hfs) hp (by simp only [narrow, Bool.and_eq_true] at thin; exact thin.2)
      (by simp [Asm.assign]) (by simp [Asm.assign]) (by simp [Asm.assign])
      (by simp [Asm.assign]) hN (by simp) (by omega)
    refine Calls.fn hf.width room rfl (Runs.block_cons tag0 (Runs.block_cons w0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond
        (Runs.when_true 1 tag_cond (by decide)
          (Runs.block_cons (Runs.ifElse_false tag_cond
            (Runs.block_cons (Runs.set' hq)
              (Runs.block_cons (Runs.set' (eval_word hn 0 (by simp) (by simp [eval, Asm.assign])))
                (Runs.set' (by simp [eval, Asm.assign])))))
            (Runs.block_cons (Runs.set' rfl) run))))))))) ?_
    simp [PlanWidth.fn, eval, h2', fixedWidth]

/-- The loop over fields adds each field's width to the running width, wrapped to a word. -/
theorem planWidth_loop (hf : PlanFns m) (fs : List Desc) (a j N sp : Nat) (acc : UInt64) (env : Env)
    (mem : Memory) (hw : WordsAt w mem a (Plan.wordsAll fs)) (hp : Desc.allWellFormed fs = .ok ())
    (thin : narrowAll fs = true)
    (h4 : env 4 = a.toUInt64) (h6 : env 6 = j.toUInt64) (h3 : env 3 = N.toUInt64) (h2 : env 2 = acc)
    (hN : N < 2 ^ 64) (hj : j + fs.length = N) (stack : w.stackLo + 112 * Desc.deepestNesting fs ≤ sp) :
    ∃ env', Runs m w sp env mem widthLoop env' mem ∧ env' 2 = acc + (fieldsWidth fs).toUInt64 := by
  match fs with
  | [] =>
    refine ⟨env, Runs.loop_exit _ _ _ _ _ _ _ ?_, by simp [h2, fieldsWidth]⟩
    simp at hj
    simp [eval, Cond.holds, h6, h3, hj]
  | f :: rest =>
    simp only [Plan.wordsAll] at hw
    obtain ⟨hf1, hrest⟩ := wordsAt_split hw
    have hp := allWellFormed_cons hp
    simp only [Desc.deepestNesting] at stack
    have s1 : w.stackLo + 112 * f.nesting ≤ sp := by
      have := Nat.le_max_left f.nesting (Desc.deepestNesting rest); omega
    have s2 : w.stackLo + 112 * Desc.deepestNesting rest ≤ sp := by
      have := Nat.le_max_right f.nesting (Desc.deepestNesting rest); omega
    simp only [narrowAll, Bool.and_eq_true] at thin
    have width := planWidth_calls hf f a sp mem hf1 hp.1 thin.1 s1
    have skip := next_ok m w hf.codec f hp.1 sp mem a hf1 (by rw [walkLevel_eq]; omega)
    obtain ⟨env', run, h2'⟩ := planWidth_loop hf rest (a + 8 * (Plan.words f).length) (j + 1) N sp
      (acc + (fixedWidth f).toUInt64)
      (Asm.assign (Asm.assign (Asm.assign (Asm.assign env 5 (fixedWidth f).toUInt64) 2
        (acc + (fixedWidth f).toUInt64)) 4 (a + 8 * (Plan.words f).length).toUInt64) 6 (j.toUInt64 + 1)) mem
      hrest hp.2 thin.2 (by simp [Asm.assign]) (by simp [Asm.assign]) (by simp [Asm.assign, h3]) (by simp [Asm.assign])
      hN (by simp at hj; omega) s2
    refine ⟨env', Runs.loop_step 1 ?_ (by decide)
      (Runs.block_cons (Runs.call (by simp [eval, h4]) width)
        (Runs.block_cons (Runs.set' (by simp [eval, Asm.assign, h2]))
          (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, h4]) skip)
            (Runs.set' (by simp [eval, Asm.assign, h6]))))) run, ?_⟩
    · -- One more field remains, so the count is still below the total.
      simp at hj
      have lt : j.toUInt64 < N.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, addr_toNat (by omega), addr_toNat hN]; omega
      simp [eval, Cond.holds, h6, h3, lt]
    · rw [h2']; simp [fieldsWidth, UInt64.add_assoc]

end

/-! ### Fixed-size and plain tests -/

/-- A truth value as the word the tests return. -/
def bitOf (b : Bool) : UInt64 := if b then 1 else 0

/-- Two answers combined by a bitwise and are the answer to both. -/
theorem bitOf_and (a b : Bool) : (bitOf a &&& bitOf b) = bitOf (a && b) := by
  cases a <;> cases b <;> decide

/-- The fixed-size test's frame holds eleven words. -/
theorem fixedFrame : PlanFixed.fn.frame = 11 := by decide

/-- The loop over fields in the fixed-size test. -/
abbrev fixedLoop : Stmt :=
  while_ (lt PlanFixed.i PlanFixed.n) [callInto PlanFixed.x "ssz_plan_fixed" [PlanFixed.q],
    PlanFixed.r ::= PlanFixed.r &&& PlanFixed.x, callInto PlanFixed.q "ssz_plan_next" [PlanFixed.q],
    PlanFixed.i ::= PlanFixed.i + 1]

mutual

/-- The fixed-size test answers whether a well-formed type has a fixed size. -/
theorem planFixed_calls (hf : PlanFns m) (d : Desc) (a sp : Nat) (mem : Memory) (hw : WordsAt w mem a (Plan.words d))
    (hp : d.wellFormed = .ok ()) (stack : w.stackLo + 112 * d.nesting ≤ sp) :
    Calls m w "ssz_plan_fixed" sp [a.toUInt64] mem (bitOf (hasWidth d)) mem := by
  have one := nesting_pos d
  have room : w.stackLo + 8 + 8 * PlanFixed.fn.frame ≤ sp := by rw [fixedFrame]; omega
  have inner : w.stackLo + 112 * (d.nesting - 1) ≤ sp - 8 - 8 * PlanFixed.fn.frame := by rw [fixedFrame]; omega
  have tagRead := eval_tag (w := w) (env := entryEnv [a.toUInt64]) (mem := mem) (e := .var 0) hw
    (by simp [eval, entryEnv])
  have tag0 := Runs.set' (m := m) (sp := sp - 8 - 8 * PlanFixed.fn.frame) (x := 1) tagRead
  have r0 := Runs.set' (m := m) (w := w) (v := 0) (sp := sp - 8 - 8 * PlanFixed.fn.frame) (x := 2) (e := (0 : Expr))
    (env := Asm.assign (entryEnv [a.toUInt64]) 1 (Plan.tag d).toUInt64) (mem := mem) rfl
  cases d with
  | bool | uint _ | byteVector _ | bitVector _ =>
    refine Calls.fn hf.fixed room rfl (Runs.block_cons tag0 (Runs.block_cons r0
      (Runs.ifElse_true 1 tag_cond (by decide) (Runs.set' rfl)))) ?_
    simp [PlanFixed.fn, eval, Asm.assign, hasWidth, bitOf]
  | byteList _ | bitList _ | progressiveBitList _ | list _ _ | progressiveList _ _ | compatibleUnion _ _ =>
    refine Calls.fn hf.fixed room rfl (Runs.block_cons tag0 (Runs.block_cons r0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_false tag_cond (Runs.when_false tag_cond))))) ?_
    simp [PlanFixed.fn, eval, Asm.assign, hasWidth, bitOf]
  | vector e l =>
    simp only [Plan.words] at hw
    obtain ⟨_, he⟩ := wordsAt_split hw
    replace hp := wellFormed_vector hp
    simp only [Desc.nesting] at inner
    have call := planFixed_calls hf e (a + 16) (sp - 8 - 8 * PlanFixed.fn.frame) mem (by simpa using he) hp
      (by omega)
    refine Calls.fn hf.fixed room rfl (Runs.block_cons tag0 (Runs.block_cons r0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_true 1 tag_cond (by decide) (Runs.call (by simp [eval, Asm.assign, entryEnv]) call))))) ?_
    simp [PlanFixed.fn, eval, Asm.assign, hasWidth]
  | container names fs =>
    simp only [Plan.words] at hw
    obtain ⟨hh, hfs⟩ := wordsAt_split hw
    replace hp := wellFormed_container hp
    simp only [Desc.nesting] at inner
    have hN : fs.length < 2 ^ 64 := fields_small hfs
    obtain ⟨env', run, h2'⟩ := planFixed_loop hf fs (a + 16) 0 fs.length (sp - 8 - 8 * PlanFixed.fn.frame) true
      (Asm.assign (Asm.assign (Asm.assign (Asm.assign (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
        (Plan.tag (.container names fs)).toUInt64) 2 0) 3 fs.length.toUInt64) 4 (a + 16).toUInt64) 2 1) 6 0) mem
      (by simpa using hfs) hp (by simp [Asm.assign]) (by simp [Asm.assign]) (by simp [Asm.assign])
      (by simp [Asm.assign, bitOf]) hN (by simp) (by omega)
    refine Calls.fn hf.fixed room rfl (Runs.block_cons tag0 (Runs.block_cons r0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_false tag_cond (Runs.when_true 1 tag_cond (by decide)
          (Runs.block_cons (Runs.ifElse_true 1 tag_cond (by decide)
            (Runs.block_cons (Runs.set' (eval_word hh 1 (by simp) (by simp [eval, Asm.assign, entryEnv])))
              (Runs.set' (by simp [eval, Asm.assign, entryEnv]))))
            (Runs.block_cons (Runs.set' rfl) (Runs.block_cons (Runs.set' rfl) run)))))))) ?_
    simp [PlanFixed.fn, eval, h2', hasWidth]
  | progressiveContainer active names fs =>
    simp only [Plan.words] at hw
    obtain ⟨hpre, hfs⟩ := wordsAt_split hw
    obtain ⟨hpre, hn⟩ := wordsAt_split hpre
    obtain ⟨hh, _⟩ := wordsAt_split hpre
    replace hp := wellFormed_progressiveContainer hp
    simp only [Desc.nesting] at inner
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hn hfs
    have hN : fs.length < 2 ^ 64 := fields_small hfs
    rw [show a + 8 * (0 + 1 + 1 + active.length) = a + 16 + 8 * active.length by omega] at hn
    have hk : eval w (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
        (Plan.tag (.progressiveContainer active names fs)).toUInt64) 2 0) mem
        (.load .b8 (.op .add (.var 0) (.lit 8))) = some active.length.toUInt64 := by
      have := eval_word hh 1 (by simp) (e := .op .add (.var 0) (.lit 8))
        (env := Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
          (Plan.tag (.progressiveContainer active names fs)).toUInt64) 2 0) (mem := mem)
        (by simp [eval, Asm.assign, entryEnv])
      simpa using this
    have hq : eval w (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
        (Plan.tag (.progressiveContainer active names fs)).toUInt64) 2 0) mem
        (PlanFixed.p + 16 + 8 * ld (PlanFixed.p + 8)) = some (a + 16 + 8 * active.length).toUInt64 := by
      simp only [mul_eq, ld_eq, add_eq, ofNat_eq, eval_op', eval_var', hk, eval_lit']
      simp [Asm.assign, entryEnv]
    obtain ⟨env', run, h2'⟩ := planFixed_loop hf fs (a + 16 + 8 * active.length + 8) 0 fs.length
      (sp - 8 - 8 * PlanFixed.fn.frame) true
      (Asm.assign (Asm.assign (Asm.assign (Asm.assign (Asm.assign (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
        (Plan.tag (.progressiveContainer active names fs)).toUInt64) 2 0) 4 (a + 16 + 8 * active.length).toUInt64)
        3 fs.length.toUInt64) 4 (a + 16 + 8 * active.length + 8).toUInt64) 2 1) 6 0) mem
      (by rw [show a + 16 + 8 * active.length + 8 = a + 8 * (0 + 1 + 1 + active.length + (0 + 1)) by omega]
          exact hfs) hp (by simp [Asm.assign]) (by simp [Asm.assign]) (by simp [Asm.assign])
      (by simp [Asm.assign, bitOf]) hN (by simp) (by omega)
    refine Calls.fn hf.fixed room rfl (Runs.block_cons tag0 (Runs.block_cons r0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_false tag_cond (Runs.when_true 1 tag_cond (by decide)
          (Runs.block_cons (Runs.ifElse_false tag_cond
            (Runs.block_cons (Runs.set' hq)
              (Runs.block_cons (Runs.set' (eval_word hn 0 (by simp) (by simp [eval, Asm.assign])))
                (Runs.set' (by simp [eval, Asm.assign])))))
            (Runs.block_cons (Runs.set' rfl) (Runs.block_cons (Runs.set' rfl) run)))))))) ?_
    simp [PlanFixed.fn, eval, h2', hasWidth]

/-- The loop over fields keeps one only while every field so far has a fixed size. -/
theorem planFixed_loop (hf : PlanFns m) (fs : List Desc) (a j N sp : Nat) (acc : Bool) (env : Env)
    (mem : Memory) (hw : WordsAt w mem a (Plan.wordsAll fs)) (hp : Desc.allWellFormed fs = .ok ())
    (h4 : env 4 = a.toUInt64) (h6 : env 6 = j.toUInt64) (h3 : env 3 = N.toUInt64) (h2 : env 2 = bitOf acc)
    (hN : N < 2 ^ 64) (hj : j + fs.length = N) (stack : w.stackLo + 112 * Desc.deepestNesting fs ≤ sp) :
    ∃ env', Runs m w sp env mem fixedLoop env' mem ∧ env' 2 = bitOf (acc && allHaveWidth fs) := by
  match fs with
  | [] =>
    refine ⟨env, Runs.loop_exit _ _ _ _ _ _ _ ?_, by simp [h2, allHaveWidth]⟩
    simp at hj
    simp [eval, Cond.holds, h6, h3, hj]
  | f :: rest =>
    simp only [Plan.wordsAll] at hw
    obtain ⟨hf1, hrest⟩ := wordsAt_split hw
    have hp := allWellFormed_cons hp
    simp only [Desc.deepestNesting] at stack
    have s1 : w.stackLo + 112 * f.nesting ≤ sp := by
      have := Nat.le_max_left f.nesting (Desc.deepestNesting rest); omega
    have s2 : w.stackLo + 112 * Desc.deepestNesting rest ≤ sp := by
      have := Nat.le_max_right f.nesting (Desc.deepestNesting rest); omega
    have fixed := planFixed_calls hf f a sp mem hf1 hp.1 s1
    have skip := next_ok m w hf.codec f hp.1 sp mem a hf1 (by rw [walkLevel_eq]; omega)
    obtain ⟨env', run, h2'⟩ := planFixed_loop hf rest (a + 8 * (Plan.words f).length) (j + 1) N sp
      (acc && hasWidth f)
      (Asm.assign (Asm.assign (Asm.assign (Asm.assign env 5 (bitOf (hasWidth f))) 2
        (bitOf (acc && hasWidth f))) 4 (a + 8 * (Plan.words f).length).toUInt64) 6 (j.toUInt64 + 1)) mem
      hrest hp.2 (by simp [Asm.assign]) (by simp [Asm.assign]) (by simp [Asm.assign, h3]) (by simp [Asm.assign])
      hN (by simp at hj; omega) s2
    refine ⟨env', Runs.loop_step 1 ?_ (by decide)
      (Runs.block_cons (Runs.call (by simp [eval, h4]) fixed)
        (Runs.block_cons (Runs.set' (by simp [eval, Asm.assign, h2, bitOf_and]))
          (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, h4]) skip)
            (Runs.set' (by simp [eval, Asm.assign, h6]))))) run, ?_⟩
    · -- One more field remains, so the count is still below the total.
      simp at hj
      have lt : j.toUInt64 < N.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, addr_toNat (by omega), addr_toNat hN]; omega
      simp [eval, Cond.holds, h6, h3, lt]
    · rw [h2']; simp [allHaveWidth, Bool.and_assoc]

end

/-- The plain test's frame holds nine words. -/
theorem plainFrame : PlanPlain.fn.frame = 9 := by decide

/-- The loop over fields in the plain test. -/
abbrev plainLoop : Stmt :=
  while_ (lt PlanPlain.i PlanPlain.n) [callInto PlanPlain.x "ssz_plan_plain" [PlanPlain.q],
    PlanPlain.r ::= PlanPlain.r &&& PlanPlain.x, callInto PlanPlain.q "ssz_plan_next" [PlanPlain.q],
    PlanPlain.i ::= PlanPlain.i + 1]

mutual

/-- The plain test answers whether a well-formed type is plain. -/
theorem planPlain_calls (hf : PlanFns m) (d : Desc) (a sp : Nat) (mem : Memory) (hw : WordsAt w mem a (Plan.words d))
    (hp : d.wellFormed = .ok ()) (stack : w.stackLo + 112 * d.nesting ≤ sp) :
    Calls m w "ssz_plan_plain" sp [a.toUInt64] mem (bitOf (plain d)) mem := by
  have one := nesting_pos d
  have room : w.stackLo + 8 + 8 * PlanPlain.fn.frame ≤ sp := by rw [plainFrame]; omega
  have inner : w.stackLo + 112 * (d.nesting - 1) ≤ sp - 8 - 8 * PlanPlain.fn.frame := by rw [plainFrame]; omega
  have tagRead := eval_tag (w := w) (env := entryEnv [a.toUInt64]) (mem := mem) (e := .var 0) hw
    (by simp [eval, entryEnv])
  have tag0 := Runs.set' (m := m) (sp := sp - 8 - 8 * PlanPlain.fn.frame) (x := 1) tagRead
  have r0 := Runs.set' (m := m) (w := w) (v := 0) (sp := sp - 8 - 8 * PlanPlain.fn.frame) (x := 2) (e := (0 : Expr))
    (env := Asm.assign (entryEnv [a.toUInt64]) 1 (Plan.tag d).toUInt64) (mem := mem) rfl
  cases d with
  | bool | uint _ | byteVector _ | bitVector _ =>
    refine Calls.fn hf.plain room rfl (Runs.block_cons tag0 (Runs.block_cons r0
      (Runs.ifElse_true 1 tag_cond (by decide) (Runs.set' rfl)))) ?_
    simp [PlanPlain.fn, eval, Asm.assign, plain, bitOf]
  | byteList _ | bitList _ | progressiveBitList _ | list _ _ | progressiveList _ _ | compatibleUnion _ _
  | progressiveContainer _ _ _ =>
    refine Calls.fn hf.plain room rfl (Runs.block_cons tag0 (Runs.block_cons r0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_false tag_cond (Runs.when_false tag_cond))))) ?_
    simp [PlanPlain.fn, eval, Asm.assign, plain, bitOf]
  | vector e l =>
    simp only [Plan.words] at hw
    obtain ⟨_, he⟩ := wordsAt_split hw
    replace hp := wellFormed_vector hp
    simp only [Desc.nesting] at inner
    have call := planPlain_calls hf e (a + 16) (sp - 8 - 8 * PlanPlain.fn.frame) mem (by simpa using he) hp
      (by omega)
    refine Calls.fn hf.plain room rfl (Runs.block_cons tag0 (Runs.block_cons r0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_true 1 tag_cond (by decide) (Runs.call (by simp [eval, Asm.assign, entryEnv]) call))))) ?_
    simp [PlanPlain.fn, eval, Asm.assign, plain]
  | container names fs =>
    simp only [Plan.words] at hw
    obtain ⟨hh, hfs⟩ := wordsAt_split hw
    replace hp := wellFormed_container hp
    simp only [Desc.nesting] at inner
    have hN : fs.length < 2 ^ 64 := fields_small hfs
    obtain ⟨env', run, h2'⟩ := planPlain_loop hf fs (a + 16) 0 fs.length (sp - 8 - 8 * PlanPlain.fn.frame) true
      (Asm.assign (Asm.assign (Asm.assign (Asm.assign (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
        (Plan.tag (.container names fs)).toUInt64) 2 0) 3 fs.length.toUInt64) 4 (a + 16).toUInt64) 2 1) 6 0) mem
      (by simpa using hfs) hp (by simp [Asm.assign]) (by simp [Asm.assign]) (by simp [Asm.assign])
      (by simp [Asm.assign, bitOf]) hN (by simp) (by omega)
    refine Calls.fn hf.plain room rfl (Runs.block_cons tag0 (Runs.block_cons r0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_false tag_cond (Runs.when_true 1 tag_cond (by decide)
        (Runs.block_cons (Runs.set' (eval_word hh 1 (by simp) (by simp [eval, Asm.assign, entryEnv])))
          (Runs.block_cons (Runs.set' (by simp [eval, Asm.assign, entryEnv]))
            (Runs.block_cons (Runs.set' rfl) (Runs.block_cons (Runs.set' rfl) run))))))))) ?_
    simp [PlanPlain.fn, eval, h2', plain]

/-- The loop over fields keeps one only while every field so far is plain. -/
theorem planPlain_loop (hf : PlanFns m) (fs : List Desc) (a j N sp : Nat) (acc : Bool) (env : Env)
    (mem : Memory) (hw : WordsAt w mem a (Plan.wordsAll fs)) (hp : Desc.allWellFormed fs = .ok ())
    (h4 : env 4 = a.toUInt64) (h6 : env 6 = j.toUInt64) (h3 : env 3 = N.toUInt64) (h2 : env 2 = bitOf acc)
    (hN : N < 2 ^ 64) (hj : j + fs.length = N) (stack : w.stackLo + 112 * Desc.deepestNesting fs ≤ sp) :
    ∃ env', Runs m w sp env mem plainLoop env' mem ∧ env' 2 = bitOf (acc && plainAll fs) := by
  match fs with
  | [] =>
    refine ⟨env, Runs.loop_exit _ _ _ _ _ _ _ ?_, by simp [h2, plainAll]⟩
    simp at hj
    simp [eval, Cond.holds, h6, h3, hj]
  | f :: rest =>
    simp only [Plan.wordsAll] at hw
    obtain ⟨hf1, hrest⟩ := wordsAt_split hw
    have hp := allWellFormed_cons hp
    simp only [Desc.deepestNesting] at stack
    have s1 : w.stackLo + 112 * f.nesting ≤ sp := by
      have := Nat.le_max_left f.nesting (Desc.deepestNesting rest); omega
    have s2 : w.stackLo + 112 * Desc.deepestNesting rest ≤ sp := by
      have := Nat.le_max_right f.nesting (Desc.deepestNesting rest); omega
    have test := planPlain_calls hf f a sp mem hf1 hp.1 s1
    have skip := next_ok m w hf.codec f hp.1 sp mem a hf1 (by rw [walkLevel_eq]; omega)
    obtain ⟨env', run, h2'⟩ := planPlain_loop hf rest (a + 8 * (Plan.words f).length) (j + 1) N sp
      (acc && plain f)
      (Asm.assign (Asm.assign (Asm.assign (Asm.assign env 5 (bitOf (plain f))) 2
        (bitOf (acc && plain f))) 4 (a + 8 * (Plan.words f).length).toUInt64) 6 (j.toUInt64 + 1)) mem
      hrest hp.2 (by simp [Asm.assign]) (by simp [Asm.assign]) (by simp [Asm.assign, h3]) (by simp [Asm.assign])
      hN (by simp at hj; omega) s2
    refine ⟨env', Runs.loop_step 1 ?_ (by decide)
      (Runs.block_cons (Runs.call (by simp [eval, h4]) test)
        (Runs.block_cons (Runs.set' (by simp [eval, Asm.assign, h2, bitOf_and]))
          (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, h4]) skip)
            (Runs.set' (by simp [eval, Asm.assign, h6]))))) run, ?_⟩
    · -- One more field remains, so the count is still below the total.
      simp at hj
      have lt : j.toUInt64 < N.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, addr_toNat (by omega), addr_toNat hN]; omega
      simp [eval, Cond.holds, h6, h3, lt]
    · rw [h2']; simp [plainAll, Bool.and_assoc]

end

/-! ### Saturating arithmetic -/

/-- A saturated number is at most the cap. -/
theorem sat_le (x : Nat) : sat x ≤ scratchCap := Nat.min_le_right _ _

/-- A saturated sum is at most the cap. -/
theorem sadd_le (x y : Nat) : sadd x y ≤ scratchCap := sat_le _

/-- A saturated product is at most the cap. -/
theorem smul_le (x y : Nat) : smul x y ≤ scratchCap := sat_le _

/-- The tree need is at most the cap. -/
theorem treeNeed_le (n : Nat) : treeNeed n ≤ scratchCap := sadd_le _ _

/-- Assigning a variable twice keeps the second value. -/
theorem assign_assign {f : Env} {x : Nat} {a b : UInt64} : Asm.assign (Asm.assign f x a) x b = Asm.assign f x b := by
  funext y; simp only [Asm.assign]; split <;> rfl

/-- Assigning a variable the value it holds changes nothing. -/
theorem assign_self {f : Env} {x : Nat} {a : UInt64} (h : f x = a) : Asm.assign f x a = f := by
  funext y; simp only [Asm.assign]; split <;> simp_all

section Steps
variable {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory}

/-- Two numbers below the word size compare as words the way they compare as numbers. -/
theorem toUInt64_lt {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) : x.toUInt64 < y.toUInt64 ↔ x < y := by
  rw [UInt64.lt_iff_toNat_lt, addr_toNat hx, addr_toNat hy]

/-- Saturating a variable in place. -/
theorem satIn_runs (r : Var) {x : Nat} (h : env r.idx = x.toUInt64) (hx : x < 2 ^ 64) :
    Runs m w sp env mem (satIn r) (Asm.assign env r.idx (sat x).toUInt64) mem := by
  have capv : scratchCap = 2 ^ 62 := rfl
  by_cases c : scratchCap < x
  · have hs : sat x = scratchCap := by simp only [sat]; omega
    rw [hs]
    exact Runs.ite_true 1 (by simp [eval, Cond.holds, h, (toUInt64_lt (by decide) hx).mpr c]) (by decide)
      (Runs.set' (by simp [eval]))
  · have hs : sat x = x := by simp only [sat]; omega
    rw [hs, assign_self h]
    refine Runs.ite_false ?_ (Runs.skip _ _ _ _ _)
    have : ¬ (scratchCap : Nat).toUInt64 < x.toUInt64 := fun l => c ((toUInt64_lt (by decide) hx).mp l)
    simp [eval, Cond.holds, h, this]

/-- A saturated sum into a variable. -/
theorem saddIn_runs (r : Var) {a b : Expr} {x y : Nat} (ha : eval w env mem a = some x.toUInt64)
    (hb : eval w env mem b = some y.toUInt64) (hx : x ≤ scratchCap) (hy : y ≤ scratchCap) :
    Runs m w sp env mem (.block (saddIn r a b)) (Asm.assign env r.idx (sadd x y).toUInt64) mem := by
  have capv : scratchCap = 2 ^ 62 := rfl
  have step := Runs.set' (m := m) (w := w) (env := env) (mem := mem) (sp := sp) (x := r.idx) (e := a + b) (v := (x + y).toUInt64)
    (by simp only [add_eq, eval_op', ha, hb]; simp)
  have sat := satIn_runs (m := m) (w := w) (sp := sp) (mem := mem) r
    (env := Asm.assign env r.idx (x + y).toUInt64) (x := x + y) (by simp [Asm.assign]) (by omega)
  rw [assign_assign] at sat
  exact Runs.block_cons step sat

/-- A saturated product into a variable. -/
theorem smulIn_runs (r : Var) {a b : Expr} {x y : Nat} (ha : eval w env mem a = some x.toUInt64)
    (hb : eval w env mem b = some y.toUInt64) (hx : x ≤ scratchCap) (hy : y ≤ scratchCap) :
    Runs m w sp env mem (smulIn r a b) (Asm.assign env r.idx (smul x y).toUInt64) mem := by
  have capv : scratchCap = 2 ^ 62 := rfl
  have xs : x < 2 ^ 64 := by omega
  have ys : y < 2 ^ 64 := by omega
  by_cases z : x = 0
  · subst z
    have : smul 0 y = 0 := by simp [smul, sat]
    rw [this]
    exact Runs.ite_true 1 (by simp [eval, Cond.holds, ha]) (by decide) (Runs.set' (by simp [eval]))
  · have xnz : x.toUInt64 ≠ 0 := by
      intro h; have := congrArg UInt64.toNat h; rw [addr_toNat xs] at this; simp at this; omega
    have quot : (scratchCap : Nat).toUInt64 / x.toUInt64 = (scratchCap / x).toUInt64 := by
      apply UInt64.toNat_inj.mp
      have dl := Nat.div_le_self scratchCap x
      rw [UInt64.toNat_div, addr_toNat (by decide), addr_toNat xs, addr_toNat (by omega)]
    refine Runs.ite_false (by simp [eval, Cond.holds, ha, xnz]) ?_
    by_cases big : scratchCap / x < y
    · -- The product passes the cap.
      have over : scratchCap < x * y := by
        have := Nat.lt_mul_div_succ scratchCap (Nat.pos_of_ne_zero z)
        have : x * (scratchCap / x + 1) ≤ x * y := Nat.mul_le_mul_left _ big
        omega
      have hs : smul x y = scratchCap := by simp only [smul, sat]; omega
      rw [hs]
      have dl := Nat.div_le_self scratchCap x
      have lt : (scratchCap / x).toUInt64 < y.toUInt64 := (toUInt64_lt (by omega) ys).mpr big
      exact Runs.ite_true 1 (by simp [eval, Cond.holds, ha, hb, xnz, quot, lt])
        (by decide) (Runs.set' (by simp [eval]))
    · -- The product stays under the cap.
      have under : x * y ≤ scratchCap := by
        have := (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero z)).mp (Nat.le_of_not_lt big)
        rw [Nat.mul_comm]; exact this
      have hs : smul x y = x * y := by simp only [smul, sat]; omega
      rw [hs]
      have dl := Nat.div_le_self scratchCap x
      have nlt : ¬ (scratchCap / x).toUInt64 < y.toUInt64 := fun l => big ((toUInt64_lt (by omega) ys).mp l)
      exact Runs.ite_false (by simp [eval, Cond.holds, ha, hb, xnz, quot, nlt])
        (Runs.set' (by simp only [mul_eq, eval_op', ha, hb]; simp))

/-- The larger of two values into a variable. -/
theorem maxIn_runs (r : Var) {a b : Expr} {x y : Nat} (ha : eval w env mem a = some x.toUInt64)
    (hb : eval w env mem b = some y.toUInt64) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    Runs m w sp env mem (maxIn r a b) (Asm.assign env r.idx (max x y).toUInt64) mem := by
  have capv : scratchCap = 2 ^ 62 := rfl
  by_cases c : x < y
  · rw [Nat.max_eq_right (by omega)]
    exact Runs.ite_true 1 (by simp [eval, Cond.holds, ha, hb, (toUInt64_lt hx hy).mpr c]) (by decide)
      (Runs.set' hb)
  · rw [Nat.max_eq_left (by omega)]
    have : ¬ x.toUInt64 < y.toUInt64 := fun l => c ((toUInt64_lt hx hy).mp l)
    exact Runs.ite_false (by simp [eval, Cond.holds, ha, hb, this]) (Runs.set' ha)

/-- The tree need over a count of nodes into a variable. -/
theorem treeIn_runs (r : Var) {a : Expr} {n : Nat} (ha : eval w env mem a = some n.toUInt64) (hn : n ≤ scratchCap) :
    Runs m w sp env mem (.block (treeIn r a)) (Asm.assign env r.idx (treeNeed n).toUInt64) mem := by
  have capv : scratchCap = 2 ^ 62 := rfl
  have first := smulIn_runs (m := m) (sp := sp) r (a := (32 : Expr)) (x := 32) (by simp [eval]) ha (by decide) hn
  have second := saddIn_runs (m := m) (w := w) (sp := sp) (mem := mem) r
    (env := Asm.assign env r.idx (smul 32 n).toUInt64)
    (a := ((RootProgressive.spineBytes + 32 * zeroHeights : Nat) : Expr)) (b := (r : Expr))
    (x := RootProgressive.spineBytes + 32 * zeroHeights) (y := smul 32 n) (by simp [eval]) (by simp [eval, Asm.assign])
    (by decide) (smul_le _ _)
  rw [assign_assign] at second
  exact Runs.block_cons first second

end Steps

/-! ### The packed bound -/

/-- The nodes for a width at most the cap need a tree of depth at most 57. -/
theorem depth_small {width : Nat} (h : width ≤ scratchCap) : depthFor (nodesFor width) ≤ 57 :=
  depthFor_le_of_le_two_pow (by simp only [nodesFor]; simp only [scratchCap] at h; omega)

/-- The doubling loop of the packed bound, from a power reached so far, ends at two to the depth. -/
theorem doubling_runs {m : Module} {w : World} {sp : Nat} {mem : Memory} (D : Nat) (hD : D ≤ 57) :
    ∀ k j (env : Env), j + k = D → env 2 = D.toUInt64 → env 4 = (2 ^ j).toUInt64 → env 5 = j.toUInt64 →
    ∃ env', Runs m w sp env mem (while_ (lt ScratchPacked.i ScratchPacked.depth)
        [ScratchPacked.pw ::= ScratchPacked.pw + ScratchPacked.pw, ScratchPacked.i ::= ScratchPacked.i + 1])
        env' mem ∧
      env' 4 = (2 ^ D).toUInt64 ∧ ∀ v, v ≠ 4 → v ≠ 5 → env' v = env v := by
  intro k
  induction k with
  | zero =>
    intro j env hj h2 h4 h5
    simp only [Nat.add_zero] at hj
    subst hj
    refine ⟨env, Runs.loop_exit _ _ _ _ _ _ _ ?_, h4, fun _ _ _ => rfl⟩
    simp [eval, Cond.holds, h2, h5]
  | succ k ih =>
    intro j env hj h2 h4 h5
    have pj : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by rw [Nat.pow_succ]; omega
    obtain ⟨env', run, e4, frame⟩ := ih (j + 1)
      (Asm.assign (Asm.assign env 4 (2 ^ (j + 1)).toUInt64) 5 (j + 1).toUInt64) (by omega)
      (by simp [Asm.assign, h2]) (by simp [Asm.assign]) (by simp [Asm.assign])
    refine ⟨env', Runs.loop_step 1 ?_ (by decide)
      (Runs.block_cons (Runs.set' (by simp [eval, h4, ← pj]))
        (Runs.set' (by simp [eval, Asm.assign, h5]))) run, e4, fun v a b => ?_⟩
    · have lt : j.toUInt64 < D.toUInt64 := (toUInt64_lt (by omega) (by omega)).mpr (by omega)
      simp [eval, Cond.holds, h2, h5, lt]
    · rw [frame v a b]; simp [Asm.assign, a, b]

/-- The packed bound's function computes the packed bound, for a width and a count at most the cap. -/
theorem scratchPacked_calls {m : Module} {w : World} (hd : m.fns.lookup "ssz_depth_for" = some DepthFor.fn)
    (hf : m.fns.lookup "ssz_scratch_packed" = some ScratchPacked.fn) (width count sp : Nat) (mem : Memory)
    (hw : width ≤ scratchCap) (hc : count ≤ scratchCap) (stack : w.stackLo + 256 ≤ sp) :
    Calls m w "ssz_scratch_packed" sp [width.toUInt64, count.toUInt64] mem (packedNeed width count).toUInt64 mem := by
  have capv : scratchCap = 2 ^ 62 := rfl
  have frame : ScratchPacked.fn.frame = 11 := by decide
  have dframe : DepthFor.fn.frame = 5 := by decide
  have room : w.stackLo + 8 + 8 * ScratchPacked.fn.frame ≤ sp := by rw [frame]; omega
  let inner := sp - 8 - 8 * ScratchPacked.fn.frame
  have nodes : ((width.toUInt64).toNat + 32 - 1) / 32 = nodesFor width := by
    rw [addr_toNat (by omega)]; rfl
  have nodesSmall : nodesFor width < 2 ^ 64 := by simp only [nodesFor]; omega
  have depth := depthFor_calls (w := w) hd (sp := inner) (by rw [dframe]; simp only [inner, frame]; omega)
    (nodesFor width).toUInt64 mem
  rw [addr_toNat nodesSmall] at depth
  have dsmall := depth_small hw
  let D := depthFor (nodesFor width)
  -- The depth, then the roots' bytes.
  have s1 := Runs.call (m := m) (sp := inner) (env := entryEnv [width.toUInt64, count.toUInt64]) (dst := 2)
    (args := [ceilDiv ScratchPacked.width 32]) (values := [(nodesFor width).toUInt64])
    (by simp only [List.mapM_cons, List.mapM_nil]
        rw [eval_ceilDiv (x := width.toUInt64) (by simp [eval, entryEnv]) 32 (by simp), nodes]; rfl) depth
  have s2 := smulIn_runs (m := m) (w := w) (sp := inner) (mem := mem) ScratchPacked.r
    (env := Asm.assign (entryEnv [width.toUInt64, count.toUInt64]) 2 D.toUInt64) (a := (32 : Expr))
    (b := (ScratchPacked.count : Expr)) (x := 32) (y := count) (by simp [eval]) (by simp [eval, Asm.assign, entryEnv])
    (by decide) hc
  by_cases zero : D = 0
  · -- One node per value: the roots are the whole need.
    refine Calls.fn hf room rfl (Runs.block_cons s1 (Runs.block_cons s2
      (Runs.when_false (by simp [eval, Cond.holds, Asm.assign, zero])))) ?_
    simp [ScratchPacked.fn, eval, Asm.assign, packedNeed, D] at zero ⊢
    simp [zero]
  · -- Blocks of two to the depth nodes, hashed down level by level.
    let E2 := Asm.assign (Asm.assign (entryEnv [width.toUInt64, count.toUInt64]) 2 D.toUInt64) 3
      (smul 32 count).toUInt64
    let E4 := Asm.assign (Asm.assign E2 4 1) 5 0
    obtain ⟨E5, loop, e4, keep⟩ := doubling_runs (m := m) (w := w) (sp := inner) (mem := mem) D dsmall D 0 E4
      (by omega) (by simp [E4, E2, Asm.assign]) (by simp [E4, Asm.assign]) (by simp [E4, Asm.assign])
    have k1 : E5 1 = count.toUInt64 := by rw [keep 1 (by decide) (by decide)]; simp [E4, E2, Asm.assign, entryEnv]
    have k3 : E5 3 = (smul 32 count).toUInt64 := by rw [keep 3 (by decide) (by decide)]; simp [E4, E2, Asm.assign]
    have pw : 2 ^ D ≤ scratchCap := by
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) dsmall; simp only [D]; omega
    have t1 := smulIn_runs (m := m) (w := w) (sp := inner) (mem := mem) ScratchPacked.t (env := E5)
      (a := (32 : Expr)) (b := (ScratchPacked.pw : Expr)) (x := 32) (y := 2 ^ D) (by simp [eval]) (by simp [eval, e4])
      (by decide) pw
    have t2 := smulIn_runs (m := m) (w := w) (sp := inner) (mem := mem) ScratchPacked.u
      (env := Asm.assign E5 6 (smul 32 (2 ^ D)).toUInt64) (a := (2 : Expr)) (b := (ScratchPacked.count : Expr))
      (x := 2) (y := count) (by simp [eval]) (by simp [eval, Asm.assign, k1]) (by decide) hc
    have t3 := smulIn_runs (m := m) (w := w) (sp := inner) (mem := mem) ScratchPacked.t
      (env := Asm.assign (Asm.assign E5 6 (smul 32 (2 ^ D)).toUInt64) 7 (smul 2 count).toUInt64)
      (a := (ScratchPacked.u : Expr)) (b := (ScratchPacked.t : Expr)) (x := smul 2 count) (y := smul 32 (2 ^ D))
      (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign]) (smul_le _ _) (smul_le _ _)
    have t4 := saddIn_runs (m := m) (w := w) (sp := inner) (mem := mem) ScratchPacked.r
      (env := Asm.assign (Asm.assign (Asm.assign E5 6 (smul 32 (2 ^ D)).toUInt64) 7 (smul 2 count).toUInt64) 6
        (smul (smul 2 count) (smul 32 (2 ^ D))).toUInt64)
      (a := (ScratchPacked.r : Expr)) (b := (ScratchPacked.t : Expr)) (x := smul 32 count)
      (y := smul (smul 2 count) (smul 32 (2 ^ D))) (by simp [eval, Asm.assign, k3]) (by simp [eval, Asm.assign])
      (smul_le _ _) (smul_le _ _)
    have nz : D.toUInt64 ≠ 0 := by
      intro h; have := congrArg UInt64.toNat h; rw [addr_toNat (by omega)] at this; simp at this; exact zero this
    refine Calls.fn hf room rfl (Runs.block_cons s1 (Runs.block_cons s2
      (Runs.when_true 1 (by simp [eval, Cond.holds, Asm.assign, nz]) (by decide)
        (Runs.block_append
          (Runs.block_cons (Runs.set' rfl) (Runs.block_cons (Runs.set' rfl) (Runs.block_cons loop
            (Runs.block_cons t1 (Runs.block_cons t2 t3))))) t4)))) ?_
    simp [ScratchPacked.fn, eval, Asm.assign, packedNeed, D] at zero ⊢
    simp [zero]

/-! ### The saturated width -/

/-- Every word of a plan is below two to the 64, as a plan a binding writes always is. -/
def Fits (ws : List Nat) : Prop := ∀ x ∈ ws, x < 2 ^ 64

/-- Words that fit, split at the end of a first part. -/
theorem fits_split {xs ys : List Nat} (h : Fits (xs ++ ys)) : Fits xs ∧ Fits ys :=
  ⟨fun x m => h x (List.mem_append_left _ m), fun x m => h x (List.mem_append_right _ m)⟩

/-- A saturated total of widths is at most the cap, from a total at most the cap. -/
theorem satFieldsWidth_le : ∀ (fs : List Desc) (acc : Nat), acc ≤ scratchCap → satFieldsWidth fs acc ≤ scratchCap
  | [], _, h => h
  | _ :: rest, _, _ => satFieldsWidth_le rest _ (sadd_le _ _)

/-- A saturated width is at most the cap, when the plan's words fit. -/
theorem satWidth_le (d : Desc) (fits : Fits (Plan.words d)) : satWidth d ≤ scratchCap := by
  have capv : scratchCap = 2 ^ 62 := rfl
  cases d with
  | bitVector n =>
    have := fits n (by simp [Plan.words])
    simp only [satWidth]; omega
  | bool => simp [satWidth]; omega
  | container _ fs => exact satFieldsWidth_le fs 0 (by omega)
  | progressiveContainer _ _ fs => exact satFieldsWidth_le fs 0 (by omega)
  | uint _ | byteVector _ => exact sat_le _
  | vector _ _ => exact smul_le _ _
  | _ => simp [satWidth]

/-- The saturated width function's frame holds eleven words. -/
theorem scratchWidthFrame : ScratchWidth.fn.frame = 11 := by decide

/-- The loop over fields in the saturated width function. -/
abbrev scratchWidthLoop : Stmt :=
  while_ (lt ScratchWidth.i ScratchWidth.n) ([callInto ScratchWidth.x "ssz_scratch_width" [ScratchWidth.q]] ++
    saddIn ScratchWidth.w ScratchWidth.w ScratchWidth.x ++
    [callInto ScratchWidth.q "ssz_plan_next" [ScratchWidth.q], ScratchWidth.i ::= ScratchWidth.i + 1])

mutual

/-- The saturated width function returns a well-formed type's saturated width. -/
theorem scratchWidth_calls (hf : PlanFns m) (d : Desc) (a sp : Nat) (mem : Memory)
    (hw : WordsAt w mem a (Plan.words d)) (fits : Fits (Plan.words d)) (hp : d.wellFormed = .ok ())
    (stack : w.stackLo + 112 * d.nesting ≤ sp) :
    Calls m w "ssz_scratch_width" sp [a.toUInt64] mem (satWidth d).toUInt64 mem := by
  have capv : scratchCap = 2 ^ 62 := rfl
  have one := nesting_pos d
  have room : w.stackLo + 8 + 8 * ScratchWidth.fn.frame ≤ sp := by rw [scratchWidthFrame]; omega
  have inner : w.stackLo + 112 * (d.nesting - 1) ≤ sp - 8 - 8 * ScratchWidth.fn.frame := by
    rw [scratchWidthFrame]; omega
  have tagRead := eval_tag (w := w) (env := entryEnv [a.toUInt64]) (mem := mem) (e := .var 0) hw
    (by simp [eval, entryEnv])
  have tag0 := Runs.set' (m := m) (sp := sp - 8 - 8 * ScratchWidth.fn.frame) (x := 1) tagRead
  have w0 := Runs.set' (m := m) (w := w) (v := 0) (sp := sp - 8 - 8 * ScratchWidth.fn.frame) (x := 2)
    (e := (0 : Expr)) (env := Asm.assign (entryEnv [a.toUInt64]) 1 (Plan.tag d).toUInt64) (mem := mem) rfl
  cases d with
  | bool =>
    refine Calls.fn hf.scratchWidth room rfl (Runs.block_cons tag0 (Runs.block_cons w0
      (Runs.ifElse_true 1 tag_cond (by decide) (Runs.set' rfl)))) ?_
    simp [ScratchWidth.fn, eval, Asm.assign, satWidth]
  | uint n | byteVector n =>
    simp only [Plan.words] at hw fits
    have nf := fits n (by simp)
    refine Calls.fn hf.scratchWidth room rfl (Runs.block_cons tag0 (Runs.block_cons w0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_true 1 tag_cond (by decide)
        (Runs.block_cons (Runs.set' (eval_word hw 1 (by simp) (by simp [eval, Asm.assign, entryEnv])))
          (satIn_runs ScratchWidth.w (x := n) (by simp [Asm.assign]) nf)))))) ?_
    simp [ScratchWidth.fn, eval, Asm.assign, satWidth]
  | bitVector n =>
    simp only [Plan.words] at hw fits
    have nf := fits n (by simp)
    have hld : eval w (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1 (Plan.tag (.bitVector n)).toUInt64) 2 0) mem
        (.load .b8 (.op .add (.var 0) (.lit 8))) = some n.toUInt64 :=
      eval_word hw 1 (by simp) (by simp [eval, Asm.assign, entryEnv])
    refine Calls.fn hf.scratchWidth room rfl (Runs.block_cons tag0 (Runs.block_cons w0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_false tag_cond (Runs.ifElse_true 1 tag_cond (by decide)
        (Runs.set' (eval_ceilDiv hld 8 (by simp)))))))) ?_
    simp only [ScratchWidth.fn, eval, Asm.assign, satWidth]
    simp only [ite_true]
    congr 2
    rw [addr_toNat nf]
    omega
  | byteList _ | bitList _ | progressiveBitList _ | list _ _ | progressiveList _ _ | compatibleUnion _ _ =>
    refine Calls.fn hf.scratchWidth room rfl (Runs.block_cons tag0 (Runs.block_cons w0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond
        (Runs.when_false tag_cond))))))) ?_
    simp [ScratchWidth.fn, eval, Asm.assign, satWidth]
  | vector e l =>
    simp only [Plan.words] at hw fits
    obtain ⟨hh, he⟩ := wordsAt_split hw
    obtain ⟨fh, fe⟩ := fits_split fits
    have lf := fh l (by simp)
    replace hp := wellFormed_vector hp
    simp only [Desc.nesting] at inner
    have call := scratchWidth_calls hf e (a + 16) (sp - 8 - 8 * ScratchWidth.fn.frame) mem (by simpa using he) fe hp
      (by omega)
    let E := Asm.assign (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
        (Plan.tag (.vector e l)).toUInt64) 2 0) 5 (satWidth e).toUInt64
    have hld : eval w E mem (.load .b8 (.op .add (.var 0) (.lit 8))) = some l.toUInt64 :=
      eval_word hh 1 (by simp) (by simp [E, eval, Asm.assign, entryEnv])
    have s3 := satIn_runs (m := m) (w := w) (sp := sp - 8 - 8 * ScratchWidth.fn.frame) (mem := mem) ScratchWidth.y
      (env := Asm.assign E 7 l.toUInt64) (x := l) (by simp [Asm.assign]) lf
    have s4 := smulIn_runs (m := m) (w := w) (sp := sp - 8 - 8 * ScratchWidth.fn.frame) (mem := mem) ScratchWidth.w
      (env := Asm.assign (Asm.assign E 7 l.toUInt64) 7 (sat l).toUInt64)
      (a := (ScratchWidth.x : Expr)) (b := (ScratchWidth.y : Expr)) (x := satWidth e) (y := sat l)
      (by simp [E, eval, Asm.assign]) (by simp [eval, Asm.assign]) (satWidth_le e fe) (sat_le _)
    refine Calls.fn hf.scratchWidth room rfl (Runs.block_cons tag0 (Runs.block_cons w0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond (Runs.ifElse_true 1 tag_cond (by decide)
        (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, entryEnv]) call)
          (Runs.block_cons (Runs.set' hld) (Runs.block_cons s3 s4))))))))) ?_
    simp [ScratchWidth.fn, eval, Asm.assign, satWidth]
  | container names fs =>
    simp only [Plan.words] at hw fits
    obtain ⟨hh, hfs⟩ := wordsAt_split hw
    obtain ⟨_, ffs⟩ := fits_split fits
    replace hp := wellFormed_container hp
    simp only [Desc.nesting] at inner
    have hN : fs.length < 2 ^ 64 := fields_small hfs
    obtain ⟨env', run, h2'⟩ := scratchWidth_loop hf fs (a + 16) 0 fs.length (sp - 8 - 8 * ScratchWidth.fn.frame) 0
      (Asm.assign (Asm.assign (Asm.assign (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
        (Plan.tag (.container names fs)).toUInt64) 2 0) 3 fs.length.toUInt64) 4 (a + 16).toUInt64) 6 0) mem
      (by simpa using hfs) ffs hp (by omega)
      (by simp [Asm.assign]) (by simp [Asm.assign]) (by simp [Asm.assign])
      (by simp [Asm.assign]) hN (by simp) (by omega)
    refine Calls.fn hf.scratchWidth room rfl (Runs.block_cons tag0 (Runs.block_cons w0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond
        (Runs.when_true 1 tag_cond (by decide)
          (Runs.block_cons (Runs.ifElse_true 1 tag_cond (by decide)
            (Runs.block_cons (Runs.set' (eval_word hh 1 (by simp) (by simp [eval, Asm.assign, entryEnv])))
              (Runs.set' (by simp [eval, Asm.assign, entryEnv]))))
            (Runs.block_cons (Runs.set' rfl) run))))))))) ?_
    simp [ScratchWidth.fn, eval, h2', satWidth]
  | progressiveContainer active names fs =>
    simp only [Plan.words] at hw fits
    obtain ⟨hpre, hfs⟩ := wordsAt_split hw
    obtain ⟨hpre, hn⟩ := wordsAt_split hpre
    obtain ⟨hh, _⟩ := wordsAt_split hpre
    obtain ⟨_, ffs⟩ := fits_split fits
    replace hp := wellFormed_progressiveContainer hp
    simp only [Desc.nesting] at inner
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hn hfs
    have hN : fs.length < 2 ^ 64 := fields_small hfs
    rw [show a + 8 * (0 + 1 + 1 + active.length) = a + 16 + 8 * active.length by omega] at hn
    have hk : eval w (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
        (Plan.tag (.progressiveContainer active names fs)).toUInt64) 2 0) mem
        (.load .b8 (.op .add (.var 0) (.lit 8))) = some active.length.toUInt64 := by
      have := eval_word hh 1 (by simp) (e := .op .add (.var 0) (.lit 8))
        (env := Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
          (Plan.tag (.progressiveContainer active names fs)).toUInt64) 2 0) (mem := mem)
        (by simp [eval, Asm.assign, entryEnv])
      simpa using this
    have hq : eval w (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
        (Plan.tag (.progressiveContainer active names fs)).toUInt64) 2 0) mem
        (ScratchWidth.p + 16 + 8 * ld (ScratchWidth.p + 8)) = some (a + 16 + 8 * active.length).toUInt64 := by
      simp only [mul_eq, ld_eq, add_eq, ofNat_eq, eval_op', eval_var', hk, eval_lit']
      simp [Asm.assign, entryEnv]
    obtain ⟨env', run, h2'⟩ := scratchWidth_loop hf fs (a + 16 + 8 * active.length + 8) 0 fs.length
      (sp - 8 - 8 * ScratchWidth.fn.frame) 0
      (Asm.assign (Asm.assign (Asm.assign (Asm.assign (Asm.assign (Asm.assign (entryEnv [a.toUInt64]) 1
        (Plan.tag (.progressiveContainer active names fs)).toUInt64) 2 0) 4 (a + 16 + 8 * active.length).toUInt64)
        3 fs.length.toUInt64) 4 (a + 16 + 8 * active.length + 8).toUInt64) 6 0) mem
      (by rw [show a + 16 + 8 * active.length + 8 = a + 8 * (0 + 1 + 1 + active.length + (0 + 1)) by omega]
          exact hfs) ffs hp (by omega)
      (by simp [Asm.assign]) (by simp [Asm.assign]) (by simp [Asm.assign])
      (by simp [Asm.assign]) hN (by simp) (by omega)
    refine Calls.fn hf.scratchWidth room rfl (Runs.block_cons tag0 (Runs.block_cons w0 (Runs.ifElse_false tag_cond
      (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond
        (Runs.when_true 1 tag_cond (by decide)
          (Runs.block_cons (Runs.ifElse_false tag_cond
            (Runs.block_cons (Runs.set' hq)
              (Runs.block_cons (Runs.set' (eval_word hn 0 (by simp) (by simp [eval, Asm.assign])))
                (Runs.set' (by simp [eval, Asm.assign])))))
            (Runs.block_cons (Runs.set' rfl) run))))))))) ?_
    simp [ScratchWidth.fn, eval, h2', satWidth]

/-- The loop over fields adds each field's saturated width to the running total. -/
theorem scratchWidth_loop (hf : PlanFns m) (fs : List Desc) (a j N sp acc : Nat) (env : Env)
    (mem : Memory) (hw : WordsAt w mem a (Plan.wordsAll fs)) (fits : Fits (Plan.wordsAll fs))
    (hp : Desc.allWellFormed fs = .ok ()) (hacc : acc ≤ scratchCap)
    (h4 : env 4 = a.toUInt64) (h6 : env 6 = j.toUInt64) (h3 : env 3 = N.toUInt64) (h2 : env 2 = acc.toUInt64)
    (hN : N < 2 ^ 64) (hj : j + fs.length = N) (stack : w.stackLo + 112 * Desc.deepestNesting fs ≤ sp) :
    ∃ env', Runs m w sp env mem scratchWidthLoop env' mem ∧ env' 2 = (satFieldsWidth fs acc).toUInt64 := by
  match fs with
  | [] =>
    refine ⟨env, Runs.loop_exit _ _ _ _ _ _ _ ?_, by simp [h2, satFieldsWidth]⟩
    simp at hj
    simp [eval, Cond.holds, h6, h3, hj]
  | f :: rest =>
    simp only [Plan.wordsAll] at hw fits
    obtain ⟨hf1, hrest⟩ := wordsAt_split hw
    obtain ⟨ff, frest⟩ := fits_split fits
    have hp := allWellFormed_cons hp
    simp only [Desc.deepestNesting] at stack
    have s1 : w.stackLo + 112 * f.nesting ≤ sp := by
      have := Nat.le_max_left f.nesting (Desc.deepestNesting rest); omega
    have s2 : w.stackLo + 112 * Desc.deepestNesting rest ≤ sp := by
      have := Nat.le_max_right f.nesting (Desc.deepestNesting rest); omega
    have width := scratchWidth_calls hf f a sp mem hf1 ff hp.1 s1
    have skip := next_ok m w hf.codec f hp.1 sp mem a hf1 (by rw [walkLevel_eq]; omega)
    have add := saddIn_runs (m := m) (w := w) (sp := sp) (mem := mem) ScratchWidth.w
      (env := Asm.assign env 5 (satWidth f).toUInt64) (a := (ScratchWidth.w : Expr)) (b := (ScratchWidth.x : Expr))
      (x := acc) (y := satWidth f) (by simp [eval, Asm.assign, h2]) (by simp [eval, Asm.assign]) hacc
      (satWidth_le f ff)
    obtain ⟨env', run, h2'⟩ := scratchWidth_loop hf rest (a + 8 * (Plan.words f).length) (j + 1) N sp
      (sadd acc (satWidth f))
      (Asm.assign (Asm.assign (Asm.assign (Asm.assign env 5 (satWidth f).toUInt64) 2
        (sadd acc (satWidth f)).toUInt64) 4 (a + 8 * (Plan.words f).length).toUInt64) 6 (j.toUInt64 + 1)) mem
      hrest frest hp.2 (sadd_le _ _) (by simp [Asm.assign]) (by simp [Asm.assign]) (by simp [Asm.assign, h3])
      (by simp [Asm.assign]) hN (by simp at hj; omega) s2
    refine ⟨env', Runs.loop_step 1 ?_ (by decide)
      (Runs.block_append (Runs.block_append (Runs.call (by simp [eval, h4]) width) add)
        (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, h4]) skip)
          (Runs.set' (by simp [eval, Asm.assign, h6])))) run, ?_⟩
    · -- One more field remains, so the count is still below the total.
      simp at hj
      have lt : j.toUInt64 < N.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, addr_toNat (by omega), addr_toNat hN]; omega
      simp [eval, Cond.holds, h6, h3, lt]
    · rw [h2']; simp [satFieldsWidth]

end

/-! ### The scratch bound of fixed-size roots -/

/-- The packed bound is at most the cap. -/
theorem packedNeed_le (width count : Nat) : packedNeed width count ≤ scratchCap := by
  unfold packedNeed; dsimp only; split
  · exact smul_le _ _
  · exact sadd_le _ _

/-- The scratch bound of fixed-size roots is at most the cap. -/
theorem rootsNeed_le (d : Desc) (count : Nat) : rootsNeed d count ≤ scratchCap := by
  cases d <;> simp only [rootsNeed] <;> (repeat' split) <;> first | exact packedNeed_le _ _ | exact sadd_le _ _

/-- The most the fields' roots need is at most the cap, from a most at most the cap. -/
theorem fieldsRootsNeed_le : ∀ (fs : List Desc) (count most : Nat), most ≤ scratchCap →
    fieldsRootsNeed fs count most ≤ scratchCap
  | [], _, _, h => h
  | f :: rest, count, _, h => fieldsRootsNeed_le rest count _ (Nat.max_le.mpr ⟨rootsNeed_le f count, h⟩)

/-- Every tag is below thirteen. -/
theorem tag_lt (d : Desc) : Plan.tag d < 13 := by
  cases d <;> simp [Plan.tag]

/-- A type's tag is at most one exactly when the type is basic. -/
theorem tag_le_one (d : Desc) : (Plan.tag d ≤ 1) = d.isBasic := by
  cases d <;> simp [Plan.tag, Desc.isBasic]

/-- Comparing a type's tag with one answers whether the type is basic. -/
theorem eval_le_tag {w : World} {env : Env} {mem : Memory} {x : Expr} {e : Desc}
    (h : eval w env mem x = some (Plan.tag e).toUInt64) : eval w env mem (le x 1) = some (if e.isBasic then 1 else 0) := by
  simp only [le_eq', eval_cmp', h, ofNat_eq, eval_lit']
  cases e <;> simp [Plan.tag, Desc.isBasic, Cond.holds]

/-- A value at most the cap fits a word. -/
theorem lt64 {x : Nat} (h : x ≤ scratchCap) : x < 2 ^ 64 := Nat.lt_of_le_of_lt h (by decide)

/-- An at-most comparison of two values below the word size answers as the numbers compare. -/
theorem eval_le_nat {w : World} {env : Env} {mem : Memory} {a b : Expr} {x y : Nat}
    (ha : eval w env mem a = some x.toUInt64) (hb : eval w env mem b = some y.toUInt64) (hx : x < 2 ^ 64)
    (hy : y < 2 ^ 64) : eval w env mem (le a b) = some (if x ≤ y then 1 else 0) := by
  simp only [le_eq', eval_cmp', ha, hb, Option.bind_some]
  have inj : x.toUInt64 = y.toUInt64 ↔ x = y := by
    constructor
    · intro h; have := congrArg UInt64.toNat h; rwa [addr_toNat hx, addr_toNat hy] at this
    · intro h; rw [h]
  by_cases lt : x < y
  · have ne : x ≠ y := by omega
    simp [Cond.holds, (toUInt64_lt hx hy).mpr lt, Nat.le_of_lt lt]
  · by_cases eq : x = y
    · subst eq; simp [Cond.holds]
    · have nlt : ¬ x.toUInt64 < y.toUInt64 := fun h => lt ((toUInt64_lt hx hy).mp h)
      have nle : ¬ x ≤ y := by omega
      have neq : (x.toUInt64 == y.toUInt64) = false := by simp [inj, eq]
      simp [Cond.holds, neq, nlt, nle]

/-- The fixed-size roots bound's frame holds seventeen words. -/
theorem scratchRootsFrame : ScratchRoots.fn.frame = 17 := by decide

/-- The loop over fields in the fixed-size roots bound. -/
abbrev scratchRootsLoop : Stmt :=
  while_ (lt ScratchRoots.i ScratchRoots.k) [callInto ScratchRoots.x "ssz_scratch_roots" [ScratchRoots.q,
    ScratchRoots.count], maxIn ScratchRoots.t ScratchRoots.x ScratchRoots.t,
    callInto ScratchRoots.q "ssz_plan_next" [ScratchRoots.q], ScratchRoots.i ::= ScratchRoots.i + 1]

set_option maxRecDepth 8000 in
mutual

/-- The fixed-size roots bound function returns the bound, for a count at most the cap. -/
theorem scratchRoots_calls (hf : PlanFns m) (d : Desc) (a count sp : Nat) (mem : Memory)
    (hw : WordsAt w mem a (Plan.words d)) (fits : Fits (Plan.words d)) (hp : d.wellFormed = .ok ())
    (hc : count ≤ scratchCap) (stack : w.stackLo + 256 * (d.nesting + 1) ≤ sp) :
    Calls m w "ssz_scratch_roots" sp [a.toUInt64, count.toUInt64] mem (rootsNeed d count).toUInt64 mem := by
  have one := nesting_pos d
  have room' : w.stackLo + 8 + 8 * 17 ≤ sp := by omega
  have inner : w.stackLo + 256 * d.nesting + 112 ≤ sp - 8 - 8 * 17 := by omega
  have tagRead := eval_tag (w := w) (env := entryEnv [a.toUInt64, count.toUInt64]) (mem := mem) (e := .var 0) hw
    (by simp [eval, entryEnv])
  have tag0 := Runs.set' (m := m) (sp := sp - 8 - 8 * ScratchRoots.fn.frame) (x := 2) tagRead
  -- Every other fixed-size type packs.
  have packs : Plan.tag d ≠ 7 → Plan.tag d ≠ 10 →
      Calls m w "ssz_scratch_roots" sp [a.toUInt64, count.toUInt64] mem (packedNeed (satWidth d) count).toUInt64
        mem := by
    intro n7 n10
    have width := scratchWidth_calls hf d a (sp - 8 - 8 * ScratchRoots.fn.frame) mem hw fits hp
      (by rw [scratchRootsFrame]; omega)
    have packed := scratchPacked_calls (w := w) hf.depth hf.scratchPacked (satWidth d) count
      (sp - 8 - 8 * ScratchRoots.fn.frame) mem (satWidth_le d fits) hc (by rw [scratchRootsFrame]; omega)
    have t7 : (Plan.tag d).toUInt64 ≠ 7 := by
      intro h; apply n7; have := congrArg UInt64.toNat h
      rw [addr_toNat (by have := tag_lt d; omega)] at this; simpa using this
    have t10 : (Plan.tag d).toUInt64 ≠ 10 := by
      intro h; apply n10; have := congrArg UInt64.toNat h
      rw [addr_toNat (by have := tag_lt d; omega)] at this; simpa using this
    refine Calls.fn hf.scratchRoots (scratchRootsFrame ▸ room') rfl (Runs.block_cons tag0 (Runs.ifElse_false
      (by simp [eval, Cond.holds, Asm.assign, t7]) (Runs.ifElse_false (by simp [eval, Cond.holds, Asm.assign, t10])
        (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, entryEnv]) width)
          (Runs.call (by simp [eval, Asm.assign, entryEnv]) packed))))) ?_
    simp [ScratchRoots.fn, eval, Asm.assign]
  cases d with
  | vector e l =>
    simp only [Plan.words] at hw fits
    obtain ⟨hh, he⟩ := wordsAt_split hw
    obtain ⟨fh, fe⟩ := fits_split fits
    have lf : l < 2 ^ 64 := fh l (by simp)
    replace hp := wellFormed_vector hp
    simp only [Desc.nesting] at inner
    have he' : WordsAt w mem (a + 16) (Plan.words e) := by simpa using he
    let isp := sp - 8 - 8 * ScratchRoots.fn.frame
    let E1 := Asm.assign (entryEnv [a.toUInt64, count.toUInt64]) 2 (Plan.tag (.vector e l)).toUInt64
    have sl := Runs.set' (m := m) (sp := isp) (x := 3) (e := ld (ScratchRoots.p + 8)) (env := E1) (mem := mem)
      (eval_word hh 1 (by simp) (by simp [E1, eval, Asm.assign, entryEnv]))
    have ss := satIn_runs (m := m) (w := w) (sp := isp) (mem := mem) ScratchRoots.len
      (env := Asm.assign E1 3 l.toUInt64) (x := l) (by simp [Asm.assign]) lf
    rw [assign_assign] at ss
    let E2 := Asm.assign (Asm.assign E1 3 (sat l).toUInt64) 4 (a + 16).toUInt64
    have se := Runs.set' (m := m) (w := w) (sp := isp) (x := 4) (e := ScratchRoots.p + 16)
      (env := Asm.assign E1 3 (sat l).toUInt64) (mem := mem) (v := (a + 16).toUInt64)
      (by simp [E1, eval, Asm.assign, entryEnv])
    have tagE := eval_tag (w := w) (env := E2) (mem := mem) (e := .var 4) he' (by simp [E2, eval, Asm.assign])
    simp only [E2] at tagE
    have c1 : E2 1 = count.toUInt64 := by simp [E2, E1, Asm.assign, entryEnv]
    have L := sat_le l
    by_cases basic : e.isBasic
    · -- Basic elements pack together.
      have width := scratchWidth_calls hf e (a + 16) isp mem he' fe hp (by simp only [isp]; rw [scratchRootsFrame]; omega)
      have mul := smulIn_runs (m := m) (w := w) (sp := isp) (mem := mem) ScratchRoots.w
        (env := Asm.assign E2 12 (satWidth e).toUInt64) (a := (ScratchRoots.w : Expr)) (b := (ScratchRoots.len : Expr))
        (x := satWidth e) (y := sat l) (by simp [eval, Asm.assign]) (by simp [E2, eval, Asm.assign])
        (satWidth_le e fe) L
      rw [assign_assign] at mul
      have packed := scratchPacked_calls (w := w) hf.depth hf.scratchPacked (smul (satWidth e) (sat l)) count isp
        mem (smul_le _ _) hc (by simp only [isp]; rw [scratchRootsFrame]; omega)
      refine Calls.fn hf.scratchRoots (scratchRootsFrame ▸ room') rfl (Runs.block_cons tag0
        (Runs.ifElse_true 1 tag_cond (by decide) (Runs.block_cons sl (Runs.block_cons ss (Runs.block_cons se
          (Runs.ifElse_true 1 (by have := eval_le_tag (e := e) tagE; rw [ite_eq_left basic] at this; exact this) (by decide)
            (Runs.block_cons (Runs.call (by simp [eval, Asm.assign]) width)
              (Runs.block_cons mul (Runs.call (by simp [eval, Asm.assign, c1]) packed))))))))) ?_
      simp [ScratchRoots.fn, eval, Asm.assign, rootsNeed, basic]
    · have notBasic : eval w (Asm.assign (Asm.assign E1 3 (sat l).toUInt64) 4 (a + 16).toUInt64) mem
          (le (ld ScratchRoots.e) 1) = some 0 := by
        have := eval_le_tag (e := e) tagE; rw [ite_eq_right basic] at this; exact this
      have child (c : Nat) (hc' : c ≤ scratchCap) := scratchRoots_calls hf e (a + 16) c isp mem he' fe hp hc'
        (by simp only [isp]; rw [scratchRootsFrame]; omega)
      have R := rootsNeed_le e
      by_cases one : count = 1
      · -- One value: its elements' roots chunk by chunk, then their tree.
        subst one
        have k1 : E1 1 = (1 : Nat).toUInt64 := by simp [E1, Asm.assign, entryEnv]
        have one' : (1 : Nat).toUInt64 = 1 := rfl
        let C := if sat l ≤ recordsPerChunk then rootsNeed e (sat l)
          else sadd (smul 32 (sat l)) (rootsNeed e recordsPerChunk)
        have CL : C ≤ scratchCap := by simp only [C]; split; exact R _; exact sadd_le _ _
        -- The chunks' need, into the children's need, leaving the length in place.
        obtain ⟨Ec, chunks, e3, e6⟩ : ∃ Ec, Runs m w isp E2 mem
            (ifElse (le ScratchRoots.len (recordsPerChunk : Nat))
              [callInto ScratchRoots.t "ssz_scratch_roots" [ScratchRoots.e, ScratchRoots.len]]
              ([callInto ScratchRoots.t "ssz_scratch_roots" [ScratchRoots.e, (recordsPerChunk : Nat)],
                smulIn ScratchRoots.u 32 ScratchRoots.len] ++ saddIn ScratchRoots.t ScratchRoots.u ScratchRoots.t))
            Ec mem ∧ Ec 3 = (sat l).toUInt64 ∧ Ec 6 = C.toUInt64 := by
          by_cases small : sat l ≤ recordsPerChunk
          · -- Few enough elements for one chunk.
            refine ⟨_, Runs.ifElse_true 1 (by
                have := eval_le_nat (w := w) (env := E2) (mem := mem) (a := (ScratchRoots.len : Expr))
                  (b := ((recordsPerChunk : Nat) : Expr)) (x := sat l) (y := recordsPerChunk)
                  (by simp [E2, eval, Asm.assign]) (by simp [eval]) (lt64 L) (by decide)
                rw [ite_eq_left small] at this; exact this) (by decide)
              (Runs.block_cons (Runs.call (by simp [E2, eval, Asm.assign]) (child (sat l) L))
                (Runs.block_nil m w isp _ mem)), by simp [E2, Asm.assign], by simp [C, Asm.assign, small]⟩
          · -- Chunks of a fixed count, their roots kept in a buffer.
            refine ⟨_, Runs.ifElse_false (by
                have := eval_le_nat (w := w) (env := E2) (mem := mem) (a := (ScratchRoots.len : Expr))
                  (b := ((recordsPerChunk : Nat) : Expr)) (x := sat l) (y := recordsPerChunk)
                  (by simp [E2, eval, Asm.assign]) (by simp [eval]) (lt64 L) (by decide)
                rw [ite_eq_right small] at this; exact this)
              (Runs.block_append (Runs.block_cons (Runs.call (by simp [E2, eval, Asm.assign]) (child recordsPerChunk
                  (by decide)))
                (Runs.block_cons (smulIn_runs ScratchRoots.u (x := 32) (y := sat l) (by simp [eval])
                  (by simp [E2, eval, Asm.assign]) (by decide) L) (Runs.block_nil m w isp _ mem)))
                (saddIn_runs ScratchRoots.t (x := smul 32 (sat l)) (y := rootsNeed e recordsPerChunk)
                  (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign]) (smul_le _ _) (R _))),
              by simp [E2, Asm.assign], by simp [C, Asm.assign, small]⟩
        have TL := treeNeed_le (sat l)
        refine Calls.fn hf.scratchRoots (scratchRootsFrame ▸ room') rfl (Runs.block_cons tag0
          (Runs.ifElse_true 1 tag_cond (by decide) (Runs.block_cons sl (Runs.block_cons ss (Runs.block_cons se
            (Runs.ifElse_false notBasic (Runs.ifElse_true 1 (by simp [eval, Cond.holds, Asm.assign, k1, one'])
              (by decide)
              (Runs.block_append (Runs.block_append (Runs.block_append (Runs.block_append (Runs.block_append
                (Runs.block_cons chunks
                  (Runs.block_cons (smulIn_runs ScratchRoots.u (x := 32) (y := sat l) (by simp [eval])
                    (by simp [eval, e3]) (by decide) L) (Runs.block_nil m w isp _ mem)))
                (saddIn_runs ScratchRoots.u (x := smul 32 (sat l)) (y := 32) (by simp [eval, Asm.assign])
                  (by simp [eval]) (smul_le _ _) (by decide)))
                (treeIn_runs ScratchRoots.x (n := sat l) (by simp [eval, Asm.assign, e3]) L))
                (saddIn_runs ScratchRoots.u (x := sadd (smul 32 (sat l)) 32) (y := treeNeed (sat l))
                  (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign]) (sadd_le _ _) TL))
                (Runs.block_cons (maxIn_runs ScratchRoots.t (x := C) (y := sadd (sadd (smul 32 (sat l)) 32)
                    (treeNeed (sat l))) (by simp [eval, Asm.assign, e6]) (by simp [eval, Asm.assign]) (lt64 CL)
                    (lt64 (sadd_le _ _)))
                  (Runs.block_nil m w isp _ mem)))
                (saddIn_runs ScratchRoots.r (x := 32) (y := max C (sadd (sadd (smul 32 (sat l)) 32) (treeNeed (sat l))))
                  (by simp [eval]) (by simp [eval, Asm.assign]) (by decide)
                  (Nat.max_le.mpr ⟨CL, sadd_le _ _⟩)))))))))) ?_
        simp [ScratchRoots.fn, eval, Asm.assign, rootsNeed, basic, C]
      · -- Several values: every element root of every value, then a tree per value.
        have k1 : E1 1 = count.toUInt64 := by simp [E1, Asm.assign, entryEnv]
        have ne1 : count.toUInt64 ≠ 1 := by
          intro h; apply one; have := congrArg UInt64.toNat h; rw [addr_toNat (lt64 hc)] at this; simpa using this
        have R1 := R count
        refine Calls.fn hf.scratchRoots (scratchRootsFrame ▸ room') rfl (Runs.block_cons tag0
          (Runs.ifElse_true 1 tag_cond (by decide) (Runs.block_cons sl (Runs.block_cons ss (Runs.block_cons se
            (Runs.ifElse_false notBasic (Runs.ifElse_false (by simp [eval, Cond.holds, Asm.assign, k1, ne1])
              (Runs.block_append (Runs.block_append (Runs.block_cons (Runs.call (m := m) (sp := isp) (env := E2) (mem := mem) (dst := 6)
            (args := [(ScratchRoots.e : Expr), (ScratchRoots.count : Expr)]) (by simp [E2, eval, Asm.assign, k1])
            (child count hc))
          (Runs.block_cons (smulIn_runs ScratchRoots.u (x := 64) (y := count) (by simp [eval])
            (by simp [E2, eval, Asm.assign, k1]) (by decide) hc)
          (Runs.block_cons (smulIn_runs ScratchRoots.u (x := smul 64 count) (y := sat l)
            (by simp [eval, Asm.assign]) (by simp [E2, eval, Asm.assign]) (smul_le _ _) L)
          (Runs.block_cons (maxIn_runs ScratchRoots.t (x := rootsNeed e count) (y := smul (smul 64 count) (sat l))
            (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign]) (lt64 R1) (lt64 (smul_le _ _)))
          (Runs.block_cons (smulIn_runs ScratchRoots.u (x := 32) (y := count) (by simp [eval])
            (by simp [E2, eval, Asm.assign, k1]) (by decide) hc)
          (Runs.block_cons (smulIn_runs ScratchRoots.x (x := smul 32 count) (y := sat l)
            (by simp [eval, Asm.assign]) (by simp [E2, eval, Asm.assign]) (smul_le _ _) L)
            (Runs.block_nil m w isp _ mem)))))))
          (saddIn_runs ScratchRoots.u (x := smul 32 count) (y := smul (smul 32 count) (sat l))
            (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign]) (smul_le _ _) (smul_le _ _)))
          (saddIn_runs ScratchRoots.r (x := sadd (smul 32 count) (smul (smul 32 count) (sat l)))
            (y := max (rootsNeed e count) (smul (smul 64 count) (sat l)))
            (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign]) (sadd_le _ _)
            (Nat.max_le.mpr ⟨R1, smul_le _ _⟩)))))))))) ?_
        simp [ScratchRoots.fn, eval, Asm.assign, rootsNeed, basic, one]
  | container names fs =>
    simp only [Plan.words] at hw fits
    obtain ⟨hh, hfs⟩ := wordsAt_split hw
    obtain ⟨_, ffs⟩ := fits_split fits
    replace hp := wellFormed_container hp
    simp only [Desc.nesting] at inner
    have hN : fs.length < 2 ^ 64 := fields_small hfs
    let isp := sp - 8 - 8 * ScratchRoots.fn.frame
    let Et := Asm.assign (entryEnv [a.toUInt64, count.toUInt64]) 2 (Plan.tag (.container names fs)).toUInt64
    let E8 := Asm.assign (Asm.assign Et 13 fs.length.toUInt64) 8 fs.length.toUInt64
    let EL := Asm.assign (Asm.assign (Asm.assign (Asm.assign E8 8 (sat fs.length).toUInt64) 9 (a + 16).toUInt64) 6 0)
      10 0
    have s1 : Runs m w isp Et mem (ScratchRoots.k ::= ld (ScratchRoots.p + 8)) (Asm.assign Et 13 fs.length.toUInt64)
        mem := Runs.set' (eval_word hh 1 (by simp) (by simp [Et, eval, Asm.assign, entryEnv]))
    have ss := satIn_runs (m := m) (w := w) (sp := isp) (mem := mem) ScratchRoots.n (env := E8) (x := fs.length)
      (by simp [E8, Asm.assign]) hN
    -- The fields' bounds, the most of them kept.
    obtain ⟨E', loop, m6, keep⟩ := scratchRoots_loop hf fs (a + 16) 0 fs.length count isp 0 EL mem
      (by simpa using hfs) ffs hp (by decide) hc (by simp [EL, Asm.assign]) (by simp [EL, Asm.assign])
      (by simp [EL, E8, Asm.assign]) (by simp [EL, Asm.assign]) (by simp [EL, E8, Et, Asm.assign, entryEnv]) hN
      (by simp) (by simp only [isp]; rw [scratchRootsFrame]; omega)
    have k1 : E' 1 = count.toUInt64 := by
      rw [keep 1 (by decide) (by decide) (by decide) (by decide)]; simp [EL, E8, Et, Asm.assign, entryEnv]
    have k8 : E' 8 = (sat fs.length).toUInt64 := by
      rw [keep 8 (by decide) (by decide) (by decide) (by decide)]; simp [EL, Asm.assign]
    have ML := fieldsRootsNeed_le fs count 0 (by decide)
    have NL := sat_le fs.length
    -- The records' roots and trees, past the fields.
    obtain ⟨Ef, tail, rf⟩ : ∃ Ef, Runs m w isp E' mem
        (ifElse (eq ScratchRoots.count 1)
          ([smulIn ScratchRoots.u 32 ScratchRoots.n] ++ saddIn ScratchRoots.u 32 ScratchRoots.u ++
            treeIn ScratchRoots.x ScratchRoots.n ++ saddIn ScratchRoots.x 32 ScratchRoots.x ++
            [maxIn ScratchRoots.t ScratchRoots.t ScratchRoots.x] ++ saddIn ScratchRoots.r ScratchRoots.u ScratchRoots.t)
          ([smulIn ScratchRoots.u 32 ScratchRoots.count, smulIn ScratchRoots.x ScratchRoots.u ScratchRoots.n] ++
            saddIn ScratchRoots.u ScratchRoots.u ScratchRoots.x ++ [smulIn ScratchRoots.x 64 ScratchRoots.count,
              smulIn ScratchRoots.x ScratchRoots.x ScratchRoots.n, maxIn ScratchRoots.t ScratchRoots.t ScratchRoots.x] ++
            saddIn ScratchRoots.r ScratchRoots.u ScratchRoots.t))
        Ef mem ∧ Ef 5 = (rootsNeed (.container names fs) count).toUInt64 := by
      by_cases one : count = 1
      · -- One record: its field roots, then their tree.
        subst one
        refine ⟨_, Runs.ifElse_true 1 (by simp [eval, Cond.holds, k1]) (by decide)
          (Runs.block_append (Runs.block_append (Runs.block_append (Runs.block_append (Runs.block_append
            (Runs.block_cons (smulIn_runs ScratchRoots.u (x := 32) (y := sat fs.length) (by simp [eval])
              (by simp [eval, k8]) (by decide) NL) (Runs.block_nil m w isp _ mem))
            (saddIn_runs ScratchRoots.u (x := 32) (y := smul 32 (sat fs.length)) (by simp [eval])
              (by simp [eval, Asm.assign]) (by decide) (smul_le _ _)))
            (treeIn_runs ScratchRoots.x (n := sat fs.length) (by simp [eval, Asm.assign, k8]) NL))
            (saddIn_runs ScratchRoots.x (x := 32) (y := treeNeed (sat fs.length)) (by simp [eval])
              (by simp [eval, Asm.assign]) (by decide) (treeNeed_le _)))
            (Runs.block_cons (maxIn_runs ScratchRoots.t (x := fieldsRootsNeed fs 1 0)
                (y := sadd 32 (treeNeed (sat fs.length))) (by simp [eval, Asm.assign, m6])
                (by simp [eval, Asm.assign]) (lt64 ML) (lt64 (sadd_le _ _)))
              (Runs.block_nil m w isp _ mem)))
            (saddIn_runs ScratchRoots.r (x := sadd 32 (smul 32 (sat fs.length)))
              (y := max (fieldsRootsNeed fs 1 0) (sadd 32 (treeNeed (sat fs.length))))
              (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign]) (sadd_le _ _)
              (Nat.max_le.mpr ⟨ML, sadd_le _ _⟩))), ?_⟩
        simp [Asm.assign, rootsNeed]
      · -- Several records: every field root of every record, then a tree per record.
        have ne1 : count.toUInt64 ≠ 1 := by
          intro h; apply one; have := congrArg UInt64.toNat h; rw [addr_toNat (lt64 hc)] at this; simpa using this
        refine ⟨_, Runs.ifElse_false (by simp [eval, Cond.holds, k1, ne1])
          (Runs.block_append (Runs.block_append (Runs.block_append
            (Runs.block_cons (smulIn_runs ScratchRoots.u (x := 32) (y := count) (by simp [eval])
              (by simp [eval, k1]) (by decide) hc)
              (Runs.block_cons (smulIn_runs ScratchRoots.x (x := smul 32 count) (y := sat fs.length)
                (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign, k8]) (smul_le _ _) NL)
                (Runs.block_nil m w isp _ mem)))
            (saddIn_runs ScratchRoots.u (x := smul 32 count) (y := smul (smul 32 count) (sat fs.length))
              (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign]) (smul_le _ _) (smul_le _ _)))
            (Runs.block_cons (smulIn_runs ScratchRoots.x (x := 64) (y := count) (by simp [eval])
              (by simp [eval, Asm.assign, k1]) (by decide) hc)
              (Runs.block_cons (smulIn_runs ScratchRoots.x (x := smul 64 count) (y := sat fs.length)
                (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign, k8]) (smul_le _ _) NL)
                (Runs.block_cons (maxIn_runs ScratchRoots.t (x := fieldsRootsNeed fs count 0)
                    (y := smul (smul 64 count) (sat fs.length)) (by simp [eval, Asm.assign, m6])
                    (by simp [eval, Asm.assign]) (lt64 ML) (lt64 (smul_le _ _)))
                  (Runs.block_nil m w isp _ mem)))))
            (saddIn_runs ScratchRoots.r (x := sadd (smul 32 count) (smul (smul 32 count) (sat fs.length)))
              (y := max (fieldsRootsNeed fs count 0) (smul (smul 64 count) (sat fs.length)))
              (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign]) (sadd_le _ _)
              (Nat.max_le.mpr ⟨ML, smul_le _ _⟩))), ?_⟩
        simp [Asm.assign, rootsNeed, one]
    refine Calls.fn hf.scratchRoots (scratchRootsFrame ▸ room') rfl (Runs.block_cons tag0
      (Runs.ifElse_false tag_cond (Runs.ifElse_true 1 tag_cond (by decide)
        (Runs.block_cons s1 (Runs.block_cons (Runs.set' rfl) (Runs.block_cons ss
          (Runs.block_cons (Runs.set' (by simp [E8, Et, eval, Asm.assign, entryEnv]))
            (Runs.block_cons (Runs.set' rfl) (Runs.block_cons (Runs.set' rfl) (Runs.block_cons loop
              (Runs.block_cons tail (Runs.block_nil m w isp _ mem)))))))))))) ?_
    simp [ScratchRoots.fn, eval, rf]
  | bool | uint _ | byteVector _ | byteList _ | bitVector _ | bitList _ | progressiveBitList _ | list _ _
  | progressiveList _ _ | progressiveContainer _ _ _ | compatibleUnion _ _ =>
    have := packs (by simp [Plan.tag]) (by simp [Plan.tag])
    simpa [rootsNeed] using this

/-- The loop over fields keeps the most any field's roots need, and leaves every other variable alone. -/
theorem scratchRoots_loop (hf : PlanFns m) (fs : List Desc) (a j N count sp most : Nat) (env : Env)
    (mem : Memory) (hw : WordsAt w mem a (Plan.wordsAll fs)) (fits : Fits (Plan.wordsAll fs))
    (hp : Desc.allWellFormed fs = .ok ()) (hmost : most ≤ scratchCap) (hc : count ≤ scratchCap)
    (h9 : env 9 = a.toUInt64) (h10 : env 10 = j.toUInt64) (h13 : env 13 = N.toUInt64) (h6 : env 6 = most.toUInt64)
    (h1 : env 1 = count.toUInt64)
    (hN : N < 2 ^ 64) (hj : j + fs.length = N) (stack : w.stackLo + 256 * (Desc.deepestNesting fs + 1) ≤ sp) :
    ∃ env', Runs m w sp env mem scratchRootsLoop env' mem ∧ env' 6 = (fieldsRootsNeed fs count most).toUInt64 ∧
      ∀ v, v ≠ 6 → v ≠ 9 → v ≠ 10 → v ≠ 11 → env' v = env v := by
  match fs with
  | [] =>
    refine ⟨env, Runs.loop_exit _ _ _ _ _ _ _ ?_, by simp [h6, fieldsRootsNeed], fun _ _ _ _ _ => rfl⟩
    simp at hj
    simp [eval, Cond.holds, h10, h13, hj]
  | f :: rest =>
    simp only [Plan.wordsAll] at hw fits
    obtain ⟨hf1, hrest⟩ := wordsAt_split hw
    obtain ⟨ff, frest⟩ := fits_split fits
    have hp := allWellFormed_cons hp
    simp only [Desc.deepestNesting] at stack
    have s1 : w.stackLo + 256 * (f.nesting + 1) ≤ sp := by
      have := Nat.le_max_left f.nesting (Desc.deepestNesting rest); omega
    have s2 : w.stackLo + 256 * (Desc.deepestNesting rest + 1) ≤ sp := by
      have := Nat.le_max_right f.nesting (Desc.deepestNesting rest); omega
    have roots := scratchRoots_calls hf f a count sp mem hf1 ff hp.1 hc s1
    have skip := next_ok m w hf.codec f hp.1 sp mem a hf1 (by rw [walkLevel_eq]; omega)
    have big := maxIn_runs (m := m) (w := w) (sp := sp) (mem := mem) ScratchRoots.t
      (env := Asm.assign env 11 (rootsNeed f count).toUInt64) (a := (ScratchRoots.x : Expr))
      (b := (ScratchRoots.t : Expr)) (x := rootsNeed f count) (y := most) (by simp [eval, Asm.assign])
      (by simp [eval, Asm.assign, h6]) (Nat.lt_of_le_of_lt (rootsNeed_le f count) (by decide)) (Nat.lt_of_le_of_lt hmost (by decide))
    obtain ⟨env', run, h6', keep⟩ := scratchRoots_loop hf rest (a + 8 * (Plan.words f).length) (j + 1) N count sp
      (max (rootsNeed f count) most)
      (Asm.assign (Asm.assign (Asm.assign (Asm.assign env 11 (rootsNeed f count).toUInt64) 6
        (max (rootsNeed f count) most).toUInt64) 9 (a + 8 * (Plan.words f).length).toUInt64) 10 (j.toUInt64 + 1))
      mem hrest frest hp.2 (Nat.max_le.mpr ⟨rootsNeed_le f count, hmost⟩) hc (by simp [Asm.assign])
      (by simp [Asm.assign]) (by simp [Asm.assign, h13]) (by simp [Asm.assign]) (by simp [Asm.assign, h1])
      hN (by simp at hj; omega) s2
    refine ⟨env', Runs.loop_step 1 ?_ (by decide)
      (Runs.block_cons (Runs.call (by simp [eval, h9, h1]) roots)
        (Runs.block_cons big
          (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, h9]) skip)
            (Runs.set' (by simp [eval, Asm.assign, h10]))))) run, ?_, fun v a b c d => ?_⟩
    · -- One more field remains, so the count is still below the total.
      simp at hj
      have lt : j.toUInt64 < N.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, addr_toNat (by omega), addr_toNat hN]; omega
      simp [eval, Cond.holds, h10, h13, lt]
    · rw [h6']; simp [fieldsRootsNeed]
    · rw [keep v a b c d]; simp [Asm.assign, a, b, c, d]

end

/-! ### The scratch bound of a value's root -/

/-- The scratch bound of a value's root is at most the cap. -/
theorem varNeed_le : ∀ (d : Desc) (size : Nat), varNeed d size ≤ scratchCap
  | .vector e l, size => by
    simp only [varNeed]; split
    · exact rootsNeed_le _ _
    · exact sadd_le _ _
  | .container names fs, size => by
    simp only [varNeed]; split
    · exact rootsNeed_le _ _
    · exact Nat.max_le.mpr ⟨sadd_le _ _, sadd_le _ _⟩
  | .byteList _, _ | .bitList _, _ | .progressiveBitList _, _ | .list _ _, _ | .progressiveList _ _, _
  | .progressiveContainer _ _ _, _ | .compatibleUnion _ _, _ => sadd_le _ _
  | .bool, _ | .uint _, _ | .byteVector _, _ | .bitVector _, _ => rootsNeed_le _ _

/-- The most several types need is at most the cap, from a most at most the cap. -/
theorem fieldsVarNeed_le : ∀ (fs : List Desc) (size most : Nat), most ≤ scratchCap →
    fieldsVarNeed fs size most ≤ scratchCap
  | [], _, _, h => h
  | f :: rest, size, _, h => fieldsVarNeed_le rest size _ (Nat.max_le.mpr ⟨varNeed_le f size, h⟩)

/-- The nodes over the bytes of a word-sized size are at most the cap. -/
theorem nodesFor_le {size : Nat} (hs : size < 2 ^ 64) : nodesFor size ≤ scratchCap := by
  simp only [nodesFor, scratchCap]; omega

/-- The quotient of two values below the word size, by a nonzero divisor. -/
theorem eval_div_nat {w : World} {env : Env} {mem : Memory} {a b : Expr} {x y : Nat}
    (ha : eval w env mem a = some x.toUInt64) (hb : eval w env mem b = some y.toUInt64) (hx : x < 2 ^ 64)
    (hy : y < 2 ^ 64) (nz : y ≠ 0) : eval w env mem (a / b) = some (x / y).toUInt64 := by
  have ynz : y.toUInt64 ≠ 0 := by
    intro h; have := congrArg UInt64.toNat h; rw [addr_toNat hy] at this; exact nz this
  simp only [div_eq, eval_div', ha, hb, Option.bind_some]
  simp only [ynz, beq_iff_eq, ite_false]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div, addr_toNat hx, addr_toNat hy, addr_toNat (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)]

/-- The rounded-up count of nodes over a word-sized size. -/
theorem eval_nodes {w : World} {env : Env} {mem : Memory} {a : Expr} {size : Nat}
    (ha : eval w env mem a = some size.toUInt64) (hs : size < 2 ^ 64) :
    eval w env mem (ceilDiv a 32) = some (nodesFor size).toUInt64 := by
  rw [eval_ceilDiv ha 32 (by simp), addr_toNat hs]; rfl

/-- The most elements of a type other than a basic one a list's encoding of a size can hold, unsaturated. -/
def nodesRaw (e : Desc) (size : Nat) : Nat :=
  if hasWidth e then (if satWidth e = 0 then 0 else size / satWidth e) else size / bytesPerOffset

/-- The step setting a list's node count from its element's width, or from the offset size. -/
abbrev listNodes : Stmt :=
  ifElse RootScratch.fx [callInto RootScratch.w "ssz_scratch_width" [RootScratch.e],
      ifElse (eq RootScratch.w 0) [RootScratch.nodes ::= 0] [RootScratch.nodes ::= RootScratch.size / RootScratch.w]]
    [RootScratch.nodes ::= RootScratch.size / 4]

/-- The node count step sets the unsaturated count, and changes only the count and the width. -/
theorem listNodes_runs (hf : PlanFns m) (e : Desc) (ea size sp : Nat) (env : Env) (mem : Memory)
    (hw : WordsAt w mem ea (Plan.words e)) (fits : Fits (Plan.words e)) (hp : e.wellFormed = .ok ())
    (hs : size < 2 ^ 64) (h14 : env 14 = bitOf (hasWidth e)) (h8 : env 8 = ea.toUInt64)
    (h1 : env 1 = size.toUInt64) (stack : w.stackLo + 112 * e.nesting ≤ sp) :
    ∃ E, Runs m w sp env mem listNodes E mem ∧ E 7 = (nodesRaw e size).toUInt64 ∧
      ∀ v, v ≠ 7 → v ≠ 15 → E v = env v := by
  by_cases fx : hasWidth e
  · have width := scratchWidth_calls hf e ea sp mem hw fits hp stack
    have WL := satWidth_le e fits
    by_cases z : satWidth e = 0
    · refine ⟨_, Runs.ifElse_true 1 (by simp [eval, h14, fx, bitOf]) (by decide)
        (Runs.block_cons (Runs.call (by simp [eval, h8]) width)
          (Runs.block_cons (Runs.ifElse_true 1 (by simp [eval, Cond.holds, Asm.assign, z]) (by decide)
            (Runs.block_cons (Runs.set' rfl) (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))),
        by simp [Asm.assign, nodesRaw, fx, z], fun v a b => by simp [Asm.assign, a, b]⟩
    · have nz : (satWidth e).toUInt64 ≠ 0 := by
        intro h; have := congrArg UInt64.toNat h; rw [addr_toNat (lt64 WL)] at this; exact z this
      refine ⟨_, Runs.ifElse_true 1 (by simp [eval, h14, fx, bitOf]) (by decide)
        (Runs.block_cons (Runs.call (by simp [eval, h8]) width)
          (Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, Asm.assign, nz])
            (Runs.block_cons (Runs.set' (eval_div_nat (x := size) (y := satWidth e)
              (by simp [eval, Asm.assign, h1]) (by simp [eval, Asm.assign]) hs (lt64 WL) z))
              (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))),
        by simp [Asm.assign, nodesRaw, fx, z], fun v a b => by simp [Asm.assign, a, b]⟩
  · refine ⟨_, Runs.ifElse_false (by simp [eval, h14, fx, bitOf])
      (Runs.block_cons (Runs.set' (eval_div_nat (x := size) (y := 4) (by simp [eval, h1]) (by simp [eval]) hs
        (by decide) (by decide))) (Runs.block_nil _ _ _ _ _)),
      by simp [Asm.assign, nodesRaw, fx, bytesPerOffset], fun v a b => by simp [Asm.assign, a]⟩

/-- The step computing a list's element need, by the fixed-size bound or by recursion. -/
abbrev listChunk : Stmt :=
  ifElse RootScratch.pl [RootScratch.k ::= RootScratch.nodes,
      when (lt (recordsPerChunk : Nat) RootScratch.k) [RootScratch.k ::= (recordsPerChunk : Nat)],
      callInto RootScratch.t "ssz_scratch_roots" [RootScratch.e, RootScratch.k],
      callInto RootScratch.x "ssz_scratch_roots" [RootScratch.e, 1], maxIn RootScratch.t RootScratch.x RootScratch.t]
    [callInto RootScratch.t "ssz_root_scratch" [RootScratch.e, RootScratch.size]]

/-- The element need step sets the need of a list's elements, and changes only the need, the chunk count and a
partial bound. -/
theorem listChunk_runs (hf : PlanFns m) (e : Desc) (ea size sp nodes : Nat) (env : Env) (mem : Memory)
    (hw : WordsAt w mem ea (Plan.words e)) (fits : Fits (Plan.words e)) (hp : e.wellFormed = .ok ())
    (hn : nodes ≤ scratchCap) (h13 : env 13 = bitOf (plain e)) (h7 : env 7 = nodes.toUInt64)
    (h8 : env 8 = ea.toUInt64) (h1 : env 1 = size.toUInt64) (stack : w.stackLo + 256 * (e.nesting + 1) ≤ sp)
    (rec : plain e = false →
      Calls m w "ssz_root_scratch" sp [ea.toUInt64, size.toUInt64] mem (varNeed e size).toUInt64 mem) :
    ∃ E, Runs m w sp env mem listChunk E mem ∧
      E 4 = (if plain e then max (rootsNeed e 1) (rootsNeed e (min nodes recordsPerChunk)) else varNeed e size).toUInt64 ∧
      ∀ v, v ≠ 4 → v ≠ 6 → v ≠ 10 → E v = env v := by
  -- One record's need, then the larger of it and the chunk's.
  have floor : ∀ (E : Env) (c : Nat), E 4 = (rootsNeed e c).toUInt64 → E 8 = ea.toUInt64 →
      Runs m w sp E mem (.block [callInto RootScratch.x "ssz_scratch_roots" [RootScratch.e, 1],
        maxIn RootScratch.t RootScratch.x RootScratch.t])
        (Asm.assign (Asm.assign E 6 (rootsNeed e 1).toUInt64) 4 (max (rootsNeed e 1) (rootsNeed e c)).toUInt64) mem :=
    fun E c h4 h8' => Runs.block_cons (Runs.call (by simp [eval, h8'])
      (scratchRoots_calls hf e ea 1 sp mem hw fits hp (by decide) stack))
      (Runs.block_cons (maxIn_runs RootScratch.t (x := rootsNeed e 1) (y := rootsNeed e c)
        (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign, h4]) (lt64 (rootsNeed_le _ _))
        (lt64 (rootsNeed_le _ _))) (Runs.block_nil _ _ _ _ _))
  by_cases pl : plain e
  · by_cases big : recordsPerChunk < nodes
    · -- Past one chunk, a chunk's count of records.
      have lt : (recordsPerChunk : Nat).toUInt64 < nodes.toUInt64 := (toUInt64_lt (by decide) (lt64 hn)).mpr big
      refine ⟨_, Runs.ifElse_true 1 (by simp [eval, h13, pl, bitOf]) (by decide)
        (Runs.block_cons (Runs.set' (v := nodes.toUInt64) (by simp [eval, h7]))
          (Runs.block_cons (Runs.when_true 1 (by simp [eval, Cond.holds, Asm.assign, lt]) (by decide)
            (Runs.block_cons (Runs.set' rfl) (Runs.block_nil _ _ _ _ _)))
            (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, h8])
              (scratchRoots_calls hf e ea recordsPerChunk sp mem hw fits hp (by decide) stack))
              (floor _ recordsPerChunk (by simp [Asm.assign]) (by simp [Asm.assign, h8]))))),
        by simp [Asm.assign, pl, Nat.min_eq_right (Nat.le_of_lt big)], fun v a b c => by simp [Asm.assign, a, b, c]⟩
    · -- At most one chunk, every record.
      have nlt : ¬ (recordsPerChunk : Nat).toUInt64 < nodes.toUInt64 :=
        fun h => big ((toUInt64_lt (by decide) (lt64 hn)).mp h)
      refine ⟨_, Runs.ifElse_true 1 (by simp [eval, h13, pl, bitOf]) (by decide)
        (Runs.block_cons (Runs.set' (v := nodes.toUInt64) (by simp [eval, h7]))
          (Runs.block_cons (Runs.when_false (by simp [eval, Cond.holds, Asm.assign, nlt]))
            (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, h8])
              (scratchRoots_calls hf e ea nodes sp mem hw fits hp hn stack))
              (floor _ nodes (by simp [Asm.assign]) (by simp [Asm.assign, h8]))))),
        by simp [Asm.assign, pl, Nat.min_eq_left (Nat.le_of_not_lt big)], fun v a b c => by simp [Asm.assign, a, b, c]⟩
  · -- Elements of any other type, by recursion.
    refine ⟨_, Runs.ifElse_false (by simp [eval, h13, pl, bitOf])
      (Runs.block_cons (Runs.call (by simp [eval, h8, h1]) (rec (by simpa using pl))) (Runs.block_nil _ _ _ _ _)),
      by simp [Asm.assign, pl], fun v a _ _ => by simp [Asm.assign, a]⟩

/-- The step computing a list's node count and its elements' need. -/
abbrev listElements : Stmt :=
  ifElse (le (ld RootScratch.e) 1)
    [RootScratch.nodes ::= ceilDiv RootScratch.size 32, satIn RootScratch.nodes, RootScratch.t ::= 0]
    [callInto RootScratch.fx "ssz_plan_fixed" [RootScratch.e], listNodes, satIn RootScratch.nodes,
      callInto RootScratch.pl "ssz_plan_plain" [RootScratch.e], listChunk]

/-- The elements' need of a list, from the size of its encoding. -/
def listElementsNeed (e : Desc) (size : Nat) : Nat :=
  if e.isBasic then 0
  else if plain e then max (rootsNeed e 1) (rootsNeed e (min (nodesBound e size) recordsPerChunk))
  else varNeed e size

/-- The list step sets the node bound and the elements' need. -/
theorem listElements_runs (hf : PlanFns m) (e : Desc) (ea size sp : Nat) (env : Env) (mem : Memory)
    (hw : WordsAt w mem ea (Plan.words e)) (fits : Fits (Plan.words e)) (hp : e.wellFormed = .ok ())
    (hs : size < 2 ^ 64) (h8 : env 8 = ea.toUInt64) (h1 : env 1 = size.toUInt64)
    (stack : w.stackLo + 256 * (e.nesting + 1) ≤ sp)
    (rec : plain e = false →
      Calls m w "ssz_root_scratch" sp [ea.toUInt64, size.toUInt64] mem (varNeed e size).toUInt64 mem) :
    ∃ E, Runs m w sp env mem listElements E mem ∧ E 7 = (nodesBound e size).toUInt64 ∧
      E 4 = (listElementsNeed e size).toUInt64 := by
  have tagE := eval_tag (w := w) (env := env) (mem := mem) (e := .var 8) hw (by simp [eval, h8])
  have NL := nodesFor_le hs
  by_cases basic : e.isBasic
  · -- Basic elements pack, and need nothing of their own.
    refine ⟨_, Runs.ifElse_true 1 (by have := eval_le_tag (e := e) tagE; rw [ite_eq_left basic] at this; exact this)
      (by decide) (Runs.block_cons (Runs.set' (eval_nodes (by simp [eval, h1]) hs))
        (Runs.block_cons (satIn_runs RootScratch.nodes (x := nodesFor size) (by simp [Asm.assign]) (lt64 NL))
          (Runs.block_cons (Runs.set' rfl) (Runs.block_nil _ _ _ _ _)))),
      by simp [Asm.assign, nodesBound, basic], by simp [Asm.assign, listElementsNeed, basic]⟩
  · have one := nesting_pos e
    have fixed := planFixed_calls hf e ea sp mem hw hp (by omega)
    have plainE := planPlain_calls hf e ea sp mem hw hp (by omega)
    obtain ⟨EN, nodes, n7, nkeep⟩ := listNodes_runs hf e ea size sp (Asm.assign env 14 (bitOf (hasWidth e))) mem hw
      fits hp hs (by simp [Asm.assign]) (by simp [Asm.assign, h8]) (by simp [Asm.assign, h1]) (by omega)
    have rawFits : nodesRaw e size < 2 ^ 64 := by
      simp only [nodesRaw]; split
      · split
        · decide
        · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hs
      · exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hs
    have bound : nodesBound e size = sat (nodesRaw e size) := by simp [nodesBound, nodesRaw, basic]
    let EP := Asm.assign (Asm.assign EN 7 (sat (nodesRaw e size)).toUInt64) 13 (bitOf (plain e))
    obtain ⟨EC, chunk, c4, ckeep⟩ := listChunk_runs hf e ea size sp (sat (nodesRaw e size)) EP mem hw fits hp
      (sat_le _) (by simp [EP, Asm.assign]) (by simp [EP, Asm.assign])
      (by simp [EP, Asm.assign, nkeep 8 (by decide) (by decide), h8])
      (by simp [EP, Asm.assign, nkeep 1 (by decide) (by decide), h1]) stack rec
    refine ⟨EC, Runs.ifElse_false (by have := eval_le_tag (e := e) tagE; rw [ite_eq_right basic] at this; exact this)
      (Runs.block_cons (Runs.call (by simp [eval, h8]) fixed)
        (Runs.block_cons nodes
          (Runs.block_cons (satIn_runs RootScratch.nodes (x := nodesRaw e size) n7 rawFits)
            (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, nkeep 8 (by decide) (by decide), h8]) plainE)
              (Runs.block_cons chunk (Runs.block_nil _ _ _ _ _)))))), ?_, ?_⟩
    · rw [ckeep 7 (by decide) (by decide) (by decide), bound]; simp [EP, Asm.assign]
    · rw [c4]; simp [listElementsNeed, basic, bound]

/-- A list's steps past its element's address. -/
abbrev listTail : List Stmt :=
  [listElements, smulIn RootScratch.u 32 RootScratch.nodes] ++ saddIn RootScratch.u 96 RootScratch.u ++
    treeIn RootScratch.x RootScratch.nodes ++ [maxIn RootScratch.t RootScratch.t RootScratch.x] ++
    saddIn RootScratch.r RootScratch.u RootScratch.t

/-- A list's steps past its element's address give the list's scratch bound. -/
theorem listTail_runs (hf : PlanFns m) (e : Desc) (ea size sp : Nat) (env : Env) (mem : Memory)
    (hw : WordsAt w mem ea (Plan.words e)) (fits : Fits (Plan.words e)) (hp : e.wellFormed = .ok ())
    (hs : size < 2 ^ 64) (h8 : env 8 = ea.toUInt64) (h1 : env 1 = size.toUInt64)
    (stack : w.stackLo + 256 * (e.nesting + 1) ≤ sp)
    (rec : plain e = false →
      Calls m w "ssz_root_scratch" sp [ea.toUInt64, size.toUInt64] mem (varNeed e size).toUInt64 mem) :
    ∃ E, Runs m w sp env mem (.block listTail) E mem ∧ E 3 = (varNeed (.list e 0) size).toUInt64 := by
  obtain ⟨EL, elems, e7, e4⟩ := listElements_runs hf e ea size sp env mem hw fits hp hs h8 h1 stack rec
  have NB : nodesBound e size ≤ scratchCap := sat_le _
  have EL' : listElementsNeed e size ≤ scratchCap := by
    simp only [listElementsNeed]; split
    · decide
    · split
      · exact Nat.max_le.mpr ⟨rootsNeed_le _ _, rootsNeed_le _ _⟩
      · exact varNeed_le _ _
  refine ⟨_, Runs.block_append (Runs.block_append (Runs.block_append (Runs.block_append
    (Runs.block_cons elems (Runs.block_cons (smulIn_runs RootScratch.u (x := 32) (y := nodesBound e size)
      (by simp [eval]) (by simp [eval, e7]) (by decide) NB) (Runs.block_nil _ _ _ _ _)))
    (saddIn_runs RootScratch.u (x := 96) (y := smul 32 (nodesBound e size)) (by simp [eval])
      (by simp [eval, Asm.assign]) (by decide) (smul_le _ _)))
    (treeIn_runs RootScratch.x (n := nodesBound e size) (by simp [eval, Asm.assign, e7]) NB))
    (Runs.block_cons (maxIn_runs RootScratch.t (x := listElementsNeed e size) (y := treeNeed (nodesBound e size))
      (by simp [eval, Asm.assign, e4]) (by simp [eval, Asm.assign]) (lt64 EL') (lt64 (treeNeed_le _)))
      (Runs.block_nil _ _ _ _ _)))
    (saddIn_runs RootScratch.r (x := sadd 96 (smul 32 (nodesBound e size)))
      (y := max (listElementsNeed e size) (treeNeed (nodesBound e size))) (by simp [eval, Asm.assign])
      (by simp [eval, Asm.assign]) (sadd_le _ _) (Nat.max_le.mpr ⟨EL', treeNeed_le _⟩)), ?_⟩
  simp [Asm.assign, varNeed, listElementsNeed]

/-- The scratch bound function's frame holds nineteen words. -/
theorem rootScratchFrame : RootScratch.fn.frame = 19 := by decide

/-- The loop over child types in the scratch bound. -/
abbrev rootScratchLoop : Stmt :=
  while_ (lt RootScratch.i RootScratch.k) [callInto RootScratch.x "ssz_root_scratch" [RootScratch.q,
    RootScratch.size], maxIn RootScratch.t RootScratch.x RootScratch.t,
    callInto RootScratch.q "ssz_plan_next" [RootScratch.q], RootScratch.i ::= RootScratch.i + 1]

set_option maxRecDepth 8000 in
mutual

/-- The scratch bound function returns the scratch bound of a well-formed type, for a word-sized size. -/
theorem rootScratch_calls (hf : PlanFns m) (d : Desc) (a size sp : Nat) (mem : Memory)
    (hw : WordsAt w mem a (Plan.words d)) (fits : Fits (Plan.words d)) (hp : d.wellFormed = .ok ())
    (hs : size < 2 ^ 64) (stack : w.stackLo + 256 * (d.nesting + 2) ≤ sp) :
    Calls m w "ssz_root_scratch" sp [a.toUInt64, size.toUInt64] mem (varNeed d size).toUInt64 mem := by
  have one := nesting_pos d
  have room' : w.stackLo + 8 + 8 * 19 ≤ sp := by omega
  have inner : w.stackLo + 256 * d.nesting + 256 ≤ sp - 8 - 8 * 19 := by omega
  have tagRead := eval_tag (w := w) (env := entryEnv [a.toUInt64, size.toUInt64]) (mem := mem) (e := .var 0) hw
    (by simp [eval, entryEnv])
  have tag0 := Runs.set' (m := m) (sp := sp - 8 - 8 * RootScratch.fn.frame) (x := 2) tagRead
  have roots := scratchRoots_calls hf d a 1 (sp - 8 - 8 * RootScratch.fn.frame) mem hw fits hp (by decide)
    (by rw [rootScratchFrame]; omega)
  have NL := nodesFor_le hs
  cases d with
  | bool | uint _ | byteVector _ | bitVector _ =>
    -- A basic type or a byte or bit vector has the bound of its fixed-size root.
    refine Calls.fn hf.rootScratch (rootScratchFrame ▸ room') rfl (Runs.block_cons tag0
      (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond
        (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond
          (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, entryEnv]) roots)
            (Runs.block_nil _ _ _ _ _)))))))) ?_
    simp [RootScratch.fn, eval, Asm.assign, varNeed]
  | byteList _ | bitList _ | progressiveBitList _ =>
    -- Bytes pack into nodes, then a tree over them.
    refine Calls.fn hf.rootScratch (rootScratchFrame ▸ room') rfl (Runs.block_cons tag0
      (Runs.ifElse_true 1 tag_cond (by decide)
        (Runs.block_append (Runs.block_append (Runs.block_append
          (Runs.block_cons (Runs.set' (eval_nodes (by simp [eval, Asm.assign, entryEnv]) hs))
            (Runs.block_cons (smulIn_runs RootScratch.u (x := 32) (y := nodesFor size) (by simp [eval])
              (by simp [eval, Asm.assign]) (by decide) NL) (Runs.block_nil _ _ _ _ _)))
          (saddIn_runs RootScratch.u (x := 96) (y := smul 32 (nodesFor size)) (by simp [eval])
            (by simp [eval, Asm.assign]) (by decide) (smul_le _ _)))
          (treeIn_runs RootScratch.x (n := nodesFor size) (by simp [eval, Asm.assign]) NL))
          (saddIn_runs RootScratch.r (x := sadd 96 (smul 32 (nodesFor size))) (y := treeNeed (nodesFor size))
            (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign]) (sadd_le _ _) (treeNeed_le _))))) ?_
    simp [RootScratch.fn, eval, Asm.assign, varNeed]
  | list e l =>
    simp only [Plan.words] at hw fits
    obtain ⟨_, he⟩ := wordsAt_split hw
    obtain ⟨_, fe⟩ := fits_split fits
    replace hp := wellFormed_list hp
    simp only [Desc.nesting] at inner
    have he' : WordsAt w mem (a + 16) (Plan.words e) := by simpa using he
    -- The element's need, by recursion, when the element is not plain.
    obtain ⟨E, tail, r3⟩ := listTail_runs hf e (a + 16) size (sp - 8 - 8 * RootScratch.fn.frame)
      (Asm.assign (Asm.assign (entryEnv [a.toUInt64, size.toUInt64]) 2 (Plan.tag (.list e l)).toUInt64) 8
        (a + 16).toUInt64) mem he' fe hp hs (by simp [Asm.assign]) (by simp [Asm.assign, entryEnv])
      (by rw [rootScratchFrame]; omega)
      (fun _ => rootScratch_calls hf e (a + 16) size _ mem he' fe hp hs (by rw [rootScratchFrame]; omega))
    refine Calls.fn hf.rootScratch (rootScratchFrame ▸ room') rfl (Runs.block_cons tag0
      (Runs.ifElse_false tag_cond (Runs.ifElse_true 1 tag_cond (by decide)
        (Runs.block_cons (Runs.ifElse_true 1 tag_cond (by decide)
          (Runs.block_cons (Runs.set' (v := (a + 16).toUInt64) (by simp [eval, Asm.assign, entryEnv]))
            (Runs.block_nil _ _ _ _ _))) tail)))) ?_
    simp [RootScratch.fn, eval, r3, varNeed]
  | progressiveList e l =>
    have hlen : (9 :: Plan.bound l).length = 3 := by cases l <;> rfl
    simp only [Plan.words] at hw fits
    obtain ⟨_, he⟩ := wordsAt_split hw
    obtain ⟨_, fe⟩ := fits_split fits
    replace hp := wellFormed_progressiveList hp
    simp only [Desc.nesting] at inner
    have he' : WordsAt w mem (a + 24) (Plan.words e) := by rw [hlen] at he; simpa using he
    -- The element's need, by recursion, when the element is not plain.
    obtain ⟨E, tail, r3⟩ := listTail_runs hf e (a + 24) size (sp - 8 - 8 * RootScratch.fn.frame)
      (Asm.assign (Asm.assign (entryEnv [a.toUInt64, size.toUInt64]) 2 (Plan.tag (.progressiveList e l)).toUInt64)
        8 (a + 24).toUInt64) mem he' fe hp hs (by simp [Asm.assign]) (by simp [Asm.assign, entryEnv])
      (by rw [rootScratchFrame]; omega)
      (fun _ => rootScratch_calls hf e (a + 24) size _ mem he' fe hp hs (by rw [rootScratchFrame]; omega))
    refine Calls.fn hf.rootScratch (rootScratchFrame ▸ room') rfl (Runs.block_cons tag0
      (Runs.ifElse_false tag_cond (Runs.ifElse_true 1 tag_cond (by decide)
        (Runs.block_cons (Runs.ifElse_false tag_cond
          (Runs.block_cons (Runs.set' (v := (a + 24).toUInt64) (by simp [eval, Asm.assign, entryEnv]))
            (Runs.block_nil _ _ _ _ _))) tail)))) ?_
    simp [RootScratch.fn, eval, r3, varNeed]
  | vector e l =>
    have plainT := planPlain_calls hf (.vector e l) a (sp - 8 - 8 * RootScratch.fn.frame) mem hw hp
      (by rw [rootScratchFrame]; omega)
    by_cases pl : plain (.vector e l)
    · -- A plain vector has the bound of its fixed-size root.
      refine Calls.fn hf.rootScratch (rootScratchFrame ▸ room') rfl (Runs.block_cons tag0
        (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond (Runs.ifElse_true 1 tag_cond (by decide)
          (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, entryEnv]) plainT)
            (Runs.block_cons (Runs.ifElse_true 1 (by simp [eval, Asm.assign, pl, bitOf]) (by decide)
              (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, entryEnv]) roots)
                (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))))))) ?_
      simp [RootScratch.fn, eval, Asm.assign, varNeed, pl]
    · simp only [Plan.words] at hw fits
      obtain ⟨hh, he⟩ := wordsAt_split hw
      obtain ⟨fh, fe⟩ := fits_split fits
      have lf : l < 2 ^ 64 := fh l (by simp)
      have hp' := wellFormed_vector hp
      simp only [Desc.nesting] at inner
      have he' : WordsAt w mem (a + 16) (Plan.words e) := by simpa using he
      have L := sat_le l
      have V := varNeed_le e size
      -- The element's need, by recursion, then the tree over the elements' roots.
      have recV := rootScratch_calls hf e (a + 16) size (sp - 8 - 8 * RootScratch.fn.frame) mem he' fe hp' hs
        (by rw [rootScratchFrame]; omega)
      refine Calls.fn hf.rootScratch (rootScratchFrame ▸ room') rfl (Runs.block_cons tag0
        (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond (Runs.ifElse_true 1 tag_cond (by decide)
          (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, entryEnv]) plainT)
            (Runs.block_cons (Runs.ifElse_false (by simp [eval, Asm.assign, pl, bitOf])
              (Runs.block_cons (Runs.ifElse_true 1 tag_cond (by decide)
                (Runs.block_append (Runs.block_append (Runs.block_append (Runs.block_append
                  (Runs.block_cons (Runs.set' (v := l.toUInt64)
                      (eval_word hh 1 (by simp) (by simp [eval, Asm.assign, entryEnv])))
                    (Runs.block_cons (satIn_runs RootScratch.n (x := l) (by simp [Asm.assign]) lf)
                      (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, entryEnv]) recV)
                        (Runs.block_nil _ _ _ _ _))))
                  (treeIn_runs RootScratch.x (n := sat l) (by simp [eval, Asm.assign]) L))
                  (saddIn_runs RootScratch.x (x := 32) (y := treeNeed (sat l)) (by simp [eval])
                    (by simp [eval, Asm.assign]) (by decide) (treeNeed_le _)))
                  (Runs.block_cons (maxIn_runs RootScratch.t (x := varNeed e size) (y := sadd 32 (treeNeed (sat l)))
                      (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign]) (lt64 V) (lt64 (sadd_le _ _)))
                    (Runs.block_cons (smulIn_runs RootScratch.u (x := 32) (y := sat l) (by simp [eval])
                      (by simp [eval, Asm.assign]) (by decide) L) (Runs.block_nil _ _ _ _ _))))
                  (saddIn_runs RootScratch.r (x := smul 32 (sat l)) (y := max (varNeed e size)
                      (sadd 32 (treeNeed (sat l)))) (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign])
                    (smul_le _ _) (Nat.max_le.mpr ⟨V, sadd_le _ _⟩))))
                (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))))))) ?_
      simp [RootScratch.fn, eval, Asm.assign, varNeed, pl]
  | container names fs =>
    have plainT := planPlain_calls hf (.container names fs) a (sp - 8 - 8 * RootScratch.fn.frame) mem hw hp
      (by rw [rootScratchFrame]; omega)
    by_cases pl : plain (.container names fs)
    · -- A plain container has the bound of its fixed-size root.
      refine Calls.fn hf.rootScratch (rootScratchFrame ▸ room') rfl (Runs.block_cons tag0
        (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond (Runs.ifElse_true 1 tag_cond (by decide)
          (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, entryEnv]) plainT)
            (Runs.block_cons (Runs.ifElse_true 1 (by simp [eval, Asm.assign, pl, bitOf]) (by decide)
              (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, entryEnv]) roots)
                (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))))))) ?_
      simp [RootScratch.fn, eval, Asm.assign, varNeed, pl]
    · simp only [Plan.words] at hw fits
      obtain ⟨hh, hfs⟩ := wordsAt_split hw
      obtain ⟨_, ffs⟩ := fits_split fits
      have hp' := wellFormed_container hp
      simp only [Desc.nesting] at inner
      have hN : fs.length < 2 ^ 64 := fields_small hfs
      let isp := sp - 8 - 8 * RootScratch.fn.frame
      let Et := Asm.assign (Asm.assign (entryEnv [a.toUInt64, size.toUInt64]) 2
        (Plan.tag (.container names fs)).toUInt64) 13 (bitOf (plain (.container names fs)))
      let E9 := Asm.assign (Asm.assign Et 10 fs.length.toUInt64) 9 fs.length.toUInt64
      let EL := Asm.assign (Asm.assign (Asm.assign (Asm.assign E9 9 (sat fs.length).toUInt64) 11 (a + 16).toUInt64)
        4 0) 12 0
      have ss := satIn_runs (m := m) (w := w) (sp := isp) (mem := mem) RootScratch.n (env := E9) (x := fs.length)
        (by simp [E9, Asm.assign]) hN
      -- The fields' needs, the most of them kept.
      obtain ⟨E', loop, m4, keep⟩ := rootScratch_loop hf fs (a + 16) 0 fs.length size isp 0 EL mem
        (by simpa using hfs) ffs hp' (by decide) hs (by simp [EL, Asm.assign]) (by simp [EL, Asm.assign])
        (by simp [EL, E9, Asm.assign]) (by simp [EL, Asm.assign]) (by simp [EL, E9, Et, Asm.assign, entryEnv]) hN
        (by simp) (by simp only [isp]; rw [rootScratchFrame]; omega)
      have k9 : E' 9 = (sat fs.length).toUInt64 := by
        rw [keep 9 (by decide) (by decide) (by decide) (by decide)]; simp [EL, Asm.assign]
      have F := fieldsVarNeed_le fs size 0 (by decide)
      have N := sat_le fs.length
      refine Calls.fn hf.rootScratch (rootScratchFrame ▸ room') rfl (Runs.block_cons tag0
        (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond (Runs.ifElse_true 1 tag_cond (by decide)
          (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, entryEnv]) plainT)
            (Runs.block_cons (Runs.ifElse_false (by simp [eval, Asm.assign, pl, bitOf])
              (Runs.block_cons (Runs.ifElse_false tag_cond
                (Runs.block_append (Runs.block_append (Runs.block_append (Runs.block_append (Runs.block_append
                  (Runs.block_append (Runs.block_append (Runs.block_append
                  (Runs.block_cons (Runs.set' (v := fs.length.toUInt64)
                      (eval_word hh 1 (by simp) (by simp [eval, Asm.assign, entryEnv])))
                    (Runs.block_cons (Runs.set' rfl) (Runs.block_cons ss
                      (Runs.block_cons (Runs.set' (v := (a + 16).toUInt64) (by simp [E9, Et, eval, Asm.assign, entryEnv]))
                        (Runs.block_nil _ _ _ _ _)))))
                  (Runs.block_cons (Runs.set' rfl) (Runs.block_cons (Runs.set' rfl)
                    (Runs.block_cons loop (Runs.block_nil _ _ _ _ _)))))
                  (Runs.block_cons (smulIn_runs RootScratch.u (x := 56) (y := sat fs.length) (by simp [eval])
                    (by simp [eval, k9]) (by decide) N) (Runs.block_nil _ _ _ _ _)))
                  (saddIn_runs RootScratch.u (x := smul 56 (sat fs.length)) (y := fieldsVarNeed fs size 0)
                    (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign, m4]) (smul_le _ _) F))
                  (Runs.block_cons (smulIn_runs RootScratch.x (x := 32) (y := sat fs.length) (by simp [eval])
                    (by simp [eval, Asm.assign, k9]) (by decide) N) (Runs.block_nil _ _ _ _ _)))
                  (saddIn_runs RootScratch.x (x := smul 32 (sat fs.length)) (y := 32) (by simp [eval, Asm.assign])
                    (by simp [eval]) (smul_le _ _) (by decide)))
                  (treeIn_runs RootScratch.t (n := sat fs.length) (by simp [eval, Asm.assign, k9]) N))
                  (saddIn_runs RootScratch.x (x := sadd (smul 32 (sat fs.length)) 32) (y := treeNeed (sat fs.length))
                    (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign]) (sadd_le _ _) (treeNeed_le _)))
                  (Runs.block_cons (maxIn_runs RootScratch.r (x := sadd (smul 56 (sat fs.length)) (fieldsVarNeed fs size 0))
                      (y := sadd (sadd (smul 32 (sat fs.length)) 32) (treeNeed (sat fs.length)))
                      (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign]) (lt64 (sadd_le _ _))
                      (lt64 (sadd_le _ _)))
                    (Runs.block_nil _ _ _ _ _))))
                (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))))))) ?_
      simp [RootScratch.fn, eval, Asm.assign, varNeed, pl]
  | progressiveContainer active names fs =>
    simp only [Plan.words] at hw fits
    obtain ⟨hpre, hfs⟩ := wordsAt_split hw
    obtain ⟨hpre, hn⟩ := wordsAt_split hpre
    obtain ⟨hh, _⟩ := wordsAt_split hpre
    obtain ⟨fpre, ffs⟩ := fits_split fits
    have Af : active.length < 2 ^ 64 := fpre active.length (by simp)
    have hp' := wellFormed_progressiveContainer hp
    simp only [Desc.nesting] at inner
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hn hfs
    have hN : fs.length < 2 ^ 64 := fields_small hfs
    rw [show a + 8 * (0 + 1 + 1 + active.length) = a + 16 + 8 * active.length by omega] at hn
    let isp := sp - 8 - 8 * RootScratch.fn.frame
    let Et := Asm.assign (entryEnv [a.toUInt64, size.toUInt64]) 2
      (Plan.tag (.progressiveContainer active names fs)).toUInt64
    let E2 := Asm.assign (Asm.assign Et 16 active.length.toUInt64) 11 (a + 16 + 8 * active.length).toUInt64
    let E5 := Asm.assign (Asm.assign (Asm.assign E2 16 (sat active.length).toUInt64) 10 fs.length.toUInt64) 9
      fs.length.toUInt64
    let EL := Asm.assign (Asm.assign (Asm.assign (Asm.assign E5 9 (sat fs.length).toUInt64) 11
      (a + 16 + 8 * active.length + 8).toUInt64) 4 0) 12 0
    have sa := satIn_runs (m := m) (w := w) (sp := isp) (mem := mem) RootScratch.ks (env := E2)
      (x := active.length) (by simp [E2, Asm.assign]) Af
    have sn := satIn_runs (m := m) (w := w) (sp := isp) (mem := mem) RootScratch.n (env := E5) (x := fs.length)
      (by simp [E5, Asm.assign]) hN
    -- The fields' needs, the most of them kept.
    have hfs' : WordsAt w mem (a + 16 + 8 * active.length + 8) (Plan.wordsAll fs) := by
      rw [show a + 16 + 8 * active.length + 8 = a + 8 * (0 + 1 + 1 + active.length + (0 + 1)) by omega]
      exact hfs
    obtain ⟨E', loop, m4, keep⟩ := rootScratch_loop hf fs (a + 16 + 8 * active.length + 8) 0 fs.length size isp 0
      EL mem hfs' ffs hp' (by decide) hs (by simp [EL, Asm.assign]) (by simp [EL, Asm.assign])
      (by simp [EL, E5, Asm.assign]) (by simp [EL, Asm.assign]) (by simp [EL, E5, E2, Et, Asm.assign, entryEnv]) hN
      (by simp) (by simp only [isp]; rw [rootScratchFrame]; omega)
    have k9 : E' 9 = (sat fs.length).toUInt64 := by
      rw [keep 9 (by decide) (by decide) (by decide) (by decide)]; simp [EL, Asm.assign]
    have k16 : E' 16 = (sat active.length).toUInt64 := by
      rw [keep 16 (by decide) (by decide) (by decide) (by decide)]; simp [EL, E5, Asm.assign]
    have F := fieldsVarNeed_le fs size 0 (by decide)
    have N := sat_le fs.length
    have K := sat_le active.length
    refine Calls.fn hf.rootScratch (rootScratchFrame ▸ room') rfl (Runs.block_cons tag0
      (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond
        (Runs.ifElse_true 1 tag_cond (by decide)
          (Runs.block_append (Runs.block_append (Runs.block_append (Runs.block_append (Runs.block_append
            (Runs.block_append (Runs.block_append (Runs.block_append (Runs.block_append
            (Runs.block_cons (Runs.set' (v := active.length.toUInt64)
                (eval_word hh 1 (by simp) (by simp [eval, Asm.assign, entryEnv])))
              (Runs.block_cons (Runs.set' (v := (a + 16 + 8 * active.length).toUInt64)
                  (by simp [eval, Asm.assign, entryEnv]))
                (Runs.block_cons sa
                  (Runs.block_cons (Runs.set' (v := fs.length.toUInt64)
                      (eval_word hn 0 (by simp) (by simp [E2, eval, Asm.assign])))
                    (Runs.block_cons (Runs.set' rfl) (Runs.block_cons sn
                      (Runs.block_cons (Runs.set' (v := (a + 16 + 8 * active.length + 8).toUInt64)
                          (by simp [E5, E2, eval, Asm.assign]))
                        (Runs.block_nil _ _ _ _ _))))))))
            (Runs.block_cons (Runs.set' rfl) (Runs.block_cons (Runs.set' rfl)
              (Runs.block_cons loop (Runs.block_nil _ _ _ _ _)))))
            (Runs.block_cons (smulIn_runs RootScratch.u (x := 56) (y := sat fs.length) (by simp [eval])
              (by simp [eval, k9]) (by decide) N) (Runs.block_nil _ _ _ _ _)))
            (saddIn_runs RootScratch.u (x := smul 56 (sat fs.length)) (y := fieldsVarNeed fs size 0)
              (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign, m4]) (smul_le _ _) F))
            (Runs.block_cons (smulIn_runs RootScratch.x (x := 32) (y := sat fs.length) (by simp [eval])
              (by simp [eval, Asm.assign, k9]) (by decide) N)
              (Runs.block_cons (smulIn_runs RootScratch.t (x := 32) (y := sat active.length) (by simp [eval])
                (by simp [eval, Asm.assign, k16]) (by decide) K) (Runs.block_nil _ _ _ _ _))))
            (saddIn_runs RootScratch.x (x := smul 32 (sat fs.length)) (y := smul 32 (sat active.length))
              (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign]) (smul_le _ _) (smul_le _ _)))
            (treeIn_runs RootScratch.t (n := sat active.length) (by simp [eval, Asm.assign, k16]) K))
            (saddIn_runs RootScratch.x (x := sadd (smul 32 (sat fs.length)) (smul 32 (sat active.length)))
              (y := treeNeed (sat active.length)) (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign])
              (sadd_le _ _) (treeNeed_le _)))
            (Runs.block_cons (maxIn_runs RootScratch.r (x := sadd (smul 56 (sat fs.length)) (fieldsVarNeed fs size 0))
                (y := sadd (sadd (smul 32 (sat fs.length)) (smul 32 (sat active.length))) (treeNeed (sat active.length)))
                (by simp [eval, Asm.assign]) (by simp [eval, Asm.assign]) (lt64 (sadd_le _ _)) (lt64 (sadd_le _ _)))
              (Runs.block_nil _ _ _ _ _)))
            (saddIn_runs RootScratch.r (x := 64) (y := max (sadd (smul 56 (sat fs.length)) (fieldsVarNeed fs size 0))
                (sadd (sadd (smul 32 (sat fs.length)) (smul 32 (sat active.length))) (treeNeed (sat active.length))))
              (by simp [eval]) (by simp [eval, Asm.assign]) (by decide)
              (Nat.max_le.mpr ⟨sadd_le _ _, sadd_le _ _⟩)))))))) ?_
    simp [RootScratch.fn, eval, Asm.assign, varNeed]
  | compatibleUnion sel opts =>
    have paired := wellFormed_union_paired hp
    simp only [Plan.words] at hw fits
    obtain ⟨hpre, hos⟩ := wordsAt_split hw
    obtain ⟨hh, _⟩ := wordsAt_split hpre
    obtain ⟨_, fos⟩ := fits_split fits
    have hp' := wellFormed_union hp
    simp only [Desc.nesting] at inner
    simp only [List.length_append, List.length_cons, List.length_nil] at hos
    have hN : opts.length < 2 ^ 64 := fields_small hos
    rw [show a + 8 * (0 + 1 + 1 + sel.length) = a + 16 + 8 * opts.length by omega] at hos
    let isp := sp - 8 - 8 * RootScratch.fn.frame
    let Et := Asm.assign (entryEnv [a.toUInt64, size.toUInt64]) 2 (Plan.tag (.compatibleUnion sel opts)).toUInt64
    let EL := Asm.assign (Asm.assign (Asm.assign (Asm.assign Et 10 opts.length.toUInt64) 11
      (a + 16 + 8 * opts.length).toUInt64) 4 0) 12 0
    -- The options' needs, the most of them kept.
    obtain ⟨E', loop, m4, _⟩ := rootScratch_loop hf opts (a + 16 + 8 * opts.length) 0 opts.length size isp 0
      EL mem hos fos hp' (by decide) hs (by simp [EL, Asm.assign]) (by simp [EL, Asm.assign])
      (by simp [EL, Asm.assign]) (by simp [EL, Asm.assign]) (by simp [EL, Et, Asm.assign, entryEnv]) hN
      (by simp) (by simp only [isp]; rw [rootScratchFrame]; omega)
    have F := fieldsVarNeed_le opts size 0 (by decide)
    refine Calls.fn hf.rootScratch (rootScratchFrame ▸ room') rfl (Runs.block_cons tag0
      (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond (Runs.ifElse_false tag_cond
        (Runs.ifElse_false tag_cond (Runs.ifElse_true 1 tag_cond (by decide)
          (Runs.block_append (Runs.block_append
            (Runs.block_cons (Runs.set' (v := opts.length.toUInt64)
                (eval_word hh 1 (by simp) (by simp [eval, Asm.assign, entryEnv])))
              (Runs.block_cons (Runs.set' (v := (a + 16 + 8 * opts.length).toUInt64)
                  (by simp [eval, Asm.assign, entryEnv])) (Runs.block_nil _ _ _ _ _)))
            (Runs.block_cons (Runs.set' rfl) (Runs.block_cons (Runs.set' rfl)
              (Runs.block_cons loop (Runs.block_nil _ _ _ _ _)))))
            (saddIn_runs RootScratch.r (x := 64) (y := fieldsVarNeed opts size 0) (by simp [eval])
              (by simp [eval, m4]) (by decide) F)))))))) ?_
    simp [RootScratch.fn, eval, Asm.assign, varNeed]

/-- The loop over child types keeps the most any child needs, and leaves every other variable alone. -/
theorem rootScratch_loop (hf : PlanFns m) (fs : List Desc) (a j N size sp most : Nat) (env : Env)
    (mem : Memory) (hw : WordsAt w mem a (Plan.wordsAll fs)) (fits : Fits (Plan.wordsAll fs))
    (hp : Desc.allWellFormed fs = .ok ()) (hmost : most ≤ scratchCap) (hs : size < 2 ^ 64)
    (h11 : env 11 = a.toUInt64) (h12 : env 12 = j.toUInt64) (h10 : env 10 = N.toUInt64)
    (h4 : env 4 = most.toUInt64) (h1 : env 1 = size.toUInt64)
    (hN : N < 2 ^ 64) (hj : j + fs.length = N) (stack : w.stackLo + 256 * (Desc.deepestNesting fs + 2) ≤ sp) :
    ∃ env', Runs m w sp env mem rootScratchLoop env' mem ∧ env' 4 = (fieldsVarNeed fs size most).toUInt64 ∧
      ∀ v, v ≠ 4 → v ≠ 6 → v ≠ 11 → v ≠ 12 → env' v = env v := by
  match fs with
  | [] =>
    refine ⟨env, Runs.loop_exit _ _ _ _ _ _ _ ?_, by simp [h4, fieldsVarNeed], fun _ _ _ _ _ => rfl⟩
    simp at hj
    simp [eval, Cond.holds, h12, h10, hj]
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
    have need := rootScratch_calls hf f a size sp mem hf1 ff hp.1 hs s1
    have skip := next_ok m w hf.codec f hp.1 sp mem a hf1 (by rw [walkLevel_eq]; omega)
    have big := maxIn_runs (m := m) (w := w) (sp := sp) (mem := mem) RootScratch.t
      (env := Asm.assign env 6 (varNeed f size).toUInt64) (a := (RootScratch.x : Expr))
      (b := (RootScratch.t : Expr)) (x := varNeed f size) (y := most) (by simp [eval, Asm.assign])
      (by simp [eval, Asm.assign, h4]) (lt64 (varNeed_le f size)) (lt64 hmost)
    obtain ⟨env', run, h4', keep⟩ := rootScratch_loop hf rest (a + 8 * (Plan.words f).length) (j + 1) N size sp
      (max (varNeed f size) most)
      (Asm.assign (Asm.assign (Asm.assign (Asm.assign env 6 (varNeed f size).toUInt64) 4
        (max (varNeed f size) most).toUInt64) 11 (a + 8 * (Plan.words f).length).toUInt64) 12 (j.toUInt64 + 1))
      mem hrest frest hp.2 (Nat.max_le.mpr ⟨varNeed_le f size, hmost⟩) hs (by simp [Asm.assign])
      (by simp [Asm.assign]) (by simp [Asm.assign, h10]) (by simp [Asm.assign]) (by simp [Asm.assign, h1])
      hN (by simp at hj; omega) s2
    refine ⟨env', Runs.loop_step 1 ?_ (by decide)
      (Runs.block_cons (Runs.call (by simp [eval, h11, h1]) need)
        (Runs.block_cons big
          (Runs.block_cons (Runs.call (by simp [eval, Asm.assign, h11]) skip)
            (Runs.set' (by simp [eval, Asm.assign, h12]))))) run, ?_, fun v a b c d => ?_⟩
    · -- One more child remains, so the count is still below the total.
      simp at hj
      have lt : j.toUInt64 < N.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, addr_toNat (by omega), addr_toNat hN]; omega
      simp [eval, Cond.holds, h12, h10, lt]
    · rw [h4']; simp [fieldsVarNeed]
    · rw [keep v a b c d]; simp [Asm.assign, a, b, c, d]

end

/-- The scratch bound function returns the scratch bytes rooting an encoding of a word-sized size needs. -/
theorem rootScratch_exact (hf : PlanFns m) (d : Desc) (a size sp : Nat) (mem : Memory)
    (hw : WordsAt w mem a (Plan.words d)) (fits : Fits (Plan.words d)) (hp : d.wellFormed = .ok ())
    (hs : size < 2 ^ 64) (stack : w.stackLo + 256 * (d.nesting + 2) ≤ sp) :
    Calls m w "ssz_root_scratch" sp [a.toUInt64, size.toUInt64] mem (rootScratch d size).toUInt64 mem :=
  rootScratch_calls hf d a size sp mem hw fits hp hs stack

end EthLib.Consensus.Ssz.Native.Driver
