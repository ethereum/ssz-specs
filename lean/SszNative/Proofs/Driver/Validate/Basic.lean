import SszNative.Driver.Validate
import SszNative.Proofs.Ir.Wp
import SszNative.Proofs.Asm.Bytes

/-!
The terms the decoding check's proofs are stated in, and the steps they are built from.

A plan sits in memory as words, a node at the address of its tag.
An encoding sits in memory as bytes, a part of it named by absolute addresses.
A refusal is four words written at one place, the only memory the check ever writes.
-/

namespace Ssz.Native.Driver.Validate

open Ssz Ssz.Native Ssz.Native.Ir Ssz.Native.Asm

/-- The module holds every function of the check under its exported name. -/
def Loaded (m : Module) : Prop :=
  ∀ p ∈ fns, m.fns.lookup p.1 = some p.2

/-- The plan's words at an address: readable, and each word read back as itself. -/
def PlanAt (w : World) (mem : Memory) (p : Nat) (ws : List Nat) : Prop :=
  w.access p (8 * ws.length) ∧ ∀ i (h : i < ws.length), readLE mem (p + 8 * i) 8 = (ws[i]).toUInt64

/-- An encoding's bytes from an address: readable, and each byte in its place. -/
def DataAt (w : World) (mem : Memory) (base : Nat) (b : ByteArray) : Prop :=
  w.access base b.size ∧ ∀ i (h : i < b.size), mem (base + i) = b[i]

/-- Memory after four words are written from an address, as a refusal is. -/
def wrote4 (mem : Memory) (err : Nat) (a b c d : UInt64) : Memory :=
  store (store (store (store mem err 8 (qwordByte a)) (err + 8) 8 (qwordByte b)) (err + 16) 8 (qwordByte c))
    (err + 24) 8 (qwordByte d)

/-- Memory after a refusal's four words are written at an address. -/
def wrote (mem : Memory) (err : Nat) (e : Err) : Memory :=
  wrote4 mem err (UInt64.ofNat (e.toWords[0]!)) (UInt64.ofNat (e.toWords[1]!)) (UInt64.ofNat (e.toWords[2]!))
    (UInt64.ofNat (e.toWords[3]!))

/-- The result a check returns for an outcome: zero when accepted, one when refused. -/
def res : Except Err Unit → UInt64
  | .ok _ => 0
  | .error _ => 1

/-- The memory a check leaves for an outcome: untouched when accepted, the refusal written when refused. -/
def after (mem : Memory) (err : Nat) : Except Err Unit → Memory
  | .ok _ => mem
  | .error e => wrote mem err e

/-- A region of memory that a refusal written at an address leaves alone. -/
def Clear (err a n : Nat) : Prop := err + 32 ≤ a ∨ a + n ≤ err

/-! The words of each refusal the check gives. -/

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_overLimit (a b : Nat) : (Err.overLimit a b).toWords = [1, a, b, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_overLimit (a b : Nat) : (Err.overLimit a b).ctorIdx = 1 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_scope (a b : Nat) : (Err.scope a b).toWords = [2, a, b, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_scope (a b : Nat) : (Err.scope a b).ctorIdx = 2 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_scopeTooSmall (a b : Nat) : (Err.scopeTooSmall a b).toWords = [3, a, b, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_scopeTooSmall (a b : Nat) : (Err.scopeTooSmall a b).ctorIdx = 3 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_scopeUndivided (a b : Nat) : (Err.scopeUndivided a b).toWords = [4, a, b, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_scopeUndivided (a b : Nat) : (Err.scopeUndivided a b).ctorIdx = 4 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_scopeWidthless : (Err.scopeWidthless).toWords = [5, 0, 0, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_scopeWidthless : (Err.scopeWidthless).ctorIdx = 5 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_firstOffset (a b : Nat) : (Err.firstOffset a b).toWords = [6, a, b, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_firstOffset (a b : Nat) : (Err.firstOffset a b).ctorIdx = 6 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_offsetUnordered : (Err.offsetUnordered).toWords = [7, 0, 0, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_offsetUnordered : (Err.offsetUnordered).ctorIdx = 7 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_offsetPastScope : (Err.offsetPastScope).toWords = [8, 0, 0, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_offsetPastScope : (Err.offsetPastScope).ctorIdx = 8 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_offsetUnaligned : (Err.offsetUnaligned).toWords = [9, 0, 0, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_offsetUnaligned : (Err.offsetUnaligned).ctorIdx = 9 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_offsetBelowTable : (Err.offsetBelowTable).toWords = [10, 0, 0, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_offsetBelowTable : (Err.offsetBelowTable).ctorIdx = 10 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_notABit (a : Nat) : (Err.notABit a).toWords = [12, a, 0, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_notABit (a : Nat) : (Err.notABit a).ctorIdx = 12 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_paddingBits : (Err.paddingBits).toWords = [14, 0, 0, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_paddingBits : (Err.paddingBits).ctorIdx = 14 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_emptyEncoding : (Err.emptyEncoding).toWords = [15, 0, 0, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_emptyEncoding : (Err.emptyEncoding).ctorIdx = 15 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_noDelimiter : (Err.noDelimiter).toWords = [16, 0, 0, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_noDelimiter : (Err.noDelimiter).ctorIdx = 16 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_trailingZeros : (Err.trailingZeros).toWords = [17, 0, 0, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_trailingZeros : (Err.trailingZeros).ctorIdx = 17 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_noSelector : (Err.noSelector).toWords = [18, 0, 0, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_noSelector : (Err.noSelector).ctorIdx = 18 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_unknownSelector (a : Nat) : (Err.unknownSelector a).toWords = [19, a, 0, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_unknownSelector (a : Nat) : (Err.unknownSelector a).ctorIdx = 19 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_unionSelectorRange (a b c : Nat) : (Err.unionSelectorRange a b c).toWords = [55, a, b, c] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_unionSelectorRange (a b c : Nat) : (Err.unionSelectorRange a b c).ctorIdx = 55 := rfl

/-- This refusal's four words: its code, its numbers, then zeros. -/
@[simp] theorem toWords_offsetOverflow (a : Nat) : (Err.offsetOverflow a).toWords = [59, a, 0, 0] := rfl

/-- This refusal's code. -/
@[simp] theorem ctorIdx_offsetOverflow (a : Nat) : (Err.offsetOverflow a).ctorIdx = 59 := rfl


/-! Reading memory. -/

/-- Bytes inside a readable region are readable. -/
theorem access_sub {w : World} {a n x k : Nat} (h : w.access a n) (lo : a ≤ x) (hi : x + k ≤ a + n) :
    w.access x k := by
  simp only [World.access, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at *
  omega

/-- A sum of two addresses below 2^64 does not wrap. -/
theorem toNat_add (a b : Nat) (h : a + b < 2 ^ 64) : (a.toUInt64 + b.toUInt64).toNat = a + b := by
  simp [UInt64.toNat_add]; omega

/-- The words of the first list sit at the address. -/
theorem PlanAt.left {w : World} {mem : Memory} {p : Nat} {a b : List Nat} (h : PlanAt w mem p (a ++ b)) :
    PlanAt w mem p a := by
  refine ⟨access_sub h.1 (Nat.le_refl _) (by simp; omega), fun i hi => ?_⟩
  have := h.2 i (by simp; omega)
  rwa [List.getElem_append_left hi] at this

/-- The words of the second list sit past the first. -/
theorem PlanAt.right {w : World} {mem : Memory} {p : Nat} {a b : List Nat} (h : PlanAt w mem p (a ++ b)) :
    PlanAt w mem (p + 8 * a.length) b := by
  refine ⟨access_sub h.1 (by omega) (by simp; omega), fun i hi => ?_⟩
  have := h.2 (a.length + i) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa [Nat.mul_add, Nat.add_assoc] using this

/-- Words at an address are at any equal address. -/
theorem PlanAt.at_eq {w : World} {mem : Memory} {p q : Nat} {ws : List Nat} (h : PlanAt w mem p ws) (e : p = q) :
    PlanAt w mem q ws := e ▸ h

/-- A plan ends below the address bound. -/
theorem PlanAt.bound {w : World} {mem : Memory} {p : Nat} {ws : List Nat} (h : PlanAt w mem p ws) :
    p + 8 * ws.length ≤ 2 ^ 63 := by
  have := h.1; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1

/-- A word of the plan, read at an offset from the node, for rewriting. -/
theorem PlanAt.read {w : World} {mem : Memory} {p : Nat} {ws : List Nat} (h : PlanAt w mem p ws) (k : Nat)
    (aligned : k % 8 = 0) (inside : k / 8 < ws.length) : readLE mem (p + k) 8 = (ws[k / 8]!).toUInt64 := by
  have := h.2 (k / 8) inside
  rw [show p + 8 * (k / 8) = p + k by omega] at this
  rw [this, getElem!_pos ws (k / 8) inside]

/-- A word of the plan is readable. -/
theorem PlanAt.readable {w : World} {mem : Memory} {p : Nat} {ws : List Nat} (h : PlanAt w mem p ws) (k : Nat)
    (aligned : k % 8 = 0) (inside : k / 8 < ws.length) : w.access (p + k) 8 = true :=
  access_sub h.1 (by omega) (by omega)

/-- The node's own tag word, for rewriting. -/
theorem PlanAt.read0 {w : World} {mem : Memory} {p : Nat} {ws : List Nat} (h : PlanAt w mem p ws)
    (inside : 0 < ws.length) : readLE mem p 8 = (ws[0]!).toUInt64 := by
  simpa using h.read 0 rfl (by simpa using inside)

/-- The node's own tag word is readable. -/
theorem PlanAt.readable0 {w : World} {mem : Memory} {p : Nat} {ws : List Nat} (h : PlanAt w mem p ws)
    (inside : 0 < ws.length) : w.access p 8 = true := by
  simpa using h.readable 0 rfl (by simpa using inside)

/-! Evaluating the notation's expressions. -/

section
variable {w : World} {env : Env} {mem : Memory}

/-- A variable written by name is its value. -/
@[simp] theorem eval_varOf (v : Var) : eval w env mem (v : Expr) = some (env v.idx) := rfl

/-- A variable is its value. -/
@[simp] theorem eval_var (x : Nat) : eval w env mem (.var x) = some (env x) := rfl

/-- A numeral is its value. -/
@[simp] theorem eval_ofNat (n : Nat) :
    eval w env mem (no_index (OfNat.ofNat n : Expr)) = some (OfNat.ofNat n) := rfl

/-- A number cast to an expression is its value as a word. -/
@[simp] theorem eval_natCast (n : Nat) : eval w env mem (n : Expr) = some n.toUInt64 := rfl

/-- A constant is itself. -/
@[simp] theorem eval_lit (n : UInt64) : eval w env mem (.lit n) = some n := rfl

/-- A sum is the wrapped sum of its operands. -/
@[simp] theorem eval_add (a b : Expr) :
    eval w env mem (a + b) = (eval w env mem a).bind fun x => (eval w env mem b).map fun y => x + y := by
  simp only [HAdd.hAdd, Add.add, eval, aluResult, bind, pure]
  cases eval w env mem a <;> cases eval w env mem b <;> rfl

/-- A difference is the wrapped difference of its operands. -/
@[simp] theorem eval_sub (a b : Expr) :
    eval w env mem (a - b) = (eval w env mem a).bind fun x => (eval w env mem b).map fun y => x - y := by
  simp only [HSub.hSub, Sub.sub, eval, aluResult, bind, pure]
  cases eval w env mem a <;> cases eval w env mem b <;> rfl

/-- A product is the wrapped product of its operands. -/
@[simp] theorem eval_mul (a b : Expr) :
    eval w env mem (a * b) = (eval w env mem a).bind fun x => (eval w env mem b).map fun y => x * y := by
  simp only [HMul.hMul, Mul.mul, eval, aluResult, bind, pure]
  cases eval w env mem a <;> cases eval w env mem b <;> rfl

/-- A mask is the bitwise and of its operands. -/
@[simp] theorem eval_and (a b : Expr) :
    eval w env mem (a &&& b) = (eval w env mem a).bind fun x => (eval w env mem b).map fun y => x &&& y := by
  simp only [HAnd.hAnd, AndOp.and, eval, aluResult, bind, pure]
  cases eval w env mem a <;> cases eval w env mem b <;> rfl

/-- A join is the bitwise or of its operands. -/
@[simp] theorem eval_or (a b : Expr) :
    eval w env mem (a ||| b) = (eval w env mem a).bind fun x => (eval w env mem b).map fun y => x ||| y := by
  simp only [HOr.hOr, OrOp.or, eval, aluResult, bind, pure]
  cases eval w env mem a <;> cases eval w env mem b <;> rfl

/-- A quotient has a value only for a divisor other than zero. -/
@[simp] theorem eval_div (a b : Expr) :
    eval w env mem (a / b) =
      (eval w env mem a).bind fun x => (eval w env mem b).bind fun y => if y = 0 then none else some (x / y) := by
  simp only [HDiv.hDiv, Div.div, eval, bind, pure]
  cases eval w env mem a <;> cases eval w env mem b <;> simp [Option.bind]

/-- A remainder has a value only for a divisor other than zero. -/
@[simp] theorem eval_mod (a b : Expr) :
    eval w env mem (a % b) =
      (eval w env mem a).bind fun x => (eval w env mem b).bind fun y => if y = 0 then none else some (x % y) := by
  simp only [HMod.hMod, Mod.mod, eval, bind, pure]
  cases eval w env mem a <;> cases eval w env mem b <;> simp [Option.bind]

/-- A right shift by a constant below 64. -/
@[simp] theorem eval_shr (a : Expr) (k : Nat) :
    eval w env mem (.shr a k) = (eval w env mem a).bind fun x => if k < 64 then some (x >>> k.toUInt64) else none := by
  simp only [eval, bind, pure]

/-- Comparisons give one or zero. -/
@[simp] theorem eval_lt (a b : Expr) :
    eval w env mem (Expr.lt a b) =
      (eval w env mem a).bind fun x => (eval w env mem b).map fun y => if x < y then 1 else 0 := by
  simp only [Expr.lt, eval, Cond.holds, bind, pure]
  cases eval w env mem a <;> cases eval w env mem b <;> simp [Option.bind]

/-- One when the first is at most the second. -/
@[simp] theorem eval_le (a b : Expr) :
    eval w env mem (Expr.le a b) =
      (eval w env mem a).bind fun x => (eval w env mem b).map fun y => if x ≤ y then 1 else 0 := by
  simp only [Expr.le, eval, Cond.holds, bind, pure]
  cases eval w env mem a <;> cases eval w env mem b <;> simp [Option.bind, UInt64.le_iff_lt_or_eq, or_comm]

/-- One when both are equal. -/
@[simp] theorem eval_eq (a b : Expr) :
    eval w env mem (Expr.eq a b) =
      (eval w env mem a).bind fun x => (eval w env mem b).map fun y => if x = y then 1 else 0 := by
  simp only [Expr.eq, eval, Cond.holds, bind, pure]
  cases eval w env mem a <;> cases eval w env mem b <;> simp [Option.bind]

/-- One when they differ. -/
@[simp] theorem eval_ne (a b : Expr) :
    eval w env mem (Expr.ne a b) =
      (eval w env mem a).bind fun x => (eval w env mem b).map fun y => if x = y then 0 else 1 := by
  simp only [Expr.ne, eval, Cond.holds, bind, pure]
  cases eval w env mem a <;> cases eval w env mem b <;> simp [Option.bind]

/-- Loads read little-endian bytes from readable memory. -/
@[simp] theorem eval_ld (a : Expr) :
    eval w env mem (Expr.ld a) = (eval w env mem a).bind fun x =>
      if w.access x.toNat 8 then some (readLE mem x.toNat 8) else none := by
  simp only [Expr.ld, eval, Width.bytes, bind, pure]
  cases eval w env mem a <;> simp only [Option.bind] <;> split <;> simp_all

/-- Four bytes read from readable memory. -/
@[simp] theorem eval_ld4 (a : Expr) :
    eval w env mem (Expr.ld4 a) = (eval w env mem a).bind fun x =>
      if w.access x.toNat 4 then some (readLE mem x.toNat 4) else none := by
  simp only [Expr.ld4, eval, Width.bytes, bind, pure]
  cases eval w env mem a <;> simp only [Option.bind] <;> split <;> simp_all

/-- One byte read from readable memory. -/
@[simp] theorem eval_ld1 (a : Expr) :
    eval w env mem (Expr.ld1 a) = (eval w env mem a).bind fun x =>
      if w.access x.toNat 1 then some (readLE mem x.toNat 1) else none := by
  simp only [Expr.ld1, eval, Width.bytes, bind, pure]
  cases eval w env mem a <;> simp only [Option.bind] <;> split <;> simp_all

end

/-! Finding the functions. -/

/-- The module finds each function of the check under its name. -/
theorem Loaded.validate {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate" = some validateFn :=
  hm ("ssz_validate", validateFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.fail {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_fail" = some failFn :=
  hm ("ssz_validate_fail", failFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.skip {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_skip" = some skipFn :=
  hm ("ssz_validate_skip", skipFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.skipAll {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_skip_all" = some skipAllFn :=
  hm ("ssz_validate_skip_all", skipAllFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.width {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_width" = some widthFn :=
  hm ("ssz_validate_width", widthFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.fieldsWidth {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_fields_width" = some fieldsWidthFn :=
  hm ("ssz_validate_fields_width", fieldsWidthFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.leading {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_leading" = some leadingFn :=
  hm ("ssz_validate_leading", leadingFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.hasProbes {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_has_probes" = some hasProbesFn :=
  hm ("ssz_validate_has_probes", hasProbesFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.anyProbes {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_any_probes" = some anyProbesFn :=
  hm ("ssz_validate_any_probes", anyProbesFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.probe {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_probe" = some probeFn :=
  hm ("ssz_validate_probe", probeFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.records {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_records" = some recordsFn :=
  hm ("ssz_validate_records", recordsFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.fieldsProbe {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_fields_probe" = some fieldsProbeFn :=
  hm ("ssz_validate_fields_probe", fieldsProbeFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.delimited {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_delimited" = some delimitedFn :=
  hm ("ssz_validate_delimited", delimitedFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.spans {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_spans" = some spansFn :=
  hm ("ssz_validate_spans", spansFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.each {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_each" = some eachFn :=
  hm ("ssz_validate_each", eachFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.vector {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_vector" = some vectorFn :=
  hm ("ssz_validate_vector", vectorFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.list {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_list" = some listFn :=
  hm ("ssz_validate_list", listFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.inline {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_inline" = some inlineFn :=
  hm ("ssz_validate_inline", inlineFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.structSpans {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_struct_spans" = some structSpansFn :=
  hm ("ssz_validate_struct_spans", structSpansFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.nextBody {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_next_body" = some nextBodyFn :=
  hm ("ssz_validate_next_body", nextBodyFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.fields {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_fields" = some fieldsFn :=
  hm ("ssz_validate_fields", fieldsFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.struct {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_struct" = some structFn :=
  hm ("ssz_validate_struct", structFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.option {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_option" = some optionFn :=
  hm ("ssz_validate_option", optionFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.range {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_range" = some rangeFn :=
  hm ("ssz_validate_range", rangeFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.eq {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_eq" = some eqFn :=
  hm ("ssz_validate_eq", eqFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.bytes {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_bytes" = some bytesFn :=
  hm ("ssz_validate_bytes", bytesFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.compat {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_compat" = some compatFn :=
  hm ("ssz_validate_compat", compatFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.compatAll {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_compat_all" = some compatAllFn :=
  hm ("ssz_validate_compat_all", compatAllFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.optionsAgree {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_options_agree" = some optionsAgreeFn :=
  hm ("ssz_validate_options_agree", optionsAgreeFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.layouts {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_layouts" = some layoutsFn :=
  hm ("ssz_validate_layouts", layoutsFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.plan {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_plan" = some planFn :=
  hm ("ssz_validate_plan", planFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.planAll {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_plan_all" = some planAllFn :=
  hm ("ssz_validate_plan_all", planAllFn) (by simp [fns])

/-- The module finds this function of the check under its exported name. -/
theorem Loaded.pairs {m : Module} (hm : Loaded m) : m.fns.lookup "ssz_validate_pairs" = some pairsFn :=
  hm ("ssz_validate_pairs", pairsFn) (by simp [fns])

/-! Calls and their results. -/

/-- A call's arguments and result may be written in any equal form. -/
theorem Calls.congr {m : Module} {w : World} {f : String} {sp : Nat} {args args' : List UInt64} {mem mem' : Memory}
    {r r' : UInt64} (h : Calls m w f sp args mem r mem') (ha : args = args') (hr : r = r') :
    Calls m w f sp args' mem r' mem' := by
  subst ha hr; exact h

/-- A function's body, run below a frame of a known size, reaching its result is a call to it. -/
theorem Calls.body {m : Module} {w : World} {f : String} {sp : Nat} {args : List UInt64} {mem mem' : Memory}
    {fn : Fn} {r : UInt64} (k : Nat) (hf : m.fns.lookup f = some fn) (frame : fn.frame = k)
    (room : w.stackLo + 8 + 8 * k ≤ sp) (count : args.length = fn.params)
    (hb : Wp m w (sp - 8 - 8 * k) fn.body (entryEnv args) mem
      (fun env' mem'' => eval w env' mem'' fn.result = some r ∧ mem'' = mem')) :
    Calls m w f sp args mem r mem' := by
  subst frame; exact Calls.of_wp hf room count hb

/-- Two words equal as numbers below 2^64 are equal. -/
theorem u64_eq {a b : UInt64} (h : a.toNat = b.toNat) : a = b := UInt64.toNat_inj.mp h

/-- Proves an equation of words by their values as numbers. -/
macro "u64" : tactic => `(tactic| first | rfl | (apply u64_eq; simp [UInt64.toNat_add, UInt64.toNat_mul]; omega))

/--
Room on the stack for calls nested a number of levels deep, then a number of calls more.

A call takes at most 160 bytes of return address and frame, and a level at most 32 calls.
-/
abbrev Room (w : World) (sp level calls : Nat) : Prop := w.stackLo + level * 5120 + calls * 160 ≤ sp

/-! The plan's shape. -/

/-- The words of two lists of types are the words of each, one after the other. -/
theorem wordsAll_append : ∀ a b : List Desc, Plan.wordsAll (a ++ b) = Plan.wordsAll a ++ Plan.wordsAll b
  | [], _ => by simp [Plan.wordsAll]
  | d :: a, b => by simp [Plan.wordsAll, wordsAll_append a b, List.append_assoc]

/-- Every type writes at least its tag. -/
theorem words_length_pos (d : Desc) : 0 < (Plan.words d).length := by
  cases d <;> simp [Plan.words]

/-- A list of types splits around any one of them. -/
theorem wordsAll_split (fs : List Desc) (k : Nat) (hk : k < fs.length) :
    Plan.wordsAll fs = Plan.wordsAll (fs.take k) ++ Plan.words fs[k] ++ Plan.wordsAll (fs.drop (k + 1)) := by
  have h := List.take_append_drop k fs
  rw [List.drop_eq_getElem_cons hk] at h
  calc Plan.wordsAll fs = Plan.wordsAll (fs.take k ++ fs[k] :: fs.drop (k + 1)) := by rw [h]
    _ = _ := by rw [wordsAll_append]; simp only [Plan.wordsAll, List.append_assoc]

/-- One more type taken adds its words. -/
theorem wordsAll_take_succ (fs : List Desc) (k : Nat) (hk : k < fs.length) :
    Plan.wordsAll (fs.take (k + 1)) = Plan.wordsAll (fs.take k) ++ Plan.words fs[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, wordsAll_append]
  simp [Plan.wordsAll]

/-- A type in a list nests no deeper than the deepest of them. -/
theorem nesting_le_deepest : ∀ (fs : List Desc) (f : Desc), f ∈ fs → f.nesting ≤ Desc.deepestNesting fs
  | [], _, h => by simp at h
  | g :: rest, f, h => by
    simp only [List.mem_cons] at h
    simp only [Desc.deepestNesting]
    rcases h with rfl | h
    · omega
    · have := nesting_le_deepest rest f h; omega

/-! Reading the encoding. -/

/-- A byte of the encoding, read at its address. -/
theorem DataAt.byte {w : World} {mem : Memory} {base : Nat} {b : ByteArray} (h : DataAt w mem base b) (i : Nat)
    (hi : i < b.size) : readLE mem (base + i) 1 = (b.get! i).toUInt64 := by
  simp [readLE, h.2 i hi, ByteArray.get!, hi]
  rfl

/-! Words as numbers: every word the check computes is a number below 2^64, written as one. -/

section
variable {a b n : Nat}

/-- A number below 2^64 is the number of its word. -/
theorem toNat_ofNat_lt (h : a < 2 ^ 64) : (UInt64.ofNat a).toNat = a := by
  simp; omega

/-- The sum of two numbers' words is the word of their sum. -/
theorem ofNat_add_ofNat : UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b) := by
  apply u64_eq; simp [UInt64.toNat_add]

/-- A number's word plus a constant is the word of the sum. -/
theorem ofNat_add_lit : UInt64.ofNat a + (no_index (OfNat.ofNat n : UInt64)) = UInt64.ofNat (a + (OfNat.ofNat n : Nat)) :=
  ofNat_add_ofNat (a := a) (b := n)

/-- A constant plus a number's word is the word of the sum. -/
theorem lit_add_ofNat : (no_index (OfNat.ofNat n : UInt64)) + UInt64.ofNat a = UInt64.ofNat ((OfNat.ofNat n : Nat) + a) :=
  ofNat_add_ofNat (a := n) (b := a)

/-- The product of two numbers' words is the word of their product. -/
theorem ofNat_mul_ofNat : UInt64.ofNat a * UInt64.ofNat b = UInt64.ofNat (a * b) := by
  apply u64_eq; simp [UInt64.toNat_mul]

/-- A constant times a number's word is the word of the product. -/
theorem lit_mul_ofNat : (no_index (OfNat.ofNat n : UInt64)) * UInt64.ofNat a = UInt64.ofNat ((OfNat.ofNat n : Nat) * a) :=
  ofNat_mul_ofNat (a := n) (b := a)

/-- A number's word times a constant is the word of the product. -/
theorem ofNat_mul_lit : UInt64.ofNat a * (no_index (OfNat.ofNat n : UInt64)) = UInt64.ofNat (a * (OfNat.ofNat n : Nat)) :=
  ofNat_mul_ofNat (a := a) (b := n)

/-- A difference that does not wrap is the word of the difference. -/
theorem ofNat_sub_ofNat (h : b ≤ a) (ha : a < 2 ^ 64) : UInt64.ofNat a - UInt64.ofNat b = UInt64.ofNat (a - b) := by
  have hle : UInt64.ofNat b ≤ UInt64.ofNat a := by
    rw [UInt64.le_iff_toNat_le]; simp; omega
  apply u64_eq; rw [UInt64.toNat_sub_of_le _ _ hle]; simp; omega

/-- A number's word less a smaller constant is the word of the difference. -/
theorem ofNat_sub_lit (h : (OfNat.ofNat n : Nat) ≤ a) (ha : a < 2 ^ 64) :
    UInt64.ofNat a - (no_index (OfNat.ofNat n : UInt64)) = UInt64.ofNat (a - (OfNat.ofNat n : Nat)) := by
  have : (OfNat.ofNat n : UInt64) = UInt64.ofNat n := rfl
  rw [this]; exact ofNat_sub_ofNat h ha

/-- The quotient of words below 2^64 is the word of the quotient. -/
theorem ofNat_div_ofNat (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNat a / UInt64.ofNat b = UInt64.ofNat (a / b) := by
  have h1 : a / b < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
  apply u64_eq; simp only [UInt64.toNat_div, toNat_ofNat_lt ha, toNat_ofNat_lt hb, toNat_ofNat_lt h1]

/-- A word divided by a constant is the word of the quotient. -/
theorem ofNat_div_lit (ha : a < 2 ^ 64) (hn : (OfNat.ofNat n : Nat) < 2 ^ 64) :
    UInt64.ofNat a / (no_index (OfNat.ofNat n : UInt64)) = UInt64.ofNat (a / (OfNat.ofNat n : Nat)) := by
  have : (OfNat.ofNat n : UInt64) = UInt64.ofNat n := rfl
  rw [this]; exact ofNat_div_ofNat ha hn

/-- The remainder of words below 2^64 is the word of the remainder. -/
theorem ofNat_mod_ofNat (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNat a % UInt64.ofNat b = UInt64.ofNat (a % b) := by
  have h1 : a % b < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha
  apply u64_eq; simp only [UInt64.toNat_mod, toNat_ofNat_lt ha, toNat_ofNat_lt hb, toNat_ofNat_lt h1]

/-- A word modulo a constant is the word of the remainder. -/
theorem ofNat_mod_lit (ha : a < 2 ^ 64) (hn : (OfNat.ofNat n : Nat) < 2 ^ 64) :
    UInt64.ofNat a % (no_index (OfNat.ofNat n : UInt64)) = UInt64.ofNat (a % (OfNat.ofNat n : Nat)) := by
  have : (OfNat.ofNat n : UInt64) = UInt64.ofNat n := rfl
  rw [this]; exact ofNat_mod_ofNat ha hn

/-- Words of numbers below 2^64 are equal exactly when the numbers are. -/
theorem ofNat_eq_ofNat (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : UInt64.ofNat a = UInt64.ofNat b ↔ a = b := by
  constructor
  · intro h; have := congrArg UInt64.toNat h; simp at this; omega
  · rintro rfl; rfl

/-- A number's word equals a constant exactly when the number does. -/
theorem ofNat_eq_lit (ha : a < 2 ^ 64) (hn : (OfNat.ofNat n : Nat) < 2 ^ 64) :
    UInt64.ofNat a = (no_index (OfNat.ofNat n : UInt64)) ↔ a = (OfNat.ofNat n : Nat) := ofNat_eq_ofNat ha hn

/-- A constant equals a number's word exactly when it equals the number. -/
theorem lit_eq_ofNat (ha : a < 2 ^ 64) (hn : (OfNat.ofNat n : Nat) < 2 ^ 64) :
    (no_index (OfNat.ofNat n : UInt64)) = UInt64.ofNat a ↔ (OfNat.ofNat n : Nat) = a := ofNat_eq_ofNat hn ha

/-- Words of numbers below 2^64 compare as the numbers do. -/
theorem ofNat_lt_ofNat (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : UInt64.ofNat a < UInt64.ofNat b ↔ a < b := by
  rw [UInt64.lt_iff_toNat_lt, toNat_ofNat_lt ha, toNat_ofNat_lt hb]

/-- A number's word is below a constant exactly when the number is. -/
theorem ofNat_lt_lit (ha : a < 2 ^ 64) (hn : (OfNat.ofNat n : Nat) < 2 ^ 64) :
    UInt64.ofNat a < (no_index (OfNat.ofNat n : UInt64)) ↔ a < (OfNat.ofNat n : Nat) := ofNat_lt_ofNat ha hn

/-- A constant is below a number's word exactly when it is below the number. -/
theorem lit_lt_ofNat (ha : a < 2 ^ 64) (hn : (OfNat.ofNat n : Nat) < 2 ^ 64) :
    (no_index (OfNat.ofNat n : UInt64)) < UInt64.ofNat a ↔ (OfNat.ofNat n : Nat) < a := ofNat_lt_ofNat hn ha

/-- Words of numbers below 2^64 compare as the numbers do. -/
theorem ofNat_le_ofNat (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : UInt64.ofNat a ≤ UInt64.ofNat b ↔ a ≤ b := by
  rw [UInt64.le_iff_toNat_le, toNat_ofNat_lt ha, toNat_ofNat_lt hb]

/-- A number's word is at most a constant exactly when the number is. -/
theorem ofNat_le_lit (ha : a < 2 ^ 64) (hn : (OfNat.ofNat n : Nat) < 2 ^ 64) :
    UInt64.ofNat a ≤ (no_index (OfNat.ofNat n : UInt64)) ↔ a ≤ (OfNat.ofNat n : Nat) := ofNat_le_ofNat ha hn

/-- A constant is at most a number's word exactly when it is at most the number. -/
theorem lit_le_ofNat (ha : a < 2 ^ 64) (hn : (OfNat.ofNat n : Nat) < 2 ^ 64) :
    (no_index (OfNat.ofNat n : UInt64)) ≤ UInt64.ofNat a ↔ (OfNat.ofNat n : Nat) ≤ a := ofNat_le_ofNat hn ha

/-- A callee's variable on entry is its argument. -/
theorem entryEnv_getD (args : List UInt64) (i : Nat) : entryEnv args i = args.getD i 0 := rfl

/-- A variable just given a value has it. -/
theorem assign_same (env : Env) (x : Nat) (v : UInt64) : Asm.assign env x v x = v := by simp [Asm.assign]

/-- Any other variable keeps its value. -/
theorem assign_other (env : Env) (x y : Nat) (v : UInt64) (h : y ≠ x) : Asm.assign env x v y = env y := by
  simp [Asm.assign, h]

/-- An optional bound is always two words. -/
@[simp] theorem bound_length (l : Option Nat) : (Plan.bound l).length = 2 := by cases l <;> rfl

/-- Zero masks anything to zero. -/
theorem zero_band (x : UInt64) : (0 &&& x) = 0 := by apply u64_eq; simp
/-- Anything masked by zero is zero. -/
theorem band_zero (x : UInt64) : (x &&& 0) = 0 := by apply u64_eq; simp
/-- One masked by one is one. -/
theorem one_band_one : ((1 : UInt64) &&& 1) = 1 := by decide
/-- Zero joined with anything is that thing. -/
theorem zero_bor (x : UInt64) : (0 ||| x) = x := by apply u64_eq; simp
/-- Anything joined with zero is itself. -/
theorem bor_zero (x : UInt64) : (x ||| 0) = x := by apply u64_eq; simp
/-- One joined with one is one. -/
theorem one_bor_one : ((1 : UInt64) ||| 1) = 1 := by decide

/-- A word chosen by a condition, masked. -/
theorem ite_band (c : Prop) [Decidable c] (a b d : UInt64) :
    ((if c then a else b) &&& d) = if c then a &&& d else b &&& d := by split <;> rfl

/-- A word masked by one chosen by a condition. -/
theorem band_ite (c : Prop) [Decidable c] (a b d : UInt64) :
    (d &&& (if c then a else b)) = if c then d &&& a else d &&& b := by split <;> rfl

/-- A word chosen by a condition, joined. -/
theorem ite_bor (c : Prop) [Decidable c] (a b d : UInt64) :
    ((if c then a else b) ||| d) = if c then a ||| d else b ||| d := by split <;> rfl

/-- A word joined with one chosen by a condition. -/
theorem bor_ite (c : Prop) [Decidable c] (a b d : UInt64) :
    (d ||| (if c then a else b)) = if c then d ||| a else d ||| b := by split <;> rfl

/-- Two conditions of zero or one, both holding. -/
theorem ite_and_ite (c d : Prop) [Decidable c] [Decidable d] :
    ((if c then 1 else 0 : UInt64) &&& (if d then 1 else 0)) = if c ∧ d then 1 else 0 := by
  by_cases hc : c <;> by_cases hd : d <;> simp [hc, hd]

/-- Two conditions of zero or one, either holding. -/
theorem ite_or_ite (c d : Prop) [Decidable c] [Decidable d] :
    ((if c then 1 else 0 : UInt64) ||| (if d then 1 else 0)) = if c ∨ d then 1 else 0 := by
  by_cases hc : c <;> by_cases hd : d <;> simp [hc, hd]

end

/--
Runs a program forward by rewriting: the notation unfolded, each expression evaluated, each word kept as a number.

Side conditions on sizes are left to omega, from the facts in context.
-/
macro "wsimp" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (disch := omega) [-UInt64.ofNat_add, -UInt64.ofNat_mul, ofNat_add_ofNat, ofNat_add_lit,
      lit_add_ofNat, ofNat_mul_ofNat, lit_mul_ofNat, ofNat_mul_lit, ofNat_sub_ofNat, ofNat_sub_lit, ofNat_div_ofNat,
      ofNat_div_lit, ofNat_mod_ofNat, ofNat_mod_lit, toNat_ofNat_lt, ofNat_eq_ofNat, ofNat_eq_lit, lit_eq_ofNat,
      ofNat_lt_ofNat, ofNat_lt_lit, lit_lt_ofNat, ofNat_le_ofNat, ofNat_le_lit, lit_le_ofNat, ite_and_ite,
      ite_or_ite, Nat.mod_eq_of_lt, Ssz.Native.Ir.Stmt.assign, Ssz.Native.Ir.Stmt.ifElse, Ssz.Native.Ir.Stmt.when,
      Ssz.Native.Ir.Stmt.callInto, Ssz.Native.Ir.Stmt.while_, Ssz.Native.Driver.Validate.word,
      Ssz.Native.Driver.Validate.both, Ssz.Native.Driver.Validate.either, Ssz.Native.Driver.Validate.fail,
      Ssz.Native.Driver.Validate.code, Ssz.Native.Ir.entryEnv, Ssz.Native.Asm.assign, $args,*])

/-- Evaluates an expression to a normal form, naming the value it has. -/
macro "wonly" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (simp (config := { decide := true }) (disch := omega) only [eval_var, eval_ofNat, eval_natCast, eval_lit,
      eval_add, eval_sub, eval_mul, eval_and, eval_or, eval_div, eval_mod, eval_shr, eval_lt, eval_le, eval_eq,
      eval_ne, eval_ld, eval_ld4, eval_ld1, Option.bind_some, Option.map_some, entryEnv_getD, List.getD_cons_zero,
      List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind, bound_length,
      List.getD_cons_succ, assign_same, assign_other, ofNat_add_ofNat, ofNat_add_lit, lit_add_ofNat,
      ofNat_mul_ofNat, lit_mul_ofNat, ofNat_mul_lit, ofNat_sub_ofNat, ofNat_sub_lit, ofNat_div_ofNat, ofNat_div_lit,
      ofNat_mod_ofNat, ofNat_mod_lit, toNat_ofNat_lt, ofNat_eq_ofNat, ofNat_eq_lit, lit_eq_ofNat, ofNat_lt_ofNat,
      ofNat_lt_lit, lit_lt_ofNat, ofNat_le_ofNat, ofNat_le_lit, lit_le_ofNat, ite_and_ite, ite_or_ite, ite_band, band_ite, ite_bor, bor_ite, zero_band, band_zero, one_band_one, zero_bor,
      bor_zero, one_bor_one, if_true,
      if_false, ite_not, Ssz.Native.Driver.Validate.word, Ssz.Native.Driver.Validate.both,
      Ssz.Native.Driver.Validate.either, Ssz.Native.Driver.Validate.code, Ssz.Native.Driver.Validate.none_,
      Ssz.Native.Driver.Validate.bound32, Var.idx, UInt64.toNat_zero, UInt64.toNat_one, Width.bytes, true_and, and_true, ite_self, beq_iff_eq, List.cons_append, List.nil_append, List.append_nil,
      List.take_succ_cons, List.take_zero, List.take_nil,
      ctorIdx_overLimit, ctorIdx_scope, ctorIdx_scopeTooSmall, ctorIdx_scopeUndivided, ctorIdx_scopeWidthless, ctorIdx_firstOffset, ctorIdx_offsetUnordered, ctorIdx_offsetPastScope, ctorIdx_offsetUnaligned, ctorIdx_offsetBelowTable, ctorIdx_notABit, ctorIdx_paddingBits, ctorIdx_emptyEncoding, ctorIdx_noDelimiter, ctorIdx_trailingZeros, ctorIdx_noSelector, ctorIdx_unknownSelector, ctorIdx_unionSelectorRange, ctorIdx_offsetOverflow, $args,*]))

/-- Evaluates an expression to a normal form, naming the value it has. -/
macro "wev" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (wonly [$args,*]) <;> rfl)

/--
Takes one step of a block: an assignment, or a branch whose condition evaluates to a constant either way.

Calls and loops are left to the proof, which knows what they compute.
-/
macro "wstep" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    try show Ssz.Native.Ir.Wp _ _ _ (Ssz.Native.Ir.Stmt.block _) _ _ _
    first
    | (refine Ssz.Native.Ir.Wp.set (v := ?v) ?h ?k
       case h => ((wev [$args,*]); done))
    | (refine Ssz.Native.Ir.Wp.ifElse_f ?h ?k
       case h => ((wonly [$args,*]); done))
    | (refine Ssz.Native.Ir.Wp.ifElse_t (v := ?v) ?h ?nz ?k
       case h => ((wev [$args,*]); done)
       case nz => ((wonly [$args,*]); done))
    | (refine Ssz.Native.Ir.Wp.when_f ?h ?k
       case h => ((wonly [$args,*]); done))
    | (refine Ssz.Native.Ir.Wp.when_t (v := ?v) ?h ?nz ?k
       case h => ((wev [$args,*]); done)
       case nz => ((wonly [$args,*]); done))
    | refine Ssz.Native.Ir.Wp.done ?_))

/-- Takes steps of a block for as long as one can be taken. -/
macro "wsteps" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| repeat (wstep [$args,*]; try simp only [List.cons_append, List.nil_append, List.append_nil]))

/-- Takes a call at the head of a block, by what a proved call computes. -/
macro "wcall" h:term:max "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    try show Ssz.Native.Ir.Wp _ _ _ (Ssz.Native.Ir.Stmt.block _) _ _ _
    refine Ssz.Native.Ir.Wp.call (values := ?vs) ?hv (Calls.congr $h ?ha rfl) ?k
    case hv => ((wev [$args,*]); done)
    case ha => first | with_reducible rfl | ((wonly [List.cons.injEq, and_true, $args,*]) <;> omega)))

/-- Settles what a body leaves: its result, and its memory. -/
macro "wfin" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (wonly [Option.some.injEq, and_true, List.length_append, List.length_cons, List.length_nil,
      List.length_map, $args,*]) <;> (try omega) <;> (try simp))

end Ssz.Native.Driver.Validate

