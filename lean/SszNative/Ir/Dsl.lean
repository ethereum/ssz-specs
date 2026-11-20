import SszNative.Ir.Syntax

/-!
Notation for writing programs of the small language as readable code.

Variables are named values of their own type, so a number in an expression is always a constant.
-/

namespace EthLib.Consensus.Ssz.Native.Ir

open EthLib.Consensus.Ssz.Native.Asm (Alu Cond Width)

/-- A variable of a function, by its number. -/
structure Var where
  /-- The variable's number. -/
  idx : Nat

instance : Coe Var Expr := ⟨fun v => .var v.idx⟩

instance (n : Nat) : OfNat Expr n := ⟨.lit (OfNat.ofNat n)⟩

instance : NatCast Expr := ⟨fun n => .lit n.toUInt64⟩

instance : Add Expr := ⟨.op .add⟩
instance : Sub Expr := ⟨.op .sub⟩
instance : Mul Expr := ⟨.op .mul⟩
instance : Div Expr := ⟨.div⟩
instance : Mod Expr := ⟨.mod⟩
instance : AndOp Expr := ⟨.op .and⟩
instance : OrOp Expr := ⟨.op .or⟩
instance : XorOp Expr := ⟨.op .xor⟩

namespace Expr

/-- One when the first is below the second. -/
def lt (a b : Expr) : Expr := .cmp .b a b

/-- One when the first is at most the second. -/
def le (a b : Expr) : Expr := .cmp .be a b

/-- One when both are equal. -/
def eq (a b : Expr) : Expr := .cmp .e a b

/-- One when they differ. -/
def ne (a b : Expr) : Expr := .cmp .ne a b

/-- The eight bytes at an address. -/
def ld (a : Expr) : Expr := .load .b8 a

/-- The byte at an address. -/
def ld1 (a : Expr) : Expr := .load .b1 a

/-- The four bytes at an address. -/
def ld4 (a : Expr) : Expr := .load .b4 a

end Expr

namespace Stmt

/-- Give a variable a value. -/
def assign (v : Var) (e : Expr) : Stmt := .set v.idx e

/-- Store eight bytes. -/
def st (a v : Expr) : Stmt := .store .b8 a v

/-- Store one byte. -/
def st1 (a v : Expr) : Stmt := .store .b1 a v

/-- Run the body while the condition is not zero. -/
def while_ (c : Expr) (body : List Stmt) : Stmt := .loop c (.block body)

/-- The first statements when the condition is not zero, and nothing otherwise. -/
def when (c : Expr) (body : List Stmt) : Stmt := .ite c (.block body) .skip

/-- The first statements when the condition is not zero, and the second otherwise. -/
def ifElse (c : Expr) (yes no : List Stmt) : Stmt := .ite c (.block yes) (.block no)

/-- Call a function and keep its result. -/
def callInto (v : Var) (f : String) (args : List Expr) : Stmt := .call f args v.idx

end Stmt

@[inherit_doc Stmt.assign] infix:25 " ::= " => Stmt.assign

end EthLib.Consensus.Ssz.Native.Ir
