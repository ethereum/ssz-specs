import SszNative.Asm.Instr

/-!
A small imperative language that compiles to x86-64.

Drivers are written in it rather than in assembly, and one proof of the compiler covers them all.

Every value is a 64-bit word.
A function has numbered variables, its parameters first.
Memory is the machine's own, byte-addressed.
-/

namespace Ssz.Native.Ir

open Ssz.Native.Asm (Alu Cond Width)

/-- An expression, evaluated to one 64-bit word. -/
inductive Expr where
  /-- A constant. -/
  | lit (n : UInt64)
  /-- A variable of the running function. -/
  | var (x : Nat)
  /-- An integer operation, wrapping modulo 2^64. -/
  | op (o : Alu) (a b : Expr)
  /-- A left shift by a constant below 64. -/
  | shl (a : Expr) (k : Nat)
  /-- A right shift by a constant below 64. -/
  | shr (a : Expr) (k : Nat)
  /-- The unsigned quotient, undefined for a zero divisor. -/
  | div (a b : Expr)
  /-- The unsigned remainder, undefined for a zero divisor. -/
  | mod (a b : Expr)
  /-- Bytes read from an address, little-endian and zero-extended. -/
  | load (w : Width) (a : Expr)
  /-- One when an unsigned comparison holds, and zero otherwise. -/
  | cmp (c : Cond) (a b : Expr)
  deriving Repr, Inhabited

/-- A statement. -/
inductive Stmt where
  /-- Nothing. -/
  | skip
  /-- Give a variable a value. -/
  | set (x : Nat) (e : Expr)
  /-- Write a value's low bytes to an address. -/
  | store (w : Width) (a v : Expr)
  /-- One statement, then another. -/
  | seq (a b : Stmt)
  /-- The first branch when the condition is not zero, and the second otherwise. -/
  | ite (c : Expr) (t e : Stmt)
  /-- The body, again and again, while the condition is not zero. -/
  | loop (c : Expr) (body : Stmt)
  /-- Call a function by name with up to six arguments, and keep its result in a variable. -/
  | call (f : String) (args : List Expr) (dst : Nat)
  deriving Repr, Inhabited

/-- A function: its parameter count, its variable count, its body, and the result its body leaves. -/
structure Fn where
  /-- Variables numbered below this hold the arguments on entry. -/
  params : Nat
  /-- How many variables the function has, parameters included. -/
  vars : Nat
  /-- What the function does. -/
  body : Stmt
  /-- What it returns, evaluated after the body. -/
  result : Expr
  deriving Repr, Inhabited

/-- Statements one after the other. -/
def Stmt.block : List Stmt → Stmt
  | [] => .skip
  | [s] => s
  | s :: rest => .seq s (Stmt.block rest)

end Ssz.Native.Ir
