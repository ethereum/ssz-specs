import SszNative.Ir.Syntax

/-!
Which programs fit the compiler's assumptions.

A function fits when it reads and writes only its own variables, takes at most six parameters, and passes at most six
arguments to each call.
These checks are plain functions, so a linker can run them before it trusts the compiled code.
-/

namespace Ssz.Native.Ir

/-- Whether every variable an expression reads is below a count. -/
def Expr.varsBelow (n : Nat) : Expr → Bool
  | .lit _ => true
  | .var x => x < n
  | .shl a _ | .shr a _ | .load _ a => a.varsBelow n
  | .op _ a b | .div a b | .mod a b | .cmp _ a b => a.varsBelow n && b.varsBelow n

/-- Whether a statement reads and writes only the function's variables, and passes at most six arguments. -/
def Stmt.wf (n : Nat) : Stmt → Bool
  | .skip => true
  | .set x e => x < n && e.varsBelow n
  | .store _ a v => a.varsBelow n && v.varsBelow n
  | .seq a b => a.wf n && b.wf n
  | .ite c t e => c.varsBelow n && t.wf n && e.wf n
  | .loop c body => c.varsBelow n && body.wf n
  | .call _ args dst => args.length ≤ 6 && dst < n && args.all (·.varsBelow n)

/-- Whether a function's variables, parameters, body and result fit the compiler's assumptions. -/
def Fn.wf (f : Fn) : Bool :=
  f.params ≤ 6 && f.params ≤ f.vars && f.body.wf f.vars && f.result.varsBelow f.vars

end Ssz.Native.Ir
