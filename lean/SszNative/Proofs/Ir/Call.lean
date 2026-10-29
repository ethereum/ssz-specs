import SszNative.Proofs.Ir.Frame
import SszNative.Proofs.Ir.Fuel

/-!
What a call means, and what the code of a call must guarantee to the code around it.

The guarantee is the same for compiled functions and for routines written by hand, so either can call either.
-/

namespace Ssz.Native.Ir

open Ssz.Native.Asm

/-- What calling a function or a routine of a module means, with some fuel, from a stack pointer. -/
def callSpec (m : Module) (w : World) (fuel : Nat) (f : String) (sp : Nat) (values : List UInt64) (mem : Memory) :
    Option (UInt64 × Memory) :=
  match m.fns.lookup f with
  | some fn =>
    if w.stackLo + 8 + 8 * fn.frame ≤ sp && values.length == fn.params then do
      let (env', mem') ← exec m w fuel (sp - 8 - 8 * fn.frame) (entryEnv values) mem fn.body
      let r ← eval w env' mem' fn.result
      return (r, mem')
    else none
  | none =>
    match m.ext.lookup f with
    | some e => if w.stackLo + 8 ≤ sp then e.run w sp values mem else none
    | none => none

/-- A call statement runs its arguments, then the call. -/
theorem exec_call (m : Module) (w : World) (fuel sp : Nat) (env : Env) (mem : Memory) (f : String)
    (args : List Expr) (dst : Nat) :
    exec m w (fuel + 1) sp env mem (.call f args dst) = (do
      let values ← args.mapM (eval w env mem)
      let (r, mem) ← callSpec m w fuel f sp values mem
      return (assign env dst r, mem)) := by
  rfl

/--
What a call instruction to a name guarantees, for a meaning of the call.

From the call, the machine comes back to the next instruction with the result in rax.
Memory off the stack is what the meaning says.
The stack at and above the stack pointer, the kept registers, and the stack pointer itself are as before.
-/
def CallOk (image : Image) (w : World) (name : String)
    (spec : Nat → List UInt64 → Memory → Option (UInt64 × Memory)) : Prop :=
  ∀ (r : Nat) (s : State) (sp : Nat) (args : List UInt64) (ir ir' : Memory) (res : UInt64),
    (image.code r)[s.pc]? = some (.call name) → s.status = .running → s.cpu = w.cpu →
    r < image.size → r < 2 ^ 31 → s.pc + 1 < 2 ^ 32 →
    s.gpr .rsp = sp.toUInt64 → sp ≤ w.stackHi → w.stackHi ≤ addressBound →
    args.length ≤ 6 → (∀ i < args.length, s.gpr (argReg i) = args.getD i 0) →
    (∀ a, a < w.stackLo ∨ w.stackHi ≤ a → s.mem a = ir a) →
    spec sp args ir = some (res, ir') →
    ∃ s', Reaches image r s s' ∧ s'.pc = s.pc + 1 ∧ s'.gpr .rax = res ∧ s'.gpr .rsp = sp.toUInt64 ∧
      (∀ g ∈ keptRegs, s'.gpr g = s.gpr g) ∧ (∀ a, a < w.stackLo ∨ w.stackHi ≤ a → s'.mem a = ir' a) ∧
      (∀ a, sp ≤ a → a < w.stackHi → s'.mem a = s.mem a) ∧ s'.cpu = s.cpu ∧ s'.status = .running

end Ssz.Native.Ir
