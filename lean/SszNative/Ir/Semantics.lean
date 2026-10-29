import SszNative.Ir.Syntax
import SszNative.Asm.Machine

/-!
What a program of the small language means.

Execution takes fuel, so a definition of it terminates.
A run that needs more fuel than it has, divides by zero, or reads or writes outside the program's memory has no meaning.
The compiler's proof only speaks of runs that have one.

The stack belongs to the compiled code.
The language cannot see it: a load or store landing on it has no meaning, and neither does a call too deep for it.
-/

namespace EthLib.Consensus.Ssz.Native.Ir

open EthLib.Consensus.Ssz.Native.Asm

/-- Variables, by number. -/
abbrev Env := Nat → UInt64

/-- Memory, one byte per address. -/
abbrev Memory := Nat → UInt8

/-- What a run cannot change: where the stack lies, and the processor. -/
structure World where
  /-- The lowest address the stack may grow down to. -/
  stackLo : Nat
  /-- One past the highest stack address, the entry caller's return address included. -/
  stackHi : Nat
  /-- What cpuid answers. -/
  cpu : Cpu

/-- Whether bytes from an address lie in memory a program may use: below the address bound, and off the stack. -/
def World.access (w : World) (a n : Nat) : Bool :=
  a + n ≤ addressBound && (a + n ≤ w.stackLo || w.stackHi ≤ a)

/-- A routine written outside the language, given by what it computes. -/
structure Extern where
  /--
  The result word and the memory after, for arguments, a memory, and the stack pointer at the call.

  None marks a call outside what the routine is proved for.
  -/
  run : World → (sp : Nat) → List UInt64 → Memory → Option (UInt64 × Memory)

/-- Functions in the language, and routines outside it, each under its exported name. -/
structure Module where
  /-- The functions written in the language. -/
  fns : List (String × Fn)
  /-- The routines written outside it. -/
  ext : List (String × Extern)

/-- The temporary slots an expression's evaluation needs, beyond the variables. -/
def Expr.temps : Expr → Nat
  | .lit _ | .var _ => 0
  | .shl a _ | .shr a _ | .load _ a => a.temps
  -- The first operand waits in a slot while the second is evaluated in the slots above it.
  | .op _ a b | .div a b | .mod a b | .cmp _ a b => max a.temps (b.temps + 1)

/-- The slots arguments need from a position up: argument j waits in its slot while those after it are evaluated above. -/
def argsTemps : List Expr → Nat → Nat
  | [], i => i
  | a :: rest, i => max (a.temps + i) (argsTemps rest (i + 1))

/-- The temporary slots a statement needs, beyond the variables. -/
def Stmt.temps : Stmt → Nat
  | .skip => 0
  | .set _ e => e.temps
  | .store _ a v => max a.temps (v.temps + 1)
  | .seq a b => max a.temps b.temps
  | .ite c t e => max c.temps (max t.temps e.temps)
  | .loop c body => max c.temps body.temps
  | .call _ args _ => argsTemps args 0

/--
The words a function's frame holds: its variables and its temporaries, made odd.

The return address and an odd number of words keep the stack 16-byte aligned at every call the function makes.
-/
def Fn.frame (f : Fn) : Nat :=
  let n := f.vars + max f.body.temps f.result.temps
  if n % 2 = 1 then n else n + 1

/-- The value of an expression, if it has one. -/
def eval (w : World) (env : Env) (mem : Memory) : Expr → Option UInt64
  | .lit n => some n
  | .var x => some (env x)
  | .op o a b => do
    let x ← eval w env mem a
    let y ← eval w env mem b
    return (aluResult o x y).1
  | .shl a k => do
    let x ← eval w env mem a
    if k < 64 then return x <<< k.toUInt64 else none
  | .shr a k => do
    let x ← eval w env mem a
    if k < 64 then return x >>> k.toUInt64 else none
  | .div a b => do
    let x ← eval w env mem a
    let y ← eval w env mem b
    if y == 0 then none else return x / y
  | .mod a b => do
    let x ← eval w env mem a
    let y ← eval w env mem b
    if y == 0 then none else return x % y
  | .load wd a => do
    let x ← eval w env mem a
    if w.access x.toNat wd.bytes then return readLE mem x.toNat wd.bytes else none
  | .cmp c a b => do
    let x ← eval w env mem a
    let y ← eval w env mem b
    return if c.holds (x == y) (x < y) then 1 else 0

/-- A callee's variables on entry: its arguments, then zeros. -/
def entryEnv (args : List UInt64) : Env :=
  fun i => args.getD i 0

/--
The variables and memory after a statement, if the run has a meaning.

The stack pointer is the base of the running function's frame.
A call to a function of the module puts the callee's frame below it, under the return address.
-/
def exec (m : Module) (w : World) : (fuel : Nat) → (sp : Nat) → Env → Memory → Stmt → Option (Env × Memory)
  | 0, _, _, _, _ => none
  | fuel + 1, sp, env, mem, stmt =>
    match stmt with
    | .skip => some (env, mem)
    | .set x e => (eval w env mem e).map fun v => (assign env x v, mem)
    | .store wd a v => do
      let x ← eval w env mem a
      let y ← eval w env mem v
      if w.access x.toNat wd.bytes then return (env, store mem x.toNat wd.bytes (qwordByte y)) else none
    | .seq a b => do
      let (env, mem) ← exec m w fuel sp env mem a
      exec m w fuel sp env mem b
    | .ite c t e => do
      let v ← eval w env mem c
      if v != 0 then exec m w fuel sp env mem t else exec m w fuel sp env mem e
    | .loop c body => do
      let v ← eval w env mem c
      if v == 0 then return (env, mem)
      let (env, mem) ← exec m w fuel sp env mem body
      exec m w fuel sp env mem (.loop c body)
    | .call f args dst => do
      let values ← args.mapM (eval w env mem)
      let called : Option (UInt64 × Memory) := match m.fns.lookup f with
        | some fn =>
          -- The callee's frame sits under the return address, and must stay above the stack's floor.
          if w.stackLo + 8 + 8 * fn.frame ≤ sp && values.length == fn.params then do
            let (env', mem') ← exec m w fuel (sp - 8 - 8 * fn.frame) (entryEnv values) mem fn.body
            let r ← eval w env' mem' fn.result
            return (r, mem')
          else none
        | none =>
          match m.ext.lookup f with
          -- A routine outside the language needs room for the return address.
          | some e => if w.stackLo + 8 ≤ sp then e.run w sp values mem else none
          | none => none
      let (r, mem) ← called
      return (assign env dst r, mem)

end EthLib.Consensus.Ssz.Native.Ir
