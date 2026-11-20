import SszNative.Ir.Semantics

/-!
The compiler from the small language to x86-64 instructions.

Each function becomes one routine following the System V calling convention, so compiled code calls kernels,
kernels need nothing from it, and any language with a C foreign interface can call it.

The frame keeps every variable and temporary in memory, at a fixed distance from the stack pointer:

```text
    rsp + 8 * (vars + t)   temporary t
    rsp + 8 * x            variable x
    rsp                    the frame's base, which the body never moves
```

An expression leaves its value in rax and may clobber rcx and rdx.
A statement leaves no value in any register, so a call clobbering every caller-saved register is harmless.
The code touches only caller-saved registers, so it keeps every register the convention keeps.
-/

namespace EthLib.Consensus.Ssz.Native.Ir

open EthLib.Consensus.Ssz.Native.Asm

/-- The frame slot holding a word, by its index from the base. -/
def slot (k : Nat) : Asm.Mem :=
  ⟨.rsp, 8 * k⟩

/-- The register the convention passes an argument in, by its position. -/
def argReg : Nat → Gpr
  | 0 => .rdi | 1 => .rsi | 2 => .rdx | 3 => .rcx | 4 => .r8 | _ => .r9

/--
Two operands' code joined: the first operand parked in a slot while the second runs, then both in rax and rcx.

The finish then combines them.
-/
def joinOperands (vars d : Nat) (first second finish : List Instr) : List Instr :=
  first ++ [.store .b8 (slot (vars + d)) .rax] ++ second ++ [.movReg .rcx .rax, .load .b8 .rax (slot (vars + d))] ++
    finish

/--
The code of an expression, placed at an instruction index, with its first free temporary slot.

The variable count fixes where the temporaries start.
-/
def compileExpr (vars : Nat) (pc : Nat) : Expr → (depth : Nat) → List Instr
  | .lit n, _ => [.movImm .rax n]
  | .var x, _ => [.load .b8 .rax (slot x)]
  | .shl a k, d => compileExpr vars pc a d ++ [.shlImm .rax k]
  | .shr a k, d => compileExpr vars pc a d ++ [.shrImm .rax k]
  | .load w a, d => compileExpr vars pc a d ++ [.load w .rax ⟨.rax, 0⟩]
  | .op o a b, d =>
    let first := compileExpr vars pc a d
    joinOperands vars d first (compileExpr vars (pc + first.length + 1) b (d + 1)) [.alu o .rax .rcx]
  -- The dividend's high half is zero, so the quotient always fits.
  | .div a b, d =>
    let first := compileExpr vars pc a d
    joinOperands vars d first (compileExpr vars (pc + first.length + 1) b (d + 1)) [.zeroReg .rdx, .div .rcx]
  | .mod a b, d =>
    let first := compileExpr vars pc a d
    joinOperands vars d first (compileExpr vars (pc + first.length + 1) b (d + 1))
      [.zeroReg .rdx, .div .rcx, .movReg .rax .rdx]
  -- One is the default, and the branch skips the zero when the condition holds.
  | .cmp c a b, d =>
    let first := compileExpr vars pc a d
    let core := joinOperands vars d first (compileExpr vars (pc + first.length + 1) b (d + 1))
      [.cmp .rax .rcx, .movImm .rax 1]
    core ++ [.jcc c (pc + core.length + 2), .movImm .rax 0]

/-- The code of the arguments of a call: each one evaluated and parked in its slot, then all moved to registers. -/
def compileArgs (vars : Nat) (pc : Nat) : (args : List Expr) → (i : Nat) → List Instr
  | [], _ => []
  | a :: rest, i =>
    let here := compileExpr vars pc a i ++ [.store .b8 (slot (vars + i)) .rax]
    here ++ compileArgs vars (pc + here.length) rest (i + 1)

/-- Parked arguments moved into the registers the convention passes them in. -/
def argLoads (vars n : Nat) : List Instr :=
  (List.range n).map fun i => .load .b8 (argReg i) (slot (vars + i))

/-- The code of a statement, placed at an instruction index. -/
def compileStmt (vars : Nat) (pc : Nat) : Stmt → List Instr
  | .skip => []
  | .set x e => compileExpr vars pc e 0 ++ [.store .b8 (slot x) .rax]
  | .store w a v =>
    let first := compileExpr vars pc a 0 ++ [.store .b8 (slot vars) .rax]
    first ++ compileExpr vars (pc + first.length) v 1 ++
      [.movReg .rcx .rax, .load .b8 .rax (slot vars), .store w ⟨.rax, 0⟩ .rcx]
  | .seq a b =>
    let first := compileStmt vars pc a
    first ++ compileStmt vars (pc + first.length) b
  | .ite c t e =>
    let cond := compileExpr vars pc c 0
    let yes := compileStmt vars (pc + cond.length + 2) t
    let elsePc := pc + cond.length + 2 + yes.length + 1
    let no := compileStmt vars elsePc e
    cond ++ [.test .rax, .jz elsePc] ++ yes ++ [.jmp (elsePc + no.length)] ++ no
  | .loop c body =>
    let cond := compileExpr vars pc c 0
    let inner := compileStmt vars (pc + cond.length + 2) body
    cond ++ [.test .rax, .jz (pc + cond.length + 2 + inner.length + 1)] ++ inner ++ [.jmp pc]
  | .call f args dst =>
    let parked := compileArgs vars pc args 0
    parked ++ argLoads vars args.length ++ [.call f, .store .b8 (slot dst) .rax]

/-- Registers stored to consecutive slots from a first one. -/
def slotStores (k n : Nat) (reg : Nat → Gpr) : List Instr :=
  (List.range n).map fun i => .store .b8 (slot (k + i)) (reg i)

/-- The entry of a function: its frame, its arguments stored, and its other variables zeroed. -/
def prologue (f : Fn) : List Instr :=
  [.subImm .rsp (8 * f.frame)] ++ slotStores 0 f.params argReg ++ [.zeroReg .rax] ++
    slotStores f.params (f.vars - f.params) (fun _ => .rax)

/-- A function as a routine: the prologue, the body, the result into rax, and the frame released. -/
def compileFn (f : Fn) : Array Instr :=
  let entry := prologue f
  let body := compileStmt f.vars entry.length f.body
  let result := compileExpr f.vars (entry.length + body.length) f.result 0
  (entry ++ body ++ result ++ [Instr.addImm .rsp (8 * f.frame), Instr.ret]).toArray

end EthLib.Consensus.Ssz.Native.Ir
