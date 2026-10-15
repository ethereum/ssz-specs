import Asm.Machine

/-! Printing a program as GNU assembler source for RV64I. -/

namespace Ssz.Asm

/-- The ABI name of a register, as the assembler and debuggers spell it. -/
def Reg.name (r : Reg) : String :=
  -- The standard calling convention names, in register-index order.
  let names := #["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1", "a0", "a1", "a2",
    "a3", "a4", "a5", "a6", "a7", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11",
    "t3", "t4", "t5", "t6"]
  names[r.val]!

/-- The label an instruction index gets inside one routine. -/
def label (routine : String) (target : Nat) : String :=
  s!".L{routine}_{target}"

/-- One instruction as an assembler line, with branch targets printed as labels. -/
def Instr.render (routine : String) : Instr → String
  -- Upper immediates print unsigned, as the assembler expects 0 to 0xfffff.
  | .lui rd imm => s!"lui {rd.name}, {imm.toNat}"
  -- Every other immediate is a signed 12-bit value.
  | .addi rd rs imm => s!"addi {rd.name}, {rs.name}, {imm.toInt}"
  | .addiw rd rs imm => s!"addiw {rd.name}, {rs.name}, {imm.toInt}"
  | .andi rd rs imm => s!"andi {rd.name}, {rs.name}, {imm.toInt}"
  | .add rd a b => s!"add {rd.name}, {a.name}, {b.name}"
  | .addw rd a b => s!"addw {rd.name}, {a.name}, {b.name}"
  | .sub rd a b => s!"sub {rd.name}, {a.name}, {b.name}"
  | .xor rd a b => s!"xor {rd.name}, {a.name}, {b.name}"
  | .or rd a b => s!"or {rd.name}, {a.name}, {b.name}"
  | .and rd a b => s!"and {rd.name}, {a.name}, {b.name}"
  -- Shift amounts print reduced, exactly as the encoding keeps them.
  | .slli rd rs k => s!"slli {rd.name}, {rs.name}, {k % 64}"
  | .srli rd rs k => s!"srli {rd.name}, {rs.name}, {k % 64}"
  | .slliw rd rs k => s!"slliw {rd.name}, {rs.name}, {k % 32}"
  | .srliw rd rs k => s!"srliw {rd.name}, {rs.name}, {k % 32}"
  | .lbu rd base off => s!"lbu {rd.name}, {off.toInt}({base.name})"
  | .lw rd base off => s!"lw {rd.name}, {off.toInt}({base.name})"
  | .ld rd base off => s!"ld {rd.name}, {off.toInt}({base.name})"
  | .sb src base off => s!"sb {src.name}, {off.toInt}({base.name})"
  | .sw src base off => s!"sw {src.name}, {off.toInt}({base.name})"
  | .sd src base off => s!"sd {src.name}, {off.toInt}({base.name})"
  | .beq a b t => s!"beq {a.name}, {b.name}, {label routine t}"
  | .bne a b t => s!"bne {a.name}, {b.name}, {label routine t}"
  | .bltu a b t => s!"bltu {a.name}, {b.name}, {label routine t}"
  | .bgeu a b t => s!"bgeu {a.name}, {b.name}, {label routine t}"
  | .j t => s!"j {label routine t}"
  | .ret => "ret"

/-- The instruction indices some branch or jump lands on. -/
def targets (program : Array Instr) : List Nat :=
  program.toList.filterMap fun
    | .beq _ _ t | .bne _ _ t | .bltu _ _ t | .bgeu _ _ t | .j t => some t
    | _ => none

/-- A whole routine as an exported function, labelled where control can land. -/
def render (routine : String) (program : Array Instr) : String := Id.run do
  -- The symbol is global so a linker can resolve calls from other objects.
  let mut out := s!"\t.globl {routine}\n\t.type {routine}, @function\n\t.p2align 2\n{routine}:\n"
  let landing := targets program
  for h : index in [0:program.size] do
    -- A label goes in front of every instruction a branch can reach.
    if landing.contains index then out := out ++ s!"{label routine index}:\n"
    out := out ++ s!"\t{program[index].render routine}\n"
  return out ++ s!"\t.size {routine}, .-{routine}\n"

/-- Read-only data under an exported label, one byte directive per line of sixteen. -/
def renderData (label : String) (bytes : Array UInt8) : String := Id.run do
  let mut out := s!"\t.globl {label}\n\t.p2align 3\n{label}:\n"
  for row in [0:(bytes.size + 15) / 16] do
    -- Sixteen bytes per line keeps the table readable next to a hex dump.
    let line := (bytes.extract (16 * row) (16 * row + 16)).toList.map (fun b => toString b.toNat)
    out := out ++ s!"\t.byte {", ".intercalate line}\n"
  return out

/-- 64-bit words under an exported label. -/
def renderWords (label : String) (words : List Nat) : String :=
  -- One quad per word, in order.
  s!"\t.globl {label}\n\t.p2align 3\n{label}:\n" ++ String.join (words.map fun w => s!"\t.quad {w}\n")

end Ssz.Asm
