/-!
A 64-bit RISC-V machine, cut down to the RV64I instructions the SSZ kernels emit.

The semantics follow the RISC-V unprivileged specification, chapters 2 and 4.
-/

namespace Ssz.Asm

/-- A general-purpose register index, where index zero always reads as zero. -/
abbrev Reg := Fin 32

/-- Registers and byte-addressed memory, with no program counter. -/
structure Machine where
  /-- The register file, whose entry for the zero register is never read. -/
  regs : Reg → BitVec 64
  /-- Little-endian, byte-addressed memory over the whole 64-bit address space. -/
  mem : BitVec 64 → BitVec 8

namespace Machine

/-- The value a register holds, with the zero register hardwired to zero. -/
def read (m : Machine) (r : Reg) : BitVec 64 :=
  if r = 0 then 0 else m.regs r

/-- The machine with one register replaced. -/
def write (m : Machine) (r : Reg) (v : BitVec 64) : Machine :=
  -- A write to the zero register lands in a slot no read ever consults.
  { m with regs := fun q => if q = r then v else m.regs q }

/-- A little-endian load of a given number of bytes, zero-extended to 64 bits. -/
def load (m : Machine) (address : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  -- The byte at offset k lands in bits 8k to 8k + 7.
  | count + 1 =>
    m.load address count ||| ((m.mem (address + BitVec.ofNat 64 count)).setWidth 64 <<< (8 * count))

/-- A little-endian store of the low bytes of a value. -/
def store (m : Machine) (address : BitVec 64) (count : Nat) (v : BitVec 64) : Machine :=
  -- Byte k of the stored range receives bits 8k to 8k + 7 of the value.
  { m with mem := fun x =>
      if (x - address).toNat < count then (v >>> (8 * (x - address).toNat)).setWidth 8
      else m.mem x }

end Machine

/-- Sign extension of a 32-bit result, as every word-sized RV64 instruction writes it. -/
def sext32 (v : BitVec 64) : BitVec 64 :=
  (v.setWidth 32).signExtend 64

/--
An RV64I instruction.

Branch and jump targets are instruction indices, which the emitter prints as labels.
-/
inductive Instr where
  /-- Load a 20-bit immediate into bits 12 to 31, sign-extended. -/
  | lui (rd : Reg) (imm : BitVec 20)
  /-- Add a sign-extended 12-bit immediate. -/
  | addi (rd rs : Reg) (imm : BitVec 12)
  /-- Add a sign-extended 12-bit immediate, keeping a sign-extended 32-bit result. -/
  | addiw (rd rs : Reg) (imm : BitVec 12)
  /-- Bitwise and with a sign-extended 12-bit immediate. -/
  | andi (rd rs : Reg) (imm : BitVec 12)
  /-- Add two registers. -/
  | add (rd rs1 rs2 : Reg)
  /-- Add two registers, keeping a sign-extended 32-bit result. -/
  | addw (rd rs1 rs2 : Reg)
  /-- Subtract the second register from the first. -/
  | sub (rd rs1 rs2 : Reg)
  /-- Bitwise exclusive or of two registers. -/
  | xor (rd rs1 rs2 : Reg)
  /-- Bitwise or of two registers. -/
  | or (rd rs1 rs2 : Reg)
  /-- Bitwise and of two registers. -/
  | and (rd rs1 rs2 : Reg)
  /-- Shift left by a constant, of which the encoding keeps the low six bits. -/
  | slli (rd rs : Reg) (shamt : Nat)
  /-- Logical shift right by a constant, of which the encoding keeps the low six bits. -/
  | srli (rd rs : Reg) (shamt : Nat)
  /-- Shift the low 32 bits left by a constant below 32, keeping a sign-extended result. -/
  | slliw (rd rs : Reg) (shamt : Nat)
  /-- Shift the low 32 bits right by a constant below 32, keeping a sign-extended result. -/
  | srliw (rd rs : Reg) (shamt : Nat)
  /-- Load one byte, zero-extended. -/
  | lbu (rd base : Reg) (offset : BitVec 12)
  /-- Load four bytes, sign-extended. -/
  | lw (rd base : Reg) (offset : BitVec 12)
  /-- Load eight bytes. -/
  | ld (rd base : Reg) (offset : BitVec 12)
  /-- Store the low byte. -/
  | sb (src base : Reg) (offset : BitVec 12)
  /-- Store the low four bytes. -/
  | sw (src base : Reg) (offset : BitVec 12)
  /-- Store all eight bytes. -/
  | sd (src base : Reg) (offset : BitVec 12)
  /-- Branch when two registers are equal. -/
  | beq (rs1 rs2 : Reg) (target : Nat)
  /-- Branch when two registers differ. -/
  | bne (rs1 rs2 : Reg) (target : Nat)
  /-- Branch when the first register is below the second, unsigned. -/
  | bltu (rs1 rs2 : Reg) (target : Nat)
  /-- Branch when the first register is at least the second, unsigned. -/
  | bgeu (rs1 rs2 : Reg) (target : Nat)
  /-- Jump unconditionally. -/
  | j (target : Nat)
  /-- Return to the caller, which ends the routine. -/
  | ret
  deriving Repr, Inhabited, DecidableEq

namespace Instr

/-- The effect an instruction has on registers and memory. -/
def run : Instr → Machine → Machine
  | lui rd imm, m => m.write rd ((imm ++ (0 : BitVec 12)).signExtend 64)
  | addi rd rs imm, m => m.write rd (m.read rs + imm.signExtend 64)
  | addiw rd rs imm, m => m.write rd (sext32 (m.read rs + imm.signExtend 64))
  | andi rd rs imm, m => m.write rd (m.read rs &&& imm.signExtend 64)
  | add rd a b, m => m.write rd (m.read a + m.read b)
  | addw rd a b, m => m.write rd (sext32 (m.read a + m.read b))
  | sub rd a b, m => m.write rd (m.read a - m.read b)
  | xor rd a b, m => m.write rd (m.read a ^^^ m.read b)
  | or rd a b, m => m.write rd (m.read a ||| m.read b)
  | and rd a b, m => m.write rd (m.read a &&& m.read b)
  | slli rd rs k, m => m.write rd (m.read rs <<< (k % 64))
  | srli rd rs k, m => m.write rd (m.read rs >>> (k % 64))
  -- The word shifts see only the low 32 bits of the source.
  | slliw rd rs k, m => m.write rd (((m.read rs).setWidth 32 <<< (k % 32)).signExtend 64)
  | srliw rd rs k, m => m.write rd (((m.read rs).setWidth 32 >>> (k % 32)).signExtend 64)
  | lbu rd base off, m => m.write rd (m.load (m.read base + off.signExtend 64) 1)
  | lw rd base off, m => m.write rd (sext32 (m.load (m.read base + off.signExtend 64) 4))
  | ld rd base off, m => m.write rd (m.load (m.read base + off.signExtend 64) 8)
  | sb src base off, m => m.store (m.read base + off.signExtend 64) 1 (m.read src)
  | sw src base off, m => m.store (m.read base + off.signExtend 64) 4 (m.read src)
  | sd src base off, m => m.store (m.read base + off.signExtend 64) 8 (m.read src)
  -- Control flow moves only the program counter.
  | beq .., m | bne .., m | bltu .., m | bgeu .., m | j _, m | ret, m => m

/-- The instruction index control reaches after this one. -/
def next (i : Instr) (m : Machine) (pc : Nat) : Nat :=
  match i with
  | beq a b t => if m.read a = m.read b then t else pc + 1
  | bne a b t => if m.read a = m.read b then pc + 1 else t
  | bltu a b t => if (m.read a).toNat < (m.read b).toNat then t else pc + 1
  | bgeu a b t => if (m.read a).toNat < (m.read b).toNat then pc + 1 else t
  | j t => t
  -- A routine that has returned stays where it returned.
  | ret => pc
  | _ => pc + 1

/-- Whether control always falls through to the following instruction. -/
def straight : Instr → Bool
  | beq .. | bne .. | bltu .. | bgeu .. | j _ | ret => false
  | _ => true

end Instr

/-- A machine together with the index of the next instruction to execute. -/
structure Cpu where
  /-- Registers and memory. -/
  m : Machine
  /-- Index of the next instruction in the program. -/
  pc : Nat

/-- One instruction of a program, or nothing once control leaves the program. -/
def step (program : Array Instr) (s : Cpu) : Cpu :=
  match program[s.pc]? with
  | some i => ⟨i.run s.m, i.next s.m s.pc⟩
  | none => s

/-- A given number of instructions of a program. -/
def runFor (program : Array Instr) : Nat → Cpu → Cpu
  | 0, s => s
  | n + 1, s => runFor program n (step program s)

/-- Whether control sits on a return, so the routine has handed back to its caller. -/
def returned (program : Array Instr) (s : Cpu) : Prop :=
  program[s.pc]? = some .ret

/-- Store registers at byte offsets from a base register, eight bytes each. -/
def spills (base : Reg) (slots : List (Reg × Nat)) : List Instr :=
  slots.map fun (r, offset) => .sd r base (BitVec.ofNat 12 offset)

/-- Load registers back from byte offsets from a base register, eight bytes each. -/
def reloads (base : Reg) (slots : List (Reg × Nat)) : List Instr :=
  slots.map fun (r, offset) => .ld r base (BitVec.ofNat 12 offset)

/-- Straight-line code run from start to end, with no program counter in sight. -/
def execBlock (code : List Instr) (m : Machine) : Machine :=
  code.foldl (fun m i => i.run m) m

end Ssz.Asm
