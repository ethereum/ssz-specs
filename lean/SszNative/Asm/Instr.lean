/-!
The x86-64 instructions the native kernels use, written as data.

One program is both what the proofs run on the machine model and what the emitter prints.
-/

namespace Ssz.Native.Asm

/-- A general-purpose 64-bit register, in encoding order. -/
inductive Gpr where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving Repr, DecidableEq, Inhabited

/-- A vector register, zmm0 to zmm31, whose low 256 and 128 bits are ymm and xmm. -/
abbrev Vreg := Fin 32

/-- A memory operand: a base register plus a non-negative byte displacement. -/
structure Mem where
  /-- The register holding the base address. -/
  base : Gpr
  /-- Bytes past the base. -/
  disp : Nat
  deriving Repr, DecidableEq, Inhabited

/--
One instruction.

Vector instructions act on 32-bit lanes: sixteen per zmm register, four per xmm register.
Branch targets are instruction indices, which the emitter prints as labels.
-/
inductive Instr where
  /-- Add an immediate to a register. -/
  | addImm (r : Gpr) (imm : Nat)
  /-- Subtract an immediate from a register, setting the zero flag on a zero result. -/
  | subImm (r : Gpr) (imm : Nat)
  /-- Set the zero flag when a register is zero. -/
  | test (r : Gpr)
  /-- Branch when the zero flag is set. -/
  | jz (target : Nat)
  /-- Branch when the zero flag is clear. -/
  | jnz (target : Nat)
  /-- Clear the upper halves of every vector register, before returning to SSE code. -/
  | vzeroupper
  /-- Return to the caller. -/
  | ret
  /-- Copy one register into another. -/
  | movReg (d s : Gpr)
  /-- Clear a register. -/
  | zeroReg (r : Gpr)
  /-- Add one register to another. -/
  | addReg (d s : Gpr)
  /-- Copy rcx bytes from the address in rsi to the address in rdi, advancing both and clearing rcx. -/
  | repMovsb
  /-- Store rcx copies of al from the address in rdi, advancing it and clearing rcx. -/
  | repStosb
  /-- Load one byte into a register's low 32 bits, clearing the rest. -/
  | loadByte (d : Gpr) (m : Mem)
  /-- Load two bytes into a register's low 32 bits, clearing the rest. -/
  | loadWord (d : Gpr) (m : Mem)
  /-- Copy a register's low 32 bits into a vector register's lowest lane, clearing every lane above. -/
  | vfromGpr (d : Vreg) (r : Gpr)
  /-- Load 4 bytes into a vector register's lowest lane, clearing every lane above. -/
  | vload4 (d : Vreg) (m : Mem)
  /-- Load 8 bytes into a vector register's two lowest lanes, clearing every lane above. -/
  | vload8 (d : Vreg) (m : Mem)
  /-- Load 16 bytes into a vector register's four lowest lanes, clearing every lane above. -/
  | vload16 (d : Vreg) (m : Mem)
  /-- Store a vector register's low 32 bytes. -/
  | vstoreHalf (m : Mem) (s : Vreg)
  /-- Load 64 bytes into a zmm register. -/
  | vload (d : Vreg) (m : Mem)
  /-- Store a zmm register's 64 bytes. -/
  | vstore (m : Mem) (s : Vreg)
  /-- Load 32 bytes into a ymm register, clearing the upper 256 bits. -/
  | vloadHalf (d : Vreg) (m : Mem)
  /-- Copy a register's low 256 bits and put 32 loaded bytes above them. -/
  | vinsertHigh (d s : Vreg) (m : Mem)
  /-- Copy a zmm register. -/
  | vmov (d s : Vreg)
  /-- Add lanes. -/
  | vadd (d a b : Vreg)
  /-- Add lanes of a register and of 64 loaded bytes. -/
  | vaddMem (d a : Vreg) (m : Mem)
  /-- Rotate every lane right by a constant. -/
  | vror (d a : Vreg) (k : Nat)
  /-- Shift every lane right by a constant. -/
  | vshr (d a : Vreg) (k : Nat)
  /-- Any three-input bitwise function, given by its truth table; the destination is the first input. -/
  | vternlog (d a b : Vreg) (table : BitVec 8)
  /-- Shuffle bytes within each 128-bit lane, by the indices in the second source. -/
  | vshufb (d a b : Vreg)
  /-- Pick two lanes of the first source and two of the second, within each 128-bit lane. -/
  | vshufps (d a b : Vreg) (imm : BitVec 8)
  /-- Pick 64-bit lanes from two sources, by the indices the destination holds. -/
  | vpermi2q (d a b : Vreg)
  /-- Pick 32-bit lanes from two sources, by the indices the destination holds. -/
  | vpermi2d (d a b : Vreg)
  /-- Load 16 bytes into an xmm register, keeping the bits above. -/
  | movdqu (d : Vreg) (m : Mem)
  /-- Store an xmm register's 16 bytes. -/
  | movdquStore (m : Mem) (s : Vreg)
  /-- Copy an xmm register, keeping the destination's bits above. -/
  | movdqa (d s : Vreg)
  /-- Add lanes of two xmm registers. -/
  | paddd (d s : Vreg)
  /-- Add lanes of an xmm register and of 16 loaded bytes. -/
  | padddMem (d : Vreg) (m : Mem)
  /-- Shuffle the bytes of an xmm register. -/
  | pshufb (d s : Vreg)
  /-- Pick four lanes of an xmm register. -/
  | pshufd (d s : Vreg) (imm : BitVec 8)
  /-- Shift the 32 bytes of two xmm registers right by a byte count, keeping the low 16. -/
  | palignr (d s : Vreg) (bytes : Nat)
  /-- Pick each 16-bit half-lane from one of two xmm registers. -/
  | pblendw (d s : Vreg) (imm : BitVec 8)
  /-- Two SHA-256 rounds, with the message words plus constants in xmm0. -/
  | sha256rnds2 (d s : Vreg)
  /-- The first half of four SHA-256 message schedule steps. -/
  | sha256msg1 (d s : Vreg)
  /-- The second half of four SHA-256 message schedule steps. -/
  | sha256msg2 (d s : Vreg)
  deriving Repr, DecidableEq, Inhabited

end Ssz.Native.Asm
