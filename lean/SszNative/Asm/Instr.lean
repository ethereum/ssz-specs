/-!
The x86-64 instructions the native kernels use, written as data.

One program is both what the proofs run on the machine model and what the emitter prints.
-/

namespace EthLib.Consensus.Ssz.Native.Asm

/-- A general-purpose 64-bit register, in encoding order. -/
inductive Gpr where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
  deriving Repr, DecidableEq, Inhabited

/-- A vector register, zmm0 to zmm31, whose low 256 and 128 bits are ymm and xmm. -/
abbrev Vreg := Fin 32

/-- How many bytes a scalar load or store moves. -/
inductive Width where
  | b1 | b2 | b4 | b8
  deriving Repr, DecidableEq, Inhabited

/-- The byte count of a width. -/
def Width.bytes : Width → Nat
  | .b1 => 1 | .b2 => 2 | .b4 => 4 | .b8 => 8

/-- An unsigned comparison outcome a conditional branch tests, after a compare of a first operand with a second. -/
inductive Cond where
  /-- Below: the first is smaller. -/
  | b
  /-- Above or equal: the first is not smaller. -/
  | ae
  /-- Below or equal: the first is not larger. -/
  | be
  /-- Above: the first is larger. -/
  | a
  /-- Equal. -/
  | e
  /-- Not equal. -/
  | ne
  deriving Repr, DecidableEq, Inhabited

/-- A two-operand integer operation on whole 64-bit registers. -/
inductive Alu where
  | add | sub | and | or | xor
  /-- The low 64 bits of the product. -/
  | mul
  deriving Repr, DecidableEq, Inhabited

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
  /-- Put a 64-bit constant in a register. -/
  | movImm (d : Gpr) (imm : UInt64)
  /-- Load bytes into a register, zero-extended to 64 bits. -/
  | load (w : Width) (d : Gpr) (m : Mem)
  /-- Store a register's low bytes. -/
  | store (w : Width) (m : Mem) (s : Gpr)
  /-- Combine two registers into the first, setting the zero and carry flags (left undefined by a product). -/
  | alu (op : Alu) (d s : Gpr)
  /-- Shift a register left by a constant, setting the zero and carry flags when the count is not zero. -/
  | shlImm (r : Gpr) (k : Nat)
  /-- Shift a register right by a constant, setting the zero and carry flags when the count is not zero. -/
  | shrImm (r : Gpr) (k : Nat)
  /-- Compare two registers, as the subtraction of the second from the first, keeping neither. -/
  | cmp (a b : Gpr)
  /-- Compare a register with a sign-extended 32-bit constant. -/
  | cmpImm (a : Gpr) (imm : Nat)
  /-- Divide rdx and rax, as one 128-bit number, by a register: the quotient goes to rax and the rest to rdx. -/
  | div (r : Gpr)
  /-- Branch when a condition holds. -/
  | jcc (c : Cond) (target : Nat)
  /-- Branch always. -/
  | jmp (target : Nat)
  /-- Push a register onto the stack. -/
  | push (r : Gpr)
  /-- Pop the top of the stack into a register. -/
  | pop (r : Gpr)
  /-- Call another routine of the same image by its exported name. -/
  | call (routine : String)
  /-- Reverse the order of a register's low four bytes, clearing the upper half. -/
  | bswap (r : Gpr)
  /-- Ask the processor what it supports, for the leaf in eax and the subleaf in ecx. -/
  | cpuid
  /-- Read an extended control register, the one named in ecx, into edx and eax. -/
  | xgetbv
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
  /-- Copy a ymm register, clearing the destination's bits above 256. -/
  | ymov (d s : Vreg)
  /-- Add the lanes of two ymm registers. -/
  | yadd (d a b : Vreg)
  /-- Add the lanes of a ymm register and of 32 loaded bytes. -/
  | yaddMem (d a : Vreg) (m : Mem)
  /-- The exclusive or of two ymm registers. -/
  | yxor (d a b : Vreg)
  /-- The bitwise and of two ymm registers. -/
  | yand (d a b : Vreg)
  /-- The bitwise and of the first ymm register's complement with the second. -/
  | yandn (d a b : Vreg)
  /-- The bitwise or of two ymm registers. -/
  | yor (d a b : Vreg)
  /-- Shift every lane of a ymm register right by a constant. -/
  | yshr (d a : Vreg) (k : Nat)
  /-- Shift every lane of a ymm register left by a constant. -/
  | yshl (d a : Vreg) (k : Nat)
  /-- Shuffle the bytes of a ymm register within each 128-bit lane, by the indices in the second source. -/
  | yshufb (d a b : Vreg)
  /-- Interleave the low two 32-bit lanes of each 128-bit lane of two ymm registers. -/
  | yunpackLo32 (d a b : Vreg)
  /-- Interleave the high two 32-bit lanes of each 128-bit lane of two ymm registers. -/
  | yunpackHi32 (d a b : Vreg)
  /-- Interleave the low 64-bit lane of each 128-bit lane of two ymm registers. -/
  | yunpackLo64 (d a b : Vreg)
  /-- Interleave the high 64-bit lane of each 128-bit lane of two ymm registers. -/
  | yunpackHi64 (d a b : Vreg)
  /-- Pick each 128-bit half from the halves of two ymm registers, or zero, by the immediate's two nibbles. -/
  | yperm128 (d a b : Vreg) (imm : BitVec 8)
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
  /-- The exclusive or of two xmm registers. -/
  | pxor (d s : Vreg)
  /-- The bitwise and of two xmm registers. -/
  | pand (d s : Vreg)
  /-- The bitwise and of the first xmm register's complement with the second. -/
  | pandn (d s : Vreg)
  /-- Shift every lane of an xmm register right by a constant. -/
  | psrld (d : Vreg) (k : Nat)
  /-- Shift every lane of an xmm register left by a constant. -/
  | pslld (d : Vreg) (k : Nat)
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

end EthLib.Consensus.Ssz.Native.Asm
