import SszNative.Asm.Instr

/-!
The programs the assembler encodes exactly as the model reads them.

Numbers in the instruction data are unbounded, but each encoding field has a fixed width.
Outside that width the assembler may reject a line, or accept it with another meaning.
For example, it encodes the displacement 2^64 - 1 as -1, so the access lands below the base.

Inside these bounds, every printed line is the instruction the model runs:

- displacements are non-negative and fit the signed 32-bit field, so none wraps;
- add and subtract immediates fit the signed 32-bit field, which the processor extends to the same 64-bit value;
- compare immediates are non-negative and fit the signed 32-bit field, so sign extension keeps them;
- shift, rotate, and align counts fit their byte, so the processor reads the count the model does;
- legacy SSE forms name only the first sixteen vector registers, the only ones their encoding reaches;
- the 256-bit VEX forms of the AVX2 instructions name only the first sixteen vector registers too;
- branch targets are instructions of the program, so each one prints a label that exists.
-/

namespace Ssz.Native.Asm

/-- Whether a displacement fits the signed 32-bit field, as a non-negative number. -/
def Mem.valid (m : Mem) : Bool :=
  m.disp < 2 ^ 31

/-- Whether a legacy SSE encoding can name the vector register. -/
def legacy (v : Vreg) : Bool :=
  v.val < 16

/-- Whether an instruction's operands fit their encoding, in a program of a given length. -/
def Instr.valid (size : Nat) : Instr → Bool
  -- The immediate is sign-extended from 32 bits.
  | .addImm _ imm | .subImm _ imm | .cmpImm _ imm => imm < 2 ^ 31
  -- A target outside the program has no label to land on.
  | .jz t | .jnz t | .jcc _ t | .jmp t => t < size
  | .test _ | .vzeroupper | .ret | .movReg _ _ | .zeroReg _ | .addReg _ _ | .repMovsb | .repStosb => true
  -- A 64-bit constant has its own long encoding, and the image checks that a called name exists.
  | .movImm _ _ | .alu _ _ _ | .cmp _ _ | .div _ | .push _ | .pop _ | .call _ | .cpuid | .xgetbv | .bswap _ => true
  | .loadByte _ m | .loadWord _ m | .load _ _ m | .store _ m _ => m.valid
  | .shlImm _ k | .shrImm _ k => k < 2 ^ 8
  -- The VEX and EVEX forms reach all thirty-two vector registers.
  | .vfromGpr _ _ | .vmov _ _ | .vadd _ _ _ | .vternlog _ _ _ _ | .vshufb _ _ _ | .vshufps _ _ _ _
  | .vpermi2q _ _ _ | .vpermi2d _ _ _ => true
  | .vload4 _ m | .vload8 _ m | .vload16 _ m | .vstoreHalf m _ | .vload _ m | .vstore m _
  | .vloadHalf _ m | .vinsertHigh _ _ m | .vaddMem _ _ m => m.valid
  -- The count is one immediate byte.
  | .vror _ _ k | .vshr _ _ k => k < 2 ^ 8
  -- The legacy SSE forms reach only the first sixteen vector registers.
  | .movdqu d m | .movdquStore m d | .padddMem d m => legacy d && m.valid
  | .movdqa d s | .paddd d s | .pxor d s | .pand d s | .pandn d s | .pshufb d s | .pshufd d s _ | .pblendw d s _
  | .sha256rnds2 d s | .sha256msg1 d s | .sha256msg2 d s => legacy d && legacy s
  | .palignr d s k => legacy d && legacy s && k < 2 ^ 8
  | .psrld d k | .pslld d k => legacy d && k < 2 ^ 8
  -- The 256-bit VEX forms reach only the first sixteen vector registers.
  | .ymov d s => legacy d && legacy s
  | .yadd d a b | .yxor d a b | .yand d a b | .yandn d a b | .yor d a b | .yshufb d a b
  | .yunpackLo32 d a b | .yunpackHi32 d a b | .yunpackLo64 d a b | .yunpackHi64 d a b | .yperm128 d a b _ =>
    legacy d && legacy a && legacy b
  | .yaddMem d a m => legacy d && legacy a && m.valid
  | .yshr d a k | .yshl d a k => legacy d && legacy a && k < 2 ^ 8

/-- Whether every instruction of a program fits its encoding. -/
def valid (program : Array Instr) : Bool :=
  -- The list form keeps the check cheap for the kernel to evaluate.
  program.toList.all (·.valid program.toList.length)

end Ssz.Native.Asm
