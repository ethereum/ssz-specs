import SszNative.Asm.Semantics

/-!
The whole machine: several routines linked into one image, calling each other through the stack.

A routine run alone stops at its first return.
Here a return pops its address from the stack instead, and lands back in its caller.
A return to an address outside the image leaves it, which is how an exported routine hands back to its caller.

A call checks that the processor has every feature the called routine's instructions need.
The model faults there, before the routine runs, which is never later than the processor would.

Feature detection follows the Intel manual, volume 1, sections 13.2 and 15.2:
an extension is usable when cpuid reports it and the operating system saves its registers.
-/

namespace Ssz.Native.Asm

/-- An instruction set extension a routine may need, beyond the 64-bit baseline with SSE2. -/
inductive Feature where
  | ssse3 | sse41 | sha | avx | avx2 | avx512f | avx512bw | avx512vl
  deriving Repr, DecidableEq, Inhabited

/-- The bit at a position of a 32-bit word. -/
def bit (w : UInt32) (k : Nat) : Bool :=
  (w >>> k.toUInt32) &&& 1 == 1

/-- The highest basic cpuid leaf: asking for a higher one answers with this one's words instead. -/
def Cpu.maxLeaf (cpu : Cpu) : UInt32 :=
  (cpu.cpuid 0 0).1

/-- Whether the operating system saves the SSE and AVX register state: XCR0 bits 1 and 2. -/
def Cpu.ymmState (cpu : Cpu) : Bool :=
  cpu.osxsave && cpu.xcr0 &&& 0x6 == 0x6

/-- Whether it also saves the opmasks and both upper parts of the zmm registers: XCR0 bits 5 to 7. -/
def Cpu.zmmState (cpu : Cpu) : Bool :=
  cpu.ymmState && cpu.xcr0 &&& 0xE0 == 0xE0

/-- Leaf 7's extended feature word, or nothing when the processor has no leaf 7. -/
def Cpu.leaf7 (cpu : Cpu) : UInt32 :=
  if cpu.maxLeaf < 7 then 0 else (cpu.cpuid 7 0).2.1

/-- Whether the processor runs a feature's instructions without raising the invalid opcode fault. -/
def Cpu.has (cpu : Cpu) : Feature → Bool
  | .ssse3 => bit (cpu.cpuid 1 0).2.2.1 9
  | .sse41 => bit (cpu.cpuid 1 0).2.2.1 19
  | .sha => bit cpu.leaf7 29
  | .avx => bit (cpu.cpuid 1 0).2.2.1 28 && cpu.ymmState
  -- The 256-bit integer extension needs AVX too: leaf 7's bit 5, with the AVX bit and its register state.
  | .avx2 => bit cpu.leaf7 5 && bit (cpu.cpuid 1 0).2.2.1 28 && cpu.ymmState
  | .avx512f => bit cpu.leaf7 16 && cpu.zmmState
  | .avx512bw => bit cpu.leaf7 30 && cpu.zmmState
  | .avx512vl => bit cpu.leaf7 31 && cpu.zmmState

/-- The features a register-to-register or memory vector form needs, by whether it reaches the upper sixteen registers. -/
def vexOrEvex (high : Bool) (wide : List Feature) : List Feature :=
  if high then wide else [.avx]

/-- The features an instruction needs. -/
def Instr.features : Instr → List Feature
  -- The 64-bit baseline: integer instructions, cpuid, and the SSE2 moves, adds, bitwise operations, and shifts.
  | .addImm _ _ | .subImm _ _ | .test _ | .jz _ | .jnz _ | .ret | .movReg _ _ | .zeroReg _ | .addReg _ _
  | .repMovsb | .repStosb | .loadByte _ _ | .loadWord _ _ | .movImm _ _ | .load _ _ _ | .store _ _ _
  | .alu _ _ _ | .shlImm _ _ | .shrImm _ _ | .cmp _ _ | .cmpImm _ _ | .div _ | .jcc _ _ | .jmp _
  | .push _ | .pop _ | .call _ | .cpuid | .bswap _ | .movdqu _ _ | .movdquStore _ _ | .movdqa _ _ | .paddd _ _
  | .padddMem _ _ | .pxor _ _ | .pand _ _ | .pandn _ _ | .psrld _ _ | .pslld _ _ | .pshufd _ _ _ => []
  -- The step itself checks that the operating system allows the read.
  | .xgetbv => []
  | .pshufb _ _ | .palignr _ _ _ => [.ssse3]
  | .pblendw _ _ _ => [.sse41]
  | .sha256rnds2 _ _ | .sha256msg1 _ _ | .sha256msg2 _ _ => [.sha]
  | .vzeroupper => [.avx]
  -- A move has a VEX form below register 16, and an EVEX form above, which 128 and 256 bits make a length extension.
  | .vfromGpr d _ | .vload4 d _ | .vload8 d _ => vexOrEvex (16 ≤ d.val) [.avx512f]
  | .vload16 d _ | .vloadHalf d _ => vexOrEvex (16 ≤ d.val) [.avx512f, .avx512vl]
  | .vstoreHalf _ s => vexOrEvex (16 ≤ s.val) [.avx512f, .avx512vl]
  -- Byte shuffles on whole zmm registers are the byte-and-word extension.
  | .vshufb _ _ _ => [.avx512f, .avx512bw]
  | .vload _ _ | .vstore _ _ | .vinsertHigh _ _ _ | .vmov _ _ | .vadd _ _ _ | .vaddMem _ _ _ | .vror _ _ _
  | .vshr _ _ _ | .vternlog _ _ _ _ | .vshufps _ _ _ _ | .vpermi2q _ _ _ | .vpermi2d _ _ _ => [.avx512f]
  -- A 256-bit register copy is AVX, and the 256-bit integer operations are AVX2.
  | .ymov _ _ => [.avx]
  | .yadd _ _ _ | .yaddMem _ _ _ | .yxor _ _ _ | .yand _ _ _ | .yandn _ _ _ | .yor _ _ _ | .yshr _ _ _ | .yshl _ _ _
  | .yshufb _ _ _ | .yunpackLo32 _ _ _ | .yunpackHi32 _ _ _ | .yunpackLo64 _ _ _ | .yunpackHi64 _ _ _
  | .yperm128 _ _ _ _ => [.avx2]

/-- Whether the processor has every feature a routine's instructions need. -/
def Cpu.runs (cpu : Cpu) (program : Array Instr) : Bool :=
  program.toList.all fun i => i.features.all cpu.has

/-- Routines linked together, each under its exported name. -/
abbrev Image := Array (String × Array Instr)

/-- The index of the routine a name exports, if the image has one. -/
def Image.find (image : Image) (name : String) : Option Nat :=
  image.findIdx? (·.1 == name)

/-- The instructions of a routine, or none past the image. -/
def Image.code (image : Image) (routine : Nat) : Array Instr :=
  (image[routine]?.map (·.2)).getD #[]

/--
The 64-bit address of an instruction of a routine, as a call pushes it.

The model needs only that distinct instructions get distinct addresses, and that the encoding reads back.
-/
def codeAddress (routine index : Nat) : UInt64 :=
  (routine * 2 ^ 32 + index).toUInt64

/-- The machine with the routine it is running in. -/
structure Machine where
  /-- The routine whose instructions the index counts. -/
  routine : Nat
  /-- Registers, flags, memory, the instruction index within the routine, and whether execution goes on. -/
  state : State

/--
One step of the whole machine.

Calls and returns move between routines through the stack.
Every other instruction steps as it does in a routine run alone.
-/
def Image.step (image : Image) (m : Machine) : Machine :=
  let s := m.state
  if s.status != .running then m
  else match (image.code m.routine)[s.pc]? with
    | some (.call name) =>
      match image.find name with
      | some target =>
        -- The called routine must run on this processor, or the model faults before entering it.
        if s.cpu.runs (image.code target) then
          let top := s.gpr .rsp - 8
          let back := codeAddress m.routine (s.pc + 1)
          ⟨target, { s with gpr := assign s.gpr .rsp top, mem := store s.mem top.toNat 8 (qwordByte back), pc := 0 }⟩
        else ⟨m.routine, { s with status := .faulted }⟩
      | none => ⟨m.routine, { s with status := .faulted }⟩
    | some .ret =>
      let back := (readLE s.mem (s.gpr .rsp).toNat 8).toNat
      let popped := { s with gpr := assign s.gpr .rsp (s.gpr .rsp + 8) }
      -- An address inside the image resumes its caller, and any other leaves the image.
      if back / 2 ^ 32 < image.size then ⟨back / 2 ^ 32, { popped with pc := back % 2 ^ 32 }⟩
      else ⟨m.routine, { popped with status := .returned }⟩
    | _ => ⟨m.routine, Asm.step (image.code m.routine) s⟩

/-- A number of steps of the whole machine. -/
def Image.run (image : Image) : (steps : Nat) → Machine → Machine
  | 0, m => m
  | steps + 1, m => image.run steps (image.step m)

end Ssz.Native.Asm
