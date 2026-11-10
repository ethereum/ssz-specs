import SszNative.Asm.Valid

/-! Printing programs as Intel-syntax GNU assembler, for Linux and macOS on x86-64. -/

namespace EthLib.Consensus.Ssz.Native.Asm

/-- The register's assembler name. -/
def Gpr.name : Gpr → String
  | .rax => "rax" | .rcx => "rcx" | .rdx => "rdx" | .rbx => "rbx"
  | .rsp => "rsp" | .rbp => "rbp" | .rsi => "rsi" | .rdi => "rdi"
  | .r8 => "r8" | .r9 => "r9" | .r10 => "r10" | .r11 => "r11"
  | .r12 => "r12" | .r13 => "r13" | .r14 => "r14" | .r15 => "r15"

/-- The register's low 32 bits, as the assembler names them. -/
def Gpr.name32 : Gpr → String
  | .rax => "eax" | .rcx => "ecx" | .rdx => "edx" | .rbx => "ebx"
  | .rsp => "esp" | .rbp => "ebp" | .rsi => "esi" | .rdi => "edi"
  | .r8 => "r8d" | .r9 => "r9d" | .r10 => "r10d" | .r11 => "r11d"
  | .r12 => "r12d" | .r13 => "r13d" | .r14 => "r14d" | .r15 => "r15d"

/-- The register's low 16 bits, as the assembler names them. -/
def Gpr.name16 : Gpr → String
  | .rax => "ax" | .rcx => "cx" | .rdx => "dx" | .rbx => "bx"
  | .rsp => "sp" | .rbp => "bp" | .rsi => "si" | .rdi => "di"
  | .r8 => "r8w" | .r9 => "r9w" | .r10 => "r10w" | .r11 => "r11w"
  | .r12 => "r12w" | .r13 => "r13w" | .r14 => "r14w" | .r15 => "r15w"

/-- The register's low byte, as the assembler names it. -/
def Gpr.name8 : Gpr → String
  | .rax => "al" | .rcx => "cl" | .rdx => "dl" | .rbx => "bl"
  | .rsp => "spl" | .rbp => "bpl" | .rsi => "sil" | .rdi => "dil"
  | .r8 => "r8b" | .r9 => "r9b" | .r10 => "r10b" | .r11 => "r11b"
  | .r12 => "r12b" | .r13 => "r13b" | .r14 => "r14b" | .r15 => "r15b"

/-- The register at a width, as a store names its source. -/
def Gpr.at (r : Gpr) : Width → String
  | .b1 => r.name8 | .b2 => r.name16 | .b4 => r.name32 | .b8 => r.name

/-- The memory operand size keyword of a width. -/
def Width.ptr : Width → String
  | .b1 => "byte" | .b2 => "word" | .b4 => "dword" | .b8 => "qword"

/-- The mnemonic of an integer operation. -/
def Alu.mnemonic : Alu → String
  | .add => "add" | .sub => "sub" | .and => "and" | .or => "or" | .xor => "xor" | .mul => "imul"

/-- The conditional branch mnemonic of a condition. -/
def Cond.mnemonic : Cond → String
  | .b => "jb" | .ae => "jae" | .be => "jbe" | .a => "ja" | .e => "je" | .ne => "jne"

/-- A vector register at 512, 256, or 128 bits. -/
def zmm (v : Vreg) : String := s!"zmm{v.val}"

@[inherit_doc zmm] def ymm (v : Vreg) : String := s!"ymm{v.val}"

@[inherit_doc zmm] def xmm (v : Vreg) : String := s!"xmm{v.val}"

/-- A memory operand of a given width. -/
def Mem.render (m : Mem) (width : String) : String :=
  s!"{width} ptr [{m.base.name} + {m.disp}]"

/-- An immediate byte in hex. -/
def hexByte (b : BitVec 8) : String :=
  let digits := Nat.toDigits 16 b.toNat
  "0x" ++ String.ofList (if digits.length < 2 then '0' :: digits else digits)

/-- The label an instruction index gets inside one routine. -/
def label (routine : String) (target : Nat) : String :=
  s!".L{routine}_{target}"

/-- One instruction as an assembler line. -/
def Instr.render (routine : String) : Instr → String
  | .addImm r imm => s!"add {r.name}, {imm}"
  | .subImm r imm => s!"sub {r.name}, {imm}"
  | .test r => s!"test {r.name}, {r.name}"
  | .jz t => s!"jz {label routine t}"
  | .jnz t => s!"jnz {label routine t}"
  | .vzeroupper => "vzeroupper"
  | .ret => "ret"
  | .movReg d s => s!"mov {d.name}, {s.name}"
  -- Writing the 32-bit half clears the whole register and has the shorter encoding.
  | .zeroReg r => s!"xor {r.name32}, {r.name32}"
  | .addReg d s => s!"add {d.name}, {s.name}"
  | .repMovsb => "rep movsb"
  | .repStosb => "rep stosb"
  | .loadByte d m => s!"movzx {d.name32}, {m.render "byte"}"
  | .loadWord d m => s!"movzx {d.name32}, {m.render "word"}"
  -- A 64-bit constant takes the long form, which the assembler shortens when the value allows.
  | .movImm d imm => s!"mov {d.name}, {imm.toNat}"
  -- Narrow loads zero-extend, and a 32-bit load clears the upper half by itself.
  | .load .b1 d m => s!"movzx {d.name32}, {m.render "byte"}"
  | .load .b2 d m => s!"movzx {d.name32}, {m.render "word"}"
  | .load .b4 d m => s!"mov {d.name32}, {m.render "dword"}"
  | .load .b8 d m => s!"mov {d.name}, {m.render "qword"}"
  | .store w m r => s!"mov {m.render w.ptr}, {r.at w}"
  | .alu op d r => s!"{op.mnemonic} {d.name}, {r.name}"
  | .shlImm r k => s!"shl {r.name}, {k}"
  | .shrImm r k => s!"shr {r.name}, {k}"
  | .cmp a b => s!"cmp {a.name}, {b.name}"
  | .cmpImm a imm => s!"cmp {a.name}, {imm}"
  | .div r => s!"div {r.name}"
  | .jcc c t => s!"{c.mnemonic} {label routine t}"
  | .jmp t => s!"jmp {label routine t}"
  | .push r => s!"push {r.name}"
  | .pop r => s!"pop {r.name}"
  | .call name => s!"call SYMBOL({name})"
  | .cpuid => "cpuid"
  | .xgetbv => "xgetbv"
  -- The 32-bit form reverses the low four bytes and clears the upper half.
  | .bswap r => s!"bswap {r.name32}"
  -- These clear every bit above what they write.
  -- The assembler encodes registers below 16 in the VEX form, and the rest in the EVEX form.
  | .vfromGpr d r => s!"vmovd {xmm d}, {r.name32}"
  | .vload4 d m => s!"vmovd {xmm d}, {m.render "dword"}"
  | .vload8 d m => s!"vmovq {xmm d}, {m.render "qword"}"
  -- The EVEX form of an unaligned move names its lane width.
  | .vload16 d m => s!"{if d.val < 16 then "vmovdqu" else "vmovdqu32"} {xmm d}, {m.render "xmmword"}"
  | .vstoreHalf m r => s!"{if r.val < 16 then "vmovdqu" else "vmovdqu32"} {m.render "ymmword"}, {ymm r}"
  | .vload d m => s!"vmovdqu32 {zmm d}, {m.render "zmmword"}"
  | .vstore m s => s!"vmovdqu32 {m.render "zmmword"}, {zmm s}"
  -- Both forms clear the bits above 256, and the VEX form needs no AVX-512.
  | .vloadHalf d m => s!"{if d.val < 16 then "vmovdqu" else "vmovdqu32"} {ymm d}, {m.render "ymmword"}"
  | .vinsertHigh d s m => s!"vinserti64x4 {zmm d}, {zmm s}, {m.render "ymmword"}, 1"
  | .vmov d s => s!"vmovdqa32 {zmm d}, {zmm s}"
  | .vadd d a b => s!"vpaddd {zmm d}, {zmm a}, {zmm b}"
  | .vaddMem d a m => s!"vpaddd {zmm d}, {zmm a}, {m.render "zmmword"}"
  | .vror d a k => s!"vprord {zmm d}, {zmm a}, {k}"
  | .vshr d a k => s!"vpsrld {zmm d}, {zmm a}, {k}"
  | .vternlog d a b t => s!"vpternlogd {zmm d}, {zmm a}, {zmm b}, {hexByte t}"
  | .vshufb d a b => s!"vpshufb {zmm d}, {zmm a}, {zmm b}"
  | .vshufps d a b imm => s!"vshufps {zmm d}, {zmm a}, {zmm b}, {hexByte imm}"
  | .vpermi2q d a b => s!"vpermi2q {zmm d}, {zmm a}, {zmm b}"
  | .vpermi2d d a b => s!"vpermi2d {zmm d}, {zmm a}, {zmm b}"
  | .ymov d s => s!"vmovdqa {ymm d}, {ymm s}"
  | .yadd d a b => s!"vpaddd {ymm d}, {ymm a}, {ymm b}"
  | .yaddMem d a m => s!"vpaddd {ymm d}, {ymm a}, {m.render "ymmword"}"
  | .yxor d a b => s!"vpxor {ymm d}, {ymm a}, {ymm b}"
  | .yand d a b => s!"vpand {ymm d}, {ymm a}, {ymm b}"
  | .yandn d a b => s!"vpandn {ymm d}, {ymm a}, {ymm b}"
  | .yor d a b => s!"vpor {ymm d}, {ymm a}, {ymm b}"
  | .yshr d a k => s!"vpsrld {ymm d}, {ymm a}, {k}"
  | .yshl d a k => s!"vpslld {ymm d}, {ymm a}, {k}"
  | .yshufb d a b => s!"vpshufb {ymm d}, {ymm a}, {ymm b}"
  | .yunpackLo32 d a b => s!"vpunpckldq {ymm d}, {ymm a}, {ymm b}"
  | .yunpackHi32 d a b => s!"vpunpckhdq {ymm d}, {ymm a}, {ymm b}"
  | .yunpackLo64 d a b => s!"vpunpcklqdq {ymm d}, {ymm a}, {ymm b}"
  | .yunpackHi64 d a b => s!"vpunpckhqdq {ymm d}, {ymm a}, {ymm b}"
  | .yperm128 d a b imm => s!"vperm2i128 {ymm d}, {ymm a}, {ymm b}, {hexByte imm}"
  | .movdqu d m => s!"movdqu {xmm d}, {m.render "xmmword"}"
  | .movdquStore m s => s!"movdqu {m.render "xmmword"}, {xmm s}"
  | .movdqa d s => s!"movdqa {xmm d}, {xmm s}"
  | .paddd d s => s!"paddd {xmm d}, {xmm s}"
  | .padddMem d m => s!"paddd {xmm d}, {m.render "xmmword"}"
  | .pxor d s => s!"pxor {xmm d}, {xmm s}"
  | .pand d s => s!"pand {xmm d}, {xmm s}"
  | .pandn d s => s!"pandn {xmm d}, {xmm s}"
  | .psrld d k => s!"psrld {xmm d}, {k}"
  | .pslld d k => s!"pslld {xmm d}, {k}"
  | .pshufb d s => s!"pshufb {xmm d}, {xmm s}"
  | .pshufd d s imm => s!"pshufd {xmm d}, {xmm s}, {hexByte imm}"
  | .palignr d s k => s!"palignr {xmm d}, {xmm s}, {k}"
  | .pblendw d s imm => s!"pblendw {xmm d}, {xmm s}, {hexByte imm}"
  | .sha256rnds2 d s => s!"sha256rnds2 {xmm d}, {xmm s}, xmm0"
  | .sha256msg1 d s => s!"sha256msg1 {xmm d}, {xmm s}"
  | .sha256msg2 d s => s!"sha256msg2 {xmm d}, {xmm s}"

/-- The instruction indices some branch lands on. -/
def targets (program : Array Instr) : List Nat :=
  program.toList.filterMap fun
    | .jz t | .jnz t | .jcc _ t | .jmp t => some t
    | _ => none

/-- A routine as an exported function, labelled where control can land. -/
def render (routine : String) (program : Array Instr) : String := Id.run do
  let mut out := s!"\t.globl SYMBOL({routine})\n\t.p2align 6\nSYMBOL({routine}):\n"
  let landing := targets program
  for h : index in [0:program.size] do
    if landing.contains index then out := out ++ s!"{label routine index}:\n"
    out := out ++ s!"\t{program[index].render routine}\n"
  return out

/-- Read-only bytes under an exported label, sixteen per line. -/
def renderData (name : String) (bytes : ByteArray) : String := Id.run do
  let mut out := s!"\t.globl SYMBOL({name})\n\t.p2align 6\nSYMBOL({name}):\n"
  for row in [0:(bytes.size + 15) / 16] do
    let line := ((bytes.extract (16 * row) (16 * row + 16)).toList.map fun b => toString b.toNat)
    out := out ++ s!"\t.byte {", ".intercalate line}\n"
  return out

/--
A whole assembler file: the routines, then the read-only data, for x86-64 Linux and macOS only.

It takes only routines whose operands fit their encodings, so each printed line means what the model runs.
-/
def file (routines : List (String × Array Instr)) (data : List (String × ByteArray))
    (_ : routines.all (fun routine => valid routine.2) = true) : String :=
  "// Printed from the Lean programs in SszNative by `just lean-kernels`.\n" ++
  "// Do not edit: the regressions fail when this file differs from what they print.\n" ++
  "#if defined(__x86_64__) && !defined(_WIN32)\n" ++
  "#if defined(__APPLE__)\n#define SYMBOL(name) _##name\n#else\n#define SYMBOL(name) name\n#endif\n" ++
  "\t.intel_syntax noprefix\n\t.text\n" ++
  String.join (routines.map fun (name, program) => render name program) ++
  "#if defined(__APPLE__)\n\t.section __TEXT,__const\n#else\n\t.section .rodata\n#endif\n" ++
  String.join (data.map fun (name, bytes) => renderData name bytes) ++
  "#if defined(__linux__)\n\t.section .note.GNU-stack,\"\",@progbits\n#endif\n#endif\n"

end EthLib.Consensus.Ssz.Native.Asm
