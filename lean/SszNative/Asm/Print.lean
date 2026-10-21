import SszNative.Asm.Instr

/-! Printing programs as Intel-syntax GNU assembler, for Linux and macOS on x86-64. -/

namespace Ssz.Native.Asm

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
  | .movdqu d m => s!"movdqu {xmm d}, {m.render "xmmword"}"
  | .movdquStore m s => s!"movdqu {m.render "xmmword"}, {xmm s}"
  | .movdqa d s => s!"movdqa {xmm d}, {xmm s}"
  | .paddd d s => s!"paddd {xmm d}, {xmm s}"
  | .padddMem d m => s!"paddd {xmm d}, {m.render "xmmword"}"
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
    | .jz t | .jnz t => some t
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

/-- A whole assembler file: the routines, then the read-only data, for x86-64 Linux and macOS only. -/
def file (routines : List (String × Array Instr)) (data : List (String × ByteArray)) : String :=
  "// Printed from the Lean programs in SszNative by `just lean-kernels`.\n" ++
  "// Do not edit: the regressions fail when this file differs from what they print.\n" ++
  "#if defined(__x86_64__) && !defined(_WIN32)\n" ++
  "#if defined(__APPLE__)\n#define SYMBOL(name) _##name\n#else\n#define SYMBOL(name) name\n#endif\n" ++
  "\t.intel_syntax noprefix\n\t.text\n" ++
  String.join (routines.map fun (name, program) => render name program) ++
  "#if defined(__APPLE__)\n\t.section __TEXT,__const\n#else\n\t.section .rodata\n#endif\n" ++
  String.join (data.map fun (name, bytes) => renderData name bytes) ++
  "#if defined(__linux__)\n\t.section .note.GNU-stack,\"\",@progbits\n#endif\n#endif\n"

end Ssz.Native.Asm
