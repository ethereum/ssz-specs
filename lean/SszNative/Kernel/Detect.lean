import SszNative.Asm.Machine

/-!
Which kernels the processor runs, asked of the processor itself.

The answer is a mask: bit 0 for the SHA kernels, bit 1 for the AVX-512 kernels, bit 2 for the AVX gathers,
and bit 3 for the AVX2 kernels.
It follows the Intel manual, volume 1, sections 13.2 and 15.2, as the model's feature checks do.

The routine reads three words and keeps them in scratch registers:

- r9 holds cpuid leaf 1's ecx: SSSE3, SSE4.1, AVX, and whether the extended control register is readable;
- r11 holds cpuid leaf 7's ebx, or zero when the processor has no leaf 7: SHA, AVX2, and the AVX-512 parts;
- r10 holds the extended control register's low half, or zero when it is unreadable: the saved register state.

Each feature bit is then one register shifted right and cut to its lowest bit.
A kernel family is usable when every bit it needs is set, so the mask is ands of these bits, with no branch.

cpuid writes rbx, which the caller keeps, so r8 holds it until the return.
No memory is touched.
-/

namespace EthLib.Consensus.Ssz.Native

open EthLib.Consensus.Ssz.Native.Asm

/--
The kernel families the processor runs, as a mask.

Bit 0: the SHA kernels, which need SHA, SSSE3, and SSE4.1.
Bit 1: the AVX-512 kernels, which need the foundation, the byte and word, and the vector length parts, and AVX.
Bit 2: the AVX gathers, which need AVX.
Bit 3: the AVX2 kernels, which need AVX2 and AVX.
-/
def Asm.Cpu.featureMask (cpu : Cpu) : UInt64 :=
  (if cpu.has .sha && cpu.has .ssse3 && cpu.has .sse41 then 1 else 0) |||
    (if cpu.has .avx512f && cpu.has .avx512bw && cpu.has .avx512vl && cpu.has .avx then 2 else 0) |||
    (if cpu.has .avx then 4 else 0) ||| (if cpu.has .avx2 && cpu.has .avx then 8 else 0)

namespace Kernel.Detect

/-- The register holding rbx until the return. -/
abbrev saved : Gpr := .r8

/-- The register holding cpuid leaf 1's ecx. -/
abbrev ecx1 : Gpr := .r9

/-- The register holding the extended control register's low half, or zero. -/
abbrev xcr : Gpr := .r10

/-- The register holding cpuid leaf 7's ebx, or zero. -/
abbrev ebx7 : Gpr := .r11

/-- The register holding the highest leaf, then the constant one. -/
abbrev one : Gpr := .rsi

/-- A temporary. -/
abbrev tmp : Gpr := .rdi

/-- The bit at a position of a register, anded into an accumulator. -/
def flag (acc w : Gpr) (k : Nat) : List Instr :=
  [.movReg tmp w, .shrImm tmp k, .alu .and tmp one, .alu .and acc tmp]

/-- Leaves 0 and 1: the highest leaf into the constant's register, leaf 1's ecx kept, and leaf 7's word cleared. -/
def leaves : List Instr :=
  [.movReg saved .rbx, .zeroReg .rax, .zeroReg .rcx, .cpuid, .movReg one .rax,
    .movImm .rax 1, .zeroReg .rcx, .cpuid, .movReg ecx1 .rcx, .zeroReg ebx7, .cmpImm one 7]

/-- Leaf 7, which the routine skips when the processor has no such leaf. -/
def leaf7 : List Instr :=
  [.movImm .rax 7, .zeroReg .rcx, .cpuid, .movReg ebx7 .rbx]

/-- The constant one, the control register's word cleared, and the bit saying whether it is readable. -/
def readable : List Instr :=
  [.movImm one 1, .zeroReg xcr, .movReg .rax ecx1, .shrImm .rax 27, .alu .and .rax one]

/--
The mask from the three words, rbx restored.

rax collects the SHA bits, and rdx the AVX bits.
rcx takes the AVX bits with the AVX2 one, which rax collects, then the AVX bits with the AVX-512 ones.
-/
def combine : List Instr :=
  [.movReg .rax one] ++ flag .rax ecx1 9 ++ flag .rax ecx1 19 ++ flag .rax ebx7 29 ++
    [.movReg .rdx one] ++ flag .rdx ecx1 28 ++ flag .rdx ecx1 27 ++ flag .rdx xcr 1 ++ flag .rdx xcr 2 ++
    [.movReg .rcx .rdx] ++ flag .rcx ebx7 5 ++ [.shlImm .rcx 3, .alu .or .rax .rcx] ++
    [.movReg .rcx .rdx] ++ flag .rcx ebx7 16 ++ flag .rcx ebx7 30 ++ flag .rcx ebx7 31 ++
    flag .rcx xcr 5 ++ flag .rcx xcr 6 ++ flag .rcx xcr 7 ++
    [.shlImm .rcx 1, .shlImm .rdx 2, .alu .or .rax .rcx, .alu .or .rax .rdx, .movReg .rbx saved]

end Kernel.Detect

open Kernel.Detect in
/--
The routine: no arguments, and the mask of usable kernel families in rax.

It skips leaf 7 when the highest leaf is below it, and the control register read when the system forbids it.
It changes only registers the caller does not keep, and no memory.
-/
def Kernel.detect : Array Instr :=
  ((leaves ++ [.jcc .b 16] ++ leaf7 ++ readable ++ [.jz 25, .zeroReg .rcx, .xgetbv, .movReg xcr .rax] ++
    combine ++ [.ret]) : List Instr).toArray

end EthLib.Consensus.Ssz.Native
