import SszNative.Root
import SszNative.Branch
import SszNative.Schema
import SszNative.Kernel.Assembly

/-!
# `SszNative`

SSZ read straight from encodings, on native kernels proved against the specification.

    SszNative/Asm     x86-64 instructions as data, their model, and their printer
    SszNative/Kernel  the kernels as programs, and the assembler file they print to
    SszNative         hashing, trees, decoding checks, roots, and branches over byte buffers

Compiled code runs the kernels printed from these programs.
The proofs that they compute the specification sit under `SszNative/Proofs`.
-/
