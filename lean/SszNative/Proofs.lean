import SszNative
import Ssz.Proofs.Audit
import SszNative.Proofs.Asm.Run
import SszNative.Proofs.Asm.Spec
import SszNative.Proofs.Kernel.Sha256
import SszNative.Proofs.Kernel.ShaNi.Main
import SszNative.Proofs.Kernel.ShaNiDual.Main
import SszNative.Proofs.Kernel.Gather
import SszNative.Proofs.Kernel.GatherNode
import SszNative.Proofs.Reference
import SszNative.Proofs.Kernel.Avx512.Main
import SszNative.Proofs.Validate.Main
import SszNative.Proofs.Verify
import SszNative.Proofs.Root.Main
import SszNative.Proofs.Branch.Main
import SszNative.Proofs.Schema.Main

/-!
# `SszNative.Proofs`

The proofs that the native implementation computes the specification.

    SszNative/Proofs/Asm        running blocks of instructions, and the terms kernel theorems use
    SszNative/Proofs/Kernel     each kernel run on the model computes what its Lean body does
    SszNative/Proofs/Reference  the Lean bodies the kernels stand in for, byte by byte
    SszNative/Proofs/Validate   the decoding check refuses what deserialization refuses
    SszNative/Proofs/Root       the root of an encoding is the root of the value it decodes to
    SszNative/Proofs/Branch     nodes, branches, and multiproofs read from an encoding are the specification's
    SszNative/Proofs/Verify     the native verifiers answer what the specification's answer
    SszNative/Proofs/Schema     a compiled declaration reads values as the declaration itself does
-/

-- The audit runs after every proof is imported, so a new proof module needs no entry.
audit_ssz
