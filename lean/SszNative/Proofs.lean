import SszNative
import SszNative.Proofs.Audit
import SszNative.Proofs.Asm.Run
import SszNative.Proofs.Asm.Machine
import SszNative.Proofs.Ir.Logic
import SszNative.Proofs.Ir.Link
import SszNative.Proofs.Asm.Spec
import SszNative.Proofs.Kernel.Sha256
import SszNative.Proofs.Kernel.ShaNi.Main
import SszNative.Proofs.Kernel.ShaNiDual.Main
import SszNative.Proofs.Kernel.Gather
import SszNative.Proofs.Kernel.GatherNode
import SszNative.Proofs.Kernel.Detect
import SszNative.Proofs.Reference
import SszNative.Proofs.Kernel.Avx512.Main
import SszNative.Proofs.Kernel.Avx512x2.Main
import SszNative.Proofs.Kernel.Avx2.Main
import SszNative.Proofs.Kernel.Baseline.Main
import SszNative.Proofs.Validate.Main
import SszNative.Proofs.Verify
import SszNative.Proofs.Root.Main
import SszNative.Proofs.Branch.Main
import SszNative.Proofs.Schema.Main
import SszNative.Proofs.Ir.Kernels
import SszNative.Proofs.Codec.View
import SszNative.Proofs.Codec.Assemble
import SszNative.Proofs.Driver.Codec
import SszNative.Proofs.Driver.Lay
import SszNative.Proofs.Driver.LayRun
import SszNative.Proofs.Driver.Serialize
import SszNative.Proofs.Driver.Root
import SszNative.Proofs.Driver.Gather
import SszNative.Proofs.Driver.Root.Bytes
import SszNative.Proofs.Driver.Root.Packed
import SszNative.Proofs.Driver.Root.Columns
import SszNative.Proofs.Driver.Root.Chunked
import SszNative.Proofs.Driver.Root.Need
import SszNative.Proofs.Driver.Root.RootsOf
import SszNative.Proofs.Driver.Root.ColumnPaths
import SszNative.Proofs.Driver.Root.Size
import SszNative.Proofs.Driver.Root.VectorOne
import SszNative.Proofs.Driver.Root.ContainerOne
import SszNative.Proofs.Driver.Root.Dispatch
import SszNative.Proofs.Driver.Root.Range
import SszNative.Proofs.Driver.Root.ByteList
import SszNative.Proofs.Driver.Root.Progressive
import SszNative.Proofs.Driver.Root.BitList
import SszNative.Proofs.Driver.Root.Grow
import SszNative.Proofs.Driver.Root.Elements
import SszNative.Proofs.Driver.Root.Sequence
import SszNative.Proofs.Driver.Root.Dispatcher
import SszNative.Proofs.Driver.Root.ListFacts
import SszNative.Proofs.Driver.Root.List
import SszNative.Proofs.Driver.Root.Union
import SszNative.Proofs.Driver.Root.Fields
import SszNative.Proofs.Driver.Root.Container
import SszNative.Proofs.Driver.Root.ProgressiveContainer
import SszNative.Proofs.Driver.Root.Top
import SszNative.Proofs.Driver.Tree
import SszNative.Proofs.Driver.Branch
import SszNative.Proofs.Driver.Prove
import SszNative.Proofs.Plan.Names
import SszNative.Proofs.Plan.Rename
import SszNative.Proofs.Driver.Validate.Main
import SszNative.Proofs.Driver.TreeStore
import SszNative.Proofs.Ir.Partial
import SszNative.Proofs.Driver.Validate.PlanSound
import SszNative.Proofs.Shipped

/-!
# `SszNative.Proofs`

The proofs that the native implementation computes the specification.

    SszNative/Proofs/Asm        running blocks of instructions, routines inside the whole machine, and the terms kernel theorems use
    SszNative/Proofs/Kernel     each kernel run on the model computes what its Lean body does
    SszNative/Proofs/Reference  the Lean bodies the kernels stand in for, byte by byte
    SszNative/Proofs/Validate   the decoding check refuses what deserialization refuses
    SszNative/Proofs/Root       the root of an encoding is the root of the value it decodes to
    SszNative/Proofs/Branch     nodes, branches, and multiproofs read from an encoding are the specification's
    SszNative/Proofs/Verify     the native verifiers answer what the specification's answer
    SszNative/Proofs/Schema     a compiled declaration reads values as the declaration itself does
    SszNative/Proofs/Ir         compiled code keeps its meaning, and the kernels keep their call contracts
    SszNative/Proofs/Codec      the ranges of a composite's parts are deserialization's slices, and assembly is serialization
    SszNative/Proofs/Driver     the compiled drivers compute what their Lean references compute
    SszNative/Proofs/Plan       a plan reads back as the type it was written from, its fields named by position
-/

-- The audit runs after every proof is imported, so a new proof module needs no entry.
audit_native
