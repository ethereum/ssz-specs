import SszNative
import SszNative.Asm.Semantics

/-! The native kernels against their Lean references, and against the machine model they are proved on. -/

namespace Tests.Native

open Ssz Ssz.Native Ssz.Native.Asm

private def expect (label : String) (holds : Bool) : IO Unit := do
  -- Stop at the first disagreement, naming the case.
  unless holds do throw (IO.userError label)

/-- Bytes that differ at every position, so a misplaced read shows. -/
private def pattern (size seed : Nat) : ByteArray :=
  ⟨(Array.range size).map fun i => UInt8.ofNat ((i * 131 + seed * 7 + i / 251) % 256)⟩

/-- Counts on both sides of the sixteen-pair batches, up to a thousand pairs. -/
private def counts : List Nat :=
  (List.range 40) ++ [47, 48, 49, 63, 64, 65, 255, 256, 257, 1000]

/-- Restricts the native library to the kernels a mask keeps: 1 for SHA-NI, 2 for AVX-512, 4 for AVX. -/
@[extern "ssz_native_restrict"]
private opaque restrict (mask : UInt32) : BaseIO Unit

/-- Every kernel's result is its reference's, at every count and at offsets that misalign the nodes. -/
private def kernelsMatch : IO Unit := do
  let src := pattern (64 * 1024 + 96) 1
  let other := pattern (32 * 1024 + 64) 2
  for count in counts do
    for offset in [0, 1, 32, 33] do
      let o := offset.toUSize
      let n := count.toUSize
      expect s!"pairs {count} at {offset}" (hashPairs src o n == hashPairsReference src o n)
      expect s!"columns {count} at {offset}"
        (hashColumns src o other (o + 5) n == hashColumnsReference src o other (o + 5) n)
      expect s!"fixed {count} at {offset}" (hashFixed src o other n == hashFixedReference src o other n)
  -- Inputs running past the end of their arrays take the reference's reading of them.
  expect "pairs past the end" (hashPairs src 64 1024 == hashPairsReference src 64 1024)
  expect "fixed against a short node" (hashFixed src 0 (pattern 31 3) 4 == hashFixedReference src 0 (pattern 31 3) 4)
  -- Fields of every width a gather meets, from strides that skip, abut, or repeat them.
  for (width, stride, slot) in [(0, 0, 32), (1, 13, 32), (2, 5, 32), (4, 121, 32), (8, 8, 32), (8, 121, 32),
      (16, 17, 32), (32, 121, 32), (48, 121, 64), (48, 48, 64), (8, 121, 8), (20, 121, 32)] do
    for count in [0, 1, 2, 17, 300] do
      let w := width.toUSize
      expect s!"gather {width} {stride} {slot} {count}"
        (gather src 3 stride.toUSize w count.toUSize slot.toUSize ==
          gatherReference src 3 stride.toUSize w count.toUSize slot.toUSize)

/-- Memory holding byte arrays at given addresses, and zeros elsewhere. -/
private def memoryOf (regions : List (Nat × ByteArray)) : Nat → UInt8 := fun a =>
  match regions.find? fun (base, b) => base ≤ a ∧ a < base + b.size with
  | some (base, b) => b.get! (a - base)
  | none => 0

/-- A run of the model whose vector registers are evaluated at every step, so lanes never pile up unevaluated work. -/
private def runStrict (program : Array Instr) : Nat → State → State
  | 0, s => s
  | steps + 1, s =>
    if s.status != .running then s
    else
      let next := step program s
      let lanes := Array.ofFn (n := 32) fun r => Array.ofFn (n := 16) fun l => next.vec r l
      runStrict program steps { next with vec := fun r l => lanes[r]![l]! }

/-- The machine at a routine's entry, with arguments in registers. -/
private def entry (mem : Nat → UInt8) (args : List (Gpr × Nat)) : State :=
  { gpr := fun r => ((args.find? (·.1 == r)).map (·.2.toUInt64)).getD 0,
    vec := fun _ _ => 0, zf := false, mem, pc := 0, status := .running }

/-- The model computes what the processor computes, on the same inputs. -/
private def modelMatches : IO Unit := do
  let src := pattern 2048 4
  let (tbl, input, output) := (1 <<< 20, 1 <<< 24, 1 <<< 28)
  let mem := memoryOf [(tbl, Kernel.table), (input, src)]
  -- Each layout: adjacent pairs, two columns, and a column against one node.
  for (layout, ls, rs, right) in [("pairs", 64, 64, 32), ("columns", 32, 32, 1024), ("fixed", 32, 0, 1024)] do
    -- Two iterations of each hashing kernel.
    for (name, program, units, pairs) in
        [("AVX-512", Kernel.Avx512.program ls rs, 2, 32), ("SHA-NI", Kernel.ShaNi.program ls rs, 2, 2),
          ("SHA-NI dual", Kernel.ShaNiDual.program ls rs, 2, 4)] do
      let s := entry mem [(.rdi, output), (.rsi, input), (.rdx, input + right), (.rcx, units), (.r8, tbl)]
      let f := runStrict program 20000 s
      let got : ByteArray := ⟨(Array.range (32 * pairs)).map fun i => f.mem (output + i)⟩
      let n := pairs.toUSize
      let expected :=
        if rs == 64 then hashPairs src 0 n
        else if rs == 32 then hashColumns src 0 src 1024 n
        else hashFixed src 0 (src.extract 1024 1056) n
      expect s!"{name} {layout} returns on the model" (f.status == .returned)
      expect s!"{name} {layout} on the model" (got == expected)
  -- Fields of every width with a routine of its own, 50 bytes apart.
  for (width, program, slot) in [(1, Kernel.gatherNode 1, 32), (2, Kernel.gatherNode 2, 32), (4, Kernel.gatherNode 4, 32),
      (8, Kernel.gatherNode 8, 32), (16, Kernel.gatherNode 16, 32), (32, Kernel.gatherNode 32, 32),
      (48, Kernel.gatherKey, 64)] do
    let s := entry mem [(.rdi, output), (.rsi, input + 3), (.rdx, 5), (.rcx, width), (.r8, 50 - width),
      (.r9, slot - width)]
    let f := runStrict program 1000 s
    let got : ByteArray := ⟨(Array.range (slot * 5)).map fun i => f.mem (output + i)⟩
    expect s!"gather of width {width} on the model"
      (f.status == .returned && got == gather src 3 50 width.toUSize 5 slot.toUSize)
  -- Fields of 10 bytes, 24 apart, into 32-byte slots.
  let s := entry mem [(.rdi, output), (.rsi, input + 3), (.rdx, 5), (.rcx, 10), (.r8, 14), (.r9, 22)]
  let f := runStrict Kernel.gather 1000 s
  let got : ByteArray := ⟨(Array.range (32 * 5)).map fun i => f.mem (output + i)⟩
  expect "gather on the model" (f.status == .returned && got == gather src 3 24 10 5 32)

/-- The committed assembler file is the one the Lean programs print. -/
private def kernelsFresh : IO Unit := do
  let committed ← IO.FS.readFile "native/kernels_x86.S"
  expect "native/kernels_x86.S is stale: run `just lean-kernels`" (committed == assembly)

def run : IO Unit := do
  -- Every dispatch path the processor allows: both hashing kernels, each alone, and neither.
  for mask in [7, 6, 5, 4, 0] do
    restrict mask
    kernelsMatch
  restrict 7
  modelMatches
  kernelsFresh

end Tests.Native
