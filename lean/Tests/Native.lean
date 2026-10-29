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

/-- Restricts the native library to the kernels a mask keeps: 1 for SHA-NI, 2 for AVX-512, 4 for AVX, 8 for AVX2. -/
@[extern "ssz_native_restrict"]
private opaque restrict (mask : UInt32) : BaseIO Unit

/-- The currently enabled CPU/OS capabilities, with the same bit meanings as restrict. -/
@[extern "ssz_native_features"]
private opaque features : BaseIO UInt32

/-- Reset and enable coverage counters. Ordinary executables leave these disabled. -/
@[extern "ssz_native_test_begin"]
private opaque beginCoverage : BaseIO Unit

/-- Nonempty native calls, fallbacks, and rejected bounds; see native/bindings.c. -/
@[extern "ssz_native_test_count"]
private opaque pathCount (index : UInt32) : BaseIO UInt64

/-- Restore the ordinary path with coverage instrumentation disabled. -/
@[extern "ssz_native_test_end"]
private opaque endCoverage : BaseIO Unit

/-- Every kernel's result is its reference's, at every count and at offsets that misalign the nodes. -/
private def kernelsMatch (input : IO.Ref (ByteArray × ByteArray)) : IO Unit := do
  -- Read through IO so closed pure calls cannot be memoized across feature masks.
  let (src, other) ← input.get
  for count in counts do
    for offset in [0, 1, 32, 33] do
      let o := offset.toUSize
      let n := count.toUSize
      expect s!"pairs {count} at {offset}" (hashPairs src o n == hashPairsReference src o n)
      expect s!"columns {count} at {offset}"
        (hashColumns src o other (o + 5) n == hashColumnsReference src o other (o + 5) n)
      expect s!"fixed {count} at {offset}" (hashFixed src o other n == hashFixedReference src o other n)
  -- Inputs running past the end of their arrays take the reference's reading of them.
  expect "pairs past the end" (hashPairs src 97 1024 == hashPairsReference src 97 1024)
  expect "fixed against a short node" (hashFixed src 0 (pattern 31 3) 4 == hashFixedReference src 0 (pattern 31 3) 4)
  -- Fields of every width a gather meets, from strides that skip, abut, or repeat them.
  for (width, stride, slot) in [(0, 0, 32), (1, 13, 32), (2, 5, 32), (4, 121, 32), (8, 8, 32), (8, 121, 32),
      (16, 17, 32), (32, 121, 32), (48, 121, 64), (48, 48, 64), (8, 121, 8), (20, 121, 32)] do
    for count in [0, 1, 2, 17, 300] do
      let w := width.toUSize
      expect s!"gather {width} {stride} {slot} {count}"
        (gather src 3 stride.toUSize w count.toUSize slot.toUSize ==
          gatherReference src 3 stride.toUSize w count.toUSize slot.toUSize)

/-- Partial final nodes and cursors actually rejected by the C guards. -/
private def boundariesMatch (input : IO.Ref (ByteArray × ByteArray)) : IO Unit := do
  let (src, other) ← input.get
  for remaining in [0, 1, 31, 32, 33, 63, 64] do
    let truncated := src.extract 0 (3 + 64 + remaining)
    for count in [0, 2] do
      expect s!"pairs final bytes {remaining}, count {count}"
        (hashPairs truncated 3 count.toUSize == hashPairsReference truncated 3 count.toUSize)
  for remaining in [0, 1, 31, 32] do
    let short := src.extract 0 (3 + 32 + remaining)
    expect s!"columns short left {remaining}"
      (hashColumns short 3 other 5 2 == hashColumnsReference short 3 other 5 2)
    expect s!"columns short right {remaining}"
      (hashColumns other 5 short 3 2 == hashColumnsReference other 5 short 3 2)
  let past := (src.size + 1).toUSize
  expect "pairs offset past end" (hashPairs src past 1 == hashPairsReference src past 1)
  expect "columns offset past end"
    (hashColumns src past other 0 1 == hashColumnsReference src past other 0 1)
  -- The final source cursor, although unused, is a premise of the gather theorem.
  let byte := src.extract 0 1
  let stride := (0 : USize) - 1
  expect "gather final cursor outside theorem domain"
    (gather byte 0 stride 1 1 32 == gatherReference byte 0 stride 1 1 32)

/-- Assert and report executed paths, rather than inferring execution from a mask. -/
private def reportCoverage (mask active : UInt32) : IO Unit := do
  IO.println s!"native mask {mask}, enabled features {active}"
  for (layout, base) in [("pairs", 0), ("columns", 1), ("fixed", 2)] do
    let answered ← pathCount base.toUInt32
    let fallbacks ← pathCount (base + 3).toUInt32
    let rejected ← pathCount (base + 6).toUInt32
    -- Every x86-64 processor has a hashing kernel, down to the baseline one, so the dispatcher always answers.
    expect s!"{layout}: dispatcher unexecuted" (answered != 0)
    expect s!"{layout}: reference fallback unexecuted" (fallbacks != 0)
    expect s!"{layout}: bounds refusal unexecuted" (rejected != 0)
    IO.println s!"  {layout}: dispatcher {answered}, fallback {fallbacks}, bounds refused {rejected}"
  let optimized ← pathCount 10
  if active &&& 4 != 0 then expect "AVX gather unexecuted" (optimized != 0)
  else expect "disabled AVX gather executed" (optimized == 0)
  let gatherFallback ← pathCount 11
  expect "gather cursor fallback unexecuted" (gatherFallback != 0)
  IO.println s!"  gather: general {← pathCount 9}, AVX {optimized}, fallback {gatherFallback}"

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
    vec := fun _ _ => 0, zf := false, cf := false, cpu := ⟨fun _ _ => (0, 0, 0, 0), 0⟩, mem, pc := 0,
    status := .running }

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
          ("SHA-NI dual", Kernel.ShaNiDual.program ls rs, 2, 4), ("AVX2", Kernel.Avx2.program ls rs, 2, 16),
          ("AVX-512 x32", Kernel.Avx512x2.program ls rs, 1, 32), ("baseline", Kernel.Baseline.program ls rs, 2, 8)] do
      -- The stack pointer leaves room below it for the kernels that keep scratch there.
      let s := entry mem [(.rdi, output), (.rsi, input), (.rdx, input + right), (.rcx, units), (.r8, tbl),
        (.rsp, 1 <<< 30)]
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

/-- The operand check accepts each encoding field's largest value and refuses the values past it. -/
private def operandsChecked : IO Unit := do
  -- Each case: an instruction, the length of the program holding it, and whether it fits.
  let cases : List (Instr × Nat × Bool) :=
    -- The displacement field is signed 32-bit, and the assembler turns 2^64 - 1 into -1.
    [(.movdqu 0 ⟨.rsi, 2 ^ 31 - 1⟩, 1, true), (.movdqu 0 ⟨.rsi, 2 ^ 31⟩, 1, false),
      (.vload 0 ⟨.rsi, 2 ^ 64 - 1⟩, 1, false),
      -- Add and subtract immediates are sign-extended from 32 bits.
      (.addImm .rsi (2 ^ 31 - 1), 1, true), (.subImm .rsi (2 ^ 31), 1, false),
      -- Counts are one byte.
      (.vror 0 0 255, 1, true), (.vshr 0 0 256, 1, false), (.palignr 0 0 256, 1, false),
      -- Legacy SSE stops at register 15, while the EVEX form of the same load reaches 31.
      (.movdqa 15 15, 1, true), (.movdqa 16 0, 1, false), (.movdqu 16 ⟨.rsi, 0⟩, 1, false),
      (.vload16 31 ⟨.rsi, 0⟩, 1, true),
      -- A branch lands on an instruction of its program.
      (.jz 1, 2, true), (.jnz 2, 2, false)]
  for (instr, size, fits) in cases do
    expect s!"operand check of {repr instr}" (instr.valid size == fits)

/-- The committed assembler file is the one the Lean programs print. -/
private def kernelsFresh : IO Unit := do
  let committed ← IO.FS.readFile "native/kernels_x86.S"
  expect "native/kernels_x86.S is stale: run `just lean-kernels`" (committed == assembly)

def run : IO Unit := do
  let available ← features
  IO.println s!"native hardware: SHA-NI {available &&& 1 != 0}, AVX-512 {available &&& 2 != 0}, AVX {available &&& 4 != 0}"
  if (← IO.getEnv "SSZ_REQUIRE_AVX512") == some "1" && available &&& 2 == 0 then
    throw (IO.userError "AVX-512 hardware required by SSZ_REQUIRE_AVX512=1 but unavailable")
  if available &&& 2 == 0 then IO.println "SKIP AVX-512 hardware execution: unavailable; model tests still run"
  let input ← IO.mkRef (pattern (64 * 1024 + 96) 1, pattern (32 * 1024 + 64) 2)
  -- Every dispatch path the processor allows: both hashing kernels, each alone, and neither.
  -- Every kernel family alone and together: AVX2 is bit 8, and mask 0 leaves the baseline kernel.
  for mask in [15, 7, 6, 5, 4, 8, 0] do
    restrict mask
    let active ← features
    expect "feature restriction mismatch" (active == available &&& mask)
    beginCoverage
    kernelsMatch input
    boundariesMatch input
    reportCoverage mask active
  endCoverage
  restrict 15
  modelMatches
  operandsChecked
  kernelsFresh

end Tests.Native
