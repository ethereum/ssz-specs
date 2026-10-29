import SszNative.Kernel.Avx512

/-!
Thirty-two pairs of nodes hashed at once with AVX-512, as two batches of sixteen whose rounds interleave.

One batch's rounds wait on a chain of dependent operations, which leaves the vector units idle a third of the time.
A second batch's rounds, independent of the first, fill that wait.

Thirty-two registers cannot hold two states, two schedules, and their temporaries.
So each batch's schedule words live in a scratch area below the stack pointer.
Each step computes the word sixteen rounds ahead from four words in the scratch area, as the rounds read them.

The rounds run eight at a time in a loop, since the working words return to their registers every eight rounds.
Unrolled, the routine would not fit the processor's decoded-instruction cache, and decoding would bound its speed.

The first batch keeps its working words in registers 0 to 7, with its running sum and temporaries in 24 to 28.
The second batch keeps its working words in registers 8 to 15, with its running sum and temporaries in 16 to 20.
The schedule steps use registers 21 to 23 and 29.
After the first block, each batch's state goes to the scratch area, kept for the second feed-forward.
-/

namespace Ssz.Native.Kernel.Avx512x2

open Ssz.Native.Asm
open Ssz.Native.Kernel.Avx512 (left right out count tbl home ring tmp tableEntry role roundCode loadCode
  transposeIn swapIn transposeOut storeCode)

/-- The stack pointer, the base of the scratch area. -/
abbrev sp : Gpr := .rsp

/-- The pointer to the schedule words of the current eight rounds. -/
abbrev words : Gpr := .r10

/-- The pointer to the table's constants for the current eight rounds. -/
abbrev consts : Gpr := .r11

/-- The number of eight-round blocks left in the current loop. -/
abbrev blocks : Gpr := .r9

/-- Bytes of scratch: sixty-four schedule words and eight state words per batch, sixty-four bytes each, and a gap. -/
def frame : Nat := 10240

/--
Byte offset of batch b's schedule word t.

The two batches' words alternate, and word t sits below word t - 1.
So the first stores land just below the caller's frame and move down, and no guard page below the stack is skipped.
-/
def wordSlot (b t : Nat) : Nat := frame - 128 * (t + 1) + 64 * b

/-- Byte offset of batch b's working word j after the first block, at the bottom of the scratch area. -/
def midSlot (b j : Nat) : Nat := 64 * (8 * b + j)

/-- The schedule pointer's offset from the scratch area for eight-round block i. -/
def wordsBase (i : Nat) : Nat := 7168 - 1024 * i

/-- Byte offset of word 8i + m of batch b from block i's schedule pointer. -/
def wordRel (b m : Nat) : Nat := 3072 - 128 * (m + 1) + 64 * b

/--
The second batch's register for each of the first batch's.

Working words 0 to 7 trade places with 8 to 15, and the running sum and temporaries 24 to 28 with 16 to 20.
-/
def swapReg (r : Vreg) : Vreg :=
  if r.val < 8 then r + 8
  else if r.val < 16 then r - 8
  else if r.val < 21 then r + 8
  else if 24 ≤ r.val ∧ r.val < 29 then r - 8
  else r

/-- An instruction with its vector registers renamed, for the instructions the rounds use. -/
def rename (f : Vreg → Vreg) : Instr → Instr
  | .vmov d a => .vmov (f d) (f a)
  | .vadd d a b => .vadd (f d) (f a) (f b)
  | .vaddMem d a m => .vaddMem (f d) (f a) m
  | .vror d a k => .vror (f d) (f a) k
  | .vshr d a k => .vshr (f d) (f a) k
  | .vternlog d a b t => .vternlog (f d) (f a) (f b) t
  | .vload d m => .vload (f d) m
  | i => i

/-- Batch b's copy of the first batch's instructions. -/
def forBatch (b : Nat) (code : List Instr) : List Instr :=
  if b = 0 then code else code.map (rename swapReg)

/-- The schedule steps' registers. -/
def sa : Vreg := 21

@[inherit_doc sa] def sb : Vreg := 22

@[inherit_doc sa] def sc : Vreg := 23

@[inherit_doc sa] def sd : Vreg := 29

/-- Batch b's word 8i + k + 16, from the four words it depends on, in block i. -/
def scheduleStep (b k : Nat) : List Instr :=
  [.vload sa ⟨words, wordRel b (k + 14)⟩, .vror sb sa 17, .vror sc sa 19, .vshr sa sa 10, .vternlog sa sb sc 0x96,
    .vload sb ⟨words, wordRel b (k + 1)⟩, .vror sc sb 7, .vror sd sb 18, .vshr sb sb 3, .vternlog sb sc sd 0x96,
    .vadd sa sa sb, .vaddMem sa sa ⟨words, wordRel b k⟩, .vaddMem sa sa ⟨words, wordRel b (k + 9)⟩,
    .vstore ⟨words, wordRel b (k + 16)⟩ sa]

/-- Batch b's first-block round 8i + k: T1 starts as H plus the schedule word, then the round constant joins it. -/
def firstRound (b k : Nat) : List Instr :=
  forBatch b (match roundCode k (.vaddMem Avx512.t1 (role k 7) ⟨words, wordRel b k⟩) with
    | seed :: rest => seed :: .vaddMem Avx512.t1 Avx512.t1 ⟨consts, 64 * k⟩ :: rest
    | [] => [])

/-- Batch b's padding round 8i + k: T1 starts as H plus the table's precomputed word and constant. -/
def paddingRound (b k : Nat) : List Instr :=
  forBatch b (roundCode k (.vaddMem Avx512.t1 (role k 7) ⟨consts, 64 * k⟩))

/-- Eight first-block rounds of both batches, with or without their schedule steps, then the pointer updates. -/
def firstBlock (scheduled : Bool) : List Instr :=
  (List.range 8).flatMap (fun k =>
    firstRound 0 k ++ firstRound 1 k ++ (if scheduled then scheduleStep 0 k ++ scheduleStep 1 k else [])) ++
  [.subImm words 1024, .addImm consts 512, .subImm blocks 1]

/-- Eight padding rounds of both batches, then the pointer update. -/
def paddingBlock : List Instr :=
  (List.range 8).flatMap (fun k => paddingRound 0 k ++ paddingRound 1 k) ++ [.addImm consts 512, .subImm blocks 1]

/-- Load and transpose one batch's sixteen messages, and store its sixteen input words. -/
def loadStore (ls rs b : Nat) : List Instr :=
  loadCode ls rs ++ transposeIn ++ swapIn ++ (List.range 16).map fun t => .vstore ⟨sp, wordSlot b t⟩ (ring t)

/-- Batch b's initial state in every lane. -/
def ivCode (b : Nat) : List Instr :=
  forBatch b ((List.range 8).map fun j => .vload (home j) (tableEntry (ivAvx512 j)))

/-- Batch b's first feed-forward, its state stored for the second. -/
def feedCode (b : Nat) : List Instr :=
  (List.range 8).flatMap fun j =>
    forBatch b [.vaddMem (home j) (home j) (tableEntry (ivAvx512 j))] ++
      [.vstore ⟨sp, midSlot b j⟩ (if b = 0 then home j else swapReg (home j))]

/-- Batch b's second feed-forward, from its stored state. -/
def finishCode (b : Nat) : List Instr :=
  forBatch b ((List.range 8).map fun j => .vaddMem (home j) (home j) ⟨sp, midSlot b j⟩)

/-- Everything before the first loop: both batches' input words, initial states, and the loop's pointers. -/
def setupCode (ls rs : Nat) : List Instr :=
  loadStore ls rs 0 ++ [.addImm left (16 * ls), .addImm right (16 * rs)] ++ loadStore ls rs 1 ++
  ivCode 0 ++ ivCode 1 ++ [.movReg words sp, .addImm words (wordsBase 0), .movReg consts tbl, .movImm blocks 6]

/-- Between the second loop and the third: both first feed-forwards, and the third loop's count. -/
def middleCode : List Instr :=
  feedCode 0 ++ feedCode 1 ++ [.movImm blocks 8]

/-- After the third loop: both second feed-forwards and the stores, the second batch sixteen digests further. -/
def outputCode : List Instr :=
  finishCode 0 ++ transposeOut ++ storeCode ++ [.addImm out 512] ++
  finishCode 1 ++ (List.range 8).map (fun j => .vmov (home j) (swapReg (home j))) ++ transposeOut ++ storeCode

/-- The instructions of one batch pair, with its three loops branching back to the indices given. -/
def batchCode (ls rs first second third : Nat) : List Instr :=
  setupCode ls rs ++ firstBlock true ++ [.jnz first, .movImm blocks 2] ++ firstBlock false ++ [.jnz second] ++
  middleCode ++ paddingBlock ++ [.jnz third] ++ outputCode

/-- Instruction index of the batch loop's head, after the frame and the empty-count check. -/
def loopHead : Nat := 3

/-- Instruction index of the first loop's head. -/
def firstHead (ls rs : Nat) : Nat := loopHead + (setupCode ls rs).length

/-- Instruction index of the second loop's head. -/
def secondHead (ls rs : Nat) : Nat := firstHead ls rs + (firstBlock true).length + 2

/-- Instruction index of the third loop's head. -/
def thirdHead (ls rs : Nat) : Nat := secondHead ls rs + (firstBlock false).length + 1 + middleCode.length

/-- One batch pair's instructions, at their place in the routine. -/
def body (ls rs : Nat) : List Instr :=
  batchCode ls rs (firstHead ls rs) (secondHead ls rs) (thirdHead ls rs)

/--
The routine: thirty-two digests per batch pair, for a count of batch pairs.

The arguments and strides are those of the sixteen-lane kernel, with the count in units of thirty-two pairs.
-/
def program (ls rs : Nat) : Array Instr :=
  let tail := [.addImm left (16 * ls), .addImm right (16 * rs), .addImm out 512, .subImm count 1, .jnz loopHead]
  let finish := loopHead + (body ls rs).length + tail.length
  (([.subImm sp frame, .test count, .jz finish] ++ body ls rs ++ tail ++
    [.addImm sp frame, .vzeroupper, .zeroReg .rax, .ret]) : List Instr).toArray

end Ssz.Native.Kernel.Avx512x2
