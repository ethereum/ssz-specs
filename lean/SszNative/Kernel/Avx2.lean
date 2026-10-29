import SszNative.Asm.Instr
import SszNative.Kernel.Constants

/-!
Eight pairs of nodes hashed at once with AVX2, for processors with neither AVX-512 nor the SHA instructions.

Lane j of every 256-bit register belongs to pair j.
Each pair is a 64-byte message, so its hash is two compressions, the second over the constant padding block.

Sixteen registers hold one state, a running sum, and a few temporaries, but not a schedule.
So the schedule words live in a scratch area below the stack pointer, one 32-byte row per word.
Each step computes the word sixteen rounds ahead from four words in the scratch area, as the rounds read them.

AVX2 has no rotation, so each rotation is two shifts, and the three of a mixing function are folded into one exclusive or.
The rounds run eight at a time in a loop, since the working words return to their registers every eight rounds.

Registers 0 to 7 hold the working words, renamed rather than moved each round.
Registers 8 to 11 hold the running sum and two temporaries, and registers 12 to 15 the schedule step's temporaries.
-/

namespace Ssz.Native.Kernel.Avx2

open Ssz.Native.Asm

/-- The output address, the first argument. -/
abbrev out : Gpr := .rdi

/-- The address of the first left node, the second argument. -/
abbrev left : Gpr := .rsi

/-- The address of the first right node, the third argument. -/
abbrev right : Gpr := .rdx

/-- The number of batches of eight pairs, the fourth argument. -/
abbrev count : Gpr := .rcx

/-- The constant table's address, the fifth argument. -/
abbrev tbl : Gpr := .r8

/-- The stack pointer, the base of the scratch area. -/
abbrev sp : Gpr := .rsp

/-- The pointer to the schedule words of the current eight rounds. -/
abbrev words : Gpr := .r10

/-- The pointer to the table's constants for the current eight rounds. -/
abbrev consts : Gpr := .r11

/-- The number of eight-round blocks left in the current loop. -/
abbrev blocks : Gpr := .r9

/-- Bytes of scratch: sixty-four schedule words and eight state words, 32 bytes each, and a gap. -/
def frame : Nat := 2560

/--
Byte offset of schedule word t.

Word t sits below word t - 1, so the first stores land just below the caller's frame and move down.
No guard page below the stack is skipped.
-/
def wordSlot (t : Nat) : Nat := frame - 32 * (t + 1)

/-- Byte offset of working word j after the first block, at the bottom of the scratch area. -/
def midSlot (j : Nat) : Nat := 32 * j

/-- The schedule pointer's offset from the scratch area for eight-round block i. -/
def wordsBase (i : Nat) : Nat := 1792 - 256 * i

/-- Byte offset of word 8i + m from block i's schedule pointer. -/
def wordRel (m : Nat) : Nat := 768 - 32 * (m + 1)

/-- The home register of working word j. -/
def home (j : Nat) : Vreg := ⟨j % 8, by omega⟩

/-- The register holding working word j at round t: every round shifts each word one place along. -/
def role (t j : Nat) : Vreg := home (j + 8 - t % 8)

/-- The round's running sum. -/
def t1 : Vreg := 8

/-- The round's temporaries. -/
def x : Vreg := 9

@[inherit_doc x] def y : Vreg := 10

@[inherit_doc x] def z : Vreg := 11

/-- The schedule step's temporaries. -/
def sa : Vreg := 12

@[inherit_doc sa] def sb : Vreg := 13

@[inherit_doc sa] def sc : Vreg := 14

@[inherit_doc sa] def sd : Vreg := 15

/-- A 32-byte row of the table, whose first eight lanes are those of a sixteen-lane row. -/
def tableEntry (offset : Nat) : Mem := ⟨tbl, offset⟩

/--
The exclusive or of three rotations of a word into a temporary, with a second temporary.

A right rotation by k is a right shift by k or'ed with a left shift by 32 - k.
The two halves of the three rotations are disjoint, so all six terms fold into one exclusive or.
-/
def mix (d e : Vreg) (k₁ k₂ k₃ : Nat) : List Instr :=
  [.yshr d e k₁, .yshl y e (32 - k₁), .yxor d d y,
    .yshr y e k₂, .yshl z e (32 - k₂), .yxor y y z, .yxor d d y,
    .yshr y e k₃, .yshl z e (32 - k₃), .yxor y y z, .yxor d d y]

/-- One round, after the seed that sets the running sum to H plus the round's word and constant. -/
def roundTail (t : Nat) : List Instr :=
  let a := role t 0
  let b := role t 1
  let c := role t 2
  let d := role t 3
  let e := role t 4
  let f := role t 5
  let g := role t 6
  let h := role t 7
  -- Choice takes f where e is set and g elsewhere; it joins the sum, and the sum joins d, before the mixing of e.
  [.yand x e f, .yandn y e g, .yxor x x y, .yadd t1 t1 x, .yadd d d t1] ++
  mix x e 6 11 25 ++ [.yadd d d x, .yadd t1 t1 x] ++
  mix x a 2 13 22 ++
  -- Majority is c where a and b differ, and their common bit elsewhere.
  [.yxor y a b, .yand y y c, .yand z a b, .yxor y y z, .yadd h t1 x, .yadd h h y]

/-- A first-block round: T1 starts as H plus the schedule word, then the round constant joins it. -/
def firstRound (k : Nat) : List Instr :=
  [.yaddMem t1 (role k 7) ⟨words, wordRel k⟩, .yaddMem t1 t1 ⟨consts, 64 * k⟩] ++ roundTail k

/-- A padding round: T1 starts as H plus the table's precomputed word and constant. -/
def paddingRound (k : Nat) : List Instr :=
  .yaddMem t1 (role k 7) ⟨consts, 64 * k⟩ :: roundTail k

/-- Word 8i + k + 16, from the four words it depends on, in block i. -/
def scheduleStep (k : Nat) : List Instr :=
  [.vloadHalf sa ⟨words, wordRel (k + 14)⟩,
    .yshr sb sa 17, .yshl sc sa 15, .yxor sb sb sc, .yshr sc sa 19, .yxor sb sb sc, .yshl sc sa 13, .yxor sb sb sc,
    .yshr sa sa 10, .yxor sb sb sa,
    .vloadHalf sa ⟨words, wordRel (k + 1)⟩,
    .yshr sc sa 7, .yshl sd sa 25, .yxor sc sc sd, .yshr sd sa 18, .yxor sc sc sd, .yshl sd sa 14, .yxor sc sc sd,
    .yshr sa sa 3, .yxor sc sc sa,
    .yadd sb sb sc, .yaddMem sb sb ⟨words, wordRel k⟩, .yaddMem sb sb ⟨words, wordRel (k + 9)⟩,
    .vstoreHalf ⟨words, wordRel (k + 16)⟩ sb]

/-- Eight first-block rounds, with or without their schedule steps, then the pointer updates. -/
def firstBlock (scheduled : Bool) : List Instr :=
  (List.range 8).flatMap (fun k => firstRound k ++ (if scheduled then scheduleStep k else [])) ++
  [.subImm words 256, .addImm consts 512, .subImm blocks 1]

/-- Eight padding rounds, then the pointer update. -/
def paddingBlock : List Instr :=
  (List.range 8).flatMap paddingRound ++ [.addImm consts 512, .subImm blocks 1]

/-- The mask register for the byte reversal. -/
def mask : Vreg := 15

/--
The eight-by-eight transpose of 32-bit lanes, from registers 0 to 7 into the registers `transposed` lists.

Pairs of lanes interleave, then pairs of 64-bit lanes, then the 128-bit halves swap places.
-/
def transpose : List Instr :=
  [.yunpackLo32 8 0 1, .yunpackHi32 9 0 1, .yunpackLo32 10 2 3, .yunpackHi32 11 2 3,
    .yunpackLo32 12 4 5, .yunpackHi32 13 4 5, .yunpackLo32 14 6 7, .yunpackHi32 0 6 7,
    .yunpackLo64 1 8 10, .yunpackHi64 2 8 10, .yunpackLo64 3 9 11, .yunpackHi64 4 9 11,
    .yunpackLo64 5 12 14, .yunpackHi64 6 12 14, .yunpackLo64 7 13 0, .yunpackHi64 8 13 0,
    .yperm128 9 1 5 0x20, .yperm128 10 1 5 0x31, .yperm128 11 2 6 0x20, .yperm128 12 2 6 0x31,
    .yperm128 13 3 7 0x20, .yperm128 14 3 7 0x31, .yperm128 0 4 8 0x20, .yperm128 1 4 8 0x31]

/-- Where the transpose leaves row t: lane j of it holds lane t of register j. -/
def transposed (t : Nat) : Vreg :=
  match t with
  | 0 => 9 | 1 => 11 | 2 => 13 | 3 => 0 | 4 => 10 | 5 => 12 | 6 => 14 | _ => 1

/--
Load eight nodes, reverse their words' bytes, transpose, and store eight schedule words from word `first` on.

Node j is at the base register plus the stride times j.
-/
def loadWords (base : Gpr) (stride first : Nat) : List Instr :=
  (List.range 8).map (fun j => .vloadHalf (home j) ⟨base, stride * j⟩) ++ [.vloadHalf mask (tableEntry bswapAvx512)] ++
  (List.range 8).map (fun j => .yshufb (home j) (home j) mask) ++ transpose ++
  (List.range 8).map (fun t => .vstoreHalf ⟨sp, wordSlot (first + t)⟩ (transposed t))

/-- The initial state in every lane. -/
def ivCode : List Instr :=
  (List.range 8).map fun j => .vloadHalf (home j) (tableEntry (ivAvx512 j))

/-- The first feed-forward, the state stored for the second. -/
def feedCode : List Instr :=
  (List.range 8).flatMap fun j =>
    [.yaddMem (home j) (home j) (tableEntry (ivAvx512 j)), .vstoreHalf ⟨sp, midSlot j⟩ (home j)]

/-- The second feed-forward, from the stored state. -/
def finishCode : List Instr :=
  (List.range 8).map fun j => .yaddMem (home j) (home j) ⟨sp, midSlot j⟩

/-- Everything before the first loop: the input words, the initial state, and the loop's pointers. -/
def setupCode (ls rs : Nat) : List Instr :=
  loadWords left ls 0 ++ loadWords right rs 8 ++
  ivCode ++ [.movReg words sp, .addImm words (wordsBase 0), .movReg consts tbl, .movImm blocks 6]

/-- Between the second loop and the third: the first feed-forward, and the third loop's count. -/
def middleCode : List Instr :=
  feedCode ++ [.movImm blocks 8]

/-- After the third loop: the second feed-forward, the transpose back, and the stores of eight digests. -/
def outputCode : List Instr :=
  finishCode ++ [.vloadHalf mask (tableEntry bswapAvx512)] ++ transpose ++
  (List.range 8).map (fun j => .yshufb (transposed j) (transposed j) mask) ++
  (List.range 8).map (fun j => .vstoreHalf ⟨out, 32 * j⟩ (transposed j))

/-- The instructions of one batch, with its three loops branching back to the indices given. -/
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

/-- One batch's instructions, at their place in the routine. -/
def body (ls rs : Nat) : List Instr :=
  batchCode ls rs (firstHead ls rs) (secondHead ls rs) (thirdHead ls rs)

/--
The routine: eight digests per batch, for a count of batches.

On entry: rdi the output, rsi the left nodes, rdx the right nodes, rcx the batch count, r8 the constant table.
Consecutive left nodes sit ls bytes apart, and consecutive right nodes rs bytes apart, as for the sixteen-lane kernel.
-/
def program (ls rs : Nat) : Array Instr :=
  let tail := [.addImm left (8 * ls), .addImm right (8 * rs), .addImm out 256, .subImm count 1, .jnz loopHead]
  let finish := loopHead + (body ls rs).length + tail.length
  (([.subImm sp frame, .test count, .jz finish] ++ body ls rs ++ tail ++
    [.addImm sp frame, .vzeroupper, .zeroReg .rax, .ret]) : List Instr).toArray

end Ssz.Native.Kernel.Avx2
