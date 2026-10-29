import SszNative.Asm.Instr
import SszNative.Kernel.Constants

/-!
Four pairs of nodes hashed at once with SSE2, which every x86-64 processor has.

Lane j of every 128-bit register belongs to pair j.
Each pair is a 64-byte message, so its hash is two compressions, the second over the constant padding block.

The layout follows the eight-lane AVX2 kernel at half the width.
Sixteen registers hold one state, a running sum, and a few temporaries, but not a schedule.
So the schedule words live in a scratch area below the stack pointer, one 16-byte row per word.
Each step computes the word sixteen rounds ahead from four words in the scratch area, as the rounds read them.

SSE2 has no byte shuffle, so the words are reversed one at a time in a general register on their way in and out.
That also puts word t of pair j straight into lane j of row t, with no transpose.

SSE2 has no rotation either, so each rotation is two shifts, and the shifts of a mixing function are chained.
Its instructions overwrite their first operand, so a copy comes first wherever an input is still needed.
The rounds run eight at a time in a loop, since the working words return to their registers every eight rounds.

Registers 0 to 7 hold the working words, renamed rather than moved each round.
Registers 8 to 11 hold the running sum and two temporaries, and registers 12 to 15 the schedule step's temporaries.
-/

namespace Ssz.Native.Kernel.Baseline

open Ssz.Native.Asm

/-- The output address, the first argument. -/
abbrev out : Gpr := .rdi

/-- The address of the first left node, the second argument. -/
abbrev left : Gpr := .rsi

/-- The address of the first right node, the third argument. -/
abbrev right : Gpr := .rdx

/-- The number of batches of four pairs, the fourth argument. -/
abbrev count : Gpr := .rcx

/-- The constant table's address, the fifth argument. -/
abbrev tbl : Gpr := .r8

/-- The stack pointer, the base of the scratch area. -/
abbrev sp : Gpr := .rsp

/-- The pointer to the schedule words of the current eight rounds. -/
abbrev words : Gpr := .r10

/-- The pointer to the table's constants for the current eight rounds. -/
abbrev consts : Gpr := .r11

/-- The number of eight-round blocks left in the current loop, and the register each reversed word passes through. -/
abbrev blocks : Gpr := .r9

/-- Bytes of scratch: sixty-four schedule words and eight state words, 16 bytes each, and a gap. -/
def frame : Nat := 1280

/--
Byte offset of schedule word t.

Word t sits below word t - 1, so the schedule fills the scratch area from the caller's frame down.
-/
def wordSlot (t : Nat) : Nat := frame - 16 * (t + 1)

/-- Byte offset of working word j after the first block, at the bottom of the scratch area. -/
def midSlot (j : Nat) : Nat := 16 * j

/-- The schedule pointer's offset from the scratch area for eight-round block i. -/
def wordsBase (i : Nat) : Nat := 896 - 128 * i

/-- Byte offset of word 8i + m from block i's schedule pointer. -/
def wordRel (m : Nat) : Nat := 384 - 16 * (m + 1)

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

/-- A table row, whose first four lanes are those of a sixteen-lane row. -/
def tableEntry (offset : Nat) : Mem := ⟨tbl, offset⟩

/--
The exclusive or of three right rotations of a word, by counts k₁ < k₂ < k₃, into a register.

A right rotation by k is a right shift by k or'ed with a left shift by 32 - k, and the six parts never share a bit.
Each right shift continues the one before it, and each left shift the one before it, so all six fold into one sum.
-/
def mix (d e : Vreg) (k₁ k₂ k₃ : Nat) : List Instr :=
  [.movdqa d e, .psrld d k₁, .movdqa y e, .pslld y (32 - k₃), .movdqa z d, .psrld z (k₂ - k₁), .pxor d z,
    .psrld z (k₃ - k₂), .pxor d z, .pxor d y, .pslld y (k₃ - k₂), .pxor d y, .pslld y (k₂ - k₁), .pxor d y]

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
  [.movdqa x e, .pand x f, .movdqa y e, .pandn y g, .pxor x y, .paddd t1 x, .paddd d t1] ++
  mix x e 6 11 25 ++ [.paddd d x, .paddd t1 x] ++
  mix x a 2 13 22 ++
  -- Majority is c where a and b differ, and their common bit elsewhere.
  [.movdqa y a, .pxor y b, .pand y c, .movdqa z a, .pand z b, .pxor y z, .movdqa h t1, .paddd h x, .paddd h y]

/-- A first-block round: T1 starts as the schedule word plus H, then the round constant joins it. -/
def firstRound (k : Nat) : List Instr :=
  [.movdqu t1 ⟨words, wordRel k⟩, .paddd t1 (role k 7), .padddMem t1 ⟨consts, 64 * k⟩] ++ roundTail k

/-- A padding round: T1 starts as H plus the table's precomputed word and constant. -/
def paddingRound (k : Nat) : List Instr :=
  [.movdqa t1 (role k 7), .padddMem t1 ⟨consts, 64 * k⟩] ++ roundTail k

/-- Word 8i + k + 16, from the four words it depends on, in block i. -/
def scheduleStep (k : Nat) : List Instr :=
  [.movdqu sa ⟨words, wordRel (k + 14)⟩, .movdqa sb sa, .psrld sb 10, .movdqa sc sa, .psrld sc 17, .pxor sb sc,
    .psrld sc 2, .pxor sb sc, .pslld sa 13, .pxor sb sa, .pslld sa 2, .pxor sb sa,
    .movdqu sa ⟨words, wordRel (k + 1)⟩, .movdqa sc sa, .psrld sc 3, .movdqa sd sa, .psrld sd 7, .pxor sc sd,
    .psrld sd 11, .pxor sc sd, .pslld sa 14, .pxor sc sa, .pslld sa 11, .pxor sc sa,
    .paddd sb sc, .movdqu sa ⟨words, wordRel k⟩, .paddd sb sa, .movdqu sa ⟨words, wordRel (k + 9)⟩, .paddd sb sa,
    .movdquStore ⟨words, wordRel (k + 16)⟩ sb]

/-- Eight first-block rounds, with or without their schedule steps, then the pointer updates. -/
def firstBlock (scheduled : Bool) : List Instr :=
  (List.range 8).flatMap (fun k => firstRound k ++ (if scheduled then scheduleStep k else [])) ++
  [.subImm words 128, .addImm consts 512, .subImm blocks 1]

/-- Eight padding rounds, then the pointer update. -/
def paddingBlock : List Instr :=
  (List.range 8).flatMap paddingRound ++ [.addImm consts 512, .subImm blocks 1]

/-- Copy four bytes with their order reversed, through a general register. -/
def swapCopy (src dst : Mem) : List Instr :=
  [.load .b4 blocks src, .bswap blocks, .store .b4 dst blocks]

/--
Read word t of node j, for eight words of four nodes, into lane j of schedule row first + t.

Node j is at the base register plus the stride times j, and copy n moves word n mod 8 of node n / 8.
-/
def loadWords (base : Gpr) (stride first : Nat) : List Instr :=
  (List.range 32).flatMap fun n =>
    swapCopy ⟨base, stride * (n / 8) + 4 * (n % 8)⟩ ⟨sp, wordSlot (first + n % 8) + 4 * (n / 8)⟩

/-- The initial state in every lane. -/
def ivCode : List Instr :=
  (List.range 8).map fun j => .movdqu (home j) (tableEntry (ivAvx512 j))

/-- The first feed-forward, the state stored for the second. -/
def feedCode : List Instr :=
  (List.range 8).flatMap fun j =>
    [.padddMem (home j) (tableEntry (ivAvx512 j)), .movdquStore ⟨sp, midSlot j⟩ (home j)]

/-- The second feed-forward, from the stored state, stored back for the output. -/
def finishCode : List Instr :=
  (List.range 8).flatMap fun j =>
    [.movdqu sa ⟨sp, midSlot j⟩, .paddd (home j) sa, .movdquStore ⟨sp, midSlot j⟩ (home j)]

/-- The digests: word n mod 8 of pair n / 8, from lane n / 8 of its stored row, reversed into place. -/
def outCopies : List Instr :=
  (List.range 32).flatMap fun n =>
    swapCopy ⟨sp, midSlot (n % 8) + 4 * (n / 8)⟩ ⟨out, 32 * (n / 8) + 4 * (n % 8)⟩

/-- Everything before the first loop: the input words, the initial state, and the loop's pointers. -/
def setupCode (ls rs : Nat) : List Instr :=
  loadWords left ls 0 ++ loadWords right rs 8 ++
  ivCode ++ [.movReg words sp, .addImm words (wordsBase 0), .movReg consts tbl, .movImm blocks 6]

/-- Between the second loop and the third: the first feed-forward, and the third loop's count. -/
def middleCode : List Instr :=
  feedCode ++ [.movImm blocks 8]

/-- After the third loop: the second feed-forward, and the stores of four digests. -/
def outputCode : List Instr :=
  finishCode ++ outCopies

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
The routine: four digests per batch, for a count of batches.

On entry: rdi the output, rsi the left nodes, rdx the right nodes, rcx the batch count, r8 the constant table.
Consecutive left nodes sit ls bytes apart, and consecutive right nodes rs bytes apart, as for the other kernels.
-/
def program (ls rs : Nat) : Array Instr :=
  let tail := [.addImm left (4 * ls), .addImm right (4 * rs), .addImm out 128, .subImm count 1, .jnz loopHead]
  let finish := loopHead + (body ls rs).length + tail.length
  (([.subImm sp frame, .test count, .jz finish] ++ body ls rs ++ tail ++
    [.addImm sp frame, .zeroReg .rax, .ret]) : List Instr).toArray

end Ssz.Native.Kernel.Baseline
