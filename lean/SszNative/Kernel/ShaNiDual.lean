import SszNative.Asm.Instr
import SszNative.Kernel.Constants

/-!
Two pairs of nodes hashed at once with the SHA instructions, their rounds interleaved.

One pair's rounds wait on the round instruction's latency.
The second pair's rounds fill that wait, so two pairs cost little more than one.

The pairs share register 0, which the round instruction reads, a temporary, and the byte-reversal mask.
The first pair keeps its state in registers 1 and 2, and its schedule in registers 3 to 6.
The second pair keeps its state in registers 8 and 9, and its schedule in registers 11 to 14.
After its first block, each pair keeps that block's state in the first two of its schedule registers.
-/

namespace Ssz.Native.Kernel.ShaNiDual

open Ssz.Native.Asm

/-- The registers one of the two pairs works in. -/
structure Lane where
  /-- The state's A, B, E, F words. -/
  abef : Vreg
  /-- The state's C, D, G, H words. -/
  cdgh : Vreg
  /-- Schedule vector r, holding words 4r to 4r + 3 modulo sixteen. -/
  msg : Nat → Vreg
  /-- The state's A, B, E, F words after the first block. -/
  midAbef : Vreg
  /-- The state's C, D, G, H words after the first block. -/
  midCdgh : Vreg

/-- The first pair's registers. -/
def first : Lane := ⟨1, 2, fun r => ⟨3 + r % 4, by omega⟩, 3, 4⟩

/-- The second pair's registers. -/
def second : Lane := ⟨8, 9, fun r => ⟨11 + r % 4, by omega⟩, 11, 12⟩

/-- The message words plus constants the round instruction reads implicitly. -/
abbrev wk : Vreg := 0

/-- A temporary, used by one pair at a time. -/
abbrev tmp : Vreg := 7

/-- The byte-reversal mask. -/
abbrev bswap : Vreg := 10

/-- The output address, the first argument. -/
abbrev out : Gpr := .rdi

/-- The address of the first left node, the second argument. -/
abbrev left : Gpr := .rsi

/-- The address of the first right node, the third argument. -/
abbrev right : Gpr := .rdx

/-- The number of twos of pairs, the fourth argument. -/
abbrev count : Gpr := .rcx

/-- The constant table's address, the fifth argument. -/
abbrev tbl : Gpr := .r8

/-- A table entry. -/
def tableEntry (offset : Nat) : Mem := ⟨tbl, offset⟩

/-- Four rounds of one pair: two in each half of the word-plus-constant vector. -/
def fourRounds (g : Lane) : List Instr :=
  [.sha256rnds2 g.cdgh g.abef, .pshufd wk wk 0x0E, .sha256rnds2 g.abef g.cdgh]

/-- Four first-block rounds of one pair, then the schedule vector they used rewritten sixteen words ahead. -/
def firstRounds (g : Lane) (r : Nat) : List Instr :=
  [.movdqa wk (g.msg r), .padddMem wk (tableEntry (kShaNi r))] ++ fourRounds g ++
  (if r < 12 then
    [.sha256msg1 (g.msg r) (g.msg (r + 1)),
      -- Words 4r + 9 to 4r + 12 straddle two vectors.
      .movdqa tmp (g.msg (r + 3)), .palignr tmp (g.msg (r + 2)) 4,
      .paddd (g.msg r) tmp,
      .sha256msg2 (g.msg r) (g.msg (r + 3))]
  else [])

/-- Four padding-block rounds of one pair, from the precomputed words plus constants. -/
def paddingRounds (g : Lane) (r : Nat) : List Instr :=
  [.movdqu wk (tableEntry (padShaNi r))] ++ fourRounds g

/-- One pair's message, from its left node and its right node, and the initial state. -/
def loadCode (g : Lane) (leftDisp rightDisp : Nat) : List Instr :=
  (List.range 4).flatMap (fun r =>
    [.movdqu (g.msg r) (if r < 2 then ⟨left, leftDisp + 16 * r⟩ else ⟨right, rightDisp + 16 * (r - 2)⟩),
      .pshufb (g.msg r) bswap]) ++
  [.movdqu g.abef (tableEntry ivAbef), .movdqu g.cdgh (tableEntry ivCdgh)]

/-- One pair's first feed-forward, kept for the second. -/
def middleCode (g : Lane) : List Instr :=
  [.padddMem g.abef (tableEntry ivAbef), .padddMem g.cdgh (tableEntry ivCdgh),
    .movdqa g.midAbef g.abef, .movdqa g.midCdgh g.cdgh]

/-- One pair's second feed-forward, its digest put in order, and stored at a displacement from the output. -/
def finishCode (g : Lane) (disp : Nat) : List Instr :=
  [.paddd g.abef g.midAbef, .paddd g.cdgh g.midCdgh,
    -- From ABEF and CDGH back to A..D and E..H, each big-endian.
    .pshufd g.abef g.abef 0x1B, .pshufd g.cdgh g.cdgh 0xB1,
    .movdqa tmp g.abef, .pblendw tmp g.cdgh 0xF0, .palignr g.cdgh g.abef 8,
    .pshufb tmp bswap, .pshufb g.cdgh bswap,
    .movdquStore ⟨out, disp⟩ tmp, .movdquStore ⟨out, disp + 16⟩ g.cdgh]

/-- The body for two pairs: pair 2i from the first registers, pair 2i + 1 from the second, rounds alternating. -/
def pairsCode (ls rs : Nat) : List Instr :=
  loadCode first 0 0 ++ loadCode second ls rs ++
  (List.range 16).flatMap (fun r => firstRounds first r ++ firstRounds second r) ++
  middleCode first ++ middleCode second ++
  (List.range 16).flatMap (fun r => paddingRounds first r ++ paddingRounds second r) ++
  finishCode first 0 ++ finishCode second 32

/-- Instruction index of the loop's head. -/
def loopHead : Nat := 3

/--
The routine: two parents per iteration, for a count of iterations.

On entry: rdi the output, rsi the left nodes, rdx the right nodes, rcx the count of twos, r8 the constant table.
Consecutive left nodes sit ls bytes apart, and consecutive right nodes rs bytes apart.
-/
def program (ls rs : Nat) : Array Instr :=
  let tail := [.addImm left (2 * ls), .addImm right (2 * rs), .addImm out 64, .subImm count 1, .jnz loopHead]
  let finish := loopHead + (pairsCode ls rs).length + tail.length
  (([.test count, .jz finish, .movdqu bswap (tableEntry bswapShaNi)] ++ pairsCode ls rs ++ tail ++ [.ret]) :
    List Instr).toArray

end Ssz.Native.Kernel.ShaNiDual
