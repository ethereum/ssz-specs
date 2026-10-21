import SszNative.Asm.Instr
import SszNative.Kernel.Constants

/-!
Pairs of nodes hashed one at a time with the SHA instructions.

This path suits short runs of pairs, where a sixteen-lane batch would mostly hash nothing.

Register 0 holds message words plus round constants, which the round instruction reads.
Registers 1 and 2 hold the state, as its words A, B, E, F and C, D, G, H.
Registers 3 to 6 hold the schedule, four words each.
Register 7 is a temporary.
Registers 8 and 9 keep the state between the two blocks.
Register 10 holds the byte-reversal mask.
-/

namespace Ssz.Native.Kernel.ShaNi

open Ssz.Native.Asm

/-- The output address, the first argument. -/
abbrev out : Gpr := .rdi

/-- The address of the first left node, the second argument. -/
abbrev left : Gpr := .rsi

/-- The address of the first right node, the third argument. -/
abbrev right : Gpr := .rdx

/-- The number of pairs, the fourth argument. -/
abbrev count : Gpr := .rcx

/-- The constant table's address, the fifth argument. -/
abbrev tbl : Gpr := .r8

/-- The message words plus constants the round instruction reads implicitly. -/
abbrev wk : Vreg := 0

/-- The state's A, B, E, F words. -/
abbrev abef : Vreg := 1

/-- The state's C, D, G, H words. -/
abbrev cdgh : Vreg := 2

/-- Schedule vector r, holding words 4r to 4r + 3 modulo sixteen. -/
def msg (r : Nat) : Vreg := ⟨3 + r % 4, by omega⟩

/-- A temporary. -/
abbrev tmp : Vreg := 7

/-- The state's A, B, E, F words after the first block. -/
abbrev midAbef : Vreg := 8

/-- The state's C, D, G, H words after the first block. -/
abbrev midCdgh : Vreg := 9

/-- The byte-reversal mask. -/
abbrev bswap : Vreg := 10

/-- A table entry. -/
def tableEntry (offset : Nat) : Mem := ⟨tbl, offset⟩

/-- Four rounds: two in each half of the word-plus-constant vector. -/
def fourRounds : List Instr :=
  [.sha256rnds2 cdgh abef, .pshufd wk wk 0x0E, .sha256rnds2 abef cdgh]

/-- Four first-block rounds, then the schedule vector they used is rewritten sixteen words ahead. -/
def firstRounds (r : Nat) : List Instr :=
  [.movdqa wk (msg r), .padddMem wk (tableEntry (kShaNi r))] ++ fourRounds ++
  (if r < 12 then
    [.sha256msg1 (msg r) (msg (r + 1)),
      -- Words 4r + 9 to 4r + 12 straddle two vectors.
      .movdqa tmp (msg (r + 3)), .palignr tmp (msg (r + 2)) 4,
      .paddd (msg r) tmp,
      .sha256msg2 (msg r) (msg (r + 3))]
  else [])

/-- Four padding-block rounds, from the precomputed words plus constants. -/
def paddingRounds (r : Nat) : List Instr :=
  [.movdqu wk (tableEntry (padShaNi r))] ++ fourRounds

/-- The body for one pair: its 32-byte parent from its 64 bytes. -/
def pairCode : List Instr :=
  -- The left node gives words 0 to 7, and the right node words 8 to 15.
  (List.range 4).flatMap (fun r =>
    [.movdqu (msg r) (if r < 2 then ⟨left, 16 * r⟩ else ⟨right, 16 * (r - 2)⟩), .pshufb (msg r) bswap]) ++
  [.movdqu abef (tableEntry ivAbef), .movdqu cdgh (tableEntry ivCdgh)] ++
  (List.range 16).flatMap firstRounds ++
  [.padddMem abef (tableEntry ivAbef), .padddMem cdgh (tableEntry ivCdgh), .movdqa midAbef abef, .movdqa midCdgh cdgh] ++
  (List.range 16).flatMap paddingRounds ++
  [.paddd abef midAbef, .paddd cdgh midCdgh,
    -- From ABEF and CDGH back to A..D and E..H, each big-endian.
    .pshufd abef abef 0x1B, .pshufd cdgh cdgh 0xB1,
    .movdqa tmp abef, .pblendw tmp cdgh 0xF0, .palignr cdgh abef 8,
    .pshufb tmp bswap, .pshufb cdgh bswap,
    .movdquStore ⟨out, 0⟩ tmp, .movdquStore ⟨out, 16⟩ cdgh]

/-- Instruction index of the pair loop's head. -/
def loopHead : Nat := 3

/--
The routine: one parent per pair, for a count of pairs.

On entry: rdi the output, rsi the left nodes, rdx the right nodes, rcx the pair count, r8 the constant table.
Consecutive left nodes sit ls bytes apart, and consecutive right nodes rs bytes apart.
-/
def program (ls rs : Nat) : Array Instr :=
  let tail := [.addImm left ls, .addImm right rs, .addImm out 32, .subImm count 1, .jnz loopHead]
  let finish := loopHead + pairCode.length + tail.length
  (([.test count, .jz finish, .movdqu bswap (tableEntry bswapShaNi)] ++ pairCode ++ tail ++ [.ret]) : List Instr).toArray

end Ssz.Native.Kernel.ShaNi
