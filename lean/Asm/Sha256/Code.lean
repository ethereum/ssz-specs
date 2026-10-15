import Asm.Machine
import Ssz.Hash.Sha256

/-!
The SHA-256 compression function as RV64I code.

The code is fully unrolled and keeps the whole working set in registers:

```text
    8 working words  a .. h       rotate through 8 registers, one step per round
    16 schedule words W[t-16..t-1] sit in a ring of 16 registers
    2 majority carries            hold a xor b for the next round
    2 temporaries
    = 28 registers, every one the calling convention lets a routine use
```

No message word, round constant, or working word ever goes through memory.
-/

namespace Ssz.Asm.Sha256

/-- The stack pointer. -/
abbrev sp : Reg := 2

/-- The first temporary, which also receives every mixing result. -/
abbrev t0 : Reg := 5

/-- The second temporary. -/
abbrev t1 : Reg := 6

/-- The first argument register, holding the state address on entry. -/
abbrev a0 : Reg := 10

/-- The second argument register, holding the block address on entry. -/
abbrev a1 : Reg := 11

/--
Homes of the eight working words at round zero.

The last is the state-address register, so the state can be read through it to the end.
-/
def stateRegs : Vector Reg 8 :=
  #v[12, 13, 14, 15, 16, 17, 28, 10]

/--
The ring holding the sixteen most recent schedule words.

Word t lives in slot t mod 16, so a new word overwrites the one sixteen positions back.
-/
def wordRegs : Vector Reg 16 :=
  #v[1, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 29, 30, 31]

/--
The two majority carries.

The first is the block-address register, which is free once the block is in registers.
-/
def carryRegs : Vector Reg 2 :=
  #v[11, 7]

/--
The register holding working word j at round i.

Every round shifts each word one position along, so the homes rotate instead of the data:

```text
    round 0:  a=S0 b=S1 c=S2 d=S3 e=S4 f=S5 g=S6 h=S7
    round 1:  a=S7 b=S0 c=S1 d=S2 e=S3 f=S4 g=S5 h=S6
```

The new a is written over the old h, and the new e over the old d.
-/
def wordHome (i j : Nat) : Reg :=
  stateRegs[(j + 8 - i % 8) % 8]'(Nat.mod_lt _ (by decide))

/-- The register holding schedule word t. -/
def ringSlot (t : Nat) : Reg :=
  wordRegs[t % 16]'(Nat.mod_lt _ (by decide))

/-- The register holding the majority carry at round i. -/
def carry (i : Nat) : Reg :=
  carryRegs[i % 2]'(Nat.mod_lt _ (by decide))

/-- The 20 upper bits of a constant, rounded so a sign-extended lower part adds back exactly. -/
def upper (k : BitVec 32) : BitVec 20 :=
  -- Adding 2^11 first compensates for the lower 12 bits being read as signed.
  ((k + 0x800) >>> 12).setWidth 20

/-- The 12 lower bits of a constant. -/
def lower (k : BitVec 32) : BitVec 12 :=
  k.setWidth 12

/--
Three rotations of the low word of a register, folded with exclusive or.

The source moves to the high half, then a chain of three right shifts builds every rotation at once.
-/
def rotations3Code (dst tmp src : Reg) (first second third : Nat) : List Instr :=
  [.slli dst src 32,
    .srli tmp dst first, .xor tmp tmp dst,
    .srli tmp tmp second, .xor tmp tmp dst,
    .srli tmp tmp third,
    -- Fold the bits that moved down onto the bits that wrapped around.
    .srli dst tmp 32, .xor dst dst tmp]

/-- Two rotations and one logical shift of the low word of a register, folded with exclusive or. -/
def rotations2Code (dst tmp src : Reg) (first second shift : Nat) : List Instr :=
  [.slli dst src 32,
    .srli tmp dst first, .xor tmp tmp dst,
    .srli tmp tmp second,
    .srli dst tmp 32, .xor dst dst tmp,
    -- The logical shift wraps nothing around, so a word shift supplies it directly.
    .srliw tmp src shift, .xor dst dst tmp]

/--
The schedule step that turns one ring slot from word t - 16 into word t.

    W[t] = W[t-16] + small0(W[t-15]) + W[t-7] + small1(W[t-2])

The arguments are the slots of words t - 16, t - 2, t - 15, and t - 7.
-/
def scheduleCodeWith (w w2 w15 w7 : Reg) : List Instr :=
  -- small1 uses rotations by 17 and 19 and a shift by 10.
  rotations2Code t0 t1 w2 2 17 10 ++ [.addw w w t0] ++
  -- small0 uses rotations by 7 and 18 and a shift by 3.
  rotations2Code t0 t1 w15 11 7 3 ++ [.addw w w t0, .addw w w w7]

/-- The schedule step producing word t, from round 16 on. -/
def scheduleCode (t : Nat) : List Instr :=
  -- Sixteen slots back is the slot itself, and 2, 15, and 7 back are 14, 1, and 9 ahead.
  scheduleCodeWith (ringSlot t) (ringSlot (t + 14)) (ringSlot (t + 1)) (ringSlot (t + 9))

/--
One compression round, in 31 instructions.

    T1 = h + large1(e) + choice(e, f, g) + K + W     accumulated in h
    d  = d + T1
    h  = T1 + large0(a) + majority(a, b, c)          the new a

On entry the carry q holds b xor c.
On exit the carry p holds a xor b, which is the next round's b xor c.
-/
def roundCodeWith (a b d e f g h w q p : Reg) (k : BitVec 32) : List Instr :=
  -- large1 uses rotations by 6, 11, and 25, so the chain shifts by 14, 5, then 6.
  rotations3Code t0 t1 e 14 5 6 ++
  [.addw h h t0,
    -- Choice is g xor (e and (f xor g)), which takes f where e is set and g elsewhere.
    .xor t0 f g, .and t0 t0 e, .xor t0 t0 g, .addw h h t0,
    -- The round constant is built from two immediates instead of loaded from memory.
    .lui t0 (upper k), .addiw t0 t0 (lower k), .addw h h t0,
    .addw h h w,
    .addw d d h] ++
  -- large0 uses rotations by 2, 13, and 22, so the chain shifts by 9, 11, then 2.
  rotations3Code t0 t1 a 9 11 2 ++
  [.addw h h t0,
    -- Majority is b xor ((a xor b) and (b xor c)).
    .xor p a b, .and q q p, .xor q q b, .addw h h q]

/-- Round i, with its registers picked by the rotation of the working words. -/
def roundCode (i : Nat) (k : BitVec 32) : List Instr :=
  roundCodeWith (wordHome i 0) (wordHome i 1) (wordHome i 3) (wordHome i 4) (wordHome i 5)
    (wordHome i 6) (wordHome i 7) (ringSlot i) (carry i) (carry (i + 1)) k

/-- Rounds below a given count, each preceded by its schedule step from round 16 on. -/
def roundsCode : Nat → List Instr
  | 0 => []
  | i + 1 =>
    roundsCode i ++ (if 16 ≤ i then scheduleCode i else []) ++
      roundCode i (Ssz.Sha256.roundConstants[i % 64]'(Nat.mod_lt _ (by decide))).toBitVec

/-- Bytes of stack frame: thirteen spilled registers and the state address, eight bytes each. -/
def frameSize : Nat := 112

/-- The return address and the callee-saved registers the kernel overwrites, with their slots. -/
def savedSlots : List (Reg × Nat) :=
  [(1, 0), (8, 8), (9, 16), (18, 24), (19, 32), (20, 40), (21, 48), (22, 56), (23, 64), (24, 72),
    (25, 80), (26, 88), (27, 96)]

/--
The slots of the frame: the saved registers, then the state address.

The state address is needed again for the feed-forward, after every register is spent.
-/
def frameSlots : List (Reg × Nat) :=
  savedSlots ++ [(a0, 104)]

/-- Open a frame and spill every callee-saved register the kernel will overwrite. -/
def prologueCode : List Instr :=
  .addi sp sp (BitVec.ofInt 12 (-(frameSize : Int))) :: spills sp frameSlots

/--
One big-endian message word, read a byte at a time into ring slot k from a base and offset.

Byte loads have no alignment requirement, so the block may start at any address.
-/
def loadWordFrom (k : Nat) (base : Reg) (start : Nat) : List Instr :=
  let w := ringSlot k
  let off := fun (j : Nat) => BitVec.ofNat 12 (start + j)
  -- The word shift sign-extends from bit 31, the representation every word keeps.
  [.lbu w base (off 0), .slliw w w 24,
    .lbu t0 base (off 1), .slli t0 t0 16, .or w w t0,
    .lbu t0 base (off 2), .slli t0 t0 8, .or w w t0,
    .lbu t0 base (off 3), .or w w t0]

/-- Message word k of a block whose address is in the second argument register. -/
def loadWordCode (k : Nat) : List Instr :=
  loadWordFrom k a1 (4 * k)

/-- All sixteen message words. -/
def loadBlockCode : List Instr :=
  (List.range 16).flatMap loadWordCode

/-- The eight state words, the last into the address register itself. -/
def loadStateCode : List Instr :=
  (List.range 8).map fun j =>
    .lw (stateRegs[j % 8]'(Nat.mod_lt _ (by decide))) a0 (BitVec.ofNat 12 (4 * j))

/-- Add one incoming state word to its working word and write the sum back. -/
def feedWordCode (j : Nat) : List Instr :=
  let s := stateRegs[j % 8]'(Nat.mod_lt _ (by decide))
  let off := BitVec.ofNat 12 (4 * j)
  [.lw t0 t1 off, .addw s s t0, .sw s t1 off]

/-- Add the incoming state to the working words and write the sum back. -/
def feedForwardCode : List Instr :=
  -- The state address comes back from the frame, since its register now holds a working word.
  .ld t1 sp 104 :: (List.range 8).flatMap feedWordCode

/-- Restore the spilled registers and close the frame. -/
def epilogueCode : List Instr :=
  reloads sp savedSlots ++ [.addi sp sp (BitVec.ofNat 12 frameSize)]

/--
The straight-line body of the routine.

On entry a0 holds the address of eight native-endian 32-bit state words.
On entry a1 holds the address of one 64-byte block.
-/
def compressBody : List Instr :=
  prologueCode ++ loadBlockCode ++ loadStateCode ++
    -- Round zero needs b xor c, which every later round inherits from the round before.
    [.xor (carry 0) (wordHome 0 1) (wordHome 0 2)] ++
    roundsCode 64 ++ feedForwardCode ++ epilogueCode

/-- The whole routine, ending in its return. -/
def compressProgram : Array Instr :=
  (compressBody ++ [Instr.ret]).toArray

end Ssz.Asm.Sha256
