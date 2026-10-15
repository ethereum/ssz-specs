import Asm.Sha256.Pair

/-!
Merkleization of a run of 32-byte chunks, folding the tree upward one level at a time, in place.

```text
    level 0:  c0 c1 c2 c3 c4          five chunks
    level 1:  h(c0,c1) h(c2,c3) h(c4,z0)    the odd one pairs with the zero chunk
    level 2:  h(.,.) h(.,z1)                 and so on, with the zero subtree of each height
```

Each parent is written over the first half of the level it came from.
Pair i reads bytes 64i to 64i + 63 and writes bytes 32i to 32i + 31, which no later pair still needs.
-/

namespace Ssz.Asm.Merkle

open Ssz.Asm.Sha256 (sp t0 t1 a0 a1 a2 savedSlots pairCode)

/-- The zero register, read as the constant zero. -/
abbrev zero : Reg := 0

/-- The third temporary. -/
abbrev t2 : Reg := 7

/-- The fourth argument register, holding the zero-hash table's address on entry. -/
abbrev a3 : Reg := 13

/-- A scratch argument register. -/
abbrev a4 : Reg := 14

/-- A scratch argument register. -/
abbrev a5 : Reg := 15

/-- Bytes of stack frame: thirteen spilled registers, then the loop's six words and the output address. -/
def frameSize : Nat := 160

/-- Frame slot of the address the next parent is written to. -/
def outSlot : Nat := 104

/-- Frame slot of the chunk buffer's address. -/
def bufSlot : Nat := 112

/-- Frame slot of the number of chunks in the current level. -/
def countSlot : Nat := 120

/-- Frame slot of the index of the next pair in the current level. -/
def pairSlot : Nat := 128

/-- Frame slot of the current level's height above the leaves. -/
def heightSlot : Nat := 136

/-- Frame slot of the tree's depth. -/
def depthSlot : Nat := 144

/-- Frame slot of the zero-hash table's address. -/
def zerosSlot : Nat := 152

/-- A twelve-bit immediate, such as a frame slot's offset. -/
def slot (offset : Nat) : BitVec 12 :=
  BitVec.ofNat 12 offset

/-- The slots the entry code fills: the saved registers, the four arguments, and height zero. -/
def entrySlots : List (Reg × Nat) :=
  savedSlots ++ [(a0, bufSlot), (a1, countSlot), (a2, depthSlot), (a3, zerosSlot), (zero, heightSlot)]

/-- Open the frame, spill the saved registers and the arguments, and start at height zero. -/
def entryCode : List Instr :=
  .addi sp sp (BitVec.ofInt 12 (-(frameSize : Int))) :: spills sp entrySlots

/-- Stop once every level is folded or the level is empty, and otherwise start at pair zero. -/
def levelHeadCode (done : Nat) : List Instr :=
  [.ld t0 sp (slot heightSlot), .ld t1 sp (slot depthSlot), .bgeu t0 t1 done,
    .ld a4 sp (slot countSlot), .beq a4 zero done, .sd zero sp (slot pairSlot)]

/--
Leave the level after its last pair, and otherwise point a1 and a2 at the pair's two chunks.

The pair count is n / 2 rounded up, since an odd chunk still gets a parent.
-/
def pairHeadCode (levelEnd normal : Nat) : List Instr :=
  [.ld t0 sp (slot pairSlot), .ld a4 sp (slot countSlot), .addi t1 a4 (slot 1), .srli t1 t1 1,
    .bgeu t0 t1 levelEnd,
    .ld a5 sp (slot bufSlot), .slli t2 t0 6, .add a1 a5 t2, .addi a2 a1 (slot 32),
    -- Only the last pair of an odd level lacks a right chunk.
    .slli t2 t0 1, .addi t2 t2 (slot 1), .bne t2 a4 normal]

/-- The missing right chunk of an odd level is the zero subtree of this height. -/
def oddCode : List Instr :=
  [.ld t2 sp (slot heightSlot), .slli t2 t2 5, .ld a2 sp (slot zerosSlot), .add a2 a2 t2]

/-- Parent i goes to chunk i of the buffer. -/
def normalCode : List Instr :=
  [.slli t2 t0 5, .add t2 a5 t2, .sd t2 sp (slot outSlot)]

/-- Hash the pair, then count it. -/
def pairStepCode : List Instr :=
  pairCode outSlot ++ [.ld t0 sp (slot pairSlot), .addi t0 t0 (slot 1), .sd t0 sp (slot pairSlot)]

/-- Hash the pair, then move on to the next one. -/
def pairBodyCode (pairHead : Nat) : List Instr :=
  pairStepCode ++ [.j pairHead]

/-- The level above has n / 2 chunks rounded up, one height further from the leaves. -/
def levelEndCode (levelHead : Nat) : List Instr :=
  [.ld a4 sp (slot countSlot), .addi a4 a4 (slot 1), .srli a4 a4 1, .sd a4 sp (slot countSlot),
    .ld t0 sp (slot heightSlot), .addi t0 t0 (slot 1), .sd t0 sp (slot heightSlot), .j levelHead]

/-- A nonempty top level holds the root in its first chunk already. -/
def doneCode (finish : Nat) : List Instr :=
  [.ld a4 sp (slot countSlot), .bne a4 zero finish]

/-- Copy eight bytes from the address in t2 to the address in a5, at offset 8k. -/
def copyWord (k : Nat) : List Instr :=
  [.ld t0 t2 (slot (8 * k)), .sd t0 a5 (slot (8 * k))]

/-- With no chunks at all, the root is the zero subtree of the full depth, copied from the table. -/
def emptyCode : List Instr :=
  [.ld t1 sp (slot depthSlot), .slli t1 t1 5, .ld t2 sp (slot zerosSlot), .add t2 t2 t1,
    .ld a5 sp (slot bufSlot)] ++ (List.range 4).flatMap copyWord

/-- Restore the saved registers, close the frame, and return. -/
def finishCode : List Instr :=
  reloads sp savedSlots ++ [.addi sp sp (slot frameSize), .ret]

/-!
Instruction indices of the pieces, as literals.

The layout proofs check each one against the lengths of the pieces before it.
-/

/-- Instruction index of the level loop's head, after 19 entry instructions. -/
def levelHead : Nat := 19

/-- Instruction index of the pair loop's head. -/
def pairHead : Nat := 25

/-- Instruction index of the odd-level fix-up. -/
def oddStart : Nat := 37

/-- Instruction index where the parent's address is computed. -/
def normal : Nat := 41

/-- Instruction index of the pair hash. -/
def pairBody : Nat := 44

/-- Instruction index of the end of a level, after the 5091-instruction pair hash and its loop step. -/
def levelEnd : Nat := 5139

/-- Instruction index of the end of the level loop. -/
def done : Nat := 5147

/-- Instruction index of the empty-input case. -/
def emptyStart : Nat := 5149

/-- Instruction index of the exit. -/
def finish : Nat := 5162

/--
The routine.

On entry:

    a0  the chunk buffer, holding n chunks, with room for at least one
    a1  n, the number of chunks
    a2  the depth of the tree
    a3  the zero-hash table: the zero subtree of height k at offset 32k, for k up to the depth

On return the buffer's first chunk holds the root.
-/
def program : Array Instr :=
  (entryCode ++ levelHeadCode done ++ pairHeadCode levelEnd normal ++ oddCode ++ normalCode ++
    pairBodyCode pairHead ++ levelEndCode levelHead ++ doneCode finish ++ emptyCode ++
    finishCode).toArray

end Ssz.Asm.Merkle
