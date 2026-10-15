import Asm.Merkle.Code

/-!
An executor for hash plans: the steps that root one plain type, held as data.

Each step is four 64-bit words, offsets counted from the scratch area's start:

```text
    word 0   0 for a chunk step, anything else for a hash step
    word 1   the slot the step writes
    word 2   a chunk's source, or a hash's left slot
    word 3   a chunk's length, or a hash's right slot
```

One routine runs every plan, so the code per type is only its plan.
-/

namespace Ssz.Asm.Exec

open Ssz.Asm.Sha256 (sp t0 t1 a0 a1 a2 savedSlots pairCode)
open Ssz.Asm.Merkle (zero t2 a3 a4 a5 slot)

/-- Bytes of stack frame: thirteen spilled registers, the output address, and the loop's four words. -/
def frameSize : Nat := 144

/-- Frame slot of the address the pair hash writes to. -/
def outSlot : Nat := 104

/-- Frame slot of the scratch area's address. -/
def scratchSlot : Nat := 112

/-- Frame slot of the plan's address. -/
def planSlot : Nat := 120

/-- Frame slot of the number of steps. -/
def stepsSlot : Nat := 128

/-- Frame slot of the index of the next step. -/
def indexSlot : Nat := 136

/-- The slots the entry code fills: the saved registers, the three arguments, and step zero. -/
def entrySlots : List (Reg × Nat) :=
  savedSlots ++ [(a0, scratchSlot), (a1, planSlot), (a2, stepsSlot), (zero, indexSlot)]

/-- Open the frame and spill the saved registers and the arguments. -/
def entryCode : List Instr :=
  .addi sp sp (BitVec.ofInt 12 (-(frameSize : Int))) :: spills sp entrySlots

/--
Stop after the last step, and otherwise decode the next one.

    a1  the source or left slot's address
    a2  the length, or the right slot's offset
    t2  the written slot's address, also saved for the pair hash
-/
def stepHeadCode (finish hash : Nat) : List Instr :=
  [.ld t0 sp (slot indexSlot), .ld t1 sp (slot stepsSlot), .bgeu t0 t1 finish,
    .ld a5 sp (slot planSlot), .slli t2 t0 5, .add a5 a5 t2, .ld a4 sp (slot scratchSlot),
    .ld t1 a5 (slot 0), .ld t2 a5 (slot 8), .add t2 a4 t2, .sd t2 sp (slot outSlot),
    .ld a1 a5 (slot 16), .add a1 a4 a1, .ld a2 a5 (slot 24), .bne t1 zero hash]

/-- A chunk step starts at byte zero of its slot. -/
def chunkStartCode : List Instr :=
  [.addi t0 zero (slot 0)]

/-- One byte of a chunk: copied while within the length, zero after it. -/
def chunkByteCode (next store chunkLoop : Nat) : List Instr :=
  [.addi t1 zero (slot 32), .bgeu t0 t1 next, .addi a3 zero (slot 0), .bgeu t0 a2 store,
    .add a3 a1 t0, .lbu a3 a3 (slot 0),
    .add t1 t2 t0, .sb a3 t1 (slot 0), .addi t0 t0 (slot 1), .j chunkLoop]

/-- A hash step: point a2 at the right slot and hash. -/
def hashCode : List Instr :=
  .add a2 a4 a2 :: pairCode outSlot

/-- Count the step, and go back for the next one. -/
def nextCode (stepHead : Nat) : List Instr :=
  [.ld t0 sp (slot indexSlot), .addi t0 t0 (slot 1), .sd t0 sp (slot indexSlot), .j stepHead]

/-- Restore the saved registers, close the frame, and return. -/
def finishCode : List Instr :=
  reloads sp savedSlots ++ [.addi sp sp (slot frameSize), .ret]

/-!
Instruction indices of the pieces, as literals the layout proofs check.
-/

/-- Instruction index of the step loop's head, after 18 entry instructions. -/
def stepHead : Nat := 18

/-- Instruction index of a chunk step's start. -/
def chunkStart : Nat := 33

/-- Instruction index of a chunk's byte loop. -/
def chunkLoop : Nat := 34

/-- Instruction index of a byte's store. -/
def store : Nat := 40

/-- Instruction index of a hash step. -/
def hashStart : Nat := 44

/-- Instruction index of the step count, after the 5092-instruction hash step. -/
def next : Nat := 5136

/-- Instruction index of the exit. -/
def finish : Nat := 5140

/--
The routine.

On entry:

    a0  the scratch area, holding the encoding at offset zero
    a1  the plan, four 64-bit words per step
    a2  the number of steps
-/
def program : Array Instr :=
  (entryCode ++ stepHeadCode finish hashStart ++ chunkStartCode ++ chunkByteCode next store chunkLoop ++
    hashCode ++ nextCode stepHead ++ finishCode).toArray

end Ssz.Asm.Exec
