import SszNative.Asm.Instr

/-!
Gathering fields out of fixed-width records into zero-padded slots.

A list of records holds each field a record's width apart.
Hashing a field across all records wants those fields one slot apart, padded to whole nodes.
-/

namespace Ssz.Native.Kernel

open Ssz.Native.Asm

/--
The routine: for each of a count of records, copy a field's bytes into a slot, then zero the rest of the slot.

On entry: rdi the output, rsi the first field, rdx the count, rcx the field width,
r8 the bytes from one field's end to the next field, and r9 the zero bytes after each copy.

The direction flag is clear on entry, as the calling convention guarantees, so both copies run forward.
-/
def gather : Array Instr :=
  #[.test .rdx, .jz 11,
    .movReg .r10 .rcx, .zeroReg .rax,
    -- One record: its field, then the slot's padding, then on to the next field.
    .movReg .rcx .r10, .repMovsb, .movReg .rcx .r9, .repStosb, .addReg .rsi .r8,
    .subImm .rdx 1, .jnz 4,
    .ret]

/-- Load one field of a width into vector register 0, zero-extended, for the widths with a single load. -/
def loadField (width : Nat) : List Instr :=
  match width with
  | 1 => [.loadByte .rax ⟨.rsi, 0⟩, .vfromGpr 0 .rax]
  | 2 => [.loadWord .rax ⟨.rsi, 0⟩, .vfromGpr 0 .rax]
  | 4 => [.vload4 0 ⟨.rsi, 0⟩]
  | 8 => [.vload8 0 ⟨.rsi, 0⟩]
  | 16 => [.vload16 0 ⟨.rsi, 0⟩]
  | _ => [.vloadHalf 0 ⟨.rsi, 0⟩]

/--
The routine for fields of one width into 32-byte slots: one zero-extending load and one store per record.

The width is one of 1, 2, 4, 8, 16, and 32.
The arguments are those of the general routine, which ignores the width and padding registers here.
-/
def gatherNode (width : Nat) : Array Instr :=
  let body := loadField width ++ [.vstoreHalf ⟨.rdi, 0⟩ 0, .addReg .rsi .r8, .addImm .rsi width, .addImm .rdi 32,
    .subImm .rdx 1, .jnz 2]
  (([.test .rdx, .jz (2 + body.length)] ++ body ++ [.vzeroupper, .ret]) : List Instr).toArray

/-- The routine for 48-byte fields into 64-byte slots, as a public key into two nodes. -/
def gatherKey : Array Instr :=
  let body := [.vloadHalf 0 ⟨.rsi, 0⟩, .vload16 1 ⟨.rsi, 32⟩,
    .vstoreHalf ⟨.rdi, 0⟩ 0, .vstoreHalf ⟨.rdi, 32⟩ 1,
    .addReg .rsi .r8, .addImm .rsi 48, .addImm .rdi 64, .subImm .rdx 1, .jnz 2]
  (([.test .rdx, .jz (2 + body.length)] ++ body ++ [.vzeroupper, .ret]) : List Instr).toArray

end Ssz.Native.Kernel
