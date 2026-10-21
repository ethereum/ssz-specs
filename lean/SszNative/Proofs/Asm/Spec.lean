import SszNative.Asm.Semantics

/-! The terms the kernels' correctness theorems are stated in. -/

namespace Ssz.Native.Asm

/-- The 64 bytes of a pair: 32 from the left address, then 32 from the right one. -/
def pairMessage (mem : Nat → UInt8) (left right : Nat) : ByteArray :=
  ⟨Array.ofFn (n := 64) fun i => if i.val < 32 then mem (left + i.val) else mem (right + (i.val - 32))⟩

/-- Whether two byte ranges, each a start and a length, share no address. -/
def Apart (a : Nat × Nat) (b : Nat × Nat) : Prop :=
  a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1

/-- The registers a routine must hand back unchanged, under the System V calling convention. -/
def calleeSaved : List Gpr := [.rbx, .rsp, .rbp, .r12, .r13, .r14, .r15]

/-- The highest address a user-space access reaches, with room to spare below the top of the address space. -/
abbrev addressBound : Nat := 2 ^ 63

end Ssz.Native.Asm
