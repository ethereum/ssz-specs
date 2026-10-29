import SszNative.Asm.Semantics

/-! The terms the kernels' correctness theorems are stated in. -/

namespace EthLib.Consensus.Ssz.Native.Asm

/-- The 64 bytes of a pair: 32 from the left address, then 32 from the right one. -/
def pairMessage (mem : Nat → UInt8) (left right : Nat) : ByteArray :=
  ⟨Array.ofFn (n := 64) fun i => if i.val < 32 then mem (left + i.val) else mem (right + (i.val - 32))⟩

/-- Whether two byte ranges, each a start and a length, share no address. -/
def Apart (a : Nat × Nat) (b : Nat × Nat) : Prop :=
  a.1 + a.2 ≤ b.1 ∨ b.1 + b.2 ≤ a.1

/-- The registers a routine must hand back unchanged, under the System V calling convention. -/
def calleeSaved : List Gpr := [.rbx, .rsp, .rbp, .r12, .r13, .r14, .r15]

/-- Writing the result register leaves every register the caller keeps alone. -/
theorem assign_saved {r : Gpr} (hr : r ∈ calleeSaved) (g : Gpr → UInt64) (v : UInt64) : assign g .rax v r = g r := by
  -- The result register is not one the caller keeps.
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h <;> subst h <;> rfl

end EthLib.Consensus.Ssz.Native.Asm
