import SszNative.Ir.Semantics

/-! Memory as the drivers change it, shared by their proofs. -/

namespace Ssz.Native.Driver

open Ssz.Native.Asm Ssz.Native.Ir

/-- Memory after a count of bytes is copied from one address to another. -/
def copied (mem : Memory) (dst src n : Nat) : Memory :=
  store mem dst n (fun k => mem (src + k))

end Ssz.Native.Driver
