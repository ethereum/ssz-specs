import SszNative.Ir.Compile
import SszNative.Ir.Wf

/-!
Linking compiled functions and routines written outside the language into one image.

The compiled functions come first, in order, and the outside routines follow them.
A check run before the image is trusted makes every name find its own routine, and keeps every routine addressable.
-/

namespace Ssz.Native.Ir

open Ssz.Native.Asm

/-- The image of a module: each function compiled under its name, then the outside routines. -/
def Module.link (fns : List (String × Fn)) (externs : Image) : Image :=
  (fns.map (fun p => (p.1, compileFn p.2)) ++ externs.toList).toArray

/--
Whether a linked image can be trusted.

No two routines share a name, every function fits the compiler's assumptions, every compiled function is short enough
for a return address to name its instructions, and the image is small enough for one to name its routines.
-/
def linkCheck (fns : List (String × Fn)) (externs : Image) : Bool :=
  decide ((Module.link fns externs).toList.map (·.1)).Nodup &&
    fns.all (fun p => p.2.wf && decide ((compileFn p.2).size < 2 ^ 32)) &&
    decide ((Module.link fns externs).size < 2 ^ 31)

end Ssz.Native.Ir
