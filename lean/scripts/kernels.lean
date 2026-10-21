import SszNative.Kernel.Assembly

/-! Writes the kernels the Lean programs describe: `lake env lean --run scripts/kernels.lean`. -/

def main : IO Unit := do
  IO.FS.writeFile "native/kernels_x86.S" Ssz.Native.assembly
