import Asm.Emit
import Asm.Sha256.Code
import Asm.Merkle.Code
import Asm.Exec.Code
import Asm.Exec.State
import Asm.Root.Plan
import Ssz.Merkle.Tree

/-! Write the kernels as GNU assembler sources for RV64I. -/

open Ssz Ssz.Asm

/-- A hash plan as the executor reads it: four 64-bit words per step. -/
def planWords (d : Desc) : List Nat :=
  (Root.planFor d).steps.flatMap fun step => (List.range 4).map (Exec.stepWord step)

/-- The zero subtrees of heights 0 to 64, 32 bytes each, as the Merkleization routine reads them. -/
def zeroTable : Array UInt8 :=
  zeroRoots.foldl (fun bytes root => bytes ++ root) #[]

/-- One assembler file: a text section with the routine, then any read-only data. -/
def source (routine : String) (program : Array Instr) (data : String := "") : String :=
  "\t.text\n" ++ render routine program ++ (if data.isEmpty then "" else "\n\t.section .rodata\n" ++ data)

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.headD "riscv"
  IO.FS.createDirAll dir
  -- Each routine goes in its own file, so a build can take only what it links.
  IO.FS.writeFile (dir / "ssz_sha256_compress.s") (source "ssz_sha256_compress" Sha256.compressProgram)
  IO.FS.writeFile (dir / "ssz_merkleize.s")
    (source "ssz_merkleize" Merkle.program (renderData "ssz_zero_hashes" zeroTable))
  IO.FS.writeFile (dir / "ssz_hash_plan.s") (source "ssz_hash_plan" Exec.program)
  IO.println s!"wrote three routines to {dir}"
  return 0
