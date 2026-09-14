import Conformance.Cases

/-! Running the conformance vectors the Python specification released. -/

namespace Conformance

open Ssz Lean

/-- Whether a vector must be accepted or refused. -/
def verdict (vector : Json) : Except String Bool :=
  match field? vector "valid" with
  | some (.bool value) => .ok value
  | _ => .error "no verdict in the vector"

/-- Check one vector, using the checker for the format that filled it. -/
def checkVector (format : String) (vector : Json) : Except String Unit := do
  let valid ← verdict vector
  match format with
  | "ssz_test" => checkSsz vector valid
  | "ssz_type_rejection" => checkTypeRejection vector
  | "ssz_gindex_test" => checkGindex vector valid
  | "ssz_json_test" => checkJson vector valid
  | "proof_test" => checkProof vector valid
  | "multiproof_test" => checkMultiproof vector valid
  -- The catalogue of formats is closed, so an unknown one is a failure rather than a skip.
  | _ => .error s!"unknown fixture format: {format}"

/-- Every vector file below a directory. -/
partial def vectorFiles (directory : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for entry in ← directory.readDir do
    if ← entry.path.isDir then
      out := out ++ (← vectorFiles entry.path)
    else if entry.path.toString.endsWith ".json" then
      out := out.push entry.path
  return out

/-- How a run of the vectors went. -/
structure Tally where
  /-- Vectors that passed. -/
  passed : Nat := 0
  /-- One line per vector that failed. -/
  failures : Array String := #[]

/-- The two files that describe the release rather than test anything. -/
def isCatalogue (file : System.FilePath) : Bool :=
  [some "index.json", some "manifest.json"].contains file.fileName

/-- Run every vector below a directory. -/
def run (root : System.FilePath) : IO Tally := do
  let files ← vectorFiles root
  let mut tally : Tally := {}
  -- Sorting paths makes a failure report reproducible across filesystem iteration orders.
  for file in files.qsort (fun a b => a.toString < b.toString) do
    if isCatalogue file then continue
    let source ← IO.FS.readFile file
    -- An unreadable vector records a failure without stopping the ones after it.
    let outcome : Except String Unit := do
      let vector ← Json.parse source
      let format ← text (← field (← field vector "_info") "fixtureFormat")
      checkVector format vector
    match outcome with
    | .ok _ => tally := { tally with passed := tally.passed + 1 }
    | .error message =>
      tally := { tally with failures := tally.failures.push s!"{file}: {message}" }
  return tally

end Conformance
