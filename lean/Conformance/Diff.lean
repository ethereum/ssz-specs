import Conformance.Cases

/-! Checking the Lean implementation against a corpus the Python generated on the fly. -/

namespace Conformance

open Ssz Lean

/--
Every node of a branch, and the claim it authenticates, agreeing with the corpus.

A claim with no index is one the specification refused, and this side has to refuse it too.
-/
def diffPath (shape : Desc) (value : Value) (root : Bytes) (claim : Json) :
    Except String Unit := do
  let resolved ← indexOfPath shape readProofStep claim "path"
  match field? claim "gindex" with
  | none =>
    match resolved with
    | .error _ => return ()
    | .ok index =>
      -- A type-level address may exist while the selected value has no readable node.
      match nodeRoot shape value index, buildProof shape value index with
      | .ok _, .ok _ => .error "walked a path the specification refuses"
      | _, _ => return ()
  | some written =>
    let index ← orFail "index" resolved
    let node ← orFail "node" (nodeRoot shape value index)
    let branch ← orFail "branch" (buildProof shape value index)
    sameNumber "index" index (← number written)
    sameBytes "node" node (← bytes (← field claim "node"))
    sameNodes "branch" branch (← hexList claim "proof")
    unless (← orFail "verification" (verifyMerkleProof node branch index root)) do
      .error s!"the branch for {index} does not rebuild the root"

/-- Several claims at once, and the nodes a verifier cannot rebuild. -/
def diffMultiproof (shape : Desc) (value : Value) (root : Bytes) (claim : Json) :
    Except String Unit := do
  let indices ← numberList claim "indices"
  let supplied ← orFail "multiproof" (buildMultiproof shape value indices)
  let leaves ← indices.mapM fun index => orFail "leaf" (nodeRoot shape value index)
  sameNodes "multiproof" supplied (← hexList claim "proof")
  unless (← orFail "verification" (verifyMerkleMultiproof leaves supplied indices root)) do
    .error "the multiproof does not rebuild the root"

/-- Check one generated case. -/
def diffCase (entry : Json) : Except String Unit := do
  let (shape, spelling) ← declaration entry
  let wellFormed ← match ← field entry "wellFormed" with
    | .bool value => .ok value
    | _ => .error "no well-formedness verdict in the case"
  if shape.wellFormed.toOption.isSome != wellFormed then
    .error s!"well-formedness disagrees, expected {wellFormed}"
  let value ← carried shape spelling entry
  let written ← orFail "writing" (jsonOf shape spelling value)
  let document ← field entry "value"
  if written.compress != document.compress then
    .error s!"wrote {written.compress}, expected {document.compress}"
  let root ← bytes (← field entry "root")
  sameBytes "encoded" (← orFail "encoding" (serialize shape value))
    (← bytes (← field entry "serialized"))
  sameBytes "rooted" (← orFail "rooting" (hashTreeRoot shape value)) root
  let decoded ← orFail "decoding" (deserialize shape (← bytes (← field entry "serialized")))
  if decoded != value then .error "decoded a different value than the one encoded"
  if let some written := field? entry "default" then
    let expected ← orFail "default" (valueOf shape spelling written)
    if (← orFail "default" shape.default) != expected then .error "the default disagrees"
  for claim in ← entries (← field entry "paths") do
    diffPath shape value root claim
  if let some claim := field? entry "multiproof" then
    diffMultiproof shape value root claim

/-- Whether two types merkleize alike, compared with the specification's answer. -/
def diffCompatible (entry : Json) : Except String Unit := do
  let (left, _) ← orFail "declaration" (readDescriptor (← field entry "left"))
  let (right, _) ← orFail "declaration" (readDescriptor (← field entry "right"))
  let expected ← match ← field entry "compatible" with
    | .bool value => .ok value
    | _ => .error "no compatibility verdict in the case"
  if isCompatible left right != expected then
    .error s!"compatibility disagrees, expected {expected}"

/-- Run a generated corpus. -/
def runDiff (file : System.FilePath) : IO (Nat × Array String) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile file))
  let mut passed := 0
  let mut failures : Array String := #[]
  for (label, key, check) in
      [("case", "cases", diffCase), ("compatibility", "compatible", diffCompatible)] do
    -- An absent section contributes no cases, so a batch may carry either kind alone.
    let drawn := (field? json key).bind (·.getArr?.toOption) |>.getD #[]
    for entry in drawn do
      match check entry with
      | .ok _ => passed := passed + 1
      | .error message =>
        let name := (field? entry "name").bind (·.getStr?.toOption) |>.getD "?"
        failures := failures.push s!"{label} {name}: {message}"
  return (passed, failures)

end Conformance
