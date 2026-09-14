import Conformance.Reader

/-! What each conformance vector format asserts, one checker per format. -/

namespace Conformance

open Ssz Lean

/-- Compare two byte strings. -/
def sameBytes (what : String) (got expected : Bytes) : Except String Unit :=
  if got == expected then .ok ()
  else .error s!"{what} {toHex got}, expected {toHex expected}"

/-- Compare two numbers. -/
def sameNumber (what : String) (got expected : Nat) : Except String Unit :=
  if got == expected then .ok () else .error s!"{what} {got}, expected {expected}"

/-- Compare two lists of numbers, in order. -/
def sameNumbers (what : String) (got expected : List Nat) : Except String Unit :=
  if got == expected then .ok () else .error s!"{what} {got}, expected {expected}"

/-- Compare two lists of nodes, in order. -/
def sameNodes (what : String) (got expected : List Bytes) : Except String Unit :=
  if got == expected then .ok ()
  else .error s!"{what} {got.map toHex}, expected {expected.map toHex}"

/-- Compare a verifier's answer with the verdict the vector records. -/
def sameVerdict (got expected : Bool) : Except String Unit :=
  if got == expected then .ok ()
  else .error s!"verification answered {got}, expected {expected}"

/-- The refusal name a vector requires, or nothing where it names none. -/
def refusalName (vector : Json) : Option String :=
  (field? vector "rejectionReason").bind fun name => (text name).toOption

/--
Check that something was refused, under the name the vector gives.

A decoder that skips an offset or budget rule usually still fails, but with a different name.
-/
def refusedWith {α : Type} (expected what : String) :
    Except Err α → Except String Unit
  | .error fault =>
    if fault.reason == expected then .ok ()
    else .error s!"{what} refused with {fault.reason}, expected {expected}"
  | .ok _ => .error s!"{what} should have been refused with {expected}"

/-- The refusal name a vector requires, where it must name one. -/
def requiredName (vector : Json) : Except String String :=
  match refusalName vector with
  | some name => .ok name
  | none => .error "no rejectionReason in the vector"

/-- The declaration a vector carries. -/
def declaration (vector : Json) : Except String (Desc × Spelling) := do
  orFail "declaration" (readDescriptor (← field vector "typeDescriptor"))

/-- The value a vector carries, read through the JSON mapping. -/
def carried (shape : Desc) (spelling : Spelling) (vector : Json) : Except String Value := do
  orFail "value" (valueOf shape spelling (← field vector "value"))

/--
The index a vector's path names, kept as a refusal so a caller can require either outcome.

A path is refused either while its steps are read or while they are resolved, and a vector
draws no distinction between the two.
-/
def indexOfSteps (shape : Desc) (step : Json → Except String Step) (written : Json) :
    Except String (Except Err Nat) := do
  let steps ← (← entries written).mapM step
  return do getGeneralizedIndex shape (← readPath shape steps)

/-- The index the path in a named field names. -/
def indexOfPath (shape : Desc) (step : Json → Except String Step)
    (vector : Json) (name : String) : Except String (Except Err Nat) := do
  indexOfSteps shape step (← field vector name)

/--
The value a proof vector is about, checked the way an encoding vector checks one.

A proof of the wrong tree is worth nothing, so the bytes and the root come first.
-/
def checkSubject (shape : Desc) (value : Value) (vector : Json) (root : Bytes) :
    Except String Unit := do
  let serialized ← hexField vector "serialized"
  let encoded ← orFail "encoding" (serialize shape value)
  let rooted ← orFail "rooting" (hashTreeRoot shape value)
  sameBytes "encoded" encoded serialized
  sameBytes "rooted" rooted root

/--
An encoding vector: the bytes a value takes, its root, and what a decoder refuses.

Both the bytes and the root are compared against what the vector recorded.

Agreeing with your own encoder is not enough.
-/
def checkSsz (vector : Json) (valid : Bool) : Except String Unit := do
  let (shape, spelling) ← declaration vector
  let serialized ← hexField vector "serialized"
  if !valid then
    let expected ← requiredName vector
    return ← refusedWith expected "decoding" (deserialize shape serialized)
  let value ← carried shape spelling vector
  let root ← hexField vector "root"
  let encoded ← orFail "encoding" (serialize shape value)
  let rooted ← orFail "rooting" (hashTreeRoot shape value)
  let decoded ← orFail "decoding" (deserialize shape serialized)
  sameBytes "encoded" encoded serialized
  sameBytes "rooted" rooted root
  unless decoded == value do .error "decoded a different value than the one encoded"

/--
A declaration vector: a type the specification calls illegal, which must not be built.

The refusal can come from reading the declaration or from checking it.

A surplus declaration key is caught before any SSZ rule runs.
-/
def checkTypeRejection (vector : Json) : Except String Unit := do
  let expected ← requiredName vector
  let declared ← field vector "typeDescriptor"
  let built := do (← readDescriptor declared).1.wellFormed
  refusedWith expected "declaration" built

/--
A generalized-index vector: where in a type's tree one path lands.

There are no bytes and no value, only a declaration, a path, and the index it resolves to.

The leaf count and the tree width are redundant, and say which number came out wrong.
-/
def checkGindex (vector : Json) (valid : Bool) : Except String Unit := do
  let (shape, _) ← declaration vector
  if let some declared := field? vector "chunkCount" then
    let leaves ← orFail "chunk count" shape.chunkCount
    sameNumber "chunk count" leaves (← plain declared)
    sameNumber "tree width" (nextPow2 leaves) (← plainField vector "treeWidth")
  let resolved ← indexOfPath shape readIndexStep vector "path"
  if !valid then
    let expected ← requiredName vector
    return ← refusedWith expected "path" resolved
  let index ← orFail "index" resolved
  let depth ← orFail "depth" (gindexDepth index)
  let claimedIndex ← numberField vector "gindex"
  let claimedDepth ← plainField vector "depth"
  sameNumber "index" index claimedIndex
  sameNumber "depth" depth claimedDepth

/--
A JSON vector: the document a value is written as, and the input a parser must refuse.

Parsing a document and writing it back only shows the reader and writer agree.

The bytes are compared too, against a representation the mapping never touches.
-/
def checkJson (vector : Json) (valid : Bool) : Except String Unit := do
  let (shape, spelling) ← declaration vector
  let document ← field vector "document"
  if !valid then
    let expected ← requiredName vector
    return ← refusedWith expected "parsing" (valueOf shape spelling document)
  let serialized ← hexField vector "serialized"
  let value ← orFail "parsing" (valueOf shape spelling document)
  let written ← orFail "writing" (jsonOf shape spelling value)
  let encoded ← orFail "encoding" (serialize shape value)
  unless written.compress == document.compress do
    .error s!"wrote {written.compress}, expected {document.compress}"
  sameBytes "encoded" encoded serialized

/--
One branch, either refused under the name the vector gives or verified against the root.

A tampered vector carries a leaf and a branch this tree never produced, so only an
untampered one is held to the nodes the tree does produce.
-/
def checkBranch (shape : Desc) (value : Value) (vector : Json) (index : Nat)
    (root leaf : Bytes) (branch : List Bytes) (valid : Bool) : Except String Unit := do
  let verified := verifyMerkleProof leaf branch index root
  if let some name := refusalName vector then
    return ← refusedWith name "verification" verified
  if valid then
    let node ← orFail "node" (nodeRoot shape value index)
    let built ← orFail "branch" (buildProof shape value index)
    let order ← orFail "branch indices" (getBranchIndices index)
    let claimedOrder ← numberList vector "branchIndices"
    sameBytes "node" node leaf
    sameNodes "branch" built branch
    sameNumbers "branch indices" order claimedOrder
  let accepted ← orFail "verification" verified
  sameVerdict accepted valid

/-- A vector whose value holds no node at the claimed index, where the refusal is everything. -/
def checkAbsentNode (shape : Desc) (value : Value) (vector : Json) (index : Nat) :
    Except String Unit := do
  refusedWith (← requiredName vector) "node" (nodeRoot shape value index)

/--
A proof vector: one Merkle branch, checked as four separate claims.

A branch built for the wrong node still rebuilds a root.

Checking only the fourth claim would pass on a wrong index or a wrong tree.

The leaf is absent when the value's tree holds no node at that index, and the refusal name
is absent when the proof just fails to verify, as a tampered leaf does.
-/
def checkProof (vector : Json) (valid : Bool) : Except String Unit := do
  let (shape, spelling) ← declaration vector
  let value ← carried shape spelling vector
  let root ← hexField vector "root"
  let index ← numberField vector "index"
  checkSubject shape value vector root
  let resolved ← orFail "index" (← indexOfPath shape readProofStep vector "path")
  sameNumber "index" resolved index
  match field? vector "leaf" with
  | some claimed =>
    let leaf ← bytes claimed
    let branch ← hexList vector "branch"
    checkBranch shape value vector index root leaf branch valid
  | none => checkAbsentNode shape value vector index

/--
A multiproof vector: several claims proved at once, and the nodes a verifier cannot rebuild.

The helper indices descend on purpose.

A request for one index is then exactly that index's branch, node for node.
-/
def checkMultiproof (vector : Json) (valid : Bool) : Except String Unit := do
  let (shape, spelling) ← declaration vector
  let value ← carried shape spelling vector
  let root ← hexField vector "root"
  let indices ← numberList vector "indices"
  let leaves ← hexList vector "leaves"
  let supplied ← hexList vector "proof"
  let rooted ← orFail "rooting" (hashTreeRoot shape value)
  sameBytes "rooted" rooted root
  let resolved ← (← entries (← field vector "paths")).mapM fun path => do
    orFail "index" (← indexOfSteps shape readProofStep path)
  sameNumbers "paths resolved to" resolved indices
  let verified := verifyMerkleMultiproof leaves supplied indices root
  if let some name := refusalName vector then
    return ← refusedWith name "verification" verified
  if valid then
    let built ← orFail "multiproof" (buildMultiproof shape value indices)
    let order ← orFail "helper indices" (getHelperIndices indices)
    let claimedOrder ← numberList vector "helperIndices"
    sameNodes "multiproof" built supplied
    sameNumbers "helper indices" order claimedOrder
  let accepted ← orFail "verification" verified
  sameVerdict accepted valid

end Conformance
