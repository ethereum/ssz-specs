import EthLib.Consensus.Ssz
import Tests.Hash.Sha256
import Tests.Native
import Tests.NativeColumns

/-! Regression checks independent of the Python SSZ implementation. -/

open EthLib.Consensus.Ssz Lean

private def expect (label : String) (holds : Bool) : IO Unit := do
  -- A failed invariant stops the executable with a useful case name.
  unless holds do throw (IO.userError label)

private def refusedWith {α : Type} (label : String) (result : Except Err α) (reason : String) :
    IO Unit :=
  -- A refusal is checked for the name the reference tests give it, not merely for happening.
  expect label (match result with | .error fault => fault.reason == reason | .ok _ => false)

private def checkCanonical (shape : Desc) (bytes : Bytes) : IO Unit := do
  -- Every accepted encoding must be reproduced exactly, including offsets and padding.
  match deserialize shape bytes with
  | .error _ => pure ()
  | .ok value => expect "accepted bytes have a different encoding" ((serialize shape value).toOption == some bytes)

private def checkDocument (shape : Desc) (spelling : Spelling) (value : Value) : IO Unit := do
  -- The mapping is a round trip: what a value is written as must read back as that value.
  let .ok document := jsonOf shape spelling value | throw (IO.userError "a value has no document")
  match valueOf shape spelling document with
  | .error _ => throw (IO.userError s!"a written document was refused: {document.compress}")
  | .ok read => expect s!"document round trip for {document.compress}" (read == value)

private def checkBranches (shape : Desc) (value : Value) : IO Unit := do
  -- Authenticate all readable nodes in a finite prefix, including padding and mixed-in words.
  let .ok root := hashTreeRoot shape value | throw (IO.userError "fixture has no root")
  for index in [2:128] do
    match nodeRoot shape value index, buildProof shape value index with
    -- A readable node and its generated siblings must rebuild the same value root.
    | .ok leaf, .ok branch =>
      expect s!"branch at {index}" ((verifyMerkleProof leaf branch index root).toOption == some true)
    -- Proof construction must succeed whenever the corresponding node is readable.
    | .ok _, .error _ => throw (IO.userError s!"readable node has no branch at {index}")
    | .error _, _ => pure ()

-- A finite tree satisfies the branch premise without assigning children to its leaves.
example (left right : Bytes) :
    BranchConsistent (fun index => if index = 1 then combine left right
      else if index = 2 then left else right) 2 := by
  -- Only the single parent equation at level zero is required.
  intro level below
  have levelZero : level = 0 := by have : level < 1 := below; omega
  subst level
  rfl

-- The byte aliases meet the composite ceiling before checking their own length or limit.
-- These symbolic checks require no allocation of a four-gigabyte test input.
private theorem nativeByteVectorCeiling (b : ByteArray) (length : Nat)
    (large : b.size ≥ 2 ^ 32) :
    Native.validate (.byteVector length) b = .error (.offsetOverflow b.size) := by
  simp [Native.validate, Native.validateRange, Native.hasWidth, Native.validateFixed,
    Native.composite, bytesPerOffset, large, throw, throwThe, MonadExceptOf.throw,
    Bind.bind, Except.bind]

example (b : ByteArray) (limit : Nat) (large : b.size ≥ 2 ^ 32) :
    Native.validate (.byteList limit) b = .error (.offsetOverflow b.size) := by
  simp [Native.validate, Native.validateRange, Native.hasWidth, Native.validateVariable,
    Native.offsetBound, bytesPerOffset, large, throw, throwThe, MonadExceptOf.throw,
    Bind.bind, Except.bind]

example (b : ByteArray) (length : Nat) (large : b.size ≥ 2 ^ 32) :
    (Native.Schema.compile (.byteVector length)).validate b = .error (.offsetOverflow b.size) := by
  simpa [Native.Schema.compile, Native.fixedOf, Native.Schema.validate] using
    nativeByteVectorCeiling b length large

example (b : ByteArray) (large : b.size ≥ 2 ^ 32) :
    (Native.Schema.compile (.container ["bytes"] [.byteVector (2 ^ 32)])).validate b =
      .error (.offsetOverflow b.size) := by
  simp [Native.Schema.compile, Native.fixedOf, Native.Schema.validate, Native.plain, Native.plainAll,
    Native.composite, large]

-- A vector of booleans keeps one probe, however many elements it has.
example (count : Nat) : Native.runs (.vector .bool count) = [⟨0, 1, count, [.bit 0]⟩] := rfl

private def sameVerdict (left right : Except Err Bool) : Bool :=
  match left, right with
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

private def checkNativeIntegration : IO Unit := do
  let z : ByteArray := ⟨zeroChunk⟩
  let empty := ByteArray.empty
  let root := Native.combine z z
  -- Wrong-width expected roots answer false; malformed requests take precedence over widths.
  expect "native short root, single proof"
    ((Native.verifyMerkleProof z [z] 2 empty).toOption == some false)
  expect "native short root, multiproof"
    ((Native.verifyMerkleMultiproof [z] [z] [2] empty).toOption == some false)
  for (leaf, proof, index, expected) in
      [(z, [z], 2, root), (z, [z], 2, empty), (empty, [], 0, empty),
       (empty, [], 1, empty), (empty, [z, z], 2, empty), (empty, [z], 2, empty)] do
    expect s!"native single-proof outcome at {index}"
      (sameVerdict (Native.verifyMerkleProof leaf proof index expected)
        (verifyMerkleProof leaf.data (proof.map (·.data)) index expected.data))
  for (leaves, proof, indices, expected) in
      [([z], [z], [2], root), ([z], [z], [2], empty), ([], [], [], empty),
       ([empty], [], [], empty), ([empty, empty], [], [2, 2], empty),
       ([empty, empty], [], [2, 4], empty), ([empty], [z, z], [2], empty),
       ([empty], [z], [2], empty)] do
    expect "native multiproof outcome, including combined faults"
      (sameVerdict (Native.verifyMerkleMultiproof leaves proof indices expected)
        (verifyMerkleMultiproof (leaves.map (·.data)) (proof.map (·.data)) indices expected.data))
  -- Selector validation remains decoder-equivalent even for an illegal declaration.
  for selector in [0, 128] do
    let d := Desc.compatibleUnion [selector] [.bool]
    let b : ByteArray := ⟨#[UInt8.ofNat selector, 1]⟩
    refusedWith "native reserved selector" (Native.validate d b) "UNION_SELECTOR_RANGE"
  -- A forty-byte integer is not an SSZ integer, so the checked factory refuses its struct.
  -- Its bytes would spill past the field's one-node leaf.
  refusedWith "checked factory, uint 40 field"
    (Native.Checked.compile (.container ["a", "b"] [.uint 40, .uint 1])) "UINT_WIDTH"
  -- The same legality is checked at every depth, here a field of a list's element.
  refusedWith "checked factory, nested uint 40"
    (Native.Checked.compile (.list (.container ["a"] [.uint 40]) 4)) "UINT_WIDTH"
  -- A four-mebibyte vector of booleans, alone and as a struct's field.
  -- A bad byte is refused first, last, and at the start of a later parallel run.
  let count := 4194304
  let ones : ByteArray := ⟨Array.replicate count 1⟩
  let flags := Desc.vector .bool count
  let holder := Desc.container ["flags"] [flags]
  expect "long boolean vector" ((Native.validate flags ones).isOk)
  expect "long boolean vector, compiled" (((Native.Schema.compile holder).validate ones).isOk)
  for position in [0, 16384, count - 1] do
    let bad := ones.set! position 2
    expect "long boolean vector, bad byte"
      (match Native.validate flags bad with | .error e => e == .notABit 2 | .ok _ => false)
    expect "long boolean vector, bad byte, compiled"
      (match (Native.Schema.compile holder).validate bad with | .error e => e == .notABit 2 | .ok _ => false)
  -- A struct breaking a fixed field and its offsets is refused for the fixed field.
  -- The fixed part is read before the offsets, as the reference reads it.
  --
  --     02          the boolean, not a bit
  --     00000000    the first offset, pointing into the fixed part
  --
  -- The second struct's boolean follows its offset.
  --
  --     05000000    the first offset, five bytes past the start
  --     02          the boolean, not a bit
  --     0909        the body, longer than its limit of one
  let faults : List (Desc × ByteArray) :=
    [(.container ["a", "b"] [.bool, .byteList 1], ⟨#[2, 0, 0, 0, 0]⟩),
     (.container ["data", "flag"] [.byteList 1, .bool], ⟨#[5, 0, 0, 0, 2, 9, 9]⟩)]
  for (d, b) in faults do
    refusedWith "struct faults, reference" (deserialize d b.data) "NOT_A_BIT"
    refusedWith "struct faults, native" (Native.validate d b) "NOT_A_BIT"
    refusedWith "struct faults, compiled" ((Native.Schema.compile d).validate b) "NOT_A_BIT"
    let .ok checked := Native.Checked.compile d | throw (IO.userError "legal declaration refused")
    refusedWith "struct faults, checked" (checked.validate b) "NOT_A_BIT"
  -- Byte-vector roots use raw packed bytes after decoding; their layout is independent of encoding limits.
  let bytes : Bytes := (Array.range 33).map UInt8.ofNat
  let examples : List (Desc × Value) :=
    [(.byteVector 33, .bytes bytes),
     (.container ["bytes", "flag"] [.byteVector 33, .bool], .seq [.bytes bytes, .bool true]),
     (.vector (.byteVector 33) 2, .seq [.bytes bytes, .bytes bytes]),
     (.container ["bytes", "flag"] [.byteList 33, .bool], .seq [.bytes bytes, .bool false]),
     (.progressiveList .bool (some 1), .seq [.bool true]),
     (.progressiveBitList (some 1), .bits #[true]),
     (.compatibleUnion [1, 127] [.bool, .bool], .union 127 (.bool true))]
  for (d, value) in examples do
    let .ok encoded := serialize d value | throw (IO.userError "native integration fixture refused")
    let .ok reference := hashTreeRoot d value | throw (IO.userError "native integration fixture has no root")
    let b : ByteArray := ⟨encoded⟩
    expect "native validation after reference integration" ((Native.validate d b).isOk)
    expect "native root after reference integration"
      (((Native.hashTreeRoot d b).map (·.data)).toOption == some reference)
    let .ok checked := Native.Checked.compile d | throw (IO.userError "legal declaration refused")
    expect "checked schema after reference integration"
      (((checked.hashTreeRoot b).map (·.data)).toOption == some reference)
    for index in [2:8] do
      expect "native node after reference integration"
        (match Native.nodeRoot d b index, nodeRoot d value index with
        | .ok native, .ok spec => native.data == spec
        | .error native, .error spec => native == spec
        | _, _ => false)

def main : IO Unit := do
  -- Published vectors validate SHA-256 before it is used in the SSZ regressions.
  Tests.Sha256.run
  -- The native kernels agree with their references and with the machine model.
  Tests.Native.run
  checkNativeIntegration
  Tests.NativeColumns.run

  -- A splice cannot turn a nonexistent outer node into a valid index.
  expect "zero outer index" ((gindexConcat 0 3).isOk == false)
  -- SSZ names six integer widths, and a declaration of any other is refused as a width.
  expect "uint of no width" ((Desc.uint 0).wellFormed.isOk == false)
  expect "uint splitting a chunk" ((Desc.uint 3).wellFormed.isOk == false)
  expect "uint past a chunk" ((Desc.uint 64).wellFormed.isOk == false)
  -- A fixed shape of no width encodes to nothing, so no count of them could be recovered.
  expect "zero-width bit vector" ((Desc.bitVector 0).wellFormed.isOk == false)
  expect "zero-width byte array" ((Desc.byteVector 0).wellFormed.isOk == false)
  expect "zero-length vector" ((Desc.vector .bool 0).wellFormed.isOk == false)
  -- The refusal follows the shape wherever it is nested, since the width is what is missing.
  expect "zero-width element" ((Desc.list (.byteVector 0) 4).wellFormed.isOk == false)
  expect "zero-width field" ((Desc.container ["a"] [.bitVector 0]).wellFormed.isOk == false)
  -- A struct of no fields spans no bytes, which the specification lists as illegal too.
  expect "zero-field struct" ((Desc.container [] []).wellFormed.isOk == false)
  -- A capacity of zero bounds what a shape may hold, and bounds nothing about its width.
  expect "zero-capacity bit list" ((Desc.bitList 0).wellFormed.isOk == true)
  expect "zero-capacity list" ((Desc.list .bool 0).wellFormed.isOk == true)
  -- Field names and selectors are declaration keys, so duplicates are invalid.
  expect "duplicate field names"
    ((Desc.container ["flag", "flag"] [.bool, .bool]).wellFormed.isOk == false)
  -- The same uniqueness requirement applies when fields occupy progressive positions.
  expect "duplicate progressive field names"
    ((Desc.progressiveContainer [true, true] ["flag", "flag"] [.bool, .bool]).wellFormed.isOk == false)
  -- Repeated tags must report the duplicated selector rather than select an arbitrary option.
  expect "duplicate selector diagnostic"
    (match (Desc.compatibleUnion [7, 7] [.bool, .bool]).wellFormed with
    | .error (.unionSelectorRepeated 7) => true
    | _ => false)
  -- One active field permits one value, even when unused positions precede it.
  let shape := Desc.progressiveContainer [false, true] ["flag"] [.bool]
  -- Fixture state: one active position accepts one field value, while two values must fail.
  let extra := Value.seq [.bool false, .bool true]
  expect "extra progressive field" ((hashTreeRoot shape extra).isOk == false)
  -- Removing the sole value must also fail, even though the layout contains an inactive gap.
  expect "missing progressive field" ((hashTreeRoot shape (.seq [])).isOk == false)
  -- The matching one-value payload establishes the positive case for the same declaration.
  expect "valid progressive field" ((hashTreeRoot shape (.seq [.bool true])).isOk)
  -- An empty tree deeper than the cache still has a hashed zero root.
  expect "depth 65 zero root" ((merkleizeBounded #[] (some (2 ^ 65))).toOption == some #[
    0x30, 0x3c, 0xe3, 0x88, 0x09, 0xba, 0x7a, 0x77, 0xb6, 0x60, 0xad, 0x0b, 0x07, 0x4a, 0xf9, 0xc6,
    0xbc, 0xd5, 0xc0, 0x2b, 0xbf, 0xf2, 0xf3, 0xb0, 0x24, 0x86, 0x33, 0xb0, 0xb8, 0x76, 0xe4, 0x49])
  -- Invariant: every node a tree or a branch takes in is exactly 32 bytes wide.
  -- Fixture state: a one-leaf tree hashes nothing, so its lone leaf would be the root itself.
  refusedWith "empty lone leaf" (merkleizeBounded #[#[]] none) "COUNT"
  refusedWith "31-byte lone leaf" (merkleizeBounded #[Array.replicate 31 0] (some 1)) "COUNT"
  refusedWith "31-byte progressive leaf" (merkleizeProgressive [Array.replicate 31 0]) "COUNT"
  -- Mutation: move one byte from the sibling onto the leaf.
  --
  --     leaf 31 bytes ++ sibling 33 bytes = 64 bytes = leaf 32 bytes ++ sibling 32 bytes
  --
  -- Both pairs hash the same message, so the split itself is what gets refused.
  refusedWith "31 and 33 byte branch"
    (calculateMerkleRoot (Array.replicate 31 0) [Array.replicate 33 0] 2) "COUNT"
  refusedWith "31 and 33 byte multiproof"
    (calculateMultiMerkleRoot [Array.replicate 31 0] [Array.replicate 33 0] [2]) "COUNT"
  -- The honest 32 and 32 split rebuilds its parent.
  expect "32 and 32 byte branch"
    ((calculateMerkleRoot zeroChunk [zeroChunk] 2).toOption == some (combine zeroChunk zeroChunk))
  -- SHA-256 padding changes block count at 56 bytes and crosses a block at 64.
  -- An empty message still hashes one padding block with an explicit zero bit length.
  expect "SHA-256 0 bytes" ((EthLib.Cryptography.Hash.Sha256.hash ⟨(Array.range 0).map UInt8.ofNat⟩).data == #[
    0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
    0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55])
  -- The standard three-byte message checks a familiar digest independently of SSZ.
  expect "SHA-256 3 bytes" ((EthLib.Cryptography.Hash.Sha256.hash ⟨#[0x61, 0x62, 0x63]⟩).data == #[
    0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea, 0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
    0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c, 0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad])
  -- Fifty-five payload bytes leave exactly room for the delimiter and eight-byte length.
  expect "SHA-256 55 bytes" ((EthLib.Cryptography.Hash.Sha256.hash ⟨(Array.range 55).map UInt8.ofNat⟩).data == #[
    0x46, 0x3e, 0xb2, 0x8e, 0x72, 0xf8, 0x2e, 0x0a, 0x96, 0xc0, 0xa4, 0xcc, 0x53, 0x69, 0x0c, 0x57,
    0x12, 0x81, 0x13, 0x1f, 0x67, 0x2a, 0xa2, 0x29, 0xe0, 0xd4, 0x5a, 0xe5, 0x9b, 0x59, 0x8b, 0x59])
  -- One additional payload byte forces the length field into a second block.
  expect "SHA-256 56 bytes" ((EthLib.Cryptography.Hash.Sha256.hash ⟨(Array.range 56).map UInt8.ofNat⟩).data == #[
    0xda, 0x2a, 0xe4, 0xd6, 0xb3, 0x67, 0x48, 0xf2, 0xa3, 0x18, 0xf2, 0x3e, 0x7a, 0xb1, 0xdf, 0xdf,
    0x45, 0xac, 0xdc, 0x9d, 0x04, 0x9b, 0xd8, 0x0e, 0x59, 0xde, 0x82, 0xa6, 0x08, 0x95, 0xf5, 0x62])
  -- At sixty-three bytes, the delimiter fills the first block’s last position.
  expect "SHA-256 63 bytes" ((EthLib.Cryptography.Hash.Sha256.hash ⟨(Array.range 63).map UInt8.ofNat⟩).data == #[
    0x29, 0xaf, 0x26, 0x86, 0xfd, 0x53, 0x37, 0x4a, 0x36, 0xb0, 0x84, 0x66, 0x94, 0xcc, 0x34, 0x21,
    0x77, 0xe4, 0x28, 0xd1, 0x64, 0x75, 0x15, 0xf0, 0x78, 0x78, 0x4d, 0x69, 0xcd, 0xb9, 0xe4, 0x88])
  -- A complete payload block requires a separate padding block.
  expect "SHA-256 64 bytes" ((EthLib.Cryptography.Hash.Sha256.hash ⟨(Array.range 64).map UInt8.ofNat⟩).data == #[
    0xfd, 0xea, 0xb9, 0xac, 0xf3, 0x71, 0x03, 0x62, 0xbd, 0x26, 0x58, 0xcd, 0xc9, 0xa2, 0x9e, 0x8f,
    0x9c, 0x75, 0x7f, 0xcf, 0x98, 0x11, 0x60, 0x3a, 0x8c, 0x44, 0x7c, 0xd1, 0xd9, 0x15, 0x11, 0x08])
  -- The next payload byte belongs to the second block before its padding is appended.
  expect "SHA-256 65 bytes" ((EthLib.Cryptography.Hash.Sha256.hash ⟨(Array.range 65).map UInt8.ofNat⟩).data == #[
    0x4b, 0xfd, 0x2c, 0x8b, 0x6f, 0x1e, 0xec, 0x7a, 0x2a, 0xfe, 0xb4, 0x8b, 0x93, 0x4e, 0xe4, 0xb2,
    0x69, 0x41, 0x82, 0x02, 0x7e, 0x6d, 0x0f, 0xc0, 0x75, 0x07, 0x4f, 0x2f, 0xab, 0xb3, 0x17, 0x81])
  -- The same padding threshold repeats after one complete block of payload.
  expect "SHA-256 119 bytes" ((EthLib.Cryptography.Hash.Sha256.hash ⟨(Array.range 119).map UInt8.ofNat⟩).data == #[
    0xda, 0x18, 0x79, 0x7e, 0xd7, 0xc3, 0xa7, 0x77, 0xf0, 0x84, 0x7f, 0x42, 0x97, 0x24, 0xa2, 0xd8,
    0xcd, 0x51, 0x38, 0xe6, 0xed, 0x28, 0x95, 0xc3, 0xfa, 0x1a, 0x6d, 0x39, 0xd1, 0x8f, 0x7e, 0xc6])
  -- Crossing that threshold forces a third compression block.
  expect "SHA-256 120 bytes" ((EthLib.Cryptography.Hash.Sha256.hash ⟨(Array.range 120).map UInt8.ofNat⟩).data == #[
    0xf5, 0x2b, 0x23, 0xdb, 0x1f, 0xbb, 0x6d, 0xed, 0x89, 0xef, 0x42, 0xa2, 0x3c, 0xe0, 0xc8, 0x92,
    0x2c, 0x45, 0xf2, 0x5c, 0x50, 0xb5, 0x68, 0xa9, 0x3b, 0xf1, 0xc0, 0x75, 0x42, 0x0b, 0xbb, 0x7c])
  -- Shifting one byte across a child boundary preserves concatenation but violates SSZ.
  -- Mutation: two 32-byte children become 31 and 33, concatenating to the same 64 bytes.
  let short := Array.replicate 31 (0 : UInt8)
  let long := Array.replicate 33 (0 : UInt8)
  let root := combine zeroChunk zeroChunk
  expect "short proof leaf" ((verifyMerkleProof short [long] 2 root).isOk == false)
  -- The shared-proof verifier must reject the same ambiguous child boundary.
  expect "short multiproof leaf"
    ((verifyMerkleMultiproof [short] [long] [2] root).isOk == false)
  -- Both tree shapes and nested values must authenticate their readable nodes.
  checkBranches (.list .uint256 5) (.seq [.uint 1, .uint 2, .uint 3])
  -- An unbounded progressive spine must authenticate the same readable-node prefix.
  checkBranches (.progressiveList .uint256 none) (.seq [.uint 1, .uint 2, .uint 3])
  -- Gaps in a progressive container remain part of the authenticated tree layout.
  checkBranches shape (.seq [.bool true])
  -- A selected nested option must remain authenticated below its selector word.
  checkBranches (.compatibleUnion [1] [shape]) (.union 1 (.seq [.bool true]))
  -- Exhaust all one- and two-byte inputs for small packed and delimited types.
  let shapes : List Desc := [.bool, .uint8, .uint16, .byteVector 2, .byteList 2,
    .bitVector 9, .bitList 9, .progressiveBitList none, .list .bool 2,
    .vector .bool 2, .progressiveList .bool none, .compatibleUnion [1] [.bool]]
  for shape in shapes do
    -- The empty byte string covers both a refusal and an empty-value encoding.
    checkCanonical shape #[]
    -- Every possible first byte includes valid tags, invalid tags, and delimiter positions.
    for first in [0:256] do
      checkCanonical shape #[UInt8.ofNat first]
      -- Every possible second byte also tests partial final bytes and trailing-data rejection.
      for second in [0:256] do
        checkCanonical shape #[UInt8.ofNat first, UInt8.ofNat second]
  -- The byte alias is hex where a one-byte integer of the very same type is decimal digits.
  expect "byte alias document"
    ((jsonOf (.uint 1) .byte (.uint 255)).toOption.map Json.compress == some "\"0xff\"")
  expect "one-byte integer document"
    ((jsonOf (.uint 1) .opaque (.uint 255)).toOption.map Json.compress == some "\"255\"")
  -- A bitfield is the hex of its own encoding, so its delimiter bit is part of the document.
  expect "bit list document"
    ((jsonOf (.progressiveBitList none) .opaque (.bits #[true, false, true])).toOption.map Json.compress
      == some "\"0x0d\"")
  -- An integer wider than a double is written as digits in a string, and survives being read.
  checkDocument .uint64 .opaque (.uint (2 ^ 64 - 1))
  checkDocument .uint256 .opaque (.uint (2 ^ 256 - 1))
  -- Every shape of document the mapping writes has to read back as the value it came from.
  checkDocument (.byteList 4) .opaque (.bytes #[1, 2, 3])
  checkDocument (.bitList 9) .opaque (.bits #[true, false, true, true])
  checkDocument (.vector (.uint 1) 2) (.plain [.byte]) (.seq [.uint 1, .uint 2])
  checkDocument (.container ["a", "b"] [.uint16, .bool]) .opaque (.seq [.uint 7, .bool true])
  checkDocument (.compatibleUnion [1, 2] [.uint16, .uint16]) .opaque (.union 2 (.uint 9))
  -- The mapping writes a bitfield and a byte sequence as one hex string, never as an array.
  expect "bit list written as an array"
    ((valueOf (.bitList 20) .opaque (.arr #[.bool true])).isOk == false)
  expect "byte list written as an array"
    ((valueOf (.byteList 8) .opaque (.arr #[.str "0x01"])).isOk == false)
  -- An empty object asks for a default, and no option of a union stands above the others.
  expect "union written as an empty object"
    ((valueOf (.compatibleUnion [1] [.uint16]) .opaque (Json.mkObj [])).isOk == false)
  -- A hex string without its marker renders nothing the mapping writes.
  expect "unmarked hex" ((valueOf (.byteVector 1) .opaque (.str "ff")).isOk == false)
  -- An object is held to naming every field its struct declares, and no other.
  let pair := Desc.container ["a", "b"] [.uint16, .uint16]
  expect "object leaving out a field"
    ((valueOf pair .opaque (Json.mkObj [("a", .str "1")])).isOk == false)
  expect "object naming an undeclared field"
    ((valueOf pair .opaque (Json.mkObj
      [("a", .str "1"), ("b", .str "2"), ("c", .str "3")])).isOk == false)
  expect "struct written as hex" ((valueOf pair .opaque (.str "0x01000200")).isOk == false)
  -- Equal offsets encode empty bodies, while a gap before the first body is invalid.
  let lists := Desc.list (.byteList 2) 2
  checkCanonical lists #[8, 0, 0, 0, 8, 0, 0, 0]
  -- A first offset of five leaves one unused byte after a four-byte header and must be rejected.
  expect "offset gap" ((deserialize (.container ["items"] [.byteList 2])
    #[5, 0, 0, 0, 0]).isOk == false)
  -- An input breaking several rules is refused for the first one the specification reads.
  -- The budget comes first, then each fixed field, then the offsets, then each body.
  let flagThenBytes := Desc.container ["flag", "data"] [.bool, .byteList 1]
  refusedWith "budget before a fixed field" (deserialize flagThenBytes #[2, 0, 0, 0])
    "SCOPE_TOO_SMALL"
  refusedWith "fixed field before the first offset" (deserialize flagThenBytes #[2, 0, 0, 0, 0])
    "NOT_A_BIT"
  refusedWith "fixed field before a progressive first offset"
    (deserialize (.progressiveContainer [true, true] ["flag", "data"] [.bool, .byteList 1])
      #[2, 0, 0, 0, 0]) "NOT_A_BIT"
  -- A fixed field declared after a body is still read before that body.
  refusedWith "fixed field before an earlier body"
    (deserialize (.container ["data", "flag"] [.byteList 1, .bool]) #[5, 0, 0, 0, 2, 9, 9])
    "NOT_A_BIT"
  -- A broken table is still refused ahead of a broken body.
  refusedWith "offsets before a body"
    (deserialize (.container ["flag", "data"] [.bool, .byteList 1]) #[1, 4, 0, 0, 0, 9, 9])
    "FIRST_OFFSET"
  -- Only the digits the mapping writes are an integer, with no padding or separator.
  refusedWith "integer with a separator" (valueOf .uint64 .opaque (.str "1_000")) "WRONG_TYPE"
  refusedWith "integer with a leading zero" (valueOf .uint64 .opaque (.str "007")) "WRONG_TYPE"
  refusedWith "integer of no digits" (valueOf .uint64 .opaque (.str "")) "WRONG_TYPE"
  expect "integer zero" ((valueOf .uint64 .opaque (.str "0")).toOption == some (.uint 0))
  -- A selector is an integer too, so the same digits are refused there.
  let flag := Desc.compatibleUnion [1] [.bool]
  refusedWith "selector with a leading zero"
    (valueOf flag .opaque (Json.mkObj [("selector", .str "01"), ("data", .bool true)])) "WRONG_TYPE"
  -- A union is written as two fields, so a third is refused as it is for a struct.
  refusedWith "union naming an undeclared field"
    (valueOf flag .opaque (Json.mkObj
      [("selector", .str "1"), ("data", .bool true), ("junk", .bool true)])) "UNDECLARED_FIELD"
  -- A root of the wrong width is answered false, as the specification compares it.
  let wide := combine zeroChunk zeroChunk
  expect "short root, single proof"
    ((verifyMerkleProof zeroChunk [zeroChunk] 2 #[0]).toOption == some false)
  expect "short root, multiproof"
    ((verifyMerkleMultiproof [zeroChunk] [zeroChunk] [2] #[0]).toOption == some false)
  expect "full root, single proof"
    ((verifyMerkleProof zeroChunk [zeroChunk] 2 wide).toOption == some true)
  -- The index and the counts are checked before any node width.
  refusedWith "index before leaf width" (verifyMerkleProof #[0] [zeroChunk] 0 zeroChunk)
    "NOT_A_GINDEX"
  refusedWith "branch length before leaf width"
    (verifyMerkleProof #[0] [zeroChunk, zeroChunk] 2 zeroChunk) "BRANCH_LENGTH"
  refusedWith "proof length before leaf width"
    (verifyMerkleMultiproof [#[0]] [zeroChunk, zeroChunk] [2] zeroChunk) "PROOF_LENGTH"
  -- A union has no default, which is its own refusal and not a mismatch.
  refusedWith "union default" flag.default "NO_DEFAULT"
  -- A declared limit bounds a progressive value's root as it bounds its encoding.
  let capped := Desc.progressiveList .uint8 (some 1)
  refusedWith "progressive list over its limit, encoding"
    (serialize capped (.seq [.uint 1, .uint 2])) "LIMIT"
  refusedWith "progressive list over its limit, root"
    (hashTreeRoot capped (.seq [.uint 1, .uint 2])) "LIMIT"
  refusedWith "progressive bit list over its limit, root"
    (hashTreeRoot (.progressiveBitList (some 1)) (.bits #[true, true])) "LIMIT"
  expect "progressive list within its limit" ((hashTreeRoot capped (.seq [.uint 1])).isOk)
  -- A value the type does not admit has no document either.
  refusedWith "byte vector of the wrong length, document"
    (jsonOf (.byteVector 4) .opaque (.bytes #[1, 2, 3])) "SCOPE"
  refusedWith "byte list over its limit, document"
    (jsonOf (.byteList 1) .opaque (.bytes #[1, 2, 3])) "LIMIT"
  refusedWith "vector of the wrong length, document"
    (jsonOf (.vector .bool 3) .opaque (.seq [.bool true])) "SCOPE"
  refusedWith "list over its limit, document"
    (jsonOf (.list .bool 0) .opaque (.seq [.bool true])) "LIMIT"
  refusedWith "progressive list over its limit, document"
    (jsonOf capped .opaque (.seq [.uint 1, .uint 2])) "LIMIT"
  -- A selector outside the declared range is refused rather than cut to one byte.
  let illegal := Desc.compatibleUnion [257] [.bool]
  refusedWith "selector past one byte, encoding" (serialize illegal (.union 257 (.bool true)))
    "UNION_SELECTOR_RANGE"
  refusedWith "selector past one byte, root" (hashTreeRoot illegal (.union 257 (.bool true)))
    "UNION_SELECTOR_RANGE"
  refusedWith "reserved selector, decoding" (deserialize (.compatibleUnion [128] [.bool]) #[128, 1])
    "UNION_SELECTOR_RANGE"
  IO.println "Lean regressions passed"
