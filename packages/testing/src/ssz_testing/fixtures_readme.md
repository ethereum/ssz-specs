# SSZ conformance vectors

Generated from the Python reference implementation in this repository by `just fill`.

400 cases: 280 an implementation must accept, 120 it must refuse.
Read [what a passing run proves](#what-a-passing-run-proves) before relying on them.

## Layout

One case is one file, filed under the format that produced it.

```
fixtures/<format>/<kind>/<valid|invalid>/<case id>.json
fixtures/ssz/vector/valid/uint16_vector3-mixed.json
fixtures/ssz_type_rejection/vector/invalid/illegal-vector-zero_length.json
fixtures/ssz_gindex/container/valid/gindex-light_client-altair-finalized_root.json
fixtures/proof/container/valid/proof-container-flat_field.json
fixtures/ssz_json/vector/valid/json-vector_of_bytes.json
```

`<format>` is the fixture format: `ssz` for the byte strings below, `ssz_type_rejection` for the [illegal declarations](#illegal-type-declarations), `ssz_gindex` for the [generalized-index vectors](#generalized-index-vectors), `proof` and `multiproof` for the [Merkle proofs](#proof-vectors), and `ssz_json` for the [JSON documents](#json-mapping-vectors) — each with an envelope of its own.
`<kind>` is the SSZ kind, snake-cased.
The file name is the case id with each `/` turned into `-`, so `uint16_vector3/mixed` becomes `uint16_vector3-mixed.json`.
The id is authored and unique, so it survives a rename of the test that fills it.

`index.json` lists every case, ordered by path, with `id`, `path`, `typeName`, `kind`, `valid`, `tags` and `sha256` (of the file's bytes, unprefixed).
`manifest.json` gives `formatVersion`, `specVersion`, `generator` and `caseCount`.

## The envelope

| Field | Present | Meaning |
| --- | --- | --- |
| `valid` | always | Whether a decoder must accept `serialized`. |
| `typeName` | always | Class name the type was declared under. |
| `typeDescriptor` | always | That type's declaration, in full. |
| `serialized` | always | The bytes to hand the decoder. |
| `value` | valid | What those bytes encode. |
| `root` | valid | `hash_tree_root` of that value. |
| `rejectionReason` | invalid | The name the decoder must refuse with. |
| `_info` | always | Metadata, never part of what you assert. |

Branch on `valid`, not on which fields turned up. An absent field is omitted, never `null`.
Hex is `0x`-prefixed and lowercase, so an empty byte string is `"0x"`.
`typeName` is a label, not a contract — build the type from `typeDescriptor`.

## The type descriptor

Read off the declared class. `kind` is always present; the rest depends on it.

| `kind` | Also carries | Directory |
| --- | --- | --- |
| `Uint8` … `Uint256` | `bits` | `uint8` … `uint256` |
| `Boolean` | — | `boolean` |
| `BitVector` | `length` | `bit_vector` |
| `BitList` | `limit` | `bit_list` |
| `ProgressiveBitList` | — | `progressive_bit_list` |
| `ByteVector` | `length` | `byte_vector` |
| `ByteList` | `limit` | `byte_list` |
| `Vector` | `length`, `elementType` | `vector` |
| `List` | `limit`, `elementType` | `list` |
| `ProgressiveList` | `elementType` | `progressive_list` |
| `Container` | `fields` | `container` |
| `ProgressiveContainer` | `activeFields`, `fields` | `progressive_container` |
| `CompatibleUnion` | `options` | `compatible_union` |

`elementType`, and the `type` of every field and option, are descriptors of their own.
`fields` (`{"name", "type"}`) and `options` (`{"selector", "type"}`) are arrays, not objects, because SSZ order is load-bearing; `activeFields` is one bit per position.
`packages/testing/tests/test_type_descriptor.py` rebuilds each kind from a descriptor alone.

## How `value` is written

| SSZ type | JSON |
| --- | --- |
| `Boolean`, `Bit` | `true` |
| `Byte` | `"0xff"` |
| `Uint8` … `Uint256` | `"255"` |
| `BitVector`, `BitList`, `ProgressiveBitList` | `"0x0d"` |
| `ByteVector`, `ByteList` | `"0xdeadbeef"` |
| `Vector[Byte]`, `List[Byte]`, `ProgressiveList[Byte]` | `"0x0102"` |
| `Vector`, `List`, `ProgressiveList` | `["1", "2"]` |
| `Container`, `ProgressiveContainer` | `{"side": "1", "color": "2"}` |
| `CompatibleUnion` | `{"selector": "1", "data": {...}}` |

An integer is decimal digits in a string, so a 64-bit value survives a parser holding JSON numbers as doubles.
A bitfield's hex is exactly the bytes it serializes to, delimiter bit included.
A collection is written bare, so a byte sequence is one hex string however it was spelled, and nothing carries a wrapping object.

## Running a case

1. Build the type from `typeDescriptor`.
2. Decode `serialized`.
3. Compare against `value`.
4. Re-encode, and compare the bytes against `serialized` — this is what catches a decoder that accepts a non-canonical encoding.
5. Compute `hash_tree_root`, and compare against `root`.

For an invalid case, decode `serialized` and require a failure naming `rejectionReason`.

## A worked example

`fixtures/ssz/vector/valid/uint16_vector3-mixed.json`, with `_info` trimmed:

```json
{
    "typeName": "SampleUint16Vector3",
    "serialized": "0x6400c800ffff",
    "value": ["100", "200", "65535"],
    "root": "0x6400c800ffff0000000000000000000000000000000000000000000000000000",
    "valid": true,
    "typeDescriptor": {
        "kind": "Vector",
        "length": 3,
        "elementType": {"kind": "Uint16", "bits": 16}
    }
}
```

Three 16-bit elements, little-endian; the root packs those six bytes into one chunk and right-pads with zeros.

An invalid case carries nothing beyond the refusal:

```json
{
    "typeName": "SmokeBitList8",
    "serialized": "0x0010",
    "valid": false,
    "rejectionReason": "LIMIT",
    "typeDescriptor": {"kind": "BitList", "limit": 8}
}
```

## Generalized-index vectors

A case under `ssz_gindex/` asks a different question: not what a type's bytes are, but where in its Merkle tree one value sits.
There are no bytes and no value, only a type, a path, and the generalized index that path names.

| Field | Present | Meaning |
| --- | --- | --- |
| `valid` | always | Whether the type resolves this path at all. |
| `typeName` | always | Class name the type was declared under. |
| `typeDescriptor` | always | That type's declaration, in full, exactly as an `ssz` case carries it. |
| `path` | always | The steps from the type's own root down to the node. |
| `gindex` | valid | The generalized index, in decimal, as a string. |
| `depth` | valid | Levels that index sits below the root, which is the node count of its proof branch. |
| `chunkCount` | bounded shapes | Leaves the type merkleizes into at its own level. |
| `treeWidth` | bounded shapes | Power of two those leaves pad out to. |
| `rejectionReason` | invalid | The name the type must refuse the path with. |

`gindex` is a decimal string for the same reason every integer in a `value` is: a deep path outgrows the 53 bits a JSON number is safely read into.
`depth` is `gindex.bit_length() - 1` and `treeWidth` is `chunkCount` rounded up to a power of two, so both are redundant on purpose — an implementation whose index is wrong reads off *which* number it got wrong rather than only that the answer mismatched.

`chunkCount` and `treeWidth` describe the declared type, not the path, and are absent for a progressive shape, which grows with its data and pads to nothing.
A `CompatibleUnion` reports one chunk: an option is reached whole through the root's left child, and the union contributes no leaf of its own.

### How a path is written

A path is a JSON array, and the type of each element says what kind of step it is.

| Step | Selects |
| --- | --- |
| a string | The field of that name, on a `Container` or a `ProgressiveContainer`. |
| an integer | The element at that position — or, on a `CompatibleUnion`, the option with that selector. |
| `{"mixin": ...}` | One of the three words a root is hashed against. It ends the path. |

The three words are `elementCount` (what a `List`, `ByteList`, `BitList`, `ProgressiveList` or `ProgressiveBitList` mixes in), `fieldLayout` (a `ProgressiveContainer`'s active fields) and `typeSelector` (a `CompatibleUnion`'s selector).
Each is wrapped in an object rather than spelled as a bare string, so that no field name can ever be mistaken for one.

```json
["f20", "root"]
[3]
[{"mixin": "elementCount"}]
[1, "color"]
```

### Running a case

1. Build the type from `typeDescriptor`.
2. Resolve `path` against it.
3. For a valid case, compare the index against `gindex`; for an invalid one, require a failure naming `rejectionReason`.

An index resolves against the declaration alone. Whether a value reaches that far — whether a progressive list is that long, or a gap holds a node — is a question only a value answers, and no case here asks it.

### A worked example

`fixtures/ssz_gindex/container/valid/gindex-light_client-altair-finalized_root.json`, with `typeDescriptor` and `_info` trimmed:

```json
{
    "typeName": "GindexAltairState",
    "path": ["f20", "root"],
    "gindex": "105",
    "depth": 6,
    "valid": true,
    "chunkCount": 24,
    "treeWidth": 32
}
```

105 is the index every light client hard-codes for the finalized checkpoint root.
`chunkCount` and `treeWidth` are why: 24 fields pad to 32 leaves, which puts field 20 at 52 and its second subfield at 105.
An implementation that pads to 24 instead answers 89, and the two extra fields say so at a glance.
## Proof vectors

Two more trees sit beside `ssz/`, filled from values of the same kind: `proof/` carries one Merkle branch per case, `multiproof/` several claims proved at once.

Every proof case carries its subject the way an `ssz/` case does — `typeName`, `typeDescriptor`, `serialized`, `value` and `root` — so four things can be checked apart from one another:

1. decode `serialized`, compare against `value`, and hash it: the root must be `root`.
2. resolve `path` against the type: it must give `index`.
3. read the node at `index` off your own tree: it must be `leaf`.
4. hash `leaf` upward with `branch`: it must give `root`.

A verifier that only does the fourth passes on a wrong index, a wrong path resolution and a wrong tree, since a branch built for the wrong node still rebuilds a root.

| Field | Format | Meaning |
| --- | --- | --- |
| `path` | proof | Steps from the root down to the node being proved. |
| `index` | proof | Decimal generalized index those steps resolve to. |
| `leaf` | proof | The node the vector claims at that index. |
| `branch` | proof | Sibling nodes from the leaf upward, in the order a verifier consumes them. |
| `branchIndices` | proof | The index of each of those nodes. |
| `paths` | multiproof | Steps down to each claimed node. |
| `indices` | multiproof | Decimal generalized index each of those paths resolves to. |
| `leaves` | multiproof | The node claimed at each index, one per index, in that order. |
| `helperIndices` | multiproof | Every node the request needs, in descending order. |
| `proof` | multiproof | The node for each of those helper indices, in that same order. |
| `stricterThanSpec` | both | Present only where this suite refuses what `merkle-proofs.md` admits. |

`branchIndices` is redundant with `index`, which already fixes which siblings a branch holds. That is what it is for: it pins the ordering separately from the hashing, so a verifier reading a branch top-down fails on the indices rather than only on a root that came out wrong.

`helperIndices` descending is a contract rather than an artifact. `get_helper_indices` sorts in reverse so that a request for a single index is exactly that index's branch, node for node: `multiproof/container/one_index_is_a_branch` pins that equivalence, and `multiproof/container/spec_worked_example` pins the three nodes `merkle-proofs.md` draws for indices 8, 9 and 14.

An index is decimal digits in a string, like every other integer here, since a generalized index inside a beacon state runs past what a double holds.
A path step is an object with exactly one key: `field` for a container field, `position` for an element, and `mixin` for a reserved word — `__len__`, `__active_fields__` or `__selector__` — naming a word the root is hashed against.

`valid` is the whole verdict: false says a verifier must not accept this proof.
`rejectionReason` turns up beside it only where a named refusal has to fire; a case that merely fails to rebuild the root, such as a tampered leaf or a reversed branch, carries none.
Where a multiproof's index set is refused outright, `helperIndices` and `proof` are empty, no node having been reached.

### Where this suite is stricter than the specification

`merkle-proofs.md` admits five inputs this implementation refuses. Each such case carries `stricterThanSpec`, saying what the specification does instead.
Read that field before calling one of them a failure: it marks "this repository is stricter here", not "you are wrong". A spec-faithful verifier accepts four of the five and fails the last on a missing root.

| Case | This suite | `merkle-proofs.md` |
| --- | --- | --- |
| Index 1 with an empty branch | `ROOT_HAS_NO_BRANCH` | Returns the leaf, which is the root |
| A 31-byte proof node | `COUNT` | Hashes it, moving the boundary inside the pair |
| A repeated index | `REPEATED_INDEX` | Keeps the last leaf given for it |
| An index below another | `NESTED_INDEX` | Rebuilds the higher one, leaving the lower unchecked |
| An empty index set | `EMPTY_REQUEST` | Reaches the end with no node at index 1 to return |

## `rejectionReason`

The name of a `ValueFault` member in `src/ssz/exceptions.py`. The catalogue is closed, so fail loudly on a name you do not know rather than skipping the case.
The name is stable; the sentence rendered from it is not, and is never emitted.

| Name | The input |
| --- | --- |
| `EMPTY_ENCODING` | Is empty, where the type needs at least one byte. |
| `FIRST_OFFSET` | Opens with an offset that does not point at the end of the fixed part. |
| `LIMIT` | Holds more elements than the declared limit. |
| `NOT_A_BIT` | Encodes a boolean as a byte other than `0x00` or `0x01`. |
| `NO_DELIMITER` | Is a bitlist setting no delimiter bit. |
| `NO_SELECTOR` | Is a union with no room for a selector byte. |
| `OFFSET_BELOW_TABLE` | Opens with an offset pointing inside the offset table. |
| `OFFSET_PAST_SCOPE` | Holds an offset running past the end of the input. |
| `OFFSET_UNALIGNED` | Opens with an offset that is not a multiple of four. |
| `OFFSET_UNORDERED` | Holds an offset above the one after it. |
| `PADDING_BITS` | Is a bit vector setting a bit past its declared length. |
| `SCOPE` | Is a different length from the fixed width the type spans. |
| `SCOPE_TOO_SMALL` | Is shorter than the type's fixed part. |
| `SCOPE_UNDIVIDED` | Is not a whole number of fixed-width elements. |
| `TRAILING_ZEROS` | Is a bitlist with zero bytes past its delimiter, a second encoding of one value. |
| `TRUNCATED` | Ran out while a value was being read. |
| `UNKNOWN_SELECTOR` | Names a selector the union declares no option for. |

A generalized-index case may instead name a `TypeFault`, since a path is refused by the type as often as by one of its steps. Both catalogues are closed, and a name from either is a hard failure if you do not know it.

| Name | The path |
| --- | --- |
| `NO_MIXIN` | Names a word this shape does not mix in. |
| `NO_PARTS` | Carries on past a basic value, which is a run of bytes inside a chunk and no node of its own. |
| `NO_PARTS_MIXIN` | Carries on past a mixed-in word, which is one leaf. |
| `NO_SUCH_FIELD` | Names a field the struct does not declare — a vacant layout position among them. |
| `NO_SUCH_OPTION` | Names a selector the union declares no option for. |
| `NO_SUCH_POSITION` | Names a position outside what the shape declares, `-1` included. |

Every name in the two tables above appears in this suite. `OFFSET_OVERFLOW` completes the `ValueFault` vocabulary and needs a composite of at least 4 GiB to fire, so no vector names it.
The rest of that catalogue covers constructing values and building proofs, which no vector exercises.
A proof case names one of these instead, refused while the branch or the request was read rather than while bytes were.

| Name | The proof |
| --- | --- |
| `BRANCH_LENGTH` | Holds a different number of nodes from the one the index needs. |
| `COUNT` | Holds a node that is not 32 bytes wide. |
| `EMPTY_REQUEST` | Is a multiproof asking for no index at all. |
| `LEAF_COUNT` | Gives a different number of leaves from indices. |
| `NESTED_INDEX` | Asks for an index lying below another in the same request. |
| `PROOF_LENGTH` | Holds a different number of nodes from the one the request needs. |
| `REPEATED_INDEX` | Asks for the same index twice. |
| `ROOT_HAS_NO_BRANCH` | Is about index 1, which sits on no branch of its own. |

Every name in the two tables above appears in this suite. `OFFSET_OVERFLOW` completes the decoding vocabulary and needs a composite of at least 4 GiB to fire, so no vector names it.
The rest of the catalogue covers constructing values and walking paths, which no vector exercises.

## Illegal type declarations

`fixtures/ssz_type_rejection/` holds the declarations the specification calls illegal — a vector of zero elements, a container naming no field, a union selector outside 1 through 127.
Nothing is decoded: the input under test is the declaration itself, and there are no bytes.

| Field | Present | Meaning |
| --- | --- | --- |
| `valid` | always | `false`, always. |
| `typeName` | always | Name to declare the type under, which some refusals quote back. |
| `typeDescriptor` | always | The illegal declaration, read exactly as any other descriptor is. |
| `rejectionReason` | always | The name of the rule that must refuse it. |
| `_info` | always | Metadata, never part of what you assert. |

Build the type from `typeDescriptor` and require the build to fail.
An implementation that checks a declaration lazily may fail later — at the first value, encoding or root — and that counts, so long as no value of the type is ever produced.

`rejectionReason` here names a `TypeFault` member rather than a `ValueFault` one, from the same file and read the same way: the name is stable, the sentence rendered from it is not, and the catalogue is closed.
No name appears in both catalogues, so a consumer holding one table of reasons never has to ask which it came from.

| Name | The declaration |
| --- | --- |
| `CAPACITY_NEGATIVE` | Counts what it holds with a negative number. |
| `CONTAINER_EMPTY` | Is a container naming no field. |
| `LAYOUT_FIELD_COUNT` | Sets a number of layout positions other than its field count. |
| `LAYOUT_TOO_WIDE` | Lays out more than 256 positions, which one 32-byte word cannot hold. |
| `LAYOUT_TRAILING_GAP` | Ends its layout on a gap rather than on a field. |
| `LAYOUT_WIDTH` | Lays out no position at all. |
| `NOT_ENTITLED` | Declares a capacity its shape has none of. |
| `UNION_EMPTY` | Is a union offering no option. |
| `UNION_INCOMPATIBLE` | Is a union whose options merkleize differently. |
| `UNION_SELECTOR_RANGE` | Gives an option a selector outside 1 through 127. |
| `VECTOR_EMPTY` | Pins a fixed count of zero. |

Beyond these and the path refusals above, the `TypeFault` catalogue is about this implementation's own Python machinery — a string handed in where an integer was declared, a width asked of a type that has none — which another language cannot fail and no vector names.

## JSON mapping vectors

`fixtures/ssz_json/` asks what a value looks like written as JSON rather than as bytes.
The mapping is normative — an SSZ schema defines the JSON encoding too — and [How `value` is written](#how-value-is-written) above is the same table read from the other side.

| Field | Present | Meaning |
| --- | --- | --- |
| `valid` | always | Whether a parser must accept `document`. |
| `typeName` | always | Class name the type was declared under. |
| `typeDescriptor` | always | That type's declaration, in full, exactly as an `ssz` case carries it. |
| `document` | always | The JSON to hand the parser: the rendering of a value, or the input it must refuse. |
| `serialized` | valid | The SSZ encoding of that same value. |
| `notReadBack` | rarely | Why this implementation only wrote the document, and never read one back. |
| `rejectionReason` | invalid | The name the parser must refuse with. |

`serialized` is what keeps a valid case from being a tautology. Parsing `document` and writing it out again only proves your reader and your writer agree with each other; the bytes pin the value against a representation the mapping never touches.
It duplicates what an `ssz` case carries, and that is the point — no `ssz` case is guaranteed to exist for the type and value a JSON case chose.

### Running a case

1. Build the type from `typeDescriptor`.
2. Parse `document`.
3. Write the parsed value back out: it must be `document` again.
4. Encode it, and compare the bytes against `serialized`.

For an invalid case, parse `document` and require a failure naming `rejectionReason`.

`notReadBack` marks a document this repository can write but not parse, so step 2 never ran here. It says nothing about your implementation: run every step anyway.
One case carries it. A `CompatibleUnion` declares its option field as holding any SSZ value, which compiles to a check no JSON document passes.

### `rejectionReason`

A third closed catalogue, `JsonFault` in `packages/testing/src/ssz_testing/json_mapping.py`, read the way the other two are: the name is stable, the sentence rendered from it is not, and no name is shared with either of them.
A JSON refusal is named at the level of the mapping rather than of whichever machinery caught it, since a parser reaching the same verdict by another route is still right.

| Name | The document |
| --- | --- |
| `BITFIELD_PADDING` | Is a bitfield setting a bit past the length its type declares. |
| `HEX_PREFIX` | Writes a hex byte string without its `0x`. |
| `OVER_LIMIT` | Holds more elements than its type admits. |
| `UNDECLARED_FIELD` | Names a field its struct does not declare. |

### Where this implementation and the mapping part

The specification says every field in the schema must be present with a value, and that a parser *may* ignore additional fields. Four documents sit outside what the mapping spells, and this implementation does not treat them alike:

| The document | The specification | Here |
| --- | --- | --- |
| An object missing a declared field | Must be present with a value | Accepted, the field taking its zero value |
| An object naming an undeclared field | May be ignored | Refused, which the `may` leaves open |
| An integer as a JSON number | A string, so that a uint64 survives | Accepted beside the string |
| A hex byte string with no `0x` | Carries the prefix | Accepted on a byte array, refused on `Byte` and on a bitfield |

Rows two and four carry a vector, each on the half where refusing is what the mapping asks for.
Rows one and three carry none: a vector either way would make one reading of an open question the contract, and the reading it would pin is this implementation's own leniency.

## `_info`

`hash`, `comment`, `testId` (the case id), `generatedBy` (the test that filled it) and `description` (that test's docstring).

`hash` is SHA-256 over the case with `_info` removed, keys sorted at every level, no whitespace — not the index's `sha256`, which digests the file's whole text.

```python
import hashlib, json

case = json.load(open("fixtures/ssz/vector/valid/uint16_vector3-mixed.json"))
body = {name: field for name, field in case.items() if name != "_info"}
canonical = json.dumps(body, sort_keys=True, separators=(",", ":"))
assert "0x" + hashlib.sha256(canonical.encode()).hexdigest() == case["_info"]["hash"]
```

## What a passing run proves

Your implementation agrees with this one. Not that either agrees with the specification.

Every part of a vector comes from the same implementation: its encoder produced `serialized`, its decoder read the bytes back, and `hash_tree_root` produced `root`, which is recorded rather than checked against anything.
The round-trip catches a decoder that disagrees with its own encoder, not an encoder and decoder that agree on something the specification does not say — a wrong root is recorded as confidently as a right one.
Invalid cases are checked harder within the same limit: the decoder must raise the fault the author named. The author and the decoder are still the same project.
A proof case is no different: this implementation resolved the path, read the leaf off its own tree, built the branch and then verified it.

No second implementation has confirmed a byte string or a root here.
[PR #132](https://github.com/ethereum/ssz-specs/pull/132) adds a Lean implementation cross-checked against this one, and would be the first independent check.
