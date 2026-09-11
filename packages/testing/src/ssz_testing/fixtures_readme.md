# SSZ conformance vectors

Generated from the Python reference implementation in this repository by `just fill`.

293 cases: 199 an implementation must accept, 94 it must refuse.
Read [what a passing run proves](#what-a-passing-run-proves) before relying on them.

## Layout

One case is one file.

```
fixtures/<format>/<kind>/<valid|invalid>/<case id>.json
fixtures/ssz/vector/valid/uint16_vector3-mixed.json
fixtures/ssz_type_rejection/vector/invalid/illegal-vector-zero_length.json
```

`<format>` is the fixture format: `ssz` for the byte strings below, `ssz_type_rejection` for the declarations at the end.
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
| `BitVector`, `BitList`, `ProgressiveBitList` | `{"data": "0x0d"}` |
| `ByteVector` | `"0xdeadbeef"` |
| `ByteList` | `{"data": "0x0102"}` |
| `Vector`, `List`, `ProgressiveList` | `{"data": ["1", "2"]}` |
| `Container`, `ProgressiveContainer` | `{"side": "1", "color": "2"}` |
| `CompatibleUnion` | `{"selector": "1", "data": {...}}` |

An integer is decimal digits in a string, so a 64-bit value survives a parser holding JSON numbers as doubles.
A bitfield's hex is exactly the bytes it serializes to, delimiter bit included.

Two shapes differ from the consensus-specs mapping: every collection is wrapped in a one-key object under `data`, where that mapping writes the array or hex bare — and `ByteVector` is the lone exception, written bare.

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
    "value": {"data": ["100", "200", "65535"]},
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

Every name above appears in this suite. `OFFSET_OVERFLOW` completes the vocabulary and needs a composite of at least 4 GiB to fire, so no vector names it.
The rest of the catalogue covers constructing values, walking paths and proofs, which no vector exercises.

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

The rest of the `TypeFault` catalogue is about this implementation's own Python machinery — a string handed in where an integer was declared, a width asked of a type that has none — which another language cannot fail and no vector names.

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

No second implementation has confirmed a byte string or a root here.
[PR #132](https://github.com/ethereum/ssz-specs/pull/132) adds a Lean implementation cross-checked against this one, and would be the first independent check.

## Not covered

- No proof or generalized-index vectors, though the implementation carries both.
- No vectors for the JSON mapping itself.
