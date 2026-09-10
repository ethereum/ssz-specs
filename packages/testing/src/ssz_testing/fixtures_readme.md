# SSZ conformance vectors

Every case here is generated from the Python reference implementation in this repository, by `just fill`.
They succeed the `ssz_generic` suite that consensus-specs removed in [PR #5524](https://github.com/ethereum/consensus-specs/pull/5524).

Read [What a passing run proves](#what-a-passing-run-proves) before you rely on them.

## Where a case lives

One case is one file.

```
fixtures/ssz/vector/valid/uint16_vector3-mixed.json
         |   |      |     |
         |   |      |     `- the case id, its slashes turned into dashes
         |   |      `- whether a decoder must accept the bytes
         |   `- the SSZ kind, snake-cased
         `- the fixture format, "ssz_test" without its "_test"
```

The case id is what names a case: `uint16_vector3/mixed`, slash-separated segments of lowercase words, unique across the suite.
It is authored, so it survives a rename of the test that fills it.
The file name is that id with each `/` turned into `-`, a character no case id holds.

Two files sit at the root.

`index.json` holds a `cases` array, one row per case, ordered by path.

| Field | Meaning |
| --- | --- |
| `id` | The case id. |
| `path` | Where the case is, relative to this directory. |
| `typeName` | The declared type name the case is about. |
| `kind` | The SSZ kind, the same spelling as the directory. |
| `valid` | Whether a decoder must accept the case's bytes. |
| `tags` | Themes the case was filled under, for selecting a subset. |
| `sha256` | Digest of the case file's bytes, unprefixed. |

`manifest.json` states `formatVersion`, which is bumped whenever this layout changes, alongside `specVersion`, `generator` and `caseCount`.

This suite ships 117 cases: 109 that must decode, and 8 that must be rejected.

## The envelope

| Field | Type | Present | Meaning |
| --- | --- | --- | --- |
| `valid` | boolean | always | Whether a decoder must accept `serialized`. |
| `typeName` | string | always | Class name the type was declared under. |
| `typeDescriptor` | object | always | That type's declaration, in full. |
| `serialized` | hex string | always | The bytes to hand the decoder. |
| `value` | varies | `valid` cases | The value those bytes encode, in the JSON mapping of its own type. |
| `root` | hex string | `valid` cases | `hash_tree_root` of that value. |
| `rejectionReason` | string | invalid cases | The name the decoder must refuse those bytes with. |
| `_info` | object | always | Metadata about the case, not part of the case. |

Branch on `valid`, not on which fields turned up.

A field that does not apply is left out of the file, never written as `null`.
Every hex string is `0x`-prefixed and lowercase, so an empty byte string is `"0x"`.
`root` is 32 bytes, 64 hex digits.

`typeName` is a label, not a contract.
It is unique across the suite, and the generator refuses a run in which one name stands for two different declarations.
What a consumer builds the type from is `typeDescriptor`.

## The type descriptor

`typeDescriptor` is read off the declared class, and carries everything that fixes a wire format and a tree.
`kind` is always present, and the rest depends on it.

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

The directory spelling is the kind snake-cased, so `BitList` files under `bit_list`.
The two differ on purpose: the descriptor names the SSZ type as the specification spells it, and the directory is a path segment.

`elementType` is a descriptor of its own, and so is the `type` of every field and every option, all the way down.

`fields` and `options` are JSON arrays, not objects, because SSZ order is load-bearing.
A `fields` entry is `{"name", "type"}`, in the declaration order the wire format follows.
An `options` entry is `{"selector", "type"}`, the selector being the byte an encoding of that option leads with.
`activeFields` is one bit per position, set where a field sits and clear on a gap.

The descriptor is structural: it names the fields of a container, and nothing below the outer `typeName` carries a name.
`packages/testing/tests/test_type_descriptor.py` rebuilds each kind from a descriptor alone and reads a vector back with it.

## The JSON mapping of `value`

| SSZ type | JSON |
| --- | --- |
| `Boolean`, `Bit` | `true` |
| `Byte` | `"0xff"` |
| `Uint8` through `Uint256` | `"255"` |
| `BitVector` | `{"data": "0x55"}` |
| `BitList` | `{"data": "0x0d"}` |
| `ProgressiveBitList` | `{"data": "0x0d"}` |
| `ByteVector` | `"0xdeadbeef"` |
| `ByteList` | `{"data": "0x0102"}` |
| `Vector` | `{"data": ["1", "2", "3"]}` |
| `List` | `{"data": ["1", "2"]}` |
| `ProgressiveList` | `{"data": ["7"]}` |
| `Container` | `{"x": "1", "b": "0xab"}` |
| `ProgressiveContainer` | `{"side": "1", "color": "2"}` |
| `CompatibleUnion` | `{"selector": "1", "data": {"side": "1", "color": "2"}}` |

An integer is a string of decimal digits, so a 64-bit value survives a parser that holds JSON numbers as doubles.
A bitfield's hex holds exactly the bytes it serializes to, delimiter bit and all.
A boolean is a JSON boolean, and is the one value that is neither a string nor an object.

Two shapes will catch out a reader who knows the consensus-specs mapping.
Every collection is wrapped in a one-key object under `data`, where that mapping writes the array or the hex string bare.
A `ByteVector` is the exception among collections, and is written bare.

## Reading a valid case

1. Build the type from `typeDescriptor`.
2. Decode `serialized` into a value of that type.
3. Compare the decoded value against `value`, read through the mapping above.
4. Re-encode the decoded value, and compare the bytes against `serialized`.
5. Compute `hash_tree_root` of the decoded value, and compare against `root`.

Step 4 is not redundant with step 2.
It is what catches a decoder that accepts a non-canonical encoding of a value it otherwise reads correctly.

## A worked example

`fixtures/ssz/vector/valid/uint16_vector3-mixed.json`:

```json
{
    "typeName": "SampleUint16Vector3",
    "serialized": "0x6400c800ffff",
    "value": {
        "data": [
            "100",
            "200",
            "65535"
        ]
    },
    "root": "0x6400c800ffff0000000000000000000000000000000000000000000000000000",
    "valid": true,
    "typeDescriptor": {
        "kind": "Vector",
        "length": 3,
        "elementType": {
            "kind": "Uint16",
            "bits": 16
        }
    },
    "_info": {
        "hash": "0x29ce4cc1d17eef8427f4d629100097c7f148bedcf89f3e09d3191db529fd234d",
        "comment": "`ssz-specs` generated test",
        "testId": "uint16_vector3/mixed",
        "generatedBy": "tests/fillers/ssz/test_basic_types.py::test_uint16_vector3_typical",
        "description": "A three-element uint vector with mixed values round-trips unchanged.\n\nGiven\n-----\n- a vector of three two-byte uints with mixed values.\n- the last element at the maximum value (65535).\n\nWhen\n----\n- the value is encoded and then decoded.\n\nThen\n----\n- the decoded value equals the original.",
        "fixtureFormat": "ssz_test"
    }
}
```

- The path files the case under kind `vector` and validity `valid`, and `_info.testId` gives the case id the file name was built from.
- `typeDescriptor` says the whole type: exactly three elements, each a 16-bit unsigned integer.
- `serialized` is six bytes, one little-endian pair per element: 100 is `6400`, 200 is `c800`, 65535 is `ffff`.
- `value` holds three decimal strings, wrapped under `data` because a vector is a collection.
- `root` packs those six bytes into one 32-byte chunk and right-pads with zeros, which is the whole tree for a value of one chunk.
- `valid` is true, so the bytes must decode.

Checking it against this implementation:

```python
from ssz import Uint16, Vector, hash_tree_root


class SampleUint16Vector3(Vector[Uint16]):
    LENGTH = 3


value = SampleUint16Vector3(data=[100, 200, 65535])
encoded = value.encode_bytes()
assert "0x" + encoded.hex() == "0x6400c800ffff"
assert SampleUint16Vector3.decode_bytes(encoded) == value
assert "0x" + hash_tree_root(value).hex() == (
    "0x6400c800ffff0000000000000000000000000000000000000000000000000000"
)
```

Checking the case's own hash:

```python
import hashlib
import json

case = json.load(open("fixtures/ssz/vector/valid/uint16_vector3-mixed.json"))
body = {name: field for name, field in case.items() if name != "_info"}
canonical = json.dumps(body, sort_keys=True, separators=(",", ":"))
assert "0x" + hashlib.sha256(canonical.encode("utf-8")).hexdigest() == case["_info"]["hash"]
```

## Invalid cases

A case with `valid` false is an input a conforming decoder must refuse.
It carries the type, the bytes and the reason, and nothing else.

`fixtures/ssz/bit_list/invalid/bitlist8-invalid-over_limit.json`, with its `_info` left out:

```json
{
    "rejectionReason": "LIMIT",
    "typeName": "SmokeBitList8",
    "serialized": "0x0010",
    "valid": false,
    "typeDescriptor": {
        "kind": "BitList",
        "limit": 8
    }
}
```

Decode `serialized` into the type `typeDescriptor` declares, and require a failure.
There is no `value` and no `root`, because nothing decoded to hold a value or take a root of.

### `rejectionReason`

The value is the name of a member of the `ValueFault` enumeration in `src/ssz/exceptions.py`.
The catalogue is closed, so a name outside that enumeration can never appear.
A harness should fail loudly on one it does not know, rather than skip the case.
The name is the stable part of a refusal.
The sentence the implementation renders from it is not stable, and is never emitted.

These are the names that decoding a byte string can produce:

| Name | The input |
| --- | --- |
| `EMPTY_ENCODING` | Is empty, where the type needs at least one byte. |
| `FIRST_OFFSET` | Opens with an offset that does not point at the end of the fixed part. |
| `LIMIT` | Holds more elements than the type's declared limit. |
| `NOT_A_BIT` | Encodes a boolean as a byte other than `0x00` or `0x01`. |
| `NO_DELIMITER` | Is a bitlist whose bytes set no delimiter bit. |
| `NO_SELECTOR` | Is a union with no room for a selector byte. |
| `OFFSET_BELOW_TABLE` | Opens with an offset that points inside the offset table itself. |
| `OFFSET_PAST_SCOPE` | Holds an offset that runs past the end of the input. |
| `OFFSET_UNALIGNED` | Opens with an offset that is not a multiple of the four-byte offset width. |
| `OFFSET_UNORDERED` | Holds an offset above the offset after it. |
| `PADDING_BITS` | Is a bit vector whose last byte sets a bit past the declared length. |
| `SCOPE` | Is a different length from the fixed width the type spans. |
| `SCOPE_TOO_SMALL` | Is shorter than the type's fixed part. |
| `SCOPE_UNDIVIDED` | Is not a whole number of fixed-width elements. |
| `TRAILING_ZEROS` | Is a bitlist with zero bytes past its delimiter, a second encoding of one value. |
| `TRUNCATED` | Ran out while a value was being read from it. |
| `UNKNOWN_SELECTOR` | Names a union selector that the type declares no option for. |

`OFFSET_OVERFLOW` completes the decoding vocabulary, and needs a composite of at least 4 GiB to fire.

The rest of the catalogue belongs to constructing values, walking paths, and building or verifying proofs, none of which any vector exercises.
Six of these names appear in this suite: `FIRST_OFFSET`, `LIMIT`, `NO_SELECTOR`, `SCOPE`, `TRUNCATED` and `UNKNOWN_SELECTOR`.

## `_info`

| Field | Meaning |
| --- | --- |
| `hash` | Digest of the case, described below. |
| `comment` | Fixed provenance note, the same on every case. |
| `testId` | The case id, the same string the file is named after. |
| `generatedBy` | Node id of the test that filled the case, for tracing it back to its source. |
| `description` | The generating test's docstring, and its class docstring where it has one. |

`_info` is metadata about the case, and never part of what a harness asserts.

`hash` is a SHA-256 over the case with `_info` removed.
It is not the index's `sha256`, which digests the file's whole text, `_info` and indentation included.

To reproduce `hash`:

1. Take the case object and drop the `_info` member.
2. Serialize what remains as JSON with keys sorted lexicographically at every level of nesting.
3. Use no whitespace: `,` between members and `:` between key and value.
4. SHA-256 the UTF-8 bytes of that string, and render the digest as `0x` and 64 lowercase hex digits.

The keys to sort are the camelCase names already in the file.
Fields that are absent stay absent, and a consumer never adds a `null` back.

For the worked example above, the canonical string is:

```
{"root":"0x6400c800ffff0000000000000000000000000000000000000000000000000000","serialized":"0x6400c800ffff","typeDescriptor":{"elementType":{"bits":16,"kind":"Uint16"},"kind":"Vector","length":3},"typeName":"SampleUint16Vector3","valid":true,"value":{"data":["100","200","65535"]}}
```

## What a passing run proves

Your implementation agrees with this one.
It does not prove that either agrees with the specification.

Every part of a vector comes from the same implementation, with no independent oracle:

- The encoder produced `serialized`.
- The same project's decoder read those bytes back, and the generator asserted that the decoded value equals the authored one.
- The generator re-encoded the decoded value and asserted the bytes are identical.
- `hash_tree_root` produced `root`, which is recorded, not checked against anything.

The round-trip catches a decoder that disagrees with its own encoder.
It cannot catch an encoder and a decoder that agree on something the specification does not say.
A wrong root is recorded as confidently as a right one.

Filling with `SSZ_PARANOID_ROOTS=1`, which is what `just fill` does, recomputes every memoized root instead of trusting the memo.
That catches a stale memo, and nothing else: the recomputation runs the same layout code.

Invalid cases are checked harder within the same limit.
The decoder must raise, and it must raise the fault the author named, so a vector cannot record a refusal that fired for an unrelated reason.
The author and the decoder are still the same project.

No second implementation has confirmed a single byte string or a single root here.
[PR #132](https://github.com/ethereum/ssz-specs/pull/132) adds a Lean implementation, proved and cross-checked against this one, and would be the first independent check.

## What is not covered

- No proof vectors and no generalized-index vectors, though the reference implementation carries both.
- No vectors for a declaration the specification calls illegal, such as a zero-length vector or a field-less container.
  Those are refused from a separate catalogue that `rejectionReason` cannot name, and every emitted `typeDescriptor` is legal by construction.
- No vectors for the JSON mapping itself: `value` is written in it, but no case asks a consumer to parse JSON, and none pins a JSON input that must be refused.
- Thin negative coverage: 8 cases and 6 distinct reasons, spread over three kinds only.
  Five are compatible unions, two are progressive containers, and one is a bitlist.
  Nothing rejects a malformed uint, boolean, byte vector, byte list, bit vector, vector, list, container or progressive list.
