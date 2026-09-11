# `ssz_generic` vectors

The `ssz_generic` view of this repository's SSZ conformance vectors, written by `just export-ssz-generic`.

consensus-specs deleted its own `ssz_generic` suite in [PR #5524](https://github.com/ethereum/consensus-specs/pull/5524) and named this repository the successor. Every client harness built for it reads a directory per case holding `meta.yaml`, `serialized.ssz_snappy` and `value.yaml`. This tree is that shape, so such a harness runs this suite unchanged.

131 of the suite's 353 cases are here: 102 an implementation must accept, 29 it must refuse. Read [what is not here](#what-is-not-here) before treating a clean run as a clean bill of health.

## Layout

```
tests/general/phase0/ssz_generic/<handler>/<valid|invalid>/<case>/
```

The `tests/` prefix is the root of an extracted `consensus-spec-tests` tarball, so a harness configured with a path to one takes this directory in its place.

| File | Present | Holds |
| --- | --- | --- |
| `serialized.ssz_snappy` | always | The bytes to hand the decoder, Snappy block encoded. |
| `meta.yaml` | valid | `root`, the `hash_tree_root` of the value. |
| `value.yaml` | valid | What those bytes encode. |
| `rejection.yaml` | invalid | `reason`, the fault the decoder must refuse with. |

A valid case is checked the way the upstream format defines: encode `value` and match `serialized`, decode `serialized` and match `value`, then compare the root against `meta.yaml`. An invalid case must fail to decode.

`rejection.yaml` is the one file upstream never wrote. Upstream invalid cases carry the bytes and nothing else, so a harness has no way to tell a decoder that refused for the right reason from one that refused for the wrong one. The name inside is a `ValueFault` member, documented in the JSON tree's own README, and a harness that does not know the name can ignore the file.

## Case names

A case name opens with what the upstream grammar fixes, then carries the source case id with each `/` turned into `_`.

| Handler | Name opens with | Type |
| --- | --- | --- |
| `uints` | `uint_{bits}` | Unsigned integer of that width. |
| `boolean` | — | A boolean. |
| `bitvector` | `bitvec_{length}` | Bit vector of that many bits. |
| `bitlist` | `bitlist_{limit}` | Bit list capped at that many bits. |
| `progressive_bitlist` | `progbitlist` | Unbounded bit list. |
| `basic_vector` | `vec_{element}_{length}` | Vector of that many basic elements. |
| `basic_progressive_list` | `proglist_{element}` | Unbounded list of basic elements. |

`{element}` is one of `bool`, `uint8`, `uint16`, `uint32`, `uint64`, `uint128`, `uint256`.

`vec_uint8_4_bytes4_nonzero` is a vector of four 8-bit integers, filled by the case `bytes4/nonzero`. The prefix is the contract a harness parses; the rest names the case in the JSON tree, so a failure here is traceable to the vector that produced it.

A fixed count of bytes is exported as a vector of 8-bit integers, since the two are one SSZ type: the same bytes, the same root, and `value.yaml` spells both as a sequence of numbers.

## Snappy

The bytes are a valid Snappy block that carries its input as a single literal, with no back-references. This repository has no Snappy dependency and takes none for a corpus of 11 KB: matching back-references would save about 6 KB across all 131 cases, at the cost of a matcher nobody would re-derive.

Every decompressor reads it. The only visible difference is that a case file is a handful of bytes longer than the SSZ it holds rather than shorter.

## What is here

| Handler | Valid | Invalid |
| --- | --- | --- |
| `basic_progressive_list` | 11 | 1 |
| `basic_vector` | 28 | 5 |
| `bitlist` | 11 | 6 |
| `bitvector` | 16 | 5 |
| `boolean` | 3 | 5 |
| `progressive_bitlist` | 8 | 3 |
| `uints` | 25 | 4 |

Those are every handler upstream ever published data for.

## What is not here

222 cases, for three reasons, each named per case in `manifest.json`.

| Cases | Why |
| --- | --- |
| 75 | The handler names one of a fixed set of structures, and this type is not among them. |
| 70 | The handler for this kind is declared upstream but was never implemented. |
| 77 | `ssz_generic` asks only whether bytes decode, and this asks something else. |

The first covers containers, progressive containers and compatible unions. `containers`, `progressive_containers` and `compatible_unions` do not encode a type in the case name; they name a structure the harness already holds as a hard-coded declaration. This suite's structures are not those, so a harness would refuse the name rather than build the type. Exporting them would hand a harness cases it cannot resolve.

The second covers bounded lists, byte lists, and vectors and progressive lists of composites. `basic_list`, `complex_list`, `complex_vector` and `complex_progressive_list` are declared in the upstream format document as *not supported yet*, and no release ever carried a case under them.

The third covers the generalized-index, proof, multiproof and illegal-declaration vectors. `ssz_generic` has no handler for any of those questions. The illegal declarations come closest — upstream does file a few of them as invalid decodes of empty bytes — but this suite states them as declarations with no bytes at all, and inventing bytes for them here would be inventing a case rather than exporting one.

Every one of those 222 cases is in the JSON tree, in the full-fidelity format `fixtures/README.md` documents. Running only this tree runs 37% of the suite.

## `manifest.json`

`formatVersion`, `specVersion` (read from the JSON tree this was exported from), `generator`, `runner`, and `sourceCaseCount`.

`exported` names each case by source `id`, `handler`, `suite` and `case`. `skipped` names each remaining case by source `id` and `reason`. Together they account for every case of the source tree exactly once.

## What a passing run proves

The same thing a run of the JSON tree proves, and no more: your implementation agrees with this one, not that either agrees with the specification. `fixtures/README.md` says what that is worth.

This tree adds one step of its own between the two — the export re-reads the JSON and rewrites it under the upstream grammar. A case name that rebuilds the wrong type would compare the wrong bytes, so `packages/testing/tests/test_ssz_generic.py` rebuilds each type from the case name a harness reads and requires the same serialization and the same root as the declaration it came from.
