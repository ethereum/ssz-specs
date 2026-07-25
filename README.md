# SSZ Specs

Reference implementation of Ethereum's **SSZ** (Simple Serialize) type system,
serialization, and **Merkleization**, written in Python.

The specification is a faithful port of the SSZ and Merkleization logic used across the
Ethereum consensus specifications
([`ethereum/consensus-specs/ssz`](https://github.com/ethereum/consensus-specs/tree/master/ssz)).

## Overview

SSZ is the serialization and hashing scheme used throughout Ethereum consensus. This
repository implements:

- **Basic types**: `Boolean`, `Uint8`/`Uint16`/`Uint32`/`Uint64`.
- **Byte arrays**: fixed `Bytes4` … `Bytes64` and variable `ByteList`.
- **Bitfields**: `Bitvector` and `Bitlist`.
- **Composite types**: `Vector`, `List`, and `Container`.
- **Progressive types** ([EIP-7916](https://eips.ethereum.org/EIPS/eip-7916)):
  `ProgressiveList` and `ProgressiveBitlist`, which carry no capacity and hash into a
  tree that grows with the data.
- **(De)serialization**: canonical encode/decode with strict, offset-based decoding.
- **Merkleization**: `hash_tree_root`, `merkleize`, `merkleize_progressive`, and
  `mix_in_length`.

## Project Structure

```
src/ssz/
  __init__.py          # public re-exports of the SSZ types
  base.py              # strict, immutable Pydantic base models
  ssz_base.py          # abstract SSZType / SSZModel bases
  boolean.py           # Boolean
  uint.py              # Uint8/16/32/64
  byte_arrays.py       # fixed byte vectors and byte lists
  bitfields.py         # Bitvector / Bitlist / ProgressiveBitlist
  collections.py       # Vector / List / ProgressiveList
  container.py         # Container
  exceptions.py        # SSZ error hierarchy
  merkleization.py     # hash_tree_root dispatch and Merkle primitives
tests/                 # pytest unit tests mirroring the source modules
tests/fillers/         # test-vector fillers (generate JSON conformance vectors)
packages/testing/      # ssz-testing package: the vector generation infrastructure
```

## Development

This project uses [`uv`](https://docs.astral.sh/uv/) and
[`just`](https://just.systems/).

```bash
uv sync                 # Install dependencies
uv tool install just-bin  # Install the just command runner

just            # List all available recipes
just test       # Run the unit tests
just check      # Lint, format, typecheck, spellcheck, mdformat, lock-check
just fix        # Auto-fix lint, formatting, and markdown
```

- Python 3.12+ is required.
- All types are modeled with [Pydantic](https://docs.pydantic.dev/) for strict validation.

## Test vectors

Alongside the unit tests, the repository generates language-neutral JSON conformance
vectors that other SSZ implementations can replay. The fillers live under
`tests/fillers/` and the generation infrastructure is the `ssz-testing` workspace
package under `packages/testing/`.

```bash
just fill       # Generate all SSZ conformance vectors into fixtures/
```

Each vector records the type name, the SSZ `serialized` bytes, the `hash_tree_root`, and
an `_info` block with a content hash. Decode-failure vectors carry an empty root and a
`rejectionReason`. The generated tree lands under `fixtures/` (git-ignored).

## License

[MIT](LICENSE)
