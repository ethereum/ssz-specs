# Ethereum SSZ Specifications

This project provides a reference implementation of Ethereum's SSZ (Simple Serialize)
type system, serialization, and Merkleization.

## Specifications Overview

### SSZ Types and Serialization

The SSZ type system and (de)serialization live in `src/ssz/`: booleans, unsigned
integers, byte arrays, bitfields, lists, vectors, and containers.

### Progressive Types

[EIP-7916](https://eips.ethereum.org/EIPS/eip-7916) adds two collections that declare no
capacity: `ProgressiveList[type]` in `src/ssz/collections.py` and `ProgressiveBitlist` in
`src/ssz/bitfields.py`.

They serialize exactly like their bounded counterparts.
Only the hash tree root tells the shapes apart.
That root comes from `merkleize_progressive`, a spine of binary subtrees holding
1, 4, 16, 64, ... chunks:

- A short collection hashes through a shallow tree, with no padding out to a capacity.
- Every chunk keeps one position in the tree however much data follows it.
- Proofs therefore survive growth that a redefined capacity would invalidate.

The EIP's `ProgressiveByteList` is `ProgressiveList[Uint8]` here, byte for byte and root
for root. The bounded `ByteList` types exist only as a bytes-backed convenience over a
list of single bytes, and with no capacity to specialize on, a progressive analogue would
add nothing.

### Progressive Containers

[EIP-7495](https://eips.ethereum.org/EIPS/eip-7495) adds a struct whose fields keep their
tree positions across versions. `ProgressiveContainer` in `src/ssz/container.py` carries a
field layout of bits, declared as `ACTIVE_FIELDS`: a field is declared for each set bit,
and a clear bit leaves a gap that no field occupies.

The spec writes that layout as a call, `ProgressiveContainer(active_fields=[1, 0, 1])`. It
is a class attribute here, the way a vector's `LENGTH` and a list's `LIMIT` stand in for
the spec's `Vector[type, N]` and `List[type, N]`.

Fields hash into the progressive tree at the positions their bits mark, so adding or
dropping a field in a later version leaves every other field where it was. The layout is
mixed into the root, which is what keeps a dropped field distinct from a field holding
zero. Serialization is that of an ordinary container, and a gap costs no bytes.

### Compatible Unions

[EIP-8016](https://eips.ethereum.org/EIPS/eip-8016) adds a tagged union whose options all
merkleize into one tree shape. `CompatibleUnion` in `src/ssz/union.py` carries an `OPTIONS`
map from selector to type, and a value pairs the selector with the option it holds.

A field keeps one tree position across every option, so a proof about it verifies against
any option that declares it. The selector leads on the wire and is mixed into the root,
which separates options that would otherwise root alike.

Which types may share a union is decided by compatible merkleization, the rules the SSZ
spec states for when two types merkleize into one shape. They live alongside the type in
`src/ssz/union.py`, since the union is the only thing that requires them.

### Merkleization

The `hash_tree_root` dispatch and the Merkleization primitives live in
`src/ssz/merkleization.py`.

## Design Principles

1. **Clarity over Performance**: Readable reference implementations
1. **Strong Typing**: Pydantic models with full validation
1. **Test Coverage**: Extensive tests for all modules

## Development

- [Readme](https://github.com/ethereum/ssz-specs/blob/main/README.md)
- [Contributing](https://github.com/ethereum/ssz-specs/blob/main/CONTRIBUTING.md)
