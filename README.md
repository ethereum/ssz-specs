# SSZ Specs

Simple Serialize (SSZ) is a serialization and hashing scheme used by Ethereum.
This project is a reference implementation written in Python which serves as the
official specifications.

## Development

This project uses [`uv`](https://docs.astral.sh/uv/) and
[`just`](https://just.systems/).

```bash
just check  # Run code quality checks
just fix    # Run code quality fixers
just test   # Run unit tests
just fill   # Generate reference tests
```

## Tests

This project generates JSON reference tests, included in each release, that SSZ
implementations can run to ensure compliance with the specifications.

Each vector carries the value under test in the specification's JSON mapping.
Integers are strings of decimal digits, so that a 64-bit value survives a parser
that holds JSON numbers as doubles, and bitfields are hex byte strings holding
exactly the bytes they serialize to. A collection is written bare: the array or
the hex string itself, never wrapped in an object.

Alongside them the suite ships generalized-index vectors: a type, a path through
it, and the index that path names in the Merkle tree. `fixtures/README.md`, written
by each fill, documents every format.

## Releases

Each release ships the `eth-ssz-specs` package on PyPI and the reference tests on the
[releases page](https://github.com/ethereum/ssz-specs/releases), both built from
the tagged commit.

```bash
pip install eth-ssz-specs
```

```bash
TAG=v0.1.0
curl -sSLO "https://github.com/ethereum/ssz-specs/releases/download/$TAG/ssz-test-vectors-$TAG.tar.gz"
curl -sSLO "https://github.com/ethereum/ssz-specs/releases/download/$TAG/ssz-test-vectors-$TAG.tar.gz.sha256"
sha256sum --check "ssz-test-vectors-$TAG.tar.gz.sha256"
tar -xzf "ssz-test-vectors-$TAG.tar.gz"   # extracts fixtures/
```

## Native backend

The package can compute roots, decoding checks, Merkle trees and proof verification with x86-64 routines.
They are written and proved equal to the specification in Lean, then printed to assembly; `lean/README.md` explains how.

The backend is off by default.
Turn it on before importing `ssz`:

```bash
SSZ_BACKEND=native python ...
```

Or at run time:

```python
import ssz.native

ssz.native.enable()  # True when the routines run here
```

`SSZ_REQUIRE_NATIVE=1`, next to `SSZ_BACKEND=native`, makes the import fail where the routines cannot run, instead of falling back.

The routines need an x86-64 processor on Linux and a C compiler.
On first use, `cc` (or `$CC`) assembles the shipped `kernels_x86.S` into a library cached in `~/.cache/eth-ssz-specs`, or under `$XDG_CACHE_HOME` when it is set.
`SSZ_NATIVE_LIB` points to a library built elsewhere instead.
On any other platform `enable()` returns `False`, and everything runs in Python as before.

Every x86-64 processor runs the routines; nothing is configured.
At load, a proved detection routine reads `cpuid` and `xgetbv`, and each hash picks the fastest kernel the processor allows:

| processor offers | SHA-256 kernel |
|---|---|
| AVX-512 | 32 or 16 pairs at a time; the rest padded to 16, or given to SHA |
| SHA extensions | two pairs at a time, then one, for the rest |
| AVX2, without AVX-512 or SHA extensions | 8 pairs at a time |
| none of these | SSE2, which every x86-64 processor has, 4 pairs at a time |

A processor with both AVX-512 and the SHA extensions uses AVX-512 for large batches and SHA for what remains.

Calls keep their signatures, answers and errors, so downstream code such as consensus-specs changes nothing.
An input the routines do not cover is computed by the Python.

One difference is visible: a long vector or list of composite elements, decoded in native mode, holds a lazy sequence in `.data` rather than a list.
It behaves as a mutable sequence, and decodes each element the first time it is read.

## Types

### `Boolean`

A true or false value.

```python
Boolean(True)
```

### `Bit`

A zero or one value.

```python
Bit(1)
```

### `Byte`

Eight bits of opaque data.

It serializes and hashes exactly as an 8-bit unsigned integer does, and the two
merkleize compatibly. Only the JSON mapping tells them apart: opaque data is
written as a hex byte string, `"0xff"`, where a number is written as a string of
decimal digits, `"255"`.

```python
Byte(0xFF)
```

### `Uint8`

An 8-bit unsigned integer.

```python
Uint8(0xFF)
```

### `Uint16`

A 16-bit unsigned integer.

```python
Uint16(0xFFFF)
```

### `Uint32`

A 32-bit unsigned integer.

```python
Uint32(0xFFFFFFFF)
```

### `Uint64`

A 64-bit unsigned integer.

```python
Uint64(0xFFFFFFFFFFFFFFFF)
```

### `Uint128`

A 128-bit unsigned integer.

```python
Uint128(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
```

### `Uint256`

A 256-bit unsigned integer.

```python
Uint256(0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
```

### `Vector`

A fixed number of elements.

```python
class Color(Vector[Uint8]):
    LENGTH = 3


Color(data=[255, 128, 0])
```

### `List`

A variable number of elements up to a limit.

```python
class Scores(List[Uint64]):
    LIMIT = 8


Scores(data=[10, 20, 30])
```

### `ByteVector`

A fixed number of bytes.

```python
class Serial(ByteVector):
    LENGTH = 4


Serial(b"\x01\x02\x03\x04")
```

### `ByteList`

A variable number of bytes up to a limit.

```python
class Message(ByteList):
    LIMIT = 32


Message(data=b"hello")
```

### `BitVector`

A fixed number of bits.

```python
class Weekdays(BitVector):
    LENGTH = 7


Weekdays(data=[1, 0, 0, 1, 0, 1, 0])
```

### `BitList`

A variable number of bits up to a limit.

```python
class Answers(BitList):
    LIMIT = 20


Answers(data=[1, 0, 1])
```

### `ProgressiveList`

A variable number of elements, with an optional limit.

```python
class Temperatures(ProgressiveList[Uint16]):
    pass


class RecentTemperatures(ProgressiveList[Uint16]):
    LIMIT = 24


Temperatures(data=[20, 21, 19])
```

### `ProgressiveByteList`

A variable number of bytes, with an optional limit.

```python
ProgressiveByteList(data="0xdeadbeef")
```

### `ProgressiveBitList`

A variable number of bits, with an optional limit.

```python
ProgressiveBitList(data=[1, 0, 1])
```

### `Container`

A fixed set of named fields.

```python
class Point(Container):
    x: Uint64
    y: Uint64


Point(x=1, y=2)
```

### `ProgressiveContainer`

Named fields that keep their positions as the set changes.

```python
class Square(ProgressiveContainer):
    ACTIVE_FIELDS = (1, 0, 1)

    side: Uint16  # position 0
    color: Uint8  # position 2


Square(side=0x1234, color=0x42)
```

Past a handful of positions, state the width and the gaps instead:
`ACTIVE_FIELDS = active_fields(width=46, gaps=(8, 9, 10, 28))`.

### `CompatibleUnion`

A choice between options that share one tree shape.

```python
class Shape(CompatibleUnion):
    OPTIONS = {1: Square, 2: Circle}


Shape(selector=1, data=Square(side=0x1234, color=0x42))
```
