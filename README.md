# SSZ Specs

Simple Serialize (SSZ) is a serialization and hashing scheme used by Ethereum.
This project is a reference implementation written in Python which serves as the
official specifications.

A type states a shape. A value of that shape serializes to bytes, reads back
from them, and has a 32-byte root.

```python
from ssz import Container, Uint8, Uint64


class Vote(Container):
    slot: Uint64
    choice: Uint8


vote = Vote(slot=3, choice=1)

# Each field at its own width, little-endian, nothing between them.
encoded = vote.encode_bytes()
assert encoded.hex() == "030000000000000001"
assert Vote.decode_bytes(encoded) == vote

# The root is the two fields, each padded to a 32-byte chunk, hashed together.
root = vote.hash_tree_root()
assert root.hex() == "5b0f47b11478610c5abcbc912b34ac5f7f5740b6d8b27169b1eb2aea9f1c909c"
```

## Types

Every snippet below runs against these imports, in page order: the union at the
end reuses a type declared above it.

```python
from ssz import (
    Bit,
    BitList,
    BitVector,
    Boolean,
    Byte,
    ByteList,
    ByteVector,
    CompatibleUnion,
    Container,
    List,
    ProgressiveBitList,
    ProgressiveContainer,
    ProgressiveList,
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Uint128,
    Uint256,
    Vector,
)
```

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

A variable number of elements with no limit.

```python
class Temperatures(ProgressiveList[Uint16]):
    pass


Temperatures(data=[20, 21, 19])
```

### `ProgressiveBitList`

A variable number of bits with no limit.

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

Only the positions both options set have to agree. `Square` and `Circle` share
position 2, holding `color` in each; the position either one sets alone is a
zero leaf in the other.

```python
class Circle(ProgressiveContainer):
    ACTIVE_FIELDS = (0, 1, 1)

    radius: Uint16  # position 1
    color: Uint8  # position 2


class Shape(CompatibleUnion):
    OPTIONS = {1: Square, 2: Circle}


Shape(selector=1, data=Square(side=0x1234, color=0x42))
```

## Installation

```bash
pip install eth-ssz-specs
```

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

## Releases

Each release ships the `eth-ssz-specs` package on PyPI and the reference tests on the
[releases page](https://github.com/ethereum/ssz-specs/releases), both built from
the tagged commit.

```bash
TAG=v0.1.0
curl -sSLO "https://github.com/ethereum/ssz-specs/releases/download/$TAG/ssz-test-vectors-$TAG.tar.gz"
curl -sSLO "https://github.com/ethereum/ssz-specs/releases/download/$TAG/ssz-test-vectors-$TAG.tar.gz.sha256"
sha256sum --check "ssz-test-vectors-$TAG.tar.gz.sha256"
tar -xzf "ssz-test-vectors-$TAG.tar.gz"   # extracts fixtures/
```
