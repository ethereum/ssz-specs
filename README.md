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

## Releases

Each release ships the `eth-ssz-specs` package on PyPI and the reference tests on the
[releases page](https://github.com/leanEthereum/ssz-specs/releases), both built from
the tagged commit.

```bash
pip install eth-ssz-specs
```

```bash
TAG=v0.1.0
curl -sSLO "https://github.com/leanEthereum/ssz-specs/releases/download/$TAG/ssz-test-vectors-$TAG.tar.gz"
curl -sSLO "https://github.com/leanEthereum/ssz-specs/releases/download/$TAG/ssz-test-vectors-$TAG.tar.gz.sha256"
sha256sum --check "ssz-test-vectors-$TAG.tar.gz.sha256"
tar -xzf "ssz-test-vectors-$TAG.tar.gz"   # extracts fixtures/
```

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
    ACTIVE_FIELDS = active_fields(width=3, gaps=(1,))

    side: Uint16   # position 0
    color: Uint8   # position 2

Square(side=0x1234, color=0x42)
```

### `CompatibleUnion`

A choice between options that share one tree shape.

```python
class Shape(CompatibleUnion):
    OPTIONS = {1: Square, 2: Circle}

Shape(selector=1, data=Square(side=0x1234, color=0x42))
```
