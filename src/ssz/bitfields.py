"""
SSZ bitfield types.

A bitfield is a packed sequence of booleans serialized to bytes.

Three flavors are defined by the SSZ spec, the third added by EIP-7916:

- Fixed-length: exactly N bits encoded in ceil(N / 8) bytes.
- Variable-length: 0 to N bits encoded with a trailing delimiter bit that marks the end.
- Progressive: any number of bits, encoded exactly like the variable-length flavor.

All three flavors pack bits little-endian within each byte.
Bit i of the input lands in byte i // 8 at position i % 8.
"""

import math
from collections.abc import Sequence
from typing import (
    IO,
    Any,
    ClassVar,
    Self,
    override,
)

from pydantic import Field, field_validator

from ssz.boolean import Boolean
from ssz.exceptions import (
    SSZDefinitionError,
    SSZFixedSizeError,
    SSZLengthError,
    SSZLimitError,
    SSZScopeError,
    SSZSerializationError,
    SSZTypeMismatch,
    SSZValueError,
)
from ssz.ssz_base import SSZCollection


class BitVector(SSZCollection[Boolean]):
    """
    Fixed-length SSZ bitfield with exactly N bits.

    - Subclasses pin the bit count by setting the class-level length.
    - Serialization packs bits little-endian into ceil(N / 8) bytes.
    - Trailing bits in the last byte are zero when N is not a multiple of 8.

    For example, [1, 1, 1, 1, 1] (5 bits, all set) encodes to a single byte.
    list[i] lands at bit i, where bit 0 is the LSB (rightmost in the byte):

        bit position:  7 6 5 4 3 2 1 0
        byte 0:        0 0 0 1 1 1 1 1   ->  0b00011111

    Bits 5, 6, 7 are trailing zeros — only the lowest 5 hold data.

    Built from nothing, a bitvector holds every bit clear.
    """

    LENGTH: ClassVar[int]
    """Number of bits in the vector."""

    data: Sequence[Boolean] = Field(default_factory=list)
    """
    The bits, in position order.

    - Any iterable of bool-like values is accepted on input, lists and tuples included.
    - Stored as a list once validated.
    - Indexed writes and assignment to this attribute both validate every bit.
    - Writing into the sequence in place skips validation entirely.
    """

    @classmethod
    def __pydantic_init_subclass__(cls, **kwargs: Any) -> None:
        """Give the bits their default, which is every bit clear."""
        super().__pydantic_init_subclass__(**kwargs)

        # A shape that never declared its bit count keeps its inherited default.
        # The missing declaration is rejected when a value is validated.
        if cls.LENGTH is None:
            return

        length, shared = cls.LENGTH, Boolean(False)
        # One shared boolean fills every position.
        # - A boolean cannot be mutated, so no bit can alias another.
        # - A vector of composite elements cannot take this shortcut.
        cls.model_fields["data"].default_factory = lambda: [shared] * length
        cls.model_rebuild(force=True)

    @override
    def _validate_element(self, value: Any) -> Boolean:
        """Wrap one incoming bit in Boolean, exactly as construction does."""
        return Boolean(value)

    @field_validator("data", mode="before")
    @classmethod
    def _coerce_and_validate(cls, bits_input: Any) -> list[Boolean]:
        """Enforce the exact bit count and coerce inputs into booleans."""
        # Subclasses must declare LENGTH before any instances can be validated.
        if cls.LENGTH is None:
            raise SSZDefinitionError(cls.__name__, "LENGTH")

        # Materialize generic iterables into a tuple so the length check works.
        if not isinstance(bits_input, (list, tuple)):
            bits_input = tuple(bits_input)

        # Fixed-length type: the input must contain exactly LENGTH elements.
        if len(bits_input) != cls.LENGTH:
            raise SSZLengthError(cls.__name__, cls.LENGTH, len(bits_input))

        # Each value is wrapped as a bit, which refuses anything outside 0 and 1.
        #
        # One already of exactly that class is the shared value for its bit.
        # Wrapping it again would hand back the object it is.
        # A named spelling is still converted, the test being on the exact class.
        return [bit if type(bit) is Boolean else Boolean(bit) for bit in bits_input]

    @classmethod
    @override
    def is_fixed_size(cls) -> bool:
        """Always fixed-size by definition."""
        return True

    @classmethod
    @override
    def get_byte_length(cls) -> int:
        """Return the number of bytes needed to pack the bits."""
        return math.ceil(cls.LENGTH / 8)

    @override
    def serialize(self, stream: IO[bytes]) -> int:
        """Write SSZ bytes to a binary stream."""
        encoded_data = self.encode_bytes()
        stream.write(encoded_data)
        return len(encoded_data)

    @classmethod
    @override
    def deserialize(cls, stream: IO[bytes], scope: int) -> Self:
        """Read SSZ bytes from a stream and return an instance."""
        expected_byte_count = cls.get_byte_length()
        if scope != expected_byte_count:
            raise SSZScopeError(cls.__name__, expected_byte_count, scope)
        serialized_bytes = stream.read(scope)
        if len(serialized_bytes) != scope:
            raise SSZScopeError(cls.__name__, scope, len(serialized_bytes))
        return cls.decode_bytes(serialized_bytes)

    @override
    def encode_bytes(self) -> bytes:
        """
        Encode the bitfield to SSZ bytes.

        Bits are packed little-endian within each byte.
        Bit i of the input lands in byte i // 8 at position i % 8.

        Returns:
            ceil(N / 8) bytes containing the packed bits.
        """
        # Each bit is set in place, in a buffer already the width of the result.
        #
        # Accumulating one wide integer instead grows that integer with the data.
        # Every addition then costs more than the one before it.
        # Packing a long bitfield that way is quadratic in its bit count.
        packed = bytearray(self.get_byte_length())
        # Bit i lives in byte i // 8, at position i % 8 counted from the low end.
        for position, bit in enumerate(self.data):
            if bit:
                packed[position >> 3] |= 1 << (position & 7)
        return bytes(packed)

    @classmethod
    @override
    def decode_bytes(cls, data: bytes) -> Self:
        """
        Decode SSZ bytes into a bitfield.

        Input must be exactly ceil(N / 8) bytes.
        Fixed-length bitfields carry no delimiter — the byte count alone is enough to recover N.

        Args:
            data: SSZ-encoded bytes with the packed bits.

        Returns:
            A bitfield instance with N bits read from the input.

        Raises:
            SSZValueError: If the input length does not match the expected byte count.
            SSZValueError: If any padding bit above the last data bit is set.
        """
        # Reject inputs whose byte count does not match the expected size.
        expected_byte_count = cls.get_byte_length()
        if len(data) != expected_byte_count:
            raise SSZValueError(
                f"{cls.__name__}: expected {expected_byte_count} bytes, got {len(data)}"
            )

        # When the bit count is not a multiple of 8, the last byte holds padding
        # bits above the highest data bit.
        # SSZ requires those padding bits to be zero so the encoding is canonical.
        # Without this check, 0b00011111 and 0b11111111 both decode to a 5-bit
        # vector of all ones.
        if trailing_bit_count := cls.LENGTH % 8:
            if data[-1] >> trailing_bit_count:
                raise SSZValueError(
                    f"{cls.__name__}: non-zero padding bits in final byte {data[-1]:#04x}"
                )

        # Every byte is unpacked whole, and the bits past the wanted count dropped.
        # Only the final byte holds fewer than eight of them, so at most seven go.
        #
        # The two shared values are bound once, not built per bit.
        # That is what keeps reading a wide bitfield off the wire cheap.
        #
        # Example: two bytes holding nine declared bits.
        #
        #     data     :  0b00000101   0b00000001
        #     byte 0   ->  1, 0, 1, 0, 0, 0, 0, 0
        #     byte 1   ->  1, 0, 0, 0, 0, 0, 0, 0
        #     declared ->  [1, 0, 1, 0, 0, 0, 0, 0, 1]   the surplus seven dropped
        false, true = Boolean(False), Boolean(True)
        bits = [true if byte >> position & 1 else false for byte in data for position in range(8)]
        del bits[cls.LENGTH :]
        return cls(data=bits)


class _SSZBitList(SSZCollection[Boolean]):
    """
    Shared behavior for the two delimited SSZ bitfield shapes.

    The bounded bitlist and the progressive bitlist both build on this base:

    - A bounded bitlist caps its bit count at a declared limit.
    - A progressive bitlist accepts any bit count.

    The base carries the bit field, and each shape carries its own count rule.

    Both encode identically.
    Data bits pack little-endian, then one delimiter bit closes the sequence.

    They differ in exactly two places:

    - The bit-count rule, applied on construction and again on decode.
    - The Merkle tree shape, which lives in the merkleization module.
    """

    data: Sequence[Boolean] = Field(default_factory=list)
    """
    The bits, in position order.

    - Any iterable of bool-like values is accepted on input, lists and tuples included.
    - Stored as a list once validated.
    - Indexed writes and assignment to this attribute both validate every bit.
    - Writing into the sequence in place skips validation entirely.
    """

    @classmethod
    def _reject_excess_bits(cls, count: int) -> None:
        """
        Reject a bit count the type cannot hold.

        A progressive bitlist has no capacity, so it rejects nothing.
        The bounded bitlist overrides this with its capacity check.
        """

    @override
    def _validate_element(self, value: Any) -> Boolean:
        """Wrap one incoming bit in Boolean, exactly as construction does."""
        return Boolean(value)

    def append(self, value: Boolean) -> None:
        """Add one bit at the end, validating it and the resulting length."""
        self._begin_mutation()
        element = self._validate_element(value)
        self._validate_length(len(self.data) + 1)
        self._mutable_data.append(element)

    def pop(self) -> Boolean:
        """
        Remove and return the last bit.

        - Removing one can never breach a capacity.
        - No shape offering this declares a fixed bit count.
        - So the resulting length has nothing left to check.

        Raises:
            IndexError: If the bitfield is empty.
        """
        self._begin_mutation()
        return self._mutable_data.pop()

    def __add__(self, other: Any) -> Self:
        """
        Concatenate with another bit sequence and return a new instance.

        The left operand decides the resulting type, whatever the right one is:

        - Two bitlists of different capacities concatenate into the left one's type.
        - A bounded and a progressive bitlist do too, and merkleize as that type.

        The result is built through the constructor, so every bit is wrapped there.
        A bounded bitlist therefore still rejects a concatenation that overflows it.
        """
        match other:
            case _SSZBitList():
                new_data = (*self.data, *other.data)
            case list() | tuple():
                new_data = (*self.data, *other)
            case _:
                return NotImplemented
        return type(self)(data=new_data)

    @classmethod
    @override
    def is_fixed_size(cls) -> bool:
        """Variable-size by definition — the bit count varies from one instance to the next."""
        return False

    @classmethod
    @override
    def get_byte_length(cls) -> int:
        """
        Variable-size types have no fixed byte length.

        Raises:
            SSZTypeError: Always — call this only on fixed-size types.
        """
        raise SSZFixedSizeError(cls.__name__, "bitlist")

    @override
    def serialize(self, stream: IO[bytes]) -> int:
        """Write SSZ bytes to a binary stream."""
        encoded_data = self.encode_bytes()
        stream.write(encoded_data)
        return len(encoded_data)

    @classmethod
    @override
    def deserialize(cls, stream: IO[bytes], scope: int) -> Self:
        """Read SSZ bytes from a stream and return an instance."""
        serialized_bytes = stream.read(scope)
        if len(serialized_bytes) != scope:
            raise SSZScopeError(cls.__name__, scope, len(serialized_bytes))
        return cls.decode_bytes(serialized_bytes)

    @override
    def encode_bytes(self) -> bytes:
        """
        Encode the bitlist to SSZ bytes with a trailing delimiter.

        # Overview

        Data bits are packed little-endian within each byte.
        A single 1 bit is placed immediately after the last data bit.
        The trailing bit is what lets the decoder recover the original count.

        # Delimiter

        SSZ encodes bitlists as raw bytes with no length prefix.
        Without a marker, [1, 0] and [1, 0, 0, 0, 0, 0, 0, 0] would share the byte 0x01.
        A trailing 1 bit is the smallest sentinel that disambiguates them.

        # Layout

            bits = [1, 0, 1]   ->  byte 0:  0 0 0 0 [1] 1 0 1   (delimiter at bit 3)

            bits = [1] * 8     ->  byte 0:  1 1 1 1 1 1 1 1
                                   byte 1:  0 0 0 0 0 0 0 [1]   (delimiter spills)

        Returns:
            SSZ bytes containing the data bits followed by the delimiter.
        """
        # The encoding carries one bit more than the data: the delimiter past its end.
        # It therefore takes the bytes that many bits need.
        #
        # An empty bitlist is the same rule with no data at all.
        # Its encoding is the single byte 0x01.
        num_bits = len(self.data)
        # Each bit is set in place, in a buffer already the width of the result.
        #
        # Accumulating one wide integer instead grows that integer with the data.
        # Every addition then costs more than the one before it.
        # Packing a long bitfield that way is quadratic in its bit count.
        packed = bytearray((num_bits + 8) // 8)
        # Bit i lives in byte i // 8, at position i % 8 counted from the low end.
        for position, bit in enumerate(self.data):
            if bit:
                packed[position >> 3] |= 1 << (position & 7)
        # The delimiter closes the sequence at the position one past the last data bit.
        packed[num_bits >> 3] |= 1 << (num_bits & 7)
        return bytes(packed)

    @classmethod
    @override
    def decode_bytes(cls, data: bytes) -> Self:
        """
        Decode SSZ bytes into a bitlist by locating the delimiter bit.

        # Overview

        - The highest set bit in the input is the delimiter, and it sits in the final byte.
        - Bits below it are data.
        - The rest of that final byte is zero padding, seven bits of it at most.
        - Whole zero bytes past the delimiter byte are refused, so a value has one encoding.
        - Empty input is invalid, the empty bitlist still encoding as one byte, 0x01.

        # Integer interpretation

        Reading the byte stream as a little-endian integer aligns bits and bytes perfectly:

            byte 0 bit j  ->  integer bit j
            byte 1 bit j  ->  integer bit (8 + j)
            byte k bit j  ->  integer bit (8 * k + j)

        For example, the two bytes 0b00000101 and 0b00000010:

            read as one integer  =  0b1000000101

            byte 0 bit 0 (=1)  ->  integer bit 0
            byte 0 bit 2 (=1)  ->  integer bit 2
            byte 1 bit 1 (=1)  ->  integer bit 9      (= 8 * 1 + 1)

        The highest set bit of the integer is exactly the delimiter position.

        Args:
            data: SSZ-encoded bytes containing data bits followed by a single 1 delimiter.

        Returns:
            A bitlist instance with the recovered data bits.

        Raises:
            SSZSerializationError: If the input is empty, holds no 1 bits, or carries zero
                bytes past the one holding the delimiter.
            SSZLimitError: If the recovered bit count exceeds a declared capacity.
        """
        # Phase 1: reject empty input.
        #
        # The empty bitlist still encodes to one byte (0x01).
        if len(data) == 0:
            raise SSZSerializationError(f"{cls.__name__}: cannot decode empty bytes")

        # Phase 2: locate the delimiter, and require it to sit in the final byte.
        #
        # Read as one little-endian integer, the input holds every bit at its stream position.
        # Its highest set bit is therefore the delimiter.
        #
        # Example: the single byte 0b00001101, the encoding of the three bits [1, 0, 1].
        #
        #     bit position :  7 6 5 4  3  2 1 0
        #     byte 0       :  0 0 0 0 [1] 1 0 1
        #                              ^ the delimiter, at position 3, so three data bits
        #
        # Example: the bytes 0b11111111 and 0b00000001, the encoding of eight set bits.
        # Eight data bits fill the first byte whole, so the delimiter spills to position 8.
        packed_integer = int.from_bytes(data, "little")
        if packed_integer == 0:
            raise SSZSerializationError(f"{cls.__name__}: no delimiter bit found")
        delimiter_pos = packed_integer.bit_length() - 1

        # The delimiter must sit in the final byte of the input.
        # Reading the stream as one integer silently drops trailing zero bytes.
        # So a canonical encoding and one with extra zero bytes decode the same.
        # Rejecting the padded form keeps a single valid encoding per value.
        if delimiter_pos // 8 != len(data) - 1:
            raise SSZSerializationError(
                f"{cls.__name__}: non-canonical trailing zero bytes after delimiter"
            )

        # Phase 3: enforce the size limit, then extract the data bits below the delimiter.
        #
        # The delimiter position equals the data bit count.
        # Everything from it upward is dropped, padding included.
        #
        # Example: the single byte 0b00001101, its delimiter at position 3.
        #
        #   byte 0  ->  1, 0, 1, 1, 0, 0, 0, 0
        #                        ^ the delimiter, and the first bit dropped
        #
        # Recovered bits: [1, 0, 1]
        num_bits = delimiter_pos
        # Checked before the bits are built, so an over-capacity payload is refused cheaply.
        cls._reject_excess_bits(num_bits)

        # - Every byte is unpacked whole, then the bits past the wanted count dropped.
        # - One to eight go, the delimiter always among them.
        # - The two shared values are bound once, not built per bit.
        false, true = Boolean(False), Boolean(True)
        bits = [true if byte >> position & 1 else false for byte in data for position in range(8)]
        del bits[num_bits:]
        return cls(data=bits)


class BitList(_SSZBitList):
    """
    Variable-length SSZ bitfield with 0 to N bits.

    - Subclasses pin the maximum bit count by setting the class-level limit.
    - Serialization packs data bits little-endian, then appends a single 1 bit as a delimiter.
    - The delimiter is what lets the decoder recover the original bit count.

    For example, [1, 0, 1] (3 data bits) encodes to a single byte.

    list[i] lands at bit i, where bit 0 is the LSB (rightmost in the byte):

        bit position:  7 6 5 4  3  2 1 0
        byte 0:        0 0 0 0 [1] 1 0 1   ->  0b00001101   (bracketed bit is the delimiter)

    Without the delimiter, two different lists would collide:

        [1, 0, 1]                ->  0b00000101
        [1, 0, 1, 0, 0, 0, 0, 0] ->  0b00000101
    """

    LIMIT: ClassVar[int]
    """Maximum number of bits allowed."""

    @field_validator("data", mode="before")
    @classmethod
    def _coerce_and_validate(cls, bits_input: Any) -> list[Boolean]:
        """Enforce the maximum bit count and coerce inputs into booleans."""
        # Subclasses must declare LIMIT before any instances can be validated.
        if cls.LIMIT is None:
            raise SSZDefinitionError(cls.__name__, "LIMIT")

        # Accept the natural input shapes:
        #
        #   - list or tuple    pass through directly.
        #   - other iterables  materialize into a list so the length is known.
        #   - str or bytes     rejected — iterable, but the elements are not booleans.
        if isinstance(bits_input, (list, tuple)):
            elements = bits_input
        elif hasattr(bits_input, "__iter__") and not isinstance(bits_input, (str, bytes)):
            elements = list(bits_input)
        else:
            raise SSZTypeMismatch("iterable", type(bits_input))

        # Variable-length type: any count is fine, up to LIMIT.
        if len(elements) > cls.LIMIT:
            raise SSZLimitError(cls.__name__, cls.LIMIT, len(elements))

        # Each value is wrapped as a bit, which refuses anything outside 0 and 1.
        #
        # One already of exactly that class is the shared value for its bit.
        # Wrapping it again would hand back the object it is.
        # A named spelling is still converted, the test being on the exact class.
        return [bit if type(bit) is Boolean else Boolean(bit) for bit in elements]

    @classmethod
    @override
    def _reject_excess_bits(cls, count: int) -> None:
        """
        Reject a count above the declared capacity.

        Raises:
            SSZValueError: When the count exceeds the declared capacity.
        """
        if count > cls.LIMIT:
            raise SSZLimitError(cls.__name__, cls.LIMIT, count)


class ProgressiveBitList(_SSZBitList):
    """
    Variable-length SSZ bitfield with no capacity, per EIP-7916.

    Any number of bits, packed and delimited like a bounded bitlist:

        [1, 0, 1]  ->  byte 0:  0 0 0 0 [1] 1 0 1   ->  0b00001101

    So the two encode to the same bytes, and only their Merkle trees differ.
    A bounded bitlist pads its tree to the depth its limit needs.
    Ten bits under a 2048-bit limit still hash through the depth 2048 bits need.
    This shape grows its tree with the data instead:

    - A short bitlist hashes through a shallow tree.
    - A bit keeps its position however many bits follow it, so proofs survive growth.

    The merkleization module builds that tree.

    Nothing is declared to use the type, so it is instantiated directly:

        ProgressiveBitList(data=[1, 0, 1])
    """

    @field_validator("data", mode="before")
    @classmethod
    def _coerce_and_validate(cls, bits_input: Any) -> list[Boolean]:
        """Coerce inputs into booleans, with no count rule to apply."""
        # The accepted input shapes are the ones the bounded bitlist takes, listed there.
        # No capacity check follows, because every count this shape holds is valid.
        if isinstance(bits_input, (list, tuple)):
            elements = bits_input
        elif hasattr(bits_input, "__iter__") and not isinstance(bits_input, (str, bytes)):
            elements = list(bits_input)
        else:
            raise SSZTypeMismatch("iterable", type(bits_input))

        # Each value is wrapped as a bit, which refuses anything outside 0 and 1.
        #
        # One already of exactly that class is the shared value for its bit.
        # Wrapping it again would hand back the object it is.
        # A named spelling is still converted, the test being on the exact class.
        return [bit if type(bit) is Boolean else Boolean(bit) for bit in elements]
