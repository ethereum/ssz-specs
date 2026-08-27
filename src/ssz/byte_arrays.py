"""
SSZ byte array types.

A byte array is a contiguous sequence of bytes serialized directly to the wire.

Two flavors are defined by the SSZ spec:

- Fixed-length: exactly N bytes — the byte count is part of the type.
- Variable-length: 0 to N bytes — the byte count is recovered from the surrounding context.

Both flavors serialize as the raw bytes themselves — no length prefix, no delimiter.
"""

from collections.abc import Iterable, Sequence
from enum import Enum
from typing import IO, TYPE_CHECKING, Any, ClassVar, NoReturn, Self, override

from pydantic import Field, field_serializer, field_validator
from pydantic.annotated_handlers import GetCoreSchemaHandler
from pydantic_core import core_schema

from ssz.exceptions import (
    SSZDefinitionError,
    SSZFixedSizeError,
    SSZLengthError,
    SSZLimitError,
    SSZScopeError,
    SSZSerializationError,
    SSZTypeError,
)
from ssz.ssz_base import SSZCollection, SSZType


class _Omitted(Enum):
    """
    Marks a constructor argument that was never passed.

    - The default depends on the declared width, so no signature default can hold it.
    - Zero bytes stays a byte-count error, so the one in-domain candidate is unavailable.
    - A single-member enum is the one sentinel spelling a type checker narrows.
    """

    TOKEN = "omitted"


class ByteVector(bytes, SSZType):
    r"""
    Fixed-length SSZ byte array with exactly N bytes.

    - Inherits from bytes so the instance is usable wherever a bytes value is expected.
    - Subclasses pin the byte count by setting the class-level length.
    - Equality relates a type only to its ancestors and descendants.
    - Hashing agrees with that relation.

    The spec reads a fixed byte array as a vector of single bytes, so its default is every
    byte zero.

    For example, Bytes4 wraps four raw bytes and serializes verbatim:

        Bytes4(b"\x01\x02\x03\x04")  ->  wire bytes 01 02 03 04
    """

    LENGTH: ClassVar[int]
    """The exact number of bytes (overridden by subclasses)."""

    @staticmethod
    def _coerce_to_bytes(value: bytes | bytearray | str | Iterable[int]) -> bytes:
        """
        Coerce an input into a plain bytes object.

        Accepts:

        - bytes — handed back as it stands, being immutable already.
        - A bytes subclass or a bytearray — copied into a plain, immutable bytes object.
        - Iterables of integers in 0..255.
        - Hex strings, optionally prefixed with 0x.

        Args:
            value: The raw input to convert.

        Returns:
            The coerced bytes.

        Raises:
            TypeError: If the input type is not coercible.
            ValueError: If a hex string is malformed or an integer is out of range.
        """
        # A plain bytes object is already the answer, and a subclass is copied out below.
        if type(value) is bytes:
            return value

        match value:
            case bytes() | bytearray():
                return bytes(value)
            case str():
                return bytes.fromhex(value.removeprefix("0x"))
            case Iterable():
                return bytes(value)
            case _:
                raise TypeError(f"Cannot coerce {type(value).__name__} to bytes")

    def __new__(
        cls, value: bytes | bytearray | str | Iterable[int] | _Omitted = _Omitted.TOKEN
    ) -> Self:
        """
        Construct and validate a new byte array.

        Args:
            value: Any input coercible to bytes — bytes, bytearray, iterable of ints, or hex string.
                Omitting it gives the default value, which is every byte zero.

        Raises:
            SSZTypeError: If the subclass has not declared a length.
            SSZValueError: If the coerced byte count differs from the declared length.
            TypeError: If a value is passed that no coercion accepts.
        """
        if cls.LENGTH is None:
            raise SSZDefinitionError(cls.__name__, "LENGTH")

        # Only the total absence of an argument asks for the default:
        #
        #     Bytes4()      ->  00000000        four zero bytes
        #     Bytes4(b"")   ->  length error    zero bytes is a wrong count, not a request
        #     Bytes4(None)  ->  coercion error  a missing value passed by hand is an input
        #
        # Repeating a zero byte the declared number of times gives exactly that many, so the
        # coercion and the count check below have nothing left to settle.
        if value is _Omitted.TOKEN:
            return cls._trusted(b"\x00" * cls.LENGTH)

        coerced_bytes = cls._coerce_to_bytes(value)
        if len(coerced_bytes) != cls.LENGTH:
            raise SSZLengthError(cls.__name__, cls.LENGTH, len(coerced_bytes), unit="bytes")
        return super().__new__(cls, coerced_bytes)

    def __setattr__(self, name: str, value: Any) -> NoReturn:
        """
        Refuse to attach state to a value.

        Raises:
            SSZTypeError: Always, because a byte array is only the bytes it holds.
        """
        raise SSZTypeError(f"{type(self).__name__} is immutable")

    @classmethod
    def _trusted(cls, data: bytes) -> Self:
        """
        Wrap bytes of an already-established length, skipping every check.

        # Safety

        The byte count must follow from how the value was built, never from a caller.
        A wrong width yields an instance.
        It merkleizes to a wrong root rather than failing.

        Args:
            data: Exactly the declared number of bytes.

        Returns:
            An instance wrapping those bytes, unvalidated.
        """
        return bytes.__new__(cls, data)

    @classmethod
    def zero(cls) -> Self:
        """
        Return a new instance filled with zero bytes, which is also the default.

        A shape with no declared width has no byte count to zero.
        It reports its declaration error instead.
        """
        return cls()

    @classmethod
    @override
    def is_fixed_size(cls) -> bool:
        """Always fixed-size by definition."""
        return True

    @classmethod
    @override
    def get_byte_length(cls) -> int:
        """Return the declared byte length."""
        return cls.LENGTH

    @override
    def serialize(self, stream: IO[bytes]) -> int:
        """Write the raw bytes to a binary stream and return the number of bytes written."""
        stream.write(self)
        return len(self)

    @classmethod
    @override
    def deserialize(cls, stream: IO[bytes], scope: int) -> Self:
        """
        Read the declared number of bytes from a stream.

        Args:
            stream: Source binary stream.
            scope: Number of bytes the caller has allocated for this value.
                Must equal the declared width.

        Returns:
            A new instance wrapping the read bytes.

        Raises:
            SSZSerializationError:
                - When scope does not equal the declared width.
                - When the stream ends before delivering scope bytes.
        """
        if scope != cls.LENGTH:
            raise SSZScopeError(cls.__name__, cls.LENGTH, scope)
        serialized_bytes = stream.read(scope)
        if len(serialized_bytes) != scope:
            raise SSZScopeError(cls.__name__, scope, len(serialized_bytes))
        # The read delivered exactly the checked count, which the guard above pinned.
        return cls._trusted(serialized_bytes)

    @override
    def encode_bytes(self) -> bytes:
        """Return the SSZ-encoded bytes as a plain bytes object."""
        return bytes(self)

    @classmethod
    @override
    def decode_bytes(cls, data: bytes) -> Self:
        """Parse SSZ bytes into an instance — the constructor enforces the declared length."""
        return cls(data)

    @classmethod
    def __get_pydantic_core_schema__(
        cls, source_type: Any, handler: GetCoreSchemaHandler
    ) -> core_schema.CoreSchema:
        """
        Provide a Pydantic core schema for strict byte-array validation.

        - Already-typed instances pass through.
        - Plain bytes inputs go through length-checked validation, then get wrapped.
        - Hex string inputs (with an optional 0x prefix) go through the constructor.
        - JSON serialization converts the bytes to a 0x-prefixed hex string.
        """
        # Shared validator that runs the constructor on a verified input.
        # The constructor handles bytes, bytearray, hex strings, or iterables of ints.
        # It also enforces the declared length.
        from_input_validator = core_schema.no_info_plain_validator_function(cls)

        # Bytes path enforces the exact declared length, then wraps into a typed instance.
        bytes_path = core_schema.chain_schema(
            [
                core_schema.bytes_schema(min_length=cls.LENGTH, max_length=cls.LENGTH),
                from_input_validator,
            ]
        )

        # Hex string path routes any string through the constructor.
        # The constructor strips an optional 0x prefix, decodes hex, and length-checks.
        str_path = core_schema.chain_schema(
            [
                core_schema.str_schema(),
                from_input_validator,
            ]
        )

        # Final union accepts any branch and serializes back to a 0x-prefixed hex string:
        #
        #   - Branch 1: input is already a typed instance, pass through.
        #   - Branch 2: input is bytes that need length-checking and wrapping.
        #   - Branch 3: input is a hex string that goes through the constructor.
        return core_schema.union_schema(
            [
                core_schema.is_instance_schema(cls),
                bytes_path,
                str_path,
            ],
            serialization=core_schema.plain_serializer_function_ser_schema(
                lambda x: "0x" + x.hex()
            ),
        )

    def __repr__(self) -> str:
        """Return the official form: ClassName(hex_string)."""
        type_name = type(self).__name__
        return f"{type_name}({self.hex()})"

    def __eq__(self, other: object) -> bool:
        r"""
        Equality between two byte arrays whose types are related by inheritance.

        - One of the two types must derive from the other.
        - Nothing but a byte array may meet one at all.

        A root is declared a kind of chunk, so it is usable where a chunk is expected:

            x = b"\x11" * 32

            Root(x) == Chunk(x)    ->  True     a root is a kind of chunk
            Bytes32(x) == Root(x)  ->  refused  siblings, neither derives from the other
            Bytes32(x) == x        ->  refused  raw bytes are not a byte array at all

        Whenever this returns True the hash agrees, as every Python type must.
        A container finds a value by its hash before it compares it.
        Two related types are one value here, so no hash naming the concrete type could keep step.

        Args:
            other: The value to compare against.

        Raises:
            TypeError: If other is not a byte array, or is a sibling type rather than an
                ancestor or a descendant.
        """
        if not isinstance(other, ByteVector) or not (
            isinstance(other, type(self)) or isinstance(self, type(other))
        ):
            raise TypeError(
                f"Unsupported operand type(s) for ==: "
                f"'{type(self).__name__}' and '{type(other).__name__}'"
            )
        return bytes.__eq__(self, other)

    def __ne__(self, other: object) -> bool:
        """
        Inequality under the same relation as equality.

        Defined explicitly because the parent bytes class has a not-equal of its own that
        would bypass the type rule.

        Raises:
            TypeError: If other is not a byte array, or is a sibling type rather than an
                ancestor or a descendant.
        """
        if not isinstance(other, ByteVector) or not (
            isinstance(other, type(self)) or isinstance(self, type(other))
        ):
            raise TypeError(
                f"Unsupported operand type(s) for !=: "
                f"'{type(self).__name__}' and '{type(other).__name__}'"
            )
        return bytes.__ne__(self, other)

    # Equality calls a root and a chunk of the same bytes one value, which leaves the
    # concrete type no room in the hash.
    # Two types the comparison refuses to relate then share a bucket when their bytes agree,
    # so a lookup reaches the refusal rather than missing in silence.
    # Differing bytes give differing hashes, where absent is the right answer either way.
    __hash__ = bytes.__hash__


class ByteList(SSZCollection[int]):
    r"""
    Variable-length SSZ byte array with 0 to N bytes.

    - Subclasses pin the maximum byte count by setting the class-level limit.
    - Serialization writes the raw bytes.
    - The byte count is recovered from the wrapping context.
    - Equality relates a type only to its ancestors and descendants.
    - Hashing agrees with that relation.

    For example, a 4-byte payload under a limit of 10:

        instance.data = b"\xde\xad\xbe\xef"  ->  wire bytes de ad be ef
    """

    LIMIT: ClassVar[int]
    """Maximum number of bytes the instance may contain."""

    data: bytes = Field(default=b"")
    """
    The raw bytes stored in this list.

    The spec's default is empty, and bytes cannot be mutated.
    One shared empty value is therefore safe here, where a shared list would not be.
    """

    @field_validator("data", mode="before")
    @classmethod
    def _validate_byte_list_data(cls, value: Any) -> bytes:
        """Enforce the maximum byte count and coerce inputs into a plain bytes object."""
        # Subclasses must declare LIMIT before any instances can be validated.
        if cls.LIMIT is None:
            raise SSZDefinitionError(cls.__name__, "LIMIT")

        # Coerce the input first, then enforce the upper bound.
        coerced_bytes = ByteVector._coerce_to_bytes(value)
        if len(coerced_bytes) > cls.LIMIT:
            raise SSZLimitError(cls.__name__, cls.LIMIT, len(coerced_bytes))
        return coerced_bytes

    @field_serializer("data", when_used="json")
    def _serialize_data(self, value: bytes) -> str:
        """Serialize the raw bytes to a 0x-prefixed hex string for JSON output."""
        return "0x" + value.hex()

    def _store(self, working: bytearray) -> None:
        """
        Store mutated bytes, checking the byte count and nothing else.

        Assigning to the field would re-coerce a payload that is already bytes.

        Raises:
            SSZLimitError: When the mutation leaves more bytes than the limit allows.
        """
        self._validate_length(len(working))
        payload = bytes(working)
        # A type checker reads this field through an inherited sequence declaration, so the
        # assignment spelling is kept for it and the dictionary write for the runtime.
        if not TYPE_CHECKING:
            self.__dict__["data"] = payload
            self.__pydantic_fields_set__.add("data")
        else:  # pragma: no cover
            self.data = payload

    @override
    def __setitem__(self, index: int | slice, value: int | Sequence[int]) -> None:
        """Replace the byte or bytes at a position, revalidating the stored payload."""
        self._begin_mutation()
        working = bytearray(self.data)
        working[index] = value  # ty: ignore[invalid-assignment]
        self._store(working)

    def append(self, value: int) -> None:
        """Add one byte at the end, revalidating the stored payload."""
        self._begin_mutation()
        working = bytearray(self.data)
        working.append(value)
        self._store(working)

    def pop(self) -> int:
        """Remove and return the last byte, revalidating the stored payload."""
        self._begin_mutation()
        working = bytearray(self.data)
        last = working.pop()
        self._store(working)
        return last

    @classmethod
    @override
    def is_fixed_size(cls) -> bool:
        """Variable-size by definition — the byte count depends on the value."""
        return False

    @classmethod
    @override
    def get_byte_length(cls) -> int:
        """
        Variable-size types have no fixed byte length.

        Raises:
            SSZTypeError: Always — call this only on fixed-size types.
        """
        raise SSZFixedSizeError(cls.__name__, "byte list")

    @override
    def serialize(self, stream: IO[bytes]) -> int:
        """Write the raw bytes to a binary stream and return the number of bytes written."""
        stream.write(self.data)
        return len(self.data)

    @classmethod
    @override
    def deserialize(cls, stream: IO[bytes], scope: int) -> Self:
        """
        Read scope bytes from a stream into a new instance.

        For variable-size values, the caller computes scope from the surrounding context.

        Args:
            stream: Source binary stream.
            scope: Number of bytes belonging to this value.

        Returns:
            A new instance wrapping the read bytes.

        Raises:
            SSZSerializationError:
                - When scope is negative.
                - When the stream ends before delivering scope bytes.
            SSZValueError: When scope exceeds the declared limit.
        """
        if scope < 0:
            raise SSZSerializationError(f"{cls.__name__}: negative scope")
        if scope > cls.LIMIT:
            raise SSZLimitError(cls.__name__, cls.LIMIT, scope)
        serialized_bytes = stream.read(scope)
        if len(serialized_bytes) != scope:
            raise SSZScopeError(cls.__name__, scope, len(serialized_bytes))
        return cls(data=serialized_bytes)

    @override
    def encode_bytes(self) -> bytes:
        """Return the SSZ-encoded bytes — the raw payload, with no length prefix."""
        return self.data

    @classmethod
    @override
    def decode_bytes(cls, data: bytes) -> Self:
        """Parse SSZ bytes into an instance — the validator enforces the declared limit."""
        return cls(data=data)

    def __bytes__(self) -> bytes:
        """Return the underlying raw bytes."""
        return self.data

    def __add__(self, other: Any) -> bytes:
        """Concatenate with a bytes-like value on the right, returning plain bytes."""
        return self.data + bytes(other)

    def __radd__(self, other: Any) -> bytes:
        """Concatenate with a bytes-like value on the left, returning plain bytes."""
        return bytes(other) + self.data

    def __repr__(self) -> str:
        """Return the official form: ClassName(hex_string)."""
        type_name = type(self).__name__
        return f"{type_name}({self.data.hex()})"

    def __eq__(self, other: object) -> bool:
        """
        Equality between two byte lists whose types are related by inheritance.

        - One of the two types must derive from the other.
        - Nothing but a byte list may meet one at all.
        - Whenever this returns True the hash agrees.

        Two unrelated limits are refused even when the payloads match, because a payload
        under one limit is not the same value as under another.

        Args:
            other: The value to compare against.

        Raises:
            TypeError: If other is not a byte list, or is a sibling type rather than an
                ancestor or a descendant.
        """
        if not isinstance(other, ByteList) or not (
            isinstance(other, type(self)) or isinstance(self, type(other))
        ):
            raise TypeError(
                f"Unsupported operand type(s) for ==: "
                f"'{type(self).__name__}' and '{type(other).__name__}'"
            )
        return self.data == other.data

    def __ne__(self, other: object) -> bool:
        """
        Inequality under the same relation as equality.

        Both operators apply the one type rule.

        Raises:
            TypeError: If other is not a byte list, or is a sibling type rather than an
                ancestor or a descendant.
        """
        if not isinstance(other, ByteList) or not (
            isinstance(other, type(self)) or isinstance(self, type(other))
        ):
            raise TypeError(
                f"Unsupported operand type(s) for !=: "
                f"'{type(self).__name__}' and '{type(other).__name__}'"
            )
        return self.data != other.data

    def __hash__(self) -> int:
        """Return the hash of the payload alone, which is the one thing equality compares."""
        return hash(self.data)

    def hex(self) -> str:
        """Return the hexadecimal string representation of the underlying bytes."""
        return self.data.hex()
