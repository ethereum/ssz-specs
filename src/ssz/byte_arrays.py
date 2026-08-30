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
from typing import IO, Any, ClassVar, NoReturn, Self, cast, overload, override

from pydantic import Field, field_serializer, field_validator
from pydantic.annotated_handlers import GetCoreSchemaHandler
from pydantic_core import core_schema

from ssz.base import wrapping_schema
from ssz.exceptions import SSZTypeError, SSZValueError, TypeFault, ValueFault
from ssz.ssz_base import SSZCollection, SSZType


class _Omitted(Enum):
    """
    Marks a constructor argument that was never passed.

    - The default depends on the declared width, so no signature default can hold it.
    - Zero bytes stays a byte-count error, so the one in-domain candidate is unavailable.
    - A single-member enum is the one sentinel spelling a type checker narrows.
    """

    TOKEN = "omitted"


def _coerced_bytes(type_name: str, value: Any) -> bytes:
    r"""
    Read one constructor input as the byte string it stands for.

    Both shapes below accept the same spellings, so both read their input through here:

        b"\x01\x02"     bytes and bytearray, taken as they are
        "0x0102"        hex digits, the prefix optional
        [1, 2]          any other iterable of byte values

    Args:
        type_name: The shape doing the reading, for the refusal to name.
        value: Whatever the caller passed.

    Returns:
        The bytes the input stands for, of whatever length it turned out to be.

    Raises:
        SSZTypeError: When no spelling above accepts the input.
        SSZValueError: When a string holds something other than hex digits.
    """
    # A plain bytes object is already the answer, and a subclass is copied out below.
    if type(value) is bytes:
        return value
    match value:
        case bytes() | bytearray():
            return bytes(value)
        case str():
            try:
                return bytes.fromhex(value.removeprefix("0x"))
            except ValueError as not_hex:
                raise SSZValueError(ValueFault.NOT_HEX, type=type_name) from not_hex
        case Iterable():
            return bytes(value)
        case _:
            raise SSZTypeError(TypeFault.WRONG_TYPE, expected="bytes", got=type(value).__name__)


class ByteVector(bytes, SSZType):
    """Fixed-length SSZ byte array with exactly N bytes."""

    LENGTH: ClassVar[int | None]
    """The exact number of bytes (overridden by subclasses)."""

    UNIT = "bytes"

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
            SSZTypeError: If a value is passed that no coercion accepts.
            SSZValueError: If the coerced byte count differs from the declared length.
        """
        if cls.LENGTH is None:
            raise SSZTypeError(TypeFault.UNDECLARED, type=cls.__name__, requirement="LENGTH")

        # Only the total absence of an argument asks for the default:
        #
        #     Bytes4()      ->  00000000        four zero bytes
        #     Bytes4(b"")   ->  length error    zero bytes is a wrong count, not a request
        #     Bytes4(None)  ->  coercion error  a missing value passed by hand is an input
        if value is _Omitted.TOKEN:
            return cls._trusted(b"\x00" * cls.LENGTH)

        coerced_bytes = _coerced_bytes(cls.__name__, value)
        if len(coerced_bytes) != cls.LENGTH:
            raise SSZValueError(
                ValueFault.COUNT,
                type=cls.__name__,
                expected=cls.LENGTH,
                actual=len(coerced_bytes),
                unit=cls.UNIT,
            )

        return super().__new__(cls, coerced_bytes)

    def __setattr__(self, name: str, value: Any) -> NoReturn:
        """
        Refuse to attach state to a value.

        Raises:
            SSZTypeError: Always, because a byte array is only the bytes it holds.
        """
        raise SSZTypeError(TypeFault.IMMUTABLE, type=type(self).__name__)

    @classmethod
    def _trusted(cls, data: bytes) -> Self:
        """
        Wrap bytes of an already-established length, skipping every check.

        This is package-internal.

        Every caller inside the package states, where it calls, what established the width:

        - a digest is 32 bytes by construction,
        - a fixed-width conversion is the width it was asked for,
        - anything else is pinned by a guard directly above.

        A caller outside that contract gets an instance whose width contradicts its own type.

        Nothing downstream reads the width again, so the contradiction is never reported.

        Args:
            data: Exactly the declared number of bytes.

        Returns:
            An instance wrapping those bytes, unvalidated.
        """
        return bytes.__new__(cls, data)

    @classmethod
    def zero(cls) -> Self:
        """Return a new instance filled with zero bytes, which is also the default."""
        return cls()

    @classmethod
    @override
    def fixed_size(cls) -> int:
        """The declared byte count, which is the width by definition."""
        return cls.declared_length()

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
            SSZValueError:
                - When scope does not equal the declared width.
                - When the stream ends before delivering scope bytes.
        """
        length = cls.declared_length()
        if scope != length:
            raise SSZValueError(ValueFault.SCOPE, type=cls.__name__, expected=length, actual=scope)
        serialized_bytes = stream.read(scope)
        if len(serialized_bytes) != scope:
            raise SSZValueError(
                ValueFault.TRUNCATED,
                type=cls.__name__,
                expected=scope,
                actual=len(serialized_bytes),
            )
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
        """Provide a Pydantic core schema for strict byte-array validation."""
        return wrapping_schema(
            cls,
            core_schema.bytes_schema(min_length=cls.LENGTH, max_length=cls.LENGTH),
            core_schema.str_schema(),
            to_json=lambda instance: "0x" + instance.hex(),
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

        Args:
            other: The value to compare against.

        Raises:
            TypeError:
                - If other is not a byte array,
                - If other is a sibling type rather than an ancestor or a descendant.
        """
        # An exact type match answers most calls without consulting the abstract base.
        # The base test guards the other branch, which bytes and object would pass.
        if not (
            isinstance(other, type(self))
            or (isinstance(other, ByteVector) and isinstance(self, type(other)))
        ):
            raise TypeError(
                "Unsupported operand type(s) for ==: "
                + f"'{type(self).__name__}' and '{type(other).__name__}'"
            )
        return bytes.__eq__(self, other)

    def __ne__(self, other: object) -> bool:
        """
        Inequality under the same relation as equality.

        Raises:
            TypeError:
                - If other is not a byte array,
                - If other is a sibling type rather than an ancestor or a descendant.
        """
        if not (
            isinstance(other, type(self))
            or (isinstance(other, ByteVector) and isinstance(self, type(other)))
        ):
            raise TypeError(
                "Unsupported operand type(s) for !=: "
                + f"'{type(self).__name__}' and '{type(other).__name__}'"
            )
        return bytes.__ne__(self, other)

    # Equality calls a root and a chunk of the same bytes one value, so only the bytes hash.
    __hash__ = bytes.__hash__


class ByteList(SSZCollection[int]):
    r"""Variable-length SSZ byte array with 0 to N bytes."""

    LIMIT: ClassVar[int | None]
    """Maximum number of bytes the instance may contain."""

    UNIT = "bytes"

    data: bytes = Field(default=b"")
    """
    The raw bytes stored in this list.

    The spec's default is empty, and bytes cannot be mutated.
    One shared empty value is therefore safe here, where a shared list would not be.
    """

    @field_validator("data", mode="before")
    @classmethod
    def _validate_byte_list_data(cls, value: Any) -> bytes:
        """
        Enforce the maximum byte count and coerce inputs into a plain bytes object.

        Raises:
            SSZTypeError: When the limit was never declared, or no coercion accepts the input.
            SSZValueError: When the coerced byte count exceeds the declared limit.
        """
        # Subclasses must declare LIMIT before any instances can be validated.
        if cls.LIMIT is None:
            raise SSZTypeError(TypeFault.UNDECLARED, type=cls.__name__, requirement="LIMIT")

        # Coerce the input first, then enforce the upper bound.
        coerced_bytes = _coerced_bytes(cls.__name__, value)
        if len(coerced_bytes) > cls.LIMIT:
            raise SSZValueError(
                ValueFault.LIMIT,
                type=cls.__name__,
                limit=cls.LIMIT,
                actual=len(coerced_bytes),
                unit=cls.UNIT,
            )
        return coerced_bytes

    @field_serializer("data", when_used="json")
    def _serialize_data(self, value: bytes) -> str:
        """Serialize the raw bytes to a 0x-prefixed hex string for JSON output."""
        return "0x" + value.hex()

    def _store(self, working: bytearray) -> None:
        """
        Store mutated bytes, checking the byte count and nothing else.

        The field validates on assignment, so the entry is written directly and marked set.

        Raises:
            SSZValueError: When the mutation leaves more bytes than the limit allows.
        """
        self._validate_length(len(working))
        self.__dict__["data"] = bytes(working)
        self.__pydantic_fields_set__.add("data")

    @overload
    def __setitem__(self, index: int, value: int) -> None: ...
    @overload
    def __setitem__(self, index: slice, value: Sequence[int]) -> None: ...

    @override
    def __setitem__(self, index: int | slice, value: int | Sequence[int]) -> None:
        """Replace the byte or bytes at a position, revalidating the stored payload."""
        self._begin_mutation()
        working = bytearray(self.data)
        # Narrowing the position does not narrow the value, so each branch says which it holds.
        if isinstance(index, slice):
            working[index] = cast("Sequence[int]", value)
        else:
            working[index] = cast("int", value)
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

    KIND = "byte list"

    @classmethod
    @override
    def fixed_size(cls) -> None:
        """No width by definition — the byte count depends on the value."""
        return None

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
            SSZValueError:
                - When scope is negative.
                - When scope exceeds the declared limit.
                - When the stream ends before delivering scope bytes.
        """
        if scope < 0:
            raise SSZValueError(ValueFault.SCOPE_NEGATIVE, scope=scope)
        limit = cls.declared_limit()
        if scope > limit:
            raise SSZValueError(
                ValueFault.LIMIT, type=cls.__name__, limit=limit, actual=scope, unit=cls.UNIT
            )
        serialized_bytes = stream.read(scope)
        if len(serialized_bytes) != scope:
            raise SSZValueError(
                ValueFault.TRUNCATED,
                type=cls.__name__,
                expected=scope,
                actual=len(serialized_bytes),
            )
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

        Args:
            other: The value to compare against.

        Raises:
            TypeError:
                - If other is not a byte list,
                - If other is a sibling type rather than an ancestor or a descendant.
        """
        # An exact type match answers most calls without consulting the abstract base.
        # The base test guards the other branch, which object would pass.
        if not (
            isinstance(other, type(self))
            or (isinstance(other, ByteList) and isinstance(self, type(other)))
        ):
            raise TypeError(
                "Unsupported operand type(s) for ==: "
                + f"'{type(self).__name__}' and '{type(other).__name__}'"
            )
        return self.data == other.data

    def __ne__(self, other: object) -> bool:
        """
        Inequality under the same relation as equality.

        Both operators apply the one type rule.

        Raises:
            TypeError:
                - If other is not a byte list,
                - If other is a sibling type rather than an ancestor or a descendant.
        """
        if not (
            isinstance(other, type(self))
            or (isinstance(other, ByteList) and isinstance(self, type(other)))
        ):
            raise TypeError(
                "Unsupported operand type(s) for !=: "
                + f"'{type(self).__name__}' and '{type(other).__name__}'"
            )
        return self.data != other.data

    def __hash__(self) -> int:
        """Return the hash of the payload alone, which is the one thing equality compares."""
        return hash(self.data)

    def hex(self) -> str:
        """Return the hexadecimal string representation of the underlying bytes."""
        return self.data.hex()
