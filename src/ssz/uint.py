"""Unsigned Integer Type Specification."""

from __future__ import annotations

from numbers import Number
from types import NotImplementedType
from typing import IO, Any, ClassVar, NoReturn, Self, SupportsInt, TypeAlias, overload, override

from pydantic.annotated_handlers import GetCoreSchemaHandler
from pydantic_core import core_schema

from ssz.base import wrapping_schema
from ssz.exceptions import SSZTypeError, SSZValueError, TypeFault, ValueFault
from ssz.ssz_base import SSZType

INTERN_BELOW = 256
"""How many of the smallest values each width shares, covering where consensus arithmetic stays."""


class BaseUint(int, SSZType):
    """Base class for fixed-width unsigned integer types."""

    BITS: ClassVar[int]
    """The number of bits in the integer (overridden by subclasses)."""

    MAX_VALUE: ClassVar[int]
    """Cached inclusive upper bound ``2**BITS - 1``, computed once per width."""

    BYTE_LENGTH: ClassVar[int]
    """Cached serialized byte width ``BITS // 8``, computed once per width."""

    _INTERNED: ClassVar[tuple[Any, ...]] = ()
    """Shared instances of this class, indexed by the value each one holds."""

    _INTERN_LEN: ClassVar[int] = 0
    """How many entries the shared table holds."""

    def __init_subclass__(cls, **kwargs: Any) -> None:
        """Cache the per-width constants so hot paths never recompute them."""
        super().__init_subclass__(**kwargs)
        cls.MAX_VALUE = 2**cls.BITS - 1
        cls.BYTE_LENGTH = cls.BITS // 8
        # One table per class, so a named subtype comes back as itself.
        cls._INTERNED = tuple(
            int.__new__(cls, n) for n in range(min(INTERN_BELOW, cls.MAX_VALUE + 1))
        )
        cls._INTERN_LEN = len(cls._INTERNED)

    def __new__(cls, value: SupportsInt = 0) -> Self:
        """
        Create and range-check a new instance.

        Args:
            value: The integer to wrap.
                Omitting it gives the default value, zero.

        Raises:
            SSZTypeError: If value is not an int. Bool, string, and float are rejected.
            SSZValueError: If value is outside [0, 2**BITS - 1].
        """
        # An exact int needs neither guard below.
        if type(value) is int:
            return cls._wrap(value)
        # Bool subclasses int, so reject it explicitly before the value check.
        if not isinstance(value, int) or isinstance(value, bool):
            raise SSZTypeError(TypeFault.WRONG_TYPE, expected="int", got=type(value).__name__)
        # Narrowing keeps the bound check below off an arbitrary subclass's own operators.
        return cls._wrap(int(value))

    @classmethod
    def _wrap(cls, value: int) -> Self:
        """
        Range-check an integer and wrap it into a typed instance.

        The caller has already narrowed the value to a plain int, so no type guard runs here.

        Raises:
            SSZValueError: If value is outside [0, 2**BITS - 1].
        """
        if value < cls._INTERN_LEN:
            # A negative index would read from the end of the table instead of refusing.
            if value >= 0:
                interned: tuple[Self, ...] = cls._INTERNED
                return interned[value]
        elif value <= cls.MAX_VALUE:
            return int.__new__(cls, value)
        raise SSZValueError(ValueFault.RANGE, value=value, type=cls.__name__, max=cls.MAX_VALUE)

    def __setattr__(self, name: str, value: Any) -> NoReturn:
        """
        Refuse to attach state to a value.

        Instances are shared, so state attached through one would be readable through all.

        Raises:
            SSZTypeError: Always, because a count is only the number it holds.
        """
        raise SSZTypeError(TypeFault.IMMUTABLE, type=type(self).__name__)

    @classmethod
    def __get_pydantic_core_schema__(
        cls, source_type: Any, handler: GetCoreSchemaHandler
    ) -> core_schema.CoreSchema:
        """
        Hook into Pydantic's validation system.

        A field holds a uint as an instance or as a strict int within the unsigned range.
        """
        return wrapping_schema(
            cls,
            core_schema.int_schema(ge=0, lt=2**cls.BITS, strict=True),
            to_json=int,
        )

    @classmethod
    @override
    def fixed_size(cls) -> int:
        """The width the declared bit count settles, whatever value an instance holds."""
        return cls.BYTE_LENGTH

    @override
    def encode_bytes(self) -> bytes:
        """Serialize to little-endian bytes, reading the width off the cached attribute."""
        return self.to_bytes(self.BYTE_LENGTH, "little")

    @classmethod
    @override
    def decode_bytes(cls, data: bytes) -> Self:
        """
        Deserialize from little-endian bytes.

        Raises:
            SSZValueError: If the byte string has the wrong length.
        """
        expected_length = cls.BYTE_LENGTH
        if len(data) != expected_length:
            raise SSZValueError(
                ValueFault.TRUNCATED,
                type=cls.__name__,
                expected=expected_length,
                actual=len(data),
            )

        return cls._wrap(int.from_bytes(data, "little"))

    @override
    def serialize(self, stream: IO[bytes]) -> int:
        """Write little-endian bytes to a stream and return the count written."""
        encoded_data = self.encode_bytes()
        stream.write(encoded_data)
        return len(encoded_data)

    @classmethod
    @override
    def deserialize(cls, stream: IO[bytes], scope: int) -> Self:
        """
        Read little-endian bytes from a stream within a fixed scope.

        Raises:
            SSZValueError: If the scope mismatches, or the stream ends early.
        """
        byte_length = cls.BYTE_LENGTH
        if scope != byte_length:
            raise SSZValueError(
                ValueFault.SCOPE, type=cls.__name__, expected=byte_length, actual=scope
            )
        serialized_bytes = stream.read(byte_length)
        if len(serialized_bytes) != byte_length:
            raise SSZValueError(
                ValueFault.TRUNCATED,
                type=cls.__name__,
                expected=byte_length,
                actual=len(serialized_bytes),
            )
        return cls._wrap(int.from_bytes(serialized_bytes, "little"))

    @classmethod
    def max_value(cls) -> Self:
        """The maximum value for this unsigned integer."""
        return cls(cls.MAX_VALUE)

    @classmethod
    def _raise_type_error(cls, other: Any, op_symbol: str) -> NoReturn:
        """Helper to raise a consistent TypeError."""
        raise TypeError(
            f"Unsupported operand type(s) for {op_symbol}: "
            + f"'{cls.__name__}' and '{type(other).__name__}'"
        )

    @classmethod
    def _resolve_type(cls, other: Any, op_symbol: str) -> type[Self] | NotImplementedType:
        """The type an operation produces: the more derived of the two, or NotImplemented."""
        other_cls = type(other)
        # A plain int is the one non-uint operand allowed through, by identity so bool stays out.
        if other_cls is int:
            return cls
        if issubclass(other_cls, BaseUint):
            # The derived type wins in whichever position it appears.
            if issubclass(other_cls, cls):
                return other_cls
            if issubclass(cls, other_cls):
                return cls
        # A number reaching here is a sibling width, or a unit this one cannot count in.
        if isinstance(other, Number):
            cls._raise_type_error(other, op_symbol)
        # Anything else is declined, so a list multiplied by a uint still repeats itself.
        return NotImplemented

    @classmethod
    def _require_relation(cls, other: Any, op_symbol: str) -> None:
        """
        Insist on a relation where an arithmetic operator would settle for declining.

        A declined comparison answers false rather than raising, which mixes types silently.

        Raises:
            TypeError: When no relation admits the operand.
        """
        if cls._resolve_type(other, op_symbol) is NotImplemented:
            cls._raise_type_error(other, op_symbol)

    def __add__(self, other: Any) -> Self:
        """Forward addition."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "+")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__add__(self, other))

    def __radd__(self, other: Any) -> Self:
        """Reverse addition."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "+")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__add__(other, self))

    def __sub__(self, other: Any) -> Self:
        """Forward subtraction."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "-")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__sub__(self, other))

    def __rsub__(self, other: Any) -> Self:
        """Reverse subtraction."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "-")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__sub__(other, self))

    def __mul__(self, other: Any) -> Self:
        """Forward multiplication."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "*")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__mul__(self, other))

    def __rmul__(self, other: Any) -> Self:
        """Reverse multiplication."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "*")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__mul__(other, self))

    def __floordiv__(self, other: Any) -> Self:
        """Forward floor division."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "//")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__floordiv__(self, other))

    def __rfloordiv__(self, other: Any) -> Self:
        """Reverse floor division."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "//")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__floordiv__(other, self))

    def __mod__(self, other: Any) -> Self:
        """Forward modulo."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "%")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__mod__(self, other))

    def __rmod__(self, other: Any) -> Self:
        """Reverse modulo."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "%")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__mod__(other, self))

    @overload
    def __pow__(self, value: int, mod: None = None, /) -> Self: ...
    @overload
    def __pow__(self, value: int, mod: int, /) -> Self: ...
    # Narrowing both parent overloads to one subtype is safe, but the strict check refuses it.
    def __pow__(self, value: int, mod: int | None = None, /) -> Self:  # ty: ignore[invalid-method-override]
        """Forward exponentiation and three-argument pow."""
        cls = type(self)
        if type(value) is not cls:
            cls = cls._resolve_type(value, "**")
            if cls is NotImplemented:
                return NotImplemented
        # The modulus resolves against the type the exponent settled on, so its unit survives.
        if mod is not None and type(mod) is not cls:
            cls = cls._resolve_type(mod, "**")
            if cls is NotImplemented:
                return NotImplemented
        power = pow(int(self), int(value), int(mod) if mod is not None else None)
        return cls._wrap(power)

    def __rpow__(self, base: int, modulo: int | None = None, /) -> Self:
        """Reverse exponentiation and three-argument pow."""
        cls = type(self)
        if type(base) is not cls:
            cls = cls._resolve_type(base, "**")
            if cls is NotImplemented:
                return NotImplemented
        if modulo is not None and type(modulo) is not cls:
            cls = cls._resolve_type(modulo, "**")
            if cls is NotImplemented:
                return NotImplemented
        power = pow(int(base), int(self), int(modulo) if modulo is not None else None)
        return cls._wrap(power)

    def __divmod__(self, other: Any) -> tuple[Self, Self]:
        """Forward divmod."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "divmod")
            if cls is NotImplemented:
                return NotImplemented
        quotient, remainder = int.__divmod__(self, other)
        return cls._wrap(quotient), cls._wrap(remainder)

    def __rdivmod__(self, other: Any) -> tuple[Self, Self]:
        """Reverse divmod."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "divmod")
            if cls is NotImplemented:
                return NotImplemented
        quotient, remainder = int.__rdivmod__(self, other)
        return cls._wrap(quotient), cls._wrap(remainder)

    def __and__(self, other: Any) -> Self:
        """Forward bitwise AND."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "&")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__and__(self, other))

    def __rand__(self, other: Any) -> Self:
        """Reverse bitwise AND."""
        return self.__and__(other)

    def __or__(self, other: Any) -> Self:
        """Forward bitwise OR."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "|")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__or__(self, other))

    def __ror__(self, other: Any) -> Self:
        """Reverse bitwise OR."""
        return self.__or__(other)

    def __xor__(self, other: Any) -> Self:
        """Forward bitwise XOR."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "^")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__xor__(self, other))

    def __rxor__(self, other: Any) -> Self:
        """Reverse bitwise XOR."""
        return self.__xor__(other)

    def __lshift__(self, other: Any) -> Self:
        """Forward left bit-shift."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "<<")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__lshift__(self, other))

    def __rlshift__(self, other: Any) -> Self:
        """Reverse left bit-shift."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, "<<")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__lshift__(other, self))

    def __rshift__(self, other: Any) -> Self:
        """Forward right bit-shift."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, ">>")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__rshift__(self, other))

    def __rrshift__(self, other: Any) -> Self:
        """Reverse right bit-shift."""
        cls = type(self)
        if type(other) is not cls:
            cls = cls._resolve_type(other, ">>")
            if cls is NotImplemented:
                return NotImplemented
        return cls._wrap(int.__rshift__(other, self))

    def __eq__(self, other: object) -> bool:
        """Equality."""
        if type(other) is not type(self):
            self._require_relation(other, "==")
        return super().__eq__(other)

    def __ne__(self, other: object) -> bool:
        """Inequality."""
        if type(other) is not type(self):
            self._require_relation(other, "!=")
        return super().__ne__(other)

    def __lt__(self, other: Any) -> bool:
        """Less-than."""
        if type(other) is not type(self):
            self._require_relation(other, "<")
        return super().__lt__(other)

    def __le__(self, other: Any) -> bool:
        """Less-than-or-equal."""
        if type(other) is not type(self):
            self._require_relation(other, "<=")
        return super().__le__(other)

    def __gt__(self, other: Any) -> bool:
        """Greater-than."""
        if type(other) is not type(self):
            self._require_relation(other, ">")
        return super().__gt__(other)

    def __ge__(self, other: Any) -> bool:
        """Greater-than-or-equal."""
        if type(other) is not type(self):
            self._require_relation(other, ">=")
        return super().__ge__(other)

    def __repr__(self) -> str:
        """Official representation includes the subtype name."""
        return f"{type(self).__name__}({int(self)})"

    def __str__(self) -> str:
        """Informal representation matches the underlying value."""
        return str(int(self))

    # Equality admits a bare integer, so the value alone can decide the hash.
    __hash__ = int.__hash__

    def __index__(self) -> int:
        """Return a plain integer for slicing and indexing."""
        return int(self)


class Uint8(BaseUint):
    """A type representing an 8-bit unsigned integer (uint8)."""

    BITS = 8


class Uint16(BaseUint):
    """A type representing a 16-bit unsigned integer (uint16)."""

    BITS = 16


class Uint32(BaseUint):
    """A type representing a 32-bit unsigned integer (uint32)."""

    BITS = 32


class Uint64(BaseUint):
    """A type representing a 64-bit unsigned integer (uint64)."""

    BITS = 64


class Uint128(BaseUint):
    """A type representing a 128-bit unsigned integer (uint128)."""

    BITS = 128


class Uint256(BaseUint):
    """A type representing a 256-bit unsigned integer (uint256)."""

    BITS = 256


Byte: TypeAlias = Uint8
"""Eight bits of opaque data, which the spec encodes and hashes as an eight-bit number."""
