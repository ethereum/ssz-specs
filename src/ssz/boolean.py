"""SSZ boolean type — true or false serialized as a single byte."""

from __future__ import annotations

from numbers import Number
from typing import IO, Any, ClassVar, NoReturn, Self, TypeAlias, override

from pydantic.annotated_handlers import GetCoreSchemaHandler
from pydantic_core import CoreSchema, core_schema

from ssz.base import wrapping_schema
from ssz.exceptions import (
    SSZSerializationError,
    SSZTypeError,
    SSZTypeMismatch,
    SSZValueError,
)
from ssz.ssz_base import SSZType


class Boolean(int, SSZType):
    r"""
    Strict SSZ boolean encoded as exactly one byte.

    - Inherits from int so true/false work natively in truthiness checks.
    - Arithmetic and the shifts are refused, a bit being nothing to count with.
    - Counting the set bits of a bitfield therefore runs over plain integers.
    - Bitwise ops (& | ^) reject operands of any other type.
    - Every comparison rejects anything but another boolean, and hashing agrees.

    Wire format:

        true   ->  b"\x01"
        false  ->  b"\x00"
    """

    _INTERNED: ClassVar[tuple[Any, ...]] = ()
    """The two values of this class, one shared instance each.

    A bit is the whole of what one of these values holds.
    Every holder of a given bit can therefore be handed the same object.
    """

    def __init_subclass__(cls, **kwargs: Any) -> None:
        """Build the pair a named boolean hands out, so a subtype comes back as itself."""
        super().__init_subclass__(**kwargs)
        # Allocated past this class's own constructor, which reads the pair being built.
        cls._INTERNED = (int.__new__(cls, 0), int.__new__(cls, 1))

    def __new__(cls, value: bool | int = False) -> Self:
        """
        Return the shared instance of this class holding the given bit.

        Only the four values true, false, 0, and 1 are accepted.

        Args:
            value: The raw value to wrap.
                Omitting it gives the default value, false.

        Raises:
            SSZTypeError: If value is not a bool or int.
            SSZValueError: If value is an integer outside 0 or 1.
        """
        if not isinstance(value, int):
            raise SSZTypeMismatch("bool or int", type(value))

        # Coerce to a plain int before the membership test:
        #
        #   - value in (0, 1) does value == 0 or value == 1.
        #   - For a Boolean operand, those comparisons hit strict equality and raise.
        #   - int(value) returns a plain int, so == falls back to int equality.
        bit = int(value)
        if bit not in (0, 1):
            raise SSZValueError(f"Boolean value must be 0 or 1, not {value}")

        # The value is 0 or 1 by this point, so it indexes the pair directly.
        interned: tuple[Self, ...] = cls._INTERNED
        return interned[bit]

    def __setattr__(self, name: str, value: Any) -> NoReturn:
        """
        Refuse to attach state to a value.

        - A shared instance reaches every holder of that bit.
        - State attached through one would be readable through all the others.
        - A slot declaration cannot close this off.
        - Any subclass omitting one regains the dictionary this refusal guards.

        Raises:
            SSZTypeError: Always, because a bit is only the bit it holds.
        """
        raise SSZTypeError(f"{type(self).__name__} is immutable")

    @classmethod
    def __get_pydantic_core_schema__(
        cls, source_type: Any, handler: GetCoreSchemaHandler
    ) -> CoreSchema:
        """
        Provide a Pydantic core schema that enforces strict boolean validation.

        A field holds a boolean as an instance or as a strict bool.
        The ints 0 and 1 are refused here, though the constructor takes them.

        JSON carries the value as a plain bool.
        """
        return wrapping_schema(cls, core_schema.bool_schema(strict=True), to_json=bool)

    @classmethod
    @override
    def fixed_size(cls) -> int:
        """One byte, for either of the two values."""
        return 1

    @override
    def encode_bytes(self) -> bytes:
        r"""
        Encode the boolean to its SSZ byte representation.

        - true   -> b"\x01"
        - false  -> b"\x00"
        """
        return b"\x01" if self else b"\x00"

    @classmethod
    @override
    def decode_bytes(cls, data: bytes) -> Self:
        """
        Decode a single SSZ byte into a boolean.

        Input must be exactly one byte with value 0x00 or 0x01.

        Args:
            data: SSZ-encoded byte.

        Returns:
            A boolean wrapping the decoded value.

        Raises:
            SSZSerializationError:
                - When the input length is not 1.
                - When the byte value is outside the 0x00 / 0x01 set.
        """
        if len(data) != 1:
            raise SSZSerializationError(f"Boolean: expected 1 byte, got {len(data)}")
        if data[0] not in (0, 1):
            raise SSZSerializationError(f"Boolean: byte must be 0x00 or 0x01, got {data[0]:#04x}")

        # The byte is 0 or 1 by the guard above.
        # That is the whole of what the constructor settles before indexing this same pair.
        interned: tuple[Self, ...] = cls._INTERNED
        return interned[data[0]]

    @override
    def serialize(self, stream: IO[bytes]) -> int:
        """Write the SSZ-encoded byte to a binary stream."""
        encoded_data = self.encode_bytes()
        stream.write(encoded_data)
        return len(encoded_data)

    @classmethod
    @override
    def deserialize(cls, stream: IO[bytes], scope: int) -> Self:
        """
        Read one SSZ byte from a stream and decode into a boolean.

        Args:
            stream: Source binary stream.
            scope: Number of bytes the caller has allocated for this value (must be 1).

        Returns:
            A boolean wrapping the decoded value.

        Raises:
            SSZSerializationError:
                - When scope is not 1.
                - When the underlying byte decode fails.
        """
        if scope != 1:
            raise SSZSerializationError(f"Boolean: expected scope of 1, got {scope}")
        return cls.decode_bytes(stream.read(1))

    @classmethod
    def _raise_type_error(cls, other: Any, op_symbol: str) -> NoReturn:
        """Helper to raise a consistent TypeError."""
        raise TypeError(
            f"Unsupported operand type(s) for {op_symbol}: "
            + f"'{cls.__name__}' and '{type(other).__name__}'"
        )

    @classmethod
    def _raise_unary_type_error(cls, op_symbol: str) -> NoReturn:
        """Helper to raise a consistent TypeError where there is one operand only."""
        raise TypeError(f"Unsupported operand type for {op_symbol}: '{cls.__name__}'")

    @classmethod
    def _refuse_arithmetic(cls, other: Any, op_symbol: str) -> Any:
        """
        Refuse a number, and decline anything else.

        No number stands in an arithmetic relation to a truth value.
        Declining leaves a type that knows how to combine with a bit free to answer.

        Returns:
            NotImplemented, for an operand that is not a number.

        Raises:
            TypeError: When the operand is a number.
        """
        if isinstance(other, Number):
            cls._raise_type_error(other, op_symbol)
        return NotImplemented

    def __add__(self, other: Any) -> Any:
        """Forward addition."""
        return self._refuse_arithmetic(other, "+")

    def __radd__(self, other: Any) -> Any:
        """Reverse addition."""
        return self._refuse_arithmetic(other, "+")

    def __sub__(self, other: Any) -> Any:
        """Forward subtraction."""
        return self._refuse_arithmetic(other, "-")

    def __rsub__(self, other: Any) -> Any:
        """Reverse subtraction."""
        return self._refuse_arithmetic(other, "-")

    def __mul__(self, other: Any) -> Any:
        """Forward multiplication."""
        return self._refuse_arithmetic(other, "*")

    def __rmul__(self, other: Any) -> Any:
        """Reverse multiplication."""
        return self._refuse_arithmetic(other, "*")

    def __truediv__(self, other: Any) -> Any:
        """Forward true division."""
        return self._refuse_arithmetic(other, "/")

    def __rtruediv__(self, other: Any) -> Any:
        """Reverse true division."""
        return self._refuse_arithmetic(other, "/")

    def __floordiv__(self, other: Any) -> Any:
        """Forward floor division."""
        return self._refuse_arithmetic(other, "//")

    def __rfloordiv__(self, other: Any) -> Any:
        """Reverse floor division."""
        return self._refuse_arithmetic(other, "//")

    def __mod__(self, other: Any) -> Any:
        """Forward modulo."""
        return self._refuse_arithmetic(other, "%")

    def __rmod__(self, other: Any) -> Any:
        """Reverse modulo."""
        return self._refuse_arithmetic(other, "%")

    def __divmod__(self, other: Any) -> Any:
        """Forward divmod."""
        return self._refuse_arithmetic(other, "divmod")

    def __rdivmod__(self, other: Any) -> Any:
        """Reverse divmod."""
        return self._refuse_arithmetic(other, "divmod")

    def __pow__(self, other: Any, modulo: Any = None) -> Any:
        """Forward exponentiation and three-argument pow."""
        return self._refuse_arithmetic(other, "**")

    def __rpow__(self, other: Any, modulo: Any = None) -> Any:
        """Reverse exponentiation and three-argument pow."""
        return self._refuse_arithmetic(other, "**")

    def __lshift__(self, other: Any) -> Any:
        """Forward left bit-shift."""
        return self._refuse_arithmetic(other, "<<")

    def __rlshift__(self, other: Any) -> Any:
        """Reverse left bit-shift."""
        return self._refuse_arithmetic(other, "<<")

    def __rshift__(self, other: Any) -> Any:
        """Forward right bit-shift."""
        return self._refuse_arithmetic(other, ">>")

    def __rrshift__(self, other: Any) -> Any:
        """Reverse right bit-shift."""
        return self._refuse_arithmetic(other, ">>")

    def __neg__(self) -> NoReturn:
        """Negation, which lands outside the two values a bit may hold."""
        self._raise_unary_type_error("unary -")

    def __pos__(self) -> NoReturn:
        """Unary plus, which reads a bit as the quantity it is not."""
        self._raise_unary_type_error("unary +")

    def __invert__(self) -> NoReturn:
        """Inversion, which complements a whole integer rather than one bit."""
        self._raise_unary_type_error("~")

    def __abs__(self) -> NoReturn:
        """Magnitude, which a truth value has none of."""
        self._raise_unary_type_error("abs()")

    def __and__(self, other: Any) -> Self:
        """Bitwise AND between two booleans — rejects any other operand."""
        if not isinstance(other, type(self)):
            self._raise_type_error(other, "&")
        return type(self)(int(self) & int(other))

    def __rand__(self, other: Any) -> Self:
        """Bitwise AND when the boolean is on the right of the operator."""
        return self.__and__(other)

    def __or__(self, other: Any) -> Self:
        """Bitwise OR between two booleans — rejects any other operand."""
        if not isinstance(other, type(self)):
            self._raise_type_error(other, "|")
        return type(self)(int(self) | int(other))

    def __ror__(self, other: Any) -> Self:
        """Bitwise OR when the boolean is on the right of the operator."""
        return self.__or__(other)

    def __xor__(self, other: Any) -> Self:
        """Bitwise XOR between two booleans — rejects any other operand."""
        if not isinstance(other, type(self)):
            self._raise_type_error(other, "^")
        return type(self)(int(self) ^ int(other))

    def __rxor__(self, other: Any) -> Self:
        """Bitwise XOR when the boolean is on the right of the operator."""
        return self.__xor__(other)

    def __eq__(self, other: object) -> bool:
        """
        Strict equality.

        - Only another boolean compares.
        - A raw bool is refused like any other type.

        Raises:
            TypeError: If other is not a Boolean.
        """
        if isinstance(other, Boolean):
            return int(self) == int(other)
        self._raise_type_error(other, "==")

    def __ne__(self, other: object) -> bool:
        """
        Strict inequality.

        - Only another boolean compares.
        - Defined explicitly because the parent class's not-equal bypasses strict equality.

        Raises:
            TypeError: If other is not a Boolean.
        """
        if isinstance(other, Boolean):
            return int(self) != int(other)
        self._raise_type_error(other, "!=")

    def __lt__(self, other: Any) -> bool:
        """
        Strict less-than, ordering false below true.

        Raises:
            TypeError: If other is not a Boolean.
        """
        if isinstance(other, Boolean):
            return int(self) < int(other)
        self._raise_type_error(other, "<")

    def __le__(self, other: Any) -> bool:
        """
        Strict less-than-or-equal, ordering false below true.

        Raises:
            TypeError: If other is not a Boolean.
        """
        if isinstance(other, Boolean):
            return int(self) <= int(other)
        self._raise_type_error(other, "<=")

    def __gt__(self, other: Any) -> bool:
        """
        Strict greater-than, ordering true above false.

        Raises:
            TypeError: If other is not a Boolean.
        """
        if isinstance(other, Boolean):
            return int(self) > int(other)
        self._raise_type_error(other, ">")

    def __ge__(self, other: Any) -> bool:
        """
        Strict greater-than-or-equal, ordering true above false.

        Raises:
            TypeError: If other is not a Boolean.
        """
        if isinstance(other, Boolean):
            return int(self) >= int(other)
        self._raise_type_error(other, ">=")

    def __repr__(self) -> str:
        """Return the official form: Boolean(True) or Boolean(False)."""
        return f"Boolean({bool(self)})"

    def __str__(self) -> str:
        """Return the user-facing form: True or False."""
        return str(bool(self))

    # Defining equality clears the inherited hash.
    # The bit is the whole value, so hashing it matches equality.
    # A raw bool then shares a bucket, and a membership test reaches the refusal.
    __hash__ = int.__hash__


# A class builds its pair as it is declared, and this one is declared by no such step.
# Its own pair is therefore built here, as soon as there is a class to build one from.
Boolean._INTERNED = (int.__new__(Boolean, 0), int.__new__(Boolean, 1))

Bit: TypeAlias = Boolean
"""One bit, a spelling for bitfield elements that the spec itself does not define."""
