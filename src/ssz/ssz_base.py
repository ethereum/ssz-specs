"""Abstract bases for the SSZ type system."""

import io
from abc import ABC, abstractmethod
from collections.abc import Iterator, Sequence
from typing import IO, TYPE_CHECKING, Any, ClassVar, Final, Self, cast, override

from pydantic import ConfigDict

from ssz.base import StrictBaseModel
from ssz.exceptions import (
    SSZLengthError,
    SSZLimitError,
    SSZSerializationError,
    SSZTypeError,
)

BYTES_PER_LENGTH_OFFSET: Final = 4
"""Width of an SSZ offset prefixing each variable-size element.

Encoded as a uint32 in little-endian byte order."""


class SSZType(ABC):
    """Abstract base for every SSZ-encodable type."""

    @classmethod
    @abstractmethod
    def is_fixed_size(cls) -> bool:
        """
        Whether every instance encodes to the same number of bytes.

        Returns:
            True for fixed-size types, False for variable-size.
        """
        ...

    @classmethod
    @abstractmethod
    def get_byte_length(cls) -> int:
        """
        Fixed encoded byte length of this type.

        Returns:
            The constant byte width every instance encodes to.

        Raises:
            SSZTypeError: If the type is variable-size.
        """
        ...

    @abstractmethod
    def serialize(self, stream: IO[bytes]) -> int:
        """
        Write the SSZ encoding to a binary stream.

        Args:
            stream: Output binary stream.

        Returns:
            Number of bytes written.
        """
        ...

    @classmethod
    @abstractmethod
    def deserialize(cls, stream: IO[bytes], scope: int) -> Self:
        """
        Read one value from a binary stream within a bounded byte budget.

        Args:
            stream: Source binary stream.
            scope: Number of bytes belonging to this value.

        Returns:
            A new instance reconstructed from the stream.
        """
        ...

    def encode_bytes(self) -> bytes:
        """
        Encode this value to its SSZ byte representation.

        Returns:
            Serialized bytes.
        """
        stream = io.BytesIO()
        self.serialize(stream)
        return stream.getvalue()

    @classmethod
    def decode_bytes(cls, data: bytes) -> Self:
        """
        Decode SSZ bytes into a new instance.

        Rejects trailing bytes left over after the stream-based decoder finishes.
        A spec decoder must accept exactly one canonical encoding per value.

        Args:
            data: SSZ-encoded bytes containing exactly one value.

        Returns:
            A new instance reconstructed from the input.

        Raises:
            SSZSerializationError: If the input carries bytes past the decoded value.
        """
        stream = io.BytesIO(data)
        instance = cls.deserialize(stream, len(data))

        # Spec contract: each canonical encoding maps to exactly one value.
        #
        # Any unread bytes mean the input either over-allocated or carries noise.
        leftover = len(data) - stream.tell()
        if leftover:
            raise SSZSerializationError(f"{cls.__name__}: {leftover} trailing byte(s) after decode")
        return instance


class SSZModel(StrictBaseModel, SSZType):
    """
    Pydantic-backed SSZ base used by containers, lists, vectors, and bitfields.

    Two shapes share this base:

    - Collections wrap an inner sequence in one Pydantic field called data.
    - Containers expose multiple named Pydantic fields that map to a struct on the wire.

    The default length and string forms switch on which shape the subclass uses.

    Mutability is configurable per type through the MUTABLE flag. It defaults
    to on and is inherited, so an application can declare one base with
    MUTABLE set to False and every type built on it is immutable.
    """

    MUTABLE: ClassVar[bool] = True
    """Whether instances accept mutation. Set False on a subclass to freeze it."""

    def _require_mutable(self) -> None:
        """Reject the mutation when the type declares itself immutable."""
        if not type(self).MUTABLE:
            raise SSZTypeError(f"{type(self).__name__} is immutable")

    # Hidden from type checkers: a visible __setattr__ typed to accept Any
    # would exempt every field assignment from static checking against the
    # declared field types.
    if not TYPE_CHECKING:  # pragma: no cover

        def __setattr__(self, name: str, value: Any) -> None:
            """Gate field assignment on the MUTABLE flag, then validate as usual."""
            self._require_mutable()
            super().__setattr__(name, value)

    def __len__(self) -> int:
        """Element count for a collection, field count for every other shape."""
        # The base class decides, not the field name.
        # A union names its payload field the way the spec does, and is not a collection.
        if isinstance(self, SSZCollection):
            return len(self.data)
        return len(type(self).model_fields)

    def __repr__(self) -> str:
        """Show a collection's contents, and any other shape's fields by name."""
        cls_name = type(self).__name__
        if isinstance(self, SSZCollection):
            return f"{cls_name}(data={list(self.data)!r})"
        field_strs = [f"{name}={getattr(self, name)!r}" for name in type(self).model_fields]
        return f"{cls_name}({' '.join(field_strs)})"


class SSZCollection[T](SSZModel):
    """
    Pydantic-backed SSZ base for collections that wrap their contents in one data field.

    Sequences, bitfields, and byte lists all share this base.
    Containers do not — their contents live in named fields, not a single data field.

    Every subclass wraps its contents in one field named data.

    Construction passes the field by keyword, or the elements positionally
    through the `of` factory:

        Uint8List4(data=[1, 2, 3])
        Uint8List4.of(1, 2, 3)

    Collections mutate in place. Mutation validates the incoming elements and
    the resulting length by the same rules construction applies. Elements
    already inside the collection were validated when they entered, so they
    are left alone and mutation cost is proportional to the change, not the
    collection size. Element assignment lives on this shared base; only
    variable-size collections offer append and pop. Fixed-length shapes accept
    element assignment but reject any length change. Mutability itself is
    configurable through the inherited MUTABLE flag.

    The type parameter is the declared element type: sequences bind their own
    element type, bitfields bind Boolean, and byte lists bind int. Mutation is
    typed against it, so type checkers flag raw values at mutation sites even
    though runtime validation coerces them exactly as construction does.
    """

    model_config = ConfigDict(frozen=False, validate_assignment=True)

    data: Sequence[T]
    """The contents, declared with its concrete type and default by each subclass."""

    @classmethod
    def of(cls, *elements: Any) -> Self:
        r"""
        Build an instance from the given elements.

        Pydantic models are keyword-only, so the data field is normally passed by
        keyword. This factory is the positional form: each argument is exactly one
        element, and no argument is ever spread. Classmethods are inherited without
        re-synthesis, so unlike a custom constructor this form stays fully visible
        to static type checkers on every subclass.

            Uint8List4.of(1, 2, 3)     ==  Uint8List4(data=[1, 2, 3])
            Uint8List4.of()            ==  Uint8List4(data=[])
            Uint8List4.of(*existing)   spreads an existing sequence
            ByteList10.of(0xDE, 0xAD)  ==  ByteList10(data=b"\xde\xad")

        Args:
            *elements: The elements of the new collection.

        Returns:
            A new instance holding exactly the given elements.
        """
        return cls(data=elements)

    # The parent Pydantic model iterates field name and value pairs.
    # Yielding the contents instead is the intended collection behavior.
    # The narrower element type violates strict Liskov substitution, so it is suppressed.
    @override
    def __iter__(self) -> Iterator[T]:  # ty: ignore[invalid-method-override]
        """
        Iterate over the contents.

        Defined here because the parent Pydantic model otherwise yields
        name/value pairs of its fields.
        """
        return iter(self.data)

    def __setitem__(self, index: int | slice, value: T | Sequence[T]) -> None:
        """Replace the element(s) at ``index``, validating each new element."""
        self._require_mutable()
        if isinstance(index, slice):
            elements = [self._validate_element(v) for v in cast("Sequence[T]", value)]
            # Dry run on a copy: the resulting length must pass the declared
            # bound before the stored payload changes.
            candidate = list(self.data)
            candidate[index] = elements
            self._validate_length(len(candidate))
            cast("list[T]", self.data)[index] = elements
        else:
            cast("list[T]", self.data)[index] = self._validate_element(value)

    def _validate_element(self, value: Any) -> Any:
        """
        Validate one incoming element by the family's construction rule.

        Each concrete family implements this with the same rule its data
        validator applies to every element at construction.
        """
        raise NotImplementedError

    def _validate_length(self, length: int) -> None:
        """Check a prospective element count against the declared size bound."""
        cls = type(self)
        declared_length = getattr(cls, "LENGTH", None)
        if declared_length is not None and length != declared_length:
            raise SSZLengthError(cls.__name__, declared_length, length)
        declared_limit = getattr(cls, "LIMIT", None)
        if declared_limit is not None and length > declared_limit:
            raise SSZLimitError(cls.__name__, declared_limit, length)
