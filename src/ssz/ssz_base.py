"""Abstract bases for the SSZ type system."""

import io
from abc import ABC, abstractmethod
from typing import IO, Any, Final, Self

from ssz.base import StrictBaseModel
from ssz.exceptions import SSZSerializationError

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
    """

    def __len__(self) -> int:
        """Element count for collections, field count for containers."""
        data_field = getattr(self, "data", None)
        if data_field is not None:
            return len(data_field)
        return len(type(self).model_fields)

    def __repr__(self) -> str:
        """Show collection contents as data=[...] or container fields as name=value pairs."""
        cls_name = type(self).__name__
        data_field = getattr(self, "data", None)
        if data_field is not None:
            return f"{cls_name}(data={list(data_field)!r})"
        field_strs = [f"{name}={getattr(self, name)!r}" for name in type(self).model_fields]
        return f"{cls_name}({' '.join(field_strs)})"


class SSZCollection(SSZModel):
    """
    Pydantic-backed SSZ base for collections that wrap their contents in one data field.

    Sequences, bitfields, and byte lists all share this base.
    Containers do not — their contents live in named fields, not a single data field.

    Construction passes the field by keyword, or the elements positionally
    through the `of` factory:

        Uint8List4(data=[1, 2, 3])
        Uint8List4.of(1, 2, 3)
    """

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
        # The data field is declared by each concrete subclass, not this base.
        return cls(data=elements)  # ty: ignore[unknown-argument]
