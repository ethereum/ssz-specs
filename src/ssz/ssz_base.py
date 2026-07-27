"""Abstract bases for the SSZ type system."""

import io
from abc import ABC, abstractmethod
from collections.abc import Iterator, Sequence
from typing import IO, TYPE_CHECKING, Any, ClassVar, Final, Self, cast, overload, override

from pydantic import ConfigDict

from ssz.base import StrictBaseModel
from ssz.exceptions import (
    SSZLengthError,
    SSZLimitError,
    SSZSerializationError,
    SSZTypeError,
    SSZTypeMismatch,
)

BYTES_PER_LENGTH_OFFSET: Final = 4
"""Width of an SSZ offset prefixing each variable-size element.

Encoded as a uint32 in little-endian byte order."""

_CAPACITY_NAMES: Final = ("LENGTH", "LIMIT")
"""The class attributes a shape declares its element count with.

An exact count and an upper bound are spelled differently, and no shape declares both."""


class SSZType(ABC):
    """
    Abstract base for every SSZ-encodable type.

    Every type but one has a default value, and building it from nothing gives that default:

        uint, boolean                      zero, false
        fixed byte array                   every byte zero
        bitvector                          every bit clear
        vector                             the element default, once per position
        container                          one field default per field
        list, bitlist, progressive shapes  empty
        compatible union                   none, and asking for one is an error

    A composite default is built from the defaults of its parts, so it recurses.
    A part with no default leaves the whole with none.

    Only the total absence of input asks for a default.
    An empty sequence handed to a fixed-length shape is a wrong count, and an error.
    """

    def __init_subclass__(cls, **kwargs: Any) -> None:
        """
        Narrow a declared capacity to a plain integer, at the point it is declared.

        A capacity may be written with a typed value.
        A consensus spec already holds its length constants as uints.
        Requiring a cast at every declaration would therefore mean casting almost all of them:

            class Attestations(List[Attestation]):
                LIMIT = MAX_ATTESTATIONS   # already a Uint64

        Two facts make narrowing necessary rather than cosmetic.

        - Every element count computed inside this library is a plain integer.
        - A uint refuses a plain integer operand outright.

        A capacity left typed would reach a comparison it cannot take part in.

        A capacity that is not an integer at all is refused here as well.
        Declaration is the only place that refusal can be useful:

            LIMIT = 4.7   ->  refused, rather than resolving to a chunk count nobody wrote
            LIMIT = "4"   ->  refused, rather than reporting a wrong element count later

        Raises:
            SSZTypeMismatch: When a declared capacity is not an integer.
            SSZTypeMismatch: When a declared capacity is a boolean, which counts nothing.
        """
        super().__init_subclass__(**kwargs)

        for name in _CAPACITY_NAMES:
            # Only a capacity this class declares itself.
            # An inherited one was already narrowed when its own class was created.
            if name not in cls.__dict__:
                continue

            # A plain integer is the common case.
            # Recognizing it costs one identity check, once per type declared.
            declared = cls.__dict__[name]
            if type(declared) is int:
                continue

            # A boolean is a flag rather than a count.
            # Narrowing one would turn a nonsensical declaration into a capacity of 1,
            # which is worse than refusing it.
            #
            # A boolean of this library's own is left to narrow, because every integer
            # here already accepts one in place of 0 or 1.
            if not isinstance(declared, int) or isinstance(declared, bool):
                raise SSZTypeMismatch(f"an integer count for {cls.__name__}.{name}", type(declared))

            # Every integer type narrows the same way, whatever width it declares.
            setattr(cls, name, int(declared))

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

    @classmethod
    def default(cls) -> Self:
        """
        Build the default value of this type.

        Construction with no argument gives the same value.
        This spelling exists because a type checker reads a field list, not the defaults
        this library attaches to it, and so reports a no-argument construction as missing
        its arguments.

        Returns:
            A fresh default value.

        Raises:
            SSZTypeError: When the type has no default value.
        """
        return cls()

    def is_zero(self) -> bool:
        """
        Whether this value equals the default of its own type.

        The spec calls such a value zeroed.
        A fresh default is built per call, and hoisting it into a constant would alias it.

        Returns:
            True when the value is the default of its type.

        Raises:
            SSZTypeError: When the type has no default, leaving nothing to compare against.
        """
        # The runtime type, so a named subtype compares against its own default.
        return self == type(self).default()

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
    collection size.
    Reading a position and assigning to one both live on this shared base.
    Only variable-size collections offer append and pop. Fixed-length shapes accept
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

        A fixed-length shape needs every element, and no argument means zero of them.
        So this factory with no argument is a length error there, never the default.
        Only construction with no argument at all asks for the default.

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

    @overload
    def __getitem__(self, index: int) -> T: ...
    @overload
    def __getitem__(self, index: slice) -> Sequence[T]: ...

    def __getitem__(self, index: int | slice) -> T | Sequence[T]:
        """
        Read the element or elements at a position.

        Reading delegates to the contents.
        Every addressing form the host language offers therefore works, including a
        position counted from the end.

        A position counted from the end resolves against the number of elements held.
        It never resolves against the declared capacity.

            held = [10, 20, 30]   under a capacity of 4

            [-1]  ->  30          the last element held
            [-3]  ->  10
            [-4]  ->  IndexError  no fourth element to count back to

        The zeros that pad a value to its capacity belong to merkleization.
        They are not members of the value.
        So the unused slot is unaddressable from either end.
        """
        return self.data[index]

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
