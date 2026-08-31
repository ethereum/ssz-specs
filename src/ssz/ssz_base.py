"""Abstract bases for the SSZ type system."""

import io
from abc import ABC, abstractmethod
from collections.abc import Iterator, Sequence
from copy import copy as shallow_copy
from typing import IO, TYPE_CHECKING, Any, ClassVar, Final, Self, cast, final, overload, override

from pydantic import ConfigDict, Field
from pydantic.annotated_handlers import GetCoreSchemaHandler
from pydantic_core import core_schema

from ssz.base import StrictBaseModel
from ssz.exceptions import SSZTypeError, SSZValueError, TypeFault, ValueFault

if TYPE_CHECKING:
    # Wanted for one annotation, which is never evaluated.
    from ssz.chunks import Root

_CAPACITY_NAMES: Final = ("LENGTH", "LIMIT")
"""The class attributes a shape declares its element count with."""

_COLD_CACHE: Final = {"_version": 0, "_root_memo": None}
"""What each cache slot holds before anything has touched it."""


class SSZType(ABC):
    """Abstract base for every SSZ-encodable type."""

    LENGTH: ClassVar[int | None] = None
    """Exact element count, or None where the shape declares none."""

    LIMIT: ClassVar[int | None] = None
    """Maximum element count, read the same way: None means no count, never a count of zero."""

    UNIT: ClassVar[str] = "elements"
    """What this shape counts, where a refusal reports a count it would not admit."""

    KIND: ClassVar[str] = "type"
    """How a shape names itself where it is asked for a width it does not have."""

    @classmethod
    def __get_pydantic_core_schema__(
        cls, source_type: Any, handler: GetCoreSchemaHandler, /
    ) -> core_schema.CoreSchema:
        """Accept any SSZ value by membership, which is all an abstract field can check."""
        return core_schema.is_instance_schema(cls)

    @classmethod
    def declared_length(cls) -> int:
        """The exact element count this shape pins, or a definition error where it pins none."""
        if cls.LENGTH is None:
            raise SSZTypeError(TypeFault.UNDECLARED, type=cls.__name__, requirement="LENGTH")
        return cls.LENGTH

    @classmethod
    def declared_limit(cls) -> int:
        """The element count this shape bounds, or a definition error where it bounds none."""
        if cls.LIMIT is None:
            raise SSZTypeError(TypeFault.UNDECLARED, type=cls.__name__, requirement="LIMIT")
        return cls.LIMIT

    def __init_subclass__(cls, **kwargs: Any) -> None:
        """
        Narrow a declared capacity, and refuse a root of the type's own, where each is declared.

        Raises:
            SSZTypeError: A capacity that is not a whole number at or above zero.
            SSZTypeError: A type that declares a root of its own.
        """
        super().__init_subclass__(**kwargs)

        # The resolved attribute covers a method, a property, or one inherited from outside.
        # A field of that name shadows only instances, so the annotations are read as well.
        if (
            cls.hash_tree_root is not SSZType.hash_tree_root
            or "hash_tree_root" in cls.__annotations__
        ):
            raise SSZTypeError(TypeFault.OWN_ROOT, type=cls.__name__)

        for name in _CAPACITY_NAMES:
            # An inherited capacity was already narrowed when its own class was created.
            if name not in cls.__dict__:
                continue

            declared = cls.__dict__[name]
            if type(declared) is not int:
                # A boolean is a flag rather than a count.
                # Narrowing one would make a nonsensical declaration a capacity of 1.
                #
                # A boolean of this library's own narrows, every integer here taking one.
                if not isinstance(declared, int) or isinstance(declared, bool):
                    raise SSZTypeError(
                        TypeFault.NOT_AN_INTEGER,
                        type=cls.__name__,
                        field=name,
                        got=type(declared).__name__,
                    )

                declared = int(declared)
                setattr(cls, name, declared)

            # A capacity counts what a shape holds, and nothing is held a negative number of times.
            if declared < 0:
                raise SSZTypeError(
                    TypeFault.CAPACITY_NEGATIVE, type=cls.__name__, field=name, got=declared
                )

    @classmethod
    @abstractmethod
    def fixed_size(cls) -> int | None:
        """
        Bytes every instance encodes to, or None where that count varies.

        Returns:
            The width every instance shares, or None for a variable-size shape.
        """
        ...

    @classmethod
    def is_fixed_size(cls) -> bool:
        """
        Whether every instance encodes to the same number of bytes.

        Returns:
            True for fixed-size types, False for variable-size.
        """
        return cls.fixed_size() is not None

    @classmethod
    def get_byte_length(cls) -> int:
        """
        Fixed encoded byte length of this type.

        Returns:
            The constant byte width every instance encodes to.

        Raises:
            SSZTypeError: When the type is variable-size, so it has no width to give.
        """
        width = cls.fixed_size()
        if width is None:
            raise SSZTypeError(TypeFault.NOT_FIXED_SIZE, type=cls.__name__, kind=cls.KIND)
        return width

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
        Build the default value of this type, which every type but one has:

            uint, boolean                      zero, false
            fixed byte array                   every byte zero
            bitvector                          every bit clear
            vector                             the element default, once per position
            container                          one field default per field
            list, bitlist, progressive shapes  empty
            compatible union                   none, and asking for one is an error

        A composite builds from its parts, so a part with no default leaves it none.
        Only the total absence of input asks for a default, never an empty sequence.

        Construction with no argument gives the same value.
        This spelling exists because a type checker reads that as missing its arguments.

        Raises:
            SSZTypeError: When the type has no default value.
        """
        return cls()

    @classmethod
    def empty(cls) -> Self:
        """
        Build a value holding nothing, which is the default under another name.

        Raises:
            SSZTypeError: When the type has no default value.
        """
        return cls.default()

    def copy(self) -> Self:
        """
        An independent duplicate of this value, at every depth.

        An immutable value already satisfies that, so it hands itself back.

        Returns:
            A duplicate nothing can be written through to reach this value.
        """
        return self

    def __copy__(self) -> Self:
        """Answer the copy module with the value itself, where it would rebuild a subclass."""
        return self

    def __deepcopy__(self, memo: dict[int, Any]) -> Self:
        """Answer a deep copy with the value itself, there being no depth to descend into."""
        return self

    def is_zero(self) -> bool:
        """
        Whether this value equals the default of its own type.

        The spec calls such a value zeroed.

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

        Rejects trailing bytes, because a spec decoder accepts one encoding per value.

        Args:
            data: SSZ-encoded bytes containing exactly one value.

        Returns:
            A new instance reconstructed from the input.

        Raises:
            SSZValueError: If the input carries bytes past the decoded value.
        """
        stream = io.BytesIO(data)
        instance = cls.deserialize(stream, len(data))

        # Unread bytes mean the input either over-allocated or carries noise.
        leftover = len(data) - stream.tell()
        if leftover:
            raise SSZValueError(ValueFault.TRAILING_BYTES, leftover=leftover)
        return instance

    @final
    def hash_tree_root(self) -> "Root":
        """
        Merkle root of this value.

        The declared shape lays the tree out, so contents alone do not decide the root.
        The module-level function is what the spec defines, and it alone reaches plain bytes.

        Raises:
            SSZTypeError: A type with no registered merkleization rule.
        """
        # Merkleization imports this module, so the name is bound per call, not at import.
        from ssz.roots import hash_tree_root

        return hash_tree_root(self)


class SSZModel(StrictBaseModel, SSZType, ABC):
    """
    Pydantic-backed SSZ base used by containers, lists, vectors, and bitfields.

    A collection wraps its contents in one field; a container names one per struct field.
    """

    __slots__ = ("_root_memo", "_version")
    """
    The mutation counter and the remembered root, one pair per value.

    Slots, because a field would serialize and a private attribute would join equality.
    """

    if TYPE_CHECKING:
        # Declared for the type checker only, and never run.
        # A real annotation here would become a Pydantic private attribute, not a slot.
        _version: ClassVar[int]
        _root_memo: ClassVar["tuple[object, Root] | None"]

    MUTABLE: ClassVar[bool] = True
    """Whether instances accept mutation, and False on a subclass freezes it."""

    def __hash__(self) -> int:
        """
        Hash by Merkle tree root, which is what equality compares.

        A mutable value hashes differently once mutated, so a dict or set loses track of it.
        """
        return hash(self.hash_tree_root())

    def _begin_mutation(self) -> None:
        """
        Admit one mutation, refusing it outright on an immutable type.

        Every mutator passes here, so invalidation is one name to grep for.

        Raises:
            SSZTypeError: When the type declares itself immutable.
        """
        if not type(self).MUTABLE:
            raise SSZTypeError(TypeFault.IMMUTABLE, type=type(self).__name__)
        # Written past this class's own __setattr__, which is the door itself.
        object.__setattr__(self, "_version", self._version + 1)

    # Hidden from type checkers, which would otherwise stop checking field assignments.
    # A visible __getattr__ would also make every misspelled attribute resolve.
    if not TYPE_CHECKING:  # pragma: no cover

        def __setattr__(self, name: str, value: Any) -> None:
            """Pass the mutation door, then assign and validate as usual."""
            self._begin_mutation()
            super().__setattr__(name, value)

        def __getattr__(self, name: str) -> Any:
            """Fill a cache slot on first read, leaving every other name to Pydantic."""
            # Only an unset slot reaches here, so a filled one costs nothing.
            if name in _COLD_CACHE:
                cold = _COLD_CACHE[name]
                object.__setattr__(self, name, cold)
                return cold
            return super().__getattr__(name)

    @override
    def copy(self) -> Self:  # ty: ignore[invalid-method-override]
        """
        An independent duplicate of this value, at every depth.

        Entries are replaced in the field dictionary rather than assigned.
        Assignment would revalidate, and an immutable type refuses it outright.

        Returns:
            A duplicate that shares no writable object with this value.
        """
        duplicate = shallow_copy(self)
        stored = duplicate.__dict__
        for name in type(self).model_fields:
            value = stored[name]
            if isinstance(value, SSZModel):
                stored[name] = value.copy()
            elif type(value) is list:
                stored[name] = [
                    element.copy() if isinstance(element, SSZModel) else element
                    for element in value
                ]
        return duplicate

    def __len__(self) -> int:
        """How many fields this shape declares."""
        return len(type(self).model_fields)

    def __repr__(self) -> str:
        """Show the fields by name."""
        cls_name = type(self).__name__
        field_strs = [f"{name}={getattr(self, name)!r}" for name in type(self).model_fields]
        return f"{cls_name}({' '.join(field_strs)})"


class SSZCollection[T](SSZModel, Sequence[T], ABC):
    """
    Pydantic-backed SSZ base for collections that wrap their contents in one data field.

    Sequences, bitfields, and byte lists all share this base; containers do not.

        Uint8List4(data=[1, 2, 3])
        Uint8List4.of(1, 2, 3)
    """

    model_config = ConfigDict(validate_assignment=True)

    # A subclass narrows this field only where the declaration here carries a value.
    data: Sequence[T] = Field()
    """The contents, declared with its concrete type and default by each subclass."""

    @classmethod
    def of(cls, *elements: Any) -> Self:
        r"""
        Build an instance from the given elements, each argument being exactly one:

            Uint8List4.of(1, 2, 3)     ==  Uint8List4(data=[1, 2, 3])
            Uint8List4.of()            ==  Uint8List4(data=[])
            ByteList10.of(0xDE, 0xAD)  ==  ByteList10(data=b"\xde\xad")

        No argument means zero elements, where no argument at all asks for the default.
        """
        return cls(data=elements)

    # The narrower element type violates strict Liskov substitution, so it is suppressed.
    @override
    def __iter__(self) -> Iterator[T]:  # ty: ignore[invalid-method-override]
        """
        Iterate over the contents.

        The parent Pydantic model would otherwise yield field name and value pairs.
        """
        return iter(self.data)

    @override
    def __len__(self) -> int:
        """How many elements this shape holds, which is what a sequence counts."""
        return len(self.data)

    @override
    def __repr__(self) -> str:
        """Show the contents, since the fields are one sequence under one name."""
        return f"{type(self).__name__}(data={list(self.data)!r})"

    @overload
    def __getitem__(self, index: int) -> T: ...
    @overload
    def __getitem__(self, index: slice) -> Sequence[T]: ...

    def __getitem__(self, index: int | slice) -> T | Sequence[T]:
        """
        Read the element or elements at a position.

        A position counted from the end resolves against the elements held, never the padding.
        """
        return self.data[index]

    @overload
    def __setitem__(self, index: int, value: T) -> None: ...
    @overload
    def __setitem__(self, index: slice, value: Sequence[T]) -> None: ...

    def __setitem__(self, index: int | slice, value: T | Sequence[T]) -> None:
        """Replace the element(s) at the index, validating each new element."""
        self._begin_mutation()
        if isinstance(index, slice):
            elements = [self._validate_element(v) for v in cast("Sequence[T]", value)]
            # A step of anything but one resizes nothing, so the held count stands.
            # The store below refuses a mismatched count with the error a plain list raises.
            held = len(self.data)
            start, stop, step = index.indices(held)
            selected = len(range(start, stop, step))
            self._validate_length(held - selected + len(elements) if step == 1 else held)
            self._mutable_data[index] = elements
        else:
            self._mutable_data[index] = self._validate_element(value)

    @property
    def _mutable_data(self) -> list[T]:
        """
        The contents as the list they are stored in, for a mutator to write through.

        Validation always returns a list, and a shape holding anything else never asks here.
        """
        return cast("list[T]", self.data)

    @classmethod
    def _input_expectation(cls) -> str:
        """
        How this shape names the input it accepts, for the error a refusal raises.

        A shape declaring an element type names it, since "iterable of Uint8" says more.
        """
        return "iterable"

    @classmethod
    def _shape_input(cls, raw_input: Any) -> Sequence[Any]:
        """
        Normalize a validator input into a length-checkable sequence.

        A list or tuple passes through, and any other iterable materializes into one.
        A string or a byte string is refused, since iterating one yields characters or ints.

        Raises:
            SSZTypeError: When the input is a string, bytes, or non-iterable.
        """
        if isinstance(raw_input, (list, tuple)):
            return raw_input
        if isinstance(raw_input, (str, bytes, bytearray)):
            raise SSZTypeError(
                TypeFault.WRONG_TYPE,
                expected=cls._input_expectation(),
                got=type(raw_input).__name__,
            )
        if hasattr(raw_input, "__iter__"):
            return list(raw_input)
        raise SSZTypeError(TypeFault.WRONG_TYPE, expected="iterable", got=type(raw_input).__name__)

    @classmethod
    def _validate_element(cls, value: Any) -> Any:
        """
        Validate one incoming element by the family's construction rule.

        Each family implements it with the rule its data validator applies at construction.
        """
        raise NotImplementedError

    @classmethod
    def _validate_length(cls, length: int) -> None:
        """
        Check a prospective element count against whatever bound the shape declares.

        LENGTH pins an exact count, LIMIT bounds one, and a progressive shape declares neither.

        Raises:
            SSZValueError: When a pinned count is not met exactly.
            SSZValueError: When a bounded count is exceeded.
        """
        if cls.LENGTH is not None and length != cls.LENGTH:
            raise SSZValueError(
                ValueFault.COUNT,
                type=cls.__name__,
                expected=cls.LENGTH,
                actual=length,
                unit=cls.UNIT,
            )
        if cls.LIMIT is not None and length > cls.LIMIT:
            raise SSZValueError(
                ValueFault.LIMIT,
                type=cls.__name__,
                limit=cls.LIMIT,
                actual=length,
                unit=cls.UNIT,
            )
