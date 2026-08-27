"""Abstract bases for the SSZ type system."""

import io
from abc import ABC, abstractmethod
from collections.abc import Iterator, Sequence
from copy import copy as shallow_copy
from typing import IO, TYPE_CHECKING, Any, ClassVar, Final, Self, cast, final, overload, override

from pydantic import ConfigDict

from ssz.base import StrictBaseModel
from ssz.exceptions import (
    SSZDefinitionError,
    SSZLengthError,
    SSZLimitError,
    SSZSerializationError,
    SSZTypeError,
    SSZTypeMismatch,
)

if TYPE_CHECKING:
    # The name is wanted for one annotation, which is never evaluated.
    # The method that carries it explains why the import cannot happen at runtime.
    from ssz.merkleization import Root

BYTES_PER_LENGTH_OFFSET: Final = 4
"""Width of an SSZ offset prefixing each variable-size element.

Encoded as a uint32 in little-endian byte order."""

_CAPACITY_NAMES: Final = ("LENGTH", "LIMIT")
"""The class attributes a shape declares its element count with.

An exact count and an upper bound are spelled differently, and no shape declares both."""

_COLD_CACHE: Final = {"_version": 0, "_root_memo": None}
"""What each cache slot holds before anything has touched it.

Filled on first read, so decoding pays nothing and a copied value starts cold rather
than stale.
"""


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

    LENGTH: ClassVar[int | None] = None
    """Exact element count, or None where the shape declares none.

    A shape that pins its count overrides this with an integer and narrows the annotation."""

    LIMIT: ClassVar[int | None] = None
    """Maximum element count, read the same way: None means no count, never a count of zero."""

    def __init_subclass__(cls, **kwargs: Any) -> None:
        """
        Narrow a declared capacity, and refuse a root of the type's own, where each is declared.

        A capacity may be written with a typed value.
        Requiring a cast at every declaration would therefore mean casting almost all of them:

            class Attestations(List[Attestation]):
                LIMIT = MAX_ATTESTATIONS   # already a Uint64

        Narrowing keeps every count this library computes, compares and reports a plain
        integer, whatever the declaration was written at.

        A capacity that is not an integer at all is refused here as well.
        Declaration is the only place that refusal can be useful:

            LIMIT = 4.7   ->  refused, rather than resolving to a chunk count nobody wrote
            LIMIT = "4"   ->  refused, rather than reporting a wrong element count later

        # Refusing a root of its own

        One value has one root, and a type does not get to state a second one.

        Two callers reach a nested root through the module-level function, not through a method.

        - A layout roots each of its leaves with it.
        - A proof roots one addressed node with it.

        A type declaring a root of its own would answer only the callers that spell it
        as a method.

        - The tree above it would go on answering with the spec's own root.
        - So one value would carry two roots, and neither would report the other.
        - A proof built against one would fail against the other, with no diagnostic.

        Only this one name is refused, so subclassing itself stays untouched:

            class Root(Chunk)                               ->  fine, declares nothing of its own
            class Fingerprint(Root): def is_all_ones(...)   ->  fine, declares another method
            class Fast(Root): def hash_tree_root(...)       ->  refused, a method of its own
            class Fast(Mixin, Root)                         ->  refused, a method from outside
            class Odd(Container): hash_tree_root: Uint16    ->  refused, a field of that name

        The last two matter because neither one appears in the class body being created.
        A field shadows the method on every instance, and a mixin wins the lookup ahead of it.

        Raises:
            SSZTypeMismatch: When a declared capacity is not an integer.
            SSZTypeMismatch: When a declared capacity is a boolean, which counts nothing.
            SSZDefinitionError: When a type declares a hash_tree_root of its own.
        """
        super().__init_subclass__(**kwargs)

        # Reading the resolved attribute covers every way a type can answer for itself:
        # a method of its own, a property, or one inherited from outside this type system.
        #
        # A field of that name shadows the method on each instance rather than on the class,
        # which leaves the resolved attribute looking untouched.
        # So the annotations this class declares are read as well.
        if (
            cls.hash_tree_root is not SSZType.hash_tree_root
            or "hash_tree_root" in cls.__annotations__
        ):
            raise SSZDefinitionError(cls.__name__, "no hash_tree_root of its own")

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

    @classmethod
    def empty(cls) -> Self:
        """
        Build a value holding nothing.

        Returns:
            A fresh default value.

        Raises:
            SSZTypeError: When the type has no default value.
        """
        return cls.default()

    def copy(self) -> Self:
        """
        An independent duplicate of this value, at every depth.

        A value that cannot change already satisfies that, so the three immutable shapes
        hand themselves back.

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

    @final
    def hash_tree_root(self) -> "Root":
        """
        Merkle root of this value.

        The root is the top node of the binary tree a value merkleizes into.
        It stands in for the whole value, so a proof is checked against it.

        The declared shape lays that tree out, so contents alone do not decide the root.
        The same three numbers reach four roots, each row below changing one thing:

            shape                    value      root
            Vector[Uint8], LENGTH 3  [1, 2, 3]  01 02 03 00 ... 00
            List[Uint8], LIMIT 3     [1, 2, 3]  14 9f 1a fc ... b9
            List[Uint64], LIMIT 3    [1, 2, 3]  8d fc c0 c6 ... 93
            List[Uint64], LIMIT 8    [1, 2, 3]  7e 0a de cc ... 59

        - A vector fixes its count, so row one is the packed bytes themselves.
        - A list does not, so row two hashes those same bytes against a 3.
        - Row three packs into 24 bytes instead of 3, so its leaf differs.
        - Row four bounds a wider tree, so every leaf sits one level deeper.
        - A capacity reaches that tree only through the width it rounds up to.

        A root is remembered until the value changes.
        A value mutated since it was last rooted is hashed again.
        One left alone answers with the bytes it answered with before.

        A mutation counter on each model guards the memo.
        The merkleization module decides what counts as changed.

        The tree rules live with the merkleization primitives, not here.
        The module-level function is the form the spec defines.
        It is also the only form reaching plain bytes, which merkleize and carry no method.

        Returns:
            The root of this value's Merkle tree.

        Raises:
            SSZTypeError: When the type has no registered merkleization rule.
        """
        # Merkleization dispatches on every SSZ type, so its module imports this one.
        # A root is an SSZ type too, so the name is bound per call rather than at import.
        from ssz.merkleization import hash_tree_root

        return hash_tree_root(self)

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

    Every mutation raises this value's version.
    A remembered root is reused only while every version below it is unchanged.
    """

    __slots__ = ("_root_memo", "_version")
    """The mutation counter and the remembered root, one pair per value.

    Slots, because a field would serialize and a private attribute would take part in
    equality. A slot is invisible to both, which is what a cache has to be.
    """

    if TYPE_CHECKING:
        # Declared for the type checker only. Writing these as annotations in the class
        # body would make Pydantic read them as private attributes, which is the shape
        # the slots above exist to avoid. This block never runs, so nothing is declared.
        _version: ClassVar[int]
        _root_memo: ClassVar["tuple[object, Root] | None"]

    MUTABLE: ClassVar[bool] = True
    """Whether instances accept mutation. Set False on a subclass to freeze it."""

    def __hash__(self) -> int:
        """Hash by Merkle tree root, which is what equality compares."""
        return hash(self.hash_tree_root())

    def _begin_mutation(self) -> None:
        """
        Admit one mutation, refusing it outright on an immutable type.

        Every mutator passes here, so invalidation is one name to grep for.
        Raising the version retires any remembered root. It only ever goes up.
        Raising it before validation means a failed mutation costs a recomputation
        rather than a stale root.

        Raises:
            SSZTypeError: When the type declares itself immutable.
        """
        if not type(self).MUTABLE:
            raise SSZTypeError(f"{type(self).__name__} is immutable")
        # Written past this class's own __setattr__, which is the door itself.
        object.__setattr__(self, "_version", self._version + 1)

    # Hidden from type checkers: a visible __setattr__ typed to accept Any
    # would exempt every field assignment from static checking against the
    # declared field types.
    # A visible fallback returning Any would make
    # every misspelled attribute resolve instead of being reported.
    if not TYPE_CHECKING:  # pragma: no cover

        def __setattr__(self, name: str, value: Any) -> None:
            """Pass the mutation door, then assign and validate as usual."""
            self._begin_mutation()
            super().__setattr__(name, value)

        def __getattr__(self, name: str) -> Any:
            """Fill a cache slot on first read, leaving every other name to Pydantic."""
            # An unset slot raises before this method is reached, so the common case of
            # a slot already filled never gets here at all.
            if name in _COLD_CACHE:
                cold = _COLD_CACHE[name]
                object.__setattr__(self, name, cold)
                return cold
            return super().__getattr__(name)

    @override
    def copy(self) -> Self:  # ty: ignore[invalid-method-override]
        """
        An independent duplicate of this value, at every depth.

        Every field holding something writable is duplicated, stopping at the immutable
        leaves. Entries are replaced in the field dictionary rather than assigned, because
        an immutable type refuses assignment and assignment would revalidate.

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


class SSZCollection[T](SSZModel, Sequence[T]):
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

    model_config = ConfigDict(validate_assignment=True)

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

    # The narrower element type violates strict Liskov substitution, so it is suppressed.
    @override
    def __iter__(self) -> Iterator[T]:  # ty: ignore[invalid-method-override]
        """
        Iterate over the contents.

        The parent Pydantic model otherwise yields field name and value pairs.
        Yielding the contents instead is the intended collection behavior.
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

    @overload
    def __setitem__(self, index: int, value: T) -> None: ...
    @overload
    def __setitem__(self, index: slice, value: Sequence[T]) -> None: ...

    def __setitem__(self, index: int | slice, value: T | Sequence[T]) -> None:
        """Replace the element(s) at the index, validating each new element."""
        self._begin_mutation()
        if isinstance(index, slice):
            elements = [self._validate_element(v) for v in cast("Sequence[T]", value)]
            # The resulting count is arithmetic, so no copy is made to observe it.
            # A step of anything but one resizes nothing.
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

        - The field is declared a sequence, so any iterable is accepted on input.
        - Validation always returns a list, so a list is always what is stored.
        - A shape holding anything else overrides every mutator and never asks for this.
        """
        return cast("list[T]", self.data)

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
        if cls.LENGTH is not None and length != cls.LENGTH:
            raise SSZLengthError(cls.__name__, cls.LENGTH, length)
        if cls.LIMIT is not None and length > cls.LIMIT:
            raise SSZLimitError(cls.__name__, cls.LIMIT, length)
