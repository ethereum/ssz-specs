"""
SSZ vector and list collections.

Three sequence shapes are defined by the SSZ spec, the third added by EIP-7916:

- A vector holds exactly LENGTH elements of one declared type.
- A list holds between zero and LIMIT elements of one declared type.
- A progressive list holds any number of elements of one declared type.

The encoding shape follows from the element type:

- Fixed-size elements share one known width, and pack back-to-back.
- Variable-size elements are prefixed by a table of uint32 byte offsets.

The table takes 4 bytes per element, so the first offset is 4 * N.

Three variable-size bodies of widths 5, 3 and 7 encode to 27 bytes:

    bytes 0..3   : off_0 = 12   (first body starts at byte 12)
    bytes 4..7   : off_1 = 17
    bytes 8..11  : off_2 = 20
    bytes 12..16 : body_0       (5 bytes)
    bytes 17..19 : body_1       (3 bytes)
    bytes 20..26 : body_2       (7 bytes)
"""

import io
from abc import ABC
from collections.abc import Iterable, Mapping, Sequence
from itertools import pairwise
from typing import IO, Any, ClassVar, Self, cast, overload, override

from pydantic import Field, field_serializer, field_validator

from ssz.byte_arrays import ByteVector
from ssz.exceptions import SSZError, SSZTypeError, SSZValueError, TypeFault, ValueFault
from ssz.ssz_base import (
    BYTES_PER_LENGTH_OFFSET,
    SSZCollection,
    SSZModel,
    SSZType,
)
from ssz.uint import Uint32


class _SSZSequence[T: SSZType](SSZCollection[T], ABC):
    """
    Shared scaffolding for the three SSZ sequence shapes.

    - All of them store their elements in one field.
    - All of them share one input rule, one count rule, and one coercion rule.
    - All of them share the offset-table reader and writer.

    The element type is inferred from the generic parameter, once per subclass.
    """

    ELEMENT_TYPE: ClassVar[type[SSZType]]
    """SSZ type of every element, inferred from the generic parameter."""

    IMMUTABLE_ELEMENTS: ClassVar[bool] = False
    """Whether elements are immutable, so one object can be shared across positions and copies."""

    data: Sequence[T] = Field(default_factory=list[T])
    """The elements, stored as a list once validated."""

    @classmethod
    def __pydantic_init_subclass__(cls, **kwargs: Any) -> None:
        """Read the element type from the generic parameter, then classify it."""
        super().__pydantic_init_subclass__(**kwargs)

        # A shape naming its element type by hand has nothing left to infer.
        if "ELEMENT_TYPE" not in cls.__dict__:
            for base in (cls, *cls.__bases__):
                # An empty default skips bases that were never made generic.
                metadata = getattr(base, "__pydantic_generic_metadata__", {})

                # Bases outside the sequence hierarchy carry no element type.
                origin = metadata.get("origin")
                if not (isinstance(origin, type) and issubclass(origin, _SSZSequence)):
                    continue

                # A bare TypeVar means this layer is abstract, so it is skipped.
                inferred = next(
                    (
                        argument
                        for argument in metadata.get("args", ())
                        if isinstance(argument, type) and issubclass(argument, SSZType)
                    ),
                    None,
                )
                if inferred is not None:
                    cls.ELEMENT_TYPE = inferred
                    break

        # Asked once here, because the vector default and the deep copy both need it.
        if (element_type := getattr(cls, "ELEMENT_TYPE", None)) is not None:
            cls.IMMUTABLE_ELEMENTS = issubclass(element_type, (int, bytes))

    @classmethod
    def _check_declaration(cls) -> None:
        """
        Refuse a shape that has not declared what it needs to hold a value.

        Raises:
            SSZTypeError: When the element type was never declared.
        """
        if not hasattr(cls, "ELEMENT_TYPE"):
            raise SSZTypeError(TypeFault.UNDECLARED, type=cls.__name__, requirement="ELEMENT_TYPE")

    @classmethod
    @override
    def _input_expectation(cls) -> str:
        """Name the element type in a refusal, since a sequence declares one."""
        return f"iterable of {cls.ELEMENT_TYPE.__name__}"

    @field_validator("data", mode="before")
    @classmethod
    def _coerce_and_validate(cls, raw_input: Any) -> list[SSZType]:
        """Shape the input, check the element count, then coerce every element."""
        cls._check_declaration()

        # Strings and non-iterables are refused, and a generator is materialized.
        elements = cls._shape_input(raw_input)

        # Checked before coercion, so an oversized input reports the capacity it broke.
        cls._validate_length(len(elements))

        # An element already of the declared class is settled without a call.
        # Whole sequences of them arrive here whenever a value is revalidated.
        element_type = cls.ELEMENT_TYPE
        coerce = cls._validate_element
        return [
            element if type(element) is element_type else coerce(element) for element in elements
        ]

    @classmethod
    @override
    def _validate_element(cls, value: Any) -> SSZType:
        """
        Coerce one value into the declared element type.

        The last two arms are what this type's own JSON rendering produces.
        Accepting them is what makes that rendering readable back in:

            Vector[Point]    ->  {"data": [{"x": 1, "y": 2}]}
            Vector[Bytes4]   ->  {"data": ["0x01020304"]}

        Each is as narrow as the rendering it mirrors.
        So a hex string with no prefix stays refused.

        Raises:
            SSZError: The refusal the element type itself raised, where it raised one.
            SSZTypeError: When the class is unrelated, or a foreign refusal named it.
        """
        element_type = cls.ELEMENT_TYPE
        element_class = type(value)

        # An identity check on two type objects, not a walk of an abstract base.
        if element_class is element_type:
            return value

        # Past here the class is accepted, so a failure is about the value's contents.
        try:
            # An ancestor class is a raw value to wrap: an int for a uint.
            if issubclass(element_type, element_class):
                return element_type(value)

            # A mapping is how a Pydantic-backed element renders, and how it reads back.
            if isinstance(value, Mapping) and issubclass(element_type, SSZModel):
                return element_type.model_validate(value)

            # A 0x-prefixed string is how a fixed byte array renders, and nothing else.
            if (
                isinstance(value, str)
                and value.startswith("0x")
                and issubclass(element_type, ByteVector)
            ):
                return element_type(value)

        # An SSZ refusal already says what broke and why, so it is caught first.
        except SSZError:
            raise

        # Anything else, a pydantic refusal included, says only that the value did not fit.
        except (TypeError, ValueError) as exception:
            raise SSZTypeError(
                TypeFault.WRONG_TYPE,
                expected=element_type.__name__,
                got=element_class.__name__,
            ) from exception

        raise SSZTypeError(
            TypeFault.WRONG_TYPE, expected=element_type.__name__, got=element_class.__name__
        )

    def _write_variable_payload(self, stream: IO[bytes]) -> int:
        """
        Write the offset table, then the element bodies.

        An offset is only known once every body before it has been measured.
        A forward-only stream cannot revisit an earlier slot, so bodies are buffered.

        Returns:
            Total bytes written, which is also the final offset.
        """
        bodies = io.BytesIO()

        # The first offset points just past the whole table.
        offset = len(self.data) * BYTES_PER_LENGTH_OFFSET

        # An offset written here comes from arithmetic and could exceed the width.
        # Its range check is a real spec rule, while reading needs no such check.
        for element in self.data:
            Uint32(offset).serialize(stream)
            offset += element.serialize(bodies)

        stream.write(bodies.getvalue())
        return offset

    @classmethod
    def _read_offsets(cls, stream: IO[bytes], count: int) -> list[int]:
        """
        Read the given number of table entries, each a little-endian uint32.

        An offset is a byte position, not a value the spec gives a type to.
        So it is read as the plain integer it is compared and subtracted as.

        Raises:
            SSZValueError: When the stream ends before the table is complete.
        """
        width = count * BYTES_PER_LENGTH_OFFSET
        table = stream.read(width)
        if len(table) != width:
            raise SSZValueError(
                ValueFault.TRUNCATED, type=cls.__name__, expected=width, actual=len(table)
            )
        return [
            int.from_bytes(table[at : at + BYTES_PER_LENGTH_OFFSET], "little")
            for at in range(0, width, BYTES_PER_LENGTH_OFFSET)
        ]

    @classmethod
    def _read_elements(cls, stream: IO[bytes], spans: Iterable[int]) -> list[SSZType]:
        """Read one element per span, naming the position of the one that refuses."""
        elements: list[SSZType] = []
        for index, span in enumerate(spans):
            try:
                elements.append(cls.ELEMENT_TYPE.deserialize(stream, span))
            except SSZError as error:
                error.at(index)
                raise
        return elements

    @classmethod
    def _read_bodies(cls, stream: IO[bytes], offsets: list[int], scope: int) -> Self:
        """
        Read one body per offset, after checking the table closes over the budget.

        Appending the budget gives one boundary more than there are bodies.
        Consecutive pairs are then exactly the spans to read:

            offsets       12       17       20
            boundaries    12       17       20       27
            spans         12..17   17..20   20..27

        A pair that decreases is a body of negative width.
        The pair closed by the budget is a body reaching past the input.

        Each span is read from where the last stopped, so a short body shifts every later span.

        This is the only place that reads bodies.
        So a table cannot be read from without having been checked.

        Raises:
            SSZValueError:
                - When an offset is above the one after it.
                - When the last offset runs past the budget.
        """
        boundaries = [*offsets, scope]

        # The last pair is the only one closed by the budget rather than an offset.
        last = len(offsets) - 1

        for index, (start, end) in enumerate(pairwise(boundaries)):
            if end >= start:
                continue
            if index == last:
                error = SSZValueError(ValueFault.OFFSET_PAST_SCOPE, offset=start, scope=end)
            else:
                error = SSZValueError(ValueFault.OFFSET_UNORDERED, offset=start, next=end)
            error.at(index)
            raise error

        # Every element is already the declared type, and the caller settled the count.
        # So the value is built past validation rather than through it.
        return cls.model_construct(
            _fields_set={"data"},
            data=cls._read_elements(stream, (end - start for start, end in pairwise(boundaries))),
        )

    @override
    def __len__(self) -> int:
        """Return the number of elements in the sequence."""
        return len(self.data)

    @property
    def elements(self) -> list[T]:
        """A fresh list of the elements, which writing to never reaches this value."""
        return list(self.data)

    def __deepcopy__(self, memo: dict[int, Any] | None = None) -> Self:
        """A duplicate over the very same elements, none of which can be written to."""
        cls = type(self)

        # Sharing needs immutable elements and no other field to copy.
        if not cls.IMMUTABLE_ELEMENTS or len(cls.model_fields) != 1:
            return super().__deepcopy__(cast("dict[int, Any]", memo))
        return cls.model_construct(
            _fields_set=set(self.__pydantic_fields_set__), data=list(self.data)
        )

    @field_serializer("data", when_used="json")
    def _serialize_data(self, value: Sequence[T]) -> list[Any]:
        """Render the elements as a JSON-friendly list."""
        # Pydantic does not flatten SSZ leaf types into JSON primitives on its own.
        serialized_elements: list[Any] = []
        for element in value:
            if isinstance(element, ByteVector):
                serialized_elements.append("0x" + element.hex())

            # A boolean also subclasses int, and is excluded so it stays true or false.
            elif isinstance(element, int) and not isinstance(element, bool):
                serialized_elements.append(int(element))

            # Nested containers and primitives are left to Pydantic.
            else:
                serialized_elements.append(element)
        return serialized_elements


class Vector[T: SSZType](_SSZSequence[T]):
    """
    Fixed-length SSZ sequence, holding exactly LENGTH elements of one type.

    Subclasses declare their length in the class body.
    The element type comes from the generic parameter.

    Three Uint16 values encode as six raw bytes:

        bytes 0..1 : 67 45   (= 0x4567, little-endian)
        bytes 2..3 : 23 01   (= 0x0123)
        bytes 4..5 : ef cd   (= 0xCDEF)

    Built from nothing, a vector holds the element default at every position.
    An element type with no default leaves it with none.

    A range of a vector is a plain sequence, holding too few elements to be one.
    """

    LENGTH: ClassVar[int | None]
    """Exact number of elements, fixed at the type level."""

    @classmethod
    def __pydantic_init_subclass__(cls, **kwargs: Any) -> None:
        """
        Refuse a capacity no vector has, then give the elements their default.

        Raises:
            SSZTypeError: When the shape declares a bound, which a vector has none of.
            SSZTypeError: When the declared length is zero or negative.
        """
        super().__pydantic_init_subclass__(**kwargs)

        # The count is pinned, so a bound is a second count rule the tree never reads.
        if cls.LIMIT is not None:
            raise SSZTypeError(TypeFault.NOT_ENTITLED, type=cls.__name__, capacity="LIMIT")

        # An abstract layer keeps the empty default it inherits.
        # Building a value from it fails its own declaration check instead.
        if not hasattr(cls, "ELEMENT_TYPE") or cls.LENGTH is None:
            return

        # The spec writes a vector as Vector[type, N] with N > 0.
        # A vector of no elements has no offset table to read a body from.
        if cls.LENGTH < 1:
            raise SSZTypeError(TypeFault.VECTOR_EMPTY, length=cls.LENGTH)

        element_type, length = cls.ELEMENT_TYPE, cls.LENGTH
        if cls.IMMUTABLE_ELEMENTS:
            shared = element_type()
            cls.model_fields["data"].default_factory = lambda: [shared] * length

        # A mutable element needs one instance per position.
        # Sharing one would make a write to position 0 visible at every position.
        else:
            cls.model_fields["data"].default_factory = lambda: [
                element_type() for _ in range(length)
            ]

        # The compiled schema holds the previous factory until it is rebuilt.
        cls.model_rebuild(force=True)

    @classmethod
    @override
    def _check_declaration(cls) -> None:
        """
        A vector also needs its exact count, which no input can supply.

        Raises:
            SSZTypeError: When the element type or the length was never declared.
        """
        if not hasattr(cls, "ELEMENT_TYPE") or cls.LENGTH is None:
            raise SSZTypeError(
                TypeFault.UNDECLARED, type=cls.__name__, requirement="ELEMENT_TYPE and LENGTH"
            )

    KIND = "vector"

    @classmethod
    @override
    def fixed_size(cls) -> int | None:
        """The element width once per position, and no width at all where an element has none."""
        element_width = cls.ELEMENT_TYPE.fixed_size()
        return None if element_width is None else element_width * cls.declared_length()

    @override
    def serialize(self, stream: IO[bytes]) -> int:
        """Write the SSZ encoding to a binary stream, and return the byte count."""
        if self.ELEMENT_TYPE.is_fixed_size():
            return sum(element.serialize(stream) for element in self.data)
        return self._write_variable_payload(stream)

    @classmethod
    @override
    def deserialize(cls, stream: IO[bytes], scope: int) -> Self:
        """
        Read one vector from a binary stream within the given byte budget.

        Raises:
            SSZValueError: When the budget or any offset is inconsistent.
        """
        # Fixed-size case: the budget is the element width times the count, exactly.
        if cls.is_fixed_size():
            element_byte_length = cls.ELEMENT_TYPE.get_byte_length()
            expected_total = element_byte_length * cls.declared_length()
            if scope != expected_total:
                raise SSZValueError(
                    ValueFault.SCOPE, type=cls.__name__, expected=expected_total, actual=scope
                )
            return cls.model_construct(
                _fields_set={"data"},
                data=cls._read_elements(stream, [element_byte_length] * cls.declared_length()),
            )

        # Variable-size case: the count is known, so the table's width is known too.
        expected_first = cls.declared_length() * BYTES_PER_LENGTH_OFFSET
        if scope < expected_first:
            raise SSZValueError(
                ValueFault.SCOPE_TOO_SMALL,
                type=cls.__name__,
                expected=expected_first,
                actual=scope,
            )

        # The declared length is positive, so there is always a first offset to read.
        offsets = cls._read_offsets(stream, cls.declared_length())

        # The first body starts right after the table.
        # Any other value leaves a gap or an overlap, so one value could encode twice.
        if offsets[0] != expected_first:
            raise SSZValueError(ValueFault.FIRST_OFFSET, actual=offsets[0], expected=expected_first)
        return cls._read_bodies(stream, offsets, scope)


class _SSZList[T: SSZType](_SSZSequence[T]):
    """
    Shared behavior for the two variable-length SSZ sequence shapes.

    Both encode identically, and differ in exactly two places:

    - The element-count rule, which is the bound each one declares, or none at all.
    - The Merkle tree shape, which lives in the merkleization module.
    """

    def append(self, value: T) -> None:
        """
        Add one element at the end, coerced as construction coerces one.

        Raises:
            SSZValueError: When the resulting count exceeds a declared capacity.
        """
        self._begin_mutation()

        # Coerced before the count is checked, so a bad value is reported as one.
        element = self._validate_element(value)
        self._validate_length(len(self.data) + 1)
        self._mutable_data.append(cast("T", element))

    def pop(self) -> T:
        """
        Remove and return the last element.

        Raises:
            IndexError: When the sequence is empty.
        """
        self._begin_mutation()
        return self._mutable_data.pop()

    @overload
    def __getitem__(self, index: int) -> T: ...
    @overload
    def __getitem__(self, index: slice) -> Self: ...

    @override
    def __getitem__(self, index: int | slice) -> T | Self:
        """Read the element or elements at a position, a range giving this same type."""
        # A range goes through the constructor.
        # So a bounded list still refuses one that would overflow it.
        if isinstance(index, slice):
            return type(self)(data=self.data[index])
        return self.data[index]

    def __add__(self, other: Any) -> Self:
        """Concatenate with another sequence, the left operand deciding the type."""
        match other:
            case _SSZList():
                new_data = (*self.data, *other.data)
            case list() | tuple():
                new_data = (*self.data, *other)

            # Anything else lets the right operand try the reflected operation.
            case _:
                return NotImplemented

        # Built through the constructor, so a bounded list still rejects an overflow.
        return type(self)(data=new_data)

    KIND = "list"

    @classmethod
    @override
    def fixed_size(cls) -> None:
        """No width: the element count varies from one instance to the next."""
        return None

    @override
    def serialize(self, stream: IO[bytes]) -> int:
        """Write the SSZ encoding to a binary stream, and return the byte count."""
        # No length prefix either way.
        # The count is recovered on decode from the budget, or from the table.
        if self.ELEMENT_TYPE.is_fixed_size():
            return sum(element.serialize(stream) for element in self.data)
        return self._write_variable_payload(stream)

    @classmethod
    @override
    def deserialize(cls, stream: IO[bytes], scope: int) -> Self:
        """
        Read one sequence from a binary stream within the given byte budget.

        A declared capacity is checked as soon as the count is known.
        A shape without one is still bounded by the budget.
        So neither can be driven to allocate beyond its input.

        Raises:
            SSZTypeError: When the shape has not declared what it holds.
            SSZValueError: When the budget or any offset is malformed, or the recovered
                count exceeds a declared capacity.
        """
        # A decode is built past the validator that asks this, so the decoder asks it.
        cls._check_declaration()

        # A negative budget divides into a negative count, which reads as no elements at all.
        if scope < 0:
            raise SSZValueError(ValueFault.SCOPE_NEGATIVE, scope=scope)

        if scope == 0:
            # A count of zero is still a count, so no exit here returns an unchecked one.
            cls._validate_length(0)
            return cls.model_construct(_fields_set={"data"}, data=[])

        # Fixed-size case: the count is the budget divided by the element width.
        if cls.ELEMENT_TYPE.is_fixed_size():
            element_size = cls.ELEMENT_TYPE.get_byte_length()
            if scope % element_size != 0:
                raise SSZValueError(ValueFault.SCOPE_UNDIVIDED, scope=scope, width=element_size)
            num_elements = scope // element_size

            # Checked here, so an over-capacity payload reports the capacity it broke.
            cls._validate_length(num_elements)
            return cls.model_construct(
                _fields_set={"data"},
                data=cls._read_elements(stream, [element_size] * num_elements),
            )

        # Variable-size case: the first offset is the table's own width.
        # So it gives both where the bodies begin and how many there are.
        if scope < BYTES_PER_LENGTH_OFFSET:
            raise SSZValueError(
                ValueFault.SCOPE_TOO_SMALL,
                type=cls.__name__,
                expected=BYTES_PER_LENGTH_OFFSET,
                actual=scope,
            )
        first_offset = cls._read_offsets(stream, 1)[0]

        # Zero is contradictory: no elements, yet one body spanning the whole budget.
        if first_offset < BYTES_PER_LENGTH_OFFSET:
            raise SSZValueError(
                ValueFault.OFFSET_BELOW_TABLE,
                offset=first_offset,
                width=BYTES_PER_LENGTH_OFFSET,
            )
        if first_offset % BYTES_PER_LENGTH_OFFSET != 0:
            raise SSZValueError(
                ValueFault.OFFSET_UNALIGNED,
                offset=first_offset,
                width=BYTES_PER_LENGTH_OFFSET,
            )
        if first_offset > scope:
            raise SSZValueError(ValueFault.OFFSET_PAST_SCOPE, offset=first_offset, scope=scope)

        num_elements = first_offset // BYTES_PER_LENGTH_OFFSET
        cls._validate_length(num_elements)

        # The first offset is read already, so only the rest of the table remains.
        offsets = [first_offset, *cls._read_offsets(stream, num_elements - 1)]
        return cls._read_bodies(stream, offsets, scope)


class List[T: SSZType](_SSZList[T]):
    """Variable-length SSZ sequence holding zero to LIMIT elements of one type."""

    LIMIT: ClassVar[int | None]
    """Maximum number of elements allowed."""

    @classmethod
    def __pydantic_init_subclass__(cls, **kwargs: Any) -> None:
        """Refuse a bound no list can have, and an exact count that is a vector's rule."""
        super().__pydantic_init_subclass__(**kwargs)

        # A pinned count is a vector's rule, and the tree here is laid out from the bound.
        if cls.LENGTH is not None:
            raise SSZTypeError(TypeFault.NOT_ENTITLED, type=cls.__name__, capacity="LENGTH")

        # A bound below zero leaves the type no value at all, the empty one included.
        if cls.LIMIT is not None and cls.LIMIT < 0:
            raise SSZTypeError(TypeFault.LIMIT_NEGATIVE, limit=cls.LIMIT)

    @classmethod
    @override
    def _check_declaration(cls) -> None:
        """
        A bounded list also needs the bound it enforces.

        Raises:
            SSZTypeError: When the element type or the limit was never declared.
        """
        if not hasattr(cls, "ELEMENT_TYPE") or cls.LIMIT is None:
            raise SSZTypeError(
                TypeFault.UNDECLARED, type=cls.__name__, requirement="ELEMENT_TYPE and LIMIT"
            )


class ProgressiveList[T: SSZType](_SSZList[T]):
    """
    Variable-length SSZ sequence with no capacity, per EIP-7916.

    It encodes to the same bytes as a bounded list, and only the Merkle trees differ.
    """

    @classmethod
    def __pydantic_init_subclass__(cls, **kwargs: Any) -> None:
        """Refuse a capacity, there being no such thing here."""
        super().__pydantic_init_subclass__(**kwargs)

        # EIP-7916 gives this shape no capacity, and its tree grows with what it holds.
        if cls.LENGTH is not None:
            raise SSZTypeError(TypeFault.NOT_ENTITLED, type=cls.__name__, capacity="LENGTH")
        if cls.LIMIT is not None:
            raise SSZTypeError(TypeFault.NOT_ENTITLED, type=cls.__name__, capacity="LIMIT")
