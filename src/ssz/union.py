"""SSZ compatible union, per EIP-8016."""

from collections.abc import Callable, Mapping
from typing import IO, Any, ClassVar, Final, Self, override

from pydantic import ConfigDict, model_validator

from ssz.bitfields import BitList, BitVector, ProgressiveBitList
from ssz.boolean import Boolean
from ssz.byte_arrays import ByteList, ByteVector
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container, ProgressiveContainer
from ssz.exceptions import SSZError, SSZTypeError, SSZValueError, TypeFault, ValueFault
from ssz.ssz_base import SSZModel, SSZType
from ssz.uint import BaseUint, Uint8

MIN_SELECTOR: Final = 1
"""Lowest selector a union may declare, zero being reserved so an all-zero value names none."""

MAX_SELECTOR: Final = 127
"""Highest selector a union may declare, the high bit being reserved."""


class CompatibleUnion(SSZModel):
    """
    Tagged union whose options all merkleize into one tree shape, per EIP-8016.

    One tree position per field is what lets a proof verify against any option declaring it.
    """

    model_config = ConfigDict(frozen=True)

    KIND = "compatible union"

    OPTIONS: ClassVar[Mapping[int, type[SSZType]]]
    """Selector to type, one entry per variant the union admits."""

    selector: Uint8
    """Selector of the option this value holds."""

    data: SSZType
    """The value of the selected option."""

    @classmethod
    def __pydantic_init_subclass__(cls, **kwargs: Any) -> None:
        """
        Enforce the option rules on every declared union.

        Raises:
            SSZTypeError: When the options are missing, malformed, or not all of one shape.
        """
        super().__pydantic_init_subclass__(**kwargs)

        # Merkleization rests on every option sharing one shape, so the set must be known.
        if not hasattr(cls, "OPTIONS"):
            raise SSZTypeError(TypeFault.UNDECLARED, type=cls.__name__, requirement="OPTIONS")
        if not cls.OPTIONS:
            raise SSZTypeError(TypeFault.UNION_EMPTY)
        # A sequence of types would read its own entries as selectors.
        if not isinstance(cls.OPTIONS, Mapping):
            raise SSZTypeError(TypeFault.UNION_NOT_A_MAP, got=type(cls.OPTIONS).__name__)

        for selector, option in cls.OPTIONS.items():
            # A bool is an int subclass, so identity keeps true out of selector position.
            if type(selector) is not int:
                raise SSZTypeError(TypeFault.UNION_SELECTOR_TYPE, selector=selector)
            if not MIN_SELECTOR <= selector <= MAX_SELECTOR:
                raise SSZTypeError(
                    TypeFault.UNION_SELECTOR_RANGE,
                    selector=selector,
                    low=MIN_SELECTOR,
                    high=MAX_SELECTOR,
                )
            if not (isinstance(option, type) and issubclass(option, SSZType)):
                raise SSZTypeError(TypeFault.UNION_OPTION_TYPE, selector=selector)

        # Compatibility is not transitive, so every pair has to be asked, not just neighbours.
        options = list(cls.OPTIONS.items())
        for index, (selector, option) in enumerate(options):
            for other_selector, other in options[index + 1 :]:
                if not is_compatible(option, other):
                    raise SSZTypeError(
                        TypeFault.UNION_INCOMPATIBLE, selector=selector, other=other_selector
                    )

    @model_validator(mode="before")
    @classmethod
    def _reject_a_default(cls, raw_input: Any) -> Any:
        """Refuse the empty input that asks for a default, which this type does not have."""
        if raw_input == {}:
            raise SSZTypeError(TypeFault.NO_DEFAULT, type=cls.__name__)
        return raw_input

    @model_validator(mode="after")
    def _check_selected_option(self) -> Self:
        """
        Check that the value holds the option its selector names.

        Raises:
            SSZValueError: When the selector names no option.
            SSZTypeError: When the value is a type other than the one named.
        """
        # A value is built field by field, so its selector may name nothing at all.
        option = type(self).OPTIONS.get(int(self.selector))
        if option is None:
            raise SSZValueError(
                ValueFault.UNKNOWN_SELECTOR,
                selector=int(self.selector),
                type=type(self).__name__,
            )
        # A reader picks the tree shape from the selector, so the value must be that option.
        if not isinstance(self.data, option):
            raise SSZTypeError(
                TypeFault.WRONG_TYPE, expected=option.__name__, got=type(self.data).__name__
            )
        return self

    @classmethod
    @override
    def fixed_size(cls) -> None:
        """No width, even where every option shares one, since the selector is read per value."""
        return None

    @override
    def serialize(self, stream: IO[bytes]) -> int:
        """Write the selector byte, then the encoding of the option it names."""
        return self.selector.serialize(stream) + self.data.serialize(stream)

    @classmethod
    @override
    def deserialize(cls, stream: IO[bytes], scope: int) -> Self:
        """
        Read one union within the given byte budget, the selector leading.

        Raises:
            SSZValueError: When the budget holds no selector, or the selector names no option.
        """
        selector_width = Uint8.get_byte_length()
        if scope < selector_width:
            raise SSZValueError(ValueFault.NO_SELECTOR, scope=scope)

        selector = Uint8.deserialize(stream, selector_width)
        option = cls.OPTIONS.get(int(selector))
        if option is None:
            raise SSZValueError(
                ValueFault.UNKNOWN_SELECTOR, selector=int(selector), type=cls.__name__
            )

        # A refusal inside the option names the selector it was read under, as a path step.
        try:
            data = option.deserialize(stream, scope - selector_width)
        except SSZError as error:
            error.at(int(selector))
            raise
        return cls(selector=selector, data=data)


def is_compatible(left: type[SSZType], right: type[SSZType]) -> bool:
    """
    Whether two types merkleize into the same tree shape.

    Reflexive and symmetric, but not transitive.

    Two layouts may each agree with a third on the positions they share, and still clash.
    """
    # The spec's first rule, and the only answer available for a type declaring no shape.
    if left is right:
        return True

    # A byte array and a sequence of single bytes are one shape, so this outranks those rules.
    left_bytes, right_bytes = _byte_sequence(left), _byte_sequence(right)
    if left_bytes is not None or right_bytes is not None:
        return left_bytes == right_bytes

    # No shape is a subclass of another, so at most one claims a side and order does not matter.
    for shape, parameters_agree in _SHAPE_RULES.items():
        if issubclass(left, shape) or issubclass(right, shape):
            return (
                issubclass(left, shape)
                and issubclass(right, shape)
                and parameters_agree(left, right)
            )
    return False


def _byte_sequence(ssz_type: type[SSZType]) -> tuple[type[SSZType], int] | None:
    """The byte-array shape a type spells, either spelling, or None for any other shape."""
    element = getattr(ssz_type, "ELEMENT_TYPE", None)
    of_bytes = element is not None and issubclass(element, BaseUint) and element.BITS == Uint8.BITS
    if issubclass(ssz_type, ByteVector) or (of_bytes and issubclass(ssz_type, Vector)):
        return None if ssz_type.LENGTH is None else (Vector, ssz_type.LENGTH)
    if issubclass(ssz_type, ByteList) or (of_bytes and issubclass(ssz_type, List)):
        return None if ssz_type.LIMIT is None else (List, ssz_type.LIMIT)
    # A progressive list of bytes carries no capacity, so no byte array spells its shape.
    return None


def _capacities_agree(left: int | None, right: int | None) -> bool:
    """Whether two shapes pin the same count, a shape pinning none agreeing with nothing."""
    return left is not None and left == right


def _elements_agree(left: type[SSZType], right: type[SSZType]) -> bool:
    """Whether two sequence types both declare an element type, and compatible ones."""
    left_element = getattr(left, "ELEMENT_TYPE", None)
    right_element = getattr(right, "ELEMENT_TYPE", None)
    if left_element is None or right_element is None:
        return False
    return is_compatible(left_element, right_element)


def _fields_agree(left: type[Container], right: type[Container]) -> bool:
    """Whether two structs name the same fields in the same order, holding compatible types."""
    if len(left._FIELD_TYPES) != len(right._FIELD_TYPES):
        return False
    return all(
        left_name == right_name and is_compatible(left_type, right_type)
        for (left_name, left_type), (right_name, right_type) in zip(
            left._FIELD_TYPES, right._FIELD_TYPES, strict=True
        )
    )


def _layouts_agree(left: type[ProgressiveContainer], right: type[ProgressiveContainer]) -> bool:
    """
    Whether two field layouts place the fields they share alike.

    Two rules, each in one direction:

    - A position set in both must hold one field name, of compatible types.
    - A name set in both must sit at one position.

    The second does not follow from the first, since one name can sit at two positions:

        position     0        1        2
        (1, 0, 1)    amount   -        tag
        (0, 1, 1)    -        amount   tag

    A position set in only one layout is free, the other leaving a zero leaf there.
    """
    left_fields, right_fields = _fields_by_position(left), _fields_by_position(right)
    if left_fields is None or right_fields is None:
        return False

    # A proof addresses a position, so two names at one position would read as each other.
    for position, (name, field_type) in left_fields.items():
        if position not in right_fields:
            continue
        other_name, other_type = right_fields[position]
        if name != other_name or not is_compatible(field_type, other_type):
            return False

    # One name at two positions would send a single proof to two different leaves.
    right_positions = {name: position for position, (name, _) in right_fields.items()}
    return all(
        position == right_positions[name]
        for position, (name, _) in left_fields.items()
        if name in right_positions
    )


def _fields_by_position(
    ssz_type: type[ProgressiveContainer],
) -> dict[int, tuple[str, type[SSZType]]] | None:
    """Each set position of a layout mapped to the field standing there, or None if undeclared."""
    layout = getattr(ssz_type, "ACTIVE_FIELDS", None)
    if layout is None:
        return None
    # A field belongs to the n-th set position, so layout (1, 0, 1) puts its fields at 0 and 2.
    set_positions = (position for position, bit in enumerate(layout) if bit)
    return dict(zip(set_positions, ssz_type._FIELD_TYPES, strict=True))


def _options_agree(left: type[CompatibleUnion], right: type[CompatibleUnion]) -> bool:
    """Whether every option of one union fits every option of the other."""
    left_options = getattr(left, "OPTIONS", None)
    right_options = getattr(right, "OPTIONS", None)
    if left_options is None or right_options is None:
        return False
    # One crossing pair does not stand for the rest, the relation not being transitive.
    return all(
        is_compatible(left_option, right_option)
        for left_option in left_options.values()
        for right_option in right_options.values()
    )


_SHAPE_RULES: Final[Mapping[type[SSZType], Callable[[Any, Any], bool]]] = {
    # A basic type answers for its width alone, so a named subtype of one still fits.
    BaseUint: lambda left, right: left.BITS == right.BITS,
    Boolean: lambda _left, _right: True,
    # A bitfield answers for its capacity, and never across the three bitfield shapes.
    BitVector: lambda left, right: _capacities_agree(left.LENGTH, right.LENGTH),
    BitList: lambda left, right: _capacities_agree(left.LIMIT, right.LIMIT),
    # A progressive bitfield carries no capacity, so any two of them agree on one.
    ProgressiveBitList: lambda _left, _right: True,
    # A sequence answers for its capacity and its element type.
    Vector: lambda left, right: (
        _capacities_agree(left.LENGTH, right.LENGTH) and _elements_agree(left, right)
    ),
    List: lambda left, right: (
        _capacities_agree(left.LIMIT, right.LIMIT) and _elements_agree(left, right)
    ),
    ProgressiveList: _elements_agree,
    Container: _fields_agree,
    # A progressive container answers for the positions its layout sets, not its width.
    ProgressiveContainer: _layouts_agree,
    CompatibleUnion: _options_agree,
}
"""Every shape a value can take, mapped to what two types of it must share."""
