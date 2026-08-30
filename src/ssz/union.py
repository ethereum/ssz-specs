"""SSZ compatible union, per EIP-8016."""

from collections.abc import Mapping
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
"""Lowest selector a union may declare.

Zero is reserved against incomplete initialization, so an all-zero value names no option."""

MAX_SELECTOR: Final = 127
"""Highest selector a union may declare, the high bit being reserved."""


def _byte_vector_length(ssz_type: type[SSZType]) -> int | None:
    """Fixed byte count of a type that is a vector of bytes, or None for anything else."""
    if issubclass(ssz_type, ByteVector):
        return getattr(ssz_type, "LENGTH", None)
    element = getattr(ssz_type, "ELEMENT_TYPE", None)
    if issubclass(ssz_type, Vector) and element is not None and issubclass(element, BaseUint):
        return getattr(ssz_type, "LENGTH", None) if element.BITS == Uint8.BITS else None
    return None


def _byte_list_limit(ssz_type: type[SSZType]) -> int | None:
    """Capacity of a type that is a list of bytes, or None for anything else."""
    if issubclass(ssz_type, ByteList):
        return getattr(ssz_type, "LIMIT", None)
    element = getattr(ssz_type, "ELEMENT_TYPE", None)
    if issubclass(ssz_type, List) and element is not None and issubclass(element, BaseUint):
        return getattr(ssz_type, "LIMIT", None) if element.BITS == Uint8.BITS else None
    return None


def _progressive_layouts_agree(
    left: type[ProgressiveContainer], right: type[ProgressiveContainer]
) -> bool:
    """
    Whether two field layouts place their shared fields alike.

    Two rules, each in one direction:

    - A position set in both must hold one field name, of compatible types.
    - A name set in both must sit at one position.

    The second does not follow from the first, since one name can sit at two positions:

        position     0        1        2
        (1, 0, 1)    amount   -        tag
        (0, 1, 1)    -        amount   tag

    A position set in only one layout is free, the other leaving a zero leaf there.
    """
    left_fields = _fields_by_position(left)
    right_fields = _fields_by_position(right)

    # A proof addresses a position, so two names at one position would read as each other.
    for position, (name, field_type) in left_fields.items():
        if position not in right_fields:
            continue
        other_name, other_type = right_fields[position]
        if name != other_name or not is_compatible(field_type, other_type):
            return False

    # One name at two positions would send a single proof to two different leaves.
    left_positions = {name: position for position, (name, _) in left_fields.items()}
    right_positions = {name: position for position, (name, _) in right_fields.items()}
    return all(
        position == right_positions[name]
        for name, position in left_positions.items()
        if name in right_positions
    )


def _fields_by_position(
    ssz_type: type[ProgressiveContainer],
) -> dict[int, tuple[str, type[SSZType]]]:
    """Map each set position of a layout to the field name and type standing there."""
    # A field belongs to the n-th set position, not to position n.
    # Layout (1, 0, 1) puts the first field at 0 and the second at 2.
    set_positions = (i for i, bit in enumerate(ssz_type.ACTIVE_FIELDS) if bit)
    return {
        position: (name, field_type)
        for position, (name, field_type) in zip(set_positions, ssz_type._FIELD_TYPES, strict=True)
    }


def is_compatible(left: type[SSZType], right: type[SSZType]) -> bool:
    """
    Whether two types merkleize into the same tree shape.

    Args:
        left: One SSZ type.
        right: The type to compare it against.

    Returns:
        True when a proof about one verifies against the other.
    """
    # The spec's first rule.
    if left is right:
        return True

    # Basic types answer for their width alone, so a named subtype of one still fits.
    if issubclass(left, BaseUint) and issubclass(right, BaseUint):
        return left.BITS == right.BITS
    if issubclass(left, Boolean) and issubclass(right, Boolean):
        return True

    # A byte array is the spec's alias for a vector or list of single bytes, and fits it.
    left_bytes, right_bytes = _byte_vector_length(left), _byte_vector_length(right)
    if left_bytes is not None or right_bytes is not None:
        return left_bytes == right_bytes
    left_byte_list, right_byte_list = _byte_list_limit(left), _byte_list_limit(right)
    if left_byte_list is not None or right_byte_list is not None:
        return left_byte_list == right_byte_list

    # Bitfields answer for their capacity, and never across the three shapes.
    if issubclass(left, BitVector) or issubclass(right, BitVector):
        return (
            issubclass(left, BitVector)
            and issubclass(right, BitVector)
            and left.LENGTH == right.LENGTH
        )
    if issubclass(left, BitList) or issubclass(right, BitList):
        return (
            issubclass(left, BitList) and issubclass(right, BitList) and left.LIMIT == right.LIMIT
        )
    # A progressive bitlist carries no parameter, so any two of them agree.
    if issubclass(left, ProgressiveBitList) or issubclass(right, ProgressiveBitList):
        return issubclass(left, ProgressiveBitList) and issubclass(right, ProgressiveBitList)

    # Sequences answer for their capacity and their element type.
    if issubclass(left, Vector) or issubclass(right, Vector):
        return (
            issubclass(left, Vector)
            and issubclass(right, Vector)
            and left.LENGTH == right.LENGTH
            and is_compatible(left.ELEMENT_TYPE, right.ELEMENT_TYPE)
        )
    if issubclass(left, List) or issubclass(right, List):
        return (
            issubclass(left, List)
            and issubclass(right, List)
            and left.LIMIT == right.LIMIT
            and is_compatible(left.ELEMENT_TYPE, right.ELEMENT_TYPE)
        )
    if issubclass(left, ProgressiveList) or issubclass(right, ProgressiveList):
        return (
            issubclass(left, ProgressiveList)
            and issubclass(right, ProgressiveList)
            and is_compatible(left.ELEMENT_TYPE, right.ELEMENT_TYPE)
        )

    # A container answers for its field names, in order, and their types.
    if issubclass(left, Container) or issubclass(right, Container):
        return (
            issubclass(left, Container)
            and issubclass(right, Container)
            and list(left.model_fields) == list(right.model_fields)
            and all(
                is_compatible(left_type, right_type)
                for (_, left_type), (_, right_type) in zip(
                    left._FIELD_TYPES, right._FIELD_TYPES, strict=True
                )
            )
        )

    # A progressive container answers for the positions its layout sets, not its width.
    if issubclass(left, ProgressiveContainer) or issubclass(right, ProgressiveContainer):
        return (
            issubclass(left, ProgressiveContainer)
            and issubclass(right, ProgressiveContainer)
            and _progressive_layouts_agree(left, right)
        )

    # Two unions agree when every option of one fits every option of the other.
    if issubclass(left, CompatibleUnion) or issubclass(right, CompatibleUnion):
        return (
            issubclass(left, CompatibleUnion)
            and issubclass(right, CompatibleUnion)
            and all(
                is_compatible(left_option, right_option)
                for left_option in left.OPTIONS.values()
                for right_option in right.OPTIONS.values()
            )
        )

    return False


class CompatibleUnion(SSZModel):
    """
    Tagged union whose options all merkleize into one tree shape, per EIP-8016.

    Options are a map from selector to type, and a value carries the selector it holds:

        class Shape(CompatibleUnion):
            OPTIONS = {1: Square, 2: Circle}

        Shape(selector=1, data=Square(side=Uint16(0x1234), color=Uint8(0x42)))

    The selector leads the option's own encoding:

        01        34 12   42
        selector  side    color

    A field keeps one tree position across every option.
    A proof about it therefore verifies against any option that declares it.

    The selector is mixed into the root, so two options holding equal data do not root alike.

    A union is always variable-size, even where every option shares one width.

    A union has no default value, so a struct or a vector holding one has none either.

    The spec writes the options as a call, where they are a class attribute here:

        CompatibleUnion({1: Square, 2: Circle})
    """

    model_config = ConfigDict(frozen=True)

    OPTIONS: ClassVar[Mapping[int, type[SSZType]]]
    """Selector to type option, one entry per variant the union admits."""

    selector: Uint8
    """Selector of the option this value holds."""

    data: SSZType
    """The value of the selected option."""

    @classmethod
    def __pydantic_init_subclass__(cls, **kwargs: Any) -> None:
        """
        Enforce the option rules of EIP-8016 on every declared union.

        Raises:
            SSZTypeError: When no options are declared, the options are not a map, the
                options are empty, a selector is not a plain int in 1 through 127, an
                option is not an SSZ type, or two options merkleize differently.
        """
        super().__pydantic_init_subclass__(**kwargs)

        # Merkleization proves every option shares one shape, so the set must be known.
        if not hasattr(cls, "OPTIONS"):
            raise SSZTypeError(TypeFault.UNDECLARED, type=cls.__name__, requirement="OPTIONS")

        # A union with no option admits no value at all.
        if not cls.OPTIONS:
            raise SSZTypeError(TypeFault.UNION_EMPTY)

        # A sequence of types would read its own entries as selectors.
        if not isinstance(cls.OPTIONS, Mapping):
            raise SSZTypeError(TypeFault.UNION_NOT_A_MAP, got=type(cls.OPTIONS).__name__)

        for selector, option in cls.OPTIONS.items():
            # A selector is a plain int, and a typed one compares strictly against the bounds.
            if type(selector) is not int:
                raise SSZTypeError(TypeFault.UNION_SELECTOR_TYPE, selector=selector)

            if not MIN_SELECTOR <= selector <= MAX_SELECTOR:
                raise SSZTypeError(
                    TypeFault.UNION_SELECTOR_RANGE,
                    selector=selector,
                    low=MIN_SELECTOR,
                    high=MAX_SELECTOR,
                )

            # An option is a type this library can serialize, not any Python class.
            if not (isinstance(option, type) and issubclass(option, SSZType)):
                raise SSZTypeError(TypeFault.UNION_OPTION_TYPE, selector=selector)

        # Every pair is checked, since a clash between the second and third is as fatal as any.
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
        """
        Refuse to build a compatible union from nothing, which the spec makes an error.

        Raises:
            SSZTypeError: When no input is given at all.
        """
        # An empty input is the only way to ask for a default, and this type has none.
        if raw_input == {}:
            raise SSZTypeError(TypeFault.NO_DEFAULT, type=cls.__name__)
        return raw_input

    @model_validator(mode="after")
    def _check_selected_option(self) -> Self:
        """
        Check that the value holds the option its selector names.

        Raises:
            SSZValueError: When the selector names no option.
            SSZTypeError: When the value is a type other than the one the selector names.
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

    KIND = "compatible union"

    @classmethod
    @override
    def fixed_size(cls) -> None:
        """No width, even where every option shares one: the selector is read per value."""
        return None

    @override
    def serialize(self, stream: IO[bytes]) -> int:
        """Write the selector byte, then the encoding of the option it names."""
        return self.selector.serialize(stream) + self.data.serialize(stream)

    @classmethod
    @override
    def deserialize(cls, stream: IO[bytes], scope: int) -> Self:
        """
        Read one union from a binary stream within the given byte budget.

        The selector leads, so the option is known before its bytes are read.

        Raises:
            SSZValueError: When the budget holds no selector, or the selector names no option.
        """
        # The selector is one byte, so a budget under one cannot hold even that.
        if scope < Uint8.get_byte_length():
            raise SSZValueError(ValueFault.NO_SELECTOR, scope=scope)

        selector = Uint8.deserialize(stream, Uint8.get_byte_length())
        option = cls.OPTIONS.get(int(selector))
        if option is None:
            raise SSZValueError(
                ValueFault.UNKNOWN_SELECTOR, selector=int(selector), type=cls.__name__
            )

        # A refusal inside the option names the selector it was read under, as a path step.
        try:
            data = option.deserialize(stream, scope - Uint8.get_byte_length())
        except SSZError as error:
            error.at(int(selector))
            raise
        return cls(selector=selector, data=data)
