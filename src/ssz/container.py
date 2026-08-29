"""
SSZ container types.

Two struct shapes, the second added by EIP-7495:

- A container merkleizes its fields into a tree sized by the field count.
- A progressive container merkleizes each field at the position its layout assigns.

Both encode identically: fixed-size fields inline, variable-size fields behind offsets.
"""

import io
from itertools import pairwise
from typing import IO, Any, ClassVar, Final, Self, override

from pydantic import ConfigDict, model_validator
from pydantic.functional_validators import ModelWrapValidatorHandler
from pydantic_core import PydanticUndefined

from ssz.exceptions import (
    SSZActiveFieldsError,
    SSZDefinitionError,
    SSZError,
    SSZFixedSizeError,
    SSZScopeError,
    SSZSerializationError,
    SSZTypeMismatch,
    SSZValueError,
)
from ssz.ssz_base import BYTES_PER_LENGTH_OFFSET, SSZModel, SSZType
from ssz.uint import Uint32

MAX_ACTIVE_FIELDS: Final = 256
"""Widest field layout a progressive container may declare: one 32-byte word holds 256 bits."""


def active_fields(width: int, gaps: tuple[int, ...] = ()) -> tuple[int, ...]:
    """
    Build a field layout from its width and the positions no field occupies.

    A width of 46 with gaps at 8, 9, 10 and 28 is the post-EIP-8015 beacon state layout.

    The width is declared and not counted, so recording a gap keeps later fields in place.

    Args:
        width: Total positions in the layout, occupied or not.
        gaps: Positions no field occupies, ascending.

    Returns:
        One bit per position, set where a field sits.

    Raises:
        SSZTypeMismatch: When the width or a gap is not a plain integer.
        SSZValueError:
            - When the width is below one.
            - When the gaps are unordered, repeated, or outside the width.
    """
    # A boolean passes for an integer wherever the host language looks, so it is refused by name.
    if not isinstance(width, int) or isinstance(width, bool):
        raise SSZTypeMismatch("an integer width", type(width))

    # Uints of unequal width refuse to compare, so the range check below runs on plain integers.
    width = int(width)
    if width < 1:
        raise SSZValueError(f"a layout holds at least one position, got a width of {width}")

    positions: list[int] = []
    for gap in gaps:
        if not isinstance(gap, int) or isinstance(gap, bool):
            raise SSZTypeMismatch("an integer position", type(gap))
        position = int(gap)
        # A position outside the width would vanish, leaving no gap where one was written.
        if not 0 <= position < width:
            raise SSZValueError(f"gap {position} falls outside a layout of {width} positions")
        positions.append(position)

    # Two gaps at one position leave one hole, and a fixed order makes every layout read alike.
    if any(later <= earlier for earlier, later in pairwise(positions)):
        raise SSZValueError(f"gaps {tuple(positions)} are not in ascending order")

    gap_positions = frozenset(positions)
    return tuple(0 if position in gap_positions else 1 for position in range(width))


class _SSZContainer(SSZModel):
    """Shared wire format for the two SSZ struct shapes, which differ only in how they merkleize."""

    model_config = ConfigDict(validate_assignment=True)

    _FIELD_TYPES: ClassVar[tuple[tuple[str, type[SSZType]], ...]] = ()
    """Each field's name and declared type, in the declaration order the wire format follows."""

    _LEADING_SLOTS: ClassVar[tuple[tuple[str, bool], ...]] = ()
    """Each field's name and whether its leading slot holds the field itself, in wire order."""

    _LEADING_WIDTH: ClassVar[int] = 0
    """Bytes the leading part spans, which is where the first variable payload begins."""

    @model_validator(mode="wrap")
    @classmethod
    def _accept_hex_string(cls, value: Any, handler: ModelWrapValidatorHandler[Self]) -> Self:
        """
        Reconstruct the container from a hex-encoded SSZ payload.

        - Other input shapes pass through to field-by-field validation.
        - Hex strings accept an optional 0x prefix.
        """
        if isinstance(value, str):
            try:
                return cls.from_hex(value)
            except SSZError as exception:
                raise ValueError(f"invalid {cls.__name__} hex: {exception}") from exception
        return handler(value)

    @classmethod
    def __pydantic_init_subclass__(cls, **kwargs: Any) -> None:
        """
        Give every field the default of its own type, so a struct needs no arguments.

        Each default is built on the omission, so two fields never alias one mutable value.

        A field whose type has no default raises when left out, and the struct inherits that.

        The wire layout is settled here too, since a declaration cannot change.
        """
        super().__pydantic_init_subclass__(**kwargs)

        field_types: list[tuple[str, type[SSZType]]] = []
        leading_slots: list[tuple[str, bool]] = []
        leading_width = 0
        for name, field in cls.model_fields.items():
            declared = field.annotation

            # A field declared as anything but an SSZ type has neither an encoding nor a root.
            if not (isinstance(declared, type) and issubclass(declared, SSZType)):
                # A declared class names itself; anything else is named by what it is.
                raise SSZTypeMismatch(
                    f"an SSZ type for {cls.__name__}.{name}",
                    declared if isinstance(declared, type) else type(declared),
                )

            if field.default_factory is None and field.default is PydanticUndefined:
                field.default_factory = declared
            field_types.append((name, declared))

            # Asking a declared type this per encode would walk its whole subtree again.
            inline = declared.is_fixed_size()
            leading_slots.append((name, inline))
            leading_width += declared.get_byte_length() if inline else BYTES_PER_LENGTH_OFFSET

        cls.model_rebuild(force=True)

        cls._FIELD_TYPES = tuple(field_types)
        cls._LEADING_SLOTS = tuple(leading_slots)
        cls._LEADING_WIDTH = leading_width

    @classmethod
    @override
    def is_fixed_size(cls) -> bool:
        """True only when every field is fixed-size."""
        return all(field_type.is_fixed_size() for _, field_type in cls._FIELD_TYPES)

    @classmethod
    @override
    def get_byte_length(cls) -> int:
        """
        Sum of field widths.

        Raises:
            SSZFixedSizeError: When any field is variable-size, so the struct has no width.
        """
        # A variable-size field has no width to give, so asking for one is the check.
        #
        # Checking first would walk every declared type twice, and again at every nesting.
        try:
            return sum(field_type.get_byte_length() for _, field_type in cls._FIELD_TYPES)
        except SSZFixedSizeError as variable_field:
            raise SSZFixedSizeError(cls.__name__, "container") from variable_field

    @override
    def serialize(self, stream: IO[bytes]) -> int:
        """Write the fixed part with offsets, then the variable payloads."""
        # The declaration fixes the leading width, so the first payload's start needs no counting.
        # The same running count ends as the total written.
        offset = self._LEADING_WIDTH

        # Variable payloads stage in a buffer while the output takes the fixed part.
        tail = io.BytesIO()
        for name, inline in self._LEADING_SLOTS:
            field_value = getattr(self, name)
            if inline:
                field_value.serialize(stream)
            else:
                Uint32(offset).serialize(stream)
                offset += field_value.serialize(tail)
        stream.write(tail.getvalue())
        return offset

    @classmethod
    @override
    def deserialize(cls, stream: IO[bytes], scope: int) -> Self:
        """Read the fixed part with offsets, then each variable payload by its offset window."""
        fields: dict[str, SSZType] = {}
        variable_fields: list[tuple[str, type[SSZType], int]] = []
        bytes_read = 0

        # Phase 1: each slot is either the field itself or an offset to its tail payload.
        for name, field_type in cls._FIELD_TYPES:
            if field_type.is_fixed_size():
                width = field_type.get_byte_length()
                fields[name] = field_type.deserialize(stream, width)
                bytes_read += width
            else:
                offset = int(Uint32.deserialize(stream, BYTES_PER_LENGTH_OFFSET))
                variable_fields.append((name, field_type, offset))
                bytes_read += BYTES_PER_LENGTH_OFFSET

        if not variable_fields:
            # With no tail, the fixed part just read is the whole encoding.
            # A wider budget would leave bytes unread inside the window handed down.
            if scope != bytes_read:
                raise SSZScopeError(cls.__name__, bytes_read, scope)
            return cls(**fields)

        # Duplicated from the collection decoder on purpose, so each error names its field.
        # The first offset must land on the end of the fixed part.
        # Any other value leaves a gap or an overlap, giving one value two encodings.
        if variable_fields[0][2] != bytes_read:
            first_offset = variable_fields[0][2]
            raise SSZSerializationError(
                f"{cls.__name__}: first offset {first_offset} != fixed-part end {bytes_read}"
            )

        # Phase 2: each variable payload spans from its offset to the next.
        # Scope closes the final span.
        boundaries = [offset for _, _, offset in variable_fields] + [scope]
        for (name, field_type, _), (start, end) in zip(
            variable_fields, pairwise(boundaries), strict=True
        ):
            if end < start:
                raise SSZSerializationError(
                    f"{cls.__name__}.{name}: non-monotonic offsets ({start} > {end})"
                )
            fields[name] = field_type.deserialize(stream, end - start)

        return cls(**fields)

    @classmethod
    def from_hex(cls, value: str) -> Self:
        """Decode from a hex string with an optional 0x prefix."""
        return cls.decode_bytes(bytes.fromhex(value.removeprefix("0x")))


class Container(_SSZContainer):
    """
    Ordered struct of named heterogeneous SSZ fields.

    The Merkle tree holds one leaf per field, padded to the next power of two.
    """


class ProgressiveContainer(_SSZContainer):
    """
    Ordered struct whose fields keep their tree positions across versions, per EIP-7495.

    - A layout of bits places the fields.
    - A set bit merkleizes a field at that position.
    - A clear bit leaves a zero leaf instead.

    Fields are declared in the order of the set bits.
    """

    ACTIVE_FIELDS: ClassVar[tuple[int, ...]]
    """Field layout, one bit per position, lowest position first, set where a field sits."""

    @classmethod
    def __pydantic_init_subclass__(cls, **kwargs: Any) -> None:
        """
        Enforce the layout rules of EIP-7495 on every declared shape.

        Raises:
            SSZDefinitionError: When no layout is declared.
            SSZActiveFieldsError: When a declared layout breaks one of those rules.
        """
        super().__pydantic_init_subclass__(**kwargs)

        # Merkleization places each field by its position, so a shape needs a layout.
        if not hasattr(cls, "ACTIVE_FIELDS"):
            raise SSZDefinitionError(cls.__name__, "ACTIVE_FIELDS")

        # Every shape is checked, since a restated layout that disagrees would drop a field.
        layout, name = cls.ACTIVE_FIELDS, cls.__name__

        # A layout is bits and nothing else: the string "100" would read as three set positions.
        if any(bit not in (0, 1) for bit in layout):
            raise SSZActiveFieldsError(name, layout, "a position holds neither 0 nor 1")

        # An empty layout encodes to zero bytes, and a list of those has no recoverable count.
        if not layout:
            raise SSZActiveFieldsError(name, layout, "the layout is empty")

        # A trailing gap is a second spelling of one shape: (1, 1, 0) and (1, 1) root alike.
        if not layout[-1]:
            raise SSZActiveFieldsError(name, layout, "the layout ends in a gap")

        # The whole layout is mixed into the root as one 32-byte word.
        if len(layout) > MAX_ACTIVE_FIELDS:
            raise SSZActiveFieldsError(
                name,
                layout,
                f"the layout holds {len(layout)} positions, over the limit of {MAX_ACTIVE_FIELDS}",
            )

        # One field per set position, in declaration order.
        active_count = sum(layout)
        if len(cls.model_fields) != active_count:
            raise SSZActiveFieldsError(
                name,
                layout,
                f"the layout sets {active_count} positions, "
                + f"and the struct declares {len(cls.model_fields)}",
            )
