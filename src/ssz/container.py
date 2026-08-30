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

from ssz.exceptions import SSZError, SSZTypeError, SSZValueError, TypeFault, ValueFault
from ssz.ssz_base import BYTES_PER_LENGTH_OFFSET, SSZModel, SSZType, offset_table_spans
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
        SSZTypeError: When the width or a gap is not a plain integer.
        SSZTypeError: When the width is below one.
        SSZTypeError: When the gaps are unordered, repeated, or outside the width.
    """
    # A boolean passes for an integer wherever the host language looks, so it is refused by name.
    if not isinstance(width, int) or isinstance(width, bool):
        raise SSZTypeError(TypeFault.LAYOUT_WIDTH_TYPE, got=type(width).__name__)

    # Uints of unequal width refuse to compare, so the range check below runs on plain integers.
    width = int(width)
    if width < 1:
        raise SSZTypeError(TypeFault.LAYOUT_WIDTH, width=width)

    positions: list[int] = []
    for gap in gaps:
        if not isinstance(gap, int) or isinstance(gap, bool):
            raise SSZTypeError(TypeFault.LAYOUT_GAP_TYPE, got=type(gap).__name__)
        position = int(gap)
        # A position outside the width would vanish, leaving no gap where one was written.
        if not 0 <= position < width:
            raise SSZTypeError(TypeFault.LAYOUT_GAP_OUTSIDE, gap=position, width=width)
        positions.append(position)

    # Two gaps at one position leave one hole, and a fixed order makes every layout read alike.
    if any(later <= earlier for earlier, later in pairwise(positions)):
        raise SSZTypeError(TypeFault.LAYOUT_GAPS_UNORDERED, gaps=tuple(positions))

    gap_positions = frozenset(positions)
    return tuple(0 if position in gap_positions else 1 for position in range(width))


class _SSZContainer(SSZModel):
    """Shared wire format for the two SSZ struct shapes, which differ only in how they merkleize."""

    model_config = ConfigDict(validate_assignment=True)

    KIND = "container"

    _FIELD_TYPES: ClassVar[tuple[tuple[str, type[SSZType]], ...]] = ()
    """Each field's name and declared type, in the declaration order the wire format follows."""

    _LEADING_SLOTS: ClassVar[tuple[tuple[str, bool], ...]] = ()
    """Each field's name and whether its leading slot holds the field itself, in wire order."""

    _LEADING_WIDTH: ClassVar[int] = 0
    """Bytes the leading part spans, which is where the first variable payload begins."""

    _FIXED_SIZE: ClassVar[int | None] = 0
    """Width of the whole struct, or None where a field leaves it without one."""

    @model_validator(mode="wrap")
    @classmethod
    def _accept_hex_string(cls, value: Any, handler: ModelWrapValidatorHandler[Self]) -> Self:
        """
        Reconstruct the container from a hex-encoded SSZ payload.

        - Other input shapes pass through to field-by-field validation.
        - Hex strings accept an optional 0x prefix.
        """
        if isinstance(value, str):
            return cls.from_hex(value)
        return handler(value)

    @classmethod
    def __pydantic_init_subclass__(cls, **kwargs: Any) -> None:
        """
        Settle what the declaration fixes: the field types, their defaults, and the total width.

        Every field gets the default of its own type, so a struct needs no arguments.
        Each default is built on the omission, so two fields never alias one mutable value.

        A field whose type has no default raises when left out, and the struct inherits that.

        The wire layout is settled here too, since a declaration cannot change.
        """
        super().__pydantic_init_subclass__(**kwargs)

        field_types: list[tuple[str, type[SSZType]]] = []
        leading_slots: list[tuple[str, bool]] = []
        leading_width = 0
        total_width: int | None = 0
        for name, field in cls.model_fields.items():
            declared = field.annotation

            # A field declared as anything but an SSZ type has neither an encoding nor a root.
            if not (isinstance(declared, type) and issubclass(declared, SSZType)):
                # A declared class names itself; anything else is named by what it is.
                named = declared if isinstance(declared, type) else type(declared)
                raise SSZTypeError(
                    TypeFault.NOT_AN_SSZ_TYPE,
                    type=cls.__name__,
                    field=name,
                    got=named.__name__,
                )

            if field.default_factory is None and field.default is PydanticUndefined:
                field.default_factory = declared
            field_types.append((name, declared))

            # One width answers both: the slot the field takes, and the struct's own span.
            width = declared.fixed_size()
            inline = width is not None
            leading_slots.append((name, inline))
            leading_width += width if inline else BYTES_PER_LENGTH_OFFSET
            total_width = None if width is None or total_width is None else total_width + width

        cls.model_rebuild(force=True)

        cls._FIELD_TYPES = tuple(field_types)
        cls._LEADING_SLOTS = tuple(leading_slots)
        cls._LEADING_WIDTH = leading_width
        cls._FIXED_SIZE = total_width

    @classmethod
    @override
    def fixed_size(cls) -> int | None:
        """The sum settled at declaration, since no field can join a struct afterwards."""
        return cls._FIXED_SIZE

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
        variable_fields: list[tuple[str, type[SSZType]]] = []
        offsets: list[int] = []
        bytes_read = 0

        # Phase 1: each slot is either the field itself or an offset to its tail payload.
        for name, field_type in cls._FIELD_TYPES:
            try:
                if field_type.is_fixed_size():
                    width = field_type.get_byte_length()
                    fields[name] = field_type.deserialize(stream, width)
                    bytes_read += width
                else:
                    offsets.append(int(Uint32.deserialize(stream, BYTES_PER_LENGTH_OFFSET)))
                    variable_fields.append((name, field_type))
                    bytes_read += BYTES_PER_LENGTH_OFFSET
            except SSZError as error:
                error.at(name)
                raise

        if not variable_fields:
            # With no tail, the fixed part just read is the whole encoding.
            # A wider budget would leave bytes unread inside the window handed down.
            if scope != bytes_read:
                raise SSZValueError(
                    ValueFault.SCOPE, type=cls.__name__, expected=bytes_read, actual=scope
                )
            return cls(**fields)

        # The first offset lands on the end of the fixed part, which a struct measures itself.
        # Any other value leaves a gap or an overlap, giving one value two encodings.
        if offsets[0] != bytes_read:
            raise SSZValueError(ValueFault.FIRST_OFFSET, actual=offsets[0], expected=bytes_read)

        # Phase 2: the table is settled whole, so no payload is read behind a broken one.
        # Each field names itself on a refusal, the table's own included.
        spans = offset_table_spans(offsets, scope, [name for name, _ in variable_fields])
        for (name, field_type), span in zip(variable_fields, spans, strict=True):
            try:
                fields[name] = field_type.deserialize(stream, span)
            except SSZError as error:
                error.at(name)
                raise

        return cls(**fields)

    @classmethod
    def from_hex(cls, value: str) -> Self:
        """
        Decode from a hex string with an optional 0x prefix.

        Raises:
            SSZValueError: When the string holds something other than hex digits.
        """
        try:
            data = bytes.fromhex(value.removeprefix("0x"))
        except ValueError as not_hex:
            raise SSZValueError(ValueFault.NOT_HEX, type=cls.__name__) from not_hex
        return cls.decode_bytes(data)


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
            SSZTypeError: When no layout is declared, or a declared one breaks a rule.
        """
        super().__pydantic_init_subclass__(**kwargs)

        # Merkleization places each field by its position, so a shape needs a layout.
        if not hasattr(cls, "ACTIVE_FIELDS"):
            raise SSZTypeError(TypeFault.UNDECLARED, type=cls.__name__, requirement="ACTIVE_FIELDS")

        # Every shape is checked, since a restated layout that disagrees would drop a field.
        # The layout rides along on each refusal, which is the one thing none of them prints.
        layout = cls.ACTIVE_FIELDS

        # A layout is bits and nothing else: the string "100" would read as three set positions.
        if any(bit not in (0, 1) for bit in layout):
            raise SSZTypeError(TypeFault.LAYOUT_NOT_BITS, layout=layout)

        # An empty layout encodes to zero bytes, and a list of those has no recoverable count.
        if not layout:
            raise SSZTypeError(TypeFault.LAYOUT_WIDTH, width=len(layout), layout=layout)

        # A trailing gap is a second spelling of one shape: (1, 1, 0) and (1, 1) root alike.
        if not layout[-1]:
            raise SSZTypeError(TypeFault.LAYOUT_TRAILING_GAP, layout=layout)

        # The whole layout is mixed into the root as one 32-byte word.
        if len(layout) > MAX_ACTIVE_FIELDS:
            raise SSZTypeError(
                TypeFault.LAYOUT_TOO_WIDE,
                width=len(layout),
                limit=MAX_ACTIVE_FIELDS,
                layout=layout,
            )

        # One field per set position, in declaration order.
        if len(cls.model_fields) != sum(layout):
            raise SSZTypeError(
                TypeFault.LAYOUT_FIELD_COUNT,
                active=sum(layout),
                declared=len(cls.model_fields),
                layout=layout,
            )
