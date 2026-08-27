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
    SSZSerializationError,
    SSZTypeMismatch,
    SSZValueError,
)
from ssz.ssz_base import BYTES_PER_LENGTH_OFFSET, SSZModel, SSZType
from ssz.uint import Uint32

MAX_ACTIVE_FIELDS: Final = 256
"""Widest field layout a progressive container may declare.

The whole layout is mixed into the root as one 32-byte word, which holds 256 bits.

The chunk width in bits is restated here rather than imported.
The merkleization module imports this one, so the dependency cannot run the other way."""


def active_fields(width: int, gaps: tuple[int, ...] = ()) -> tuple[int, ...]:
    """
    Build a field layout from its width and the positions no field occupies.

    A layout is one bit per position, clearest written out as (1, 0, 1) while they are few.
    Past a handful, a changed bit is invisible in review, and the width and gaps read better:

        [1] * 8 + [0] * 3 + [1] * 17 + [0] + [1] * 17   the post-EIP-8015 beacon state

        active_fields(width=46, gaps=(8, 9, 10, 28))    the same layout, here

    Public because the consensus specs import it by name, though nothing here calls it.

    # Why the width is given rather than counted

    The width and the field count are stated independently, and cross-checked on declaration:

        a struct drops a field and records the gap  ->  width rises by 0, fields fall by 1
        a struct drops a field and records nothing  ->  the counts disagree, and it fails

    A counted width would derive the narrower layout instead, renumbering every later field.
    The check counts positions and does not place them, so a misplaced gap still passes.

    Args:
        width: Total positions in the layout, occupied or not.
        gaps: Positions no field occupies, ascending.

    Returns:
        One bit per position, set where a field sits.

    Raises:
        SSZTypeMismatch: When the width or a gap is not a plain integer.
        SSZValueError: When the width is below one.
        SSZValueError: When the gaps are unordered, repeated, or outside the width.
    """
    # A boolean counts nothing.
    # The host language admits one wherever an integer fits, so it is refused by name.
    if not isinstance(width, int) or isinstance(width, bool):
        raise SSZTypeMismatch("an integer width", type(width))

    # Narrow before anything reads the value.
    #
    # A width and a gap may each be written with a uint, and of different sizes.
    # A uint refuses a relation against a uint of another size.
    # The range check below compares the two, so plain integers keep it about the layout.
    width = int(width)
    if width < 1:
        raise SSZValueError(f"a layout holds at least one position, got a width of {width}")

    positions: list[int] = []
    for gap in gaps:
        if not isinstance(gap, int) or isinstance(gap, bool):
            raise SSZTypeMismatch("an integer position", type(gap))
        position = int(gap)
        # A position outside the width names nothing.
        # Left unchecked it would vanish, leaving a layout with no gap where one was written.
        if not 0 <= position < width:
            raise SSZValueError(f"gap {position} falls outside a layout of {width} positions")
        positions.append(position)

    # Two gaps at one position leave one hole, so the layout carries one field too many.
    # Reordering changes nothing in the layout itself.
    # One order is fixed so that every layout reads the same way in review.
    if any(later <= earlier for earlier, later in pairwise(positions)):
        raise SSZValueError(f"gaps {tuple(positions)} are not in ascending order")

    gap_positions = frozenset(positions)
    return tuple(0 if position in gap_positions else 1 for position in range(width))


class _SSZContainer(SSZModel):
    """
    Shared wire format for the two SSZ struct shapes.

    They differ only in how their fields are merkleized.

    Built from nothing, a struct holds one field default per field.
    A field whose type has no default leaves the struct with none.

    Assigning a field validates it against its declared type, exactly as construction does.
    That declared type is what a type checker sees, so it flags a value the validator would coerce.
    """

    model_config = ConfigDict(validate_assignment=True)

    _FIELD_TYPES: ClassVar[tuple[tuple[str, type[SSZType]], ...]] = ()
    """Each field's name and declared type, in the declaration order the wire format follows.

    Settled once per shape, since a declaration cannot change.
    A width is still asked each time, since what a type derives one from stays writable."""

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
        """
        super().__pydantic_init_subclass__(**kwargs)

        for field in cls.model_fields.values():
            if field.default_factory is None and field.default is PydanticUndefined:
                field.default_factory = field.annotation
        cls.model_rebuild(force=True)
        cls._FIELD_TYPES = tuple((name, f.annotation) for name, f in cls.model_fields.items())

    @classmethod
    @override
    def is_fixed_size(cls) -> bool:
        """True only when every field is fixed-size."""
        return all(f.annotation.is_fixed_size() for f in cls.model_fields.values())

    @classmethod
    @override
    def get_byte_length(cls) -> int:
        """
        Sum of field widths.

        Raises:
            SSZFixedSizeError: When any field is variable-size, so the struct has no width.
        """
        # A variable-size field has no width to give, so asking for one is the check.
        # Checking first would walk every declared type twice, and again at every nesting.
        try:
            return sum(f.annotation.get_byte_length() for f in cls.model_fields.values())
        except SSZFixedSizeError as variable_field:
            raise SSZFixedSizeError(cls.__name__, "container") from variable_field

    @override
    def serialize(self, stream: IO[bytes]) -> int:
        """Write the fixed part with offsets, then the variable payloads."""
        field_values = [getattr(self, name) for name in type(self).model_fields]

        # Leading-part width: each slot is either the field's byte length or one offset.
        offset = sum(
            type(v).get_byte_length() if type(v).is_fixed_size() else BYTES_PER_LENGTH_OFFSET
            for v in field_values
        )

        # Variable payloads stage in a buffer while the output takes the fixed part.
        tail = io.BytesIO()
        for field_value in field_values:
            if type(field_value).is_fixed_size():
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
    r"""
    Ordered struct of named heterogeneous SSZ fields.

    The Merkle tree holds one leaf per field, padded to the next power of two:

        class Pair(Container):
            a: Uint64
            b: Uint64

        leaves  :  root(a)   root(b)
                      \________/
                          root

    A third field widens that tree to four leaves, and both existing fields drop one level.
    A proof against the two-field version then stops verifying, which the other shape avoids.
    """


class ProgressiveContainer(_SSZContainer):
    """
    Ordered struct whose fields keep their tree positions across versions, per EIP-7495.

    - A layout of bits places the fields.
    - A set bit merkleizes a field at that position.
    - A clear bit leaves a zero leaf instead.

    Fields are declared in the order of the set bits:

        class Square(ProgressiveContainer):
            ACTIVE_FIELDS = (1, 0, 1)

            side: Uint16     # position 0
            color: Uint8     # position 2

        class Circle(ProgressiveContainer):
            ACTIVE_FIELDS = (0, 1, 1)

            radius: Uint16   # position 1
            color: Uint8     # position 2

        position    0            1              2
        (1, 0, 1)   root(side)   ZERO           root(color)
        (0, 1, 1)   ZERO         root(radius)   root(color)

    A position decides where a field is hashed, never a declaration index:

    - A proof about the shared position verifies against either shape.
    - Dropping a field clears its bit, and the zero leaf holds the rest in place.
    - Adding a position extends the tree past every position already placed.

    The layout is mixed into the root, so a gap never reads as a field holding zero.

    Encoding is that of an ordinary container, and a gap costs no bytes:

        Square(side=0x1234, color=0x42)    ->  0x341242
        Circle(radius=0x1234, color=0x42)  ->  0x341242

    The same three bytes, and two different roots.

    The spec writes the layout as a call, ProgressiveContainer(active_fields=[1, 0, 1]).
    It is a class attribute here, as a vector's length and a list's limit are.
    """

    ACTIVE_FIELDS: ClassVar[tuple[int, ...]]
    """Field layout, one bit per position, lowest position first, set where a field sits.

    Past a handful of positions, state it by width and gaps instead:

        ACTIVE_FIELDS = active_fields(width=46, gaps=(8, 9, 10, 28))
    """

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
                f"and the struct declares {len(cls.model_fields)}",
            )
