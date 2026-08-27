"""
SSZ container types.

Two struct shapes are defined by the SSZ spec, the second added by EIP-7495:

- A container merkleizes its fields into a tree sized by the field count.
- A progressive container merkleizes each field at the position its layout assigns.

A layout outlives any one version of a struct, so its fields keep their positions.
Both encode identically: fixed-size fields inline, variable-size fields behind offsets.
"""

import io
from functools import cache
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

One layout is mixed into the root as a single 32-byte word, which holds 256 bits.
That matches how a length is mixed into a list root.

The value is the chunk width in bits, restated rather than imported: the merkleization
module imports this one, so the dependency cannot run the other way."""


def active_fields(width: int, gaps: tuple[int, ...] = ()) -> tuple[int, ...]:
    """
    Build a field layout from its width and the positions no field occupies.

    A layout is one bit per position, and most positions hold a field.
    Writing every bit out is unreadable past a handful of fields, and a change to one of
    them is invisible in review:

        (1, 1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ...)

        active_fields(width=40, gaps=(3, 8, 9))

    Both give the same layout, and the second states the whole of what makes it unusual.

    # Why the width is given rather than counted

    The width could be read off the field count and the number of gaps.
    Stating it keeps the two independent, which is what lets a dropped field be caught:

        a struct drops a field and records the gap  ->  width rises by 0, fields fall by 1
        a struct drops a field and records nothing  ->  the counts disagree, and it fails

    Counting the width instead would make the second case derive a narrower layout and
    accept it, moving every later field to a new position under the same declaration.

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
    # A width may be written with a uint.
    # Narrowing keeps the positions below plain, as well as the messages naming them.
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

    # Ascending order rules out a repeat as well.
    # A repeat would otherwise be absorbed: two gaps at one position leave one hole,
    # which puts one more field in the layout than the width was written for.
    if any(later <= earlier for earlier, later in pairwise(positions)):
        raise SSZValueError(f"gaps {tuple(positions)} are not in ascending order")

    gap_positions = frozenset(positions)
    return tuple(0 if position in gap_positions else 1 for position in range(width))


class _SSZContainer(SSZModel):
    """
    Shared wire format for the two SSZ struct shapes.

    Both shapes encode the same way and differ only in how their fields are merkleized.

    Built from nothing, a struct holds one field default per field.
    One field whose type has no default leaves the struct with none.

    Containers are mutable: assigning a field revalidates the value against
    the field's declared type, exactly as construction does. Assignment is
    typed against the declared field types, so type checkers flag raw values
    even though runtime validation coerces them. Hashing is by Merkle tree
    root, so containers work as dict keys and set members with value
    semantics that match equality. Mutability itself is configurable
    through the inherited MUTABLE flag.
    """

    model_config = ConfigDict(validate_assignment=True)

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

        Each default is built when a field is left out, never shared, since a value is
        mutable and one instance handed to two fields would alias.

        A field whose type has no default raises when that field is left out, which is how
        a struct holding such a type inherits the absence.
        """
        super().__pydantic_init_subclass__(**kwargs)

        for field in cls.model_fields.values():
            if field.default_factory is None and field.default is PydanticUndefined:
                field.default_factory = field.annotation
        cls.model_rebuild(force=True)

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
        # A variable-size field has no width to give.
        # Asking for one is therefore the check.
        #
        # Asking first walks the declared types to decide, and the widths walk them again.
        # Each nested struct repeats both walks over its own fields.
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
        for name, field_type in _field_types(cls):
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

        # These offset checks mirror the variable-length collection decoder.
        # The duplication is intentional: inlining keeps the per-field name in each error.
        #
        # Canonical form: the first offset must point to the end of the fixed part.
        # Any other value leaves a gap or overlap, allowing two encodings of one value.
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

    A third field widens that tree to four leaves.
    Both existing fields drop one level down.
    A proof against the two-field version therefore stops verifying.
    The progressive shape avoids that.
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

    So a position decides where a field is hashed, never a declaration index:

    - A proof about the shared position verifies against either shape.
    - Dropping a field clears its bit, leaving a zero leaf that holds the rest in place.
    - Adding a position extends the tree past every position already placed.
    - Two layouts share proofs only where a set position holds the same field.

    The layout is mixed into the root.
    A gap therefore never reads as a field that holds zero.

    Encoding is that of an ordinary container, and a gap costs no bytes:

        Square(side=0x1234, color=0x42)    ->  0x341242
        Circle(radius=0x1234, color=0x42)  ->  0x341242

    The same three bytes, and two different roots.

    The spec writes the layout as a call, ProgressiveContainer(active_fields=[1, 0, 1]).
    It is a class attribute here, as a vector's length and a list's limit are.
    """

    ACTIVE_FIELDS: ClassVar[tuple[int, ...]]
    """Field layout, one bit per position, lowest position first, set where a field sits.

    Past a handful of positions the bits are easier to state by their width and their gaps:

        ACTIVE_FIELDS = active_fields(width=40, gaps=(3, 8, 9))
    """

    @classmethod
    def __pydantic_init_subclass__(cls, **kwargs: Any) -> None:
        """
        Enforce the layout rules of EIP-7495 on every declared shape.

        Raises:
            SSZTypeError: When no layout is declared.
            SSZTypeError: When the layout is empty, ends in a gap, holds anything but
                bits, is wider than the word it is mixed into, or disagrees with the
                declared fields.
        """
        super().__pydantic_init_subclass__(**kwargs)

        # Merkleization places each field by its position, so a shape needs a layout.
        if not hasattr(cls, "ACTIVE_FIELDS"):
            raise SSZDefinitionError(cls.__name__, "ACTIVE_FIELDS")

        # Every shape is checked, not only the one that introduces a layout.
        # A restated layout that disagrees with the fields would drop one from the tree.
        layout, name = cls.ACTIVE_FIELDS, cls.__name__

        # A layout is bits, so anything else is a typo rather than a value to coerce.
        # The string "100" would otherwise read as three set positions.
        if any(bit not in (0, 1) for bit in layout):
            raise SSZActiveFieldsError(name, layout, "a position holds neither 0 nor 1")

        # An empty layout admits no field, so the container would encode to zero bytes.
        # A list of zero-byte elements has no recoverable element count.
        if not layout:
            raise SSZActiveFieldsError(name, layout, "the layout is empty")

        # A trailing gap is a second spelling of one type, invisible to the packed word.
        # At some widths the tree ignores it too, so (1, 1, 0) and (1, 1) root alike.
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


type _FieldType = tuple[str, type[SSZType]]
"""One field: its name and the type it declares."""


@cache
def _field_types(cls: type[_SSZContainer]) -> tuple[_FieldType, ...]:
    """
    Each field's declared type, in the declaration order the wire format follows.

    Only what the declaration settles is kept. A width is asked of the type each time,
    because the attributes a type derives one from stay writable for as long as the type does.
    """
    return tuple((name, field.annotation) for name, field in cls.model_fields.items())
