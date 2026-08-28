"""Reusable pydantic glue shared by the SSZ types."""

from collections.abc import Callable
from typing import Any

from pydantic import BaseModel, ConfigDict
from pydantic_core import core_schema


class StrictBaseModel(BaseModel):
    """
    Strict base model for all SSZ types.

    - Extra forbidden: unknown fields rejected at construction
    - Strict: no implicit type coercion

    Each shape declares whether it is frozen.
    """

    model_config = ConfigDict(
        validate_default=True,
        arbitrary_types_allowed=True,
        extra="forbid",
        strict=True,
    )


def wrapping_schema(
    cls: type,
    *accepted: core_schema.CoreSchema,
    to_json: Callable[[Any], Any],
) -> core_schema.CoreSchema:
    r"""
    Build the pydantic schema for an SSZ type that wraps one validated primitive.

    A uint is an int, a boolean is a bool, a byte array is bytes.
    Each declares which raw forms a field may hold it as, and the constructor turns one
    into the typed value:

        Header(slot=7)            ->  the int is gated, then Uint64(7) wraps it
        Header(tag="0xdeadbeef")  ->  the str is gated, then Bytes4(...) wraps it

    An instance is its own branch, reaching the field untouched.
    A field may hold a subclass of what it declares, and narrowing one to the declared
    class would refuse it, or silently reshape a value that was already the right one.

    # Why the gate is a schema rather than the constructor alone

    The constructor accepts more than a field should, and reports what it refuses with an
    SSZ error, which pydantic does not recognize.
    Left to it, a bad field escapes model construction as a bare SSZ error or a TypeError,
    naming neither the field nor the model.
    Gating on the accepted shapes first keeps every refusal a ValidationError:

        Header(tag=b"\x01\x02")  ->  ValidationError, no bytes branch of the right width
        Header(tag=123)          ->  ValidationError, no branch at all

    Args:
        cls: The SSZ type, called on whatever a raw branch admits.
        accepted: The raw forms a field may hold this type as, besides an instance of it.
            Each states its own constraints, so the width or range is checked here.
        to_json: Turns an instance into its JSON form.

    Returns:
        A schema admitting an instance or an accepted raw form, and refusing the rest.
    """
    # One validator, shared by every raw branch, running the constructor on what it admits.
    wrap = core_schema.no_info_plain_validator_function(cls)
    return core_schema.union_schema(
        # An instance is listed first, so the common case settles before any coercion.
        [
            core_schema.is_instance_schema(cls),
            *(core_schema.chain_schema([raw, wrap]) for raw in accepted),
        ],
        serialization=core_schema.plain_serializer_function_ser_schema(to_json),
    )
