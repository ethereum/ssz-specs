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
    """
    Build the pydantic schema for an SSZ type that wraps one validated primitive.

    - An instance takes a branch of its own, reaching the field untouched.
    - Every other accepted form is checked, then handed to the constructor.

    # Why the gate is a schema rather than the constructor alone

    The constructor accepts more than a field should.
    It refuses with an SSZ error, which pydantic does not recognize, so a bad field would
    escape model construction naming neither the field nor the model.

    # Why an instance skips the constructor

    A field may hold a subclass of what it declares.
    Narrowing one back to the declared class would refuse a value that was already right.

    Args:
        cls: The SSZ type, called on whatever a raw branch admits.
        accepted: The raw forms a field may hold this type as, besides an instance of it.
        to_json: Turns an instance into its JSON form.

    Returns:
        A schema admitting an instance or an accepted form, and refusing the rest.
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
