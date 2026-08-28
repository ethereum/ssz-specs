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
    """
    # The constructor accepts more than a field should.
    # It refuses with an SSZ error, which pydantic does not recognize.
    # Gating on the accepted forms first keeps every refusal a validation error.
    wrap = core_schema.no_info_plain_validator_function(cls)
    return core_schema.union_schema(
        # An instance is listed first, and reaches the field without meeting the constructor.
        # A field may hold a subclass of what it declares.
        # The constructor would narrow one back, refusing a value that was already right.
        [
            core_schema.is_instance_schema(cls),
            *(core_schema.chain_schema([raw, wrap]) for raw in accepted),
        ],
        serialization=core_schema.plain_serializer_function_ser_schema(to_json),
    )
