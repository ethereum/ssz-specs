"""Reusable pydantic glue shared by the SSZ types."""

from collections.abc import Callable
from functools import cache
from typing import Any

from pydantic import BaseModel, ConfigDict, TypeAdapter, ValidationInfo
from pydantic_core import core_schema

from ssz.exceptions import document_refusals


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

    - An instance is settled first, and reaches the field without meeting the constructor.
    - Every other accepted form is checked, then handed to the constructor.
    """

    def build(value: Any, info: ValidationInfo) -> Any:
        # A refusal pydantic does not recognize leaves a document a type error, not a fault.
        with document_refusals(info.mode):
            return cls(value)

    wrap = core_schema.with_info_plain_validator_function(build)
    return core_schema.no_info_wrap_validator_function(
        # A field may hold a subclass of what it declares.
        # The constructor would narrow one back, refusing a value that was already right.
        #
        # Asked here rather than as a union branch, since such a branch cannot run on a document.
        # It reports that in place of the refusal the document earned, which leaves a number out
        # of range reading no differently from a misspelled one.
        lambda value, handler: value if isinstance(value, cls) else handler(value),
        core_schema.union_schema([core_schema.chain_schema([raw, wrap]) for raw in accepted]),
        serialization=core_schema.plain_serializer_function_ser_schema(to_json),
    )


@cache
def json_writer(ssz_type: type) -> TypeAdapter[Any]:
    """The JSON mapping one type spells, built once per type."""
    return TypeAdapter(ssz_type)
