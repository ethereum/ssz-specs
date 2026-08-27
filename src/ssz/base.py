"""Reusable, strict base model for SSZ types."""

from pydantic import BaseModel, ConfigDict


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
