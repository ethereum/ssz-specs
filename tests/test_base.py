"""Tests for the reusable strict base model."""

import pytest
from pydantic import ConfigDict, ValidationError

from ssz.base import StrictBaseModel


class StrictExample(StrictBaseModel):
    """A strict model used to exercise the extra-forbid and strict constraints."""

    first_value: int


class FrozenExample(StrictBaseModel):
    """A strict model that declares itself frozen, as each SSZ shape does."""

    model_config = ConfigDict(frozen=True)

    first_value: int


def test_strict_model_accepts_attribute_assignment() -> None:
    """The base states no frozen flag, leaving each shape to declare its own."""
    instance = StrictExample(first_value=1)

    instance.first_value = 2

    assert instance.first_value == 2


def test_frozen_model_rejects_attribute_assignment() -> None:
    """A model that declares itself frozen raises when an attribute is reassigned."""
    instance = FrozenExample(first_value=1)
    with pytest.raises(ValidationError):
        instance.first_value = 2


def test_strict_model_rejects_unknown_fields() -> None:
    """A strict model forbids extra fields at construction."""
    with pytest.raises(ValidationError):
        StrictExample(first_value=1, unexpected=2)  # type: ignore[call-arg]


def test_strict_model_rejects_implicit_type_coercion() -> None:
    """Strict mode rejects a value that would otherwise coerce into the declared type."""
    with pytest.raises(ValidationError):
        StrictExample(first_value="1")  # type: ignore[arg-type]
