"""
How a type, a value and a path are written for the Lean side to read.

The corpus writes them the way the released vectors write them, so the Lean side reads a
generated case with the same readers it reads a released one with:

    descriptor   <->  Conformance.readDescriptor
    json_value   <->  Ssz.valueOf
    Step         <->  Conformance.readProofStep
"""

from dataclasses import dataclass
from typing import Final, TypeAlias

import ssz
from ssz.base import json_writer
from ssz_testing.fixtures import describe_type

Json: TypeAlias = dict[str, object]
"""One JSON object, as the corpus writes them."""


def descriptor(ssz_type: type[ssz.SSZType]) -> object:
    """
    The type as the Lean side reads it, derived from the declaring class itself.

    Deriving it rather than carrying it alongside is what stops the two drifting apart.
    """
    return describe_type(ssz_type).model_dump(mode="json", by_alias=True, exclude_none=True)


def json_value(value: ssz.SSZType) -> object:
    """The value as the Lean side reads it, in the JSON the mapping assigns it."""
    return json_writer(type(value)).dump_python(value, mode="json")


MIXED_IN_WORDS: Final[dict[ssz.PathStep, str]] = {
    ssz.LENGTH_KEY: "__len__",
    ssz.ACTIVE_FIELDS_KEY: "__active_fields__",
    ssz.SELECTOR_KEY: "__selector__",
}
"""Each reserved path step, and the name the released vectors give the same word."""


@dataclass(frozen=True, slots=True)
class Step:
    """
    One step of a path, kept in both spellings so neither can drift from the other.

    The two differ on one point: a struct field is named here and counted there, names being
    part of this implementation's API rather than of SSZ.
    """

    python: ssz.PathStep
    """The step as this implementation takes it: a field name, a position, or a word."""

    lean: int | str
    """The step as the Lean side takes it: an ordinal, a selector, or the word's name."""

    name: str | None = None
    """The field name, where this step names one, which the released spelling carries."""

    def to_json(self) -> Json:
        """The step as the corpus writes it, in the spelling a proof vector uses."""
        if self.name is not None:
            return {"field": self.name}
        if isinstance(self.lean, int):
            return {"position": self.lean}
        return {"mixin": self.lean}
