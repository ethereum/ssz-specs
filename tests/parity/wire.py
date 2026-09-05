"""
How a type, a value and a path are written for the Lean side to read.

Each name here mirrors one Lean reader:

    descriptor   <->  Conformance.readDesc
    json_value   <->  Conformance.readValue
    Step         <->  Conformance.readStep
"""

from dataclasses import dataclass
from typing import Final, TypeAlias

import ssz

Json: TypeAlias = dict[str, object]
"""One JSON object, as the corpus writes them."""


def descriptor(ssz_type: type[ssz.SSZType]) -> Json:
    """
    The type as the Lean side reads it, derived from the declaring class itself.

    Deriving it rather than carrying it alongside is what stops the two drifting apart.
    Only well-formed types are reachable, so refusing a malformed one is not tested here.

    Raises:
        AssertionError: A type outside the universe this corpus generates.
    """
    if issubclass(ssz_type, ssz.Boolean):
        return {"k": "bool"}
    if issubclass(ssz_type, ssz.BaseUint):
        return {"k": "uint", "w": ssz_type.get_byte_length()}
    # A byte array is neither a vector nor a list, so it is answered before them.
    if issubclass(ssz_type, ssz.ByteVector):
        return {"k": "byteVector", "n": ssz_type.declared_length()}
    if issubclass(ssz_type, ssz.ByteList):
        return {"k": "byteList", "n": ssz_type.declared_limit()}
    if issubclass(ssz_type, ssz.BitVector):
        return {"k": "bitVector", "n": ssz_type.declared_length()}
    # A progressive shape carries no capacity, so it is answered before the bounded one.
    if issubclass(ssz_type, ssz.ProgressiveBitList):
        return {"k": "progressiveBitList"}
    if issubclass(ssz_type, ssz.BitList):
        return {"k": "bitList", "n": ssz_type.declared_limit()}
    if issubclass(ssz_type, ssz.Vector):
        el = descriptor(ssz_type.ELEMENT_TYPE)
        return {"k": "vector", "el": el, "n": ssz_type.declared_length()}
    if issubclass(ssz_type, ssz.ProgressiveList):
        return {"k": "progressiveList", "el": descriptor(ssz_type.ELEMENT_TYPE)}
    if issubclass(ssz_type, ssz.List):
        el = descriptor(ssz_type.ELEMENT_TYPE)
        return {"k": "list", "el": el, "n": ssz_type.declared_limit()}
    # A progressive container adds a layout to what a struct already carries.
    if issubclass(ssz_type, ssz.ProgressiveContainer):
        return {
            "k": "progressiveContainer",
            "active": [bit == 1 for bit in ssz_type.ACTIVE_FIELDS],
            "names": [name for name, _ in ssz_type._FIELD_TYPES],
            "fields": [descriptor(held) for _, held in ssz_type._FIELD_TYPES],
        }
    if issubclass(ssz_type, ssz.Container):
        return {
            "k": "container",
            "names": [name for name, _ in ssz_type._FIELD_TYPES],
            "fields": [descriptor(held) for _, held in ssz_type._FIELD_TYPES],
        }
    if issubclass(ssz_type, ssz.CompatibleUnion):
        selectors = sorted(ssz_type.OPTIONS)
        return {
            "k": "compatibleUnion",
            "selectors": selectors,
            "options": [descriptor(ssz_type.OPTIONS[chosen]) for chosen in selectors],
        }
    raise AssertionError(f"no descriptor for {ssz_type.__name__}")


def json_value(value: ssz.SSZType) -> object:
    """
    The value as the Lean side reads it.

    Written out by shape rather than by the model serializer, so that the corpus
    says exactly what the Lean side reads, whatever the models do.

    Raises:
        AssertionError: A value outside the universe this corpus generates.
    """
    if isinstance(value, ssz.Boolean):
        return bool(value)
    if isinstance(value, ssz.BaseUint):
        return int(value)
    # A byte vector is its own hexadecimal string, with nothing wrapping it.
    if isinstance(value, ssz.ByteVector):
        return "0x" + bytes(value).hex()
    if isinstance(value, ssz.ByteList):
        return {"data": "0x" + bytes(value.data).hex()}
    if isinstance(value, (ssz.BitVector, ssz.BitList, ssz.ProgressiveBitList)):
        return {"data": [bool(bit) for bit in value.data]}
    if isinstance(value, ssz.CompatibleUnion):
        return {"selector": int(value.selector), "data": json_value(value.data)}
    if isinstance(value, (ssz.Container, ssz.ProgressiveContainer)):
        return {name: json_value(getattr(value, name)) for name, _ in type(value)._FIELD_TYPES}
    if isinstance(value, ssz.SSZCollection):
        return {"data": [json_value(element) for element in value.data]}
    raise AssertionError(f"no spelling for {type(value).__name__}")


MIXED_IN_WORDS: Final[dict[ssz.PathStep, str]] = {
    ssz.LENGTH_KEY: "length",
    ssz.ACTIVE_FIELDS_KEY: "activeFields",
    ssz.SELECTOR_KEY: "selector",
}
"""Each reserved path step, and the name the Lean side gives the same word."""


@dataclass(frozen=True, slots=True)
class Step:
    """
    One step of a path, kept in both spellings so neither can drift from the other.

    The two differ on one point.
    A struct field is named here and counted there.
    Names are part of this implementation's API rather than of SSZ.
    """

    python: ssz.PathStep
    """The step as this implementation takes it: a field name, a position, or a word."""

    lean: int | str
    """The step as the Lean side takes it: an ordinal, a selector, or the word's name."""

    def to_json(self) -> Json:
        """The step as the corpus writes it."""
        return {"p": self.lean} if isinstance(self.lean, int) else {"w": self.lean}
