"""The declaration a consumer rebuilds from one emitted descriptor, which is all a vector hands."""

from collections.abc import Mapping
from typing import Any, Final

from ssz import (
    BaseUint,
    BitList,
    BitVector,
    Boolean,
    Byte,
    ByteList,
    ByteVector,
    CompatibleUnion,
    Container,
    List,
    ProgressiveBitList,
    ProgressiveContainer,
    ProgressiveList,
    SSZType,
    Union,
    Vector,
)

BASES: Final[Mapping[str, type[SSZType]]] = {
    "Boolean": Boolean,
    "Byte": Byte,
    "BitVector": BitVector,
    "BitList": BitList,
    "ProgressiveBitList": ProgressiveBitList,
    "ByteVector": ByteVector,
    "ByteList": ByteList,
    "Vector": Vector,
    "List": List,
    "ProgressiveList": ProgressiveList,
    "Container": Container,
    "ProgressiveContainer": ProgressiveContainer,
    "CompatibleUnion": CompatibleUnion,
    "Union": Union,
}
"""Every kind that names a base of its own, the rest being unsigned integers of a width."""


def _declared_options(descriptor: Mapping[str, Any]) -> Any:
    """A union's options as its own kind declares them, a missing type being the None option."""
    options = descriptor["options"]
    if descriptor["kind"] != "Union":
        return {option["selector"]: build_declaration(option["type"]) for option in options}
    return tuple(
        build_declaration(option["type"]) if "type" in option else None
        for option in sorted(options, key=lambda option: option["selector"])
    )


def build_declaration(descriptor: Mapping[str, Any], type_name: str | None = None) -> type[SSZType]:
    """
    Rebuild an SSZ type from one emitted descriptor, reading no declaration of this repo.

    Args:
        descriptor: One emitted `typeDescriptor`, as a consumer parses it out of the JSON.
        type_name: Name to declare it under, the kind standing in for a nested type.

    Returns:
        The type that declaration spells, which is illegal wherever the declaration is.
    """
    name = type_name or descriptor["kind"]
    body: dict[str, Any] = {"__module__": "consumer"}

    # A kind naming no base of its own is an unsigned integer, spelled by its width alone.
    base = BASES.get(descriptor["kind"])
    if base is None:
        return type(name, (BaseUint,), body | {"BITS": descriptor["bits"]})

    if "length" in descriptor:
        body["LENGTH"] = descriptor["length"]
    if "limit" in descriptor:
        body["LIMIT"] = descriptor["limit"]
    if "elementType" in descriptor:
        body["ELEMENT_TYPE"] = build_declaration(descriptor["elementType"])
    if "activeFields" in descriptor:
        body["ACTIVE_FIELDS"] = tuple(descriptor["activeFields"])
    if "options" in descriptor:
        body["OPTIONS"] = _declared_options(descriptor)
    # A struct names its fields through annotations, which is how the declaration order survives.
    if "fields" in descriptor:
        body["__annotations__"] = {
            field["name"]: build_declaration(field["type"]) for field in descriptor["fields"]
        }
    return type(name, (base,), body)
