"""The declaration a consumer rebuilds from one emitted descriptor, which is all a vector hands."""

from collections.abc import Mapping
from typing import Any, Final

from ssz import (
    BaseUint,
    BitList,
    BitVector,
    Boolean,
    ByteList,
    ByteVector,
    CompatibleUnion,
    Container,
    List,
    ProgressiveBitList,
    ProgressiveContainer,
    ProgressiveList,
    SSZType,
    Vector,
)

BASES: Final[Mapping[str, type[SSZType]]] = {
    "Boolean": Boolean,
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
}
"""The base each descriptor kind names, an unsigned integer being spelled by its width instead."""


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

    # An unsigned integer is the one kind named by its width rather than by a base of its own.
    if "bits" in descriptor:
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
        body["OPTIONS"] = {
            option["selector"]: build_declaration(option["type"])
            for option in descriptor["options"]
        }
    # A struct names its fields through annotations, which is how the declaration order survives.
    if "fields" in descriptor:
        body["__annotations__"] = {
            field["name"]: build_declaration(field["type"]) for field in descriptor["fields"]
        }
    return type(name, (BASES[descriptor["kind"]],), body)
