"""Export of the filled vectors as the `ssz_generic` tree consensus-specs used to publish."""

import json
import shutil
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Final

from ssz_testing.hex_codec import from_hex
from ssz_testing.plugin import FIXTURE_FORMAT_VERSION, GENERATOR, json_document
from ssz_testing.snappy import compress

RUNNER: Final = "ssz_generic"
"""The consensus-specs test runner this tree is shaped for."""

SUITE_ROOT: Final = Path("tests", "general", "phase0", RUNNER)
"""Where a harness looks for that runner, counted from the root of an extracted tarball."""

EXPORT_FORMAT_VERSION: Final = 1
"""Shape of the exported tree, bumped whenever a consumer has to change to keep reading it."""

SOURCE_FORMAT: Final = "ssz"
"""The one fixture format that answers the question `ssz_generic` asks: are these bytes valid."""

BASIC_ELEMENT_NAMES: Final = {
    "Boolean": "bool",
    "Uint8": "uint8",
    "Uint16": "uint16",
    "Uint32": "uint32",
    "Uint64": "uint64",
    "Uint128": "uint128",
    "Uint256": "uint256",
}
"""How the case-name grammar spells each element type a basic sequence may hold."""

BITFIELD_KINDS: Final = frozenset({"BitVector", "BitList", "ProgressiveBitList"})
"""Kinds whose value is the hex of the bytes they serialize to, delimiter bit included."""

FIXED_STRUCTURE_KINDS: Final = frozenset({"Container", "ProgressiveContainer", "CompatibleUnion"})
"""Kinds whose handler resolves a case name against a fixed set of structures a harness holds."""

NO_HANDLER_FOR_FORMAT: Final = (
    "ssz_generic asks only whether bytes decode, and this asks something else"
)
"""Why a vector of another fixture format is left out."""

STRUCTURE_NOT_UPSTREAM: Final = (
    "the handler names one of a fixed set of structures, and this type is not among them"
)
"""Why a struct, a progressive struct or a union is left out."""

HANDLER_NEVER_IMPLEMENTED: Final = (
    "the handler for this kind is declared upstream but was never implemented"
)
"""Why a bounded list, a byte list or a sequence of composites is left out."""

UpstreamScalar = bool | int | str
"""What one YAML scalar of an exported value can be."""

UpstreamValue = UpstreamScalar | list[UpstreamScalar]
"""A whole exported value: a scalar, or a flat sequence of them, every handler being basic."""


@dataclass(frozen=True, slots=True)
class Handler:
    """One `ssz_generic` handler, against the prefix its case names have to open with."""

    name: str
    """Directory the handler's cases sit under."""

    case_prefix: str
    """What the grammar fixes at the front of a case name, empty where the grammar fixes nothing."""

    def case_name(self, case_id: str) -> str:
        """The case directory's name: what the grammar demands, then the source id for a reader."""
        described = case_id.replace("/", "_")
        return f"{self.case_prefix}_{described}" if self.case_prefix else described


def upstream_handler(descriptor: dict[str, Any]) -> Handler | None:
    """The handler that rebuilds this declaration from a case name, or nothing where none does."""
    kind = descriptor["kind"]
    if kind == "Boolean":
        return Handler("boolean", "")
    if kind.startswith("Uint"):
        return Handler("uints", f"uint_{descriptor['bits']}")
    if kind == "BitVector":
        return Handler("bitvector", f"bitvec_{descriptor['length']}")
    if kind == "BitList":
        return Handler("bitlist", f"bitlist_{descriptor['limit']}")
    if kind == "ProgressiveBitList":
        return Handler("progressive_bitlist", "progbitlist")
    # A fixed count of bytes is a vector of 8-bit integers, spelled and merkleized alike.
    if kind == "ByteVector":
        return Handler("basic_vector", f"vec_uint8_{descriptor['length']}")
    element = BASIC_ELEMENT_NAMES.get(descriptor.get("elementType", {}).get("kind", ""))
    if element is None:
        return None
    if kind == "Vector":
        return Handler("basic_vector", f"vec_{element}_{descriptor['length']}")
    if kind == "ProgressiveList":
        return Handler("basic_progressive_list", f"proglist_{element}")
    return None


def skip_reason(fixture_format: str, descriptor: dict[str, Any]) -> str:
    """Why no handler reads a case, in the terms the upstream runner states."""
    if fixture_format != SOURCE_FORMAT:
        return NO_HANDLER_FOR_FORMAT
    if descriptor["kind"] in FIXED_STRUCTURE_KINDS:
        return STRUCTURE_NOT_UPSTREAM
    return HANDLER_NEVER_IMPLEMENTED


def upstream_scalar(descriptor: dict[str, Any], value: Any) -> UpstreamScalar:
    """One scalar as the upstream writer holds it: a flag, a number, or the hex of a bitfield."""
    kind = descriptor["kind"]
    if kind == "Boolean" or kind in BITFIELD_KINDS:
        return value
    return int(value)


def upstream_value(descriptor: dict[str, Any], value: Any) -> UpstreamValue:
    """The value as the upstream generator's YAML writer holds it, read off this suite's JSON."""
    if descriptor["kind"] == "ByteVector":
        return list(from_hex(value))
    if "elementType" in descriptor:
        return [upstream_scalar(descriptor["elementType"], element) for element in value]
    return upstream_scalar(descriptor, value)


def yaml_scalar(value: UpstreamScalar) -> str:
    """One scalar spelled the way the upstream writer spells it, hex quoted and numbers bare."""
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, int):
        return str(value)
    return f"'{value}'"


def yaml_document(value: UpstreamValue) -> str:
    """A whole value as one YAML document, a sequence written flow style on a single line."""
    if isinstance(value, list):
        return "[" + ", ".join(yaml_scalar(element) for element in value) + "]"
    return yaml_scalar(value)


def case_files(case: dict[str, Any]) -> dict[str, bytes]:
    """What one case directory holds: the bytes always, and then what their verdict calls for."""
    files = {"serialized.ssz_snappy": compress(from_hex(case["serialized"]))}
    if case["valid"]:
        files["meta.yaml"] = f"root: '{case['root']}'\n".encode()
        files["value.yaml"] = (
            yaml_document(upstream_value(case["typeDescriptor"], case["value"])) + "\n"
        ).encode()
    else:
        # Upstream invalid cases carry only the bytes; the fault this suite names is kept beside
        # them under a name no handler reads, so a harness sees the tree it expects.
        files["rejection.yaml"] = f"reason: {case['rejectionReason']}\n".encode()
    return files


_EXPORT_DOCUMENT: Final = Path(__file__).parent / "ssz_generic_readme.md"
"""How to read the exported tree, copied in as the output directory's README."""


def export(source: Path, destination: Path) -> dict[str, Any]:
    """
    Write the `ssz_generic` view of a filled tree, and return the manifest accounting for it.

    Every case of the source tree is named exactly once, under the cases exported or those no
    handler reads, so the two lists together are the coverage claim.

    Raises:
        ValueError: When the source tree states a format version this export does not read.
        ValueError: When two source cases resolve to one case directory.
    """
    source_manifest = json.loads((source / "manifest.json").read_text(encoding="utf-8"))
    if source_manifest["formatVersion"] != FIXTURE_FORMAT_VERSION:
        raise ValueError(
            f"the vectors under '{source}' state format version "
            f"{source_manifest['formatVersion']}, and this export reads version "
            f"{FIXTURE_FORMAT_VERSION}"
        )

    index = json.loads((source / "index.json").read_text(encoding="utf-8"))
    exported: list[dict[str, str]] = []
    skipped: list[dict[str, str]] = []
    claimed: dict[str, str] = {}

    for row in index["cases"]:
        case = json.loads((source / row["path"]).read_text(encoding="utf-8"))
        fixture_format = Path(row["path"]).parts[0]
        descriptor = case["typeDescriptor"]
        handler = upstream_handler(descriptor) if fixture_format == SOURCE_FORMAT else None
        if handler is None:
            skipped.append({"id": row["id"], "reason": skip_reason(fixture_format, descriptor)})
            continue

        suite = "valid" if case["valid"] else "invalid"
        name = handler.case_name(row["id"])
        directory = SUITE_ROOT / handler.name / suite / name
        claimed_by = claimed.setdefault(str(directory), row["id"])
        if claimed_by != row["id"]:
            raise ValueError(f"case ids '{claimed_by}' and '{row['id']}' both name '{directory}'")

        (destination / directory).mkdir(parents=True, exist_ok=True)
        for file_name, content in case_files(case).items():
            (destination / directory / file_name).write_bytes(content)
        exported.append({"id": row["id"], "handler": handler.name, "suite": suite, "case": name})

    destination.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(_EXPORT_DOCUMENT, destination / "README.md")
    manifest = {
        "formatVersion": EXPORT_FORMAT_VERSION,
        "specVersion": source_manifest["specVersion"],
        "generator": GENERATOR,
        "runner": RUNNER,
        "sourceCaseCount": len(index["cases"]),
        "exported": exported,
        "skipped": skipped,
    }
    (destination / "manifest.json").write_text(json_document(manifest), encoding="utf-8")
    return manifest
