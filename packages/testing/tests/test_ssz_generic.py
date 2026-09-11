"""A harness holding only a case name rebuilds the type, and reads the same vector back."""

import json
from pathlib import Path
from typing import Any

import pytest

from ssz import (
    BitList,
    BitVector,
    Boolean,
    ByteList,
    ByteVector,
    Container,
    List,
    ProgressiveBitList,
    ProgressiveList,
    SSZType,
    Uint8,
    Uint64,
    Uint256,
    Vector,
    hash_tree_root,
)
from ssz_testing.fixtures import describe_type
from ssz_testing.serialization import SSZTest
from ssz_testing.ssz_generic import (
    HANDLER_NEVER_IMPLEMENTED,
    NO_HANDLER_FOR_FORMAT,
    STRUCTURE_NOT_UPSTREAM,
    SUITE_ROOT,
    Handler,
    case_files,
    export,
    skip_reason,
    upstream_handler,
    upstream_value,
    yaml_document,
)
from ssz_testing.type_builder import build_declaration


class Bytes4(ByteVector):
    LENGTH = 4


class Numbers8(List[Uint8]):
    LIMIT = 8


class Message8(ByteList):
    LIMIT = 8


class Uint8Vector4(Vector[Uint8]):
    LENGTH = 4


class BoolVector3(Vector[Boolean]):
    LENGTH = 3


class Uint256Vector2(Vector[Uint256]):
    LENGTH = 2


class Bytes4Vector2(Vector[Bytes4]):
    LENGTH = 2


class Bits9(BitVector):
    LENGTH = 9


class Bits16(BitList):
    LIMIT = 16


class Numbers(ProgressiveList[Uint64]):
    pass


class Pair(Container):
    number: Uint8
    flag: Boolean


class Pairs(ProgressiveList[Pair]):
    pass


def declaration_of(ssz_type: type[SSZType]) -> dict[str, Any]:
    """The descriptor a vector of that type carries, which is all the export reads."""
    return describe_type(ssz_type).to_json(exclude_none=True)


BASIC_ELEMENTS = {
    "bool": {"kind": "Boolean"},
    "uint8": {"kind": "Uint8", "bits": 8},
    "uint16": {"kind": "Uint16", "bits": 16},
    "uint32": {"kind": "Uint32", "bits": 32},
    "uint64": {"kind": "Uint64", "bits": 64},
    "uint128": {"kind": "Uint128", "bits": 128},
    "uint256": {"kind": "Uint256", "bits": 256},
}


def type_from_case_name(handler: str, case_name: str) -> type[SSZType]:
    """Rebuild the type from the handler and the case name, the only inputs a harness reads."""
    words = case_name.split("_")
    if handler == "boolean":
        return build_declaration({"kind": "Boolean"})
    if handler == "progressive_bitlist":
        return build_declaration({"kind": "ProgressiveBitList"})
    if handler == "uints":
        return build_declaration({"kind": "Uint", "bits": int(words[1])})
    if handler == "bitvector":
        return build_declaration({"kind": "BitVector", "length": int(words[1])})
    if handler == "bitlist":
        return build_declaration({"kind": "BitList", "limit": int(words[1])})
    if handler == "basic_vector":
        return build_declaration(
            {"kind": "Vector", "length": int(words[2]), "elementType": BASIC_ELEMENTS[words[1]]}
        )
    return build_declaration({"kind": "ProgressiveList", "elementType": BASIC_ELEMENTS[words[1]]})


@pytest.mark.parametrize(
    "ssz_type,handler",
    [
        (Boolean, Handler("boolean", "")),
        (Uint8, Handler("uints", "uint_8")),
        (Uint256, Handler("uints", "uint_256")),
        (Bits9, Handler("bitvector", "bitvec_9")),
        (Bits16, Handler("bitlist", "bitlist_16")),
        (ProgressiveBitList, Handler("progressive_bitlist", "progbitlist")),
        (Bytes4, Handler("basic_vector", "vec_uint8_4")),
        (Uint8Vector4, Handler("basic_vector", "vec_uint8_4")),
        (BoolVector3, Handler("basic_vector", "vec_bool_3")),
        (Uint256Vector2, Handler("basic_vector", "vec_uint256_2")),
        (Numbers, Handler("basic_progressive_list", "proglist_uint64")),
    ],
    ids=lambda parameter: getattr(parameter, "__name__", None) or str(parameter),
)
def test_a_declaration_the_grammar_spells_names_its_handler(
    ssz_type: type[SSZType], handler: Handler
) -> None:
    """The grammar fixes the front of the case name, which is how a harness reads the type back."""
    assert upstream_handler(declaration_of(ssz_type)) == handler


@pytest.mark.parametrize(
    "ssz_type",
    [Numbers8, Message8, Bytes4Vector2, Pair, Pairs],
    ids=lambda ssz_type: ssz_type.__name__,
)
def test_a_declaration_the_grammar_cannot_spell_names_no_handler(ssz_type: type[SSZType]) -> None:
    """A sequence of composites, a byte list and a struct are outside every published handler."""
    assert upstream_handler(declaration_of(ssz_type)) is None


@pytest.mark.parametrize(
    "ssz_value",
    [
        Boolean(True),
        Uint8(255),
        Uint256(2**256 - 1),
        Bits9(data=[1, 0, 1, 0, 0, 0, 0, 0, 1]),
        Bits16(data=[1, 0, 1]),
        ProgressiveBitList(data=[1, 1, 0]),
        Bytes4(b"\xde\xad\xbe\xef"),
        Uint8Vector4(data=[222, 173, 190, 239]),
        BoolVector3(data=[Boolean(True), Boolean(False), Boolean(True)]),
        Uint256Vector2(data=[0, 2**256 - 1]),
        Numbers(data=[1, 2, 3]),
        Numbers(data=[]),
    ],
    ids=lambda ssz_value: type(ssz_value).__name__,
)
def test_the_type_a_case_name_rebuilds_reads_the_same_bytes_and_the_same_root(
    ssz_value: SSZType,
) -> None:
    """A fixed count of bytes and a vector of eight-bit integers are one type, spelled twice."""
    handler = upstream_handler(declaration_of(type(ssz_value)))
    assert handler is not None
    rebuilt = type_from_case_name(handler.name, handler.case_name("case"))

    encoded = ssz_value.encode_bytes()
    decoded = rebuilt.decode_bytes(encoded)

    assert decoded.encode_bytes() == encoded
    assert hash_tree_root(decoded) == hash_tree_root(ssz_value)


@pytest.mark.parametrize(
    "ssz_value,rendered",
    [
        (Boolean(True), "true"),
        (Boolean(False), "false"),
        (Uint8(255), "255"),
        (Uint64(2**64 - 1), "18446744073709551615"),
        (
            Uint256(2**256 - 1),
            "115792089237316195423570985008687907853269984665640564039457584007913129639935",
        ),
        (Bits9(data=[1, 0, 1, 0, 0, 0, 0, 0, 1]), "'0x0501'"),
        (Bits16(data=[1, 0, 1]), "'0x0d'"),
        (ProgressiveBitList(data=[1, 1, 0]), "'0x0b'"),
        (Bytes4(b"\xde\xad\xbe\xef"), "[222, 173, 190, 239]"),
        (Uint8Vector4(data=[222, 173, 190, 239]), "[222, 173, 190, 239]"),
        (BoolVector3(data=[Boolean(True), Boolean(False), Boolean(True)]), "[true, false, true]"),
        (Numbers(data=[1, 2, 3]), "[1, 2, 3]"),
        (Numbers(data=[]), "[]"),
    ],
    ids=lambda parameter: str(parameter)[:40],
)
def test_the_value_is_written_the_way_the_upstream_generator_wrote_it(
    ssz_value: SSZType, rendered: str
) -> None:
    """Numbers bare however wide, bitfields quoted hex, and a fixed count of bytes expanded."""
    case = SSZTest(type_name=type(ssz_value).__name__, value=ssz_value).generate().json_dict

    assert yaml_document(upstream_value(case["typeDescriptor"], case["value"])) == rendered


def test_a_valid_case_carries_the_root_the_value_and_the_bytes() -> None:
    """The three files the upstream format defines, and nothing else."""
    case = SSZTest(type_name="Uint8", value=Uint8(255)).generate().json_dict

    assert case_files(case) == {
        "serialized.ssz_snappy": b"\x01\x00\xff",
        "meta.yaml": (
            b"root: '0xff00000000000000000000000000000000000000000000000000000000000000'\n"
        ),
        "value.yaml": b"255\n",
    }


def test_an_invalid_case_carries_the_bytes_and_the_fault_beside_them() -> None:
    """Upstream carries only the bytes here, and the fault this suite names is kept alongside."""
    from ssz import ValueFault
    from ssz_testing import ExpectedRejection

    case = (
        SSZTest(
            type_name="Bits16",
            value=Bits16(data=[1]),
            raw_bytes="0x000010",
            expected_rejection=ExpectedRejection(reason=ValueFault.LIMIT),
        )
        .generate()
        .json_dict
    )

    assert case_files(case) == {
        "serialized.ssz_snappy": b"\x03\x08\x00\x00\x10",
        "rejection.yaml": b"reason: LIMIT\n",
    }


@pytest.mark.parametrize(
    "fixture_format,ssz_type,reason",
    [
        ("ssz_gindex", Pair, NO_HANDLER_FOR_FORMAT),
        ("proof", Pair, NO_HANDLER_FOR_FORMAT),
        ("ssz", Pair, STRUCTURE_NOT_UPSTREAM),
        ("ssz", Numbers8, HANDLER_NEVER_IMPLEMENTED),
        ("ssz", Bytes4Vector2, HANDLER_NEVER_IMPLEMENTED),
    ],
    ids=["gindex", "proof", "struct", "list", "complex_vector"],
)
def test_a_case_no_handler_reads_says_which_of_the_three_reasons_keeps_it_out(
    fixture_format: str, ssz_type: type[SSZType], reason: str
) -> None:
    """A format the runner never answered, a struct it names by hand, a handler never written."""
    assert skip_reason(fixture_format, declaration_of(ssz_type)) == reason


def test_the_case_name_opens_with_what_the_grammar_fixes_and_then_the_source_id() -> None:
    """The prefix is the contract; the rest tells a reader which vector of this suite it is."""
    assert Handler("uints", "uint_8").case_name("basic_type/uint8/max") == (
        "uint_8_basic_type_uint8_max"
    )
    assert Handler("boolean", "").case_name("basic_type/boolean/true") == "basic_type_boolean_true"


FILLER_MODULE = '''
"""One vector of every shape the export carries, and of every shape it does not."""

from ssz import (
    BitList,
    BitVector,
    Boolean,
    ByteList,
    ByteVector,
    Container,
    List,
    ProgressiveBitList,
    ProgressiveList,
    Uint8,
    Uint64,
    ValueFault,
    Vector,
)
from ssz_testing import ExpectedRejection, GindexTestFiller, SSZTestFiller


class Bytes4(ByteVector):
    """Four bytes."""

    LENGTH = 4


class Bits9(BitVector):
    """Nine bits."""

    LENGTH = 9


class Bits16(BitList):
    """Up to sixteen bits."""

    LIMIT = 16


class Numbers(ProgressiveList[Uint64]):
    """Unbounded eight-byte numbers."""


class Numbers8(List[Uint8]):
    """Up to eight one-byte numbers."""

    LIMIT = 8


class Message8(ByteList):
    """Up to eight bytes."""

    LIMIT = 8


class Uint8Vector4(Vector[Uint8]):
    """Four one-byte numbers."""

    LENGTH = 4


class Pair(Container):
    """One number and one flag."""

    number: Uint8
    flag: Boolean


def test_a_number(ssz_test: SSZTestFiller) -> None:
    """The widest one-byte value."""
    ssz_test(case_id="uint8/max", type_name="Uint8", value=Uint8(255))


def test_a_flag(ssz_test: SSZTestFiller) -> None:
    """A true boolean."""
    ssz_test(case_id="boolean/true", type_name="Boolean", value=Boolean(True))


def test_a_bit_vector(ssz_test: SSZTestFiller) -> None:
    """Nine bits over two bytes."""
    ssz_test(
        case_id="bits9/mixed",
        type_name="Bits9",
        value=Bits9(data=[1, 0, 1, 0, 0, 0, 0, 0, 1]),
    )


def test_a_bit_list(ssz_test: SSZTestFiller) -> None:
    """Three bits and a delimiter."""
    ssz_test(case_id="bits16/three", type_name="Bits16", value=Bits16(data=[1, 0, 1]))


def test_a_progressive_bit_list(ssz_test: SSZTestFiller) -> None:
    """Three bits with no limit."""
    ssz_test(
        case_id="progbits/three",
        type_name="ProgressiveBitList",
        value=ProgressiveBitList(data=[1, 1, 0]),
    )


def test_a_byte_vector(ssz_test: SSZTestFiller) -> None:
    """Four bytes."""
    ssz_test(case_id="bytes4/nonzero", type_name="Bytes4", value=Bytes4(b"\\xde\\xad\\xbe\\xef"))


def test_a_vector_of_numbers(ssz_test: SSZTestFiller) -> None:
    """The same four bytes spelled as a vector of one-byte numbers."""
    ssz_test(
        case_id="uint8_vector4/nonzero",
        type_name="Uint8Vector4",
        value=Uint8Vector4(data=[222, 173, 190, 239]),
    )


def test_a_progressive_list(ssz_test: SSZTestFiller) -> None:
    """Three eight-byte numbers."""
    ssz_test(case_id="proglist/three", type_name="Numbers", value=Numbers(data=[1, 2, 3]))


def test_bytes_no_decoder_may_accept(ssz_test: SSZTestFiller) -> None:
    """More bits than the limit admits."""
    ssz_test(
        case_id="bits16/invalid/over_limit",
        type_name="Bits16",
        value=Bits16(data=[1]),
        raw_bytes="0x000010",
        expected_rejection=ExpectedRejection(reason=ValueFault.LIMIT),
    )


def test_a_struct(ssz_test: SSZTestFiller) -> None:
    """A struct, which the upstream handler names by hand."""
    ssz_test(
        case_id="pair/typical",
        type_name="Pair",
        value=Pair(number=Uint8(1), flag=Boolean(True)),
    )


def test_a_bounded_list(ssz_test: SSZTestFiller) -> None:
    """A bounded list, whose handler was never implemented upstream."""
    ssz_test(case_id="numbers8/three", type_name="Numbers8", value=Numbers8(data=[1, 2, 3]))


def test_a_byte_list(ssz_test: SSZTestFiller) -> None:
    """A byte list, whose handler was never implemented upstream."""
    ssz_test(case_id="message8/hello", type_name="Message8", value=Message8(data=b"hello"))


def test_an_index(ssz_gindex_test: GindexTestFiller) -> None:
    """A path resolved to an index, which the upstream runner never asked about."""
    ssz_gindex_test(
        case_id="gindex/pair/flag",
        type_name="Pair",
        ssz_type=Pair,
        path=("flag",),
        gindex=3,
    )
'''

COLLIDING_MODULE = '''
"""Two case ids that differ only where the export joins the id's segments."""

from ssz import Uint8
from ssz_testing import SSZTestFiller


def test_slashed(ssz_test: SSZTestFiller) -> None:
    """A two-segment id."""
    ssz_test(case_id="uint8/one", type_name="Uint8", value=Uint8(1))


def test_joined(ssz_test: SSZTestFiller) -> None:
    """The same words as one segment."""
    ssz_test(case_id="uint8_one", type_name="Uint8", value=Uint8(2))
'''

SKIPPED_REASONS = {
    "pair/typical": STRUCTURE_NOT_UPSTREAM,
    "numbers8/three": HANDLER_NEVER_IMPLEMENTED,
    "message8/hello": HANDLER_NEVER_IMPLEMENTED,
    "gindex/pair/flag": NO_HANDLER_FOR_FORMAT,
}

EXPORTED_CASES = {
    "uint8/max": ("uints", "valid", "uint_8_uint8_max"),
    "boolean/true": ("boolean", "valid", "boolean_true"),
    "bits9/mixed": ("bitvector", "valid", "bitvec_9_bits9_mixed"),
    "bits16/three": ("bitlist", "valid", "bitlist_16_bits16_three"),
    "progbits/three": ("progressive_bitlist", "valid", "progbitlist_progbits_three"),
    "bytes4/nonzero": ("basic_vector", "valid", "vec_uint8_4_bytes4_nonzero"),
    "uint8_vector4/nonzero": ("basic_vector", "valid", "vec_uint8_4_uint8_vector4_nonzero"),
    "proglist/three": ("basic_progressive_list", "valid", "proglist_uint64_proglist_three"),
    "bits16/invalid/over_limit": ("bitlist", "invalid", "bitlist_16_bits16_invalid_over_limit"),
}


def fill(pytester: pytest.Pytester, module: str, filled: int) -> Path:
    """Run one filler module the way the fill command does, and return the tree it wrote."""
    pytester.makeini("[pytest]\ntestpaths = tests\n")
    pytester.makepyfile(**{"tests/fillers/test_shapes": module})
    pytester.runpytest("-p", "ssz_testing.plugin", "--clean").assert_outcomes(passed=filled)
    return pytester.path / "fixtures"


@pytest.fixture
def exported(pytester: pytest.Pytester) -> tuple[Path, dict[str, Any]]:
    """A filled tree exported into a sibling directory, against the manifest it produced."""
    source = fill(pytester, FILLER_MODULE, len(EXPORTED_CASES) + len(SKIPPED_REASONS))
    destination = pytester.path / "ssz-generic"
    return destination, export(source, destination)


def test_every_source_case_is_either_exported_or_named_as_left_out(
    exported: tuple[Path, dict[str, Any]],
) -> None:
    """The two lists together are the coverage claim, so neither may lose a case."""
    _, manifest = exported

    assert {row["id"] for row in manifest["exported"]} == set(EXPORTED_CASES)
    assert {row["id"]: row["reason"] for row in manifest["skipped"]} == SKIPPED_REASONS
    assert manifest["sourceCaseCount"] == len(EXPORTED_CASES) + len(SKIPPED_REASONS)


def test_each_exported_case_sits_where_the_upstream_runner_looks_for_it(
    exported: tuple[Path, dict[str, Any]],
) -> None:
    """A harness walks handler, then verdict, then case, from the root of an extracted tarball."""
    destination, manifest = exported

    placed = {
        row["id"]: (row["handler"], row["suite"], row["case"]) for row in manifest["exported"]
    }
    assert placed == EXPORTED_CASES
    for handler, suite, case in EXPORTED_CASES.values():
        assert (destination / SUITE_ROOT / handler / suite / case).is_dir()


def test_a_case_holds_the_files_its_verdict_calls_for(
    exported: tuple[Path, dict[str, Any]],
) -> None:
    """A valid case carries a root and a value, an invalid one carries the fault instead."""
    destination, _ = exported
    suites = destination / SUITE_ROOT

    valid = suites / "basic_vector" / "valid" / "vec_uint8_4_bytes4_nonzero"
    assert sorted(path.name for path in valid.iterdir()) == [
        "meta.yaml",
        "serialized.ssz_snappy",
        "value.yaml",
    ]
    assert (valid / "value.yaml").read_text(encoding="utf-8") == "[222, 173, 190, 239]\n"
    assert (valid / "serialized.ssz_snappy").read_bytes() == b"\x04\x0c\xde\xad\xbe\xef"

    invalid = suites / "bitlist" / "invalid" / "bitlist_16_bits16_invalid_over_limit"
    assert sorted(path.name for path in invalid.iterdir()) == [
        "rejection.yaml",
        "serialized.ssz_snappy",
    ]
    assert (invalid / "rejection.yaml").read_text(encoding="utf-8") == "reason: LIMIT\n"


def test_the_tree_documents_itself(exported: tuple[Path, dict[str, Any]]) -> None:
    """A consumer downloads the tarball and nothing else, so the reading guide travels with it."""
    destination, manifest = exported

    assert (destination / "README.md").exists()
    assert json.loads((destination / "manifest.json").read_text(encoding="utf-8")) == manifest


def test_the_same_source_tree_exports_to_the_same_bytes(
    exported: tuple[Path, dict[str, Any]], pytester: pytest.Pytester
) -> None:
    """The tarball is byte-reproducible, so nothing in the export may depend on the run."""
    destination, _ = exported
    again = pytester.path / "ssz-generic-again"
    export(pytester.path / "fixtures", again)

    written = {
        path.relative_to(destination): path.read_bytes()
        for path in destination.rglob("*")
        if path.is_file()
    }
    assert written == {
        path.relative_to(again): path.read_bytes() for path in again.rglob("*") if path.is_file()
    }


def test_two_source_ids_naming_one_case_directory_are_refused(
    pytester: pytest.Pytester,
) -> None:
    """The id is the only thing telling two cases of one type apart, so a clash cannot be lost."""
    source = fill(pytester, COLLIDING_MODULE, 2)

    with pytest.raises(ValueError, match="both name"):
        export(source, pytester.path / "ssz-generic")


def test_a_source_tree_of_another_format_version_is_refused(pytester: pytest.Pytester) -> None:
    """The export reads a documented shape, and a tree of another shape is not that shape."""
    source = fill(pytester, COLLIDING_MODULE, 2)
    manifest = json.loads((source / "manifest.json").read_text(encoding="utf-8"))
    manifest["formatVersion"] += 1
    (source / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")

    with pytest.raises(ValueError, match="state format version"):
        export(source, pytester.path / "ssz-generic")
