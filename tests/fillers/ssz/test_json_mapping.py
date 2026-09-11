"""SSZ conformance test vectors for the canonical JSON mapping every type assigns its values."""

import pytest

from ssz import (
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
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Uint128,
    Uint256,
    Vector,
)
from ssz_testing import JsonFault, JsonMappingFiller

pytestmark = pytest.mark.tags("json")

UNION_IS_WRITE_ONLY = (
    "a compatible union declares its option as an is-instance field, which no JSON value satisfies"
)
"""Why the union document below is only written here, and never read back."""


class JsonUint16Vector3(Vector[Uint16]):
    """Three numbers, the shape the mapping writes as an array of decimal strings."""

    LENGTH = 3


class JsonUint16List4(List[Uint16]):
    """Up to four numbers, the bounded array of the same rendering."""

    LIMIT = 4


class JsonUint16ProgressiveList(ProgressiveList[Uint16]):
    """Any number of numbers, per EIP-7916."""


class JsonByteVector4(ByteVector):
    """Four bytes of opaque data."""

    LENGTH = 4


class JsonByteList8(ByteList):
    """Up to eight bytes of opaque data."""

    LIMIT = 8


class JsonByteVector4Elementwise(Vector[Byte]):
    """The other spelling of a fixed byte array, an element type in place of a byte count."""

    LENGTH = 4


class JsonByteList4Elementwise(List[Byte]):
    """The other spelling of a bounded byte array."""

    LIMIT = 4


class JsonByteProgressiveList(ProgressiveList[Byte]):
    """The unbounded byte array, which only the elementwise spelling reaches."""


class JsonBitVector5(BitVector):
    """Five bits, packed into the one byte they fit in."""

    LENGTH = 5


class JsonBitList20(BitList):
    """Up to twenty bits, closed by a delimiter bit."""

    LIMIT = 20


class JsonPoint(Container):
    """Two numbers under names, which the mapping writes as an object."""

    x: Uint16
    y: Uint16


class JsonCorner(ProgressiveContainer):
    """Two numbers holding layout positions 0 and 2, per EIP-7495."""

    ACTIVE_FIELDS = (1, 0, 1)

    x: Uint16
    y: Uint16


class JsonEdge(ProgressiveContainer):
    """The compatible option, holding positions 1 and 2."""

    ACTIVE_FIELDS = (0, 1, 1)

    length: Uint16
    y: Uint16


class JsonShape(CompatibleUnion):
    """A union of two shapes, which the mapping writes as a selector and its data."""

    OPTIONS = {1: JsonCorner, 2: JsonEdge}


def test_uint8(ssz_json_test: JsonMappingFiller) -> None:
    """
    An eight-bit unsigned integer is written as its decimal digits in a string.

    Given
    -----
    - the value 255 as a one-byte uint.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is the string "255", the same number the byte case writes as hex.
    """
    ssz_json_test(
        case_id="json/uint8",
        type_name="Uint8",
        ssz_type=Uint8,
        value=Uint8(255),
        document="255",
    )


def test_uint16(ssz_json_test: JsonMappingFiller) -> None:
    """
    A sixteen-bit unsigned integer is written as its decimal digits in a string.

    Given
    -----
    - the value 4660 as a two-byte uint.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is the string "4660", never the hex the wire format uses.
    """
    ssz_json_test(
        case_id="json/uint16",
        type_name="Uint16",
        ssz_type=Uint16,
        value=Uint16(4660),
        document="4660",
    )


def test_uint32(ssz_json_test: JsonMappingFiller) -> None:
    """
    A thirty-two-bit unsigned integer at its maximum is written as decimal digits in a string.

    Given
    -----
    - the value 4294967295, which is the largest a four-byte uint holds.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is the string "4294967295".
    """
    ssz_json_test(
        case_id="json/uint32",
        type_name="Uint32",
        ssz_type=Uint32,
        value=Uint32(4294967295),
        document="4294967295",
    )


def test_uint64(ssz_json_test: JsonMappingFiller) -> None:
    """
    A sixty-four-bit unsigned integer at its maximum survives the mapping intact.

    Given
    -----
    - the value 18446744073709551615, which a double rounds to 18446744073709551616.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is the string "18446744073709551615", which is why the mapping uses strings.
    """
    ssz_json_test(
        case_id="json/uint64",
        type_name="Uint64",
        ssz_type=Uint64,
        value=Uint64(18446744073709551615),
        document="18446744073709551615",
    )


def test_uint128(ssz_json_test: JsonMappingFiller) -> None:
    """
    A hundred-and-twenty-eight-bit unsigned integer at its maximum is written as decimal digits.

    Given
    -----
    - the value 2**128 - 1.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is that number's decimal digits in a string.
    """
    ssz_json_test(
        case_id="json/uint128",
        type_name="Uint128",
        ssz_type=Uint128,
        value=Uint128(2**128 - 1),
        document="340282366920938463463374607431768211455",
    )


def test_uint256(ssz_json_test: JsonMappingFiller) -> None:
    """
    A two-hundred-and-fifty-six-bit unsigned integer at its maximum is written as decimal digits.

    Given
    -----
    - the value 2**256 - 1.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is that number's decimal digits in a string, 78 of them.
    """
    ssz_json_test(
        case_id="json/uint256",
        type_name="Uint256",
        ssz_type=Uint256,
        value=Uint256(2**256 - 1),
        document="115792089237316195423570985008687907853269984665640564039457584007913129639935",
    )


def test_byte(ssz_json_test: JsonMappingFiller) -> None:
    """
    A byte is written as a hex byte string, where the uint of the same width is written decimal.

    Given
    -----
    - the value 255 as a byte.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is "0xff", against the "255" the one-byte uint case writes.
    """
    ssz_json_test(
        case_id="json/byte",
        type_name="Byte",
        ssz_type=Byte,
        value=Byte(255),
        document="0xff",
    )


def test_boolean(ssz_json_test: JsonMappingFiller) -> None:
    """
    A boolean is written as a JSON bool, the one kind the mapping does not put in a string.

    Given
    -----
    - the value true.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is the bare literal true.
    """
    ssz_json_test(
        case_id="json/boolean",
        type_name="Boolean",
        ssz_type=Boolean,
        value=Boolean(True),
        document=True,
    )


def test_byte_vector(ssz_json_test: JsonMappingFiller) -> None:
    """
    A fixed byte array is written as one hex byte string, not as an array of its bytes.

    Given
    -----
    - four bytes of opaque data.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is "0x11223344", carrying no wrapping object.
    """
    ssz_json_test(
        case_id="json/byte_vector",
        type_name="JsonByteVector4",
        ssz_type=JsonByteVector4,
        value=JsonByteVector4(b"\x11\x22\x33\x44"),
        document="0x11223344",
    )


def test_byte_list(ssz_json_test: JsonMappingFiller) -> None:
    """
    A bounded byte array is written as one hex byte string, its limit showing nowhere.

    Given
    -----
    - two bytes in an array admitting up to eight.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is "0x1122".
    """
    ssz_json_test(
        case_id="json/byte_list",
        type_name="JsonByteList8",
        ssz_type=JsonByteList8,
        value=JsonByteList8(data=b"\x11\x22"),
        document="0x1122",
    )


def test_vector(ssz_json_test: JsonMappingFiller) -> None:
    """
    A vector of a non-byte element type is written as a bare array of its elements.

    Given
    -----
    - three two-byte numbers.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is the array ["1", "2", "3"], each element written as its own type is.
    """
    ssz_json_test(
        case_id="json/vector",
        type_name="JsonUint16Vector3",
        ssz_type=JsonUint16Vector3,
        value=JsonUint16Vector3(data=[Uint16(1), Uint16(2), Uint16(3)]),
        document=["1", "2", "3"],
    )


def test_vector_of_bytes(ssz_json_test: JsonMappingFiller) -> None:
    """
    A vector whose element type is the byte is written as a hex string, not as an array.

    Given
    -----
    - four bytes spelled as a vector of a byte element type.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is "0x11223344", the same as the fixed byte array spelling.
    """
    ssz_json_test(
        case_id="json/vector_of_bytes",
        type_name="JsonByteVector4Elementwise",
        ssz_type=JsonByteVector4Elementwise,
        value=JsonByteVector4Elementwise.of(0x11, 0x22, 0x33, 0x44),
        document="0x11223344",
    )


def test_list(ssz_json_test: JsonMappingFiller) -> None:
    """
    A bounded list of a non-byte element type is written as a bare array.

    Given
    -----
    - two numbers in a list admitting up to four.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is the array ["1", "2"], with nothing recording the limit.
    """
    ssz_json_test(
        case_id="json/list",
        type_name="JsonUint16List4",
        ssz_type=JsonUint16List4,
        value=JsonUint16List4(data=[Uint16(1), Uint16(2)]),
        document=["1", "2"],
    )


def test_list_of_bytes(ssz_json_test: JsonMappingFiller) -> None:
    """
    A bounded list whose element type is the byte is written as a hex string.

    Given
    -----
    - two bytes spelled as a list of a byte element type.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is "0x1122", the same as the bounded byte array spelling.
    """
    ssz_json_test(
        case_id="json/list_of_bytes",
        type_name="JsonByteList4Elementwise",
        ssz_type=JsonByteList4Elementwise,
        value=JsonByteList4Elementwise.of(0x11, 0x22),
        document="0x1122",
    )


def test_progressive_list(ssz_json_test: JsonMappingFiller) -> None:
    """
    An unbounded list of a non-byte element type is written as a bare array.

    Given
    -----
    - two numbers on a progressive spine.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is the array ["1", "2"], the spine showing nowhere.
    """
    ssz_json_test(
        case_id="json/progressive_list",
        type_name="JsonUint16ProgressiveList",
        ssz_type=JsonUint16ProgressiveList,
        value=JsonUint16ProgressiveList(data=[Uint16(1), Uint16(2)]),
        document=["1", "2"],
    )


def test_progressive_list_of_bytes(ssz_json_test: JsonMappingFiller) -> None:
    """
    An unbounded list whose element type is the byte is written as a hex string.

    Given
    -----
    - two bytes on a progressive spine.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is "0x1122", which is the only spelling this shape has.
    """
    ssz_json_test(
        case_id="json/progressive_list_of_bytes",
        type_name="JsonByteProgressiveList",
        ssz_type=JsonByteProgressiveList,
        value=JsonByteProgressiveList.of(0x11, 0x22),
        document="0x1122",
    )


def test_bit_vector(ssz_json_test: JsonMappingFiller) -> None:
    """
    A bit vector is written as the hex of the bytes it serializes to.

    Given
    -----
    - the five bits 1, 0, 1, 0, 1, which pack into the single byte 0x15.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is "0x15", the three padding bits left at zero.
    """
    ssz_json_test(
        case_id="json/bit_vector",
        type_name="JsonBitVector5",
        ssz_type=JsonBitVector5,
        value=JsonBitVector5(data=[Boolean(bit) for bit in (1, 0, 1, 0, 1)]),
        document="0x15",
    )


def test_bit_list(ssz_json_test: JsonMappingFiller) -> None:
    """
    A bit list is written as the hex of its encoding, delimiter bit included.

    Given
    -----
    - the three bits 1, 0, 1, closed by a delimiter bit at position 3.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is "0x0d", which is 0b1101: the three bits under their delimiter.
    """
    ssz_json_test(
        case_id="json/bit_list",
        type_name="JsonBitList20",
        ssz_type=JsonBitList20,
        value=JsonBitList20(data=[Boolean(bit) for bit in (1, 0, 1)]),
        document="0x0d",
    )


def test_progressive_bit_list(ssz_json_test: JsonMappingFiller) -> None:
    """
    An unbounded bit list is written the same way a bounded one is.

    Given
    -----
    - the three bits 1, 0, 1 on a progressive spine.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is "0x0d", indistinguishable from the bounded spelling.
    """
    ssz_json_test(
        case_id="json/progressive_bit_list",
        type_name="ProgressiveBitList",
        ssz_type=ProgressiveBitList,
        value=ProgressiveBitList(data=[Boolean(bit) for bit in (1, 0, 1)]),
        document="0x0d",
    )


def test_container(ssz_json_test: JsonMappingFiller) -> None:
    """
    A container is written as an object keyed by its declared field names.

    Given
    -----
    - a two-field struct holding 1 and 2.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is {"x": "1", "y": "2"}, each field written as its own type is.
    """
    ssz_json_test(
        case_id="json/container",
        type_name="JsonPoint",
        ssz_type=JsonPoint,
        value=JsonPoint(x=Uint16(1), y=Uint16(2)),
        document={"x": "1", "y": "2"},
    )


def test_progressive_container(ssz_json_test: JsonMappingFiller) -> None:
    """
    A progressive container is written as an object, its layout showing nowhere in the document.

    Given
    -----
    - a struct holding 1 and 2 at layout positions 0 and 2.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is {"x": "1", "y": "2"}, the same as the flat struct of the same fields.
    """
    ssz_json_test(
        case_id="json/progressive_container",
        type_name="JsonCorner",
        ssz_type=JsonCorner,
        value=JsonCorner(x=Uint16(1), y=Uint16(2)),
        document={"x": "1", "y": "2"},
    )


def test_compatible_union(ssz_json_test: JsonMappingFiller) -> None:
    """
    A compatible union is written as an object of a selector and the data it names.

    Given
    -----
    - selector 1, naming a struct holding 1 and 2.

    When
    ----
    - the value is written through the JSON mapping.

    Then
    ----
    - the document is {"selector": "1", "data": {"x": "1", "y": "2"}}.
    - this implementation does not read that document back, which the vector records.
    """
    ssz_json_test(
        case_id="json/compatible_union",
        type_name="JsonShape",
        ssz_type=JsonShape,
        value=JsonShape(selector=Uint8(1), data=JsonCorner(x=Uint16(1), y=Uint16(2))),
        document={"selector": "1", "data": {"x": "1", "y": "2"}},
        not_read_back=UNION_IS_WRITE_ONLY,
    )


def test_a_hex_byte_string_without_its_prefix(ssz_json_test: JsonMappingFiller) -> None:
    """
    A hex byte string written without its 0x prefix is no rendering of a byte.

    Given
    -----
    - the document "ff", read against the byte type.

    When
    ----
    - a parser reads it through the JSON mapping.

    Then
    ----
    - the document is refused, the prefix being part of the spelling and not decoration.
    """
    ssz_json_test(
        case_id="json/byte/invalid/no_hex_prefix",
        type_name="Byte",
        ssz_type=Byte,
        document="ff",
        rejection_reason=JsonFault.HEX_PREFIX,
        message_substring="String should match pattern",
    )


def test_a_bitfield_setting_a_padding_bit(ssz_json_test: JsonMappingFiller) -> None:
    """
    A bit vector whose hex sets a bit past its declared length is refused.

    Given
    -----
    - the document "0x35", which is 0b00110101 and sets bit 5 of a five-bit vector.

    When
    ----
    - a parser reads it through the JSON mapping.

    Then
    ----
    - the document is refused, a padding bit giving one value a second spelling.
    """
    ssz_json_test(
        case_id="json/bit_vector/invalid/padding_bit",
        type_name="JsonBitVector5",
        ssz_type=JsonBitVector5,
        document="0x35",
        rejection_reason=JsonFault.BITFIELD_PADDING,
        message_substring="the final byte 0x35 sets a padding bit",
    )


def test_a_collection_past_its_limit(ssz_json_test: JsonMappingFiller) -> None:
    """
    An array holding more elements than the list admits is refused.

    Given
    -----
    - five numbers, read against a list admitting four.

    When
    ----
    - a parser reads it through the JSON mapping.

    Then
    ----
    - the document is refused, a limit binding the JSON form as it binds the wire form.
    """
    ssz_json_test(
        case_id="json/list/invalid/over_limit",
        type_name="JsonUint16List4",
        ssz_type=JsonUint16List4,
        document=["1", "2", "3", "4", "5"],
        rejection_reason=JsonFault.OVER_LIMIT,
        message_substring="JsonUint16List4 holds at most 4 elements, got 5",
    )


def test_a_container_carrying_an_undeclared_field(ssz_json_test: JsonMappingFiller) -> None:
    """
    An object naming a field the struct does not declare is refused here.

    Given
    -----
    - the two declared fields, and a third named z.

    When
    ----
    - a parser reads it through the JSON mapping.

    Then
    ----
    - the document is refused, which the specification permits rather than requires.
    """
    ssz_json_test(
        case_id="json/container/invalid/undeclared_field",
        type_name="JsonPoint",
        ssz_type=JsonPoint,
        document={"x": "1", "y": "2", "z": "3"},
        rejection_reason=JsonFault.UNDECLARED_FIELD,
        message_substring="Extra inputs are not permitted",
    )
