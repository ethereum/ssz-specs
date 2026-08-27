"""Tests for the ByteVector and ByteList types."""

import copy
import hashlib
import io
import json
from typing import Any, cast

import pytest
from hypothesis import given, strategies as st
from pydantic import BaseModel

from ssz.byte_arrays import (
    ByteList,
    ByteVector,
)
from ssz.exceptions import SSZSerializationError, SSZTypeError, SSZValueError


class Bytes4(ByteVector):
    """A 4-byte array, as applications typically define for short identifiers."""

    LENGTH = 4


class Bytes32(ByteVector):
    """A 32-byte array, as applications typically define for roots and hashes."""

    LENGTH = 32


class Bytes32Sub(Bytes32):
    """A 32-byte array derived from another, the shape Root takes over Chunk."""


class Bytes32Sibling(ByteVector):
    """A second 32-byte array that shares only ByteVector with Bytes32."""

    LENGTH = 32


class ByteList5(ByteList):
    """A bytelist with limit 5 for testing."""

    LIMIT = 5


class ByteList16(ByteList):
    """A bytelist with limit 16 for testing."""

    LIMIT = 16


class ByteList16Sub(ByteList16):
    """A bytelist derived from another, inheriting its limit."""


class ModelVectors(BaseModel):
    """Pydantic model holding fixed-length byte arrays."""

    root: Bytes32
    key: Bytes4


class ModelLists(BaseModel):
    """Pydantic model holding a variable-length byte list."""

    payload: ByteList16


class TestBaseBytesConstruction:
    """Construction and coercion of fixed-length byte arrays."""

    def test_inheritance(self) -> None:
        """Concrete subclasses inherit from ByteVector and stay bytes-compatible."""
        assert issubclass(Bytes32, ByteVector)
        assert Bytes32.LENGTH == 32
        byte_array = Bytes32(b"\x00" * 32)
        assert isinstance(byte_array, Bytes32)
        assert isinstance(byte_array, bytes)
        assert len(byte_array) == 32

    @pytest.mark.parametrize(
        "input_value, expected_bytes",
        [
            (b"\x00\x01\x02\x03", b"\x00\x01\x02\x03"),
            (bytearray(b"\x00\x01\x02\x03"), b"\x00\x01\x02\x03"),
            ([0, 1, 2, 3], b"\x00\x01\x02\x03"),
            ((i for i in range(4)), b"\x00\x01\x02\x03"),
            ("00010203", b"\x00\x01\x02\x03"),
            ("0x00010203", b"\x00\x01\x02\x03"),
        ],
    )
    def test_coercion_from_supported_inputs(self, input_value: Any, expected_bytes: bytes) -> None:
        """Bytes, bytearray, iterables, generators, and hex strings all coerce to bytes."""
        coerced = Bytes4(input_value)
        assert bytes(coerced) == expected_bytes

    @pytest.mark.parametrize(
        "wrong_input, count",
        [
            (b"\x00\x01\x02", 3),
            ([0, 1, 2], 3),
            ("000102", 3),
        ],
    )
    def test_construction_with_wrong_length_raises(self, wrong_input: Any, count: int) -> None:
        """Inputs whose length doesn't match LENGTH raise with the exact element count."""
        with pytest.raises(SSZValueError) as exception_info:
            Bytes4(wrong_input)
        assert str(exception_info.value) == f"Bytes4 requires exactly 4 bytes, got {count}"

    @pytest.mark.parametrize("bad_input", [42, 1.5, None])
    def test_construction_with_non_coercible_input_raises(self, bad_input: Any) -> None:
        """Inputs outside the accepted union raise TypeError naming the offending type."""
        name = type(bad_input).__name__
        with pytest.raises(TypeError) as exception_info:
            Bytes4(bad_input)
        assert str(exception_info.value) == f"Cannot coerce {name} to bytes"

    def test_construction_without_length_attribute_raises(self) -> None:
        """Direct instantiation of the abstract base raises SSZTypeError."""
        with pytest.raises(SSZTypeError) as exception_info:
            ByteVector(b"")
        assert str(exception_info.value) == "ByteVector must define LENGTH"

    def test_zero_factory(self) -> None:
        """The zero classmethod returns an instance of LENGTH zero bytes."""
        zero_array = Bytes4.zero()
        assert isinstance(zero_array, Bytes4)
        assert bytes(zero_array) == b"\x00\x00\x00\x00"

    def test_trusted_wrapping_agrees_with_the_constructor(self) -> None:
        """A trusted wrap of a correct length is the same value the constructor builds."""
        payload = b"\x00\x01\x02\x03"
        assert Bytes4._trusted(payload) == Bytes4(payload)
        assert type(Bytes4._trusted(payload)) is Bytes4

    def test_trusted_wrapping_does_not_check_the_length(self) -> None:
        """A wrong width produces an instance rather than an error."""
        short = Bytes4._trusted(b"\x01")
        assert len(short) == 1
        with pytest.raises(SSZValueError):
            Bytes4(b"\x01")


class TestBaseBytesEquality:
    """Strict equality, inequality, and hashing of fixed-length byte arrays."""

    def test_same_type_equality(self) -> None:
        """Instances with the same value and type compare equal."""
        v1 = Bytes4(b"\x00\x01\x02\x03")
        v2 = Bytes4([0, 1, 2, 3])
        v3 = Bytes4("00010203")
        assert v1 == v2 == v3

    def test_same_type_inequality(self) -> None:
        """Instances with different values compare unequal."""
        v1 = Bytes4(b"\x00\x00\x00\x00")
        v2 = Bytes4(b"\x00\x00\x00\x01")
        assert v1 != v2

    @pytest.mark.parametrize("other", [b"\x00\x01\x02\x03", "string", 1.5, None, 42])
    def test_cross_type_equality_raises(self, other: Any) -> None:
        """Comparing with any non-ByteVector value raises TypeError."""
        name = type(other).__name__
        with pytest.raises(TypeError) as exception_info:
            _ = Bytes4(b"\x00\x01\x02\x03") == other
        assert (
            str(exception_info.value)
            == f"Unsupported operand type(s) for ==: 'Bytes4' and '{name}'"
        )

    @pytest.mark.parametrize("other", [b"\x00\x01\x02\x03", "string", 1.5, None, 42])
    def test_cross_type_inequality_raises(self, other: Any) -> None:
        """Inequality with any non-ByteVector value raises TypeError."""
        name = type(other).__name__
        with pytest.raises(TypeError) as exception_info:
            _ = Bytes4(b"\x00\x01\x02\x03") != other
        assert (
            str(exception_info.value)
            == f"Unsupported operand type(s) for !=: 'Bytes4' and '{name}'"
        )

    def test_hash_matches_the_raw_bytes(self) -> None:
        """The hash is the hash of the bytes, so a wrong type reaches the comparison."""
        byte_array = Bytes4(b"\x00\x01\x02\x03")
        assert hash(byte_array) == hash(b"\x00\x01\x02\x03")

    def test_a_raw_bytes_probe_of_a_set_raises_rather_than_missing(self) -> None:
        """Sharing a bucket with the raw bytes is what lets strict equality be reached."""
        with pytest.raises(TypeError) as exception_info:
            _ = b"\x00\x01\x02\x03" in {Bytes4(b"\x00\x01\x02\x03")}
        assert (
            str(exception_info.value) == "Unsupported operand type(s) for ==: 'Bytes4' and 'bytes'"
        )

    def test_a_raw_bytes_probe_of_a_different_value_is_simply_absent(self) -> None:
        """Different bytes hash apart, so the comparison is never reached and absent is right."""
        assert b"\x09\x09\x09\x09" not in {Bytes4(b"\x00\x01\x02\x03")}

    def test_hash_same_for_equal_instances(self) -> None:
        """Equal instances of the same type produce the same hash."""
        v1 = Bytes4(b"\x00\x01\x02\x03")
        v2 = Bytes4([0, 1, 2, 3])
        v3 = Bytes4("00010203")
        assert hash(v1) == hash(v2) == hash(v3)


class TestBaseBytesEqualityFollowsInheritance:
    """A byte-array type meets its own ancestors and descendants, and nothing else."""

    def test_a_subclass_and_its_base_compare_by_value(self) -> None:
        """Bytes32Sub derives from Bytes32, so one 32-byte string is one value under both."""
        payload = b"\x11" * 32
        assert Bytes32Sub(payload) == Bytes32(payload)
        assert Bytes32(payload) == Bytes32Sub(payload)
        assert not (Bytes32Sub(payload) != Bytes32(payload))

    def test_a_subclass_and_its_base_hash_alike(self) -> None:
        """The pair above compares equal, so Python requires one hash for both."""
        payload = b"\x11" * 32
        assert hash(Bytes32Sub(payload)) == hash(Bytes32(payload))
        assert len({Bytes32Sub(payload), Bytes32(payload)}) == 1
        assert {Bytes32(payload): "value"}[Bytes32Sub(payload)] == "value"

    def test_a_subclass_and_its_base_still_differ_by_value(self) -> None:
        """The relation admits the comparison; it does not make every pair equal."""
        assert Bytes32Sub(b"\x11" * 32) != Bytes32(b"\x22" * 32)

    def test_two_sibling_types_are_refused(self) -> None:
        """Neither sibling derives from the other, so the comparison has no answer to give."""
        payload = b"\x11" * 32
        with pytest.raises(TypeError) as exception_info:
            _ = Bytes32(payload) == Bytes32Sibling(payload)
        assert (
            str(exception_info.value)
            == "Unsupported operand type(s) for ==: 'Bytes32' and 'Bytes32Sibling'"
        )

    def test_two_sibling_types_are_refused_by_inequality_too(self) -> None:
        """Both operators apply the one relation."""
        payload = b"\x11" * 32
        with pytest.raises(TypeError) as exception_info:
            _ = Bytes32(payload) != Bytes32Sibling(payload)
        assert (
            str(exception_info.value)
            == "Unsupported operand type(s) for !=: 'Bytes32' and 'Bytes32Sibling'"
        )

    def test_a_sibling_probe_of_a_dict_raises_rather_than_missing_silently(self) -> None:
        """The reported bug: a dict keyed by one type used to answer absent for the other."""
        payload = b"\x11" * 32
        with pytest.raises(TypeError):
            _ = {Bytes32(payload): 1}[Bytes32Sibling(payload)]

    def test_equality_and_hashing_never_disagree(self) -> None:
        """Over every pair of the three 32-byte types at two payloads, equal implies one hash."""
        values = [
            constructor(payload)
            for payload in (b"\x11" * 32, b"\x22" * 32)
            for constructor in (Bytes32, Bytes32Sub, Bytes32Sibling)
        ]
        compared = 0
        for left in values:
            for right in values:
                try:
                    equal = left == right
                except TypeError:
                    continue
                compared += 1
                # The implication Python requires runs one way only, so an unequal pair
                # is free to share a hash. Here the payload alone decides both sides.
                assert equal is (hash(left) == hash(right))
        # Guard against the loop passing because every pair raised.
        assert compared == 20


class TestBaseBytesOperations:
    """Repr, hex, iteration, indexing, ordering, and concatenation."""

    def test_repr(self) -> None:
        """The repr is the class name with the hex content in parentheses."""
        assert repr(Bytes4(b"\x00\x01\x02\x03")) == "Bytes4(00010203)"

    def test_hex(self) -> None:
        """The hex method returns the lowercase hex string."""
        assert Bytes4(b"\x00\x01\x02\x03").hex() == "00010203"

    def test_length_iter_getitem(self) -> None:
        """The instance supports len, iteration, and integer indexing."""
        byte_array = Bytes4(b"\x00\x01\x02\x03")
        assert len(byte_array) == 4
        assert list(iter(byte_array)) == [0, 1, 2, 3]
        assert byte_array[2] == 2

    def test_reads_return_plain_types_and_offer_no_writer(self) -> None:
        """A fixed byte array reads exactly as plain bytes do, offering no way to write."""
        byte_array = Bytes4(b"\x01\x02\x03\x04")

        # One position gives a plain integer.
        # A trailing range gives plain bytes.
        # Neither is wrapped back into a byte-array type, because a 2-byte result would no
        # longer satisfy the 4-byte count the type declares.
        assert byte_array[-1] == 4
        assert type(byte_array[-1]) is int
        assert byte_array[-2:] == b"\x03\x04"
        assert type(byte_array[-2:]) is bytes

        # The variable-length shape reads back those same plain types.
        # It differs in accepting writes, which a fixed count leaves no room for.
        assert ByteList16(data=b"\x01\x02\x03\x04")[-2:] == b"\x03\x04"
        assert not hasattr(Bytes4, "__setitem__")
        assert hasattr(ByteList16, "__setitem__")

    def test_concatenation_returns_plain_bytes(self) -> None:
        """Concatenation of two instances returns plain bytes."""
        left_array = Bytes4(b"\x00\x00\x00\x01")
        right_array = Bytes4(b"\x00\x00\x00\x02")
        concatenated = left_array + right_array
        assert type(concatenated) is bytes
        assert concatenated == b"\x00\x00\x00\x01\x00\x00\x00\x02"

    def test_reverse_concatenation_returns_plain_bytes(self) -> None:
        """Concatenation with raw bytes on the left returns plain bytes."""
        byte_array = Bytes4(b"\x00\x00\x00\x01")
        concatenated = b"\xff" + byte_array
        assert type(concatenated) is bytes
        assert concatenated == b"\xff\x00\x00\x00\x01"

    def test_sort_lexicographic(self) -> None:
        """Instances sort lexicographically by byte content."""
        smallest = Bytes32(b"\x00" * 31 + b"\x01")
        middle = Bytes32(b"\x00" * 31 + b"\x02")
        largest = Bytes32(b"\xff" * 32)
        assert sorted([largest, middle, smallest]) == [smallest, middle, largest]

    def test_hashlib_compatibility(self) -> None:
        """An instance is usable wherever a bytes-like value is expected."""
        byte_array = Bytes32(b"\x01" + b"\x00" * 31)
        digest = hashlib.sha256(byte_array).digest()
        assert len(digest) == 32


class TestAByteArrayCarriesNoState:
    """A copy of an immutable shape is the shape itself, so it accepts no attributes."""

    def test_attaching_state_to_a_byte_array_is_refused(self) -> None:
        """Setting an attribute would reach every other name for the same value."""
        expected_message = "Bytes32 is immutable"
        with pytest.raises(SSZTypeError) as exception_info:
            Bytes32(b"\x01" * 32).note = "mine"  # type: ignore[attr-defined]
        assert str(exception_info.value) == expected_message

    def test_a_subclass_is_refused_under_its_own_name(self) -> None:
        """The refusal names the type the value was built as, not the one declaring it."""
        with pytest.raises(SSZTypeError, match=r"^Bytes32Sub is immutable$"):
            Bytes32Sub(b"\x01" * 32).note = "mine"  # type: ignore[attr-defined]

    def test_a_deep_copy_cannot_be_written_through_to_the_original(self) -> None:
        """The duplicate promised by copy is this same object, and it stays unwritable."""
        original = Bytes32(b"\x01" * 32)
        duplicate = copy.deepcopy(original)
        # The premise: an immutable shape answers a copy with itself.
        assert duplicate is original
        with pytest.raises(SSZTypeError, match=r"^Bytes32 is immutable$"):
            duplicate.note = "mine"  # type: ignore[attr-defined]


class TestBaseBytesSSZ:
    """SSZ interface methods and serialization round-trip."""

    def test_is_fixed_size(self) -> None:
        """ByteVector subclasses are always fixed-size."""
        assert Bytes32.is_fixed_size() is True

    def test_get_byte_length(self) -> None:
        """get_byte_length returns the declared LENGTH."""
        assert Bytes32.get_byte_length() == 32
        assert Bytes4.get_byte_length() == 4

    @pytest.mark.parametrize(
        "cls, payload",
        [
            (Bytes4, b"\x00\x01\x02\x03"),
            (Bytes32, b"\x11" * 32),
        ],
    )
    def test_encode_decode_roundtrip(self, cls: type[ByteVector], payload: bytes) -> None:
        """ByteVector round-trips through encode_bytes, decode_bytes, and stream serialization."""
        byte_array = cls(payload)
        assert byte_array.encode_bytes() == payload
        assert cls.decode_bytes(payload) == byte_array

        buffer = io.BytesIO()
        bytes_written = byte_array.serialize(buffer)
        assert bytes_written == len(payload)

        buffer.seek(0)
        deserialized = cls.deserialize(buffer, len(payload))
        assert byte_array == deserialized

    def test_deserialize_scope_mismatch_raises(self) -> None:
        """deserialize rejects a scope that doesn't match LENGTH."""
        buffer = io.BytesIO(b"\x00\x01\x02\x03")
        with pytest.raises(SSZSerializationError) as exception_info:
            Bytes4.deserialize(buffer, 3)
        assert str(exception_info.value) == "Bytes4: expected 4 bytes, got 3"

    def test_deserialize_stream_truncation_raises(self) -> None:
        """deserialize detects when the stream ends before delivering scope bytes."""
        buffer = io.BytesIO(b"\x00\x01")
        with pytest.raises(SSZSerializationError) as exception_info:
            Bytes4.deserialize(buffer, 4)
        assert str(exception_info.value) == "Bytes4: expected 4 bytes, got 2"


class TestBaseBytesPydantic:
    """Pydantic validation and JSON serialization for fixed-length byte arrays."""

    def test_accepts_typed_instances_and_supported_inputs(self) -> None:
        """Pydantic accepts existing instances built from hex strings or iterables."""
        model = ModelVectors(
            root=Bytes32("0x" + "11" * 32),
            key=Bytes4([0, 1, 2, 3]),
        )
        assert isinstance(model.root, Bytes32)
        assert isinstance(model.key, Bytes4)
        assert bytes(model.root) == b"\x11" * 32
        assert bytes(model.key) == b"\x00\x01\x02\x03"

    def test_json_serialization_to_hex(self) -> None:
        """Serialization uses 0x-prefixed lowercase hex for JSON output."""
        model = ModelVectors(
            root=Bytes32("0x" + "11" * 32),
            key=Bytes4([0, 1, 2, 3]),
        )
        dumped = model.model_dump()
        assert dumped["root"] == "0x" + "11" * 32
        assert dumped["key"] == "0x00010203"


class TestBaseByteListConstruction:
    """Construction and coercion of variable-length byte lists."""

    def test_inheritance(self) -> None:
        """Concrete subclasses carry the declared limit."""
        byte_list = ByteList16(data=b"\x01\x02")
        assert isinstance(byte_list, ByteList16)
        assert ByteList16.LIMIT == 16
        assert len(byte_list.data) == 2

    @pytest.mark.parametrize(
        "input_value, expected_bytes",
        [
            (b"\x00\x01\x02\x03\x04", b"\x00\x01\x02\x03\x04"),
            (bytearray(b"\x00\x01\x02\x03\x04"), b"\x00\x01\x02\x03\x04"),
            ([0, 1, 2, 3, 4], b"\x00\x01\x02\x03\x04"),
            ("0001020304", b"\x00\x01\x02\x03\x04"),
            ("0x0001020304", b"\x00\x01\x02\x03\x04"),
        ],
    )
    def test_coercion_from_supported_inputs(self, input_value: Any, expected_bytes: bytes) -> None:
        """Bytes, bytearray, iterables, and hex strings all coerce to bytes."""
        byte_list = ByteList5(data=input_value)
        assert byte_list.data == expected_bytes
        assert len(byte_list.data) == len(expected_bytes)

    def test_construction_over_limit_raises(self) -> None:
        """Input exceeding LIMIT raises with the exact size in the message."""
        with pytest.raises(SSZValueError) as exception_info:
            ByteList5(data=b"\x00" * 6)
        assert str(exception_info.value) == "ByteList5 exceeds limit of 5, got 6"

    def test_construction_without_limit_attribute_raises(self) -> None:
        """Direct instantiation of the abstract base raises SSZTypeError."""
        with pytest.raises(SSZTypeError) as exception_info:
            ByteList(data=b"")
        assert str(exception_info.value) == "ByteList must define LIMIT"


class TestBaseByteListEquality:
    """Strict equality, inequality, and hashing of variable-length byte lists."""

    def test_same_type_equality(self) -> None:
        """Instances with the same value compare equal."""
        v1 = ByteList16(data=b"\x00\x01\x02")
        v2 = ByteList16(data=b"\x00\x01\x02")
        assert v1 == v2

    def test_same_type_inequality(self) -> None:
        """Instances with different values compare unequal."""
        v1 = ByteList16(data=b"\x00")
        v2 = ByteList16(data=b"\x01")
        assert v1 != v2

    @pytest.mark.parametrize("other", [b"\x00\x01\x02", "string", 1.5, None, 42])
    def test_cross_type_equality_raises(self, other: Any) -> None:
        """Comparing with any non-ByteList value raises TypeError."""
        name = type(other).__name__
        with pytest.raises(TypeError) as exception_info:
            _ = ByteList16(data=b"\x00\x01\x02") == other
        assert (
            str(exception_info.value)
            == f"Unsupported operand type(s) for ==: 'ByteList16' and '{name}'"
        )

    @pytest.mark.parametrize("other", [b"\x00\x01\x02", "string", 1.5, None, 42])
    def test_cross_type_inequality_raises(self, other: Any) -> None:
        """Inequality with any non-ByteList value raises TypeError."""
        name = type(other).__name__
        with pytest.raises(TypeError) as exception_info:
            _ = ByteList16(data=b"\x00\x01\x02") != other
        assert (
            str(exception_info.value)
            == f"Unsupported operand type(s) for !=: 'ByteList16' and '{name}'"
        )

    def test_two_unrelated_limits_are_refused(self) -> None:
        """A payload under a limit of 5 is not the same value as one under a limit of 16."""
        with pytest.raises(TypeError) as exception_info:
            _ = ByteList5(data=b"\x00\x01") == ByteList16(data=b"\x00\x01")
        assert (
            str(exception_info.value)
            == "Unsupported operand type(s) for ==: 'ByteList5' and 'ByteList16'"
        )

    def test_two_unrelated_limits_are_refused_by_inequality_too(self) -> None:
        """Both operators apply the one relation."""
        with pytest.raises(TypeError) as exception_info:
            _ = ByteList5(data=b"\x00\x01") != ByteList16(data=b"\x00\x01")
        assert (
            str(exception_info.value)
            == "Unsupported operand type(s) for !=: 'ByteList5' and 'ByteList16'"
        )

    def test_a_subclass_and_its_base_compare_and_hash_alike(self) -> None:
        """Inheritance relates the two types, so one payload is one value under both names."""
        payload = b"\x00\x01"
        assert ByteList16Sub(data=payload) == ByteList16(data=payload)
        assert ByteList16(data=payload) == ByteList16Sub(data=payload)
        assert hash(ByteList16Sub(data=payload)) == hash(ByteList16(data=payload))
        assert not (ByteList16Sub(data=payload) != ByteList16(data=payload))

    def test_a_subclass_and_its_base_still_differ_by_value(self) -> None:
        """The relation admits the comparison; it does not make every pair equal."""
        assert ByteList16Sub(data=b"\x00") != ByteList16(data=b"\x01")

    def test_hash_is_the_hash_of_the_payload(self) -> None:
        """Equality compares the payload alone, so the hash is the payload's hash alone."""
        assert hash(ByteList16(data=b"\x00\x01\x02")) == hash(b"\x00\x01\x02")

    def test_hash_same_for_equal_instances(self) -> None:
        """Equal instances of the same type produce the same hash."""
        v1 = ByteList16(data=b"\x00\x01\x02")
        v2 = ByteList16(data=b"\x00\x01\x02")
        assert hash(v1) == hash(v2)


class TestBaseByteListOperations:
    """Repr, hex, bytes coercion, and concatenation."""

    def test_repr(self) -> None:
        """The repr is the class name with the hex content in parentheses."""
        assert repr(ByteList16(data=b"\x00\x01\x02")) == "ByteList16(000102)"

    def test_hex(self) -> None:
        """The hex method returns the lowercase hex string."""
        assert ByteList16(data=b"\x00\x01\x02").hex() == "000102"

    def test_bytes_dunder(self) -> None:
        """Calling bytes() on an instance returns the underlying bytes."""
        assert bytes(ByteList16(data=b"\x00\x01\x02")) == b"\x00\x01\x02"

    def test_reads_by_position_from_either_end(self) -> None:
        """A byte list answers integer byte values by position, counted from either end."""
        byte_list = ByteList16(data=b"\xde\xad\xbe")

        #     position from the start:    0     1     2
        #     bytes:                    0xde  0xad  0xbe
        #     position from the end:     -3    -2    -1
        assert byte_list[0] == 0xDE
        assert byte_list[-1] == 0xBE

        # A trailing range answers as raw bytes, which is how the payload is stored.
        assert byte_list[-2:] == b"\xad\xbe"

        # Answering by position and by length is all the host language needs to walk a
        # sequence backwards.
        # A byte list is therefore reversible without declaring anything further.
        assert list(reversed(byte_list)) == [0xBE, 0xAD, 0xDE]

    def test_concatenation_returns_plain_bytes(self) -> None:
        """Concatenation with a bytes-like value returns plain bytes."""
        byte_list = ByteList16(data=b"\x00\x01\x02")
        concatenated = byte_list + b"\x03\x04"
        assert type(concatenated) is bytes
        assert concatenated == b"\x00\x01\x02\x03\x04"

    def test_reverse_concatenation_returns_plain_bytes(self) -> None:
        """Concatenation with raw bytes on the left returns plain bytes."""
        byte_list = ByteList16(data=b"\x00\x01")
        concatenated = b"\xff" + byte_list
        assert type(concatenated) is bytes
        assert concatenated == b"\xff\x00\x01"


class TestBaseByteListMutation:
    """
    Mutation of a byte list, and what the stored payload looks like afterwards.

    The store checks the byte count and nothing else, so each case shows that skipping
    the coercion skips no check.
    """

    def test_the_stored_payload_is_still_plain_bytes(self) -> None:
        """A mutated payload is bytes, not the mutable buffer the mutation worked on."""
        payload = ByteList16(data=b"\xde")
        payload.append(0xAD)

        # A stored bytearray would be a payload that could change under a value that
        # already reported its root.
        assert type(payload.data) is bytes
        assert payload.data == b"\xde\xad"

    def test_mutating_the_default_marks_the_field_as_set(self) -> None:
        """A mutated value is indistinguishable from one that was assigned to."""
        payload = ByteList16()
        assert payload.model_fields_set == set()

        payload.append(0xDE)

        # The store writes the field entry itself rather than assigning to the attribute.
        # A field left unmarked would drop out of a dump that asks only for what was set.
        assert payload.model_fields_set == {"data"}
        assert payload.model_dump(exclude_unset=True) == {"data": b"\xde"}

    def test_appending_past_the_capacity_is_refused(self) -> None:
        """The capacity is the one check a mutation can break, so it is still made."""
        payload = ByteList5(data=b"\x01\x02\x03\x04\x05")
        with pytest.raises(SSZValueError) as exception_info:
            payload.append(0x06)

        # The same message the field validator raises for the same byte count.
        assert str(exception_info.value) == "ByteList5 exceeds limit of 5, got 6"
        assert payload.data == b"\x01\x02\x03\x04\x05"

    def test_a_slice_write_past_the_capacity_is_refused(self) -> None:
        """A slice can grow a payload by more than one byte, and is bounded the same way."""
        payload = ByteList5(data=b"\x01\x02")
        with pytest.raises(SSZValueError) as exception_info:
            payload[0:1] = b"\xaa\xbb\xcc\xdd\xee"
        assert str(exception_info.value) == "ByteList5 exceeds limit of 5, got 6"
        assert payload.data == b"\x01\x02"

    @pytest.mark.parametrize(
        "mutate, expected_error, message",
        [
            pytest.param(
                lambda payload: payload.append(256),
                ValueError,
                "byte must be in range(0, 256)",
                id="append_past_a_byte",
            ),
            pytest.param(
                lambda payload: payload.__setitem__(0, -1),
                ValueError,
                "byte must be in range(0, 256)",
                id="assign_below_a_byte",
            ),
            pytest.param(
                lambda payload: payload.append("x"),
                TypeError,
                "'str' object cannot be interpreted as an integer",
                id="append_something_that_is_not_a_byte",
            ),
            # The declaration refuses both pairings, so the cast is what reaches the buffer.
            pytest.param(
                lambda payload: payload.__setitem__(0, cast("Any", [1, 2])),
                TypeError,
                "'list' object cannot be interpreted as an integer",
                id="assign_a_sequence_to_one_position",
            ),
            pytest.param(
                lambda payload: payload.__setitem__(slice(0, 2), cast("Any", 5)),
                TypeError,
                "can assign only bytes, buffers, or iterables of ints in range(0, 256)",
                id="assign_one_byte_over_a_range",
            ),
        ],
    )
    def test_a_value_that_is_not_a_byte_is_refused_by_the_buffer(
        self, mutate: Any, expected_error: type[Exception], message: str
    ) -> None:
        """The mutable buffer refuses a value outside a byte, before anything is stored."""
        payload = ByteList16(data=b"\xde\xad")
        with pytest.raises(expected_error) as exception_info:
            mutate(payload)
        assert str(exception_info.value) == message
        assert payload.data == b"\xde\xad"

    def test_an_input_no_coercion_accepts_is_refused(self) -> None:
        """The coercion the validator carries out refuses what no branch of it accepts."""
        with pytest.raises(TypeError) as exception_info:
            ByteList5(data=cast("Any", 42))
        assert str(exception_info.value) == "Cannot coerce int to bytes"

    def test_popping_the_last_byte_of_an_empty_payload_is_refused(self) -> None:
        """An empty payload has no last byte, so the buffer refuses."""
        payload = ByteList16()
        with pytest.raises(IndexError):
            payload.pop()
        assert payload.data == b""

    def test_a_mutated_payload_roots_as_the_same_payload_constructed(self) -> None:
        """Mutation reaches the same value construction does, so it reaches the same root."""
        mutated = ByteList16(data=b"\xde\xad")
        mutated.append(0xBE)
        mutated[0] = 0xFF
        assert mutated.pop() == 0xBE

        constructed = ByteList16(data=b"\xff\xad")
        assert mutated == constructed
        assert mutated.hash_tree_root() == constructed.hash_tree_root()
        assert mutated.encode_bytes() == constructed.encode_bytes()

    def test_the_payload_still_validates_when_assigned_to(self) -> None:
        """Assigning the field is untouched: it coerces and bounds the input as before."""
        payload = ByteList5()

        # A bytearray is one of the inputs the validator coerces, so it still does.
        payload.data = cast("Any", bytearray(b"\x01\x02"))
        assert type(payload.data) is bytes

        with pytest.raises(SSZValueError) as exception_info:
            payload.data = b"\x01\x02\x03\x04\x05\x06"
        assert str(exception_info.value) == "ByteList5 exceeds limit of 5, got 6"


class TestBaseByteListSSZ:
    """SSZ interface methods and serialization round-trip."""

    def test_is_fixed_size(self) -> None:
        """ByteList subclasses are always variable-size."""
        assert ByteList16.is_fixed_size() is False

    def test_get_byte_length_raises(self) -> None:
        """get_byte_length raises a descriptive error for variable-size types."""
        with pytest.raises(SSZTypeError) as exception_info:
            ByteList16.get_byte_length()
        assert (
            str(exception_info.value)
            == "ByteList16: variable-size byte list has no fixed byte length"
        )

    @pytest.mark.parametrize(
        "limit, data",
        [
            (0, b""),
            (1, b"\xaa"),
            (5, b"\x00\x01\x02\x03\x04"),
            (16, bytes(range(16))),
        ],
    )
    def test_encode_decode_roundtrip(self, limit: int, data: bytes) -> None:
        """ByteList round-trips through encode_bytes, decode_bytes, and stream serialization."""

        class TestByteList(ByteList):
            LIMIT = limit

        byte_list = TestByteList(data=data)
        assert byte_list.encode_bytes() == data
        assert TestByteList.decode_bytes(data) == byte_list

        buffer = io.BytesIO()
        bytes_written = byte_list.serialize(buffer)
        assert bytes_written == len(data)

        buffer.seek(0)
        deserialized = TestByteList.deserialize(buffer, len(data))
        assert deserialized == byte_list

    def test_deserialize_negative_scope_raises(self) -> None:
        """deserialize rejects a negative scope."""
        buffer = io.BytesIO(b"")
        with pytest.raises(SSZSerializationError) as exception_info:
            ByteList16.deserialize(buffer, -1)
        assert str(exception_info.value) == "ByteList16: negative scope"

    def test_deserialize_over_limit_raises(self) -> None:
        """deserialize rejects a scope exceeding LIMIT."""
        buffer = io.BytesIO(b"\x00" * 6)
        with pytest.raises(SSZValueError) as exception_info:
            ByteList5.deserialize(buffer, 6)
        assert str(exception_info.value) == "ByteList5 exceeds limit of 5, got 6"

    def test_deserialize_stream_truncation_raises(self) -> None:
        """deserialize detects when the stream ends before delivering scope bytes."""
        buffer = io.BytesIO(b"\x00\x01")
        with pytest.raises(SSZSerializationError) as exception_info:
            ByteList16.deserialize(buffer, 3)
        assert str(exception_info.value) == "ByteList16: expected 3 bytes, got 2"


class TestBaseByteListPydantic:
    """Pydantic validation and JSON serialization for variable-length byte lists."""

    def test_accepts_valid_input(self) -> None:
        """Pydantic accepts construction with bytes within LIMIT."""
        raw_bytes = bytes.fromhex("000102030405060708090a0b0c0d0e0f")
        model = ModelLists(payload=ByteList16(data=raw_bytes))
        assert isinstance(model.payload, ByteList16)
        assert model.payload.encode_bytes() == raw_bytes

    def test_rejects_oversized_input(self) -> None:
        """Pydantic rejects data exceeding LIMIT via SSZValueError."""
        with pytest.raises(SSZValueError):
            ModelLists(payload=ByteList16(data=bytes(range(17))))

    def test_json_serialization_to_hex(self) -> None:
        """JSON-mode serialization renders the data field as a 0x-prefixed hex string."""
        raw_bytes = bytes.fromhex("0001020304")
        model = ModelLists(payload=ByteList16(data=raw_bytes))
        dumped = model.model_dump(mode="json")
        assert dumped["payload"]["data"] == "0x0001020304"


class TestBaseBytesDefault:
    """The default value of a fixed-length byte array, and the zeroed check over it."""

    def test_construction_without_an_argument_is_zeroed(self) -> None:
        """The spec gives a fixed byte array the default of LENGTH zero bytes."""
        assert bytes(Bytes4()) == b"\x00\x00\x00\x00"
        assert Bytes4() == Bytes4.zero()

    def test_an_explicitly_missing_value_is_still_rejected(self) -> None:
        """Only an omitted argument asks for the default, never a missing value passed as one."""
        # Passing a missing value through by mistake is the case this catches: an optional
        # that arrived empty must fail loudly rather than read as four zero bytes.
        #
        # A static checker rejects the call as well, which is the same property one step
        # earlier, so the suppression here is what lets the runtime half be pinned.
        with pytest.raises(TypeError) as exception_info:
            Bytes4(None)  # ty: ignore[invalid-argument-type]
        assert str(exception_info.value) == "Cannot coerce NoneType to bytes"

    def test_an_explicitly_empty_input_stays_a_length_error(self) -> None:
        """Zero bytes is a count mismatch against LENGTH, never a request for the default."""
        with pytest.raises(SSZValueError) as exception_info:
            Bytes4(b"")
        assert str(exception_info.value) == "Bytes4 requires exactly 4 bytes, got 0"

    def test_a_shape_without_a_length_reports_its_own_declaration_error(self) -> None:
        """No length means no byte count to zero, so the declaration error comes first."""
        with pytest.raises(SSZTypeError) as exception_info:
            ByteVector()
        assert str(exception_info.value) == "ByteVector must define LENGTH"

    def test_the_default_is_zeroed_and_any_set_byte_is_not(self) -> None:
        """The zero-filled array equals a fresh default of its type; a set byte does not."""
        assert Bytes4().is_zero() is True
        assert Bytes4(b"\x00\x00\x00\x01").is_zero() is False

    def test_the_default_round_trips(self) -> None:
        """The default encodes to four zero bytes and decodes back unchanged."""
        assert Bytes4().encode_bytes() == b"\x00" * 4
        assert Bytes4.decode_bytes(Bytes4().encode_bytes()) == Bytes4()


class TestBaseByteListDefault:
    """The default value of a variable-length byte list, which is the empty payload."""

    def test_construction_without_an_argument_is_empty(self) -> None:
        """A variable-size shape defaults to its empty value, so it holds no byte at all."""
        assert ByteList5() == ByteList5(data=b"")
        assert len(ByteList5()) == 0

    def test_the_default_is_zeroed_and_a_single_zero_byte_is_not(self) -> None:
        """The empty payload is the default; one zero byte is a different value of length 1."""
        assert ByteList5().is_zero() is True
        assert ByteList5(data=b"\x00").is_zero() is False

    def test_the_default_round_trips(self) -> None:
        """The default encodes to no bytes at all and decodes back unchanged."""
        assert ByteList5().encode_bytes() == b""
        assert ByteList5.decode_bytes(b"") == ByteList5()


def test_zero_default_value() -> None:
    """The zero factory produces a zero-filled byte array."""
    assert bytes(Bytes32.zero()) == b"\x00" * 32


def test_json_dumpable_via_hex() -> None:
    """Byte instances are JSON-dumpable when pre-encoded to hex strings."""
    hex_encoded_fields = {
        "root": Bytes32(b"\x11" * 32).hex(),
        "key": Bytes4(b"\x00\x01\x02\x03").hex(),
        "payload": ByteList5(data=b"\x00\x01\x02").hex(),
    }
    assert json.loads(json.dumps(hex_encoded_fields)) == hex_encoded_fields


@given(raw_bytes=st.binary(min_size=32, max_size=32))
def test_byte_vector_round_trip_random_bytes(raw_bytes: bytes) -> None:
    """Any fixed-length byte pattern survives an encode and decode round trip."""
    instance = Bytes32(raw_bytes)
    assert Bytes32.decode_bytes(instance.encode_bytes()) == instance


@given(raw_bytes=st.binary(max_size=16))
def test_byte_list_round_trip_random_bytes(raw_bytes: bytes) -> None:
    """Any byte pattern up to the limit, including empty, round-trips unchanged."""
    instance = ByteList16(data=raw_bytes)
    assert ByteList16.decode_bytes(instance.encode_bytes()) == instance
