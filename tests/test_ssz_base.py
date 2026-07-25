"""Tests for SSZModel and SSZType base class behavior."""

from typing import Any, cast

import pytest

from ssz import SSZLimitError, SSZTypeMismatch, Uint8, Uint16, Uint32, Uint64
from ssz.bitfields import BaseBitlist, BaseBitvector
from ssz.boolean import Boolean
from ssz.byte_arrays import BaseByteList
from ssz.collections import List, Vector
from ssz.container import Container
from ssz.merkleization import Root


class Uint16List4(List[Uint16]):
    """A list with up to 4 Uint16 values."""

    LIMIT = 4


class Uint16Vector2(Vector[Uint16]):
    """A vector of exactly 2 Uint16 values."""

    LENGTH = 2


class TypedUint16(Uint16):
    """A Uint16 subtype, as applications define semantic integer types."""


class TypedUint16List4(List[TypedUint16]):
    """A list with up to 4 TypedUint16 values."""

    LIMIT = 4


class RootList4(List[Root]):
    """A list with up to 4 Root values."""

    LIMIT = 4


class SmallBitvector(BaseBitvector):
    """A bitvector with exactly 3 bits."""

    LENGTH = 3


class SmallByteList(BaseByteList):
    """A byte list with up to 10 bytes."""

    LIMIT = 10


class TwoFieldContainer(Container):
    """A container with two fixed-size fields."""

    x: Uint8
    y: Uint16


class ThreeFieldContainer(Container):
    """A container with three fields, one variable-size."""

    a: Uint8
    b: Uint64
    c: Uint16List4


class SmallBitlist(BaseBitlist):
    """A bitlist with a small limit, used to test SSZModel.__len__ data path."""

    LIMIT = 8


class TestSSZModelLength:
    """
    Tests for SSZModel.__len__() on both collection and container models.

    Uses BaseBitlist (not List) for the data-path because List overrides
    __len__ with its own implementation. BaseBitlist inherits SSZModel's version.
    """

    def test_length_data_path_via_bitlist(self) -> None:
        """BaseBitlist delegates to SSZModel.__len__ which returns len(data)."""
        bl = SmallBitlist(data=(Boolean(True), Boolean(False), Boolean(True)))
        assert len(bl) == 3

    def test_length_empty_data_path_via_bitlist(self) -> None:
        bl = SmallBitlist(data=())
        assert len(bl) == 0

    def test_length_container_returns_field_count(self) -> None:
        container = TwoFieldContainer(x=Uint8(1), y=Uint16(2))
        assert len(container) == 2

    def test_length_three_field_container(self) -> None:
        container = ThreeFieldContainer(a=Uint8(5), b=Uint64(42), c=Uint16List4(data=[Uint16(1)]))
        assert len(container) == 3


class TestSSZModelRepr:
    """Tests for SSZModel.__repr__() on both collection and container models."""

    def test_repr_collection_shows_data(self) -> None:
        assert repr(Uint16List4(data=[Uint16(10), Uint16(20)])) == (
            "Uint16List4(data=[Uint16(10), Uint16(20)])"
        )

    def test_repr_empty_collection(self) -> None:
        assert repr(Uint16List4(data=[])) == "Uint16List4(data=[])"

    def test_repr_container_shows_fields(self) -> None:
        assert repr(TwoFieldContainer(x=Uint8(1), y=Uint16(2))) == (
            "TwoFieldContainer(x=Uint8(1) y=Uint16(2))"
        )

    def test_repr_three_field_container(self) -> None:
        container = ThreeFieldContainer(a=Uint8(5), b=Uint64(42), c=Uint16List4(data=[Uint16(1)]))
        assert repr(container) == (
            "ThreeFieldContainer(a=Uint8(5) b=Uint64(42) c=Uint16List4(data=[Uint16(1)]))"
        )


class TestSSZTypeEncodeDecode:
    """
    Tests for encode_bytes/decode_bytes on SSZType.

    These methods wrap the stream-based serialize/deserialize interface
    so callers can work with plain byte strings instead.
    """

    def test_encode_bytes_fixed_container(self) -> None:
        container = TwoFieldContainer(x=Uint8(1), y=Uint16(2))
        encoded = container.encode_bytes()
        assert encoded == b"\x01\x02\x00"

    def test_decode_bytes_fixed_container(self) -> None:
        assert TwoFieldContainer.decode_bytes(b"\x01\x02\x00") == TwoFieldContainer(
            x=Uint8(1), y=Uint16(2)
        )

    def test_encode_decode_roundtrip(self) -> None:
        """Encoding then decoding must recover the original object."""
        original = TwoFieldContainer(x=Uint8(255), y=Uint16(1000))
        assert TwoFieldContainer.decode_bytes(original.encode_bytes()) == original


class TestSSZCollectionOf:
    """
    Tests for the `of` factory classmethod.

    `of` is the positional construction form: each argument is exactly one
    element, and no argument is ever spread.
    """

    def test_of_builds_from_elements(self) -> None:
        """Each argument becomes one element."""
        assert Uint16List4.of(1, 2, 3) == Uint16List4(data=[Uint16(1), Uint16(2), Uint16(3)])

    def test_of_with_no_elements_builds_empty(self) -> None:
        """No arguments build an empty collection."""
        assert Uint16List4.of() == Uint16List4(data=[])

    def test_of_single_element_is_never_spread(self) -> None:
        """One argument is one element, never a whole data value."""
        assert Uint16List4.of(7) == Uint16List4(data=[Uint16(7)])

    def test_of_vector(self) -> None:
        """Vectors build from exactly LENGTH element arguments."""
        assert Uint16Vector2.of(1, 2) == Uint16Vector2(data=[Uint16(1), Uint16(2)])

    def test_of_bitvector(self) -> None:
        """Bitfields build from one bool argument per bit."""
        expected = SmallBitvector(data=[Boolean(True), Boolean(False), Boolean(True)])
        assert SmallBitvector.of(True, False, True) == expected

    def test_of_bitlist_accepts_splatted_bits(self) -> None:
        """An existing bit sequence splats into element arguments."""
        bits = [True, False]
        assert SmallBitlist.of(*bits) == SmallBitlist(data=[Boolean(True), Boolean(False)])

    def test_of_byte_list_elements_are_ints(self) -> None:
        """A byte list's elements are individual byte values."""
        assert SmallByteList.of(0xDE, 0xAD) == SmallByteList(data=b"\xde\xad")

    def test_of_rejects_bool_for_uint_elements(self) -> None:
        """A bool is not an integer element, even though bool subclasses int."""
        with pytest.raises(SSZTypeMismatch):
            Uint16List4.of(True)

    def test_of_rejects_other_uint_widths(self) -> None:
        """A uint of another width is a type error, regardless of its value."""
        with pytest.raises(SSZTypeMismatch):
            Uint16List4.of(Uint32(7))

    def test_of_accepts_a_parent_uint_class(self) -> None:
        """A value of the element type's parent class converts into the element type."""
        values = TypedUint16List4.of(Uint16(7))
        assert values == TypedUint16List4(data=[TypedUint16(7)])
        assert type(values.data[0]) is TypedUint16

    def test_of_rejects_a_child_uint_class(self) -> None:
        """A value of a child class of the element type is a type error."""
        with pytest.raises(SSZTypeMismatch):
            Uint16List4.of(TypedUint16(7))

    def test_of_beyond_limit_rejected(self) -> None:
        """More element arguments than the limit fail validation."""
        with pytest.raises(SSZLimitError):
            Uint16List4.of(1, 2, 3, 4, 5)

    def test_of_converts_plain_bytes_elements(self) -> None:
        """Plain bytes, such as bytes.fromhex output, convert into byte-array elements."""
        payload = bytes.fromhex("ab" * 32)
        values = RootList4.of(payload)
        assert values == RootList4(data=[Root(payload)])
        assert type(values.data[0]) is Root

    def test_of_rejects_hex_string_elements(self) -> None:
        """A hex string is not bytes; convert it with bytes.fromhex first."""
        with pytest.raises(SSZTypeMismatch) as exception_info:
            RootList4.of("ab" * 32)
        assert str(exception_info.value) == "Expected Root, got str"

    def test_of_wrong_length_bytes_keeps_coercion_detail(self) -> None:
        """An ancestor-class element that fails construction chains the inner detail."""
        with pytest.raises(SSZTypeMismatch) as exception_info:
            RootList4.of(b"\xab\xcd")
        expected = "Expected Root, got bytes: Root requires exactly 32 bytes, got 2"
        assert str(exception_info.value) == expected

    def test_of_returns_the_subclass_type(self) -> None:
        """The factory binds to the concrete subclass, not the base."""
        assert type(Uint16List4.of(1)) is Uint16List4

    def test_constructors_stay_keyword_only(self) -> None:
        """Positional constructor arguments stay rejected — `of` is the positional form."""
        with pytest.raises(TypeError):
            cast(Any, Uint16List4)([1, 2])
        with pytest.raises(TypeError):
            cast(Any, TwoFieldContainer)(Uint8(1), Uint16(2))
