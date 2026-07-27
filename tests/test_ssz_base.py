"""Tests for SSZModel and SSZType base class behavior."""

from typing import Any, cast

import pytest
from pydantic import ValidationError

from ssz import SSZLimitError, SSZTypeMismatch, Uint8, Uint16, Uint32, Uint64
from ssz.bitfields import BaseBitlist, BaseBitvector, ProgressiveBitlist
from ssz.boolean import Boolean
from ssz.byte_arrays import BaseByteList
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container, ProgressiveContainer
from ssz.exceptions import SSZDefaultError, SSZError, SSZTypeError, SSZValueError
from ssz.merkleization import Root
from ssz.ssz_base import SSZCollection, SSZType
from ssz.union import CompatibleUnion


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


class ByteList4(BaseByteList):
    """A byte list with up to 4 bytes, narrow enough that a 3-byte payload is one short."""

    LIMIT = 4


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


class Uint16ProgressiveList(ProgressiveList[Uint16]):
    """A progressive list of Uint16 values, the unbounded sequence shape."""


class SmallUnion(CompatibleUnion):
    """A union over one option, the only shape the spec gives no default value."""

    OPTIONS = {1: Uint8}


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


class TestSSZCollectionIteration:
    """
    Tests that every collection family iterates its contents.

    The shared base defines the iteration, because the parent Pydantic model
    would otherwise yield name/value pairs of its fields. The sequence family
    covers the same behavior through its own accessor tests; the families
    whose element type is fixed are covered here.
    """

    def test_bitvector_yields_its_bits(self) -> None:
        """A bitvector iterates booleans, not the one field that holds them."""
        bits = SmallBitvector(data=[Boolean(True), Boolean(False), Boolean(True)])
        assert list(bits) == [Boolean(True), Boolean(False), Boolean(True)]

    def test_bitlist_yields_its_bits(self) -> None:
        """A bounded bitlist iterates booleans."""
        bits = SmallBitlist(data=[Boolean(True), Boolean(False)])
        assert list(bits) == [Boolean(True), Boolean(False)]

    def test_progressive_bitlist_yields_its_bits(self) -> None:
        """A progressive bitlist iterates booleans on the same terms."""
        bits = ProgressiveBitlist(data=[Boolean(False), Boolean(True)])
        assert list(bits) == [Boolean(False), Boolean(True)]

    def test_byte_list_yields_its_byte_values(self) -> None:
        """A byte list iterates integer byte values, matching what its API mutates by."""
        payload = SmallByteList(data=b"\xde\xad")
        assert list(payload) == [0xDE, 0xAD]

    def test_membership_reads_the_contents(self) -> None:
        """The in operator routes through iteration, so it tests contents, not field names."""
        assert Boolean(True) in SmallBitlist(data=[Boolean(True)])
        assert Boolean(True) not in SmallBitlist(data=[Boolean(False)])
        assert 0xDE in SmallByteList(data=b"\xde\xad")
        assert "data" not in SmallByteList(data=b"\xde\xad")


class TestSSZCollectionMutation:
    """
    Tests for in-place collection mutation.

    Collections mutate in place: element assignment, append, and pop
    validate the incoming elements and the resulting length by the same
    rules construction applies. Existing elements were validated when
    they entered, so mutation cost is proportional to the change rather than
    the collection size.
    """

    def test_setitem_replaces_and_coerces(self) -> None:
        """Integer index assignment coerces the value into the element type."""
        values = Uint16List4(data=[Uint16(1), Uint16(2)])
        values[1] = 9  # ty: ignore[invalid-assignment]
        assert values == Uint16List4(data=[Uint16(1), Uint16(9)])

    def test_setitem_slice_revalidates(self) -> None:
        """Slice assignment replaces a range of elements."""
        bits = SmallBitvector(data=[Boolean(True), Boolean(True), Boolean(True)])
        bits[1:] = [Boolean(False), Boolean(False)]
        assert bits == SmallBitvector(data=[Boolean(True), Boolean(False), Boolean(False)])

    def test_append_grows_within_limit(self) -> None:
        """Append adds one element while under the limit."""
        values = Uint16List4(data=[Uint16(1)])
        values.append(Uint16(2))
        assert values == Uint16List4(data=[Uint16(1), Uint16(2)])

    def test_append_beyond_limit_rejected(self) -> None:
        """Append past the limit fails revalidation and raises."""
        values = Uint16List4(data=[Uint16(1)] * 4)
        with pytest.raises((SSZValueError, ValidationError)):
            values.append(Uint16(5))

    def test_fixed_length_shapes_lack_append_and_pop(self) -> None:
        """Fixed-length shapes do not offer length-changing methods at all."""
        assert not hasattr(Uint16Vector2, "append")
        assert not hasattr(Uint16Vector2, "pop")
        assert not hasattr(SmallBitvector, "append")
        assert not hasattr(SmallBitvector, "pop")

    def test_setitem_slice_resize_on_fixed_length_rejected(self) -> None:
        """A slice assignment that would resize a fixed-length shape is rejected."""
        bits = SmallBitvector(data=[Boolean(True)] * 3)
        with pytest.raises(SSZValueError):
            bits[1:] = [Boolean(False)]
        assert bits == SmallBitvector(data=[Boolean(True)] * 3)

    def test_pop_returns_last_and_shrinks(self) -> None:
        """Pop removes and returns the final element."""
        values = Uint16List4(data=[Uint16(1), Uint16(2)])
        assert values.pop() == Uint16(2)
        assert values == Uint16List4(data=[Uint16(1)])

    def test_byte_list_setitem_replaces_byte(self) -> None:
        """Byte lists mutate by integer byte value."""
        payload = SmallByteList(data=b"\xde\xad")
        payload[0] = 0xBE
        assert payload == SmallByteList(data=b"\xbe\xad")

    def test_byte_list_append_and_pop(self) -> None:
        """Byte lists append and pop by integer byte value."""
        payload = SmallByteList(data=b"\xde")
        payload.append(0xAD)
        assert payload == SmallByteList(data=b"\xde\xad")
        assert payload.pop() == 0xAD
        assert payload == SmallByteList(data=b"\xde")

    def test_bitlist_append_and_pop(self) -> None:
        """Bitlists append validated bits and pop them back."""
        bits = SmallBitlist(data=[Boolean(True)])
        bits.append(Boolean(False))
        assert bits == SmallBitlist(data=[Boolean(True), Boolean(False)])
        assert bits.pop() == Boolean(False)

    def test_setitem_slice_beyond_limit_rejected(self) -> None:
        """A slice assignment that would exceed the limit fails before storage changes."""
        values = Uint16List4(data=[Uint16(1)])
        with pytest.raises(SSZValueError):
            values[0:1] = [Uint16(2)] * 5
        assert values == Uint16List4(data=[Uint16(1)])

    def test_base_collection_leaves_element_validation_abstract(self) -> None:
        """The shared base defers single-element validation to each family."""
        values = Uint16List4(data=[])
        with pytest.raises(NotImplementedError):
            SSZCollection._validate_element(values, 1)


class TestSSZCollectionNegativeIndex:
    """
    Tests for addressing a collection from its end rather than its start.

    A position counted from the end resolves against the number of elements held.
    It never resolves against the capacity the type declares.
    Three elements under a capacity of four therefore address like this:

        held = [10, 20, 30]  under a capacity of 4

        [-1]   ->  30            the last element held
        [-3]   ->  10            the first
        [-4]   ->  IndexError    one before the first
        [3]    ->  IndexError    the slot the capacity leaves free

    The zeros that pad such a value out to its capacity exist only in its Merkle tree.
    They are not part of the value.
    So no position addresses them, from either end.
    """

    @pytest.mark.parametrize(
        "collection, replacement, expected",
        [
            pytest.param(
                Uint16Vector2(data=[Uint16(1), Uint16(2)]),
                Uint16(9),
                Uint16Vector2(data=[Uint16(1), Uint16(9)]),
                id="vector",
            ),
            pytest.param(
                Uint16List4(data=[Uint16(1), Uint16(2), Uint16(3)]),
                Uint16(9),
                Uint16List4(data=[Uint16(1), Uint16(2), Uint16(9)]),
                id="list",
            ),
            pytest.param(
                Uint16ProgressiveList(data=[Uint16(1), Uint16(2)]),
                Uint16(9),
                Uint16ProgressiveList(data=[Uint16(1), Uint16(9)]),
                id="progressive_list",
            ),
            pytest.param(
                SmallBitvector(data=[Boolean(True)] * 3),
                Boolean(False),
                SmallBitvector(data=[Boolean(True), Boolean(True), Boolean(False)]),
                id="bitvector",
            ),
            pytest.param(
                SmallBitlist(data=[Boolean(True), Boolean(True)]),
                Boolean(False),
                SmallBitlist(data=[Boolean(True), Boolean(False)]),
                id="bitlist",
            ),
            pytest.param(
                ProgressiveBitlist(data=[Boolean(True), Boolean(True)]),
                Boolean(False),
                ProgressiveBitlist(data=[Boolean(True), Boolean(False)]),
                id="progressive_bitlist",
            ),
            pytest.param(
                SmallByteList(data=b"\xde\xad\xbe"),
                0xEF,
                SmallByteList(data=b"\xde\xad\xef"),
                id="byte_list",
            ),
        ],
    )
    def test_a_negative_write_replaces_only_the_final_element(
        self, collection: SSZCollection[Any], replacement: Any, expected: SSZCollection[Any]
    ) -> None:
        """Position -1 writes the last element held, whichever shape holds it."""
        collection[-1] = replacement
        # Comparing the whole value proves both halves of the claim at once:
        #
        # - The final position took the new element.
        # - No earlier position moved.
        assert collection == expected

    @pytest.mark.parametrize(
        "collection, rejected, message",
        [
            pytest.param(
                Uint16Vector2(data=[Uint16(1), Uint16(2)]),
                "x",
                "Expected Uint16, got str",
                id="vector",
            ),
            pytest.param(
                Uint16List4(data=[Uint16(1), Uint16(2)]),
                "x",
                "Expected Uint16, got str",
                id="list",
            ),
            pytest.param(
                Uint16ProgressiveList(data=[Uint16(1), Uint16(2)]),
                "x",
                "Expected Uint16, got str",
                id="progressive_list",
            ),
            pytest.param(
                SmallBitvector(data=[Boolean(True)] * 3),
                2,
                "Boolean value must be 0 or 1, not 2",
                id="bitvector",
            ),
            pytest.param(
                SmallBitlist(data=[Boolean(True), Boolean(False)]),
                2,
                "Boolean value must be 0 or 1, not 2",
                id="bitlist",
            ),
            pytest.param(
                ProgressiveBitlist(data=[Boolean(True), Boolean(False)]),
                2,
                "Boolean value must be 0 or 1, not 2",
                id="progressive_bitlist",
            ),
        ],
    )
    def test_a_negative_write_of_a_rejected_element_leaves_the_value_alone(
        self, collection: SSZCollection[Any], rejected: Any, message: str
    ) -> None:
        """A position counted from the end is validated on exactly the same terms as any other."""
        contents_before = list(collection)
        with pytest.raises(SSZError) as exception_info:
            collection[-1] = rejected
        assert str(exception_info.value) == message
        # The incoming element is checked before it reaches storage.
        # A rejection therefore leaves the last position holding whatever it held.
        assert list(collection) == contents_before

    def test_a_negative_write_of_a_rejected_byte_reports_the_host_language_error(self) -> None:
        """A byte list rejects an out-of-range byte, but not with one of this library's errors."""
        payload = SmallByteList(data=b"\xde\xad\xbe")
        # A byte list stores a raw byte string.
        # The range check on a single byte is therefore the one the host language already
        # performs, and 256 fails it before any SSZ rule runs.
        #
        # This library's errors do not derive from the host language's value error.
        # A caller catching only SSZ errors will therefore miss this one.
        # Pinned as it stands.
        with pytest.raises(ValueError, match=r"^byte must be in range\(0, 256\)$"):
            payload[-1] = 256
        assert payload == SmallByteList(data=b"\xde\xad\xbe")

    @pytest.mark.parametrize(
        "collection, replacement, message",
        [
            pytest.param(
                Uint16Vector2(data=[Uint16(1), Uint16(2)]),
                [Uint16(9)],
                "Uint16Vector2 requires exactly 2 elements, got 1",
                id="vector",
            ),
            pytest.param(
                SmallBitvector(data=[Boolean(True)] * 3),
                [Boolean(False)],
                "SmallBitvector requires exactly 3 elements, got 2",
                id="bitvector",
            ),
        ],
    )
    def test_a_negative_slice_write_that_resizes_a_fixed_length_shape_is_rejected(
        self, collection: SSZCollection[Any], replacement: Any, message: str
    ) -> None:
        """A trailing range given fewer elements than it spans is a length error."""
        contents_before = list(collection)
        # The final two positions given one element leave the shape one element short:
        #
        #     2 elements:  [1, 2]     ->  [-2:] = [9]  ->  1 element,  needs 2
        #     3 bits:      [1, 1, 1]  ->  [-2:] = [0]  ->  2 elements, needs 3
        #
        # The resulting count is measured on a copy.
        # So the stored elements never move.
        with pytest.raises(SSZValueError) as exception_info:
            collection[-2:] = replacement
        assert str(exception_info.value) == message
        assert list(collection) == contents_before

    def test_a_growing_negative_slice_write_on_a_byte_list_is_rejected_atomically(self) -> None:
        """A trailing range given more bytes than the capacity allows changes nothing."""
        payload = ByteList4(data=b"\xde\xad\xbe")
        # 3 bytes held under a capacity of 4, replacing the final one with three:
        #
        #     stored:      de ad be
        #     [-1:] =            aa bb cc
        #     would give:  de ad aa bb cc   ->  5 bytes, one past the capacity of 4
        #
        # The capacity is enforced as the whole payload is stored back.
        # The write therefore lands complete or not at all.
        # A partly grown payload is never observable.
        with pytest.raises(SSZLimitError, match=r"^ByteList4 exceeds limit of 4, got 5$"):
            payload[-1:] = b"\xaa\xbb\xcc"
        assert payload == ByteList4(data=b"\xde\xad\xbe")

    @pytest.mark.parametrize(
        "collection, index, replacement, message",
        [
            pytest.param(
                Uint16Vector2(data=[Uint16(1), Uint16(2)]),
                -3,
                Uint16(9),
                "list assignment index out of range",
                id="one_before_a_fixed_length_shape",
            ),
            pytest.param(
                Uint16List4(data=[Uint16(1), Uint16(2), Uint16(3)]),
                -4,
                Uint16(9),
                "list assignment index out of range",
                id="one_before_the_elements_held",
            ),
            pytest.param(
                ByteList4(data=b"\xde\xad\xbe"),
                -4,
                0xFF,
                "bytearray index out of range",
                id="one_before_the_bytes_held",
            ),
        ],
    )
    def test_an_out_of_range_negative_write_leaves_the_value_alone(
        self, collection: SSZCollection[Any], index: int, replacement: Any, message: str
    ) -> None:
        """A position before the first element held addresses nothing to write to."""
        contents_before = list(collection)
        # The two variable-length cases hold 3 elements under a capacity of 4.
        # Position -4 there reaches one before the first element.
        # It does not reach the free slot the capacity leaves.
        with pytest.raises(IndexError) as exception_info:
            collection[index] = replacement
        assert str(exception_info.value) == message
        assert list(collection) == contents_before

    def test_a_frozen_shape_rejects_a_negative_write(self) -> None:
        """Freezing a type closes the path from the end along with every other one."""

        class FrozenVector(Uint16Vector2):
            MUTABLE = False

        class FrozenByteList(ByteList4):
            MUTABLE = False

        values = FrozenVector(data=[Uint16(1), Uint16(2)])
        with pytest.raises(SSZTypeError, match=r"^FrozenVector is immutable$"):
            values[-1] = Uint16(9)

        # A byte list replaces its whole payload on any write.
        # The refusal therefore has to come first.
        # Reaching the payload swap would rebuild the value instead of rejecting it.
        payload = FrozenByteList(data=b"\xde\xad")
        with pytest.raises(SSZTypeError, match=r"^FrozenByteList is immutable$"):
            payload[-1] = 0xFF

        assert values == FrozenVector(data=[Uint16(1), Uint16(2)])
        assert payload == FrozenByteList(data=b"\xde\xad")


class TestSSZMutabilityFlag:
    """
    Tests for configuring mutability per type.

    MUTABLE defaults to on and is inherited. A type that sets it to False
    rejects every mutation, while construction and reads keep working.
    """

    def test_immutable_list_rejects_mutation(self) -> None:
        """An immutable list rejects element assignment, append, pop, and data assignment."""

        class FrozenUint16List4(Uint16List4):
            MUTABLE = False

        values = FrozenUint16List4(data=[Uint16(1), Uint16(2)])
        with pytest.raises(SSZTypeError):
            values[0] = Uint16(9)
        with pytest.raises(SSZTypeError):
            values.append(Uint16(3))
        with pytest.raises(SSZTypeError):
            values.pop()
        with pytest.raises(SSZTypeError):
            values.data = [Uint16(9)]
        assert values == FrozenUint16List4(data=[Uint16(1), Uint16(2)])

    def test_immutable_byte_list_rejects_mutation(self) -> None:
        """An immutable byte list rejects byte assignment, append, and pop."""

        class FrozenByteList(SmallByteList):
            MUTABLE = False

        payload = FrozenByteList(data=b"\xde\xad")
        with pytest.raises(SSZTypeError):
            payload[0] = 0xBE
        with pytest.raises(SSZTypeError):
            payload.append(0xEF)
        with pytest.raises(SSZTypeError):
            payload.pop()
        assert payload == FrozenByteList(data=b"\xde\xad")

    def test_immutable_bitlist_rejects_mutation(self) -> None:
        """An immutable bitlist rejects append and pop."""

        class FrozenBitlist(SmallBitlist):
            MUTABLE = False

        bits = FrozenBitlist(data=[Boolean(True)])
        with pytest.raises(SSZTypeError):
            bits.append(Boolean(False))
        with pytest.raises(SSZTypeError):
            bits.pop()

    def test_immutable_container_rejects_field_assignment(self) -> None:
        """An immutable container rejects field assignment while reads keep working."""

        class FrozenContainer(TwoFieldContainer):
            MUTABLE = False

        container = FrozenContainer(x=Uint8(1), y=Uint16(2))
        with pytest.raises(SSZTypeError):
            container.x = Uint8(3)
        assert container.x == Uint8(1)

    def test_immutable_progressive_list_rejects_mutation(self) -> None:
        """The flag freezes a progressive list, which has no capacity of its own to stop it."""

        class FrozenProgressiveList(ProgressiveList[Uint16]):
            MUTABLE = False

        values = FrozenProgressiveList(data=[Uint16(1), Uint16(2)])
        with pytest.raises(SSZTypeError):
            values[0] = Uint16(9)
        with pytest.raises(SSZTypeError):
            values.append(Uint16(3))
        with pytest.raises(SSZTypeError):
            values.pop()
        with pytest.raises(SSZTypeError):
            values.data = [Uint16(9)]
        assert values == FrozenProgressiveList(data=[Uint16(1), Uint16(2)])

    def test_immutable_progressive_bitlist_rejects_mutation(self) -> None:
        """The flag freezes a progressive bitlist on the same terms."""

        class FrozenProgressiveBitlist(ProgressiveBitlist):
            MUTABLE = False

        bits = FrozenProgressiveBitlist(data=[Boolean(True)])
        with pytest.raises(SSZTypeError):
            bits[0] = Boolean(False)
        with pytest.raises(SSZTypeError):
            bits.append(Boolean(False))
        with pytest.raises(SSZTypeError):
            bits.pop()
        assert bits == FrozenProgressiveBitlist(data=[Boolean(True)])

    def test_immutable_progressive_container_rejects_field_assignment(self) -> None:
        """The flag freezes a progressive container while reads keep working."""

        class FrozenSquare(ProgressiveContainer):
            MUTABLE = False
            ACTIVE_FIELDS = (1, 0, 1)

            side: Uint16
            color: Uint8

        square = FrozenSquare(side=Uint16(0x1234), color=Uint8(0x42))
        with pytest.raises(SSZTypeError):
            square.side = Uint16(0x5678)
        assert square.side == Uint16(0x1234)

    def test_mutability_flag_is_inherited(self) -> None:
        """A subclass of an immutable type stays immutable."""

        class FrozenBase(Uint16List4):
            MUTABLE = False

        class StillFrozen(FrozenBase):
            pass

        values = StillFrozen(data=[Uint16(1)])
        with pytest.raises(SSZTypeError):
            values.append(Uint16(2))

    def test_direct_data_assignment_revalidates(self) -> None:
        """Assigning the data field directly runs the same validation as construction."""
        values = Uint16List4(data=[Uint16(1)])
        values.data = cast(Any, [2, 3])
        assert values == Uint16List4(data=[Uint16(2), Uint16(3)])
        with pytest.raises((SSZValueError, ValidationError)):
            values.data = cast(Any, [1, 2, 3, 4, 5])

    def test_container_field_assignment_coerces(self) -> None:
        """Containers are mutable; assigned values coerce into the field type."""
        container = TwoFieldContainer(x=Uint8(1), y=Uint16(2))
        container.x = 3  # ty: ignore[invalid-assignment]
        assert container == TwoFieldContainer(x=Uint8(3), y=Uint16(2))

    def test_container_collection_field_raw_payload_rejected(self) -> None:
        """A raw payload assigned to a collection field fails, exactly as at construction."""
        container = ThreeFieldContainer(a=Uint8(0), b=Uint64(0), c=Uint16List4(data=[]))
        with pytest.raises(ValidationError):
            container.c = [1, 2]  # ty: ignore[invalid-assignment]
        container.c = Uint16List4(data=[Uint16(1), Uint16(2)])
        assert container.c == Uint16List4(data=[Uint16(1), Uint16(2)])

    def test_container_assignment_of_typed_value_passes_through(self) -> None:
        """An already-typed value is assigned without re-coercion."""
        container = TwoFieldContainer(x=Uint8(1), y=Uint16(2))
        container.y = Uint16(9)
        assert container.y == Uint16(9)

    def test_container_unknown_attribute_assignment_raises(self) -> None:
        """Assigning an attribute that is not a field still raises."""
        container = TwoFieldContainer(x=Uint8(1), y=Uint16(2))
        with pytest.raises((AttributeError, ValueError)):
            container.unknown = 1  # ty: ignore[unresolved-attribute]

    def test_container_hashes_by_tree_root(self) -> None:
        """Containers hash by Merkle root, so they work as dict keys."""
        first = TwoFieldContainer(x=Uint8(1), y=Uint16(2))
        second = TwoFieldContainer(x=Uint8(1), y=Uint16(2))
        assert hash(first) == hash(second)
        lookup = {first: "found"}
        assert lookup[second] == "found"


class TestDefaultValue:
    """
    The default factory and the zeroed check, both defined once on the shared base.

    Construction with no argument gives the default of a type, and `default()` is that
    same request spelled as a call on the type. The spelling exists because a static
    checker reads a struct's declared field list rather than the defaults this library
    attaches to it, so the bare form reads there as missing its arguments.
    """

    @pytest.mark.parametrize(
        "ssz_type, expected_default",
        [
            pytest.param(Uint16, Uint16(0), id="uint"),
            pytest.param(Boolean, Boolean(False), id="boolean"),
            # A fixed byte array is a vector of single bytes, so every byte is zero.
            pytest.param(Root, Root(b"\x00" * 32), id="fixed_byte_array"),
            pytest.param(SmallBitvector, SmallBitvector(data=[Boolean(False)] * 3), id="bitvector"),
            pytest.param(Uint16Vector2, Uint16Vector2(data=[Uint16(0), Uint16(0)]), id="vector"),
            # Every variable-size shape defaults to its own empty value.
            pytest.param(Uint16List4, Uint16List4(data=[]), id="list"),
            pytest.param(SmallBitlist, SmallBitlist(data=[]), id="bitlist"),
            pytest.param(SmallByteList, SmallByteList(data=b""), id="byte_list"),
            pytest.param(Uint16ProgressiveList, Uint16ProgressiveList(data=[]), id="progressive"),
            pytest.param(ProgressiveBitlist, ProgressiveBitlist(data=[]), id="progressive_bitlist"),
            pytest.param(
                TwoFieldContainer, TwoFieldContainer(x=Uint8(0), y=Uint16(0)), id="container"
            ),
        ],
    )
    def test_every_shape_but_the_union_answers_with_its_own_default(
        self, ssz_type: type[SSZType], expected_default: SSZType
    ) -> None:
        """Each family builds the value the spec names, and that value reads as zeroed."""
        assert ssz_type.default() == expected_default
        assert ssz_type.default().is_zero() is True

    def test_a_no_argument_construction_and_the_factory_agree(self) -> None:
        """The factory is a second spelling of one request, not a second kind of default."""
        assert Uint16() == Uint16.default()
        assert Boolean() == Boolean.default()
        assert SmallBitvector() == SmallBitvector.default()
        assert Uint16Vector2() == Uint16Vector2.default()
        assert Uint16List4() == Uint16List4.default()
        assert SmallByteList() == SmallByteList.default()

    def test_each_call_builds_a_new_value(self) -> None:
        """Values are mutable, so a default must never be cached and handed out twice."""
        first, second = Uint16List4.default(), Uint16List4.default()
        assert first is not second
        first.append(Uint16(1))
        # The mutation applied to the first default leaves the next one at empty.
        assert Uint16List4.default() == Uint16List4(data=[])

    def test_the_factory_binds_to_the_concrete_subtype(self) -> None:
        """A named subtype builds itself, never the base it was declared from."""
        assert type(TypedUint16.default()) is TypedUint16
        assert TypedUint16.default() == TypedUint16(0)

    def test_is_zero_compares_against_the_runtime_type(self) -> None:
        """The comparison uses the type of the value, so a subtype meets its own default."""
        # A TypedUint16 and a Uint16 never compare at all, so reading the declared type
        # rather than the runtime one would raise here instead of answering.
        assert TypedUint16(0).is_zero() is True
        assert TypedUint16(1).is_zero() is False

    def test_a_union_has_no_default_to_build(self) -> None:
        """The one shape the spec leaves without a default refuses to invent one."""
        with pytest.raises(SSZDefaultError, match=r"^SmallUnion has no default value$"):
            SmallUnion.default()


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

    @pytest.mark.parametrize(
        "collection_type, expected_length",
        [
            pytest.param(Uint16Vector2, 2, id="vector"),
            pytest.param(SmallBitvector, 3, id="bitvector"),
        ],
    )
    def test_of_with_no_elements_is_a_length_error_on_a_fixed_length_shape(
        self, collection_type: type[SSZCollection[Any]], expected_length: int
    ) -> None:
        """No argument here means zero elements, which is a count, not a missing input."""
        # This factory always states the elements, so stating none of them is a count of
        # zero. Only construction with no argument at all asks for the default.
        type_name = collection_type.__name__
        with pytest.raises((SSZValueError, ValidationError)) as exception_info:
            collection_type.of()
        assert str(exception_info.value) == (
            f"{type_name} requires exactly {expected_length} elements, got 0"
        )
        # The same shape asked for its default is full, not empty.
        assert len(collection_type.default()) == expected_length

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
