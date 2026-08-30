"""Tests for SSZModel and SSZType base class behavior."""

from collections.abc import Callable
from decimal import Decimal
from typing import IO, Any, cast

import pytest
from pydantic import ValidationError

from ssz import (
    SSZTypeError,
    SSZValueError,
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Uint128,
    Uint256,
)
from ssz.bitfields import BitList, BitVector, ProgressiveBitList
from ssz.boolean import Boolean
from ssz.byte_arrays import ByteList, ByteVector
from ssz.collections import List, ProgressiveList, Vector
from ssz.container import Container, ProgressiveContainer
from ssz.exceptions import SSZError
from ssz.merkleization import ZERO_ROOT, Root, hash_tree_root
from ssz.paths import chunk_count
from ssz.ssz_base import SSZCollection, SSZType
from ssz.uint import BaseUint
from ssz.union import CompatibleUnion


class Uint16List4(List[Uint16]):
    """A list with up to 4 Uint16 values."""

    LIMIT = 4


class Uint16Vector2(Vector[Uint16]):
    """A vector of exactly 2 Uint16 values."""

    LENGTH = 2


class Uint16ListVector2(Vector[Uint16List4]):
    """A vector of two lists, whose elements leave it with no width of its own."""

    LENGTH = 2


class TypedUint16(Uint16):
    """A Uint16 subtype, as applications define semantic integer types."""


class TypedUint16List4(List[TypedUint16]):
    """A list with up to 4 TypedUint16 values."""

    LIMIT = 4


class RootList4(List[Root]):
    """A list with up to 4 Root values."""

    LIMIT = 4


class SmallBitVector(BitVector):
    """A bitvector with exactly 3 bits."""

    LENGTH = 3


class SmallByteList(ByteList):
    """A byte list with up to 10 bytes."""

    LIMIT = 10


class ByteList4(ByteList):
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


class SmallBitList(BitList):
    """A bitlist with a small limit, used to test SSZModel.__len__ data path."""

    LIMIT = 8


class Uint16ProgressiveList(ProgressiveList[Uint16]):
    """A progressive list of Uint16 values, the unbounded sequence shape."""


class SmallUnion(CompatibleUnion):
    """A union over one option, the only shape the spec gives no default value."""

    OPTIONS = {1: Uint8}


# Six families declare how many elements they hold.
# Each one appears twice below, once with a typed count and once with a plain integer.
# A pair declared both ways is what makes a byte-for-byte comparison possible.
#
# Every capacity here is 4.
# One shared payload therefore exercises all six.


class TypedLengthVector(Vector[Uint8]):
    """A vector whose element count is declared with a typed value."""

    LENGTH = Uint64(4)


class PlainLengthVector(Vector[Uint8]):
    """The same vector, declared with a plain integer."""

    LENGTH = 4


class TypedLimitList(List[Uint8]):
    """A list whose capacity is declared with a typed value."""

    LIMIT = Uint64(4)


class PlainLimitList(List[Uint8]):
    """The same list, declared with a plain integer."""

    LIMIT = 4


class TypedLengthBitVector(BitVector):
    """A bitvector whose bit count is declared with a typed value."""

    LENGTH = Uint64(4)


class PlainLengthBitVector(BitVector):
    """The same bitvector, declared with a plain integer."""

    LENGTH = 4


class TypedLimitBitList(BitList):
    """A bitlist whose capacity is declared with a typed value."""

    LIMIT = Uint64(4)


class PlainLimitBitList(BitList):
    """The same bitlist, declared with a plain integer."""

    LIMIT = 4


class TypedLengthBytes(ByteVector):
    """A fixed byte array whose byte count is declared with a typed value."""

    LENGTH = Uint64(4)


class PlainLengthBytes(ByteVector):
    """The same fixed byte array, declared with a plain integer."""

    LENGTH = 4


class TypedLimitByteList(ByteList):
    """A byte list whose capacity is declared with a typed value."""

    LIMIT = Uint64(4)


class PlainLimitByteList(ByteList):
    """The same byte list, declared with a plain integer."""

    LIMIT = 4


class TestSSZModelLength:
    """
    Tests for SSZModel.__len__() on both collection and container models.

    Uses BitList (not List) for the data-path because List overrides
    __len__ with its own implementation. BitList inherits SSZModel's version.
    """

    def test_length_data_path_via_bitlist(self) -> None:
        """BitList delegates to SSZModel.__len__ which returns len(data)."""
        bl = SmallBitList(data=(Boolean(True), Boolean(False), Boolean(True)))
        assert len(bl) == 3

    def test_length_empty_data_path_via_bitlist(self) -> None:
        bl = SmallBitList(data=())
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

    def test_a_value_that_leaves_bytes_behind_is_refused(self) -> None:
        """One canonical encoding per value, which takes the whole input to decode."""

        # A type that under-reads its budget, which none of this library's own types do.
        class OneByteOfMany(SSZType):
            """A type that reads one byte and leaves the rest of its budget unread."""

            @classmethod
            def fixed_size(cls) -> None:
                """No width, so no caller derives one to hand it."""
                return None

            def serialize(self, stream: IO[bytes]) -> int:
                """Write the one byte this type stands for."""
                return stream.write(b"\x00")

            @classmethod
            def deserialize(cls, stream: IO[bytes], scope: int) -> "OneByteOfMany":
                """Read one byte, whatever the budget was."""
                stream.read(1)
                return cls()

        # The outermost decode compares what was read against what was given.
        with pytest.raises(SSZValueError) as exception_info:
            OneByteOfMany.decode_bytes(b"\x00\xff")

        assert str(exception_info.value) == "1 byte(s) past the end of the value"


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
        bits = SmallBitVector(data=[Boolean(True), Boolean(False), Boolean(True)])
        assert list(bits) == [Boolean(True), Boolean(False), Boolean(True)]

    def test_bitlist_yields_its_bits(self) -> None:
        """A bounded bitlist iterates booleans."""
        bits = SmallBitList(data=[Boolean(True), Boolean(False)])
        assert list(bits) == [Boolean(True), Boolean(False)]

    def test_progressive_bitlist_yields_its_bits(self) -> None:
        """A progressive bitlist iterates booleans on the same terms."""
        bits = ProgressiveBitList(data=[Boolean(False), Boolean(True)])
        assert list(bits) == [Boolean(False), Boolean(True)]

    def test_byte_list_yields_its_byte_values(self) -> None:
        """A byte list iterates integer byte values, matching what its API mutates by."""
        payload = SmallByteList(data=b"\xde\xad")
        assert list(payload) == [0xDE, 0xAD]

    def test_membership_reads_the_contents(self) -> None:
        """The in operator routes through iteration, so it tests contents, not field names."""
        assert Boolean(True) in SmallBitList(data=[Boolean(True)])
        assert Boolean(True) not in SmallBitList(data=[Boolean(False)])
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
        bits = SmallBitVector(data=[Boolean(True), Boolean(True), Boolean(True)])
        bits[1:] = [Boolean(False), Boolean(False)]
        assert bits == SmallBitVector(data=[Boolean(True), Boolean(False), Boolean(False)])

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
        assert not hasattr(SmallBitVector, "append")
        assert not hasattr(SmallBitVector, "pop")

    def test_setitem_slice_resize_on_fixed_length_rejected(self) -> None:
        """A slice assignment that would resize a fixed-length shape is rejected."""
        bits = SmallBitVector(data=[Boolean(True)] * 3)
        with pytest.raises(SSZValueError):
            bits[1:] = [Boolean(False)]
        assert bits == SmallBitVector(data=[Boolean(True)] * 3)

    def test_pop_returns_last_and_shrinks(self) -> None:
        """Pop removes and returns the final element."""
        values = Uint16List4(data=[Uint16(1), Uint16(2)])
        assert values.pop() == Uint16(2)
        assert values == Uint16List4(data=[Uint16(1)])

    @pytest.mark.parametrize(
        "shape",
        [Uint16List4, Uint16ProgressiveList, SmallBitList, ProgressiveBitList],
        ids=["list", "progressive list", "bitlist", "progressive bitlist"],
    )
    def test_popping_an_empty_collection_is_refused(self, shape: Any) -> None:
        """An empty collection has no last element, so the store refuses."""
        # Shrinking breaches no bound, so nothing rejects the count a pop would leave.
        # The refusal is the store's own, and it is the one indexing already gives.
        empty = shape()
        with pytest.raises(IndexError):
            empty.pop()
        assert len(empty) == 0

    @pytest.mark.parametrize(
        ("shape", "contents"),
        [
            (Uint16List4, (Uint16(1), Uint16(2))),
            (SmallBitList, (Boolean(True), Boolean(False))),
        ],
        ids=["list", "bitlist"],
    )
    def test_a_tuple_input_is_stored_as_the_list_mutation_writes_through(
        self, shape: Any, contents: tuple[Any, ...]
    ) -> None:
        """The contents are declared a sequence to accept any iterable, and stored as a list."""
        # A tuple is accepted here only because the declared type is the wider one.
        values = shape(data=contents)

        # Validation returns a list whatever it was handed, which is what a mutator writes through.
        assert type(values.data) is list

        values.append(contents[0])
        assert values.pop() == contents[0]
        assert values == shape(data=contents)

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
        """BitLists append validated bits and pop them back."""
        bits = SmallBitList(data=[Boolean(True)])
        bits.append(Boolean(False))
        assert bits == SmallBitList(data=[Boolean(True), Boolean(False)])
        assert bits.pop() == Boolean(False)

    def test_setitem_slice_beyond_limit_rejected(self) -> None:
        """A slice assignment that would exceed the limit fails before storage changes."""
        values = Uint16List4(data=[Uint16(1)])
        with pytest.raises(SSZValueError):
            values[0:1] = [Uint16(2)] * 5
        assert values == Uint16List4(data=[Uint16(1)])

    def test_base_collection_leaves_element_validation_abstract(self) -> None:
        """The shared base defers single-element validation to each family."""
        # The rule depends on the declared element type, never on the value holding it.
        # The base declares it as a classmethod and each family fills it in.
        with pytest.raises(NotImplementedError):
            SSZCollection._validate_element(1)


class TestSliceWriteCount:
    """
    Tests for the count a slice write leaves behind.

    Each case writes the same slice to a plain list and to a collection, and requires the
    two to agree on the count held or on the error raised.
    """

    def test_a_growing_write_agrees_with_a_plain_list(self) -> None:
        """One position replaced by three leaves two more elements than were held."""
        values = Uint16List4(data=[Uint16(1), Uint16(2)])
        plain = [Uint16(1), Uint16(2)]

        values[0:1] = [Uint16(7), Uint16(8), Uint16(9)]
        plain[0:1] = [Uint16(7), Uint16(8), Uint16(9)]

        # Held 2, spanned 1, given 3, so 4 — exactly the capacity, and not past it.
        assert list(values) == plain
        assert len(values) == 4

    def test_a_shrinking_write_agrees_with_a_plain_list(self) -> None:
        """A span given no elements at all deletes it."""
        values = Uint16List4(data=[Uint16(1), Uint16(2), Uint16(3)])
        plain = [Uint16(1), Uint16(2), Uint16(3)]

        values[1:3] = []
        plain[1:3] = []

        assert list(values) == plain
        assert len(values) == 1

    def test_a_span_reaching_past_the_end_appends(self) -> None:
        """A slice is clamped to the count held, so a span past the end spans nothing."""
        values = Uint16List4(data=[Uint16(1)])
        plain = [Uint16(1)]

        values[10:20] = [Uint16(2)]
        plain[10:20] = [Uint16(2)]

        # Nothing was spanned, so the given element is added rather than replacing one.
        assert list(values) == plain
        assert len(values) == 2

    def test_a_span_measured_backwards_spans_nothing(self) -> None:
        """A stop before the start selects no position, so the given elements are inserted."""
        values = Uint16List4(data=[Uint16(1), Uint16(2)])
        plain = [Uint16(1), Uint16(2)]

        values[2:1] = [Uint16(9)]
        plain[2:1] = [Uint16(9)]

        assert list(values) == plain
        assert len(values) == 3

    @pytest.mark.parametrize(
        "collection, replacement, message",
        [
            pytest.param(
                Uint16Vector2(data=[Uint16(1), Uint16(2)]),
                [Uint16(7), Uint16(8)],
                "attempt to assign sequence of size 2 to extended slice of size 1",
                id="fixed_length_shape",
            ),
            pytest.param(
                Uint16List4(data=[Uint16(1), Uint16(2), Uint16(3), Uint16(4)]),
                [Uint16(7)],
                "attempt to assign sequence of size 1 to extended slice of size 2",
                id="bounded_shape_at_its_capacity",
            ),
        ],
    )
    def test_a_step_other_than_one_cannot_resize(
        self, collection: SSZCollection[Any], replacement: Any, message: str
    ) -> None:
        """A stepped write holds one element per position spanned, and resizes nothing."""
        contents_before = list(collection)

        # A step of 2 across 2 or 4 positions spans 1 or 2 of them.
        # Given any other number of elements, the host language refuses the write itself.
        # The declared capacity never comes into it: the count cannot have changed.
        #
        # So the error is the one a plain list raises, not a length or a capacity error.
        with pytest.raises(ValueError) as exception_info:
            collection[::2] = replacement
        assert str(exception_info.value) == message
        assert not isinstance(exception_info.value, SSZError)
        assert list(collection) == contents_before

    def test_a_step_other_than_one_writes_one_element_per_position(self) -> None:
        """Given exactly the count it spans, a stepped write lands."""
        values = Uint16List4(data=[Uint16(1), Uint16(2), Uint16(3), Uint16(4)])
        plain = [Uint16(1), Uint16(2), Uint16(3), Uint16(4)]

        values[::2] = [Uint16(7), Uint16(8)]
        plain[::2] = [Uint16(7), Uint16(8)]

        assert list(values) == plain
        assert len(values) == 4

    def test_a_reversing_write_replaces_every_element(self) -> None:
        """A step of -1 spans every position, which is a stepped write like any other."""
        values = Uint16Vector2(data=[Uint16(1), Uint16(2)])
        plain = [Uint16(1), Uint16(2)]

        values[::-1] = [Uint16(7), Uint16(8)]
        plain[::-1] = [Uint16(7), Uint16(8)]

        # Reversed on the way in: the last position takes the first element given.
        assert list(values) == plain == [Uint16(8), Uint16(7)]

    def test_a_reversing_write_of_the_wrong_count_is_refused(self) -> None:
        """A step of -1 spans every position, so it cannot resize either."""
        values = Uint16List4(data=[Uint16(1), Uint16(2)])
        with pytest.raises(ValueError) as exception_info:
            values[::-1] = [Uint16(7)]
        assert str(exception_info.value) == (
            "attempt to assign sequence of size 1 to extended slice of size 2"
        )
        assert list(values) == [Uint16(1), Uint16(2)]

    def test_a_step_of_zero_spans_nothing_and_is_refused(self) -> None:
        """A step of zero names no run of positions, and is refused before any check."""
        values = Uint16List4(data=[Uint16(1)])
        with pytest.raises(ValueError) as exception_info:
            values[::0] = [Uint16(7)]
        assert str(exception_info.value) == "slice step cannot be zero"
        assert list(values) == [Uint16(1)]

    def test_a_step_that_is_not_a_number_is_refused(self) -> None:
        """Resolving the slice rejects a step that names no distance."""
        values = Uint16List4(data=[Uint16(1)])
        with pytest.raises(TypeError) as exception_info:
            values[:: cast("Any", "two")] = [Uint16(7)]
        assert str(exception_info.value) == (
            "slice indices must be integers or None or have an __index__ method"
        )
        assert list(values) == [Uint16(1)]


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
                SmallBitVector(data=[Boolean(True)] * 3),
                Boolean(False),
                SmallBitVector(data=[Boolean(True), Boolean(True), Boolean(False)]),
                id="bitvector",
            ),
            pytest.param(
                SmallBitList(data=[Boolean(True), Boolean(True)]),
                Boolean(False),
                SmallBitList(data=[Boolean(True), Boolean(False)]),
                id="bitlist",
            ),
            pytest.param(
                ProgressiveBitList(data=[Boolean(True), Boolean(True)]),
                Boolean(False),
                ProgressiveBitList(data=[Boolean(True), Boolean(False)]),
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
                "expected Uint16, got str",
                id="vector",
            ),
            pytest.param(
                Uint16List4(data=[Uint16(1), Uint16(2)]),
                "x",
                "expected Uint16, got str",
                id="list",
            ),
            pytest.param(
                Uint16ProgressiveList(data=[Uint16(1), Uint16(2)]),
                "x",
                "expected Uint16, got str",
                id="progressive_list",
            ),
            pytest.param(
                SmallBitVector(data=[Boolean(True)] * 3),
                2,
                "a boolean is 0 or 1, got 2",
                id="bitvector",
            ),
            pytest.param(
                SmallBitList(data=[Boolean(True), Boolean(False)]),
                2,
                "a boolean is 0 or 1, got 2",
                id="bitlist",
            ),
            pytest.param(
                ProgressiveBitList(data=[Boolean(True), Boolean(False)]),
                2,
                "a boolean is 0 or 1, got 2",
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
        # The range check on a single byte is therefore the one the host language already performs.
        # 256 fails it before any SSZ rule runs.
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
                "Uint16Vector2 holds exactly 2 elements, got 1",
                id="vector",
            ),
            pytest.param(
                SmallBitVector(data=[Boolean(True)] * 3),
                [Boolean(False)],
                "SmallBitVector holds exactly 3 elements, got 2",
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
        # The resulting count is computed before anything is stored.
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
        with pytest.raises(SSZValueError, match=r"^ByteList4 holds at most 4 bytes, got 5$"):
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

        class FrozenBitList(SmallBitList):
            MUTABLE = False

        bits = FrozenBitList(data=[Boolean(True)])
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

        class FrozenProgressiveBitList(ProgressiveBitList):
            MUTABLE = False

        bits = FrozenProgressiveBitList(data=[Boolean(True)])
        with pytest.raises(SSZTypeError):
            bits[0] = Boolean(False)
        with pytest.raises(SSZTypeError):
            bits.append(Boolean(False))
        with pytest.raises(SSZTypeError):
            bits.pop()
        assert bits == FrozenProgressiveBitList(data=[Boolean(True)])

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

    def test_a_mutated_value_is_filed_under_a_root_it_no_longer_has(self) -> None:
        """Hashing by root is hashing by value, so mutation strands an entry under its old key."""
        # The two rules meet here: a container is mutable, and it hashes by what it holds.
        # A dict files an entry by the hash the key had on the way in, and never revisits it.
        #
        # So this is the cost of value semantics, not a defect in them.
        # A value held in a dict or a set has to go unmutated for as long as it is held.
        value = TwoFieldContainer(x=Uint8(1), y=Uint16(2))
        lookup = {value: "found"}
        before = hash(value)

        value.x = Uint8(7)

        # The root moved, so the entry is filed under a key nothing in the dict now equals.
        assert hash(value) != before
        assert TwoFieldContainer(x=Uint8(1), y=Uint16(2)) not in lookup
        # Looking the mutated value up again is not asserted, and cannot be.
        # A dict compares the key it lands on by identity before it compares the hash.
        # A probe that reaches this entry's slot answers found however the root moved.
        assert next(iter(lookup)) is value


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
            pytest.param(SmallBitVector, SmallBitVector(data=[Boolean(False)] * 3), id="bitvector"),
            pytest.param(Uint16Vector2, Uint16Vector2(data=[Uint16(0), Uint16(0)]), id="vector"),
            # Every variable-size shape defaults to its own empty value.
            pytest.param(Uint16List4, Uint16List4(data=[]), id="list"),
            pytest.param(SmallBitList, SmallBitList(data=[]), id="bitlist"),
            pytest.param(SmallByteList, SmallByteList(data=b""), id="byte_list"),
            pytest.param(Uint16ProgressiveList, Uint16ProgressiveList(data=[]), id="progressive"),
            pytest.param(ProgressiveBitList, ProgressiveBitList(data=[]), id="progressive_bitlist"),
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
        assert SmallBitVector() == SmallBitVector.default()
        assert Uint16Vector2() == Uint16Vector2.default()
        assert Uint16List4() == Uint16List4.default()
        assert SmallByteList() == SmallByteList.default()

    def test_empty_builds_the_default_value(self) -> None:
        """`empty` builds what `default` builds."""
        assert Uint16List4.empty() == Uint16List4.default()
        assert SmallBitList.empty() == SmallBitList.default()
        assert TwoFieldContainer.empty() == TwoFieldContainer.default()

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
        # A TypedUint16 and a Uint16 never compare at all.
        # Reading the declared type rather than the runtime one would raise here.
        assert TypedUint16(0).is_zero() is True
        assert TypedUint16(1).is_zero() is False

    def test_a_union_has_no_default_to_build(self) -> None:
        """The one shape the spec leaves without a default refuses to invent one."""
        with pytest.raises(SSZTypeError, match=r"^SmallUnion has no default value$"):
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
            pytest.param(SmallBitVector, 3, id="bitvector"),
        ],
    )
    def test_of_with_no_elements_is_a_length_error_on_a_fixed_length_shape(
        self, collection_type: type[SSZCollection[Any]], expected_length: int
    ) -> None:
        """No argument here means zero elements, which is a count, not a missing input."""
        # This factory always states the elements, so stating none of them is a count of zero.
        # Only construction with no argument at all asks for the default.
        type_name = collection_type.__name__
        with pytest.raises(ValidationError) as exception_info:
            collection_type.of()
        assert f"{type_name} holds exactly {expected_length} elements, got 0" in str(
            exception_info.value
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
        expected = SmallBitVector(data=[Boolean(True), Boolean(False), Boolean(True)])
        assert SmallBitVector.of(True, False, True) == expected

    def test_of_bitlist_accepts_splatted_bits(self) -> None:
        """An existing bit sequence splats into element arguments."""
        bits = [True, False]
        assert SmallBitList.of(*bits) == SmallBitList(data=[Boolean(True), Boolean(False)])

    def test_of_byte_list_elements_are_ints(self) -> None:
        """A byte list's elements are individual byte values."""
        assert SmallByteList.of(0xDE, 0xAD) == SmallByteList(data=b"\xde\xad")

    def test_of_rejects_bool_for_uint_elements(self) -> None:
        """A bool is not an integer element, even though bool subclasses int."""
        with pytest.raises(SSZTypeError):
            Uint16List4.of(True)

    def test_of_rejects_other_uint_widths(self) -> None:
        """A uint of another width is a type error, regardless of its value."""
        with pytest.raises(SSZTypeError):
            Uint16List4.of(Uint32(7))

    def test_of_accepts_a_parent_uint_class(self) -> None:
        """A value of the element type's parent class converts into the element type."""
        values = TypedUint16List4.of(Uint16(7))
        assert values == TypedUint16List4(data=[TypedUint16(7)])
        assert type(values.data[0]) is TypedUint16

    def test_of_rejects_a_child_uint_class(self) -> None:
        """A value of a child class of the element type is a type error."""
        with pytest.raises(SSZTypeError):
            Uint16List4.of(TypedUint16(7))

    def test_of_beyond_limit_rejected(self) -> None:
        """More element arguments than the limit fail validation."""
        with pytest.raises(ValidationError) as exception_info:
            Uint16List4.of(1, 2, 3, 4, 5)
        assert "Uint16List4 holds at most 4 elements, got 5" in str(exception_info.value)

    def test_of_converts_plain_bytes_elements(self) -> None:
        """Plain bytes, such as bytes.fromhex output, convert into byte-array elements."""
        payload = bytes.fromhex("ab" * 32)
        values = RootList4.of(payload)
        assert values == RootList4(data=[Root(payload)])
        assert type(values.data[0]) is Root

    def test_of_rejects_hex_string_elements(self) -> None:
        """A hex string is not bytes; convert it with bytes.fromhex first."""
        with pytest.raises(SSZTypeError) as exception_info:
            RootList4.of("ab" * 32)
        assert str(exception_info.value) == "expected Root, got str"

    def test_of_wrong_length_bytes_surfaces_the_element_s_own_refusal(self) -> None:
        """An ancestor-class element that fails construction reports why, not merely that."""
        with pytest.raises(ValidationError) as exception_info:
            RootList4.of(b"\xab\xcd")
        assert "Root holds exactly 32 bytes, got 2" in str(exception_info.value)

    def test_of_returns_the_subclass_type(self) -> None:
        """The factory binds to the concrete subclass, not the base."""
        assert type(Uint16List4.of(1)) is Uint16List4

    def test_constructors_stay_keyword_only(self) -> None:
        """Positional constructor arguments stay rejected — `of` is the positional form."""
        with pytest.raises(TypeError):
            cast(Any, Uint16List4)([1, 2])
        with pytest.raises(TypeError):
            cast(Any, TwoFieldContainer)(Uint8(1), Uint16(2))


class TestDeclaredCapacity:
    """
    Tests for declaring how many elements a shape holds with a typed value.

    A specification may keep its length constants as fixed-width unsigned integers.
    Casting each one at the point it becomes a capacity would mean casting almost all of them.
    So a typed value is accepted, then narrowed to a plain integer as the type is built:

        class Attestations(List[Attestation]):
            LIMIT = MAX_ATTESTATIONS   # already a 64-bit unsigned integer

    Narrowing keeps every count this library computes, compares and reports a plain
    integer, whatever the declaration was written at.

    Six families declare a capacity, in one of two kinds:

        vector, bitvector, fixed byte array   an exact count
        list, bitlist, byte list              an upper bound

    All six narrow a typed count through the same step on the base they share.

    A value that counts nothing is refused where it is written.
    Accepting one would turn it into a wrong count somewhere much further away.
    """

    @pytest.mark.parametrize(
        "declared_type, declared_name, absent_name",
        [
            pytest.param(TypedLengthVector, "LENGTH", "LIMIT", id="vector"),
            pytest.param(TypedLimitList, "LIMIT", "LENGTH", id="list"),
            pytest.param(TypedLengthBitVector, "LENGTH", "LIMIT", id="bitvector"),
            pytest.param(TypedLimitBitList, "LIMIT", "LENGTH", id="bitlist"),
            pytest.param(TypedLengthBytes, "LENGTH", "LIMIT", id="fixed_byte_array"),
            pytest.param(TypedLimitByteList, "LIMIT", "LENGTH", id="byte_list"),
            pytest.param(Uint64, "", "LENGTH", id="basic_type"),
            pytest.param(TwoFieldContainer, "", "LIMIT", id="container"),
        ],
    )
    def test_a_capacity_a_type_does_not_declare_reads_as_none(
        self, declared_type: type[SSZType], declared_name: str, absent_name: str
    ) -> None:
        """Both names answer on every type, so neither has to be asked for conditionally."""
        # No shape declares both kinds of count, and most declare neither.
        # The one it does not declare is the None every type inherits.
        #
        # This is what lets a length check read both names as plain attributes.
        # Asking for a name that might be absent is the expensive spelling.
        # A missing class attribute raises inside the interpreter.
        # A default only hides that raise.
        assert getattr(declared_type, absent_name) is None
        if declared_name:
            assert getattr(declared_type, declared_name) == 4

    @pytest.mark.parametrize(
        "declared_type, capacity_name",
        [
            pytest.param(TypedLengthVector, "LENGTH", id="vector"),
            pytest.param(TypedLimitList, "LIMIT", id="list"),
            pytest.param(TypedLengthBitVector, "LENGTH", id="bitvector"),
            pytest.param(TypedLimitBitList, "LIMIT", id="bitlist"),
            pytest.param(TypedLengthBytes, "LENGTH", id="fixed_byte_array"),
            pytest.param(TypedLimitByteList, "LIMIT", id="byte_list"),
        ],
    )
    def test_every_family_stores_a_typed_capacity_as_a_plain_integer(
        self, declared_type: type[SSZType], capacity_name: str
    ) -> None:
        """All six families that state a capacity narrow a typed one the same way."""
        capacity = getattr(declared_type, capacity_name)
        assert capacity == 4
        # The stored type is the load-bearing half of this test.
        #
        # A comparison against a plain integer cannot stand in for it.
        # This library's unsigned integers refuse such a comparison outright.
        # So a capacity left typed fails the line above with an operand error.
        # An operand error says nothing about which of the two shapes is stored.
        assert type(capacity) is int

    @pytest.mark.parametrize(
        "uint_type",
        [
            pytest.param(Uint8, id="8_bit"),
            pytest.param(Uint16, id="16_bit"),
            pytest.param(Uint32, id="32_bit"),
            pytest.param(Uint64, id="64_bit"),
            pytest.param(Uint128, id="128_bit"),
            pytest.param(Uint256, id="256_bit"),
        ],
    )
    def test_a_capacity_of_any_width_narrows_the_same_way(self, uint_type: type[BaseUint]) -> None:
        """The width a capacity was written at leaves no trace on the stored value."""

        # A spec derives some of its length constants from others.
        # Arithmetic there carries the width of its operands.
        # So the width a capacity arrives at is not something a declaration site chooses.
        class Probe(List[Uint8]):
            LIMIT = uint_type(4)

        assert Probe.LIMIT == 4
        assert type(Probe.LIMIT) is int

    @pytest.mark.parametrize(
        "rejected, rejected_type_name",
        [
            pytest.param(4.0, "float", id="whole_float"),
            pytest.param("4", "str", id="digit_string"),
            pytest.param(Decimal(4), "Decimal", id="decimal"),
            pytest.param(None, "NoneType", id="none"),
            pytest.param(True, "bool", id="host_language_true"),
            pytest.param(False, "bool", id="host_language_false"),
        ],
    )
    def test_a_capacity_of_the_wrong_kind_is_refused_where_it_is_written(
        self, rejected: Any, rejected_type_name: str
    ) -> None:
        """A capacity is checked as the type is built, not when the type is first used."""
        # The message names both the type and the attribute, because at this point both are known.
        #
        # Nothing inside this block builds a value.
        # So reaching the failure needs no use of the type at all.
        with pytest.raises(SSZTypeError) as exception_info:

            class Bad(List[Uint8]):
                LIMIT = rejected

        assert str(exception_info.value) == (
            f"Bad.LIMIT must be a plain integer, got {rejected_type_name}"
        )
        # The class statement raised before it could bind its own name.
        # So no value of that type was ever constructible, in this test or anywhere else.
        assert "Bad" not in locals()

    @pytest.mark.parametrize(
        "base, capacity",
        [
            pytest.param(Vector[Uint8], "LENGTH", id="vector"),
            pytest.param(List[Uint8], "LIMIT", id="list"),
            pytest.param(BitVector, "LENGTH", id="bitvector"),
            pytest.param(BitList, "LIMIT", id="bitlist"),
            pytest.param(ByteVector, "LENGTH", id="bytevector"),
            pytest.param(ByteList, "LIMIT", id="bytelist"),
        ],
    )
    def test_a_capacity_below_zero_is_refused_by_every_shape(
        self, base: type[SSZType], capacity: str
    ) -> None:
        """A count of how much a shape holds has a floor of zero, whatever the shape is."""
        # A capacity of -1 admits no value at all, the empty one included.
        #
        # The type it declares is therefore one no instance can ever satisfy.
        #
        # That is a fact about the declaration, so nothing below builds a value to reach it.
        with pytest.raises(SSZTypeError) as exception_info:
            type("Below", (base,), {capacity: -1})

        assert str(exception_info.value) == (
            f"Below.{capacity} counts what a shape holds, and -1 is not a count"
        )

    def test_a_capacity_below_zero_cannot_split_the_two_constructors(self) -> None:
        """A refused declaration is what keeps a default and an explicit value in step."""
        # A fixed byte array builds its default by repeating the zero byte.
        # Repetition reads a negative count as zero.
        # The width check below it compares against the declared -1 instead:
        #
        #     default   ->  b"\x00" * -1  ->  b""      accepted, as the declared width
        #     explicit  ->  b""           ->  refused, against a width of -1
        #
        # Both hold no bytes, and one is admitted while the other is not.
        with pytest.raises(SSZTypeError):

            class Split(ByteVector):
                LENGTH = -1

    def test_a_fractional_capacity_is_refused(self) -> None:
        """A capacity between two whole numbers has no reading that is safe to guess."""
        with pytest.raises(SSZTypeError) as exception_info:

            class Fractional(List[Uint8]):
                LIMIT = 4.7

        assert str(exception_info.value) == ("Fractional.LIMIT must be a plain integer, got float")

        # A capacity is not a hint.
        # It sets how far a value is padded before it is hashed.
        # So it is part of the Merkle root that implementations must agree on.
        #
        # One-byte elements pack 32 to a 32-byte chunk:
        #
        #     capacity 32  ->  ceil(32 / 32) = 1 chunk
        #     capacity 33  ->  ceil(33 / 32) = 2 chunks  ->  one more level of padding
        #
        # Two capacities either side of that boundary give the same contents two roots.
        # A fraction lands between two whole capacities.
        # Rounding it picks one silently, which is how a typo becomes a root nobody shares.
        class ChunkBelowBoundary(List[Uint8]):
            LIMIT = 32

        class ChunkAboveBoundary(List[Uint8]):
            LIMIT = 33

        payload = [Uint8(1), Uint8(2)]
        assert hash_tree_root(ChunkBelowBoundary(data=payload)) != hash_tree_root(
            ChunkAboveBoundary(data=payload)
        )

    def test_this_librarys_boolean_narrows_while_the_host_languages_is_refused(self) -> None:
        """The two are treated differently, on the rule every integer type here follows."""

        class LibraryBoolean(List[Uint8]):
            LIMIT = Boolean(True)

        assert LibraryBoolean.LIMIT == 1
        assert type(LibraryBoolean.LIMIT) is int

        # Refusing one of these while narrowing the other reads as an inconsistency.
        # It is not one.
        # Every integer type in this library already draws the line in the same place.
        # A capacity drawing it elsewhere is what would be inconsistent:
        assert Uint8(Boolean(True)) == Uint8(1)
        with pytest.raises(SSZTypeError, match=r"^expected int, got bool$"):
            Uint8(True)

    @pytest.mark.parametrize(
        "typed, plain",
        [
            pytest.param(
                TypedLengthVector.of(1, 2, 3, 4),
                PlainLengthVector.of(1, 2, 3, 4),
                id="vector",
            ),
            pytest.param(
                TypedLimitList.of(1, 2, 3),
                PlainLimitList.of(1, 2, 3),
                id="list",
            ),
            pytest.param(
                TypedLengthBitVector.of(True, False, True, True),
                PlainLengthBitVector.of(True, False, True, True),
                id="bitvector",
            ),
            pytest.param(
                TypedLimitBitList.of(True, False, True),
                PlainLimitBitList.of(True, False, True),
                id="bitlist",
            ),
            pytest.param(
                TypedLengthBytes(b"\xde\xad\xbe\xef"),
                PlainLengthBytes(b"\xde\xad\xbe\xef"),
                id="fixed_byte_array",
            ),
            pytest.param(
                TypedLimitByteList.of(0xDE, 0xAD, 0xBE),
                PlainLimitByteList.of(0xDE, 0xAD, 0xBE),
                id="byte_list",
            ),
        ],
    )
    def test_a_typed_capacity_leaves_no_trace_on_what_a_value_encodes_to(
        self, typed: SSZType, plain: SSZType
    ) -> None:
        """How a capacity was written cannot move a single bit of observable output."""
        # Wire bytes and Merkle root are the two things an observer reads.
        # A twin declared with a plain integer is the reference for both.
        #
        # The two values have different types.
        # A direct comparison between them is therefore unavailable.
        # Their outputs are what get compared.
        assert typed.encode_bytes() == plain.encode_bytes()
        assert hash_tree_root(typed) == hash_tree_root(plain)
        # Decoding is a third route the capacity is read on.
        # A value that survives it unchanged has been read correctly on all three.
        assert type(typed).decode_bytes(typed.encode_bytes()) == typed

    @pytest.mark.parametrize(
        "build, message",
        [
            pytest.param(
                lambda: TypedLimitList.of(1, 2, 3, 4, 5),
                "TypedLimitList holds at most 4 elements, got 5",
                id="list_over_capacity",
            ),
            pytest.param(
                lambda: TypedLimitBitList.of(*[True] * 5),
                "TypedLimitBitList holds at most 4 elements, got 5",
                id="bitlist_over_capacity",
            ),
            pytest.param(
                lambda: TypedLimitByteList.of(*[0x01] * 5),
                "TypedLimitByteList holds at most 4 bytes, got 5",
                id="byte_list_over_capacity",
            ),
            pytest.param(
                lambda: TypedLengthVector.of(1, 2, 3),
                "TypedLengthVector holds exactly 4 elements, got 3",
                id="vector_wrong_count",
            ),
            pytest.param(
                lambda: TypedLengthBitVector.of(*[True] * 3),
                "TypedLengthBitVector holds exactly 4 elements, got 3",
                id="bitvector_wrong_count",
            ),
            pytest.param(
                lambda: TypedLengthBytes(b"\xde\xad\xbe"),
                "TypedLengthBytes holds exactly 4 bytes, got 3",
                id="fixed_byte_array_wrong_count",
            ),
        ],
    )
    def test_a_bound_written_as_a_typed_value_still_reports_its_own_number(
        self, build: Callable[[], SSZType], message: str
    ) -> None:
        """A count rule states the narrowed capacity in the failure it raises."""
        # Reaching a message at all is most of the claim.
        # The rule compares a plain element count against the stored capacity.
        # A capacity left typed refuses that comparison rather than answering it:
        #
        #     5 > Uint64(4)  ->  operand error, naming neither the type nor the count
        #
        # The number in each message is the capacity exactly as declared.
        # So nothing was rounded or truncated on the way in.
        # A byte array builds outside pydantic, so it alone still raises the refusal raw.
        with pytest.raises((SSZValueError, ValidationError)) as exception_info:
            build()
        assert message in str(exception_info.value)

    def test_growing_a_value_reads_the_capacity_on_its_own_route(self) -> None:
        """Mutation checks a count against the capacity somewhere other than construction."""
        # Construction checks the count inside the field validator of each family.
        # Growing or reshaping a value checks it on the shared length rule instead.
        # A capacity that only worked at construction would fail here.
        #
        #     held  = [1, 2, 3, 4]   under a capacity of 4
        #     append                 ->  5 elements, one past the capacity
        values = TypedLimitList.of(1, 2, 3, 4)
        over_capacity = r"^TypedLimitList holds at most 4 elements, got 5$"
        with pytest.raises(SSZValueError, match=over_capacity):
            values.append(Uint8(5))

        # Replacing one element with two grows the value the same way:
        #
        #     [1, 2, 3, 4]  ->  [0:1] = [9, 9]  ->  5 elements
        with pytest.raises(SSZValueError, match=over_capacity):
            values[0:1] = [Uint8(9)] * 2
        assert values == TypedLimitList.of(1, 2, 3, 4)

        # A fixed count is enforced on the same route, from the other side:
        #
        #     4 bits  ->  [1:] = [0, 0]  ->  3 bits, one short of the required 4
        bits = TypedLengthBitVector.of(*[True] * 4)
        with pytest.raises(
            SSZValueError, match=r"^TypedLengthBitVector holds exactly 4 elements, got 3$"
        ):
            bits[1:] = [Boolean(False)] * 2
        assert bits == TypedLengthBitVector.of(*[True] * 4)

    def test_a_redeclared_capacity_is_narrowed_again(self) -> None:
        """Every declaration is checked, however deep in a hierarchy it sits."""

        class Wider(TypedLimitList):
            LIMIT = Uint8(8)

        assert Wider.LIMIT == 8
        assert type(Wider.LIMIT) is int

    def test_a_subclass_that_declares_nothing_inherits_a_narrowed_capacity(self) -> None:
        """Inheriting a capacity reaches the value the parent already narrowed."""

        class Unchanged(TypedLimitList):
            pass

        # Nothing of its own to find, which sends the lookup up to the parent.
        # The parent holds a plain integer.
        # That is what every subclass of it therefore reads.
        assert "LIMIT" not in Unchanged.__dict__
        assert Unchanged.LIMIT == 4
        assert type(Unchanged.LIMIT) is int

    def test_an_intermediate_base_that_declares_no_capacity_gains_none(self) -> None:
        """A layer that states no count is left without one, rather than given a default."""

        class Intermediate(List[Uint8]):
            pass

        # An abstract layer binds the element type.
        # It leaves the count for a concrete type below it to state.
        # Inventing a count here would make such a layer instantiable by accident.
        #
        # An undeclared capacity reads as None, which is not a count and is never taken for one.
        # So the layer states nothing, and building a value of it still fails.
        assert "LIMIT" not in Intermediate.__dict__
        assert Intermediate.LIMIT is None
        with pytest.raises(SSZTypeError) as exception_info:
            Intermediate.of(1)
        assert str(exception_info.value) == "Intermediate must declare ELEMENT_TYPE and LIMIT"

        class Concrete(Intermediate):
            LIMIT = Uint64(4)

        assert Concrete.LIMIT == 4
        assert type(Concrete.LIMIT) is int

    def test_a_shape_with_no_capacity_at_all_is_still_usable_inline(self) -> None:
        """The unbounded sequence shape states no count at all, which leaves it untouched."""
        # Written the way the spec writes it, with the element type in brackets.
        # There is no class body here for a capacity to sit in.
        values = ProgressiveList[Uint8].of(1, 2, 3)
        assert list(values) == [Uint8(1), Uint8(2), Uint8(3)]

    def test_a_capacity_assigned_after_the_class_body_is_not_narrowed(self) -> None:
        """A known limitation of where the check sits, recorded rather than relied upon."""

        # Narrowing happens while a class body is being turned into a type.
        # A value assigned onto the type afterwards never passes through that step.
        # It stays exactly as written:
        #
        #     class Late(List[Uint8]):
        #         LIMIT = 4          ->  narrowed, because the class body declared it
        #
        #     Late.LIMIT = Uint64(4) ->  untouched, because nothing declares it here
        #
        # This library never assigns a capacity this way.
        # Closing the gap would mean hooking attribute assignment on two metaclasses.
        # That would guard a mutation the library itself never performs.
        # So this is a limitation of where the check sits, not a behaviour to depend on.
        class Late(List[Uint8]):
            LIMIT = 4

        Late.LIMIT = Uint64(4)
        assert type(Late.LIMIT) is Uint64

        # The mis-set capacity then goes unremarked.
        # The internal comparison it feeds is a uint against the plain int len returns.
        # Those two types are related by inheritance, so the comparison answers correctly:
        #
        #     len(data) > Uint64(4)  ->  2 > 4  ->  False
        #
        # So the value behaves as the capacity it names, and the limit is still enforced.
        assert list(Late.of(1, 2)) == [Uint8(1), Uint8(2)]
        with pytest.raises(ValidationError) as exception_info:
            Late.of(1, 2, 3, 4, 5)
        assert "Late holds at most 4 elements, got 5" in str(exception_info.value)

    def test_an_exact_count_never_declared_is_reported_where_it_is_read(self) -> None:
        """An absent count is a definition error, not arithmetic against None."""

        class NoLength(ByteVector):
            pass

        with pytest.raises(SSZTypeError) as exception_info:
            NoLength.declared_length()
        assert str(exception_info.value) == "NoLength must declare LENGTH"

        # A fixed byte array's width is its count, so callers of the width land here too.
        with pytest.raises(SSZTypeError):
            NoLength.get_byte_length()

    def test_an_upper_bound_never_declared_is_reported_where_it_is_read(self) -> None:
        """An absent bound reads the same way, through the callers that size a tree from it."""

        class NoLimit(List[Uint16]):
            pass

        with pytest.raises(SSZTypeError) as exception_info:
            NoLimit.declared_limit()
        assert str(exception_info.value) == "NoLimit must declare LIMIT"

        # A proof sizes the tree from the bound, and reaches the same report.
        with pytest.raises(SSZTypeError):
            chunk_count(NoLimit)


class TestFixedSize:
    """
    Tests that one stated width answers every question asked about a shape's size.

    A shape states its width in one place, and both spellings that ask for it read that
    one answer. So a shape reporting a width can always give it, and one reporting none
    refuses every caller alike.

    A refusal names the shape, because the type's own name does not say which rule
    refused: a container is named for what it holds, and a vector loses its width only
    through its elements.
    """

    @pytest.mark.parametrize(
        "declared_type, width",
        [
            pytest.param(Uint64, 8, id="uint"),
            pytest.param(Boolean, 1, id="boolean"),
            pytest.param(TypedLengthBytes, 4, id="fixed_byte_array"),
            pytest.param(SmallBitVector, 1, id="bitvector"),
            pytest.param(Uint16Vector2, 4, id="vector"),
            pytest.param(TwoFieldContainer, 3, id="container"),
        ],
    )
    def test_a_shape_with_a_width_answers_both_spellings_with_it(
        self, declared_type: type[SSZType], width: int
    ) -> None:
        """The stated width settles both questions, so neither can drift from it."""
        assert declared_type.fixed_size() == width
        assert declared_type.is_fixed_size() is True
        assert declared_type.get_byte_length() == width

    @pytest.mark.parametrize(
        "declared_type, kind",
        [
            pytest.param(Uint16List4, "list", id="list"),
            pytest.param(Uint16ProgressiveList, "list", id="progressive_list"),
            pytest.param(Uint16ListVector2, "vector", id="vector"),
            pytest.param(SmallBitList, "bitlist", id="bitlist"),
            pytest.param(SmallByteList, "byte list", id="byte_list"),
            pytest.param(ThreeFieldContainer, "container", id="container"),
            pytest.param(SmallUnion, "compatible union", id="compatible_union"),
        ],
    )
    def test_a_shape_without_a_width_names_itself_where_one_is_demanded(
        self, declared_type: type[SSZType], kind: str
    ) -> None:
        """Every family that can lack a width names itself, none falling back on the bare word."""
        assert declared_type.fixed_size() is None
        assert declared_type.is_fixed_size() is False
        with pytest.raises(SSZTypeError) as exception_info:
            declared_type.get_byte_length()
        assert str(exception_info.value) == (
            f"{declared_type.__name__} is a variable-size {kind}, and has no one byte length"
        )


class TestFinalHashTreeRoot:
    """
    Tests that no type may declare a hash_tree_root of its own.

    Every value here reaches its root by one route.
    Two callers inside this library take the free function to get there.

    - A layout roots each of its nested leaves with it.
    - A proof roots a single addressed node with it.

    A subclass declaring a root of its own would therefore give one value two roots.

    - The method spelling would answer with the declaration.
    - Every recursion through the free function would answer with the spec's own tree.
    - Neither reports the other, so a wrong root leaves the library looking self-consistent.

    Both halves of the guard are checked here.

    - The declaration is refused as the class is created, so no such value is constructible.
    - The method is marked final, so a type checker refuses the same declaration statically.
    """

    def test_the_method_is_marked_final(self) -> None:
        """The static half of the guard, stated where the runtime half is."""
        # typing.final records itself on the function it decorates.
        # The runtime check below cannot stand in for it.
        # A type checker reads the decorator, and reads nothing at all from __init_subclass__.
        assert getattr(SSZType.hash_tree_root, "__final__", False) is True

    def test_a_uint_subclass_declaring_its_own_root_method_is_refused(self) -> None:
        """A basic type's subclass is refused at the class statement."""
        with pytest.raises(SSZTypeError) as exception_info:

            class BadUint(Uint16):
                def hash_tree_root(self) -> Root:  # ty: ignore[override-of-final-method]
                    return ZERO_ROOT

        assert str(exception_info.value) == "BadUint declares a hash_tree_root of its own"

    def test_a_byte_array_subclass_declaring_its_own_root_method_is_refused(self) -> None:
        """The bytes-backed families reach the guard through the same hook."""
        with pytest.raises(SSZTypeError) as exception_info:

            class BadRoot(Root):
                def hash_tree_root(self) -> Root:  # ty: ignore[override-of-final-method]
                    return ZERO_ROOT

        assert str(exception_info.value) == "BadRoot declares a hash_tree_root of its own"

    @pytest.mark.parametrize(
        "base",
        [
            pytest.param(Uint16List4, id="list"),
            pytest.param(Uint16Vector2, id="vector"),
            pytest.param(Uint16ProgressiveList, id="progressive_list"),
            pytest.param(SmallBitList, id="bitlist"),
            pytest.param(SmallByteList, id="byte_list"),
            pytest.param(TwoFieldContainer, id="container"),
            pytest.param(SmallUnion, id="compatible_union"),
        ],
    )
    def test_a_model_backed_subclass_declaring_its_own_root_method_is_refused(
        self, base: type[SSZType]
    ) -> None:
        """
        Every Pydantic-backed family is refused too, and by the same hook.

        Pydantic builds these types through a metaclass of its own. The guard sits on
        __init_subclass__, which that metaclass still runs, so one check covers both
        construction paths rather than one per family.
        """
        # Built through the family's own metaclass.
        # Pydantic's class machinery runs exactly as a class statement would run it.
        with pytest.raises(SSZTypeError) as exception_info:
            type(base)("Bad", (base,), {"hash_tree_root": lambda self: ZERO_ROOT})

        assert str(exception_info.value) == "Bad declares a hash_tree_root of its own"

    def test_a_subclass_that_declares_no_root_method_is_accepted(self) -> None:
        """
        The guard fires on that one name and on nothing else, so subclassing still works.

        This library subclasses its own byte arrays twice over: a root is a chunk, and a
        chunk is a fixed byte array. A guard keyed on anything wider than the name would
        have made those two declarations impossible.
        """
        assert issubclass(Root, ByteVector)

        class Fingerprint(Root):
            """A named root, as an application declares one."""

            def is_all_ones(self) -> bool:
                """A method of its own, which the guard has no business refusing."""
                return all(byte == 0xFF for byte in self)

        payload = b"\xab" * 32
        assert Fingerprint(payload).is_all_ones() is False
        # The inherited method is the one that answers.
        # It answers as the free function does for the base type.
        # A 32-byte array is one chunk, so it roots to its own bytes.
        assert Fingerprint(payload).hash_tree_root() == hash_tree_root(Root(payload))
        assert Fingerprint(payload).hash_tree_root() == Root(payload)

    def test_a_root_method_assigned_after_the_class_body_is_not_refused(self) -> None:
        """A known limitation of where the check sits, recorded rather than relied upon."""

        # The guard runs while a class body is being turned into a type.
        # A method assigned onto the type afterwards never passes through that step:
        #
        #     class Late(Boolean):
        #         def hash_tree_root(self): ...   ->  refused, the class body declared it
        #
        #     Late.hash_tree_root = something     ->  untouched, nothing declares it here
        #
        # This library never assigns a method this way.
        # A type checker already refuses the assignment because the method it replaces is final.
        # Closing the gap at runtime would mean hooking assignment on two metaclasses.
        # So this is a limitation of where the check sits, not a behaviour to depend on.
        class Late(Boolean):
            """A subclass that declares nothing, and so passes the guard."""

        assert Late(True).hash_tree_root() == hash_tree_root(Boolean(True))

        cast(Any, Late).hash_tree_root = lambda self: ZERO_ROOT
        # Two roots for one value, which is exactly what the guard exists to prevent.
        assert Late(True).hash_tree_root() == ZERO_ROOT
        assert hash_tree_root(Late(True)) != ZERO_ROOT

    def test_a_root_method_reached_through_a_plain_mixin_is_refused(self) -> None:
        """A root inherited from outside this type system is refused as well."""

        # A base outside this type system never appears in the class body being created.
        # It wins the lookup because it precedes the SSZ base in attribute order:
        #
        #     class Fast(Mixin, Pair)   ->  Fast.hash_tree_root is Mixin's, not the base's
        #
        # A type checker does not flag it either, because nothing is declared here.
        # So the resolved attribute is what gets compared, rather than the class body.
        class CachedRoot:
            """A plain class outside this type system, carrying a root of its own."""

            def hash_tree_root(self) -> Root:
                """Answer with a fixed root, standing in for a cache that went stale."""
                return ZERO_ROOT

        with pytest.raises(SSZTypeError) as exception_info:

            class Fast(CachedRoot, TwoFieldContainer):
                """A container that would let the mixin answer for its root."""

        assert str(exception_info.value) == "Fast declares a hash_tree_root of its own"

    def test_a_field_named_for_the_root_method_is_refused(self) -> None:
        """A field of that name is refused, because it shadows the method on every instance."""

        # A field is declared as an annotation, and leaves nothing on the class itself.
        # The resolved attribute therefore still looks untouched.
        # Every instance answers with the field:
        #
        #     Odd(hash_tree_root=7).hash_tree_root    ->  the field, 7
        #     Odd(hash_tree_root=7).hash_tree_root()  ->  not callable
        #
        # A container also hashes itself by its own root.
        # The shadowed name would break hashing rather than merely occupy it.
        with pytest.raises(SSZTypeError) as exception_info:

            class Odd(Container):
                """A container claiming the one field name the root method needs."""

                hash_tree_root: Uint16  # ty: ignore[override-of-final-method]

        assert str(exception_info.value) == "Odd declares a hash_tree_root of its own"
