"""SSZ conformance test vectors for the tagged union `Union[type_0, type_1, ...]`."""

from typing import Final

from ssz import (
    Container,
    List,
    ProgressiveList,
    Uint8,
    Uint16,
    Uint32,
    Uint64,
    Union,
)
from ssz_testing import (
    DeclaredOption,
    ExpectedRejection,
    SSZTestFiller,
    TypeDescriptor,
    TypeFault,
    TypeRejectionFiller,
    ValueFault,
    describe_type,
)

UINT8: Final = describe_type(Uint8)
"""A byte-wide integer, read off the real class, standing in as the option of an illegal union."""


class TaggedPoint(Container):
    """A composite option, so the payload behind the selector is a struct rather than a scalar."""

    x: Uint16
    y: Uint16


class TaggedUint16List4(List[Uint16]):
    """Bounded list of two-byte elements, a variable-size option."""

    LIMIT = 4


class TaggedMaybe(Union):
    """
    The specification's own example shape: None first, then two integer widths.

    Selector zero holds nothing and encodes to the single byte 0x00, which is the one SSZ
    encoding that does not follow from the general rules for the shapes around it.
    """

    OPTIONS = (None, Uint64, Uint32)


class TaggedNumbers(Union):
    """Union whose options are a variable-size list and a fixed-size struct."""

    OPTIONS = (TaggedUint16List4, TaggedPoint)


class TaggedWidths(Union):
    """Two options of one fixed width, which leaves the selector as the only difference."""

    OPTIONS = (Uint32, Uint32)


class TaggedNested(Union):
    """Union whose second option is itself a union."""

    OPTIONS = (Uint8, TaggedMaybe)


class TaggedHolder(Container):
    """Ordinary container reaching a union through an offset."""

    tag: Uint8
    body: TaggedMaybe


class TaggedWidthsHolder(Container):
    """Container over the union whose options share one width, where the offset still appears."""

    tag: Uint8
    body: TaggedWidths


class TaggedMaybeList(ProgressiveList[TaggedMaybe]):
    """Progressive list of unions, whose variable-size bodies need an offset table."""


def test_union_none_option(ssz_test: SSZTestFiller) -> None:
    """
    A union holding its None option round-trips unchanged.

    Given
    -----
    - a union whose first option is None.
    - a value holding that option.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the single byte 0x00, with nothing behind the selector.
    - the root is the all-zero chunk with selector zero mixed in beside it.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union/none_option",
        type_name="TaggedMaybe",
        value=TaggedMaybe(selector=Uint8(0), data=None),
    )


def test_union_first_declared_option(ssz_test: SSZTestFiller) -> None:
    """
    A union holding the option under selector 1 round-trips unchanged.

    Given
    -----
    - the same union, whose selector 1 names an eight-byte integer.
    - a value holding that option.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the selector byte is followed directly by the option's own eight bytes.
    - the root is the option's root with selector 1 mixed in.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union/first_declared_option",
        type_name="TaggedMaybe",
        value=TaggedMaybe(selector=Uint8(1), data=Uint64(0x1234567890ABCDEF)),
    )


def test_union_second_declared_option(ssz_test: SSZTestFiller) -> None:
    """
    A union holding the option under selector 2 round-trips unchanged.

    Given
    -----
    - the same union, whose selector 2 names a four-byte integer.
    - a value holding that option.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the payload is four bytes where the previous option's was eight.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union/second_declared_option",
        type_name="TaggedMaybe",
        value=TaggedMaybe(selector=Uint8(2), data=Uint32(0x1234ABCD)),
    )


def test_union_composite_option(ssz_test: SSZTestFiller) -> None:
    """
    A union holding a struct round-trips unchanged.

    Given
    -----
    - a union whose selector 1 names a container of two two-byte fields.
    - a value holding that option.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the struct's own encoding follows the selector byte with no offset between them.
    - the union roots to the struct's root with the selector mixed in.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union/composite_option",
        type_name="TaggedNumbers",
        value=TaggedNumbers(selector=Uint8(1), data=TaggedPoint(x=Uint16(3), y=Uint16(4))),
    )


def test_union_variable_size_option(ssz_test: SSZTestFiller) -> None:
    """
    A union holding a variable-size option round-trips unchanged.

    Given
    -----
    - the same union, whose selector 0 names a bounded list of two-byte elements.
    - a value holding two elements.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the list body follows the selector directly, with no offset between them.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union/variable_size_option",
        type_name="TaggedNumbers",
        value=TaggedNumbers(selector=Uint8(0), data=TaggedUint16List4(data=[Uint16(1), Uint16(2)])),
    )


def test_union_empty_variable_size_option(ssz_test: SSZTestFiller) -> None:
    """
    A union holding an empty variable-size option round-trips unchanged.

    Given
    -----
    - the same union, holding a list with no elements.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is the selector byte alone, as the None option's is.
    - the two are still different values: the selector differs, and so does the root.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union/empty_variable_size_option",
        type_name="TaggedNumbers",
        value=TaggedNumbers(selector=Uint8(0), data=TaggedUint16List4(data=[])),
    )


def test_union_equal_fixed_width_options_first(ssz_test: SSZTestFiller) -> None:
    """
    A union whose options share one fixed width round-trips unchanged.

    Given
    -----
    - a union declaring the same four-byte integer under selectors 0 and 1.
    - a value holding it under selector 0.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the encoding is five bytes, one for the selector and four for the payload.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union/equal_fixed_width_options/first",
        type_name="TaggedWidths",
        value=TaggedWidths(selector=Uint8(0), data=Uint32(9)),
    )


def test_union_equal_fixed_width_options_second(ssz_test: SSZTestFiller) -> None:
    """
    The same payload under the other selector round-trips unchanged and roots differently.

    Given
    -----
    - the same union, holding the same number under selector 1.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the payload bytes are identical to the first case's.
    - the root differs, because the mixed-in selector is all that separates the two.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union/equal_fixed_width_options/second",
        type_name="TaggedWidths",
        value=TaggedWidths(selector=Uint8(1), data=Uint32(9)),
    )


def test_container_holding_a_union_of_equal_fixed_width_options(ssz_test: SSZTestFiller) -> None:
    """
    A container holding that union writes an offset for it all the same.

    Given
    -----
    - a container with a one-byte tag and a field of the union whose options are all four
      bytes wide.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the container writes a four-byte offset for the union field, so the whole encoding
      is ten bytes rather than the six a fixed-size field would take.
    - a union is a variable-size type even when every option has one fixed length, which
      is what this offset shows on the wire.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union/equal_fixed_width_options/in_container",
        type_name="TaggedWidthsHolder",
        value=TaggedWidthsHolder(
            tag=Uint8(0xFF), body=TaggedWidths(selector=Uint8(1), data=Uint32(9))
        ),
    )


def test_container_holding_a_union(ssz_test: SSZTestFiller) -> None:
    """
    An ordinary container holding a union round-trips unchanged.

    Given
    -----
    - a container with a one-byte tag and a union field.
    - a union value holding the None option, whose whole encoding is one byte.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - one offset follows the fixed part, pointing at the single selector byte.
    - the union contributes its selector-mixed root as an ordinary leaf.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union/in_container",
        type_name="TaggedHolder",
        value=TaggedHolder(tag=Uint8(0xFF), body=TaggedMaybe(selector=Uint8(0), data=None)),
    )


def test_progressive_list_of_unions(ssz_test: SSZTestFiller) -> None:
    """
    A progressive list of unions round-trips unchanged.

    Given
    -----
    - a progressive list whose elements are unions.
    - two elements, the first holding None and the second an eight-byte integer.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - the elements are variable-size, so an offset table precedes the bodies.
    - the two bodies are one byte and nine bytes, so the offsets are not evenly spaced.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union/in_progressive_list",
        type_name="TaggedMaybeList",
        value=TaggedMaybeList(
            data=[
                TaggedMaybe(selector=Uint8(0), data=None),
                TaggedMaybe(selector=Uint8(1), data=Uint64(7)),
            ]
        ),
    )


def test_union_holding_a_union(ssz_test: SSZTestFiller) -> None:
    """
    A union whose option is itself a union round-trips unchanged.

    Given
    -----
    - an outer union whose selector 1 names the union above.
    - a value holding the inner union, which in turn holds its second option.

    When
    ----
    - the value is encoded and then decoded.

    Then
    ----
    - two selector bytes lead, one per level, before any payload byte.
    - each level mixes its own selector into the root of the level below it.
    - the decoded value equals the original.
    """
    ssz_test(
        case_id="union/union_option",
        type_name="TaggedNested",
        value=TaggedNested(
            selector=Uint8(1), data=TaggedMaybe(selector=Uint8(2), data=Uint32(0x1234ABCD))
        ),
    )


def test_union_decode_failure_empty_input(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union from an empty input is rejected.

    Given
    -----
    - a union whose every encoding opens with a selector byte.
    - an input of zero bytes.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the budget holds no selector at all.
    """
    ssz_test(
        case_id="union/invalid/empty_input",
        type_name="TaggedMaybe",
        value=TaggedMaybe(selector=Uint8(0), data=None),
        raw_bytes="0x",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.NO_SELECTOR,
            exact_message="a budget of 0 holds no selector",
        ),
    )


def test_union_decode_failure_selector_past_the_options(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union whose selector indexes past the declared options is rejected.

    Given
    -----
    - a union declaring three options, so selectors 0 through 2.
    - the input bytes 0x0307, whose selector is the first one past the list.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected before any payload byte is read.
    - the reason is that the selector names no option of this union.
    - an implementation reading the selector modulo the option count would accept this.
    """
    ssz_test(
        case_id="union/invalid/selector_past_the_options",
        type_name="TaggedMaybe",
        value=TaggedMaybe(selector=Uint8(0), data=None),
        raw_bytes="0x0307",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.UNKNOWN_SELECTOR,
            exact_message="selector 3 names no option of TaggedMaybe",
        ),
    )


def test_union_decode_failure_reserved_high_bit_selector(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union whose selector sets the reserved high bit is rejected.

    Given
    -----
    - the same union, and the input bytes 0x8007.
    - selectors above 127 are reserved for backwards compatible extensions.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is the same one an undeclared low selector gives: it names no option.
    - an implementation reading the selector as a signed byte would see -128 here.
    """
    ssz_test(
        case_id="union/invalid/reserved_high_bit_selector",
        type_name="TaggedMaybe",
        value=TaggedMaybe(selector=Uint8(0), data=None),
        raw_bytes="0x8007",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.UNKNOWN_SELECTOR,
            exact_message="selector 128 names no option of TaggedMaybe",
        ),
    )


def test_union_decode_failure_truncated_payload(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union whose payload is cut short is rejected.

    Given
    -----
    - a union whose selector 1 names an eight-byte integer.
    - the input bytes 0x0107, which leave that integer seven bytes short.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason surfaces from the option itself, the rest of the budget being its own.
    - the selector the payload was read under leads the message as a path step.
    """
    ssz_test(
        case_id="union/invalid/truncated_payload",
        type_name="TaggedMaybe",
        value=TaggedMaybe(selector=Uint8(0), data=None),
        raw_bytes="0x0107",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="[1]: Uint64 spans 8 bytes, and the budget is 1",
        ),
    )


def test_union_decode_failure_trailing_byte(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a union with a spare byte after the payload is rejected.

    Given
    -----
    - a union whose selector 2 names a four-byte integer.
    - the input bytes 0x020900000000, one byte longer than the canonical encoding.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that a canonical encoding maps to exactly one value.
    - the rest of the budget belongs to the option, so the option reports the surplus.
    """
    ssz_test(
        case_id="union/invalid/trailing_byte",
        type_name="TaggedMaybe",
        value=TaggedMaybe(selector=Uint8(0), data=None),
        raw_bytes="0x020900000000",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="[2]: Uint32 spans 4 bytes, and the budget is 5",
        ),
    )


def test_union_decode_failure_none_option_carrying_a_payload(ssz_test: SSZTestFiller) -> None:
    """
    Decoding a None option with bytes behind its selector is rejected.

    Given
    -----
    - a union whose first option is None, and whose encoding is therefore one byte.
    - the input bytes 0x0007, which put a byte behind that selector.

    When
    ----
    - the input is decoded into that type.

    Then
    ----
    - decoding is rejected.
    - the reason is that the None option spans the selector byte and nothing more.
    - an implementation that ignores the rest of the scope after selector zero would
      accept this, and would accept a different byte there as the same value.
    """
    ssz_test(
        case_id="union/invalid/none_option_with_a_payload",
        type_name="TaggedMaybe",
        value=TaggedMaybe(selector=Uint8(0), data=None),
        raw_bytes="0x0007",
        expected_rejection=ExpectedRejection(
            reason=ValueFault.SCOPE,
            exact_message="TaggedMaybe spans 1 bytes, and the budget is 2",
        ),
    )


def test_a_union_declaring_no_option_is_refused(ssz_type_rejection: TypeRejectionFiller) -> None:
    """
    Declaring a union that offers nothing is refused.

    Given
    -----
    - a union whose option list is empty.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, a union having at least one type option.
    - no selector byte could name an option, so the type admits no value.
    """
    ssz_type_rejection(
        case_id="union/illegal/no_options",
        type_name="IllegalOptionlessTaggedUnion",
        type_descriptor=TypeDescriptor(kind="Union", options=()),
        rejection_reason=TypeFault.UNION_EMPTY,
        exact_message="a union declares at least one option",
    )


def test_a_union_of_none_alone_is_refused(ssz_type_rejection: TypeRejectionFiller) -> None:
    """
    Declaring a union whose only option is None is refused.

    Given
    -----
    - a union declaring one option, and that option is None.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, a union opening on None having at least two type options.
    - the type would otherwise admit exactly one value, encoding to one byte that names
      nothing and carries nothing.
    """
    ssz_type_rejection(
        case_id="union/illegal/none_alone",
        type_name="IllegalEmptyTaggedUnion",
        type_descriptor=TypeDescriptor(kind="Union", options=(DeclaredOption(selector=0),)),
        rejection_reason=TypeFault.UNION_NONE_ALONE,
        exact_message="a union whose first option is None declares at least two options",
    )


def test_a_union_with_none_after_the_first_option_is_refused(
    ssz_type_rejection: TypeRejectionFiller,
) -> None:
    """
    Declaring a union whose None option is not the first is refused.

    Given
    -----
    - a union declaring a byte-wide integer under selector 0 and None under selector 1.

    When
    ----
    - the declaration is built.

    Then
    ----
    - it is refused, None being legal only as the option with index zero.
    - selector zero is the one an all-zero encoding carries, which is the selector the
      absence of a value is reserved to.
    """
    ssz_type_rejection(
        case_id="union/illegal/none_after_the_first_option",
        type_name="IllegalLateNoneTaggedUnion",
        type_descriptor=TypeDescriptor(
            kind="Union",
            options=(DeclaredOption(selector=0, type=UINT8), DeclaredOption(selector=1)),
        ),
        rejection_reason=TypeFault.UNION_NONE_NOT_FIRST,
        exact_message="option 1 is None, which is legal only as the first option",
    )
