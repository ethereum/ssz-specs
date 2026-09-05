"""The offset table a variable-size sequence or struct puts in front of its bodies."""

from collections.abc import Sequence
from itertools import pairwise
from typing import Final

from ssz.exceptions import SSZValueError, ValueFault

BYTES_PER_LENGTH_OFFSET: Final = 4
"""Width of an SSZ offset prefixing each variable-size element, a little-endian uint32."""


_COMPOSITE_SIZE_LIMIT: Final = 1 << (8 * BYTES_PER_LENGTH_OFFSET)
"""Exclusive size ceiling for composite encodings, including their final body."""


def check_composite_size(size: int) -> None:
    """Require the whole composite encoding to fit the four-byte offset range."""
    # The SSZ serialization rule bounds all fixed parts and variable bodies together.
    # https://ethereum.github.io/consensus-specs/ssz/simple-serialize/#serialization
    if size >= _COMPOSITE_SIZE_LIMIT:
        raise SSZValueError(ValueFault.OFFSET_OVERFLOW, size=size)


def offset_table_spans(offsets: Sequence[int], scope: int, steps: Sequence[str | int]) -> list[int]:
    """
    Check a whole offset table closes over its budget, and return the width of each body.

    Appending the budget gives one boundary more than there are bodies.
    Consecutive pairs are then exactly the spans to read:

        offsets       12       17       20
        boundaries    12       17       20       27
        spans         12..17   17..20   20..27

    The whole table is settled before a caller reads one byte of a body.
    A corrupt one is therefore refused as a table, not as whatever a bad span made of it.

    Raises:
        SSZValueError: An offset above the one after it, or a last one past the budget.
    """
    boundaries = [*offsets, scope]

    # The last pair is the only one closed by the budget rather than an offset.
    last = len(offsets) - 1

    spans: list[int] = []
    for index, ((start, end), step) in enumerate(zip(pairwise(boundaries), steps, strict=True)):
        if end < start:
            if index == last:
                error = SSZValueError(ValueFault.OFFSET_PAST_SCOPE, offset=start, scope=end)
            else:
                error = SSZValueError(ValueFault.OFFSET_UNORDERED, offset=start, next=end)
            error.at(step)
            raise error
        spans.append(end - start)
    return spans
