"""The offset table a variable-size sequence or struct puts in front of its bodies."""

from collections.abc import Sequence
from itertools import pairwise
from typing import Final

from ssz.exceptions import SSZValueError, ValueFault

BYTES_PER_LENGTH_OFFSET: Final = 4
"""Width of an SSZ offset prefixing each variable-size element, a little-endian uint32."""


def offset_table_spans(offsets: Sequence[int], scope: int, steps: Sequence[str | int]) -> list[int]:
    """
    Check a whole offset table closes over its budget, and return the width of each body.

    Appending the budget gives one boundary more than there are bodies.
    Consecutive pairs are then exactly the spans to read:

        offsets       12       17       20
        boundaries    12       17       20       27
        spans         12..17   17..20   20..27

    A pair that decreases is a body of negative width.
    The pair closed by the budget is a body reaching past the input.

    The whole table is settled here before a caller reads one byte of a body.
    So a corrupt table is refused as one, not as whatever a body made of a bad span.

    Args:
        offsets: Where each body starts, in wire order.
        scope: Byte budget the payload spans, which closes the last body.
        steps: What to name each body on the path of a refusal, in the same order.

    Returns:
        The width of each body, in wire order.

    Raises:
        SSZValueError: When an offset is above the one after it.
        SSZValueError: When the last offset runs past the budget.
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
