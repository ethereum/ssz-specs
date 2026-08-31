"""Unit tests for the README: every Python block on the page has to run."""

from __future__ import annotations

import pathlib
import re

README = pathlib.Path(__file__).parents[1] / "README.md"

# Every fenced Python block, in the order a reader meets them.
BLOCKS = re.findall(r"^```python\n(.*?)^```", README.read_text(), re.DOTALL | re.MULTILINE)


def test_the_page_has_python_blocks() -> None:
    """An extraction that matches nothing would pass every other test in this file."""
    assert BLOCKS


def test_the_opening_block_serializes_reads_back_and_roots() -> None:
    """
    A reader arriving at an SSZ implementation comes for the wire format and the root.

    Neither appeared anywhere on the page, so the block above the fold is where they are pinned.
    """
    opening = BLOCKS[0]
    for name in ("encode_bytes", "decode_bytes", "hash_tree_root"):
        assert name in opening, name


def test_every_block_runs_in_the_order_it_appears() -> None:
    """
    A snippet that does not run is worse than none, since a reader takes it for working code.

    The blocks share one namespace, so a later one may use a name an earlier one bound.
    The compiled filename names the block a failure came from.
    """
    namespace: dict[str, object] = {}
    for number, block in enumerate(BLOCKS, start=1):
        # Compiling inherits this module's future statements unless told not to, and the
        # postponed annotations one would leave every declared field a ForwardRef.
        code = compile(block, f"{README.name} block {number}", "exec", dont_inherit=True)
        exec(code, namespace)
