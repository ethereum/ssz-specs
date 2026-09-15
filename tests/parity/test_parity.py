"""Running a generated corpus past the Lean checker."""

import json
import subprocess
from pathlib import Path

import pytest
from hypothesis import HealthCheck, given, settings, strategies as st

from parity.corpus import Corpus
from parity.draw import Draw

LEAN_BINARY = Path(__file__).resolve().parents[2] / "lean/.lake/build/bin/conformance"
"""Where the Lean checker is built, which is also where the just recipe puts it."""

BATCH_CASES = 120
"""Cases in one seeded batch, sized so a batch is one quick crossing of the boundary."""

BATCH_PAIRS = 60
"""Type pairs in one seeded batch."""

pytestmark = pytest.mark.skipif(
    not LEAN_BINARY.exists(), reason=f"the Lean checker is not built at {LEAN_BINARY}"
)


def check(corpus: Corpus, tmp_path: Path) -> None:
    """Hand a corpus to the Lean checker, and fail with whatever it disagreed on."""
    target = tmp_path / "corpus.json"
    target.write_text(json.dumps(corpus.to_json()))
    finished = subprocess.run(
        [str(LEAN_BINARY), "--diff", str(target)], capture_output=True, text=True, timeout=300
    )
    assert finished.returncode == 0, f"{finished.stdout}\n{finished.stderr}"


@pytest.mark.parametrize("seed", range(8))
def test_lean_agrees_on_generated_types(seed: int, tmp_path: Path) -> None:
    # A batch of independent cases, checked in one crossing of the language boundary.
    draw = Draw.seeded(seed)
    check(Corpus.drawn(draw, f"seed{seed}", cases=BATCH_CASES, pairs=BATCH_PAIRS), tmp_path)


@settings(
    max_examples=40, deadline=None, suppress_health_check=[HealthCheck.function_scoped_fixture]
)
@given(data=st.data())
def test_lean_agrees_under_search(data: st.DataObject, tmp_path: Path) -> None:
    # The same checks, with the search picking the shape and shrinking any disagreement.
    draw = Draw.searched(data)
    check(Corpus.drawn(draw, "searched", cases=1, pairs=1), tmp_path)
