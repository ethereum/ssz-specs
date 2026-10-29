"""The actual Lean benchmark must fail instead of timing refused work."""

import shutil
import subprocess
from pathlib import Path

import pytest

LEAN = Path(__file__).resolve().parents[2] / "lean"


@pytest.fixture(scope="module")
def benchmark() -> Path:
    """Build once in Lean jobs; Python-only jobs have no checker to run."""
    if not any(
        (LEAN / ".lake/build/bin" / name).is_file() for name in ("conformance", "conformance.exe")
    ):
        pytest.skip("the Lean checker is not built (Python-only job)")
    if not (LEAN / "native/bindings.c").is_file():
        pytest.skip("this checkout has no native benchmark implementation")
    assert shutil.which("lake"), "a built native Lean checkout requires lake on PATH"
    built = subprocess.run(
        ["lake", "build", "bench"], cwd=LEAN, capture_output=True, text=True, timeout=300
    )
    assert built.returncode == 0, f"{built.stdout}\n{built.stderr}"
    return LEAN


def evaluate(benchmark: Path, tmp_path: Path, body: str) -> subprocess.CompletedProcess[str]:
    """Import Bench itself; never copy its definitions into the control."""
    probe = tmp_path / "BenchmarkControl.lean"
    probe.write_text(f"import Bench\nopen Ssz Ssz.Native\n\n#eval ({body} : IO Unit)\n")
    return subprocess.run(
        ["lake", "env", "lean", str(probe)],
        cwd=benchmark,
        capture_output=True,
        text=True,
        timeout=60,
    )


@pytest.mark.parametrize(
    ("body", "diagnostic"),
    [
        (
            'do let _ ← checkedRoot "root-refusal" (.error "synthetic refusal"); pure ()',
            "root-refusal: synthetic refusal",
        ),
        (
            'do let _ ← checkedRoot "root-width" (.ok ByteArray.empty); pure ()',
            "root-width: expected a 32-byte result, got 0",
        ),
        (
            'do time "work-refusal" (← IO.mkRef ByteArray.empty) (fun _ => .error "refused work")',
            "work-refusal: refused work",
        ),
        (
            'do time "work-width" (← IO.mkRef ByteArray.empty) (fun _ => .ok ByteArray.empty)',
            "work-width: expected a 32-byte result, got 0",
        ),
        (
            'do time "verification" (← IO.mkRef ByteArray.empty) '
            "(fun _ => verificationResult (.ok false))",
            "verification: branch verification returned false",
        ),
        (
            "do let bytes : ByteArray := ⟨#[2]⟩; "
            'time "malformed-bool" (← IO.mkRef bytes) (rooted .bool)',
            "malformed-bool: Ssz.Err.notABit 2",
        ),
    ],
    ids=["refused-root", "short-root", "refused-work", "short-work", "false-proof", "bad-bool"],
)
def test_failed_benchmark_exits_without_timings(
    benchmark: Path, tmp_path: Path, body: str, diagnostic: str
) -> None:
    finished = evaluate(benchmark, tmp_path, body)
    output = f"{finished.stdout}\n{finished.stderr}"
    assert finished.returncode != 0, output
    assert diagnostic in output, output
    assert "median" not in output, output


def test_successful_benchmark_emits_timings(benchmark: Path, tmp_path: Path) -> None:
    finished = evaluate(
        benchmark,
        tmp_path,
        'do let _ ← checkedRoot "verification" (verificationResult (.ok true)); '
        'time "accepted-work" (← IO.mkRef ByteArray.empty) '
        "(fun _ => .ok ⟨Array.replicate 32 0⟩)",
    )
    output = f"{finished.stdout}\n{finished.stderr}"
    assert finished.returncode == 0, output
    assert "accepted-work: median" in output, output
    assert "p10" in output and "p90" in output, output
