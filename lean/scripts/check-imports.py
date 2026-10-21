"""
Check that every module is reachable from its audited proof root.

Also check that no implementation module imports a proof.
"""

import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parents[1]

# Each tree: its implementation root, and the proof root that imports it and runs the axiom audit.
trees = [("Ssz", "Ssz.Proofs"), ("SszNative", "SszNative.Proofs")]


def imports(path: Path) -> list[str]:
    """The modules one file imports, in order."""
    found = []
    for line in path.read_text().splitlines():
        if match := re.match(r"^(?:public\s+)?import\s+(.+)", line):
            found.extend(match[1].split("--", 1)[0].split())
    return found


def closure(start: str, modules: dict[str, Path]) -> set[str]:
    """Every module of the tree reachable from one module."""
    seen: set[str] = set()
    pending = [start]
    while pending:
        module = pending.pop()
        if module in seen or module not in modules:
            continue
        seen.add(module)
        pending.extend(imports(modules[module]))
    return seen


failures = []
for implementation, proofs in trees:
    modules = {
        ".".join(path.relative_to(root).with_suffix("").parts): path
        for path in (root / implementation).rglob("*.lean")
    }
    modules[implementation] = root / f"{implementation}.lean"

    # An unimported file could otherwise escape both the default build and the axiom audit.
    missing = sorted(modules.keys() - closure(proofs, modules))
    if missing:
        heading = f"{implementation} modules missing from the audited import closure:"
        failures.append(heading + "\n" + "\n".join(missing))

    # A proof reached only through the implementation would make the split meaningless.
    reached = closure(implementation, modules)
    leaked = sorted(name for name in reached if name == proofs or name.startswith(proofs + "."))
    if leaked:
        heading = f"proof modules imported by the {implementation} implementation:"
        failures.append(heading + "\n" + "\n".join(leaked))

if failures:
    sys.exit("\n\n".join(failures))
