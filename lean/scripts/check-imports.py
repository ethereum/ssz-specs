"""Check that every specification module is reachable from the audited entry point."""

import re
import sys
from pathlib import Path

# The implementation and its proofs both belong to the audit; the fixture readers do not.
root = Path(__file__).resolve().parents[1]
modules = {
    ".".join(path.relative_to(root).with_suffix("").parts): path
    for path in (root / "Ssz").rglob("*.lean")
}
modules["Ssz"] = root / "Ssz.lean"

# The proof root imports the implementation, so one walk from it covers both trees.
pending = ["Ssz.Proofs"]
visited: set[str] = set()
while pending:
    module = pending.pop()
    if module in visited or module not in modules:
        continue
    visited.add(module)
    for line in modules[module].read_text().splitlines():
        if match := re.match(r"^(?:public\s+)?import\s+(.+)", line):
            pending.extend(match[1].split("--", 1)[0].split())

# An unimported file could otherwise escape both the default build and the axiom audit.
missing = sorted(modules.keys() - visited)
if missing:
    sys.exit("SSZ modules missing from the audited import closure:\n" + "\n".join(missing))

# A proof reached only through the implementation would make the split meaningless.
implementation = {"Ssz"}
pending = ["Ssz"]
while pending:
    module = pending.pop()
    for line in modules[module].read_text().splitlines():
        if match := re.match(r"^(?:public\s+)?import\s+(.+)", line):
            for imported in match[1].split("--", 1)[0].split():
                if imported in modules and imported not in implementation:
                    implementation.add(imported)
                    pending.append(imported)

leaked = sorted(name for name in implementation if name.startswith("Ssz.Proofs"))
if leaked:
    sys.exit("proof modules imported by the implementation:\n" + "\n".join(leaked))
