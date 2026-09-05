"""
One crossing of the language boundary: what is claimed, and how a claim is drawn.

Every class here knows both how to draw itself and how to write itself out.
No class holds a field that another of its fields already determines.
"""

from dataclasses import dataclass
from typing import Self

import ssz
from parity.draw import Draw
from parity.generate import build_path, build_type, build_value
from parity.wire import Json, Step, descriptor, json_value

PATHS_PER_CASE = 4
"""Paths drawn into each generated value."""


@dataclass(frozen=True, slots=True)
class PathClaim:
    """One path into a value, and what the specification answers about it."""

    steps: list[Step]
    """The path, from the root of the value downward."""

    gindex: int | None = None
    """Node the path names, or nothing where the specification turns the path away."""

    node: str | None = None
    """Root of the subtree at that node."""

    proof: list[str] | None = None
    """Branch authenticating that node against the value's own root."""

    @property
    def refused(self) -> bool:
        """Whether the specification turned the path away rather than answering it."""
        return self.gindex is None

    @classmethod
    def drawn(cls, draw: Draw, ssz_type: type[ssz.SSZType], value: ssz.SSZType) -> Self | None:
        """A random path into a value, and the answer, or nothing where no path was drawn."""
        steps = build_path(draw, ssz_type, value)
        if not steps:
            return None
        try:
            gindex = ssz.get_generalized_index(ssz_type, *[step.python for step in steps])
            node = ssz.node_root(value, gindex)
            proof = ssz.build_proof(value, gindex)
        except ssz.SSZError:
            # A path the specification refuses must be refused on the other side too.
            return cls(steps=steps)
        return cls(
            steps=steps,
            gindex=gindex,
            node="0x" + bytes(node).hex(),
            proof=["0x" + bytes(sibling).hex() for sibling in proof],
        )

    def to_json(self) -> Json:
        """The claim as the corpus writes it, omitting what a refusal does not answer."""
        written: Json = {"path": [step.to_json() for step in self.steps], "refused": self.refused}
        if not self.refused:
            written |= {"gindex": self.gindex, "node": self.node, "proof": self.proof}
        return written


@dataclass(frozen=True, slots=True)
class Multiproof:
    """Several nodes claimed at once, and what a verifier cannot rebuild for itself."""

    indices: list[int]
    """Nodes claimed together, deepest first."""

    proof: list[str]
    """Nodes the request needs beyond what it claims."""

    @classmethod
    def over(cls, value: ssz.SSZType, claims: list[PathClaim]) -> Self | None:
        """The claims taken together, or nothing where they make no request a verifier accepts."""
        indices = sorted(
            {claim.gindex for claim in claims if claim.gindex is not None}, reverse=True
        )
        if len(indices) < 2:
            return None
        try:
            nodes = ssz.build_multiproof(value, indices)
        except ssz.SSZError:
            # A request naming nested indices is refused, and claims nothing here.
            return None
        return cls(indices=indices, proof=["0x" + bytes(node).hex() for node in nodes])

    def to_json(self) -> Json:
        """The request as the corpus writes it."""
        return {"indices": self.indices, "proof": self.proof}


@dataclass(frozen=True, slots=True)
class Case:
    """One generated type, one value of it, and everything both sides must agree on."""

    name: str
    """What to call this case in a disagreement."""

    ssz_type: type[ssz.SSZType]
    """The type the case was drawn from."""

    value: ssz.SSZType
    """The value the case was drawn from."""

    paths: list[PathClaim]
    """Claims about nodes of the value's own tree."""

    default: ssz.SSZType | None = None
    """The type's default value, where it has one."""

    multiproof: Multiproof | None = None
    """Several of the claims taken together, where they make a request at all."""

    @classmethod
    def drawn(cls, draw: Draw, name: str) -> Self:
        """A random type, a random value of it, and the claims the specification makes."""
        ssz_type = build_type(draw)
        value = build_value(draw, ssz_type)
        try:
            default = ssz_type.default()
        except ssz.SSZError:
            # A union has no default, since no option is the one to take.
            default = None
        drawn = (PathClaim.drawn(draw, ssz_type, value) for _ in range(PATHS_PER_CASE))
        claims = [claim for claim in drawn if claim is not None]
        return cls(
            name=name,
            ssz_type=ssz_type,
            value=value,
            paths=claims,
            default=default,
            multiproof=Multiproof.over(value, claims),
        )

    def to_json(self) -> Json:
        """The case as the corpus writes it, omitting what the type does not have."""
        written: Json = {
            "name": self.name,
            "desc": descriptor(self.ssz_type),
            "value": json_value(self.value),
            "serialized": "0x" + self.value.encode_bytes().hex(),
            "root": "0x" + bytes(ssz.hash_tree_root(self.value)).hex(),
            # Every type here is declared through this implementation, so all are well formed.
            "wellFormed": True,
            "paths": [claim.to_json() for claim in self.paths],
        }
        if self.default is not None:
            written["default"] = json_value(self.default)
        if self.multiproof is not None:
            written["multiproof"] = self.multiproof.to_json()
        return written


@dataclass(frozen=True, slots=True)
class CompatibilityPair:
    """Two types, and whether the specification says they merkleize alike."""

    name: str
    """What to call this pair in a disagreement."""

    left: type[ssz.SSZType]
    """One of the two types."""

    right: type[ssz.SSZType]
    """The other."""

    @classmethod
    def drawn(cls, draw: Draw, name: str) -> Self:
        """Two random types, the same one half the time so agreement is exercised too."""
        left = build_type(draw)
        return cls(name=name, left=left, right=left if draw.flag() else build_type(draw))

    def to_json(self) -> Json:
        """The pair as the corpus writes it."""
        return {
            "name": self.name,
            "left": descriptor(self.left),
            "right": descriptor(self.right),
            "compatible": ssz.is_compatible(self.left, self.right),
        }


@dataclass(frozen=True, slots=True)
class Corpus:
    """Everything handed across the language boundary in one crossing."""

    cases: list[Case]
    """Types, values, and the claims made about them."""

    pairs: list[CompatibilityPair]
    """Type pairs, and whether they merkleize alike."""

    @classmethod
    def drawn(cls, draw: Draw, label: str, cases: int, pairs: int) -> Self:
        """A batch of independent cases and pairs, each named after the batch that drew it."""
        return cls(
            cases=[Case.drawn(draw, f"{label}-case{n}") for n in range(cases)],
            pairs=[CompatibilityPair.drawn(draw, f"{label}-pair{n}") for n in range(pairs)],
        )

    def to_json(self) -> Json:
        """The corpus as the Lean side reads it."""
        return {
            "cases": [case.to_json() for case in self.cases],
            "compatible": [pair.to_json() for pair in self.pairs],
        }
