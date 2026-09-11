"""Fixture format for a path through an SSZ type, resolved to the generalized index it names."""

from collections.abc import Mapping
from enum import StrEnum
from typing import Any, ClassVar, Final

from pydantic import Field, computed_field

from ssz.chunks import next_pow2
from ssz.exceptions import SSZError, SSZTypeError, TypeFault, ValueFault
from ssz.gindex import gindex_depth
from ssz.paths import (
    ACTIVE_FIELDS_KEY,
    LENGTH_KEY,
    SELECTOR_KEY,
    PathStep,
    chunk_count,
    get_generalized_index,
)
from ssz.ssz_base import SSZType
from ssz_testing.fixtures import (
    BaseConsensusFixture,
    BaseTestSpec,
    CamelModel,
    TypeDescriptor,
    describe_type,
)


class MixedInWord(StrEnum):
    """The three words an SSZ root is hashed against, spelled as a path can name them."""

    ELEMENT_COUNT = "elementCount"
    FIELD_LAYOUT = "fieldLayout"
    TYPE_SELECTOR = "typeSelector"


class MixinStep(CamelModel):
    """A mixed-in word wrapped in an object, so no field name can be read as one."""

    model_config = CamelModel.model_config | {"extra": "forbid", "frozen": True}

    mixin: MixedInWord
    """Which of the three words this step selects."""


ELEMENT_COUNT_STEP: Final = MixinStep(mixin=MixedInWord.ELEMENT_COUNT)
"""Path step naming the element count a variable-size shape mixes in."""

FIELD_LAYOUT_STEP: Final = MixinStep(mixin=MixedInWord.FIELD_LAYOUT)
"""Path step naming the field layout a progressive container mixes in."""

TYPE_SELECTOR_STEP: Final = MixinStep(mixin=MixedInWord.TYPE_SELECTOR)
"""Path step naming the type selector a compatible union mixes in."""

type GindexPathStep = str | int | MixinStep
"""One step as JSON spells it: a field name, an element position, or a mixed-in word."""

_RESERVED_STEPS: Final[dict[MixedInWord, PathStep]] = {
    MixedInWord.ELEMENT_COUNT: LENGTH_KEY,
    MixedInWord.FIELD_LAYOUT: ACTIVE_FIELDS_KEY,
    MixedInWord.TYPE_SELECTOR: SELECTOR_KEY,
}
"""Each spelled word against the reserved step the resolver takes for it."""


def resolver_path(path: tuple[GindexPathStep, ...]) -> tuple[PathStep, ...]:
    """The steps the resolver takes, each wrapped word becoming the reserved name it stands for."""
    return tuple(
        _RESERVED_STEPS[step.mixin] if isinstance(step, MixinStep) else step for step in path
    )


class GindexFixture(BaseConsensusFixture):
    """Emitted vector for one path through an SSZ type."""

    format_name: ClassVar[str] = "ssz_gindex_test"

    type_name: str
    """SSZ type class name."""

    ssz_type: type[SSZType] = Field(exclude=True)
    """The declaration the path is walked through, which the type name has to stand for."""

    path: tuple[GindexPathStep, ...]
    """Steps from the type's own root down to the node, as JSON spells them."""

    gindex: str | None = None
    """The generalized index in decimal, absent on a path the type refuses."""

    depth: int | None = None
    """Levels that index sits below the root, which is the node count of its proof branch."""

    @computed_field
    @property
    def type_descriptor(self) -> TypeDescriptor:
        """The declaration of that type, read off the class so no vector can misstate it."""
        return describe_type(self.ssz_type)

    @computed_field
    @property
    def chunk_count(self) -> int | None:
        """Leaves the type merkleizes into at its own level, absent for an unbounded spine."""
        try:
            return chunk_count(self.ssz_type)
        # A progressive shape grows with its data, so it has no leaf count to report.
        except SSZTypeError:
            return None

    @computed_field
    @property
    def tree_width(self) -> int | None:
        """Power of two those leaves pad out to, which is what one step down the tree costs."""
        leaves = self.chunk_count
        return None if leaves is None else next_pow2(leaves)

    def declared_types(self) -> Mapping[str, TypeDescriptor]:
        """The one name this vector emits, against the declaration it was filled from."""
        return {self.type_name: self.type_descriptor}

    def case_type_name(self) -> str:
        """The declared type name this vector is about."""
        return self.type_name

    def case_kind(self) -> str:
        """The kind the declaration already states, spelled as a directory can hold it."""
        return self.type_descriptor.directory_name


class GindexTest(BaseTestSpec):
    """Spec for one path, checked against the index or the refusal its author states."""

    format_name: ClassVar[str] = "ssz_gindex_test"
    description: ClassVar[str] = "Resolves a path through an SSZ type to a generalized index"

    type_name: str
    """SSZ type class name."""

    ssz_type: type[SSZType]
    """The declaration the path is walked through."""

    path: tuple[GindexPathStep, ...] = ()
    """The steps to walk, an empty path naming the type's own root."""

    gindex: int | None = None
    """The index the path must resolve to, required unless the path is refused."""

    refusal: TypeFault | ValueFault | None = None
    """The fault the path must be refused with, from whichever catalogue names it."""

    def generate(self) -> GindexFixture:
        """Resolve the path, check it against what the author stated, and emit the vector."""
        if (refusal := self.refusal) is not None:
            return self._generate_refusal(refusal)
        if self.gindex is None:
            raise ValueError("a path that resolves must state the generalized index it names")

        steps = resolver_path(self.path)
        index = get_generalized_index(self.ssz_type, *steps)
        assert index == self.gindex, (
            f"{self.type_name} resolves {list(steps)} to generalized index {index}, "
            f"and the vector states {self.gindex}"
        )

        return GindexFixture(
            type_name=self.type_name,
            ssz_type=self.ssz_type,
            path=self.path,
            gindex=str(index),
            depth=gindex_depth(index),
        )

    def _generate_refusal(self, refusal: TypeFault | ValueFault) -> GindexFixture:
        """Assert the type refuses the path with the authored fault, and emit that fault."""
        steps = resolver_path(self.path)
        exception_raised: SSZError[Any] | None = None
        try:
            get_generalized_index(self.ssz_type, *steps)
        # Only an SSZ refusal is a vector; anything else is a bug, and crashes the fill.
        except SSZError as exception:
            exception_raised = exception

        if exception_raised is None:
            raise AssertionError(
                f"Expected {self.type_name} to refuse {list(steps)}, but the path resolved"
            )
        if exception_raised.fault is not refusal:
            raise AssertionError(
                f"{self.type_name} refused {list(steps)} for the wrong reason.\n"
                f"  Expected fault: {refusal.name}\n"
                f"  Actual fault: {exception_raised.fault.name}"
            )

        return GindexFixture(
            type_name=self.type_name,
            ssz_type=self.ssz_type,
            path=self.path,
            rejection_reason=refusal,
        )
