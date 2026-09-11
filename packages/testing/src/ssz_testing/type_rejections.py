"""Fixture format for the type declarations the specification calls illegal."""

from collections.abc import Mapping
from typing import ClassVar

from ssz.exceptions import SSZTypeError, TypeFault
from ssz_testing.fixtures import BaseConsensusFixture, BaseTestSpec, TypeDescriptor
from ssz_testing.type_builder import build_declaration


class TypeRejectionFixture(BaseConsensusFixture):
    """Emitted vector for a type declaration no implementation may accept."""

    format_name: ClassVar[str] = "ssz_type_rejection"

    type_name: str
    """The name to declare the illegal type under, which its refusal may quote back."""

    type_descriptor: TypeDescriptor
    """The illegal declaration itself, in the shape a consumer rebuilds any type from."""

    def declared_types(self) -> Mapping[str, TypeDescriptor]:
        """The one name this vector emits, against the declaration it stands for."""
        return {self.type_name: self.type_descriptor}

    def case_type_name(self) -> str:
        """The declared type name this vector is about."""
        return self.type_name

    def case_kind(self) -> str:
        """The kind the declaration already states, spelled as a directory can hold it."""
        return self.type_descriptor.directory_name


class TypeRejectionTest(BaseTestSpec):
    """Spec for an illegal declaration, checked by building it and requiring the named refusal."""

    format_name: ClassVar[str] = "ssz_type_rejection"
    description: ClassVar[str] = "Tests that an illegal SSZ type declaration is refused"

    type_name: str
    """The name to declare the illegal type under."""

    type_descriptor: TypeDescriptor
    """The illegal declaration, authored, no class being able to hold it to be read off."""

    rejection_reason: TypeFault
    """The fault the declaration must be refused with, and the field the vector emits."""

    exact_message: str
    """Full refusal message, a fill-time self-check pinning the parameters the fault carried."""

    def generate(self) -> TypeRejectionFixture:
        """
        Build the declaration a consumer would, require the named refusal, and emit the vector.

        Raises:
            AssertionError: When the declaration stands, or is refused for another reason.
        """
        # Built through the reconstruction a consumer runs, so the vector states one declaration.
        try:
            build_declaration(self.type_descriptor.to_json(exclude_none=True), self.type_name)
        except SSZTypeError as refusal:
            if refusal.fault is not self.rejection_reason:
                raise AssertionError(
                    f"The declaration of {self.type_name} was refused for the wrong reason.\n"
                    f"  Expected fault: {self.rejection_reason.name}\n"
                    f"  Actual fault: {refusal.fault.name}"
                ) from refusal
            if str(refusal) != self.exact_message:
                raise AssertionError(
                    f"The declaration of {self.type_name} was refused with the wrong message.\n"
                    f"  Expected exact message: {self.exact_message!r}\n"
                    f"  Actual message: {str(refusal)!r}"
                ) from refusal
        else:
            raise AssertionError(
                f"Expected the declaration of {self.type_name} to be refused, but it stands"
            )

        return TypeRejectionFixture(
            type_name=self.type_name,
            type_descriptor=self.type_descriptor,
            rejection_reason=self.rejection_reason,
        )
