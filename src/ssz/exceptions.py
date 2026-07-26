"""
Typed exception hierarchy for the SSZ type system.

Every raise site passes structured data, never a pre-formatted string.
Each constructor owns one message format, so a given failure mode reads
identically everywhere it occurs, and its fields stay machine-readable.
"""

from __future__ import annotations

from collections.abc import Sequence


class SSZError(Exception):
    """Base class for every SSZ error."""


class SSZTypeError(SSZError):
    """A Python value or an SSZ type definition is unusable as given."""


class SSZValueError(SSZError):
    """A well-typed value falls outside the range SSZ permits."""


class SSZSerializationError(SSZError):
    """SSZ bytes could not be produced, or could not be parsed."""


class SSZTypeMismatch(SSZTypeError):  # noqa: N818
    """A value has the wrong Python type for the target SSZ type."""

    def __init__(self, expected: str, got: type, detail: str | None = None) -> None:
        """Record the expected phrasing, the offending type, and any coercion detail."""
        self.expected = expected
        self.got = got
        self.detail = detail
        message = f"Expected {expected}, got {got.__name__}"
        # Element coercion attaches the inner failure that triggered it.
        if detail is not None:
            message = f"{message}: {detail}"
        super().__init__(message)


class SSZDefinitionError(SSZTypeError):
    """An SSZ subclass omits an attribute its base needs to operate."""

    def __init__(self, type_name: str, requirement: str) -> None:
        """Record the type and the attribute it failed to declare."""
        self.type_name = type_name
        self.requirement = requirement
        super().__init__(f"{type_name} must define {requirement}")


class SSZActiveFieldsError(SSZTypeError):
    """A progressive container declares a field layout the spec does not permit."""

    def __init__(self, type_name: str, active_fields: Sequence[int], reason: str) -> None:
        """Record the type, the layout it declared, and the rule that layout breaks."""
        self.type_name = type_name
        self.active_fields = tuple(active_fields)
        self.reason = reason
        super().__init__(f"{type_name}: invalid active fields, {reason}")


class SSZUnionOptionsError(SSZTypeError):
    """A union declares options the spec forbids, or holds one it never declared."""

    def __init__(self, type_name: str, reason: str) -> None:
        """Record the union and the rule its options break."""
        self.type_name = type_name
        self.reason = reason
        super().__init__(f"{type_name}: invalid union options, {reason}")


class SSZFixedSizeError(SSZTypeError):
    """A fixed byte length was requested from a variable-size type."""

    def __init__(self, type_name: str, kind: str) -> None:
        """Record the type and the variable-size kind that has no fixed length."""
        self.type_name = type_name
        self.kind = kind
        super().__init__(f"{type_name}: variable-size {kind} has no fixed byte length")


class SSZLimitError(SSZValueError):
    """An element or byte count exceeds the type's declared upper bound."""

    def __init__(self, type_name: str, limit: int, actual: int) -> None:
        """Record the type, its declared upper bound, and the count that exceeded it."""
        self.type_name = type_name
        self.limit = limit
        self.actual = actual
        super().__init__(f"{type_name} exceeds limit of {limit}, got {actual}")


class SSZLengthError(SSZValueError):
    """A fixed-size type received a count other than the one it requires."""

    def __init__(self, type_name: str, expected: int, actual: int, unit: str = "elements") -> None:
        """Record the type, the required count, the actual count, and the unit."""
        self.type_name = type_name
        self.expected = expected
        self.actual = actual
        self.unit = unit
        super().__init__(f"{type_name} requires exactly {expected} {unit}, got {actual}")


class SSZRangeError(SSZValueError):
    """An integer falls outside the inclusive range a uint type can hold."""

    def __init__(self, type_name: str, value: int, max_value: int) -> None:
        """Record the type, the out-of-range value, and the inclusive upper bound."""
        self.type_name = type_name
        self.value = value
        self.max_value = max_value
        super().__init__(f"{value} out of range for {type_name} [0, {max_value}]")


class SSZScopeError(SSZSerializationError):
    """The byte budget for a value does not match the length it needs."""

    def __init__(self, type_name: str, expected: int, actual: int) -> None:
        """Record the type, the byte count it needs, and the byte budget it got."""
        self.type_name = type_name
        self.expected = expected
        self.actual = actual
        super().__init__(f"{type_name}: expected {expected} bytes, got {actual}")
