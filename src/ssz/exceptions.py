"""The two ways SSZ refuses something, and the closed catalogue of reasons for each."""

from enum import Enum
from typing import Any


class TypeFault(Enum):
    """Every way an SSZ type is unusable as declared, or as asked."""

    WRONG_TYPE = "expected {expected}, got {got}"
    UNDECLARED = "{type} must declare {requirement}"
    NOT_AN_SSZ_TYPE = "{type}.{field} must be an SSZ type, got {got}"
    NOT_AN_INTEGER = "{type}.{field} must be a plain integer, got {got}"
    CAPACITY_NEGATIVE = "{type}.{field} counts what a shape holds, and {got} is not a count"
    REBOUND = "{type} sets {field} to {got}, and {source} fixes it to {fixed}"
    OWN_ROOT = "{type} declares a hash_tree_root of its own"
    IMMUTABLE = "{type} is immutable"
    NO_DEFAULT = "{type} has no default value"
    NO_MERKLE_LAYOUT = "{type} has no Merkle layout"
    NOT_FIXED_SIZE = "{type} is a variable-size {kind}, and has no one byte length"

    VECTOR_EMPTY = "a vector holds at least one element, got a length of {length}"
    NOT_ENTITLED = "{type} declares a {capacity} its shape has none of"

    LAYOUT_NOT_BITS = "a field layout holds only 0 and 1"
    LAYOUT_WIDTH = "a field layout holds at least one position, got {width}"
    LAYOUT_WIDTH_TYPE = "a field layout width is a plain integer, got {got}"
    LAYOUT_GAP_TYPE = "a field layout position is a plain integer, got {got}"
    LAYOUT_TRAILING_GAP = "a field layout ends on a field, not on a gap"
    LAYOUT_TOO_WIDE = "a field layout holds {width} positions, over the limit of {limit}"
    LAYOUT_FIELD_COUNT = "the layout sets {active} positions, and the struct declares {declared}"
    LAYOUT_GAP_OUTSIDE = "gap {gap} falls outside a layout of {width} positions"
    LAYOUT_GAPS_UNORDERED = "gaps {gaps} are not in ascending order"

    UNION_EMPTY = "a union declares at least one option"
    UNION_NOT_A_MAP = "a union declares a selector-to-type map, got {got}"
    UNION_SELECTOR_TYPE = "selector {selector!r} is not a plain integer"
    UNION_SELECTOR_RANGE = "selector {selector} falls outside {low} through {high}"
    UNION_OPTION_TYPE = "option {selector} is not an SSZ type"
    UNION_INCOMPATIBLE = "options {selector} and {other} merkleize differently"

    NO_PARTS = "{type} has no parts to address"
    NO_PARTS_MIXIN = "the {word} of {type} has no parts to address"
    NO_MIXIN = "{type} mixes in no {word}"
    NO_CHUNK_COUNT = "{type} has no bounded chunk count"
    NOT_STEPPABLE = "{type} cannot be stepped into"


class ValueFault(Enum):
    """Every way a value, or a byte string, fails to be one an SSZ type admits."""

    RANGE = "{value} is out of range for {type} [0, {max}]"
    NOT_A_BIT = "a boolean is 0 or 1, got {value}"
    COUNT = "{type} holds exactly {expected} {unit}, got {actual}"
    LIMIT = "{type} holds at most {limit} {unit}, got {actual}"
    NOT_HEX = "{type} reads a string as hex digits, and this one holds something else"

    SCOPE = "{type} spans {expected} bytes, and the budget is {actual}"
    SCOPE_TOO_SMALL = "{type} needs at least {expected} bytes, and the budget is {actual}"
    SCOPE_NEGATIVE = "a budget of {scope} is not a byte count"
    SCOPE_UNDIVIDED = "a budget of {scope} does not divide by an element width of {width}"
    SCOPE_WIDTHLESS = "{type} holds elements of no width, so a budget of {scope} counts none"
    TRUNCATED = "{type} needs {expected} bytes, the input holds {actual}"
    TRAILING_BYTES = "{leftover} byte(s) past the end of the value"

    FIRST_OFFSET = "the first offset is {actual}, and the fixed part ends at {expected}"
    OFFSET_UNORDERED = "offset {offset} is above the offset after it, {next}"
    OFFSET_PAST_SCOPE = "offset {offset} runs past the budget of {scope}"
    OFFSET_UNALIGNED = "the first offset {offset} is not a multiple of {width}"
    OFFSET_BELOW_TABLE = "the first offset {offset} is below the table's own width of {width}"

    EMPTY_ENCODING = "an empty input encodes no value"
    NO_DELIMITER = "the encoding sets no delimiter bit"
    TRAILING_ZEROS = "zero bytes past the delimiter give one value a second encoding"
    PADDING_BITS = "the final byte {byte} sets a padding bit"

    NO_SELECTOR = "a budget of {scope} holds no selector"
    UNKNOWN_SELECTOR = "selector {selector} names no option of {type}"

    NO_SUCH_FIELD = "{type} has no field named {step}"
    NO_SUCH_OPTION = "{type} has no option with selector {step}"
    NO_SUCH_POSITION = "{type} has no position {step}"
    NOT_A_POSITION = "a position is a plain integer, got {step!r}"
    NOT_A_GINDEX = "{index} is not a generalized index"
    ROOT_HAS_NO_BRANCH = "the root has no proof branch of its own"
    REPEATED_INDEX = "a generalized index is repeated"
    NESTED_INDEX = "{index} lies below another index in the same request"
    EMPTY_REQUEST = "a request holds at least one index"
    BRANCH_LENGTH = "a branch for index {index} holds {expected} nodes, got {actual}"
    LEAF_COUNT = "{expected} indices need as many leaves, got {actual}"
    PROOF_LENGTH = "this request needs {expected} proof nodes, got {actual}"

    PATH_INTO_MIXIN = "the path descends into the mixed-in word of {type}"
    PATH_INTO_PACKED = "the path descends into the packed data of {type}"
    PATH_INTO_GAP = "the path descends into an empty position of {type}"
    PATH_PAST_SPINE = "the path lies past the end of the progressive spine of {type}"

    MERKLEIZE_LIMIT = "{count} chunks exceed a limit of {limit}"
    ZERO_TREE_WIDTH = "a zero subtree spans a power of two up to 2**{depth} leaves, got {width}"
    STALE_ROOT = "stale remembered root for {type}"
    NEGATIVE_LENGTH = "a mixed-in length is not negative, got {length}"
    SELECTOR_BYTE = "selector {selector} does not fit one byte"


class _Fields(dict[str, Any]):
    """The fields a raise site passed, naming any the template asked for and it left out."""

    def __missing__(self, key: str) -> str:
        """Report the gap in place of the value, so building a message never itself raises."""
        return f"<no {key}>"


class SSZError[FaultT: (TypeFault, ValueFault)](Exception):
    """Base for every SSZ refusal, drawing on the catalogue its subclass fixes."""

    def __init__(self, fault: FaultT, /, **fields: Any) -> None:
        """Render the fault's one sentence, and open an empty path for it to collect."""
        self.fault = fault
        """The catalogue member this refusal names, whose name is its stable tag."""

        self.fields: dict[str, Any] = fields
        """The values the raise site passed, for a reader that wants them apart."""

        self.loc: tuple[str | int, ...] = ()
        """Path from the value the caller passed down to the one that refused."""

        self.message = fault.value.format_map(_Fields(fields))
        """The rendered sentence, with no path in front of it."""

        super().__init__(self.message)

    def at(self, step: str | int) -> None:
        """Record one step of the path this error is travelling up, outermost step first."""
        self.loc = (step, *self.loc)

    def __str__(self) -> str:
        """The sentence, behind the path it came from wherever there is one."""
        if not self.loc:
            return self.message
        path = "".join(f"[{step}]" if isinstance(step, int) else f".{step}" for step in self.loc)
        return f"{path.removeprefix('.')}: {self.message}"


class SSZTypeError(SSZError[TypeFault], TypeError):
    """An SSZ type cannot do what was asked of it, or was declared in a way it cannot be."""


class SSZValueError(SSZError[ValueFault], ValueError):
    """A value, or a byte string, is not one this SSZ type admits."""
