"""
Decoding for the native backend: checked by the proved routine, then built over the encoding.

The proved check refuses exactly what decoding refuses.
An encoding it accepts is built without checking again, and a long sequence builds no element.
Each element is decoded the first time it is read, and its bytes serve its root until then.
Integers and booleans are the exception: they are built all at once, at machine speed.
An encoding it refuses is decoded by the specification, which raises its own refusal.
"""

from __future__ import annotations

import ctypes
import io
import weakref
from array import array
from collections.abc import Callable
from typing import Any, Final

from ssz import native
from ssz.boolean import Boolean
from ssz.byte_arrays import ByteVector
from ssz.collections import List, Vector
from ssz.container import Container, ProgressiveContainer
from ssz.exceptions import SSZError
from ssz.lazy import LazyElements
from ssz.offsets import BYTES_PER_LENGTH_OFFSET, check_composite_size
from ssz.ssz_base import SSZModel, SSZType
from ssz.uint import BaseUint

LAZY_ELEMENTS: Final = 64
"""The element count from which a sequence is decoded lazily, rather than all at once."""


def decode(cls: type, data: bytes) -> SSZModel | None:
    """
    A composite decoded over its encoding once the proved check accepts it, or None.

    None leaves the input to the specification, which decodes it or raises its refusal.
    """
    if not (isinstance(cls, type) and issubclass(cls, SSZModel)):
        return None
    encoding = data if type(data) is bytes else bytes(data)
    try:
        native.validate(cls, encoding)
    except (SSZError, TypeError, ValueError, OverflowError, AttributeError):
        return None
    return _decoded(cls, encoding, 0, len(encoding))


_LEAVES: Final[dict[type, Callable[[bytes], Any] | None]] = {}
"""How each class is read from exactly its bytes, or None where it is not a leaf, once per class."""


def _leaf(cls: type) -> Callable[[bytes], Any] | None:
    """How an integer, a boolean or a byte array is read from its bytes, with no stream."""
    if cls not in _LEAVES:
        if issubclass(cls, (BaseUint, Boolean)):
            _LEAVES[cls] = cls.decode_bytes
        elif issubclass(cls, ByteVector):
            # The check held the bytes to the declared width.
            _LEAVES[cls] = cls._trusted
        else:
            _LEAVES[cls] = None
    return _LEAVES[cls]


def _decoded(cls: type[SSZType], encoding: bytes, start: int, stop: int) -> Any:
    """A value of a type from an accepted encoding's range, long sequences built lazily."""
    # A struct's fields and a sequence's elements are mostly leaves, read here one call each.
    leaf = _leaf(cls)
    if leaf is not None:
        return leaf(encoding[start:stop])
    composite = issubclass(cls, (Vector, List, Container, ProgressiveContainer))
    # The size rule is asked as the specification's decoder asks it, wherever its bound is set.
    if composite:
        check_composite_size(stop - start)
    if issubclass(cls, (Vector, List)):
        basic = _basic_elements(cls, encoding, start, stop)
        if basic is not None:
            return cls.model_construct(_fields_set={"data"}, data=basic)
        lazy = _lazy_elements(cls, encoding, start, stop)
        if lazy is not None:
            value = cls.model_construct(_fields_set={"data"}, data=lazy)
            lazy.owner = weakref.ref(value)
            return value
    elif issubclass(cls, (Container, ProgressiveContainer)):
        return cls.model_construct(**_fields(cls, encoding, start, stop))
    # Anything else is short, or has no lazy form: the specification decodes it.
    return cls.deserialize(io.BytesIO(encoding[start:stop]), stop - start)


_WIDTHS: Final[dict[type, list[tuple[str, type[SSZType], int | None]]]] = {}
"""Each struct's fields with the width of each, None where it varies, once per class."""


def _fields(
    cls: type[Container | ProgressiveContainer], encoding: bytes, start: int, stop: int
) -> dict[str, Any]:
    """Each field of a struct from its range: inline where fixed, behind an offset otherwise."""
    widths = _WIDTHS.get(cls)
    if widths is None:
        widths = _WIDTHS[cls] = [(name, kind, kind.fixed_size()) for name, kind in cls._FIELD_TYPES]
    fields: dict[str, Any] = {}
    variable: list[tuple[str, type[SSZType], int]] = []
    at = start
    for name, field_type, width in widths:
        if width is None:
            offset = int.from_bytes(encoding[at : at + BYTES_PER_LENGTH_OFFSET], "little")
            variable.append((name, field_type, start + offset))
            at += BYTES_PER_LENGTH_OFFSET
        else:
            fields[name] = _decoded(field_type, encoding, at, at + width)
            at += width
    # Every field fixed is every field read in declaration order already.
    if not variable:
        return fields
    # A body runs from its offset to the next one, and the last to the end of the struct.
    for index, (name, field_type, body) in enumerate(variable):
        end = variable[index + 1][2] if index + 1 < len(variable) else stop
        fields[name] = _decoded(field_type, encoding, body, end)
    # Declaration order, as the specification's decoder builds the struct.
    return {name: fields[name] for name, _, _ in widths}


_WORD_CODES: Final = {1: "B", 2: "H", 4: "I", 8: "Q"}
"""The array type code of each basic width a word holds, in the backend's little-endian order."""


def _basic_elements(
    cls: type[Vector[Any] | List[Any]], encoding: bytes, start: int, stop: int
) -> list[Any] | None:
    """
    Every element of a sequence of integers or booleans up to a word wide, or None.

    A plain list is what the specification holds, so its reads and writes cost what they cost there.
    Built from the words in one pass, each element costs a single call.
    """
    element_type = cls.ELEMENT_TYPE
    if issubclass(element_type, Boolean):
        # The check let no byte but 0 or 1 through, and both values are shared.
        return list(map(element_type._INTERNED.__getitem__, encoding[start:stop]))
    if not issubclass(element_type, BaseUint):
        return None
    code = _WORD_CODES.get(element_type.BYTE_LENGTH)
    if code is None:
        return None
    # Every value of one byte is shared.
    if code == "B":
        return list(map(element_type._INTERNED.__getitem__, encoding[start:stop]))
    return list(map(element_type._wrap, array(code, encoding[start:stop])))


def _lazy_elements(
    cls: type[Vector[Any] | List[Any]], encoding: bytes, start: int, stop: int
) -> LazyElements | None:
    """The elements of a long sequence, decoded on first read, or None for a short one."""
    element_type = cls.ELEMENT_TYPE
    width = element_type.fixed_size()
    size = stop - start
    if width is not None:
        count = size // width
        bounds = None
    else:
        count = int.from_bytes(encoding[start : start + 4], "little") // 4 if size else 0
        # Each body starts at its offset, and the last ends where the sequence does.
        bounds = array("Q", array("I", encoding[start : start + 4 * count]))
        bounds.append(size)
    if count < LAZY_ELEMENTS:
        return None

    def element(encoding: bytes, first: int, last: int) -> Any:
        """One element from its range."""
        return _decoded(element_type, encoding, first, last)

    return LazyElements(encoding, start, stop, count, width or 0, bounds, element)


_LIBRARY: Final = native._library()
"""The proved routines, loaded once the backend is known to run."""

_ROOTS_CHUNKED: Final = _LIBRARY["ssz_roots_chunked"]
_ROOT_ELEMENTS: Final = _LIBRARY["ssz_root_elements"]
_PLAN_PLAIN: Final = _LIBRARY["ssz_plan_plain"]
for _routine in (_ROOTS_CHUNKED, _ROOT_ELEMENTS):
    _routine.restype = ctypes.c_uint64
    _routine.argtypes = (
        [ctypes.c_char_p, ctypes.c_void_p] + [ctypes.c_uint64] * 2 + [ctypes.c_void_p] * 2
    )
_PLAN_PLAIN.restype = ctypes.c_uint64
_PLAN_PLAIN.argtypes = [ctypes.c_char_p]


def element_roots(cls: type[Vector[Any] | List[Any]], lazy: LazyElements) -> bytearray:
    """
    The roots of the elements a lazy sequence's encoding holds, back to back, in one call.

    Structs of plain fields are rooted together a field at a time; the rest one by one.
    """
    element_plan = native.plan(cls.ELEMENT_TYPE)
    count = lazy.original
    size = lazy.size_of_original()
    # The roots, then the scratch the routine uses after them, as the whole value would need.
    need = native._root_scratch(native.plan(cls), lazy.stop - lazy.start)
    area = bytearray(32 * count + need + 64)
    view = (ctypes.c_char * len(area)).from_buffer(area)
    holder = ctypes.c_char_p(lazy.encoding)
    source = ctypes.cast(holder, ctypes.c_void_p).value or 0
    words = ctypes.addressof(native._scratch().words)
    # The drivers answer no status: the routines load only where a kernel can hash.
    if _PLAN_PLAIN(element_plan):
        width = cls.ELEMENT_TYPE.get_byte_length()
        _ROOTS_CHUNKED(
            element_plan, source + lazy.start, width, count, ctypes.addressof(view), words
        )
    else:
        _ROOT_ELEMENTS(
            element_plan, source + lazy.start, size, count, ctypes.addressof(view), words
        )
    del view
    del area[32 * count :]
    return area
