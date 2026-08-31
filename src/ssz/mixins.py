"""
The words a shape hashes its contents against, and the mixing itself.

Each is built at the chunk width, which yields exactly that width or raises.
"""

from collections.abc import Sequence
from hashlib import sha256

from ssz.chunks import BYTES_PER_CHUNK, Chunk, Root
from ssz.exceptions import SSZValueError, ValueFault


def mix_in(root: Root, word: Chunk) -> Root:
    """Hash a subtree root against the word its shape mixes in, as the right child."""
    # Invariant: a digest is exactly the chunk width.
    return Root._trusted(sha256(root + word).digest())


def length_word(length: int) -> Chunk:
    """
    The element count a variable-size shape mixes in, as one 32-byte little-endian word.

    Raises:
        SSZValueError: A negative length.
    """
    if length < 0:
        raise SSZValueError(ValueFault.NEGATIVE_LENGTH, length=length)
    return Chunk._trusted(length.to_bytes(BYTES_PER_CHUNK, "little"))


def active_fields_word(active_fields: Sequence[int]) -> Chunk:
    """
    The field layout a progressive container mixes in, as one 32-byte word.

    One bit per position, lowest bit first, so at most 256 fit, a bound the type enforces:

        [1, 0, 1]  ->  05 00 00 ... 00
    """
    packed_bits = sum(1 << i for i, bit in enumerate(active_fields) if bit)
    return Chunk._trusted(packed_bits.to_bytes(BYTES_PER_CHUNK, "little"))


def selector_word(selector: int) -> Chunk:
    """
    The option selector a compatible union mixes in, as one 32-byte word.

    The spec writes one byte, and a hash operand is one chunk, so it is zero-extended:

        selector 1  ->  01 00 00 ... 00

    Raises:
        SSZValueError: A selector that does not fit one byte.
    """
    if not 0 <= selector <= 0xFF:
        raise SSZValueError(ValueFault.SELECTOR_BYTE, selector=selector)
    return Chunk._trusted(selector.to_bytes(BYTES_PER_CHUNK, "little"))


def mix_in_length(root: Root, length: int) -> Root:
    """
    Mix a length into a Merkle root via the SSZ uint256 little-endian encoding.

    Two lists of identical elements under different lengths must root differently.

    Raises:
        SSZValueError: A negative length.
    """
    return mix_in(root, length_word(length))


def mix_in_active_fields(root: Root, active_fields: Sequence[int]) -> Root:
    """Mix a layout in, per EIP-7495, so a dropped field and a zeroed one differ."""
    return mix_in(root, active_fields_word(active_fields))


def mix_in_selector(root: Root, selector: int) -> Root:
    """
    Mix a type selector into a Merkle root, per EIP-8016.

    Mixing it in separates options that would otherwise root alike:

    - Two options holding equal data.
    - Two differing only in a list's element type, while that list is empty.

    Raises:
        SSZValueError: A selector that does not fit one byte.
    """
    return mix_in(root, selector_word(selector))
