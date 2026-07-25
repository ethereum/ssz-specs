"""
Fixed hash tree roots of the two progressive shapes, per EIP-7916.

Every root is written out in full, never computed from the tree it describes:

- A change to either tree shape fails here, whatever the rest of the suite does.
- Another implementation can check itself against these values directly.
"""

from __future__ import annotations

import pytest

from ssz import (
    Boolean,
    Container,
    ProgressiveBitlist,
    ProgressiveList,
    Uint8,
    Uint16,
    Uint64,
    Uint256,
)
from ssz.merkleization import hash_tree_root
from ssz.ssz_base import SSZType


class SingleFieldStruct(Container):
    """Smallest composite element there is: a container holding one byte."""

    a: Uint8


class Uint64ProgressiveList(ProgressiveList[Uint64]):
    """Progressive list of eight-byte elements, four to a chunk."""


class InnerUint64List(ProgressiveList[Uint64]):
    """Inner list of a nested progressive list, itself variable-size."""


class NestedProgressiveList(ProgressiveList[InnerUint64List]):
    """Progressive list whose elements are progressive lists, so bodies need offsets."""


class ProgressiveHolder(Container):
    """Container mixing a fixed field with both progressive shapes."""

    x: Uint64
    a: Uint64ProgressiveList
    b: ProgressiveBitlist


def root_hex(value: SSZType) -> str:
    """Return the hash tree root of a value as a 0x-prefixed hex string."""
    return "0x" + hash_tree_root(value).hex()


ZERO_MIXED_WITH_ZERO = "0xf5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"
"""Root every empty progressive value shares: the zero node with a zero length mixed in."""


@pytest.mark.parametrize(
    "element_count, expected_root",
    [
        (0, ZERO_MIXED_WITH_ZERO),
        (1, "0x905efb51c2764c2c7a4efb0548e372569df06db82115c3b1896c186632f3fe5b"),
        (2, "0x94f342b97f764e2548ea40cd9acfb1a1710ac0bb8b9cce202bfb99524256c53a"),
        (5, "0x209ec0633411cff6970c26380d214e30985d43dcc50509c1b3b28f615d333939"),
        (6, "0x997ce53709516289d7dee1a7b0bf74637cb08083648498b794c8d60fcb66e350"),
        (21, "0xcd2db52ac452ea0695ed3a34298b8562a6749f1ba683e8ffd8af2b97dd3a5dd1"),
        (22, "0x3d52e03c5b90a15ea15d5233f9a7068b363d5ea035751e540c925ba51f71ac05"),
        (31, "0x3e12b2d2b507ef7ffe70761d0b0b69af7a26449621227a7a3e06438917f4aebd"),
        (32, "0x77a8c5b3ec7b888068f0d2f0237b535b7ac6dc38c9ce75ed40a3bb6250537bc9"),
        (33, "0xbdb0c331db145d1efad9e022c70ab1f1c0896e7fc8bd8a83c6f0cd6ca89e1009"),
        (84, "0xce327a0dda6ad4e33af1e49c1168c5aa35dae66c8caee89d23ba7529734bdd50"),
        (85, "0x404664c320055384127dd62f6741a767a0396d9929720c29f7c20cc3333bd64e"),
        (86, "0xd31c2f59aad88de0a912daf3753246668f27450f1cdaf867e9f4fdbd8ee23099"),
    ],
)
def test_one_byte_element_roots(element_count: int, expected_root: str) -> None:
    """One-byte elements pack 32 to a chunk, so 32 and 33 straddle the first chunk."""
    # 33 elements: 32 bytes fill the first level, and byte 33 opens the second.
    values = [Uint8(i) for i in range(1, element_count + 1)]
    assert root_hex(ProgressiveList[Uint8](data=values)) == expected_root


@pytest.mark.parametrize(
    "element_count, expected_root",
    [
        (0, ZERO_MIXED_WITH_ZERO),
        (1, "0x905efb51c2764c2c7a4efb0548e372569df06db82115c3b1896c186632f3fe5b"),
        (2, "0x1311c18a7c020c910b000d55063dc15d23dc66bc6c4546685085661bbcbfa1c8"),
        (5, "0x894ec2b0088e5e82278042f8c492f3b764b6ff2e903bb0156334ba17c4805d38"),
        (6, "0x09de936790626c7a94b05d6e90337468cbac8c606a3b5914b84404a7a5184a69"),
        (16, "0x19f40551cc02da8ea0889141b4b6fb4063dd16893ac1c152659ed8e4c685a19e"),
        (17, "0xb7f2c26050a276c5dfc8bf1df8866864a7a6767bc61e3fa06ef225d1ff95e377"),
        (21, "0xeaee0b4e0f2ed266236046359d3631c32605d69973374ed651559c9393b8007e"),
        (22, "0x0adc5a948d8dae94466e3d151de6d0f24baa3bc82438a2694c4de227aa01be5d"),
        (84, "0x79ccccdf0b356533c85ee2ad69d4c3ded67521af5c2877cd3352c029c9806e81"),
        (85, "0x19fb9fa5cb654acc0e884ac1ee016edd1f7f4135088a9bea9e6a51132fc0a769"),
        (86, "0xbe135371387a9f497e53cefb8083dc8eb4042fb822943e39c898a026349e5df4"),
    ],
)
def test_two_byte_element_roots(element_count: int, expected_root: str) -> None:
    """Two-byte elements pack 16 to a chunk, so 16 and 17 straddle the first chunk."""
    # Counts stay under 256, so each element's value fits its width unchanged.
    values = [Uint16(i) for i in range(1, element_count + 1)]
    assert root_hex(ProgressiveList[Uint16](data=values)) == expected_root


@pytest.mark.parametrize(
    "element_count, expected_root",
    [
        (0, ZERO_MIXED_WITH_ZERO),
        (1, "0x905efb51c2764c2c7a4efb0548e372569df06db82115c3b1896c186632f3fe5b"),
        (2, "0x4250789d7838bee417a2b0d7639d928b05e8b75f1fc59588a4301b6e8f70ba58"),
        (3, "0x7e0adeccea8b17f07c3d1531a414d0b1f25543d5ddd519604ce30d5af83b1859"),
        (4, "0x95a2f252ed2659ccf75e8821f05757c4663fce68e89d0290abf5c33d772935ae"),
        (5, "0x29918e0447260511bc5be0f7dbb9817201e16e30c56af228b9cb931a16e8799d"),
        (6, "0xf4bdff2ee94b926f6db14f7e7dad2cb74b75ba057767b458d2c6c051d88e7dbf"),
        (7, "0xc1fbaac1b247e8871eb128eadd040aafbc9ef97ffaa1a7e68e75b376817b0072"),
        (16, "0x2073fec2e55f11505ebcb2ed417ece85cd6587677cabc78f352d3964b08a7edc"),
        (17, "0xb8ea7f9936e9093dd205cdeb70a459683bbf26c566193d70d6c7cd6ffcd76ef1"),
        (20, "0xc8a62a1a5fc7f814fafecb1d510213b25bda25425ab31c1ad7ff63c62c78307d"),
        (21, "0xed360c03ecbdfbb6f4b1cf5d9cbf6887038423e31121700797de968a9969aaed"),
        (22, "0x61f3eebb593ca31c113a9dfec164edea6d13272e20a5f8d0ab641c6e3e2222a9"),
        (31, "0x0162835d7e34f3c15ec0c77fa958da42391d4af1834c863395a0dd1164b20c03"),
        (32, "0x795f55932ee7d09843a4ea1b15278a9be78a2e724d8c4db44fbefbbe28b65b7d"),
        (33, "0x96f884d5f00694ee4f7a793eb76f78d1eff524e2724479ee4d34aaf8c96bf70f"),
        (84, "0x898e372f6bbc3baca40b0b736357fb2fb4badff01dffada10c725eeecf8cf9bd"),
        (85, "0xd6867a0b3368ebd6092807ac993865ecbc04e434ec41f8998152df59738705b5"),
        (86, "0x3197503e039fe2acfc88f0962c651c068bf069217bcf7a7efa8b3d0bc02473e6"),
    ],
)
def test_eight_byte_element_roots(element_count: int, expected_root: str) -> None:
    """Eight-byte elements pack four to a chunk, so 21 chunks arrive at 84 elements."""
    # 84 elements fill three levels exactly: chunks 1, 4, and 16 leave nothing over.
    values = [Uint64(i) for i in range(1, element_count + 1)]
    assert root_hex(Uint64ProgressiveList(data=values)) == expected_root


@pytest.mark.parametrize(
    "element_count, expected_root",
    [
        (0, ZERO_MIXED_WITH_ZERO),
        (1, "0x905efb51c2764c2c7a4efb0548e372569df06db82115c3b1896c186632f3fe5b"),
        (2, "0x0bf6848f5c62ed7241d5461b8b28ba0a433f49a205643b1460748b1441342f73"),
        (3, "0x8b9e13c85c24b0073f9b226ee291c1ff181f3652f42d2bcaeb26b3c302ec6004"),
        (4, "0xd3afed7f8ca8f9fad8990e6a57b66a024bd4b3fc9a7438ddb48d04dba43a509e"),
        (5, "0x472844f2f18e5c727d805241ad2f8f4f1d485cf8310602d9cf5dcf21ef8254dc"),
        (6, "0x76d03915aa777c431f6534cbd136b8f185b5df884546f52a8caa5db69ab49845"),
        (7, "0xdd36bb36b7f8ffadd270157ca7cf9f9c0e37075d5c9a45e5e986cd3fe8936c05"),
        (16, "0x0b1904fbab83131db4d3307087ac5d13ae98ac5e8c3787d7c4d6a8afa0e67c0f"),
        (17, "0x02675b51c91caf1e658e7f6fac7d3324575bacc836c0fc2439d9ba528e687552"),
        (20, "0xd0f00e7cb141fa84b50b86fcd351b41d0cfb76ec04aa1fa37d4eb094c2d2ff55"),
        (21, "0x47e0ab688eae3c1dbbb9623fadc55045accae121d492112724965f927f5d47ab"),
        (22, "0x4eb1861dc5959f6495a5daa997dcab85fcfeae76b0596aa32048be2cc221ded4"),
        (84, "0x5c67583fa321f102a5c1c15f207322e35cac921a91195bbcab13b17863cd1f79"),
        (85, "0xce4cd90414765a664070fdee5136e5dfb1eb16632f2a048b6afd5ec1e76965e1"),
        (86, "0x6455343caa59ff27ba38e2fa12f5107f3a9ecd1849ba4028d11daadb3b01649f"),
    ],
)
def test_full_chunk_element_roots(element_count: int, expected_root: str) -> None:
    """A 32-byte element fills one chunk, so the element count is the chunk count."""
    # The level boundaries land on the element counts 1, 5, 21, and 85 directly.
    values = [Uint256(i) for i in range(1, element_count + 1)]
    assert root_hex(ProgressiveList[Uint256](data=values)) == expected_root


@pytest.mark.parametrize(
    "element_count, expected_root",
    [
        (0, ZERO_MIXED_WITH_ZERO),
        (1, "0x905efb51c2764c2c7a4efb0548e372569df06db82115c3b1896c186632f3fe5b"),
        (5, "0x2e16bbdbce5094c911f42f217a5a44952af1f13da4a9e690cbd6a912f4cf36be"),
        (21, "0x9f44b96e629cf37c3f7eb9d6a585285cd038188109d914b5d0664e585786b9b9"),
        (32, "0x31527493633e0c31a7517365f827628a5f5aa6be90638093170c8283a4977b49"),
        (33, "0x00826e48669b1ff8d9e07a1c96c6b33ec5ad9f43a28a3006464faadd5d3ac6fd"),
    ],
)
def test_boolean_element_roots(element_count: int, expected_root: str) -> None:
    """A list of booleans packs one byte per element, unlike a bitlist's one bit."""
    # 33 booleans occupy 33 bytes and so two chunks, where 33 bits would occupy one.
    values = [Boolean(True)] * element_count
    assert root_hex(ProgressiveList[Boolean](data=values)) == expected_root


@pytest.mark.parametrize(
    "bit_count, expected_root",
    [
        (0, ZERO_MIXED_WITH_ZERO),
        (1, "0x905efb51c2764c2c7a4efb0548e372569df06db82115c3b1896c186632f3fe5b"),
        (2, "0x86cb388ccfae2de5e74bfe5634077e8bc4acb576db8ecbf8e71051b4475f8f6d"),
        (7, "0xcbfa55f6e94b1ce1e7b0b99306c6e6eefaf73b72bad6771a649ad290c341d6b2"),
        (8, "0x89b4e102035da473eaf22c286e07d433e11cbd721578e55111e6e3381e44a485"),
        (9, "0x3310d92ea95acd2753e76d449bd1cdbc90ba8ce90b6e7e51435cf88a5c11436e"),
        (15, "0xe70feb85f03f1a360637d23c19f3bd61c984c91cca2779c8aad0d5beb9de0e53"),
        (16, "0xf179b07e7f4669b3dcfb43ade4dc1e282c93fc067335342a980ae4591effb274"),
        (17, "0xcb7cd8596cd874d78e5277f81fc7969602781e28a9cc62f4f3abcff6c41e9b31"),
        (31, "0x0fefda6b9225394900be8af39a36cd60ffbb5eabb67318f5657e17dfe0c97e59"),
        (32, "0xd5ba948dcd79a17be3729ffb16e828a4454e6305cc8ac3a2f9438dc4e8fbe08a"),
        (33, "0x5287d9780dddc42441b94f24b09277278c23255ec530ecf87dc00f0ab4717bf5"),
        (63, "0xa5bddbc8fb0f6ebf82209ec39b91d308e38541f2d8cc9706db30f042c0582627"),
        (64, "0x33cb4d646deff716256d55a4b3872d920ffc48f13788ba79c3458854a5481e2e"),
        (65, "0xa1954d46261a829b0980d14fab8da8ebd5fcf619be99a892f6734d3e3d55a028"),
        (255, "0x00cacf1c674080785f369fa130134dcafc883203b8374decb9e6b18e5b4125b1"),
        (256, "0xb3327406854ffab96af59832dfa3f690f72c4f898e2ffd4ef3e90cc2fb876b43"),
        (257, "0xbe707c375a49431fdb06c00f7a4dcc9200d5613ea02999dc5e081913171bb8d0"),
        (511, "0x6030f9b956cb7cfb79784bac5205288f842b57c851609be7a266cc7889b9de06"),
        (512, "0xfedaba4d354436ef8a8e13f141fe0d39abafb2be19ae6488eb5abd4a37a071f6"),
        (513, "0xe1863d142701b924caf6e92f887f7f53059e9b63d08d7f02d66ca27f0ed228fc"),
    ],
)
def test_all_true_bitlist_roots(bit_count: int, expected_root: str) -> None:
    """
    Set bits at every byte and chunk boundary.

    The 256-bit case is the sharpest of them:

    - It serializes to 33 bytes, because the delimiter opens a byte of its own.
    - It packs into one chunk, because the delimiter never enters the tree.
    """
    # The delimiter is what makes the byte count and the chunk count disagree here.
    assert root_hex(ProgressiveBitlist(data=[Boolean(True)] * bit_count)) == expected_root


@pytest.mark.parametrize(
    "bit_count, expected_root",
    [
        (1, "0xe832d263aaa8f9417d9f45a702834f6961ee7b15ad4d3d27f2b0f4fe79d33031"),
        (2, "0x3ddf8417d70d875b60aa9f5123aae329c09d6768333e16529f6137c3e29586b7"),
        (7, "0xaee3ade668fe1043101f3bff93e4bd815a12664e4e96bf541d18c2442d657b45"),
        (8, "0xa5c83a46d8c0edb422b9b9b550fd13f925b84a8d4d10aa9e59bf08e9631ef1de"),
        (9, "0x9732a0f5dafad5e70b0938b5977814bea2564098253184e4ea2ab8e55b4609f2"),
        (16, "0xc4185e57368dbc5eb687ca30cbd1b1c51556e5a3a1d4c2eb5f685d2191d4685d"),
        (17, "0x41f9d716cea4a4b5b7481656f2f6fdcec09810714e5f809afbd742bac315fb90"),
        (32, "0xeab3687b1f782861a068080861319a42da0d702ba314a312312ca7d39e9f104f"),
        (33, "0xb0308e796252895a73c6a0b3a1c4373104ddb61c9a629a83a9b2d6857fba29a5"),
        (255, "0x9cec765fc332d4327b2a8cc6e8293b7d1bf63f5acdb5f012f23f4f94d4e3eaf1"),
        (256, "0x044881ec6cd8401c76de75e9e830a92c7f831c4cd1c07b77539e53b0dfa68587"),
        (257, "0xb458d2fffeaa2b0341cf44f4a31cf4d1754e56096ef0fb81ccc7d237f90b041c"),
        (512, "0x7542b5135236f9e898cf93a682f731608ac59fe28bdc16a4b34502c102d4b47e"),
        (513, "0x21c5f9d1c3705672282c1c88187ca01c95f35fb0f1898c4af25576999de4a6f7"),
    ],
)
def test_alternating_bitlist_roots(bit_count: int, expected_root: str) -> None:
    """Bits alternate starting from clear, which catches a reversed packing order."""
    # Bit i lands at position i, so a reversed packing shifts every byte of the payload.
    bits = [Boolean(index % 2) for index in range(bit_count)]
    assert root_hex(ProgressiveBitlist(data=bits)) == expected_root


@pytest.mark.parametrize(
    "element_count, expected_root",
    [
        (0, ZERO_MIXED_WITH_ZERO),
        (1, "0x905efb51c2764c2c7a4efb0548e372569df06db82115c3b1896c186632f3fe5b"),
        (2, "0x0bf6848f5c62ed7241d5461b8b28ba0a433f49a205643b1460748b1441342f73"),
        (5, "0x472844f2f18e5c727d805241ad2f8f4f1d485cf8310602d9cf5dcf21ef8254dc"),
        (6, "0x76d03915aa777c431f6534cbd136b8f185b5df884546f52a8caa5db69ab49845"),
        (21, "0x47e0ab688eae3c1dbbb9623fadc55045accae121d492112724965f927f5d47ab"),
        (22, "0x4eb1861dc5959f6495a5daa997dcab85fcfeae76b0596aa32048be2cc221ded4"),
    ],
)
def test_composite_element_roots(element_count: int, expected_root: str) -> None:
    """
    Composite elements contribute one leaf each, so the leaf count is the element count.

    These roots match the 32-byte-element list at the same count.
    A one-byte container roots to the same padded chunk a small integer packs into.
    """
    # No packing step here: each element hands its own root to the tree as a leaf.
    elements = [SingleFieldStruct(a=Uint8(i)) for i in range(1, element_count + 1)]
    assert root_hex(ProgressiveList[SingleFieldStruct](data=elements)) == expected_root


def test_nested_progressive_list_vector() -> None:
    """
    A progressive list of progressive lists needs an offset table for its bodies.

    Layout, with the empty inner list contributing no body at all:

        bytes 0..3   : off_0 = 12   (first body starts at byte 12)
        bytes 4..7   : off_1 = 28   (second body starts at byte 28)
        bytes 8..11  : off_2 = 28   (third body starts where the second ended)
        bytes 12..27 : body_0       (two eight-byte elements)
        bytes 28..35 : body_2       (one eight-byte element)

    The two equal offsets are legal.
    An empty body has zero width, so offsets are non-decreasing, not strictly increasing.
    """
    value = NestedProgressiveList(
        data=[
            InnerUint64List(data=[Uint64(1), Uint64(2)]),
            InnerUint64List(data=[]),
            InnerUint64List(data=[Uint64(3)]),
        ]
    )
    expected_bytes = "0c0000001c0000001c000000010000000000000002000000000000000300000000000000"
    assert value.encode_bytes().hex() == expected_bytes
    assert NestedProgressiveList.decode_bytes(value.encode_bytes()) == value
    assert root_hex(value) == "0x5c7cf403ba442047fc83d723043514a5c0f8e9f22b048bbc8191bed49c6a6f94"


def test_container_holding_both_progressive_shapes_vector() -> None:
    """
    A container reaches its progressive fields through offsets, as for any variable-size field.

    Layout:

        bytes 0..7   : x = 7        (fixed-size field, inline)
        bytes 8..11  : off_a = 16   (list body starts at byte 16)
        bytes 12..15 : off_b = 40   (bitlist body starts at byte 40)
        bytes 16..39 : a body       (three eight-byte elements)
        byte  40     : b body       (three bits plus the delimiter)
    """
    value = ProgressiveHolder(
        x=Uint64(7),
        a=Uint64ProgressiveList(data=[Uint64(1), Uint64(2), Uint64(3)]),
        b=ProgressiveBitlist(data=[Boolean(True), Boolean(False), Boolean(True)]),
    )
    expected_bytes = (
        "070000000000000010000000280000000100000000000000020000000000000003000000000000000d"
    )
    assert value.encode_bytes().hex() == expected_bytes
    assert ProgressiveHolder.decode_bytes(value.encode_bytes()) == value
    assert root_hex(value) == "0x4d7b2d321882a440e729af4dd579ead329397efa0e61c6e1eeb5fa848a9e8f4e"
