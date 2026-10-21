import Ssz.Hash.Sha256

/-!
Hashing pairs of nodes, the one operation every Merkle tree is built from.

Each definition here has a Lean body, which is the reference.
Compiled code runs the native kernels in its place, which compute the same function.
-/

namespace Ssz.Native

/--
The parents of consecutive pairs of 32-byte nodes.

Pair i is the 64 bytes at offset + 64i, and its parent is their SHA-256 digest.
Bytes past the end of the source read as missing, which shortens the message.
-/
@[export ssz_native_hash_pairs_reference]
def hashPairsReference (src : ByteArray) (offset pairs : USize) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (32 * pairs.toNat)
  for i in [0:pairs.toNat] do
    let start := offset.toNat + 64 * i
    out := out ++ Sha256.hash (src.extract start (start + 64))
  return out

/-- The parents of consecutive pairs of nodes, on the native kernels where the processor has them. -/
@[extern "ssz_native_hash_pairs"]
def hashPairs (src : @& ByteArray) (offset pairs : USize) : ByteArray :=
  hashPairsReference src offset pairs

/--
The parents of two columns of nodes: parent i hashes left node i followed by right node i.

Node i of a column is the 32 bytes at its offset + 32i.
-/
@[export ssz_native_hash_columns_reference]
def hashColumnsReference (left : ByteArray) (leftOffset : USize) (right : ByteArray)
    (rightOffset : USize) (count : USize) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (32 * count.toNat)
  for i in [0:count.toNat] do
    let l := leftOffset.toNat + 32 * i
    let r := rightOffset.toNat + 32 * i
    out := out ++ Sha256.hash (left.extract l (l + 32) ++ right.extract r (r + 32))
  return out

/-- The parents of two columns of nodes, on the native kernels where the processor has them. -/
@[extern "ssz_native_hash_columns"]
def hashColumns (left : @& ByteArray) (leftOffset : USize) (right : @& ByteArray) (rightOffset : USize)
    (count : USize) : ByteArray :=
  hashColumnsReference left leftOffset right rightOffset count

/-- The parents of a column of nodes, each hashed with one fixed node on its right. -/
@[export ssz_native_hash_fixed_reference]
def hashFixedReference (left : ByteArray) (leftOffset : USize) (node : ByteArray) (count : USize) :
    ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (32 * count.toNat)
  for i in [0:count.toNat] do
    let l := leftOffset.toNat + 32 * i
    out := out ++ Sha256.hash (left.extract l (l + 32) ++ node.extract 0 32)
  return out

/-- The parents of a column of nodes against one fixed node, on the native kernels where the processor has them. -/
@[extern "ssz_native_hash_fixed"]
def hashFixed (left : @& ByteArray) (leftOffset : USize) (node : @& ByteArray) (count : USize) : ByteArray :=
  hashFixedReference left leftOffset node count

/--
A field of each of a count of records, each copied into a slot of zeros.

Field i is the width bytes at start + stride * i, and slot i is the slot bytes at slot * i.
-/
@[export ssz_native_gather_reference]
def gatherReference (src : ByteArray) (start stride width count slot : USize) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (count.toNat * slot.toNat)
  for i in [0:count.toNat] do
    let s := start.toNat + stride.toNat * i
    let field := src.extract s (s + min width.toNat slot.toNat)
    out := out ++ field ++ ⟨Array.replicate (slot.toNat - field.size) 0⟩
  return out

/-- A field of each of a count of records, each in a slot of zeros, on the native kernel where there is one. -/
@[extern "ssz_native_gather"]
def gather (src : @& ByteArray) (start stride width count slot : USize) : ByteArray :=
  gatherReference src start stride width count slot

/-- The parent of two 32-byte nodes. -/
@[inline] def hashPair (left right : ByteArray) : ByteArray :=
  hashPairs (left ++ right) 0 1

end Ssz.Native
