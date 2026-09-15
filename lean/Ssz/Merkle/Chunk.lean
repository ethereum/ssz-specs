/-! Tree nodes, and the fold that joins two of them. -/

namespace Ssz

/--
Width of a tree node in bytes.

The specification fixes it at the width of the hash output.
-/
abbrev bytesPerChunk : Nat :=
  32

/-- Width of a tree node in bits. -/
abbrev bitsPerChunk : Nat :=
  8 * bytesPerChunk

/-- One node of a Merkle tree, with its width carried in the type. -/
abbrev Chunk :=
  Vector UInt8 bytesPerChunk

/-- The node an absent leaf contributes. -/
def Chunk.zero : Chunk :=
  Vector.replicate bytesPerChunk 0

/--
Folding two child nodes into their parent.

No proof below inspects it, so nothing already proven depends on which hash is used.
-/
abbrev Combine :=
  Chunk → Chunk → Chunk

end Ssz
