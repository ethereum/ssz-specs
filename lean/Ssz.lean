import Ssz.Hash.Sha256
import Ssz.Type.Desc
import Ssz.Type.Value
import Ssz.Type.Valid
import Ssz.Type.Default
import Ssz.Type.Paths
import Ssz.Codec.Error
import Ssz.Codec.Serialize
import Ssz.Codec.Deserialize
import Ssz.Codec.Layout
import Ssz.Codec.Json
import Ssz.Codec.Root
import Ssz.Codec.Proof
import Ssz.Merkle.Chunk
import Ssz.Merkle.Merkleize
import Ssz.Merkle.Tree
import Ssz.Merkle.Gindex
import Ssz.Merkle.Verify

/-!
# `Ssz`

The executable specification: everything an implementer reads.

    Ssz/Type    declarations, values, well-formedness, defaults, and paths
    Ssz/Codec   serialization, deserialization, layouts, roots, and proofs
    Ssz/Merkle  bounded and progressive trees, indices, and verification
    Ssz/Hash    pure SHA-256

Nothing here is a proof.

The properties proved of these definitions sit under `Ssz/Proofs`, mirroring this layout.
-/
