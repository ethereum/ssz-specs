import Ssz.Proofs.Audit
import Asm.Sha256.Proof
import Asm.Sha256.PairMain
import Asm.Merkle.Main
import Asm.Exec.Root

/-!
# `Asm`

RISC-V kernels for SSZ, each proved against the executable specification.

    Asm/Machine, Block, Flow, Memory, Frame   the RV64I model and how to reason about it
    Asm/Sha256                                SHA-256 compression, and the hash of two nodes
    Asm/Merkle                                Merkleization of a run of chunks
    Asm/Root                                  hash plans for fixed-size types, from their encoding
    Asm/Exec                                  the routine that runs a hash plan
    Asm/Emit                                  GNU assembler output
-/

-- Every kernel proof rests on the standard axioms only, like the rest of the specification.
audit_ssz
