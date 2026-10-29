import SszNative.Proofs.Driver.Branch.Bridge
import SszNative.Proofs.Driver.Branch.VerifyMultiproof

/-!
The compiled branch and multiproof verifiers answer what the Lean verifiers answer.

    Branch/Common          words, nodes, and the reasoning rules the driver proofs use
    Branch/Small           the level of an index, the search for a word, and the node comparison
    Branch/Hashing         what the proofs take of one hashed pair, and the words the verifiers answer
    Branch/Bridge          that contract, from the proved hashing drivers and a filled context
    Branch/VerifyBranch    the branch verifier
    Branch/Paths           the index checks and helper indices, in the shape the loops compute them
    Branch/Claims          the claim check
    Branch/Helpers         the path walk and the candidate walk
    Branch/Select          the selection of distinct candidates, largest first
    Branch/HelperIndices   the helper indices
    Branch/FoldSpec        one fold level as two passes
    Branch/Copy            copying a node
    Branch/FoldKept        the second pass
    Branch/FoldParents     the first pass
    Branch/MultiSpec       the multiproof verifier in the compiled verifier's steps
    Branch/MultiFold       the fold loop
    Branch/MultiBuild      the node set and its deepest level
    Branch/VerifyMultiproof  the multiproof verifier
-/
