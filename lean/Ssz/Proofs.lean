import Ssz
import Ssz.Proofs.Audit
import Ssz.Proofs.Type.Compatibility
import Ssz.Proofs.Type.CompatibilityIndices
import Ssz.Proofs.Type.CompatibilitySymmetry
import Ssz.Proofs.Type.DefaultLaws
import Ssz.Proofs.Type.Equality
import Ssz.Proofs.Type.FitsLaws
import Ssz.Proofs.Type.PathLaws
import Ssz.Proofs.Type.PathSteps
import Ssz.Proofs.Codec.Admits
import Ssz.Proofs.Codec.Aliases
import Ssz.Proofs.Codec.Binding
import Ssz.Proofs.Codec.BindingChildren
import Ssz.Proofs.Codec.BindingCongruence
import Ssz.Proofs.Codec.BindingDomain
import Ssz.Proofs.Codec.BindingLayout
import Ssz.Proofs.Codec.BindingLayoutInjectivity
import Ssz.Proofs.Codec.BindingLeafShape
import Ssz.Proofs.Codec.BindingLeaves
import Ssz.Proofs.Codec.BindingPacking
import Ssz.Proofs.Codec.BindingShape
import Ssz.Proofs.Codec.BindingTrace
import Ssz.Proofs.Codec.BindingTraceLaws
import Ssz.Proofs.Codec.BranchConstruction
import Ssz.Proofs.Codec.Canonical
import Ssz.Proofs.Codec.CanonicalBits
import Ssz.Proofs.Codec.CanonicalComposite
import Ssz.Proofs.Codec.CanonicalStruct
import Ssz.Proofs.Codec.CanonicalTable
import Ssz.Proofs.Codec.Canonicality
import Ssz.Proofs.Codec.DecodeFits
import Ssz.Proofs.Codec.Fits
import Ssz.Proofs.Codec.Layout
import Ssz.Proofs.Codec.JsonHex
import Ssz.Proofs.Codec.JsonLaws
import Ssz.Proofs.Codec.LayoutLaws
import Ssz.Proofs.Codec.LayoutMixin
import Ssz.Proofs.Codec.LayoutProofTree
import Ssz.Proofs.Codec.LengthBinding
import Ssz.Proofs.Codec.MultiproofConstruction
import Ssz.Proofs.Codec.NestedProof
import Ssz.Proofs.Codec.NodeWidths
import Ssz.Proofs.Codec.PathDescent
import Ssz.Proofs.Codec.PathDomain
import Ssz.Proofs.Codec.PathProof
import Ssz.Proofs.Codec.PathSelection
import Ssz.Proofs.Codec.PathSlots
import Ssz.Proofs.Codec.PathValues
import Ssz.Proofs.Codec.ProgressiveClosure
import Ssz.Proofs.Codec.ProgressiveIndex
import Ssz.Proofs.Codec.ProgressiveProofTree
import Ssz.Proofs.Codec.Proof
import Ssz.Proofs.Codec.ProofBudget
import Ssz.Proofs.Codec.ProofCorrectness
import Ssz.Proofs.Codec.ProofTree
import Ssz.Proofs.Codec.RootDomain
import Ssz.Proofs.Codec.RootLaws
import Ssz.Proofs.Codec.RoundTrip
import Ssz.Proofs.Codec.RoundTripComposite
import Ssz.Proofs.Codec.RoundTripScalar
import Ssz.Proofs.Codec.RoundTripSlices
import Ssz.Proofs.Codec.Size
import Ssz.Proofs.Codec.Summary
import Ssz.Proofs.Codec.Table
import Ssz.Proofs.Codec.Totality
import Ssz.Proofs.Codec.WalkerClosure
import Ssz.Proofs.Codec.WalkerLaws
import Ssz.Proofs.Merkle.Authentication
import Ssz.Proofs.Merkle.CommitmentTree
import Ssz.Proofs.Merkle.Gindex
import Ssz.Proofs.Merkle.HelperAntichain
import Ssz.Proofs.Merkle.HelperFrontier
import Ssz.Proofs.Merkle.HelperUniqueness
import Ssz.Proofs.Merkle.Merkleize
import Ssz.Proofs.Merkle.Multiproof
import Ssz.Proofs.Merkle.MultiproofAcceptance
import Ssz.Proofs.Merkle.MultiproofBinding
import Ssz.Proofs.Merkle.MultiproofClaims
import Ssz.Proofs.Merkle.MultiproofTrace
import Ssz.Proofs.Merkle.MultiproofTree
import Ssz.Proofs.Merkle.Tree
import Ssz.Proofs.Merkle.Verify
import Ssz.Proofs.Merkle.Widths
import Ssz.Proofs.Flat.Bounded
import Ssz.Proofs.Flat.Fold
import Ssz.Proofs.Flat.Walk
import Ssz.Proofs.Hash.Sha256Constants
import Ssz.Proofs.Hash.Sha256Laws
import Ssz.Proofs.Hash.Sha256Spec

/-!
# `Ssz.Proofs`

Machine-checked properties of the executable specification.

The proofs about `Ssz.Foo.Bar` live in `Ssz.Proofs.Foo.Bar`.

Reading them is no prerequisite for implementing SSZ.

`README.md` says in prose what they establish.

A Lake library of its own compiles them, and the specification does not depend on it.
-/

-- The audit runs after the whole specification is imported, so a new proof module needs no entry.
audit_ssz
