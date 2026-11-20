import SszNative.Proofs.Driver.Prove.SpineWalk
import SszNative.Proofs.Driver.Prove.Branch
import SszNative.Proofs.Driver.Prove.Multiproof
import SszNative.Proofs.Driver.Prove.Budget
import SszNative.Proofs.Driver.Prove.Slot
import SszNative.Proofs.Driver.Prove.Layout
import SszNative.Proofs.Driver.Prove.Leaves
import SszNative.Proofs.Driver.Prove.Bounded
import SszNative.Proofs.Driver.Prove.Spine
import SszNative.Proofs.Driver.Prove.Progressive
import SszNative.Proofs.Driver.Prove.Scratch
import SszNative.Proofs.Driver.Prove.Discharge
import SszNative.Proofs.Driver.Prove.Need
import SszNative.Proofs.Driver.Prove.NodeAt
import SszNative.Proofs.Driver.Prove.Entry

/-!
The compiled drivers that build nodes, branches, and multiproofs compute what the Lean walk computes.

    Prove/Small        powers of two and right shifts by a counted number of places
    Prove/SpineWalk    the walk down a progressive spine
    Prove/Branch       the branch of one index, from the contract of the walk to one node
    Prove/Multiproof   the nodes of several indices, from the same contract
    Prove/Budget       the Lean walk reads the same node at every budget covering the type's nesting
    Prove/Slot         the value at one position under a tree, from the layout record
    Prove/Layout       the layout record of every type, as the Lean layout describes it
    Prove/Leaves       the leaves of a tree from one position to another, from the contracts of the root calls
    Prove/Bounded      the Lean walk inside a bounded subtree, and what the bounded walk needs
    Prove/Spine        the progressive root of a run of nodes, from a later first level
    Prove/Progressive  the Lean walk inside a progressive tree, from the contracts the bounded walk takes
    Prove/Scratch      the prover's scratch bound, computed as the Lean bound
    Prove/Discharge    the root calls under a layout, from the root drivers and the range decoding accepts
    Prove/Need         the scratch each level of the walk needs, and how the prover's bound covers it
    Prove/NodeAt       the walk to a node of every type, by induction on its nesting, and its contract discharged
    Prove/Entry        the node, branch and multiproof builders, with the walk proved
-/
