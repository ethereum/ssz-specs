import SszNative.Proofs.Driver.Branch.Small

/-!
What the branch drivers' proofs take of the hashing driver, and the words the verifiers answer.

The hashing driver's own proof is separate: here its contract is a hypothesis.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.BranchProof

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm

/-- The word a verifier answers for a verdict or a refusal. -/
def answerCode : Except Err Bool → UInt64
  | .ok true => 1
  | .ok false => 0
  | .error (.notAGindex _) => 3
  | .error .rootHasNoBranch => 4
  | .error (.branchLength _ _) => 5
  | .error (.leafCount _ _) => 6
  | .error (.proofLength _ _) => 7
  | .error .emptyRequest => 8
  | .error .repeatedIndex => 9
  | .error (.nestedIndex _) => 10
  | .error .proofIncomplete => 11
  | .error _ => 255

/--
The contract of hashing one pair of nodes through the hashing driver, with a context in memory.

Memory holds a filled context while a predicate on it holds, and that predicate only reads addresses outside a free
set.
A call hashing one pair writes the digest to its output, leaves every other free address alone, and keeps the
context.
-/
structure PairHashing (m : Module) (w : World) (ctx : UInt64) (ready : Memory → Prop) (free : Nat → Prop)
    (room : Nat) : Prop where
  /-- One pair hashed from two nodes into a third place, all usable, the output free and apart from both. -/
  pair : ∀ (sp : Nat) (mem : Memory) (out left right : UInt64), ready mem → w.stackLo + room ≤ sp →
    w.access out.toNat 32 = true → w.access left.toNat 32 = true → w.access right.toNat 32 = true →
    (∀ k < 32, free (out.toNat + k)) → (∀ k < 32, free (left.toNat + k)) → (∀ k < 32, free (right.toNat + k)) →
    Apart (out.toNat, 32) (left.toNat, 32) → Apart (out.toNat, 32) (right.toNat, 32) →
    ∃ mem', Calls m w "ssz_hash_columns" sp [out, left, right, 1, ctx] mem 0 mem' ∧ ready mem' ∧
      (∀ k < 32, mem' (out.toNat + k) = (Cryptography.Hash.Sha256.hash (pairMessage mem left.toNat right.toNat)).get! k) ∧
      (∀ a, free a → ¬ (out.toNat ≤ a ∧ a < out.toNat + 32) → mem' a = mem a)
  /-- Writing only free addresses keeps the context. -/
  ready_frame : ∀ mem mem', ready mem → (∀ a, ¬ free a → mem' a = mem a) → ready mem'

/-- A digest written byte by byte reads back as that digest. -/
theorem readNode_digest {mem : Memory} {a : Nat} {d : ByteArray} (size : d.size = 32)
    (h : ∀ k < 32, mem (a + k) = d.get! k) : readNode mem a = d := by
  apply ByteArray.ext
  apply Array.ext
  · show (readNode mem a).size = d.size
    rw [readNode_size, size]
  · intro i hi _
    have bound : i < 32 := by simpa [readNode] using hi
    simp only [readNode, Array.getElem_ofFn]
    rw [h i bound, Kernel.get!_eq d i (by omega), ByteArray.getElem_eq_getElem_data]

/-- One pair hashed through the driver: the output reads back as the two nodes joined. -/
theorem PairHashing.pair_node {m : Module} {w : World} {ctx : UInt64} {ready : Memory → Prop} {free : Nat → Prop}
    {room : Nat} (hash : PairHashing m w ctx ready free room) {sp : Nat} {mem : Memory} {out left right : UInt64}
    (r : ready mem) (deep : w.stackLo + room ≤ sp) (ao : w.access out.toNat 32 = true)
    (al : w.access left.toNat 32 = true) (ar : w.access right.toNat 32 = true)
    (fo : ∀ k < 32, free (out.toNat + k)) (fl : ∀ k < 32, free (left.toNat + k))
    (fr : ∀ k < 32, free (right.toNat + k)) (pl : Apart (out.toNat, 32) (left.toNat, 32)) (pr : Apart (out.toNat, 32) (right.toNat, 32)) :
    ∃ mem', Calls m w "ssz_hash_columns" sp [out, left, right, 1, ctx] mem 0 mem' ∧ ready mem' ∧
      readNode mem' out.toNat = combine (readNode mem left.toNat) (readNode mem right.toNat) ∧
      (∀ a, free a → ¬ (out.toNat ≤ a ∧ a < out.toNat + 32) → mem' a = mem a) := by
  obtain ⟨mem', call, r', bytes, frame⟩ := hash.pair sp mem out left right r deep ao al ar fo fl fr pl pr
  -- The digest is 32 bytes, read back from where it was written.
  refine ⟨mem', call, r', ?_, frame⟩
  rw [combine_readNode]
  exact readNode_digest (Cryptography.Hash.Sha256.hash_size _) bytes

end EthLib.Consensus.Ssz.Native.Driver.BranchProof
