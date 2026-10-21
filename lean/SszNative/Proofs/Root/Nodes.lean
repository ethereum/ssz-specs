import SszNative.Tree
import SszNative.Proofs.Reference
import Ssz.Proofs.Merkle.Tree
import Ssz.Proofs.Merkle.Widths
import Ssz.Proofs.Merkle.Authentication

/-! Buffers of 32-byte nodes read as the specification's arrays of nodes, and the hashing kernels on them. -/

namespace Ssz.Native

open Ssz

/-- Node i of a buffer, counting from a byte offset. -/
def nodeOf (b : ByteArray) (offset i : Nat) : Bytes :=
  (b.extract (offset + 32 * i) (offset + 32 * i + 32)).data

/-- A count of nodes of a buffer from a byte offset, as the specification's array of nodes. -/
def nodesFrom (b : ByteArray) (offset count : Nat) : Array Bytes :=
  Array.ofFn (n := count) fun i => nodeOf b offset i.val

/-- The array has one entry per node read. -/
@[simp] theorem nodesFrom_size (b : ByteArray) (offset count : Nat) : (nodesFrom b offset count).size = count := by
  simp [nodesFrom]

/-- A node of the array read from a buffer, or none past its count. -/
theorem nodesFrom_get? (b : ByteArray) (offset count i : Nat) :
    (nodesFrom b offset count)[i]? = if i < count then some (nodeOf b offset i) else none := by
  -- Inside the count the entry is the node, and past it there is none.
  by_cases inside : i < count <;> simp [nodesFrom, inside]

/-- A node inside its buffer is 32 bytes wide. -/
theorem nodeOf_size (b : ByteArray) (offset i : Nat) (inside : offset + 32 * i + 32 ≤ b.size) :
    (nodeOf b offset i).size = 32 := by
  -- The slice is 32 bytes when it lies inside the buffer.
  simp only [nodeOf, ByteArray.data_extract, Array.size_extract, ByteArray.size_data]
  omega

/-- Moving the offset by whole nodes renumbers them. -/
theorem nodeOf_shift (b : ByteArray) (offset k i : Nat) :
    nodeOf b (offset + 32 * k) i = nodeOf b offset (k + i) := by
  -- Node i after k whole nodes starts where node k + i does.
  simp only [nodeOf]
  rw [show offset + 32 * k + 32 * i = offset + 32 * (k + i) by omega]

/-- Every node of a buffer's prefix is 32 bytes wide. -/
theorem nodesFrom_complete (b : ByteArray) (offset count : Nat) (inside : offset + 32 * count ≤ b.size) :
    ∀ chunk ∈ nodesFrom b offset count, chunk.size = bytesPerChunk := by
  intro chunk mem
  -- Each entry is a node read inside the buffer.
  obtain ⟨i, lt, rfl⟩ := Array.mem_iff_getElem.mp mem
  simp only [nodesFrom, Array.getElem_ofFn]
  exact nodeOf_size b offset i (by simp at lt; have := Nat.mul_le_mul_left 32 lt; omega)

/-- Bytes equal, one by one, to a whole array are that array. -/
theorem extract_of_get (a c : ByteArray) (o : Nat) (inside : o + c.size ≤ a.size)
    (same : ∀ k < c.size, a.get! (o + k) = c.get! k) : a.extract o (o + c.size) = c := by
  -- Equal sizes and equal bytes at every position make equal arrays.
  apply ByteArray.ext
  apply Array.ext
  · change (a.extract o (o + c.size)).size = c.size
    rw [ByteArray.size_extract]
    omega
  · intro k left right
    simp only [ByteArray.data_extract, Array.getElem_extract]
    have kc : k < c.size := right
    have := same k kc
    rw [Kernel.get!_eq _ _ (by omega), Kernel.get!_eq _ _ kc] at this
    simpa [ByteArray.getElem_eq_getElem_data] using this

/-- A byte offset that fits a machine word survives the conversion to one. -/
theorem toUSize_toNat (n : Nat) (small : n < USize.size) : n.toUSize.toNat = n :=
  USize.toNat_ofNat_of_lt' small

/-- The machine word zero, as the conversion of the number zero. -/
theorem usize_zero : (0 : USize) = (0 : Nat).toUSize := rfl

/-- Two adjacent nodes, as one 64-byte slice. -/
theorem extract_pair (b : ByteArray) (o : Nat) :
    ByteArray.mk ((b.extract o (o + 32)).data ++ (b.extract (o + 32) (o + 64)).data) = b.extract o (o + 64) := by
  apply ByteArray.ext
  -- Two adjacent slices of one array join into the slice they span.
  rw [ByteArray.data_extract, ByteArray.data_extract, ByteArray.data_extract, Array.extract_append_extract,
    Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)]

/-- The parent of pair p of a level, from the kernel that hashes adjacent pairs. -/
theorem hashPairs_node (src : ByteArray) (offset pairs p : Nat) (pair : p < pairs)
    (inside : offset + 64 * pairs ≤ src.size) (small : src.size < USize.size) :
    nodeOf (hashPairs src offset.toUSize pairs.toUSize) 0 p =
      combine (nodeOf src offset (2 * p)) (nodeOf src offset (2 * p + 1)) := by
  -- The offsets and the count fit machine words, so the conversions lose nothing.
  have ho := toUSize_toNat offset (by omega)
  have hn := toUSize_toNat pairs (by omega)
  -- The reference writes the digest of pair p as its node p.
  have node : (hashPairs src offset.toUSize pairs.toUSize).extract (32 * p) (32 * p + 32) =
      Sha256.hash (src.extract (offset + 64 * p) (offset + 64 * p + 64)) := by
    have := extract_of_get (hashPairs src offset.toUSize pairs.toUSize)
      (Sha256.hash (src.extract (offset + 64 * p) (offset + 64 * p + 64))) (32 * p)
      (by simp only [Sha256.hash_size, hashPairs, hashPairsReference_size, hn]; omega)
      (fun k within => by
        simp only [Sha256.hash_size] at within
        simp only [hashPairs]
        rw [hashPairsReference_get _ _ _ p k (by omega) within, ho])
    simpa only [Sha256.hash_size] using this
  -- The parent is the specification's combination of the two adjacent nodes.
  simp only [nodeOf, Nat.zero_add, node, combine]
  rw [show offset + 32 * (2 * p) = offset + 64 * p by omega,
    show offset + 32 * (2 * p + 1) = offset + 64 * p + 32 by omega,
    show offset + 64 * p + 32 + 32 = offset + 64 * p + 64 by omega, extract_pair]

/-- The parent of node p of a column against one fixed node. -/
theorem hashFixed_node (left : ByteArray) (offset count p : Nat) (node : ByteArray) (record : p < count)
    (inside : offset + 32 * count ≤ left.size) (small : left.size < USize.size) (wide : node.size = 32) :
    nodeOf (hashFixed left offset.toUSize node count.toUSize) 0 p = combine (nodeOf left offset p) node.data := by
  -- The offsets and the count fit machine words, so the conversions lose nothing.
  have ho := toUSize_toNat offset (by omega)
  have hn := toUSize_toNat count (by omega)
  -- The fixed node is 32 bytes, so the kernel reads all of it.
  have whole : node.extract 0 32 = node := by
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    have : node.data.size = 32 := wide
    rw [← this, Array.extract_size]
  -- The reference writes the digest of node p and the fixed node as its node p.
  have parent : (hashFixed left offset.toUSize node count.toUSize).extract (32 * p) (32 * p + 32) =
      Sha256.hash (left.extract (offset + 32 * p) (offset + 32 * p + 32) ++ node.extract 0 32) := by
    have := extract_of_get (hashFixed left offset.toUSize node count.toUSize)
      (Sha256.hash (left.extract (offset + 32 * p) (offset + 32 * p + 32) ++ node.extract 0 32)) (32 * p)
      (by simp only [Sha256.hash_size, hashFixed, hashFixedReference_size, hn]; omega)
      (fun k within => by
        simp only [Sha256.hash_size] at within
        simp only [hashFixed]
        rw [hashFixedReference_get _ _ _ _ p k (by omega) within, ho])
    simpa only [Sha256.hash_size] using this
  -- The parent is the specification's combination of the node and the fixed node.
  simp only [nodeOf, Nat.zero_add, parent, combine, whole]
  congr 2
  apply ByteArray.ext
  rw [ByteArray.data_append]

/-- The parent of node p of two columns. -/
theorem hashColumns_node (left : ByteArray) (lo : Nat) (right : ByteArray) (ro count p : Nat) (record : p < count)
    (leftInside : lo + 32 * count ≤ left.size) (rightInside : ro + 32 * count ≤ right.size)
    (leftSmall : left.size < USize.size) (rightSmall : right.size < USize.size) :
    nodeOf (hashColumns left lo.toUSize right ro.toUSize count.toUSize) 0 p =
      combine (nodeOf left lo p) (nodeOf right ro p) := by
  -- The offsets and the count fit machine words, so the conversions lose nothing.
  have hl := toUSize_toNat lo (by omega)
  have hr := toUSize_toNat ro (by omega)
  have hn := toUSize_toNat count (by omega)
  -- The reference writes the digest of the two nodes p as its node p.
  have parent : (hashColumns left lo.toUSize right ro.toUSize count.toUSize).extract (32 * p) (32 * p + 32) =
      Sha256.hash (left.extract (lo + 32 * p) (lo + 32 * p + 32) ++ right.extract (ro + 32 * p) (ro + 32 * p + 32)) := by
    have := extract_of_get (hashColumns left lo.toUSize right ro.toUSize count.toUSize)
      (Sha256.hash (left.extract (lo + 32 * p) (lo + 32 * p + 32) ++ right.extract (ro + 32 * p) (ro + 32 * p + 32)))
      (32 * p)
      (by simp only [Sha256.hash_size, hashColumns, hashColumnsReference_size, hn]; omega)
      (fun k within => by
        simp only [Sha256.hash_size] at within
        simp only [hashColumns]
        rw [hashColumnsReference_get _ _ _ _ _ p k (by omega) within, hl, hr])
    simpa only [Sha256.hash_size] using this
  -- The parent is the specification's combination of the two nodes.
  simp only [nodeOf, Nat.zero_add, parent, combine]
  congr 2
  apply ByteArray.ext
  rw [ByteArray.data_append]

/-- The kernels write one node per parent. -/
theorem hashPairs_size (src : ByteArray) (offset pairs : Nat) (small : pairs < USize.size) :
    (hashPairs src offset.toUSize pairs.toUSize).size = 32 * pairs := by
  -- The reference writes 32 bytes per parent.
  simp only [hashPairs, hashPairsReference_size, toUSize_toNat pairs small]

/-- Hashing a column against one node gives one node per entry. -/
theorem hashFixed_size (left : ByteArray) (offset count : Nat) (node : ByteArray) (small : count < USize.size) :
    (hashFixed left offset.toUSize node count.toUSize).size = 32 * count := by
  -- The reference writes 32 bytes per parent.
  simp only [hashFixed, hashFixedReference_size, toUSize_toNat count small]

/-- Hashing two columns gives one node per pair of entries. -/
theorem hashColumns_size (left : ByteArray) (lo : Nat) (right : ByteArray) (ro count : Nat)
    (small : count < USize.size) :
    (hashColumns left lo.toUSize right ro.toUSize count.toUSize).size = 32 * count := by
  -- The reference writes 32 bytes per parent.
  simp only [hashColumns, hashColumnsReference_size, toUSize_toNat count small]

/-- A node of two buffers joined end to end comes from the one it falls in. -/
theorem nodeOf_append_left (a b : ByteArray) (i : Nat) (inside : 32 * i + 32 ≤ a.size) :
    nodeOf (a ++ b) 0 i = nodeOf a 0 i := by
  -- The node ends inside the first buffer, so nothing of the second is read.
  simp only [nodeOf, Nat.zero_add, ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
  have : 32 * i + 32 - a.data.size = 0 := by change 32 * i + 32 - a.size = 0; omega
  rw [this, Array.extract_eq_empty_of_le (as := b.data) (by omega), Array.append_empty]

/-- A node past the first buffer of two, when that buffer holds whole nodes, comes from the second. -/
theorem nodeOf_append_right (a b : ByteArray) (i : Nat) (whole : a.size = 32 * i) :
    nodeOf (a ++ b) 0 i = nodeOf b 0 0 := by
  -- The first buffer ends exactly where the node starts.
  simp only [nodeOf, Nat.zero_add, Nat.mul_zero, ByteArray.data_extract, ByteArray.data_append,
    Array.extract_append]
  have w : a.data.size = 32 * i := whole
  rw [w, Array.extract_eq_empty_of_le (by rw [w]; omega), Array.empty_append, Nat.sub_self,
    show 32 * i + 32 - 32 * i = 32 by omega]

end Ssz.Native
