import SszNative.Root
import SszNative.Proofs.Reference
import SszNative.Proofs.Validate.Main
import Ssz.Proofs.Codec.NodeWidths

/-! Byte buffers of nodes, read as the specification's arrays of nodes. -/

namespace Ssz.Native.RootProof

open Ssz Ssz.Native

/-- The count nodes of a buffer from a byte offset, as the specification's array of nodes. -/
def nodesFrom (nodes : ByteArray) (offset count : Nat) : Array Bytes :=
  Array.ofFn (n := count) fun i => (nodes.extract (offset + 32 * i.val) (offset + 32 * i.val + 32)).data

/-- Two byte arrays are equal when they agree byte by byte. -/
theorem ext_get! (a b : ByteArray) (size : a.size = b.size) (same : ∀ i < a.size, a.get! i = b.get! i) :
    a = b := by
  -- Equal sizes and equal bytes at every position make equal arrays.
  apply ByteArray.ext
  apply Array.ext (by simpa using size)
  intro i ia ib
  have := same i (by simpa using ia)
  rwa [Kernel.get!_eq a i (by simpa using ia), Kernel.get!_eq b i (by simpa using ib)] at this

/-- The parent of two nodes is the specification's combination of them. -/
theorem hashPair_data (left right : ByteArray) (l : left.size = 32) (r : right.size = 32) :
    (hashPair left right).data = combine left.data right.data := by
  -- Both nodes are 32 bytes, so the pair is exactly 64 bytes.
  have ld : left.data.size = 32 := l
  have rd : right.data.size = 32 := r
  have whole : (left ++ right).extract 0 64 = left ++ right := by
    apply ByteArray.ext
    simp only [ByteArray.data_extract, ByteArray.data_append]
    rw [Array.extract_append, ld, Array.extract_eq_self_of_le (by omega), Array.extract_eq_self_of_le (by omega)]
  -- One pair at offset zero: the digest of the 64 bytes.
  have sized : (hashPair left right).size = 32 := by
    simp [hashPair, hashPairs, hashPairsReference_size]
  have parent : hashPair left right = Sha256.hash (left ++ right) := by
    apply ext_get! _ _ (by rw [sized, Sha256.hash_size])
    intro k within
    rw [sized] at within
    have := hashPairsReference_get (left ++ right) 0 1 0 k (by simp) within
    simp only [Nat.mul_zero, Nat.zero_add, USize.toNat_zero] at this
    simp only [hashPair, hashPairs]
    rw [this, whole]
  -- The kernel's digest of the joined pair is the specification's combination.
  rw [parent, combine]
  exact congrArg (fun x => (Sha256.hash x).data) (ByteArray.ext (ByteArray.data_append ..))

/-- A buffer of zeros holds zeros. -/
theorem zeros_data (n : Nat) (small : n < USize.size) : (zeros n).data = Array.replicate n 0 := by
  -- A gather of an empty field into one slot is that many zero bytes.
  have toNat : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' small
  have sized : (zeros n).size = n := by
    simp [zeros, gather, gatherReference_size, toNat]
  have bytes : zeros n = ⟨Array.replicate n 0⟩ := by
    apply ext_get! _ _ (by rw [sized]; simp [ByteArray.size])
    intro k within
    rw [sized] at within
    have := gatherReference_get ByteArray.empty 0 0 0 1 n.toUSize 0 k (by simp) (by rw [toNat]; exact within)
      (by simp) (by simp)
    simp only [toNat, Nat.mul_zero, USize.toNat_zero, Nat.not_lt_zero, if_false, Nat.zero_add] at this
    simp only [zeros, gather]
    rw [this, Kernel.get!_eq _ _ (by simp [ByteArray.size]; exact within)]
    simp [ByteArray.getElem_eq_getElem_data]
  rw [bytes]

/-- Thirty-two bytes from a position of data followed by zeros are the data's piece there, zero-padded. -/
theorem extract_padded (data : Bytes) (z s : Nat) (fit : s + 32 ≤ data.size + z) :
    (data ++ Array.replicate z (0 : UInt8)).extract s (s + 32) =
      data.extract s (s + 32) ++ Array.replicate (32 - (data.extract s (s + 32)).size) 0 := by
  -- Inside the data the bytes are the data's, and past it they are zeros.
  apply Array.ext
  · simp; omega
  · intro j hl hr
    simp only [Array.size_extract, Array.size_append, Array.size_replicate] at hl
    simp only [Array.getElem_extract, Array.getElem_append, Array.getElem_replicate, Array.size_extract]
    split <;> split <;> first | rfl | omega

/-- Data followed by enough zeros holds, node by node, the data packed into nodes. -/
theorem nodes_padded (data : Bytes) (z : Nat) (fit : 32 * chunksForBytes data.size ≤ data.size + z) :
    nodesFrom ⟨data ++ Array.replicate z 0⟩ 0 (chunksForBytes data.size) = packBytes data := by
  -- Both sides hold one node per 32 bytes, rounded up.
  apply Array.ext
  · simp [nodesFrom, packBytes, chunksForBytes]
  · intro i hl hr
    simp only [nodesFrom, packBytes, Array.getElem_ofFn, ByteArray.data_extract, Nat.zero_add]
    have : i < chunksForBytes data.size := by simpa [nodesFrom] using hl
    rw [show i * bytesPerChunk = 32 * i by simp [bytesPerChunk, Nat.mul_comm]]
    exact extract_padded data z (32 * i) (by simp [chunksForBytes] at *; omega)

/-- A packed range is its bytes followed by zeros. -/
theorem packRange_data (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (small : stop - start + 64 < USize.size) :
    (packRange b start stop).data =
      b.data.extract start stop ++ Array.replicate (32 * nodesFor (stop - start) + 32 - (stop - start)) 0 := by
  -- The copy puts the range at the start of a buffer of zeros.
  simp only [packRange, ByteArray.copySlice]
  rw [zeros_data _ (by simp [nodesFor]; omega)]
  simp only [Nat.zero_add, Array.size_replicate]
  have inside' : b.data.size = b.size := rfl
  rw [show min (stop - start) (b.data.size - start) = stop - start by omega,
    show start + (stop - start) = stop by omega]
  simp [Array.extract_replicate]

/-- A packed range holds, node by node, its bytes packed into nodes. -/
theorem packRange_nodes (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (small : stop - start + 64 < USize.size) :
    nodesFrom (packRange b start stop) 0 (nodesFor (stop - start)) = packBytes (slice b start stop) ∧
      (packRange b start stop).size = 32 * nodesFor (stop - start) + 32 := by
  -- The packed range is the range's bytes followed by zeros.
  have data := packRange_data b start stop ordered inside small
  have sized : (b.data.extract start stop).size = stop - start := by simp; omega
  constructor
  -- The bytes then pack node by node exactly as the specification packs the slice.
  · have : packRange b start stop = ⟨b.data.extract start stop ++
        Array.replicate (32 * nodesFor (stop - start) + 32 - (stop - start)) 0⟩ := ByteArray.ext data
    rw [this, show nodesFor (stop - start) = chunksForBytes (b.data.extract start stop).size by
      simp [sized, nodesFor, chunksForBytes]]
    apply nodes_padded
    simp [chunksForBytes, sized]
    omega
  -- The buffer holds the whole nodes and one spare node.
  · rw [← ByteArray.size_data, data]
    simp [sized, nodesFor]
    omega

/-- The bytes of a list of buffers, back to back. -/
def concatData : List ByteArray → Bytes
  | [] => #[]
  | r :: rs => r.data ++ concatData rs

/-- Buffers appended one after another hold their bytes in order. -/
theorem foldl_append_data (rs : List ByteArray) (init : ByteArray) :
    (rs.foldl (· ++ ·) init).data = init.data ++ concatData rs := by
  induction rs generalizing init with
  -- Appending each buffer in turn appends its bytes.
  | nil => simp [concatData]
  | cons r rs ih => simp [concatData, ih, ByteArray.data_append, Array.append_assoc]

/-- Nodes joined end to end take 32 bytes each. -/
theorem concatData_size (rs : List ByteArray) (sized : ∀ r ∈ rs, r.size = 32) :
    (concatData rs).size = 32 * rs.length := by
  induction rs with
  -- Each node adds 32 bytes.
  | nil => simp [concatData]
  | cons r rs ih =>
    simp only [concatData, Array.size_append, ByteArray.size_data, List.length_cons]
    rw [sized r (by simp), ih fun x m => sized x (by simp [m])]
    omega

/-- Node i of a run of joined nodes is the i-th node of the run. -/
theorem concatData_extract (rs : List ByteArray) (sized : ∀ r ∈ rs, r.size = 32) (i : Nat)
    (within : i < rs.length) : (concatData rs).extract (32 * i) (32 * i + 32) = rs[i].data := by
  induction rs generalizing i with
  -- Node zero is the first buffer, and node i + 1 is node i of the rest.
  | nil => simp at within
  | cons r rs ih =>
    have rd : r.data.size = 32 := sized r (by simp)
    simp only [concatData, Array.extract_append, rd]
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.zero_add, Nat.zero_sub, List.getElem_cons_zero]
      rw [Array.extract_eq_self_of_le (by omega)]
      simp
    | succ i =>
      simp only [List.getElem_cons_succ]
      rw [Array.extract_empty_of_size_le_start (by omega), Array.empty_append,
        show 32 * (i + 1) - 32 = 32 * i by omega, show 32 * (i + 1) + 32 - 32 = 32 * i + 32 by omega]
      exact ih (fun x m => sized x (by simp [m])) i (by simpa using within)

/-- Joined nodes hold, node by node, the buffers joined. -/
theorem joinNodes_nodes (rs : List ByteArray) (sized : ∀ r ∈ rs, r.size = 32) :
    nodesFrom (joinNodes rs) 0 rs.length = (rs.map ByteArray.data).toArray ∧
      (joinNodes rs).size = 32 * rs.length := by
  -- Joining nodes appends their bytes to an empty buffer.
  have data : (joinNodes rs).data = concatData rs := by
    simp [joinNodes, foldl_append_data, ByteArray.emptyWithCapacity]
    rfl
  constructor
  -- Node i of the joined buffer is the i-th buffer.
  · apply Array.ext
    · simp [nodesFrom]
    · intro i hl _
      have within : i < rs.length := by simpa [nodesFrom] using hl
      simp only [nodesFrom, Array.getElem_ofFn, ByteArray.data_extract, data, Nat.zero_add]
      rw [concatData_extract rs sized i within]
      simp
  -- Each joined node takes 32 bytes.
  · rw [← ByteArray.size_data, data, concatData_size rs sized]

end Ssz.Native.RootProof
