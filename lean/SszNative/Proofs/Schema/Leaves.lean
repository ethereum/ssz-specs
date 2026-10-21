import SszNative.Schema
import SszNative.Proofs.Root.Fixed

/-! A compiled struct's leaves are the leaves the general root writes. -/

namespace Ssz.Native

open Ssz

/-- One step of writing a struct's leaves: the next leaf copied into the next node. -/
def fillStep (b : ByteArray) (acc : ByteArray × Nat) (leaf : Leaf) : ByteArray × Nat :=
  let (buffer, node) := acc
  match leaf with
  | .bytes offset width => (b.copySlice offset buffer (32 * node) width, node + 1)
  | .nested d offset width => ((rootsOf d b offset width 1).copySlice 0 buffer (32 * node) 32, node + 1)

/-- The zero buffer the leaves are written into, for a count of leaves. -/
def leafBuffer (count : Nat) : ByteArray :=
  let size := 32 * count + 32
  if size ≤ zeroLeaves.size then zeroLeaves.extract 0 size else zeros size

/-- Writing leaves is the step above, from the zero buffer. -/
theorem fillLeaves_eq (b : ByteArray) (leaves : Array Leaf) :
    fillLeaves b leaves = (leaves.foldl (fillStep b) (leafBuffer leaves.size, 0)).1 := rfl

/-- Walking a struct's compiled leaves writes what the general root writes, one field at a time. -/
theorem foldl_leavesOf (b : ByteArray) :
    ∀ (fields : List Desc) (offset : Nat) (buffer : ByteArray) (node : Nat),
      (leavesOf fields offset).foldl (fillStep b) (buffer, node) =
        (fieldLeaves fields b 0 offset buffer node, node + fields.length)
  | [], _, buffer, node => by
    -- No fields write nothing.
    simp [leavesOf, fieldLeaves]
  | field :: rest, offset, buffer, node => by
    -- The first field is written the same way, then the rest from the next node.
    rw [leavesOf, List.foldl_cons, fieldLeaves]
    by_cases packs : packsIntoNode field = true
    · simp only [packs, if_true, fillStep, Nat.zero_add]
      rw [foldl_leavesOf b rest]
      simp only [List.length_cons]
      congr 1
      omega
    · simp only [packs, Bool.false_eq_true, if_false, fillStep, Nat.zero_add]
      rw [foldl_leavesOf b rest]
      simp only [List.length_cons]
      congr 1
      omega

/-- Two buffers of the same size that read the same everywhere are equal. -/
theorem eq_of_get! (a c : ByteArray) (size : a.size = c.size) (same : ∀ x < a.size, a.get! x = c.get! x) : a = c := by
  -- Equal sizes and equal bytes at every position make equal arrays.
  apply ByteArray.ext
  apply Array.ext
  · exact size
  · intro x la lc
    have := same x la
    rw [Kernel.get!_eq _ _ la, Kernel.get!_eq _ _ (by rw [← size]; exact la)] at this
    simpa [ByteArray.getElem_eq_getElem_data] using this

/-- The buffer leaves are written into is the zero buffer of that size. -/
theorem leafBuffer_eq (count : Nat) (small : 32 * count + 32 < USize.size) :
    leafBuffer count = zeros (32 * count + 32) := by
  simp only [leafBuffer]
  split
  · -- A slice of the cached zeros is zeros too.
    rename_i fits
    have cached := zeros_spec (32 * 65) (Nat.lt_of_lt_of_le (by decide) USize.le_size)
    have fresh := zeros_spec (32 * count + 32) small
    have cachedSize : zeroLeaves.size = 32 * 65 := cached.1
    apply eq_of_get!
    · rw [ByteArray.size_extract, fresh.1]
      rw [cachedSize] at fits ⊢
      omega
    · intro x lx
      rw [ByteArray.size_extract] at lx
      rw [fresh.2 x (by omega)]
      -- Byte x of the slice is byte x of the cached zeros.
      rw [Kernel.get!_eq _ _ (by rw [ByteArray.size_extract]; omega)]
      have inside : x < zeroLeaves.size := by rw [cachedSize] at fits ⊢; omega
      have zero : zeroLeaves.get! x = 0 := cached.2 x (by rw [← cachedSize]; exact inside)
      rw [Kernel.get!_eq _ _ inside] at zero
      simpa [ByteArray.getElem_eq_getElem_data] using zero
  · rfl

end Ssz.Native
