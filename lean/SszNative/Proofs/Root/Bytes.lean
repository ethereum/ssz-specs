import SszNative.Proofs.Root.Nodes

/-! Byte-level facts about copying into buffers, and about nodes read byte by byte. -/

namespace Ssz.Native

open Ssz

/-- Copying a range inside both arrays keeps the destination's size. -/
theorem copySlice_size (src dest : ByteArray) (so d len : Nat) (hs : so + len ≤ src.size) (hd : d + len ≤ dest.size) :
    (src.copySlice so dest d len).size = dest.size := by
  -- The copy replaces a range of the destination by a range of the same length.
  change (src.copySlice so dest d len).data.size = dest.data.size
  simp only [ByteArray.copySlice, Array.size_append, Array.size_extract]
  have : src.data.size = src.size := rfl
  have : dest.data.size = dest.size := rfl
  omega

/-- A byte after copying: from the source inside the copied range, from the destination elsewhere. -/
theorem copySlice_get (src dest : ByteArray) (so d len x : Nat) (hs : so + len ≤ src.size)
    (hd : d + len ≤ dest.size) (hx : x < dest.size) :
    (src.copySlice so dest d len).get! x = if d ≤ x ∧ x < d + len then src.get! (so + (x - d)) else dest.get! x := by
  -- Read the byte through the three parts the copy joins: before, the copied range, after.
  have ss : src.data.size = src.size := rfl
  have ds : dest.data.size = dest.size := rfl
  rw [Kernel.get!_eq _ _ (by rw [copySlice_size _ _ _ _ _ hs hd]; exact hx)]
  simp only [ByteArray.getElem_eq_getElem_data, ByteArray.copySlice]
  split
  -- Inside the copied range, the byte comes from the source.
  · rename_i inside
    rw [Kernel.get!_eq _ _ (by omega), ByteArray.getElem_eq_getElem_data]
    rw [Array.getElem_append_left (by simp only [Array.size_append, Array.size_extract]; omega),
      Array.getElem_append_right (by simp only [Array.size_extract]; omega)]
    simp only [Array.getElem_extract, Array.size_extract]
    congr 1
    omega
  -- Before or after the copied range, the byte is the destination's.
  · rename_i outside
    rw [Kernel.get!_eq _ _ hx, ByteArray.getElem_eq_getElem_data]
    by_cases before : x < d
    · rw [Array.getElem_append_left (by simp only [Array.size_append, Array.size_extract]; omega),
        Array.getElem_append_left (by simp only [Array.size_extract]; omega)]
      simp only [Array.getElem_extract, Nat.zero_add]
    · rw [Array.getElem_append_right (by simp only [Array.size_append, Array.size_extract]; omega)]
      simp only [Array.getElem_extract, Array.size_append, Array.size_extract]
      congr 1
      omega

/-- A node is the array of its bytes. -/
theorem nodeOf_of_get (a : ByteArray) (o k : Nat) (c : Bytes) (wide : c.size = 32) (inside : o + 32 * k + 32 ≤ a.size)
    (same : ∀ x < 32, a.get! (o + 32 * k + x) = c[x]!) : nodeOf a o k = c := by
  -- Two arrays of 32 bytes are equal byte by byte.
  apply Array.ext
  · rw [nodeOf_size a o k inside, wide]
  · intro x lx _
    have l32 : x < 32 := by rw [nodeOf_size a o k inside] at lx; exact lx
    have := same x l32
    rw [Kernel.get!_eq _ _ (by omega), getElem!_pos c x (by omega)] at this
    simp only [nodeOf, ByteArray.data_extract, Array.getElem_extract]
    rw [← this, ByteArray.getElem_eq_getElem_data]

/-- Byte x of a node is byte o + 32 k + x of its buffer. -/
theorem nodeOf_get (a : ByteArray) (o k x : Nat) (inside : o + 32 * k + 32 ≤ a.size) (lx : x < 32) :
    (nodeOf a o k)[x]! = a.get! (o + 32 * k + x) := by
  -- Node k from an offset starts 32 k bytes after the offset.
  rw [getElem!_pos _ x (by rw [nodeOf_size a o k inside]; exact lx), Kernel.get!_eq _ _ (by omega)]
  simp only [nodeOf, ByteArray.data_extract, Array.getElem_extract, ByteArray.getElem_eq_getElem_data]

end Ssz.Native
