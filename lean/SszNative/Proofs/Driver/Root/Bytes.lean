import SszNative.Proofs.Driver.Gather
import SszNative.Proofs.Reference
import SszNative.Proofs.Root.Nodes

/-!
Memory after a gather or a hashing run, read as the buffer the Lean reference returns.

The drivers work on memory, and the Lean root computation on buffers.
A buffer sits in memory when every one of its bytes is there, from some address.
Each kernel's memory then holds, at its output, exactly the buffer the reference computes from the buffers it read.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm

/-! ### Buffers in memory -/

/-- Memory holds the bytes it is read as. -/
theorem holds_bytesAt (mem : Memory) (a n : Nat) : Holds mem a (bytesAt mem a n) := by
  intro i hi
  have hn : i < n := by simpa [bytesAt, ByteArray.size] using hi
  rw [Kernel.get!_eq _ _ hi]
  simp [bytesAt, ByteArray.getElem_eq_getElem_data]

/-- The bytes read from where memory holds a buffer, as many as it has, are the buffer. -/
theorem bytesAt_of_holds {mem : Memory} {a n : Nat} {bytes : ByteArray} (size : bytes.size = n)
    (h : Holds mem a bytes) : bytesAt mem a n = bytes := by
  subst size
  apply ByteArray.ext
  apply Array.ext
  · simp only [bytesAt, Array.size_ofFn]; rfl
  · intro i h1 h2
    have hi : i < bytes.size := by simpa [bytesAt] using h1
    simp only [bytesAt, Array.getElem_ofFn]
    rw [h i hi, Kernel.get!_eq _ _ hi, ByteArray.getElem_eq_getElem_data]

/-- A buffer stays in memory that agrees with the old memory on its bytes. -/
theorem _root_.EthLib.Consensus.Ssz.Native.Holds.congr {m₁ m₂ : Memory} {a : Nat} {bytes : ByteArray} (h : Holds m₁ a bytes)
    (same : ∀ i < bytes.size, m₂ (a + i) = m₁ (a + i)) : Holds m₂ a bytes :=
  fun i hi => by rw [same i hi, h i hi]

/-- A buffer in memory holds its tail from further on. -/
theorem _root_.EthLib.Consensus.Ssz.Native.Holds.drop {mem : Memory} {a : Nat} {bytes : ByteArray} (h : Holds mem a bytes) (k : Nat) :
    Holds mem (a + k) (bytes.extract k bytes.size) := by
  intro i hi
  rw [ByteArray.size_extract] at hi
  rw [Nat.add_assoc, h _ (by omega), Kernel.get!_eq _ _ (by omega), Kernel.get!_eq _ _ (by rw [ByteArray.size_extract]; omega),
    ByteArray.getElem_extract]

/-- Memory holding a buffer of whole nodes reads, at each node's place, the buffer's node. -/
theorem nodeAt_of_holds {mem : Memory} {a : Nat} {bytes : ByteArray} (h : Holds mem a bytes) {i : Nat}
    (inside : 32 * i + 32 ≤ bytes.size) : nodeAt mem (a + 32 * i) = nodeOf bytes 0 i := by
  apply Array.ext
  · simp [nodeAt, nodeOf]; omega
  · intro k h1 h2
    have hk : k < 32 := by simpa [nodeAt] using h1
    simp only [nodeAt, Array.getElem_ofFn, nodeOf, Nat.zero_add, ByteArray.data_extract, Array.getElem_extract]
    rw [Nat.add_assoc, h _ (by omega), Kernel.get!_eq _ _ (by omega), ByteArray.getElem_eq_getElem_data]

/-- Memory holds a buffer of whole nodes when it reads, at each node's place, the buffer's node. -/
theorem holds_of_nodes {mem : Memory} {a count : Nat} {bytes : ByteArray} (size : bytes.size = 32 * count)
    (h : ∀ i < count, nodeAt mem (a + 32 * i) = nodeOf bytes 0 i) : Holds mem a bytes := by
  intro x hx
  have hi : x / 32 < count := by omega
  have hk : x % 32 < 32 := Nat.mod_lt _ (by decide)
  have node := congrArg (fun arr : Bytes => arr[x % 32]!) (h (x / 32) hi)
  rw [getElem!_pos _ _ (by simp [nodeAt]; exact hk), getElem!_pos _ _ (by
    simp [nodeOf]; omega)] at node
  simp only [nodeAt, Array.getElem_ofFn, nodeOf, Nat.zero_add, ByteArray.data_extract, Array.getElem_extract] at node
  rw [show a + 32 * (x / 32) + x % 32 = a + x by omega] at node
  simp only [show 32 * (x / 32) + x % 32 = x by omega] at node
  rw [node, Kernel.get!_eq _ _ hx, ByteArray.getElem_eq_getElem_data]

/-! ### Gathers -/

/--
Memory after gathering a field of each record holds, at the output, the reference gather of the records' buffer.

The records start at a byte of a buffer in memory, one stride apart, and each field lies inside the buffer.
The skip is the stride less the width, and the pad the slot less the width.
-/
theorem holds_gathered {mem : Memory} {base : Nat} {b : ByteArray} (holds : Holds mem base b)
    (out start stride width count slot : Nat) (fits : width ≤ slot) (gap : width ≤ stride)
    (inside : ∀ i < count, start + stride * i + width ≤ b.size)
    (hs : start < USize.size) (hd : stride < USize.size) (hw : width < USize.size) (hc : count < USize.size)
    (hl : slot < USize.size) :
    Holds (gathered mem out (base + start) count width (stride - width) (slot - width)) out
      (gatherReference b start.toUSize stride.toUSize width.toUSize count.toUSize slot.toUSize) := by
  intro x hx
  rw [gatherReference_size, toUSize_toNat _ hc, toUSize_toNat _ hl] at hx
  -- The byte sits in some slot, at some place in it.
  have pos : 0 < slot := Nat.pos_of_ne_zero fun h => by subst h; simp at hx
  obtain ⟨i, k, rfl, hk⟩ : ∃ i k, x = slot * i + k ∧ k < slot :=
    ⟨x / slot, x % slot, (Nat.div_add_mod x slot).symm, Nat.mod_lt x pos⟩
  have hi : i < count := Nat.lt_of_not_le fun c => by
    have := Nat.mul_le_mul_left slot c
    rw [Nat.mul_comm count slot] at hx; omega
  have ref := gatherReference_get b start.toUSize stride.toUSize width.toUSize count.toUSize slot.toUSize i k
    (by rw [toUSize_toNat _ hc]; exact hi) (by rw [toUSize_toNat _ hl]; exact hk)
    (by rw [toUSize_toNat _ hl, toUSize_toNat _ hw]; exact fits)
    (by rw [toUSize_toNat _ hs, toUSize_toNat _ hd, toUSize_toNat _ hw]; exact inside _ hi)
  simp only [toUSize_toNat _ hs, toUSize_toNat _ hd, toUSize_toNat _ hw, toUSize_toNat _ hl] at ref
  rw [ref]
  -- Inside the output, the gathered byte is the record's byte or a zero.
  have slotEq : width + (slot - width) = slot := by omega
  have strideEq : width + (stride - width) = stride := by omega
  have byte := Kernel.recordByte_at mem out (base + start) width (stride - width) (slot - width) i k (by omega)
  rw [slotEq, strideEq] at byte
  have below : slot * i + k < slot * count := by
    have := Nat.mul_le_mul_left slot (show i + 1 ≤ count by omega)
    rw [Nat.mul_succ] at this; omega
  simp only [gathered]
  rw [ite_eq_left ⟨by omega, by rw [slotEq]; omega⟩, ← Nat.add_assoc, byte]
  split
  · rw [show base + start + stride * i + k = base + (start + stride * i + k) by omega,
      holds _ (by have := inside _ hi; omega)]
  · rfl

/-! ### Hashing runs -/

/-- Memory after hashing adjacent pairs holds, at the output, the reference parents of the buffer they lie in. -/
theorem holds_hashed_pairs {mem : Memory} {base : Nat} {src : ByteArray} (holds : Holds mem base src)
    (out offset pairs : Nat) (inside : offset + 64 * pairs ≤ src.size) (ho : offset < USize.size)
    (hp : pairs < USize.size) :
    Holds (hashed mem out (base + offset) (base + offset + 32) pairs 64 64) out
      (hashPairsReference src offset.toUSize pairs.toUSize) := by
  intro x hx
  rw [hashPairsReference_size, toUSize_toNat _ hp] at hx
  have split : x = 32 * (x / 32) + x % 32 := (Nat.div_add_mod x 32).symm
  have hq : x / 32 < pairs := by omega
  have hk : x % 32 < 32 := Nat.mod_lt x (by decide)
  rw [split, hashPairsReference_get _ _ _ _ _ (by rw [toUSize_toNat _ hp]; exact hq) hk, toUSize_toNat _ ho,
    ← Nat.add_assoc, hashed_inside hq hk]
  -- Pair p is the 64 bytes of the buffer at offset + 64 p.
  rw [show base + offset + 32 + 64 * (x / 32) = base + (offset + 64 * (x / 32)) + 32 by omega,
    show base + offset + 64 * (x / 32) = base + (offset + 64 * (x / 32)) by omega,
    pairMessage_adjacent mem base src _ holds (by omega)]

/-- Memory after hashing two columns pairwise holds, at the output, the reference parents of their buffers. -/
theorem holds_hashed_columns {mem : Memory} {lb rb : Nat} {left right : ByteArray} (hl : Holds mem lb left)
    (hr : Holds mem rb right) (out lo ro count : Nat) (li : lo + 32 * count ≤ left.size)
    (ri : ro + 32 * count ≤ right.size) (hlo : lo < USize.size) (hro : ro < USize.size) (hc : count < USize.size) :
    Holds (hashed mem out (lb + lo) (rb + ro) count 32 32) out
      (hashColumnsReference left lo.toUSize right ro.toUSize count.toUSize) := by
  intro x hx
  rw [hashColumnsReference_size, toUSize_toNat _ hc] at hx
  have split : x = 32 * (x / 32) + x % 32 := (Nat.div_add_mod x 32).symm
  have hq : x / 32 < count := by omega
  have hk : x % 32 < 32 := Nat.mod_lt x (by decide)
  rw [split, hashColumnsReference_get _ _ _ _ _ _ _ (by rw [toUSize_toNat _ hc]; exact hq) hk, toUSize_toNat _ hlo,
    toUSize_toNat _ hro, ← Nat.add_assoc, hashed_inside hq hk, Nat.add_assoc, Nat.add_assoc]
  -- Parent p hashes node p of each column.
  rw [pairMessage_holds mem lb rb left right _ _ hl hr (by omega) (by omega)]

/-- Memory after hashing a column against one node holds, at the output, the reference parents. -/
theorem holds_hashed_fixed {mem : Memory} {lb nb : Nat} {left node : ByteArray} (hl : Holds mem lb left)
    (hn : Holds mem nb node) (out lo count : Nat) (li : lo + 32 * count ≤ left.size) (ni : 32 ≤ node.size)
    (hlo : lo < USize.size) (hc : count < USize.size) :
    Holds (hashed mem out (lb + lo) nb count 32 0) out (hashFixedReference left lo.toUSize node count.toUSize) := by
  intro x hx
  rw [hashFixedReference_size, toUSize_toNat _ hc] at hx
  have split : x = 32 * (x / 32) + x % 32 := (Nat.div_add_mod x 32).symm
  have hq : x / 32 < count := by omega
  have hk : x % 32 < 32 := Nat.mod_lt x (by decide)
  rw [split, hashFixedReference_get _ _ _ _ _ _ (by rw [toUSize_toNat _ hc]; exact hq) hk, toUSize_toNat _ hlo,
    ← Nat.add_assoc, hashed_inside hq hk, Nat.add_assoc, Nat.zero_mul, Nat.add_zero]
  -- Parent p hashes node p of the column, then the fixed node.
  rw [pairMessage_fixed mem lb nb left node _ hl hn (by omega) ni]

end EthLib.Consensus.Ssz.Native.Driver
