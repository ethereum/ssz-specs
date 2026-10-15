import Asm.Frame
import Asm.Sha256.PairMain
import Asm.Merkle.Layout
import Asm.Merkle.Levels

/-! The states the routine passes through, and the facts every one of them shares. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Merkle

open Ssz.Asm.Sha256 (sp t0 t1 a0 a1 a2 savedSlots pairCode workRegs)

/-- Chunk j of a buffer, as the 32 bytes at offset 32j. -/
def chunkAt (m : Machine) (buf : BitVec 64) (j : Nat) : Bytes :=
  (m.bytes (buf + BitVec.ofNat 64 (32 * j)) 32).data

/-- The stack frame's base, below the caller's stack pointer. -/
def base (m0 : Machine) : BitVec 64 :=
  m0.read sp - BitVec.ofNat 64 frameSize

/-- The chunk buffer's address. -/
def buffer (m0 : Machine) : BitVec 64 :=
  m0.read a0

/-- The number of input chunks. -/
def count (m0 : Machine) : Nat :=
  (m0.read a1).toNat

/-- The tree's depth. -/
def depth (m0 : Machine) : Nat :=
  (m0.read a2).toNat

/-- The zero-hash table's address. -/
def zeros (m0 : Machine) : BitVec 64 :=
  m0.read a3

/-- The input chunks. -/
def leaves (m0 : Machine) : List Bytes :=
  (List.range (count m0)).map (chunkAt m0 (buffer m0))

/-- Bytes of buffer the routine may write: the input, or one chunk for the root when there is none. -/
def capacity (m0 : Machine) : Nat :=
  32 * max (count m0) 1

/-- What a caller must provide. -/
structure Valid (m0 : Machine) : Prop where
  /-- Buffer offsets fit comfortably in 64 bits. -/
  small : 32 * (count m0 + 2) < 2 ^ 62
  /-- Table offsets fit comfortably in 64 bits. -/
  shallow : 32 * (depth m0 + 1) < 2 ^ 62
  /-- The buffer and the frame share no byte. -/
  bufferFrame : Disjoint (buffer m0) (capacity m0) (base m0) frameSize
  /-- The table and the frame share no byte. -/
  zerosFrame : Disjoint (zeros m0) (32 * (depth m0 + 1)) (base m0) frameSize
  /-- The table and the buffer share no byte. -/
  zerosBuffer : Disjoint (zeros m0) (32 * (depth m0 + 1)) (buffer m0) (capacity m0)
  /-- Entry k of the table is the zero subtree of height k. -/
  table : ∀ k, k ≤ depth m0 → chunkAt m0 (zeros m0) k = zeroAt k

/-- The facts every state of the routine shares, after the frame is open. -/
structure Steady (m0 : Machine) (m : Machine) : Prop where
  /-- The stack pointer sits at the frame's base. -/
  stack : m.read sp = base m0
  /-- The buffer's address is in its slot. -/
  bufferStored : m.load (base m0 + BitVec.ofNat 64 bufSlot) 8 = buffer m0
  /-- The depth is in its slot. -/
  depthStored : m.load (base m0 + BitVec.ofNat 64 depthSlot) 8 = m0.read a2
  /-- The table's address is in its slot. -/
  zerosStored : m.load (base m0 + BitVec.ofNat 64 zerosSlot) 8 = zeros m0
  /-- Each saved register is in its slot. -/
  savedStored : ∀ s ∈ savedSlots, m.load (base m0 + BitVec.ofNat 64 s.2) 8 = m0.read s.1
  /-- Memory outside the frame and the buffer is untouched. -/
  untouched : ∀ y, ¬Within y (base m0) frameSize → ¬Within y (buffer m0) (capacity m0) →
    m.mem y = m0.mem y
  /-- The global pointer is untouched. -/
  globalPointer : m.read 3 = m0.read 3
  /-- The thread pointer is untouched. -/
  threadPointer : m.read 4 = m0.read 4

/-- A byte at a frame slot lies inside the frame. -/
theorem slot_within {m0 : Machine} {c k : Nat} (fits : c + 8 ≤ frameSize) (below : k < 8) :
    Within (base m0 + BitVec.ofNat 64 c + BitVec.ofNat 64 k) (base m0) frameSize := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, within_offset (by unfold frameSize at fits; omega)]
  omega

/-- A table entry lies outside the frame and the buffer, so it reads as on entry. -/
theorem table_steady {m0 m : Machine} (valid : Valid m0) (steady : Steady m0 m) {k : Nat}
    (shallow : k ≤ depth m0) : chunkAt m (zeros m0) k = zeroAt k := by
  rw [← valid.table k shallow, chunkAt, chunkAt, Machine.bytes_congr]
  intro b below
  have inside : Within (zeros m0 + BitVec.ofNat 64 (32 * k) + BitVec.ofNat 64 b) (zeros m0)
      (32 * (depth m0 + 1)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      within_offset (by have := valid.shallow; omega)]
    have : k + 1 ≤ depth m0 + 1 := by omega
    omega
  exact steady.untouched _ (valid.zerosFrame _ inside) (valid.zerosBuffer _ inside)

/-- The dynamic slots: the output address, the count, the pair index, and the height. -/
def dynamicSlots : List Nat :=
  [outSlot, countSlot, pairSlot, heightSlot]

theorem Steady.write {m0 m : Machine} (steady : Steady m0 m) {r : Reg} {v : BitVec 64}
    (notSp : r ≠ sp) (notGp : r ≠ 3) (notTp : r ≠ 4) : Steady m0 (m.write r v) where
  stack := by rw [Machine.read_write_ne (Ne.symm notSp)]; exact steady.stack
  bufferStored := by rw [Machine.load_write]; exact steady.bufferStored
  depthStored := by rw [Machine.load_write]; exact steady.depthStored
  zerosStored := by rw [Machine.load_write]; exact steady.zerosStored
  savedStored := fun s inside => by rw [Machine.load_write]; exact steady.savedStored s inside
  untouched := fun y frame buf => by rw [Machine.mem_write]; exact steady.untouched y frame buf
  globalPointer := by rw [Machine.read_write_ne (Ne.symm notGp)]; exact steady.globalPointer
  threadPointer := by rw [Machine.read_write_ne (Ne.symm notTp)]; exact steady.threadPointer

/-- A dynamic slot shares no byte with a fixed slot or another dynamic slot. -/
theorem slot_apart {m0 : Machine} {c c' : Nat} (inside : c ∈ dynamicSlots)
    (other : c' + 8 ≤ c ∨ c + 8 ≤ c') (fits : c' + 8 ≤ frameSize) :
    Disjoint (base m0 + BitVec.ofNat 64 c') 8 (base m0 + BitVec.ofNat 64 c) 8 := by
  have : c + 8 ≤ frameSize := by
    simp only [dynamicSlots, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with h | h | h | h <;> subst h <;> decide
  unfold frameSize at this fits
  exact disjoint_offsets (by omega) (by omega)

theorem Steady.store {m0 m : Machine} (steady : Steady m0 m) {c : Nat} {v : BitVec 64}
    (inside : c ∈ dynamicSlots) : Steady m0 (m.store (base m0 + BitVec.ofNat 64 c) 8 v) := by
  have fits : c + 8 ≤ frameSize := by
    simp only [dynamicSlots, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with h | h | h | h <;> subst h <;> decide
  have apartFixed (c' : Nat) (away : c' + 8 ≤ c ∨ c + 8 ≤ c') (fits' : c' + 8 ≤ frameSize) :
      (m.store (base m0 + BitVec.ofNat 64 c) 8 v).load (base m0 + BitVec.ofNat 64 c') 8 =
        m.load (base m0 + BitVec.ofNat 64 c') 8 :=
    Machine.load_store_of_disjoint (slot_apart inside away fits') (by decide)
  have dyn : c = outSlot ∨ c = countSlot ∨ c = pairSlot ∨ c = heightSlot := by
    simpa [dynamicSlots] using inside
  refine ⟨steady.stack, ?_, ?_, ?_, fun s mem => ?_, fun y frame buf => ?_, steady.globalPointer, steady.threadPointer⟩
  · rw [apartFixed bufSlot (by rcases dyn with h | h | h | h <;> subst h <;> decide) (by decide)]
    exact steady.bufferStored
  · rw [apartFixed depthSlot (by rcases dyn with h | h | h | h <;> subst h <;> decide) (by decide)]
    exact steady.depthStored
  · rw [apartFixed zerosSlot (by rcases dyn with h | h | h | h <;> subst h <;> decide) (by decide)]
    exact steady.zerosStored
  · have below : s.2 + 8 ≤ 104 := by revert s; decide
    rw [apartFixed s.2 (by rcases dyn with h | h | h | h <;> subst h <;> simp [outSlot, countSlot,
      pairSlot, heightSlot] <;> omega) (by unfold frameSize; omega)]
    exact steady.savedStored s mem
  · rw [Machine.mem_store_of_not_within fun within => frame (within_sub within fits (by decide))]
    exact steady.untouched y frame buf

/-- A chunk of the buffer reads the same after a store to the frame. -/
theorem chunkAt_store_frame {m0 m : Machine} (valid : Valid m0) {c j : Nat} {v : BitVec 64}
    (fits : c + 8 ≤ frameSize) (inBuffer : 32 * (j + 1) ≤ capacity m0) :
    chunkAt (m.store (base m0 + BitVec.ofNat 64 c) 8 v) (buffer m0) j = chunkAt m (buffer m0) j := by
  have same : (m.store (base m0 + BitVec.ofNat 64 c) 8 v).bytes
      (buffer m0 + BitVec.ofNat 64 (32 * j)) 32 = m.bytes (buffer m0 + BitVec.ofNat 64 (32 * j)) 32 := by
    apply Machine.bytes_congr
    intro b below
    apply Machine.mem_store_of_not_within
    intro within
    have inBuf : Within (buffer m0 + BitVec.ofNat 64 (32 * j) + BitVec.ofNat 64 b) (buffer m0)
        (capacity m0) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add,
        within_offset (by have := valid.small; unfold capacity at inBuffer; omega)]
      omega
    exact valid.bufferFrame _ inBuf (within_sub within fits (by decide))
  unfold chunkAt
  rw [same]

@[simp] theorem Machine.bytes_write {m : Machine} {r : Reg} {v a : BitVec 64} {n : Nat} :
    (m.write r v).bytes a n = m.bytes a n :=
  rfl

/-- A chunk reads the same after a register write. -/
theorem chunkAt_write {m : Machine} {buf : BitVec 64} {j : Nat} {r : Reg} {v : BitVec 64} :
    chunkAt (m.write r v) buf j = chunkAt m buf j :=
  rfl

theorem level_length_le (leaves : List Bytes) : ∀ k, (level leaves k).length ≤ max leaves.length 1
  | 0 => by simp [level]; omega
  | k + 1 => by
    rw [level_length]
    have := level_length_le leaves k
    omega

/-- The shared facts depend only on memory and on sp, gp, and tp. -/
theorem Steady.of_mem {m0 m m' : Machine} (steady : Steady m0 m) (mem : m'.mem = m.mem)
    (stack : m'.read sp = m.read sp) (gp : m'.read 3 = m.read 3) (tp : m'.read 4 = m.read 4) :
    Steady m0 m' where
  stack := stack.trans steady.stack
  bufferStored := (Machine.load_of_mem mem).trans steady.bufferStored
  depthStored := (Machine.load_of_mem mem).trans steady.depthStored
  zerosStored := (Machine.load_of_mem mem).trans steady.zerosStored
  savedStored := fun s inside => (Machine.load_of_mem mem).trans (steady.savedStored s inside)
  untouched := fun y frame buf => by rw [mem]; exact steady.untouched y frame buf
  globalPointer := gp.trans steady.globalPointer
  threadPointer := tp.trans steady.threadPointer

theorem chunkAt_of_mem {m m' : Machine} {buf : BitVec 64} {j : Nat} (mem : m'.mem = m.mem) :
    chunkAt m' buf j = chunkAt m buf j := by
  have same : m'.bytes (buf + BitVec.ofNat 64 (32 * j)) 32 = m.bytes (buf + BitVec.ofNat 64 (32 * j)) 32 :=
    Machine.bytes_congr fun _ _ => by rw [mem]
  unfold chunkAt
  rw [same]

/-- A frame slot's eight bytes lie outside the buffer. -/
theorem slot_outside_buffer {m0 : Machine} (valid : Valid m0) {c k : Nat} (fits : c + 8 ≤ frameSize)
    (below : k < 8) : ¬Within (base m0 + BitVec.ofNat 64 c + BitVec.ofNat 64 k) (buffer m0) (capacity m0) :=
  fun inBuffer => valid.bufferFrame _ inBuffer (slot_within fits below)

/-- The shared facts survive any write confined to the buffer. -/
theorem Steady.of_buffer {m0 m m' : Machine} (valid : Valid m0) (steady : Steady m0 m)
    (mem : ∀ y, ¬Within y (buffer m0) (capacity m0) → m'.mem y = m.mem y)
    (stack : m'.read sp = m.read sp) (gp : m'.read 3 = m.read 3) (tp : m'.read 4 = m.read 4) :
    Steady m0 m' := by
  have slot (c : Nat) (fits : c + 8 ≤ frameSize) :
      m'.load (base m0 + BitVec.ofNat 64 c) 8 = m.load (base m0 + BitVec.ofNat 64 c) 8 :=
    Machine.load_congr fun k below => mem _ (slot_outside_buffer valid fits below)
  exact {
    stack := stack.trans steady.stack
    bufferStored := (slot bufSlot (by decide)).trans steady.bufferStored
    depthStored := (slot depthSlot (by decide)).trans steady.depthStored
    zerosStored := (slot zerosSlot (by decide)).trans steady.zerosStored
    savedStored := fun s inside => by
      have : s.2 + 8 ≤ frameSize := by revert s; decide
      exact (slot s.2 this).trans (steady.savedStored s inside)
    untouched := fun y frame buf => (mem y buf).trans (steady.untouched y frame buf)
    globalPointer := gp.trans steady.globalPointer
    threadPointer := tp.trans steady.threadPointer }

end Ssz.Asm.Merkle
