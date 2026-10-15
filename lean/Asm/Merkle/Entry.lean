import Asm.Merkle.State

/-! The loop invariants, and the entry code that establishes the first one. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Merkle

open Ssz.Asm.Sha256 (sp t0 t1 a0 a1 a2 savedSlots pairCode workRegs)

/-- At the level loop's head with level k in the buffer. -/
structure AtLevel (m0 : Machine) (k : Nat) (m : Machine) : Prop where
  /-- The facts every state shares. -/
  steady : Steady m0 m
  /-- Level k exists. -/
  height : k ≤ depth m0
  /-- The count slot holds the level's length. -/
  countStored : m.load (base m0 + BitVec.ofNat 64 countSlot) 8 = BitVec.ofNat 64 (level (leaves m0) k).length
  /-- The height slot holds k. -/
  heightStored : m.load (base m0 + BitVec.ofNat 64 heightSlot) 8 = BitVec.ofNat 64 k
  /-- The buffer holds level k. -/
  chunks : ∀ j (within : j < (level (leaves m0) k).length), chunkAt m (buffer m0) j = (level (leaves m0) k)[j]

theorem entryCode_straight : ∀ i ∈ entryCode, i.straight := by
  decide

theorem entry_reaches {m0 : Machine} (valid : Valid m0) :
    Reaches program ⟨m0, 0⟩ fun s => s.pc = levelHead ∧ AtLevel m0 0 s.m := by
  refine Reaches.block (s := ⟨m0, 0⟩) entryCode (fun k within => fetch_entry within)
    entryCode_straight (Reaches.now ?_)
  refine ⟨by show 0 + entryCode.length = levelHead; rw [entryCode_length]; rfl, ?_⟩
  -- Opening the frame moves the stack pointer down by the frame size.
  have opened : (Instr.addi sp sp (BitVec.ofInt 12 (-(frameSize : Int)))).run m0 =
      m0.write sp (base m0) := by
    have down : (BitVec.ofInt 12 (-(frameSize : Int))).signExtend 64 = 0 - BitVec.ofNat 64 frameSize := by
      decide
    have moved : m0.read sp + (0 - BitVec.ofNat 64 frameSize) = m0.read sp - BitVec.ofNat 64 frameSize := by
      bv_omega
    simp only [Instr.run, base, down, moved]
  have small : ∀ s ∈ entrySlots, s.2 < 2048 := by decide
  have inside : ∀ s ∈ entrySlots, s.2 + 8 ≤ frameSize := by decide
  have notSp : ∀ s ∈ entrySlots, s.1 ≠ sp := by decide
  have apart : SlotsApart entrySlots := by unfold SlotsApart; decide
  simp only [entryCode, execBlock_cons, opened]
  generalize hm : execBlock (spills sp entrySlots) (m0.write sp (base m0)) = m
  have spillsRead (r : Reg) : m.read r = (m0.write sp (base m0)).read r := by rw [← hm, spills_read]
  have spillsMem (y : BitVec 64) (outside : ¬Within y (base m0) frameSize) : m.mem y = m0.mem y := by
    rw [← hm, spills_mem small fun s mem within => outside (within_sub (by
        rwa [Machine.read_write_self (by decide)] at within) (inside s mem) (by decide)),
      Machine.mem_write]
  have spillsLoad (s : Reg × Nat) (mem : s ∈ entrySlots) :
      m.load (base m0 + BitVec.ofNat 64 s.2) 8 = m0.read s.1 := by
    have loaded := spills_load (base := sp) (m := m0.write sp (base m0)) apart s mem
    rwa [Machine.read_write_self (by decide), Machine.read_write_ne (notSp s mem), hm] at loaded
  refine ⟨⟨?_, ?_, ?_, ?_, fun s mem => ?_, fun y frame _ => spillsMem y frame, ?_, ?_⟩,
    Nat.zero_le _, ?_, ?_, fun j within => ?_⟩
  · rw [spillsRead, Machine.read_write_self (by decide)]
  · exact spillsLoad (a0, bufSlot) (by decide)
  · exact spillsLoad (a2, depthSlot) (by decide)
  · exact spillsLoad (a3, zerosSlot) (by decide)
  · exact spillsLoad s (by simp [entrySlots, mem])
  · rw [spillsRead, Machine.read_write_ne (by decide)]
  · rw [spillsRead, Machine.read_write_ne (by decide)]
  · rw [spillsLoad (a1, countSlot) (by decide)]
    simp [level, leaves, count]
  · rw [spillsLoad (zero, heightSlot) (by decide), Machine.read_zero]
    rfl
  · -- The buffer lies outside the frame, so the leaves are still there.
    simp only [level, leaves, List.getElem_map, List.getElem_range]
    have size : j < count m0 := by simpa [level, leaves] using within
    have same : m.bytes (buffer m0 + BitVec.ofNat 64 (32 * j)) 32 =
        m0.bytes (buffer m0 + BitVec.ofNat 64 (32 * j)) 32 := by
      apply Machine.bytes_congr
      intro b below
      apply spillsMem
      apply valid.bufferFrame
      rw [BitVec.add_assoc, ← BitVec.ofNat_add,
        within_offset (by have := valid.small; omega)]
      unfold capacity
      omega
    unfold chunkAt
    rw [same]

end Ssz.Asm.Merkle
