import Asm.Merkle.Entry
import Asm.Merkle.Arith

/-! One level of the fold: the pair loop, hashing pair i into chunk i. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Merkle

open Ssz.Asm.Sha256 (sp t0 t1 a0 a1 a2 savedSlots pairCode workRegs pair_spec)

/-- At the pair loop's head, with pairs below i of level k already hashed. -/
structure AtPair (m0 : Machine) (k i : Nat) (m : Machine) : Prop where
  /-- The facts every state shares. -/
  steady : Steady m0 m
  /-- Level k is below the top. -/
  below : k < depth m0
  /-- Level k is not empty. -/
  nonempty : 0 < (level (leaves m0) k).length
  /-- At most every pair is hashed. -/
  progress : i ≤ ((level (leaves m0) k).length + 1) / 2
  /-- The count slot holds the level's length. -/
  countStored : m.load (base m0 + BitVec.ofNat 64 countSlot) 8 = BitVec.ofNat 64 ((level (leaves m0) k).length)
  /-- The height slot holds k. -/
  heightStored : m.load (base m0 + BitVec.ofNat 64 heightSlot) 8 = BitVec.ofNat 64 k
  /-- The pair slot holds i. -/
  pairStored : m.load (base m0 + BitVec.ofNat 64 pairSlot) 8 = BitVec.ofNat 64 i
  /-- The first i parents are in place. -/
  parents : ∀ j (within : j < i), chunkAt m (buffer m0) j =
    (level (leaves m0) (k + 1))[j]'(by rw [level_length]; omega)
  /-- The children not yet read are still in place. -/
  children : ∀ j, 2 * i ≤ j → (within : j < (level (leaves m0) k).length) → chunkAt m (buffer m0) j = (level (leaves m0) k)[j]

theorem slot_ext {c : Nat} (small : c < 2048) : (slot c).signExtend 64 = BitVec.ofNat 64 c :=
  signExtend_ofNat12 small

theorem width_le (m0 : Machine) (k : Nat) : (level (leaves m0) k).length ≤ max (count m0) 1 := by
  have := level_length_le (leaves m0) k
  rwa [show (leaves m0).length = count m0 by simp [leaves]] at this

/-- The right child of pair i: node 2i + 1, or the zero subtree of the level's height if there is none. -/
def rightChild (m0 : Machine) (k i : Nat) : Bytes :=
  (level (leaves m0) k)[2 * i + 1]?.getD (zeroAt k)

theorem pairStepCode_length : pairStepCode.length = 5094 := by
  simp [pairStepCode, Sha256.pairCode_length]

theorem pairStepCode_straight : ∀ i ∈ pairStepCode, i.straight := by
  intro i inside
  simp only [pairStepCode, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with inside | h | h | h
  · exact Sha256.pairCode_straight outSlot i inside
  all_goals subst h; rfl

theorem fetch_pairStep {k : Nat} (within : k < pairStepCode.length) :
    program[pairBody + k]? = some pairStepCode[k] := by
  have := fetch_slice (fun k within => fetch_pairBody within) 0 pairStepCode
    (by simp [pairBodyCode, List.take_left']) (by simp [pairBodyCode]) k within
  rwa [Nat.add_zero] at this

theorem fetch_pairJump : program[pairBody + 5094]? = some (.j pairHead) := by
  have := fetch_one (fun k within => fetch_pairBody within) 5094
    (by simp [pairBodyCode, pairStepCode_length])
  rw [this]
  simp [pairBodyCode, List.getElem_append_right, pairStepCode_length]

/--
From the parent's address on: hash the pair into chunk i, count it, and loop.

The machine has the pair's index in t0, the buffer in a5, and the two children's addresses in a1 and a2.
-/
theorem from_normal {m0 m M : Machine} {k i : Nat} (valid : Valid m0) (state : AtPair m0 k i m)
    (more : i < ((level (leaves m0) k).length + 1) / 2) (mem : M.mem = m.mem)
    (stack : M.read sp = base m0) (gp : M.read 3 = m.read 3) (tp : M.read 4 = m.read 4)
    (index : M.read t0 = BitVec.ofNat 64 i) (buf : M.read a5 = buffer m0)
    (left : M.read a1 = buffer m0 + BitVec.ofNat 64 (64 * i))
    (right : (M.bytes (M.read a2) 32).data = rightChild m0 k i)
    (rightApart : ∀ b, b < 32 → ¬Within (M.read a2 + BitVec.ofNat 64 b) (base m0) frameSize) :
    Reaches program ⟨M, normal⟩ fun s => s.pc = pairHead ∧ AtPair m0 k (i + 1) s.m := by
  have small := valid.small
  have bounds := width_le m0 k
  -- The parent goes to chunk i, whose address is saved in its slot.
  refine Reaches.run (start := normal) (n := 3) normalCode rfl (fun k within => fetch_normal within)
    (by decide) ?_
  simp (disch := decide) only [normalCode, execBlock_cons, execBlock_nil, Instr.run,
    Machine.read_write_self, Machine.read_write_ne, index, buf, stack, slot_ext (show outSlot < 2048 by decide),
    ofNat_shift (show 2 ^ 5 * i < 2 ^ 64 by omega) (by decide)]
  -- Hash the pair, count it, and jump back to the loop's head.
  rw [show normal + 3 = pairBody from rfl]
  refine Reaches.run (start := pairBody) (n := 5094) pairStepCode pairStepCode_length
    (fun k within => fetch_pairStep within) pairStepCode_straight ?_
  refine Reaches.exec fetch_pairJump (Reaches.now ⟨rfl, ?_⟩)
  simp only [Instr.run, pairStepCode, execBlock_append]
  -- The machine about to hash: the parent's address is in its slot.
  generalize hM4 : ((M.write t2 (BitVec.ofNat 64 (2 ^ 5 * i))).write t2
    (buffer m0 + BitVec.ofNat 64 (2 ^ 5 * i))).store (base m0 + BitVec.ofNat 64 outSlot) 8
    (buffer m0 + BitVec.ofNat 64 (2 ^ 5 * i)) = M4
  have steady4 : Steady m0 M4 := by
    rw [← hM4]
    exact ((Steady.of_mem state.steady mem (by rw [stack, state.steady.stack]) gp tp).write
      (by decide) (by decide) (by decide)).write (by decide) (by decide) (by decide) |>.store
      (by simp [dynamicSlots])
  have sp4 : M4.read sp = base m0 := steady4.stack
  have out4 : M4.load (M4.read sp + BitVec.ofNat 64 outSlot) 8 = buffer m0 + BitVec.ofNat 64 (32 * i) := by
    rw [sp4, ← hM4, Machine.load_store_self8]
  -- A frame store leaves every byte outside the frame alone.
  have frameOnly (y : BitVec 64) (outside : ¬Within y (base m0) frameSize) : M4.mem y = M.mem y := by
    rw [← hM4, Machine.mem_store_of_not_within fun within =>
      outside (within_sub within (by decide) (by decide))]
    rfl
  -- A chunk of the buffer lies outside the frame, so it is as the loop left it.
  have chunkSame (j : Nat) (inBuffer : 32 * (j + 1) ≤ capacity m0) :
      chunkAt M4 (buffer m0) j = chunkAt m (buffer m0) j := by
    rw [← chunkAt_of_mem (m' := M) mem]
    have same : M4.bytes (buffer m0 + BitVec.ofNat 64 (32 * j)) 32 =
        M.bytes (buffer m0 + BitVec.ofNat 64 (32 * j)) 32 :=
      Machine.bytes_congr fun b below => frameOnly _ fun within => valid.bufferFrame _ (by
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, within_offset (by unfold capacity at inBuffer; omega)]
        omega) within
    unfold chunkAt
    rw [same]
  have leftBytes : (M4.bytes (M4.read a1) 32).data = (level (leaves m0) k)[2 * i]'(by omega) := by
    rw [show M4.read a1 = M.read a1 by rw [← hM4]; simp (disch := decide) [Machine.read_write_ne],
      left, show 64 * i = 32 * (2 * i) by omega]
    exact (chunkSame (2 * i) (by unfold capacity; omega)).trans
      (state.children (2 * i) (by omega) (by omega))
  have rightBytes : (M4.bytes (M4.read a2) 32).data = rightChild m0 k i := by
    rw [show M4.read a2 = M.read a2 by rw [← hM4]; simp (disch := decide) [Machine.read_write_ne], ← right,
      Machine.bytes_congr fun b below => frameOnly _ (rightApart b below)]
  -- The hash writes chunk i and nothing else.
  obtain ⟨hashed, memHash, regsHash⟩ := pair_spec M4 outSlot (by decide)
  rw [out4] at hashed memHash
  generalize execBlock (pairCode outSlot) M4 = M5 at hashed memHash regsHash
  have outInside (y : BitVec 64) (within : Within y (buffer m0 + BitVec.ofNat 64 (32 * i)) 32) :
      Within y (buffer m0) (capacity m0) :=
    within_sub within (by unfold capacity; omega) (by unfold capacity; omega)
  have steady5 : Steady m0 M5 := Steady.of_buffer valid steady4
    (fun y outside => memHash y fun within => outside (outInside y within))
    (regsHash sp (by decide)) (regsHash 3 (by decide)) (regsHash 4 (by decide))
  -- A frame slot is outside the buffer, so the hash left it alone.
  have slot5 (c : Nat) (fits : c + 8 ≤ frameSize) :
      M5.load (base m0 + BitVec.ofNat 64 c) 8 = M4.load (base m0 + BitVec.ofNat 64 c) 8 :=
    Machine.load_congr fun b below => memHash _ fun within =>
      slot_outside_buffer valid fits below (outInside _ within)
  have slot4 (c : Nat) (fits : c + 8 ≤ frameSize) (apart : c + 8 ≤ outSlot ∨ outSlot + 8 ≤ c) :
      M4.load (base m0 + BitVec.ofNat 64 c) 8 = m.load (base m0 + BitVec.ofNat 64 c) 8 := by
    rw [← hM4, Machine.load_store_of_disjoint (disjoint_offsets
      (by simp only [frameSize, outSlot] at fits apart ⊢; omega)
      (by simp only [frameSize, outSlot] at fits apart ⊢; omega)) (by decide), Machine.load_write,
      Machine.load_write, Machine.load_of_mem mem]
  have pair5 : M5.load (base m0 + BitVec.ofNat 64 pairSlot) 8 = BitVec.ofNat 64 i := by
    rw [slot5 pairSlot (by decide), slot4 pairSlot (by decide) (by decide), state.pairStored]
  -- Count the pair.
  simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self,
    Machine.read_write_ne, steady5.stack, slot_ext (show pairSlot < 2048 by decide),
    slot_ext (show 1 < 2048 by decide), pair5, ← BitVec.ofNat_add]
  -- Chunk i is the new parent, and every other chunk the loop tracks is unchanged.
  have chunk5 (j : Nat) (apart : j ≠ i) (inBuffer : 32 * (j + 1) ≤ capacity m0) :
      chunkAt M5 (buffer m0) j = chunkAt m (buffer m0) j := by
    rw [← chunkSame j inBuffer]
    have same : M5.bytes (buffer m0 + BitVec.ofNat 64 (32 * j)) 32 =
        M4.bytes (buffer m0 + BitVec.ofNat 64 (32 * j)) 32 :=
      Machine.bytes_congr fun b below => memHash _ (disjoint_offsets (by omega)
        (by unfold capacity at inBuffer; omega) _ ((within_offset (by omega)).mpr below))
    unfold chunkAt
    rw [same]
  have parent : chunkAt M5 (buffer m0) i = (level (leaves m0) (k + 1))[i]'(by rw [level_length]; omega) := by
    unfold chunkAt
    rw [hashed]
    simp only [level]
    rw [pairLevel_get]
    show combine (M4.bytes (M4.read a1) 32).data (M4.bytes (M4.read a2) 32).data = _
    rw [leftBytes, rightBytes]
    rfl
  have frameStore (j : Nat) (inBuffer : 32 * (j + 1) ≤ capacity m0) (v : BitVec 64) :
      chunkAt (((M5.write t0 (BitVec.ofNat 64 i)).write t0 (BitVec.ofNat 64 (i + 1))).store
        (base m0 + BitVec.ofNat 64 pairSlot) 8 v) (buffer m0) j = chunkAt M5 (buffer m0) j := by
    rw [chunkAt_store_frame valid (by decide) inBuffer, chunkAt_write, chunkAt_write]
  have slot6 (c : Nat) (fits : c + 8 ≤ frameSize) (apart : c + 8 ≤ pairSlot ∨ pairSlot + 8 ≤ c)
      (v : BitVec 64) :
      (((M5.write t0 (BitVec.ofNat 64 i)).write t0 (BitVec.ofNat 64 (i + 1))).store
        (base m0 + BitVec.ofNat 64 pairSlot) 8 v).load (base m0 + BitVec.ofNat 64 c) 8 =
        M5.load (base m0 + BitVec.ofNat 64 c) 8 := by
    rw [Machine.load_store_of_disjoint (disjoint_offsets
      (by simp only [frameSize, pairSlot] at fits apart ⊢; omega)
      (by simp only [frameSize, pairSlot] at fits apart ⊢; omega)) (by decide), Machine.load_write,
      Machine.load_write]
  refine ⟨((steady5.write (by decide) (by decide) (by decide)).write (by decide) (by decide)
      (by decide)).store (by simp [dynamicSlots]), state.below, state.nonempty, by omega, ?_, ?_, ?_,
    fun j within => ?_, fun j above within => ?_⟩
  · rw [slot6 countSlot (by decide) (by decide), slot5 countSlot (by decide),
      slot4 countSlot (by decide) (by decide), state.countStored]
  · rw [slot6 heightSlot (by decide) (by decide), slot5 heightSlot (by decide),
      slot4 heightSlot (by decide) (by decide), state.heightStored]
  · exact Machine.load_store_self8
  · rw [frameStore j (by unfold capacity; omega)]
    by_cases now : j = i
    · subst now
      exact parent
    · rw [chunk5 j now (by unfold capacity; omega)]
      exact state.parents j (by omega)
  · rw [frameStore j (by unfold capacity; omega), chunk5 j (by omega) (by unfold capacity; omega)]
    exact state.children j (by omega) within

/-- After the pointer setup: a right child in the buffer, or the zero subtree for an odd level's last pair. -/
theorem pair_branch {m0 m M : Machine} {k i : Nat} (valid : Valid m0) (state : AtPair m0 k i m)
    (more : i < ((level (leaves m0) k).length + 1) / 2) (mem : M.mem = m.mem)
    (stack : M.read sp = base m0) (gp : M.read 3 = m.read 3) (tp : M.read 4 = m.read 4)
    (index : M.read t0 = BitVec.ofNat 64 i) (buf : M.read a5 = buffer m0)
    (left : M.read a1 = buffer m0 + BitVec.ofNat 64 (2 ^ 6 * i))
    (rightNext : M.read a2 = buffer m0 + BitVec.ofNat 64 (2 ^ 6 * i) + 32#64) :
    Reaches program ⟨M, if 2 ^ 1 * i + 1 = (level (leaves m0) k).length then pairHead + 5 + 6 + 1
      else normal⟩ fun s => s.pc = pairHead ∧ AtPair m0 k (i + 1) s.m := by
  have small := valid.small
  have bounds := width_le m0 k
  have left' : M.read a1 = buffer m0 + BitVec.ofNat 64 (64 * i) := by rw [left]
  by_cases last : 2 ^ 1 * i + 1 = (level (leaves m0) k).length
  · -- The last pair of an odd level: the right child is the zero subtree of this height.
    rw [if_pos last, show pairHead + 5 + 6 + 1 = oddStart from rfl]
    refine Reaches.run (start := oddStart) (n := 4) oddCode rfl (fun k within => fetch_oddStart within)
      (by decide) ?_
    have readHeight : M.load (M.read sp + (slot heightSlot).signExtend 64) 8 = BitVec.ofNat 64 k := by
      rw [stack, slot_ext (by decide), Machine.load_of_mem mem, state.heightStored]
    have readZeros : M.load (M.read sp + (slot zerosSlot).signExtend 64) 8 = zeros m0 := by
      rw [stack, slot_ext (by decide), Machine.load_of_mem mem, state.steady.zerosStored]
    simp (disch := decide) only [oddCode, execBlock_cons, execBlock_nil, Instr.run,
      Machine.read_write_self, Machine.read_write_ne, Machine.load_write, readHeight, readZeros,
      ofNat_shift (show 2 ^ 5 * k < 2 ^ 64 by have := valid.shallow; have := state.below; omega)
        (by decide)]
    rw [show oddStart + 4 = normal from rfl]
    have shallow := valid.shallow
    have below := state.below
    refine from_normal valid state more (by simp [mem])
      (by simp (disch := decide) [Machine.read_write_ne, stack])
      (by simp (disch := decide) [Machine.read_write_ne, gp])
      (by simp (disch := decide) [Machine.read_write_ne, tp])
      (by simp (disch := decide) [Machine.read_write_ne, index])
      (by simp (disch := decide) [Machine.read_write_ne, buf])
      (by simp (disch := decide) [Machine.read_write_ne, left']) ?_ ?_
    · -- The table entry for this height is the zero subtree, and the odd node has no sibling.
      simp (disch := decide) only [Machine.read_write_self, Machine.read_write_ne]
      have entry := table_steady valid state.steady (k := k) (by omega)
      rw [← chunkAt_of_mem (m' := M) mem] at entry
      simp only [chunkAt, show 2 ^ 5 * k = 32 * k by omega] at entry ⊢
      rw [Machine.bytes_write, Machine.bytes_write, Machine.bytes_write, Machine.bytes_write, entry,
        rightChild, List.getElem?_eq_none (by omega)]
      rfl
    · intro b below
      simp (disch := decide) only [Machine.read_write_self]
      apply valid.zerosFrame
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, within_offset (by omega)]
      omega
  · -- Otherwise the right child is the next chunk of the buffer.
    rw [if_neg last]
    have rightChunk : M.read a2 = buffer m0 + BitVec.ofNat 64 (32 * (2 * i + 1)) := by
      rw [rightNext, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2
      omega
    refine from_normal valid state more mem stack gp tp index buf left' ?_ ?_
    · rw [rightChunk]
      show chunkAt M (buffer m0) (2 * i + 1) = _
      rw [chunkAt_of_mem mem, state.children (2 * i + 1) (by omega) (by omega), rightChild,
        List.getElem?_eq_getElem (by omega)]
      rfl
    · intro b below
      rw [rightChunk]
      apply valid.bufferFrame
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, within_offset (by omega)]
      unfold capacity
      omega

/-- One pair: hash it into place and count it. -/
theorem pair_step {m0 m : Machine} {k i : Nat} (valid : Valid m0) (state : AtPair m0 k i m)
    (more : i < ((level (leaves m0) k).length + 1) / 2) :
    Reaches program ⟨m, pairHead⟩ fun s => s.pc = pairHead ∧ AtPair m0 k (i + 1) s.m := by
  have steady := state.steady
  have bounds := width_le m0 k
  have small := valid.small
  have stack := steady.stack
  have readPair : m.load (m.read sp + (slot pairSlot).signExtend 64) 8 = BitVec.ofNat 64 i := by
    rw [stack, slot_ext (by decide), state.pairStored]
  have readCount : m.load (m.read sp + (slot countSlot).signExtend 64) 8 =
      BitVec.ofNat 64 (level (leaves m0) k).length := by
    rw [stack, slot_ext (by decide), state.countStored]
  -- Read the pair index and the level's length, and halve the length rounded up.
  refine Reaches.run (start := pairHead) (n := 4)
    [.ld t0 sp (slot pairSlot), .ld a4 sp (slot countSlot), .addi t1 a4 (slot 1), .srli t1 t1 1] rfl
    (fetch_slice (fun k within => fetch_pairHead within) 0 _ rfl (by decide)) (by decide) ?_
  simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self,
    Machine.read_write_ne, Machine.load_write, readPair, readCount, slot_ext (show 1 < 2048 by decide),
    ← BitVec.ofNat_add,
    ofNat_half (show (level (leaves m0) k).length + 1 < 2 ^ 64 by omega)]
  -- The pair loop goes on while pairs remain.
  refine Reaches.exec (fetch_one (fun k within => fetch_pairHead within) 4 (by decide)) ?_
  simp (disch := decide) only [List.getElem_cons_succ, List.getElem_cons_zero, pairHeadCode,
    Instr.run, Instr.next, Machine.read_write_self, Machine.read_write_ne,
    ofNat_lt_iff (show i < 2 ^ 64 by omega) (show ((level (leaves m0) k).length + 1) / 2 < 2 ^ 64 by omega),
    more, if_true]
  -- Point a1 at child 2i and a2 at child 2i + 1, and test whether that child exists.
  rw [show pairHead + 4 + 1 = pairHead + 5 from rfl]
  refine Reaches.run (start := pairHead + 5) (n := 6)
    [.ld a5 sp (slot bufSlot), .slli t2 t0 6, .add a1 a5 t2, .addi a2 a1 (slot 32), .slli t2 t0 1,
      .addi t2 t2 (slot 1)] rfl
    (fetch_slice (fun k within => fetch_pairHead within) 5 _ rfl (by decide)) (by decide) ?_
  have readBuf : m.load (base m0 + (slot bufSlot).signExtend 64) 8 = buffer m0 := by
    rw [slot_ext (by decide), steady.bufferStored]
  simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self,
    Machine.read_write_ne, Machine.load_write, stack, readBuf, slot_ext (show 32 < 2048 by decide),
    slot_ext (show 1 < 2048 by decide), ofNat_shift (show 2 ^ 6 * i < 2 ^ 64 by omega) (by decide),
    ofNat_shift (show 2 ^ 1 * i < 2 ^ 64 by omega) (by decide), ← BitVec.ofNat_add]
  refine Reaches.exec (fetch_one (fun k within => fetch_pairHead within) 11 (by decide)) ?_
  simp (disch := decide) only [List.getElem_cons_succ, List.getElem_cons_zero, pairHeadCode,
    Instr.run, Instr.next, Machine.read_write_self, Machine.read_write_ne,
    ofNat_eq_iff (show 2 ^ 1 * i + 1 < 2 ^ 64 by omega)
      (show (level (leaves m0) k).length < 2 ^ 64 by omega)]
  exact pair_branch valid state more rfl
    (by simp (disch := decide) [Machine.read_write_ne, stack])
    (by simp (disch := decide) [Machine.read_write_ne])
    (by simp (disch := decide) [Machine.read_write_ne])
    (by simp (disch := decide) [Machine.read_write_ne, Machine.read_write_self])
    (by simp (disch := decide) [Machine.read_write_ne, Machine.read_write_self])
    (by simp (disch := decide) [Machine.read_write_ne, Machine.read_write_self])
    (by simp (disch := decide) [Machine.read_write_ne, Machine.read_write_self])


end Ssz.Asm.Merkle
