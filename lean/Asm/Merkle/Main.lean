import Asm.Merkle.Exit

/-! The whole routine: the root of the upward fold, in the buffer's first chunk. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Merkle

open Ssz.Asm.Sha256 (sp t0 t1 a0 a1 a2 savedSlots)

/-- What the routine leaves behind on return. -/
def Result (m0 : Machine) (s : Cpu) : Prop :=
  returned program s ∧
    chunkAt s.m (buffer m0) 0 = merkleizeFlat combine zeroChunk (depth m0) (leaves m0) ∧
    (∀ r ∈ Sha256.preserved, s.m.read r = m0.read r) ∧
    ∀ y, ¬Within y (base m0) frameSize → ¬Within y (buffer m0) (capacity m0) → s.m.mem y = m0.mem y

/-- Two byte ranges read the same when their bytes agree position by position. -/
theorem Machine.bytes_eq {m m' : Machine} {a c : BitVec 64} {n : Nat}
    (same : ∀ k, k < n → m.mem (a + BitVec.ofNat 64 k) = m'.mem (c + BitVec.ofNat 64 k)) :
    m.bytes a n = m'.bytes c n := by
  simp only [Machine.bytes]
  have : (fun i : Fin n => (⟨m.mem (a + BitVec.ofNat 64 i.val)⟩ : UInt8)) =
      fun i : Fin n => ⟨m'.mem (c + BitVec.ofNat 64 i.val)⟩ := by
    funext i
    rw [same i.val i.isLt]
  rw [this]

theorem emptyCode_straight : ∀ i ∈ emptyCode, i.straight := by
  decide

/-- From the end of the level loop: keep the first chunk, or copy in the zero subtree when there was nothing. -/
theorem done_reaches {m0 m : Machine} {k : Nat} (valid : Valid m0) (stopped : AtDone m0 k m) :
    Reaches program ⟨m, done⟩ (Result m0) := by
  have state := stopped.reached
  have steady := state.steady
  have bounds := width_le m0 k
  have small := valid.small
  have shallow := valid.shallow
  refine Reaches.run (start := done) (n := 1) [.ld a4 sp (slot countSlot)] rfl
    (fetch_slice (fun k within => fetch_done within) 0 _ rfl (by decide)) (by decide) ?_
  simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, steady.stack,
    slot_ext (show countSlot < 2048 by decide), state.countStored]
  refine Reaches.exec (fetch_one (fun k within => fetch_done within) 1 (by decide)) ?_
  simp (disch := decide) only [List.getElem_cons_succ, List.getElem_cons_zero, doneCode,
    Instr.run, Instr.next, Machine.read_write_self, Machine.read_write_ne, Machine.read_zero]
  by_cases empty : (level (leaves m0) k).length = 0
  · -- No chunks: the root is the full-height zero subtree.
    rw [if_pos (by rw [empty]; rfl), show done + 1 + 1 = emptyStart from rfl]
    have topEmpty : level (leaves m0) (depth m0) = [] :=
      level_nil_stays (List.eq_nil_of_length_eq_zero empty) _ state.height
    have depthWord : m0.read a2 = BitVec.ofNat 64 (depth m0) := by simp [depth]
    refine Reaches.run (start := emptyStart) (n := 13) emptyCode rfl
      (fun k within => fetch_emptyStart within) emptyCode_straight ?_
    simp only [emptyCode, execBlock_append]
    simp (disch := decide) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self,
      Machine.read_write_ne, Machine.load_write, steady.stack, slot_ext (show depthSlot < 2048 by decide),
      slot_ext (show zerosSlot < 2048 by decide), slot_ext (show bufSlot < 2048 by decide),
      steady.depthStored, steady.zerosStored, steady.bufferStored, depthWord,
      ofNat_shift (show 2 ^ 5 * depth m0 < 2 ^ 64 by omega) (by decide)]
    generalize hM : ((((((m.write a4 (BitVec.ofNat 64 (level (leaves m0) k).length)).write t1
      (BitVec.ofNat 64 (depth m0))).write t1 (BitVec.ofNat 64 (2 ^ 5 * depth m0))).write t2 (zeros m0)).write
      t2 (zeros m0 + BitVec.ofNat 64 (2 ^ 5 * depth m0))).write a5 (buffer m0)) = M
    have memM : M.mem = m.mem := by rw [← hM]; rfl
    -- The table entry and the first chunk share no byte.
    have apart : Disjoint (zeros m0 + BitVec.ofNat 64 (2 ^ 5 * depth m0)) 32 (buffer m0) 32 := by
      intro x inEntry inChunk
      apply valid.zerosBuffer x (within_sub inEntry (by omega) (by omega))
      exact within_sub (c := 0) (by simpa using inChunk) (by unfold capacity; omega) (by unfold capacity; omega)
    obtain ⟨copied, memCopy, regsCopy⟩ := copy_upto (M := M) (by rw [← hM]; simp (disch := decide)
      [Machine.read_write_ne, Machine.read_write_self]) (by rw [← hM]; simp (disch := decide)
      [Machine.read_write_self]) apart 4 (by omega)
    generalize execBlock ((List.range 4).flatMap copyWord) M = M' at copied memCopy regsCopy
    have steady' : Steady m0 M' := Steady.of_buffer valid (Steady.of_mem steady memM
      (by rw [← hM]; simp (disch := decide) [Machine.read_write_ne])
      (by rw [← hM]; simp (disch := decide) [Machine.read_write_ne])
      (by rw [← hM]; simp (disch := decide) [Machine.read_write_ne]))
      (fun y outside => memCopy y fun within => outside
        (within_sub (c := 0) (by simpa using within) (by unfold capacity; omega) (by unfold capacity; omega)))
      (regsCopy sp (by decide)) (regsCopy 3 (by decide)) (regsCopy 4 (by decide))
    rw [show emptyStart + 13 = finish from rfl]
    exact (finish_reaches steady').bind fun s ⟨ret, mem, regs⟩ => Reaches.now ⟨ret, by
      -- The first chunk is the table's entry for the full depth.
      have chunk0 : chunkAt s.m (buffer m0) 0 = chunkAt m (zeros m0) (depth m0) := by
        have same : s.m.bytes (buffer m0 + BitVec.ofNat 64 (32 * 0)) 32 =
            m.bytes (zeros m0 + BitVec.ofNat 64 (32 * depth m0)) 32 := by
          apply Machine.bytes_eq
          intro b below
          rw [mem, Nat.mul_zero, BitVec.add_zero, copied b (by omega), memM,
            show 2 ^ 5 * depth m0 = 32 * depth m0 by omega]
        unfold chunkAt
        rw [same]
      rw [merkleizeFlat_level, topEmpty, chunk0, table_steady valid steady (Nat.le_refl _)]
      rfl, regs, fun y frame buf => by
        rw [mem, memCopy y fun within => buf (within_sub (c := 0) (by simpa using within)
          (by unfold capacity; omega) (by unfold capacity; omega)), memM]
        exact steady.untouched y frame buf⟩
  · -- A nonempty top level: the root is already in the first chunk.
    rw [if_neg (by
      rw [show (0 : BitVec 64) = BitVec.ofNat 64 0 from rfl, ofNat_eq_iff (by omega) (by decide)]
      exact empty)]
    have top : k = depth m0 := by have := stopped.top; omega
    have steady' := steady.write (r := a4) (v := BitVec.ofNat 64 (level (leaves m0) k).length)
      (by decide) (by decide) (by decide)
    exact (finish_reaches steady').bind fun s ⟨ret, mem, regs⟩ => Reaches.now ⟨ret, by
      rw [chunkAt_of_mem mem, chunkAt_write, state.chunks 0 (by omega), merkleizeFlat_level, ← top,
        List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      rfl, regs, fun y frame buf => by
        rw [mem, Machine.mem_write]
        exact steady.untouched y frame buf⟩

/--
The routine computes the root of the upward fold over the input chunks.

It returns with the root in the buffer's first chunk, the caller's registers restored, and memory
outside its frame and the buffer untouched.
-/
theorem merkleize_correct (m0 : Machine) (valid : Valid m0) : Reaches program ⟨m0, 0⟩ (Result m0) :=
  (entry_reaches valid).bind fun s ⟨pc, start⟩ => by
    rw [show s = ⟨s.m, levelHead⟩ by rw [← pc]]
    exact (level_loop valid _ 0 s.m rfl start).bind fun s' ⟨pc', k, stopped⟩ => by
      rw [show s' = ⟨s'.m, done⟩ by rw [← pc']]
      exact done_reaches valid stopped

/--
With the depth a declared capacity calls for, the root is the specification's bounded Merkle root.

    merkleizeBounded chunks (some capacity) = root    when the chunks fit the capacity
-/
theorem root_eq_merkleizeBounded (m0 : Machine) {capacity : Nat} (deep : depth m0 = depthFor capacity)
    (fits : count m0 ≤ capacity) :
    merkleizeBounded (leaves m0).toArray (some capacity) =
      .ok (merkleizeFlat combine zeroChunk (depth m0) (leaves m0)) := by
  rw [← merkleizeUpward_eq, merkleizeUpward, deep, List.toList_toArray]
  have : ¬capacity < (leaves m0).length := by simp [leaves]; omega
  simp only [List.size_toArray, this, if_false]
  rfl

end Ssz.Asm.Merkle
