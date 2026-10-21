import SszNative.Proofs.Kernel.Avx512.Moves
import SszNative.Proofs.Kernel.Avx512.Rounds

/-!
The sixteen-lane kernel, start to return.

The routine first tests the batch count, and skips to the end when it is zero.
Each batch is the moves in, the compute core, and the moves out.
After a batch, the pointers advance, the count goes down, and the loop branches back while batches remain.
At the end, the routine clears the upper vector state and returns.
-/

namespace Ssz.Native.Kernel.Avx512

open Ssz.Sha256 Ssz.Native.Asm

/-- A pair's message is 64 bytes. -/
theorem pairMessage_size (mem : Nat → UInt8) (l r : Nat) : (pairMessage mem l r).size = 64 := by
  -- The message is built from 64 bytes.
  simp [pairMessage, ByteArray.size]

/-- A pair's message reads only its two nodes. -/
theorem pairMessage_congr (m₁ m₂ : Nat → UInt8) (l r : Nat) (hl : ∀ i < 32, m₁ (l + i) = m₂ (l + i))
    (hr : ∀ i < 32, m₁ (r + i) = m₂ (r + i)) : pairMessage m₁ l r = pairMessage m₂ l r := by
  -- The message reads 32 bytes from each address, which agree in both memories.
  simp only [pairMessage]
  congr 2
  funext i
  split
  · exact hl i.val (by omega)
  · exact hr (i.val - 32) (by omega)

set_option maxRecDepth 100000 in
/-- One batch: sixteen pairs read from the node addresses, sixteen digests written from the output address. -/
theorem batch (ls rs : Nat) (s : State) (table : TableAt s.mem (s.gpr tbl).toNat) :
    (∀ p < 16, ∀ k < 32, (exec (batchCode ls rs) s).mem ((s.gpr out).toNat + 32 * p + k) =
      (Sha256.hash (pairMessage s.mem ((s.gpr left).toNat + ls * p) ((s.gpr right).toNat + rs * p))).get! k) ∧
    (∀ a, ¬ ((s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 512) → (exec (batchCode ls rs) s).mem a = s.mem a) ∧
    (exec (batchCode ls rs) s).gpr = s.gpr := by
  -- The loads and transpose, the rounds, then the transpose back and the stores.
  rw [batchCode_eq, exec_append (loadCode ls rs ++ transposeIn ++ swapIn ++ core) (transposeOut ++ storeCode),
    exec_append (loadCode ls rs ++ transposeIn ++ swapIn) core]
  obtain ⟨words, g1, m1, _⟩ := prologue ls rs s table
  let m : Fin 16 → ByteArray := fun p =>
    pairMessage s.mem ((s.gpr left).toNat + ls * p.val) ((s.gpr right).toNat + rs * p.val)
  obtain ⟨homes, g2, m2, _⟩ := core_spec _ (by rw [g1, m1]; exact table) m words
  obtain ⟨digests, rest, g3, _⟩ := epilogue _ (by rw [g2, m2, g1, m1]; exact table)
  rw [g2, g1] at digests rest
  rw [m2, m1] at rest
  refine ⟨fun p hp k hk => ?_, rest, by rw [g3, g2, g1]⟩
  -- Each lane's digest is the hash of its pair, as two compressions.
  rw [digests ⟨p, hp⟩ k hk, hash_pair _ (pairMessage_size _ _ _)]
  congr 2
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn]
  exact homes j hj ⟨p, hp⟩

/-- The pointer and counter updates at the end of each batch. -/
def tailCode (ls rs : Nat) : List Instr :=
  [.addImm left (16 * ls), .addImm right (16 * rs), .addImm out 512, .subImm count 1]

/-- The index of the closing instructions. -/
def finishAt (ls rs : Nat) : Nat := loopHead + (batchCode ls rs).length + 5

/-- The routine's instructions: the empty-count check, the batch, the updates, the branch back, and the closing pair. -/
theorem program_toList (ls rs : Nat) :
    (program ls rs).toList =
      [.test count, .jz (finishAt ls rs)] ++ batchCode ls rs ++ tailCode ls rs ++ [.jnz loopHead, .vzeroupper, .ret] := by
  -- The routine was built as these blocks, in this order.
  simp only [program, finishAt, tailCode, List.toList_toArray, List.length_cons, List.length_nil, List.append_assoc,
    List.cons_append, List.nil_append]

/-- The instruction at an index, read from the list the program was built from. -/
theorem fetch (p : Array Instr) (pre post : List Instr) (i : Instr) (h : p.toList = pre ++ i :: post) :
    p[pre.length]? = some i := by
  -- The instruction follows the prefix.
  rw [← Array.getElem?_toList, h]
  simp

/-- A branch taken when the zero flag is set. -/
theorem step_jz (p : Array Instr) (s : State) (t : Nat) (f : p[s.pc]? = some (.jz t)) (running : s.status = .running) :
    step p s = { s with pc := if s.zf then t else s.pc + 1 } := by
  -- The branch reads the zero flag.
  simp [step, running, f]

/-- A branch taken when the zero flag is clear. -/
theorem step_jnz (p : Array Instr) (s : State) (t : Nat) (f : p[s.pc]? = some (.jnz t))
    (running : s.status = .running) : step p s = { s with pc := if s.zf then s.pc + 1 else t } := by
  -- The branch reads the zero flag.
  simp [step, running, f]

/-- A return stops the routine. -/
theorem step_ret (p : Array Instr) (s : State) (f : p[s.pc]? = some .ret) (running : s.status = .running) :
    step p s = { s with status := .returned } := by
  -- A return only stops the routine.
  simp [step, running, f]

/-- A lanewise instruction never branches. -/
theorem lanewise_straight (i : Instr) (h : lanewise i) : i.straight := by
  -- No lanewise instruction is a branch.
  cases i <;> simp_all [lanewise, Instr.straight]

/-- A batch never branches. -/
theorem batch_straight (ls rs : Nat) : ∀ i ∈ batchCode ls rs, i.straight := by
  -- Each part of the batch is straight-line code.
  rw [← List.all_eq_true, batchCode_eq]
  have h1 : (loadCode ls rs).all Instr.straight = true := by simp [loadCode, Instr.straight]
  have h2 : transposeIn.all Instr.straight = true := by simp [transposeIn, Instr.straight]
  have h3 : swapIn.all Instr.straight = true := by simp [swapIn, Instr.straight]
  have h4 : core.all Instr.straight = true :=
    List.all_eq_true.mpr fun i h => lanewise_straight i (core_lanewise i h)
  have h5 : transposeOut.all Instr.straight = true := by simp [transposeOut, Instr.straight]
  have h6 : storeCode.all Instr.straight = true := by simp [storeCode, Instr.straight]
  simp only [List.all_append, h1, h2, h3, h4, h5, h6, Bool.and_self]

/-- The updates advance the three pointers, count one batch down, and set the zero flag on the last. -/
theorem tail_exec (ls rs : Nat) (x : State) :
    exec (tailCode ls rs) x =
      { x with
        gpr := assign (assign (assign (assign x.gpr left (x.gpr left + (16 * ls).toUInt64)) right
          (x.gpr right + (16 * rs).toUInt64)) out (x.gpr out + (512 : Nat).toUInt64)) count
          (x.gpr count - (1 : Nat).toUInt64)
        zf := x.gpr count - (1 : Nat).toUInt64 == 0 } := by
  -- Each update writes one general register and sets the zero flag.
  simp only [tailCode, exec, exec1]
  simp [assign]

/-- An address plus an offset, within reach, does not wrap. -/
theorem add_toNat (x : UInt64) (n : Nat) (h : x.toNat + n ≤ addressBound) : (x + n.toUInt64).toNat = x.toNat + n := by
  -- Both summands fit below 2^63, so the machine sum is the plain sum.
  simp only [addressBound] at h
  simp [UInt64.toNat_add]
  omega

/-- A nonzero count minus one does not wrap. -/
theorem sub_toNat (x : UInt64) (h : 1 ≤ x.toNat) : (x - (1 : Nat).toUInt64).toNat = x.toNat - 1 := by
  -- A count of at least one never wraps below zero.
  simp only [Nat.toUInt64_eq, UInt64.ofNat_one]
  rw [UInt64.toNat_sub_of_le]
  · simp
  · rw [UInt64.le_iff_toNat_le]; simpa using h

/-- One step. -/
theorem run_one (p : Array Instr) (s : State) : run p 1 s = step p s := rfl

/-- The updates never branch. -/
theorem tail_straight (ls rs : Nat) : ∀ i ∈ tailCode ls rs, i.straight := by
  -- No update is a branch.
  -- No update is a branch.
  simp [tailCode, Instr.straight]

set_option maxRecDepth 100000 in
/-- One pass of the loop body: a batch, the pointer updates, and the branch back or out. -/
theorem iteration (ls rs : Nat) (s : State) (tableEntry : s.pc = loopHead) (running : s.status = .running) :
    run (program ls rs) ((batchCode ls rs).length + 5) s =
      { exec (tailCode ls rs) (exec (batchCode ls rs) s) with
        pc := if (exec (tailCode ls rs) (exec (batchCode ls rs) s)).zf then finishAt ls rs else loopHead } := by
  -- The same layout, cut three ways: before the batch, before the updates, and before the branch.
  have layout1 : (program ls rs).toList =
      [.test count, .jz (finishAt ls rs)] ++ batchCode ls rs ++ (tailCode ls rs ++ [.jnz loopHead, .vzeroupper, .ret]) := by
    rw [program_toList]; simp only [List.append_assoc]
  have layout2 : (program ls rs).toList =
      ([.test count, .jz (finishAt ls rs)] ++ batchCode ls rs) ++ tailCode ls rs ++ [.jnz loopHead, .vzeroupper, .ret] := by
    rw [program_toList]
  have layout3 : (program ls rs).toList =
      ([.test count, .jz (finishAt ls rs)] ++ batchCode ls rs ++ tailCode ls rs) ++ .jnz loopHead :: [.vzeroupper, .ret] := by
    rw [program_toList]
  -- The batch and the updates run as straight-line blocks, then the branch reads the flag.
  rw [show (batchCode ls rs).length + 5 = (batchCode ls rs).length + ((tailCode ls rs).length + 1) by
    simp [tailCode], run_add, run_add]
  rw [run_block _ _ _ _ layout1 (batch_straight ls rs) s (by simp [tableEntry, loopHead]) running]
  rw [run_block _ _ _ _ layout2 (tail_straight ls rs) _ (by simp; omega) (by simpa using running)]
  have f3 := fetch _ _ _ _ layout3
  rw [List.length_append] at f3
  rw [run_one, step_jnz (t := loopHead)]
  rotate_left
  · exact f3
  · simpa using running
  rw [exec_with_pc]
  have hpc : ([Instr.test count, Instr.jz (finishAt ls rs)] ++ batchCode ls rs).length + (tailCode ls rs).length + 1 =
      finishAt ls rs := by
    simp only [List.length_append, List.length_cons, List.length_nil, finishAt, loopHead,
      show (tailCode ls rs).length = 4 from rfl]
  dsimp only
  rw [hpc]

/-- The closing instructions: clear the upper vector state and return, touching no memory or general register. -/
theorem closing (ls rs : Nat) (x : State) (tableEntry : x.pc = finishAt ls rs) (running : x.status = .running) :
    (run (program ls rs) 2 x).status = .returned ∧ (run (program ls rs) 2 x).mem = x.mem ∧
      (run (program ls rs) 2 x).gpr = x.gpr := by
  -- The same layout, cut before the vector reset and before the return.
  have layout4 : (program ls rs).toList =
      ([.test count, .jz (finishAt ls rs)] ++ batchCode ls rs ++ tailCode ls rs ++ [.jnz loopHead]) ++
        [.vzeroupper] ++ [.ret] := by
    rw [program_toList]; simp only [List.append_assoc, List.cons_append, List.nil_append]
  have layout5 : (program ls rs).toList =
      ([.test count, .jz (finishAt ls rs)] ++ batchCode ls rs ++ tailCode ls rs ++ [.jnz loopHead] ++ [.vzeroupper]) ++
        .ret :: [] := by
    rw [layout4]
  have pre : ([Instr.test count, Instr.jz (finishAt ls rs)] ++ batchCode ls rs ++ tailCode ls rs ++
      [Instr.jnz loopHead]).length = finishAt ls rs := by
    simp only [List.length_append, List.length_cons, List.length_nil, finishAt, loopHead,
      show (tailCode ls rs).length = 4 from rfl]
  have f5 := fetch _ _ _ _ layout5
  rw [List.length_append, pre] at f5
  -- The vector reset touches no memory or general register, then the return stops the routine.
  rw [show 2 = [Instr.vzeroupper].length + 1 from rfl, run_add,
    run_block _ _ _ _ layout4 (by simp [Instr.straight]) x (by rw [tableEntry, pre]) running, pre, run_one, step_ret]
  · simp [exec, exec1]
  · exact f5
  · simpa using running

/-- The opening instructions: skip to the closing ones when there is no batch, and enter the loop otherwise. -/
theorem opening (ls rs : Nat) (s : State) (start : s.pc = 0) (running : s.status = .running) :
    run (program ls rs) 2 s = { s with zf := s.gpr count == 0, pc := if s.gpr count == 0 then finishAt ls rs else loopHead } := by
  -- The same layout, cut before the count check and before the branch.
  have layout0 : (program ls rs).toList =
      [] ++ [.test count] ++ ([.jz (finishAt ls rs)] ++ batchCode ls rs ++ tailCode ls rs ++
        [.jnz loopHead, .vzeroupper, .ret]) := by
    rw [program_toList]; simp only [List.append_assoc, List.cons_append, List.nil_append]
  have layout1 : (program ls rs).toList =
      [.test count] ++ .jz (finishAt ls rs) :: (batchCode ls rs ++ tailCode ls rs ++
        [.jnz loopHead, .vzeroupper, .ret]) := by
    rw [program_toList]; simp only [List.append_assoc, List.cons_append, List.nil_append]
  have f1 := fetch _ _ _ _ layout1
  -- The count check sets the zero flag, then the branch reads it.
  rw [show 2 = [Instr.test count].length + 1 from rfl, run_add,
    run_block _ _ _ _ layout0 (by simp [Instr.straight]) s (by simp [start]) running, run_one, step_jz (t := finishAt ls rs)]
  · simp [exec, exec1, loopHead]
  · exact f1
  · simpa using running

/-- Where a run of batches reads and writes: within reach, and with the output clear of the table and every input. -/
structure Layout (ls rs : Nat) (s : State) (c : Nat) : Prop where
  /-- The constant table is in memory. -/
  table : TableAt s.mem (s.gpr tbl).toNat
  /-- The digests end within reach. -/
  outBound : (s.gpr out).toNat + 512 * c ≤ addressBound
  /-- The left nodes end within reach. -/
  leftBound : (s.gpr left).toNat + 16 * ls * c ≤ addressBound
  /-- The right nodes end within reach. -/
  rightBound : (s.gpr right).toNat + 16 * rs * c ≤ addressBound
  /-- The digests miss the table. -/
  tableApart : Apart ((s.gpr out).toNat, 512 * c) ((s.gpr tbl).toNat, tableSize)
  /-- The digests miss every input node. -/
  inputsApart : ∀ p < 16 * c, Apart ((s.gpr out).toNat, 512 * c) ((s.gpr left).toNat + ls * p, 32) ∧
    Apart ((s.gpr out).toNat, 512 * c) ((s.gpr right).toNat + rs * p, 32)

/-- A finished run of batches: returned, every digest written, nothing else in memory touched, and the saved registers kept. -/
def Done (ls rs : Nat) (s : State) (c : Nat) (f : State) : Prop :=
  f.status = .returned ∧
  (∀ p < 16 * c, ∀ k < 32, f.mem ((s.gpr out).toNat + 32 * p + k) =
    (Sha256.hash (pairMessage s.mem ((s.gpr left).toNat + ls * p) ((s.gpr right).toNat + rs * p))).get! k) ∧
  (∀ a, ¬ ((s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 32 * (16 * c)) → f.mem a = s.mem a) ∧
  (∀ r ∈ calleeSaved, f.gpr r = s.gpr r)

/-- The updates leave the saved registers and the table address alone. -/
theorem tail_gpr (ls rs : Nat) (x : State) (r : Gpr) (saved : r ∈ calleeSaved ∨ r = tbl) :
    (exec (tailCode ls rs) x).gpr r = x.gpr r := by
  -- The updates write only the three addresses and the count.
  rw [tail_exec]
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at saved
  rcases saved with (h | h | h | h | h | h | h) | h <;> subst h <;> simp [assign, left, right, out, count, tbl]

/-- The updates leave memory alone. -/
theorem tail_mem (ls rs : Nat) (x : State) : (exec (tailCode ls rs) x).mem = x.mem := by
  -- The updates write only registers.
  rw [tail_exec]

/-- The updates leave the routine running. -/
theorem tail_status (ls rs : Nat) (x : State) : (exec (tailCode ls rs) x).status = x.status := by
  -- The updates never stop the routine.
  rw [tail_exec]

/-- The updates set the zero flag on the last batch. -/
theorem tail_zf (ls rs : Nat) (x : State) :
    (exec (tailCode ls rs) x).zf = (x.gpr count - (1 : Nat).toUInt64 == 0) := by
  -- The countdown sets the flag.
  rw [tail_exec]

/-- The updates advance the left address by sixteen strides. -/
theorem tail_left (ls rs : Nat) (x : State) :
    (exec (tailCode ls rs) x).gpr left = x.gpr left + (16 * ls).toUInt64 := by
  rw [tail_exec]; simp [assign, right, out, count]

/-- The updates advance the right address by sixteen strides. -/
theorem tail_right (ls rs : Nat) (x : State) :
    (exec (tailCode ls rs) x).gpr right = x.gpr right + (16 * rs).toUInt64 := by
  rw [tail_exec]; simp [assign, out, count]

/-- The updates advance the output address by sixteen digests. -/
theorem tail_out (ls rs : Nat) (x : State) :
    (exec (tailCode ls rs) x).gpr out = x.gpr out + (512 : Nat).toUInt64 := by
  rw [tail_exec]; simp [assign, count]

/-- The updates count one batch down. -/
theorem tail_count (ls rs : Nat) (x : State) :
    (exec (tailCode ls rs) x).gpr count = x.gpr count - (1 : Nat).toUInt64 := by
  rw [tail_exec]; simp [assign]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The loop from its head with c + 1 batches left. -/
theorem loop (ls rs : Nat) (c : Nat) : ∀ s : State, s.pc = loopHead → s.status = .running →
    (s.gpr count).toNat = c + 1 → Layout ls rs s (c + 1) →
    ∃ steps, Done ls rs s (c + 1) (run (program ls rs) steps s) := by
  induction c with
  -- One batch left: run it, then the closing instructions.
  | zero =>
    intro s tableEntry running counted layout
    obtain ⟨outputs, outside, kept⟩ := batch ls rs s layout.table
    -- The count was one, so the countdown sets the zero flag and the loop exits.
    have one : s.gpr count = 1 := UInt64.toNat_inj.mp (by simpa using counted)
    have zf : (exec (tailCode ls rs) (exec (batchCode ls rs) s)).zf = true := by
      rw [tail_zf, kept, one]; rfl
    refine ⟨(batchCode ls rs).length + 5 + 2, ?_⟩
    rw [run_add, iteration ls rs s tableEntry running, zf, if_pos rfl]
    obtain ⟨st, mem, gpr⟩ := closing ls rs { exec (tailCode ls rs) (exec (batchCode ls rs) s) with
      pc := finishAt ls rs } rfl (by simp only; rw [tail_status, exec_status]; exact running)
    -- Every digest is this batch's, and nothing else changed.
    refine ⟨st, fun p hp k hk => ?_, fun a ha => ?_, fun r hr => ?_⟩
    · rw [mem, tail_mem]; exact outputs p (by omega) k hk
    · rw [mem, tail_mem]; exact outside a (by omega)
    · rw [gpr, tail_gpr ls rs _ r (.inl hr), kept]
  | succ c ih =>
    -- More batches left: run one, then the rest from the loop head, by induction.
    intro s tableEntry running counted layout
    obtain ⟨outputs, outside, kept⟩ := batch ls rs s layout.table
    -- The state at the loop head again, one batch further on.
    let y := { exec (tailCode ls rs) (exec (batchCode ls rs) s) with pc := loopHead }
    have O := layout.outBound
    have Lb := layout.leftBound
    have Rb := layout.rightBound
    have yout : (y.gpr out).toNat = (s.gpr out).toNat + 512 := by
      simp only [y]; rw [tail_out, kept, add_toNat _ _ (by omega)]
    have yleft : (y.gpr left).toNat = (s.gpr left).toNat + 16 * ls := by
      have : 16 * ls ≤ 16 * ls * (c + 1 + 1) := Nat.le_mul_of_pos_right _ (by omega)
      simp only [y]; rw [tail_left, kept, add_toNat _ _ (by omega)]
    have yright : (y.gpr right).toNat = (s.gpr right).toNat + 16 * rs := by
      have : 16 * rs ≤ 16 * rs * (c + 1 + 1) := Nat.le_mul_of_pos_right _ (by omega)
      simp only [y]; rw [tail_right, kept, add_toNat _ _ (by omega)]
    have ycount : (y.gpr count).toNat = c + 1 := by
      simp only [y]; rw [tail_count, kept, sub_toNat _ (by omega), counted]; rfl
    have ytbl : y.gpr tbl = s.gpr tbl := by
      simp only [y]; rw [tail_gpr ls rs _ tbl (.inr rfl), kept]
    have ymem : y.mem = (exec (batchCode ls rs) s).mem := by simp only [y]; rw [tail_mem]
    -- The count was more than one, so the loop goes back.
    have zf : (exec (tailCode ls rs) (exec (batchCode ls rs) s)).zf = false := by
      have ne : s.gpr count - (1 : Nat).toUInt64 ≠ 0 := fun h => by
        have := congrArg UInt64.toNat h
        rw [sub_toNat _ (by omega)] at this
        simp at this
        omega
      rw [tail_zf, kept]
      simpa using ne
    -- Products of a stride and a count, split off one batch.
    have lsplit : ∀ p, ls * (16 + p) = 16 * ls + ls * p := fun p => by rw [Nat.mul_add, Nat.mul_comm ls 16]
    have rsplit : ∀ p, rs * (16 + p) = 16 * rs + rs * p := fun p => by rw [Nat.mul_add, Nat.mul_comm rs 16]
    have lnext : 16 * ls * (c + 1 + 1) = 16 * ls + 16 * ls * (c + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    have rnext : 16 * rs * (c + 1 + 1) = 16 * rs + 16 * rs * (c + 1) := by
      rw [Nat.mul_succ, Nat.add_comm]
    -- Memory the batch did not write still holds what it held.
    have kept_at : ∀ a, ¬ ((s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 512) → y.mem a = s.mem a := fun a h => by
      rw [ymem]; exact outside a h
    have apart := layout.inputsApart
    have tapart := layout.tableApart
    simp only [Apart] at apart tapart
    -- The rest of the run still meets the layout, one batch further on.
    have next : Layout ls rs y (c + 1) := by
      refine ⟨fun i hi => ?_, by omega, by rw [yleft]; omega, by rw [yright]; omega, ?_, fun p hp => ?_⟩
      · rw [ytbl, kept_at _ (by omega)]
        exact layout.table i hi
      · simp only [Apart, yout, ytbl]; omega
      · have := apart (16 + p) (by omega)
        rw [lsplit, rsplit] at this
        simp only [Apart, yout, yleft, yright]
        omega
    obtain ⟨steps, st, outs, frame, saved⟩ := ih y rfl (by simp only [y]; rw [tail_status, exec_status]; exact running)
      ycount next
    refine ⟨(batchCode ls rs).length + 5 + steps, ?_⟩
    rw [run_add, iteration ls rs s tableEntry running, zf]
    simp only [Bool.false_eq_true, ↓reduceIte]
    -- Each digest comes from this batch or a later one.
    refine ⟨st, fun p hp k hk => ?_, fun a ha => ?_, fun r hr => ?_⟩
    · by_cases first : p < 16
      · -- This batch's digests: the later batches write past them.
        refine (frame _ (by rw [yout]; omega)).trans ?_
        rw [ymem]
        exact outputs p first k hk
      · -- A later batch's digests, from inputs this batch left alone.
        have := outs (p - 16) (by omega) k hk
        rw [yout, yleft, yright, show (s.gpr out).toNat + 512 + 32 * (p - 16) + k = (s.gpr out).toNat + 32 * p + k by
          omega] at this
        refine this.trans ?_
        have hp' := lsplit (p - 16)
        have hr' := rsplit (p - 16)
        rw [show 16 + (p - 16) = p by omega] at hp' hr'
        rw [show (s.gpr left).toNat + 16 * ls + ls * (p - 16) = (s.gpr left).toNat + ls * p by omega,
          show (s.gpr right).toNat + 16 * rs + rs * (p - 16) = (s.gpr right).toNat + rs * p by omega]
        have := apart p hp
        rw [pairMessage_congr y.mem s.mem _ _ (fun i hi => kept_at _ (by omega)) (fun i hi => kept_at _ (by omega))]
    · exact (frame _ (by rw [yout]; omega)).trans (kept_at _ (by omega))
    · refine (saved r hr).trans ?_
      simp only [y]
      rw [tail_gpr ls rs _ r (.inl hr), kept]

set_option maxRecDepth 100000 in
/--
The sixteen-lane kernel hashes every pair it is given.

Started at its first instruction, with a count of batches of sixteen pairs, it returns having written each pair's digest.
Pair p is the 32 bytes at the left address plus p times the left stride, then the 32 bytes at the right address plus p times the right stride.
Its digest lands 32 p bytes past the output address.
No other memory changes, and the registers the calling convention saves keep their values.

The output must sit clear of the table and of every input node, and every region must lie within reach.
-/
theorem program_correct (ls rs : Nat) (s : State) (start : s.pc = 0) (running : s.status = .running)
    (table : TableAt s.mem (s.gpr tbl).toNat) (n : Nat) (pairs : n = 16 * (s.gpr count).toNat)
    (outBound : (s.gpr out).toNat + 32 * n ≤ addressBound)
    (leftBound : (s.gpr left).toNat + ls * n ≤ addressBound)
    (rightBound : (s.gpr right).toNat + rs * n ≤ addressBound)
    (tableApart : Apart ((s.gpr out).toNat, 32 * n) ((s.gpr tbl).toNat, tableSize))
    (inputsApart : ∀ p < n, Apart ((s.gpr out).toNat, 32 * n) ((s.gpr left).toNat + ls * p, 32) ∧
      Apart ((s.gpr out).toNat, 32 * n) ((s.gpr right).toNat + rs * p, 32)) :
    ∃ steps,
      (run (program ls rs) steps s).status = .returned ∧
      (∀ p < n, ∀ k < 32, (run (program ls rs) steps s).mem ((s.gpr out).toNat + 32 * p + k) =
        (Sha256.hash (pairMessage s.mem ((s.gpr left).toNat + ls * p) ((s.gpr right).toNat + rs * p))).get! k) ∧
      (∀ a, ¬ ((s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 32 * n) → (run (program ls rs) steps s).mem a = s.mem a) ∧
      (∀ r ∈ calleeSaved, (run (program ls rs) steps s).gpr r = s.gpr r) := by
  subst pairs
  have opened := opening ls rs s start running
  cases h : (s.gpr count).toNat with
  | zero =>
    -- No batch: straight to the closing instructions.
    have zero : s.gpr count = 0 := UInt64.toNat_inj.mp (by simpa using h)
    simp only [zero, beq_self_eq_true, ↓reduceIte] at opened
    obtain ⟨st, mem, gpr⟩ := closing ls rs { s with zf := true, pc := finishAt ls rs } rfl running
    refine ⟨2 + 2, ?_⟩
    rw [run_add, opened]
    exact ⟨st, fun p hp => absurd hp (by omega), fun a _ => congrFun mem a, fun r _ => by rw [gpr]⟩
  | succ c =>
    -- At least one batch: the loop, from its head.
    have nonzero : (s.gpr count == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro zero
      rw [zero] at h
      simp at h
    simp only [nonzero, Bool.false_eq_true, ↓reduceIte] at opened
    have layout : Layout ls rs { s with zf := false, pc := loopHead } (c + 1) := by
      refine ⟨table, ?_, ?_, ?_, ?_, ?_⟩
      · simp only; rw [h] at outBound; omega
      · simp only; rw [h] at leftBound
        rw [show 16 * ls * (c + 1) = ls * (16 * (c + 1)) by rw [Nat.mul_comm 16 ls, Nat.mul_assoc]]; exact leftBound
      · simp only; rw [h] at rightBound
        rw [show 16 * rs * (c + 1) = rs * (16 * (c + 1)) by rw [Nat.mul_comm 16 rs, Nat.mul_assoc]]; exact rightBound
      · simp only; rw [h] at tableApart; simp only [Apart] at tableApart ⊢; omega
      · intro p hp
        rw [h] at inputsApart
        have := inputsApart p hp
        simp only [Apart] at this ⊢
        omega
    obtain ⟨steps, st, outs, frame, saved⟩ := loop ls rs c { s with zf := false, pc := loopHead } rfl running h layout
    refine ⟨2 + steps, ?_⟩
    rw [run_add, opened]
    refine ⟨st, fun p hp k hk => outs p (by omega) k hk, fun a ha => frame a (by omega), saved⟩
