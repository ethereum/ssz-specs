import SszNative.Proofs.Kernel.Avx512x2.Loops

/-!
The thirty-two-lane kernel between and after its loops: the feed-forwards, and the digests going out.

After the first blocks, each batch adds the initial state and keeps the result in the scratch area.
After the padding blocks, each batch adds that result back, and the sixteen-lane kernel's transpose and stores
write its sixteen digests.
-/

namespace EthLib.Consensus.Ssz.Native.Kernel.Avx512x2

open EthLib.Cryptography.Hash.Sha256 hiding K IV
open EthLib.Consensus.Ssz.Native.Asm
open EthLib.Consensus.Ssz.Native.Kernel.Avx512 (tbl out home ring tmp tableEntry transposeOut storeCode assign_apply range8 epilogue
  add_toNat)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- The first feed-forwards, on one lane: each working word gains its initial-state word, and is kept in a row. -/
theorem feed_view (G : Gpr → UInt64) (S T : Nat) (hS : (G sp).toNat = S) (hT : (G tbl).toNat = T) (l : Fin 16)
    (v : View) (rows : TableRows T l v) (apart : FrameApart S T) (j : Nat) (hj : j < 8) :
    let w := viewRun G (feedCode 0 ++ feedCode 1) v
    w.regs (home j) = v.regs (home j) + Cryptography.Hash.Sha256.IV[j]! ∧
    w.regs (swapReg (home j)) = v.regs (swapReg (home j)) + Cryptography.Hash.Sha256.IV[j]! ∧
    w.mem (S + midSlot 0 j) = v.regs (home j) + Cryptography.Hash.Sha256.IV[j]! ∧
    w.mem (S + midSlot 1 j) = v.regs (swapReg (home j)) + Cryptography.Hash.Sha256.IV[j]! := by
  -- Each initial-state word is read from its table row.
  have row : ∀ i < 8, v.mem (T + ivAvx512 i) = Cryptography.Hash.Sha256.IV[i]! := fun i hi => by
    rw [show ivAvx512 i = 64 * (128 + i) by simp only [ivAvx512]; omega, rows _ (by omega),
      Avx512.tableWord_iv i l.val hi l.isLt]
  -- No table row read is a kept-state row.
  have ne0 : ∀ i, i < 8 → (T + ivAvx512 i = S) = False := by
    intro i hi
    simp only [eq_iff_iff, iff_false]
    simp only [FrameApart, frame, tableSize, ivAvx512] at apart ⊢
    omega
  have ne : ∀ i d, i < 8 → d < 1024 → (T + ivAvx512 i = S + d) = False := by
    intro i d hi hd
    simp only [eq_iff_iff, iff_false]
    simp only [FrameApart, frame, tableSize, ivAvx512] at apart ⊢
    omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [feedCode, forBatch, range8, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
      List.append_nil, rename, tableEntry,
      midSlot, home, swapReg] <;>
    simp [assign, row, viewRun, viewStep, addrOf, hS, hT, ne, ne0]

/-- Whether every store of a list goes to a kept-state row through the stack pointer. -/
def storesMid (body : List Instr) : Bool :=
  body.all fun i => match i with
    | .vstore m _ => m.base == sp && decide (m.disp < 1024) && m.disp % 64 == 0
    | _ => true

/-- The first feed-forwards store only to kept-state rows. -/
theorem feedCode_storesMid : storesMid (feedCode 0 ++ feedCode 1) = true := by
  -- Every store, checked by evaluation.
  decide

/-- The first feed-forwards store only to the kept-state rows. -/
theorem feed_other (G : Gpr → UInt64) (v : View) (a : Nat) (h : ∀ b < 2, ∀ j < 8, a ≠ (G sp).toNat + midSlot b j) :
    (viewRun G (feedCode 0 ++ feedCode 1) v).mem a = v.mem a := by
  apply viewRun_mem_other
  intro i hi
  have := List.all_eq_true.mp feedCode_storesMid i hi
  cases i <;> simp only [storeOf, ne_eq, reduceCtorEq, not_false_eq_true]
  rename_i m r
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
  obtain ⟨⟨base, small⟩, row⟩ := this
  simp only [addrOf, base, Option.some.injEq]
  intro e
  exact h ((m.disp / 64) / 8) (by omega) ((m.disp / 64) % 8) (by omega) (by simp only [midSlot]; omega)

/-- The first feed-forwards are rowwise through the stack and table pointers. -/
theorem feedCode_shape : (feedCode 0 ++ feedCode 1).all (shapeOK sp tbl (frame - 64) tableSize) = true := by
  -- Every instruction, checked by evaluation.
  decide

/-- The second feed-forwards are rowwise through the stack pointer. -/
theorem finishCode_shape : (finishCode 0).all (shapeOK sp tbl (frame - 64) tableSize) = true ∧
    (finishCode 1).all (shapeOK sp tbl (frame - 64) tableSize) = true := by
  -- Every instruction, checked by evaluation.
  decide

/-- The move of the second batch's digest words is rowwise. -/
theorem moves_shape :
    ((List.range 8).map (fun j => Instr.vmov (home j) (swapReg (home j)))).all
      (shapeOK sp tbl (frame - 64) tableSize) = true := by
  -- Every move, checked by evaluation.
  decide

set_option maxRecDepth 20000 in
/-- A batch's second feed-forward, on one lane: each working word gains its kept row. -/
theorem finish_view (G : Gpr → UInt64) (b : Nat) (hb : b < 2) (v : View) (j : Nat) (hj : j < 8) :
    (viewRun G (finishCode b) v).regs (if b = 0 then home j else swapReg (home j)) =
      v.regs (if b = 0 then home j else swapReg (home j)) + v.mem ((G sp).toNat + midSlot b j) := by
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;>
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [finishCode, forBatch, range8, List.map_cons, List.map_nil, rename, home, swapReg, midSlot] <;>
    simp [assign, viewRun, viewStep, addrOf]

/-- The digest words' move, on one lane: the first batch's registers take the second batch's. -/
theorem moves_view (G : Gpr → UInt64) (v : View) (j : Nat) (hj : j < 8) :
    (viewRun G ((List.range 8).map (fun j => Instr.vmov (home j) (swapReg (home j)))) v).regs (home j) =
      v.regs (swapReg (home j)) := by
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [range8, List.map_cons, List.map_nil, home, swapReg] <;>
    simp [assign, viewRun, viewStep]

/-- Whether an instruction moves lanes or stores, and leaves a register alone. -/
def keepsVec (r : Vreg) : Instr → Bool
  | .vload d _ | .vmov d _ | .vshufps d _ _ _ | .vpermi2q d _ _ | .vpermi2d d _ _ | .vshufb d _ _ => d != r
  | .vstore _ _ => true
  | _ => false

/-- A list of such instructions leaves the register alone. -/
theorem exec_keepsVec (r : Vreg) (body : List Instr) (h : body.all (keepsVec r) = true) (s : State) :
    (exec body s).vec r = s.vec r := by
  induction body generalizing s with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    rw [exec_cons, ih h.2]
    -- The first instruction writes another register, or memory.
    have hi := h.1
    cases i <;> simp [keepsVec] at hi <;> simp only [exec1, assign] <;> rw [ite_eq_right (Ne.symm hi)]

/-- A batch's transpose and stores leave the second batch's registers. -/
theorem epilogue_keeps : ∀ r : Vreg, 8 ≤ r.val → r.val < 16 → (transposeOut ++ storeCode).all (keepsVec r) = true := by
  -- Every register, checked by evaluation.
  decide

/-- The address of a digest byte, split at the second batch. -/
theorem out_split (O p k : Nat) (hp : 16 ≤ p) : O + 512 + 32 * (p - 16) + k = O + 32 * p + k := by omega

end EthLib.Consensus.Ssz.Native.Kernel.Avx512x2
