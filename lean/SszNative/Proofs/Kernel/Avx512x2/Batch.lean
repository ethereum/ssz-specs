import SszNative.Proofs.Kernel.Avx512x2.Output

/-!
One batch pair of the thirty-two-lane kernel, from the loop head to the pointer updates.

The pair runs the setup, the two first-block loops, the first feed-forwards, the padding loop, and the output.
Each lane l of the first batch hashes pair l, and each lane l of the second batch pair 16 + l.
-/

namespace EthLib.Consensus.Ssz.Native.Kernel.Avx512x2

open EthLib.Cryptography.Hash.Sha256 hiding K IV
open EthLib.Consensus.Ssz.Native.Asm
open EthLib.Consensus.Ssz.Native.Kernel.Avx512 (tbl left right out count home tableEntry transposeOut storeCode epilogue add_toNat
  roundsTo K W PW home_eq_role home_eq_role64 compress_rounds pairMessage_size)

/-- The index of the closing instructions. -/
def finishAt (ls rs : Nat) : Nat := loopHead + (body ls rs).length + 5

/-- The routine's opening: the frame, the empty-count check, and the branch past the loop. -/
def opening (ls rs : Nat) : List Instr := [.subImm sp frame, .test count, .jz (finishAt ls rs)]

/-- The pointer updates and the branch back, after each batch pair. -/
def tailCode (ls rs : Nat) : List Instr :=
  [.addImm left (16 * ls), .addImm right (16 * rs), .addImm out 512, .subImm count 1, .jnz loopHead]

/-- The routine's closing: the frame released, the upper vector state cleared, the result zeroed, and the return. -/
def closingCode : List Instr := [.addImm sp frame, .vzeroupper, .zeroReg .rax, .ret]

/-- The routine's instructions: the opening, a batch pair, the updates, and the closing. -/
theorem program_toList (ls rs : Nat) :
    (program ls rs).toList = opening ls rs ++ body ls rs ++ tailCode ls rs ++ closingCode := by
  simp only [program, opening, tailCode, closingCode, finishAt, List.toList_toArray, List.append_assoc,
    List.cons_append, List.nil_append]
  rfl

/-- A batch pair's instructions, its loops branching back to their heads. -/
theorem body_eq (ls rs : Nat) :
    body ls rs = setupCode ls rs ++ firstBlock true ++ [.jnz (firstHead ls rs), .movImm blocks 2] ++
      firstBlock false ++ [.jnz (secondHead ls rs)] ++ middleCode ++ paddingBlock ++ [.jnz (thirdHead ls rs)] ++
      outputCode := by
  simp only [body, batchCode, List.append_assoc, List.cons_append, List.nil_append]

/-- The opening is three instructions. -/
theorem opening_length (ls rs : Nat) : (opening ls rs).length = loopHead := rfl

/-- The routine, cut before and after one part of a batch pair. -/
theorem layout (ls rs : Nat) (pre seg post : List Instr)
    (h : opening ls rs ++ body ls rs ++ tailCode ls rs ++ closingCode = pre ++ seg ++ post) :
    (program ls rs).toList = pre ++ seg ++ post := by
  rw [program_toList, h]

/-- The second feed-forwards and the digest move write only the first batch's registers, and store nothing. -/
theorem output_writes : writesIn (fun d => d.val < 8) (finishCode 0) = true ∧ storesNothing (finishCode 0) = true ∧
    storesNothing (finishCode 1) = true ∧
    storesNothing ((List.range 8).map (fun j => Instr.vmov (home j) (swapReg (home j)))) = true := by
  -- Every instruction, checked by evaluation.
  decide

/-- A vector of words read back through their defaulted reads is the vector. -/
theorem ofFn_getElem! (v : Vector UInt32 8) : (Vector.ofFn fun j : Fin 8 => v[j.val]!) = v := by
  apply Vector.ext; intro j hj
  simp only [Vector.getElem_ofFn]
  exact getElem!_pos v j hj

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/--
The output: both second feed-forwards, and both batches' digests stored, the second batch's sixteen digests on.

The first batch's final words are its registers plus its kept rows, and likewise for the second batch.
-/
theorem output_spec (y : State) (S T O : Nat) (hS : (y.gpr sp).toNat = S) (hT : (y.gpr tbl).toNat = T)
    (hO : (y.gpr out).toNat = O) (table : TableAt y.mem T) (apart : FrameApart S T)
    (outApart : Apart (O, 1024) (S, frame)) (outTable : Apart (O, 1024) (T, tableSize))
    (outBound : O + 1024 ≤ addressBound) (fA fB : Fin 16 → Vector UInt32 8)
    (hA : ∀ l, ∀ j < 8, y.vec (home j) l + (view y l).mem (S + midSlot 0 j) = (fA l)[j]!)
    (hB : ∀ l, ∀ j < 8, y.vec (swapReg (home j)) l + (view y l).mem (S + midSlot 1 j) = (fB l)[j]!) :
    (∀ p : Fin 16, ∀ k < 32, (exec outputCode y).mem (O + 32 * p.val + k) = (digest (fA p)).get! k) ∧
    (∀ p : Fin 16, ∀ k < 32, (exec outputCode y).mem (O + 512 + 32 * p.val + k) = (digest (fB p)).get! k) ∧
    (∀ a, ¬ (O ≤ a ∧ a < O + 1024) → a < S ∨ S + frame ≤ a → (exec outputCode y).mem a = y.mem a) ∧
    (exec outputCode y).gpr out = y.gpr out + (512 : Nat).toUInt64 ∧
    (∀ r, r ≠ out → (exec outputCode y).gpr r = y.gpr r) := by
  obtain ⟨w0, n0, n1, nm⟩ := output_writes
  simp only [Apart, FrameApart, frame, tableSize] at outApart outTable apart
  have hout : outputCode = finishCode 0 ++ (transposeOut ++ storeCode) ++ [.addImm out 512] ++ finishCode 1 ++
      (List.range 8).map (fun j => Instr.vmov (home j) (swapReg (home j))) ++ (transposeOut ++ storeCode) := by
    simp only [outputCode, List.append_assoc]
  have hrun : exec outputCode y = exec (transposeOut ++ storeCode)
      (exec ((List.range 8).map (fun j => Instr.vmov (home j) (swapReg (home j)))) (exec (finishCode 1)
        (exec [.addImm out 512] (exec (transposeOut ++ storeCode) (exec (finishCode 0) y))))) := by
    rw [hout]; simp only [exec_append]
  rw [hrun]
  -- The first batch's second feed-forward.
  obtain ⟨v1, r1, k1, g1, -, -⟩ := exec_rows (finishCode 0) sp tbl (frame - 64) tableSize finishCode_shape.1 y S T 0 0
    (by rw [hS]; rfl) rfl (by simp [frame]) (by rw [hT]; rfl) (by omega) (by simp only [FrameApart, frame, tableSize]; omega)
  generalize hz1 : exec (finishCode 0) y = z1 at v1 r1 k1 g1
  have midRow : ∀ b j, RowOrOut S (S + midSlot b j) := fun b j => by simp only [RowOrOut, midSlot]; omega
  -- The first batch's digests.
  have tab1 : TableAt z1.mem (z1.gpr tbl).toNat := by
    rw [g1, hT]
    exact table_kept _ _ S T table (by simp only [FrameApart, frame, tableSize]; omega) k1
  obtain ⟨d2, k2, g2, -⟩ := epilogue z1 tab1
  rw [g1, hO] at d2 k2
  have keep2 : ∀ j < 8, (exec (transposeOut ++ storeCode) z1).vec (swapReg (home j)) = z1.vec (swapReg (home j)) :=
    fun j hj => by
      have := swap_role_range 0 j
      rw [← home_eq_role j hj] at this
      exact exec_keepsVec _ _ (epilogue_keeps _ this.1 this.2) z1
  generalize hz2 : exec (transposeOut ++ storeCode) z1 = z2 at d2 k2 g2 keep2
  -- The output pointer moves on.
  have g3 : (exec [.addImm out 512] z2).gpr = assign z2.gpr out (z2.gpr out + (512 : Nat).toUInt64) := by
    simp [exec, exec1]
  have v3 : (exec [.addImm out 512] z2).vec = z2.vec := by simp [exec, exec1]
  have m3 : (exec [.addImm out 512] z2).mem = z2.mem := by simp [exec, exec1]
  generalize hz3 : exec [.addImm out 512] z2 = z3 at g3 v3 m3
  have sp3 : (z3.gpr sp).toNat = S := by rw [g3]; simp [assign, g2, g1, hS]
  have tbl3 : (z3.gpr tbl).toNat = T := by rw [g3]; simp [assign, g2, g1, hT]
  -- The second batch's second feed-forward, from rows the first batch's stores missed.
  obtain ⟨v4, r4, k4, g4, -, -⟩ := exec_rows (finishCode 1) sp tbl (frame - 64) tableSize finishCode_shape.2 z3 S T 0 0
    (by rw [sp3]; rfl) rfl (by simp [frame]) (by rw [tbl3]; rfl) (by omega) (by simp only [FrameApart, frame, tableSize]; omega)
  generalize hz4 : exec (finishCode 1) z3 = z4 at v4 r4 k4 g4
  -- The move of the second batch's words.
  obtain ⟨v5, r5, k5, g5, -, -⟩ := exec_rows _ sp tbl (frame - 64) tableSize moves_shape z4 S T 0 0
    (by rw [g4, sp3]; rfl) rfl (by simp [frame]) (by rw [g4, tbl3]; rfl) (by omega)
    (by simp only [FrameApart, frame, tableSize]; omega)
  generalize hz5 : exec ((List.range 8).map (fun j => Instr.vmov (home j) (swapReg (home j)))) z4 = z5 at v5 r5 k5 g5
  -- The second batch's digests.
  have tab5 : TableAt z5.mem (z5.gpr tbl).toNat := by
    rw [g5, g4, tbl3]
    intro i hi
    simp only [tableSize] at hi
    rw [k5 _ (by first | omega | (simp only [frame] at *; omega)), k4 _ (by first | omega | (simp only [frame] at *; omega)), m3, k2 _ (by first | omega | (simp only [frame] at *; omega)), k1 _ (by first | omega | (simp only [frame] at *; omega))]
    exact table i hi
  obtain ⟨d6, k6, g6, -⟩ := epilogue z5 tab5
  have out5 : (z5.gpr out).toNat = O + 512 := by
    rw [g5, g4, g3]; simp only [assign, ite_true]; rw [g2, g1, add_toNat _ _ (by rw [hO]; omega), hO]
  rw [out5] at d6 k6
  generalize hz6 : exec (transposeOut ++ storeCode) z5 = z6 at d6 k6 g6
  -- The first batch's final words.
  have finalA : ∀ p : Fin 16, (Vector.ofFn fun j : Fin 8 => z1.vec (home j.val) p) = fA p := by
    intro p
    rw [← ofFn_getElem! (fA p)]
    apply Vector.ext; intro j hj
    simp only [Vector.getElem_ofFn]
    rw [v1, ← hA p j hj]
    have := finish_view y.gpr 0 (by omega) (view y p) j hj
    simp only [ite_true] at this
    rw [this, hS]
    rfl
  -- The second batch's final words.
  have finalB : ∀ p : Fin 16, (Vector.ofFn fun j : Fin 8 => z5.vec (home j.val) p) = fB p := by
    intro p
    rw [← ofFn_getElem! (fB p)]
    apply Vector.ext; intro j hj
    simp only [Vector.getElem_ofFn]
    rw [v5, moves_view _ _ j hj]
    simp only [view]
    rw [v4, ← hB p j hj]
    have := finish_view z3.gpr 1 (by omega) (view z3 p) j hj
    simp only [show ¬ (1 = 0) from by decide, ite_false] at this
    rw [this, sp3]
    simp only [view]
    have big := swap_role_range 0 j
    rw [← home_eq_role j hj] at big
    rw [v3, keep2 j hj, v1, viewRun_regs_keep _ _ _ w0 _ _ (by simp only [decide_eq_false_iff_not]; omega)]
    congr 1
    -- The second batch's kept row, untouched by the first batch's stores.
    have e2 : readWord z2.mem (S + midSlot 1 j + 4 * p.val) = readWord z1.mem (S + midSlot 1 j + 4 * p.val) := by
      have := p.isLt
      simp only [readWord]
      rw [k2 _ (by simp only [midSlot]; omega), k2 _ (by simp only [midSlot]; omega),
        k2 _ (by simp only [midSlot]; omega), k2 _ (by simp only [midSlot]; omega)]
    rw [m3, e2, r1 p _ (midRow 1 j), viewRun_mem_nothing _ _ n0]
    rfl
  refine ⟨fun p k hk => ?_, fun p k hk => ?_, fun a hout hframe => ?_, ?_, fun r hr => ?_⟩
  · -- Later instructions leave the first batch's digests.
    rw [k6 _ (by first | omega | (simp only [frame] at *; omega)), k5 _ (by first | omega | (simp only [frame] at *; omega)), k4 _ (by first | omega | (simp only [frame] at *; omega)), m3, d2 p k hk, finalA]
  · rw [d6 p k hk, finalB]
  · rw [k6 _ (by first | omega | (simp only [frame] at *; omega)), k5 a hframe, k4 a hframe, m3, k2 _ (by first | omega | (simp only [frame] at *; omega)), k1 a hframe]
  · rw [g6, g5, g4, g3]; simp [assign, g2, g1]
  · rw [g6, g5, g4, g3]; simp [assign, hr, g2, g1]

end EthLib.Consensus.Ssz.Native.Kernel.Avx512x2
