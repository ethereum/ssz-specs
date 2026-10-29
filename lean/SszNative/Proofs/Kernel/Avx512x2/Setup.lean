import SszNative.Proofs.Kernel.Avx512x2.Steps

/-!
The thirty-two-lane kernel's setup: both batches' messages loaded, their input words stored, and both initial states.

After it, every lane meets the first-block invariant before round 0.
-/

namespace EthLib.Consensus.Ssz.Native.Kernel.Avx512x2

open EthLib.Cryptography.Hash.Sha256 hiding K IV
open EthLib.Consensus.Ssz.Native.Asm
open EthLib.Consensus.Ssz.Native.Kernel.Avx512 (left right out count tbl tableEntry loadCode transposeIn swapIn home ring tmp role W
  W_input prologue pairMessage_congr add_toNat home_eq_role roundsTo assign_apply range8)

/-- Lane l's message in batch b: the pair 16b + l from the batch's node addresses. -/
def msg (mem : Nat → UInt8) (L R ls rs : Nat) (l : Fin 16) (b : Nat) : ByteArray :=
  pairMessage mem (L + ls * (16 * b + l.val)) (R + rs * (16 * b + l.val))

/-- Memory and registers before a batch pair, as its setup needs them. -/
structure SetupPre (ls rs : Nat) (s : State) : Prop where
  /-- The constant table is in memory. -/
  table : TableAt s.mem (s.gpr tbl).toNat
  /-- The scratch area misses the table. -/
  apart : FrameApart (s.gpr sp).toNat (s.gpr tbl).toNat
  /-- The scratch area misses every input node. -/
  inputs : ∀ p < 32, Apart ((s.gpr left).toNat + ls * p, 32) ((s.gpr sp).toNat, frame) ∧
    Apart ((s.gpr right).toNat + rs * p, 32) ((s.gpr sp).toNat, frame)
  /-- The second batch's left nodes start within reach. -/
  leftBound : (s.gpr left).toNat + 16 * ls ≤ addressBound
  /-- The second batch's right nodes start within reach. -/
  rightBound : (s.gpr right).toNat + 16 * rs ≤ addressBound
  /-- The scratch area ends within reach. -/
  frameBound : (s.gpr sp).toNat + frame ≤ addressBound

/-- A table row, as a lane of memory holding the table sees it. -/
theorem table_row (mem : Nat → UInt8) (T : Nat) (table : TableAt mem T) (l : Fin 16) (row : Nat) (h : row < 149) :
    readWord mem (T + 64 * row + 4 * l.val) = tableWord (16 * row + l.val) := by
  -- Row r, lane l is table word 16r + l.
  rw [show T + 64 * row + 4 * l.val = T + 4 * (16 * row + l.val) by omega]
  exact readWord_table mem T table _ (by simp only [tableSize]; omega)

/-- The table, unchanged where memory is unchanged off the scratch area, still holds. -/
theorem table_kept (mem mem' : Nat → UInt8) (S T : Nat) (table : TableAt mem T) (apart : FrameApart S T)
    (kept : ∀ a, a < S ∨ S + frame ≤ a → mem' a = mem a) : TableAt mem' T := by
  intro i hi
  simp only [FrameApart] at apart
  rw [kept _ (by omega)]
  exact table i hi

/-- Pairs whose nodes miss the scratch area read the same through memory unchanged off it. -/
theorem msg_kept (mem mem' : Nat → UInt8) (S l r : Nat)
    (kept : ∀ a, a < S ∨ S + frame ≤ a → mem' a = mem a)
    (al : Apart (l, 32) (S, frame)) (ar : Apart (r, 32) (S, frame)) :
    pairMessage mem' l r = pairMessage mem l r := by
  simp only [Apart] at al ar
  exact pairMessage_congr _ _ _ _ (fun i hi => kept _ (by omega)) (fun i hi => kept _ (by omega))

/-- One batch's input-word stores. -/
def inputStores (b : Nat) : List Instr := (List.range 16).map fun t => .vstore ⟨sp, wordSlot b t⟩ (ring t)

/-- The input-word stores are rowwise through the stack pointer. -/
theorem inputStores_shape (b : Nat) (hb : b < 2) :
    (inputStores b).all (shapeOK sp tbl (frame - 64) tableSize) = true := by
  -- Both batches, checked by evaluation.
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> decide

/-- The input-word stores write no register. -/
theorem inputStores_regs (G : Gpr → UInt64) (b : Nat) (v : View) : (viewRun G (inputStores b) v).regs = v.regs := by
  funext r
  apply viewRun_regs_other
  intro i hi
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hi
  simp [destOf]

/-- The input-word stores write only their batch's rows. -/
theorem inputStores_other (G : Gpr → UInt64) (b : Nat) (v : View) (a : Nat)
    (h : ∀ u < 16, a ≠ (G sp).toNat + wordSlot b u) : (viewRun G (inputStores b) v).mem a = v.mem a := by
  apply viewRun_mem_other
  intro i hi
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
  simp only [storeOf, addrOf, ne_eq, Option.some.injEq]
  exact fun e => h u (List.mem_range.mp hu) e.symm

set_option maxRecDepth 20000 in
/-- The initial-state loads: both batches' working words start as the initial state. -/
theorem ivCode_view (G : Gpr → UInt64) (T : Nat) (hT : (G tbl).toNat = T) (l : Fin 16) (v : View)
    (rows : TableRows T l v) (j : Nat) (hj : j < 8) :
    (viewRun G (ivCode 0 ++ ivCode 1) v).regs (home j) = Cryptography.Hash.Sha256.IV[j]! ∧
    (viewRun G (ivCode 0 ++ ivCode 1) v).regs (swapReg (home j)) = Cryptography.Hash.Sha256.IV[j]! := by
  -- Each word is loaded from its table row.
  have row : ∀ i < 8, v.mem ((G tbl).toNat + ivAvx512 i) = Cryptography.Hash.Sha256.IV[i]! := fun i hi => by
    rw [hT, show ivAvx512 i = 64 * (128 + i) by simp only [ivAvx512]; omega, rows _ (by omega),
      Avx512.tableWord_iv i l.val hi l.isLt]
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ivCode, forBatch, range8, List.map_cons, List.map_nil, List.cons_append, List.nil_append, rename,
      viewRun, viewStep, addrOf,
      tableEntry, ite_true, home, swapReg] <;> simp [row, viewRun, viewStep, addrOf, assign]

/-- The initial-state loads store nothing. -/
theorem ivCode_mem (G : Gpr → UInt64) (v : View) : (viewRun G (ivCode 0 ++ ivCode 1) v).mem = v.mem := by
  apply viewRun_mem_nothing
  -- Every load, checked by evaluation.
  decide

/-- The initial-state loads read table rows through the table pointer. -/
theorem ivCode_shape : (ivCode 0 ++ ivCode 1).all (shapeOK sp tbl (frame - 64) tableSize) = true := by
  -- Every load, checked by evaluation.
  decide

/-- The setup's last instructions set the loop pointers and count, and touch neither vectors nor memory. -/
theorem pointers_exec (x : State) :
    let y := exec [.movReg words sp, .addImm words (wordsBase 0), .movReg consts tbl, .movImm blocks 6] x
    y.vec = x.vec ∧ y.mem = x.mem ∧ y.gpr words = x.gpr sp + (wordsBase 0).toUInt64 ∧ y.gpr consts = x.gpr tbl ∧
      y.gpr blocks = 6 ∧ ∀ r, r ≠ words → r ≠ consts → r ≠ blocks → y.gpr r = x.gpr r := by
  -- Four register writes.
  refine ⟨rfl, rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_⟩ <;> simp [exec, exec1, assign, *]

/-- The pointer advance between the batches touches neither vectors nor memory. -/
theorem advance_exec (ls rs : Nat) (x : State) :
    let y := exec [.addImm left (16 * ls), .addImm right (16 * rs)] x
    y.vec = x.vec ∧ y.mem = x.mem ∧ y.gpr left = x.gpr left + (16 * ls).toUInt64 ∧
      y.gpr right = x.gpr right + (16 * rs).toUInt64 ∧ ∀ r, r ≠ left → r ≠ right → y.gpr r = x.gpr r := by
  -- Two register writes.
  refine ⟨rfl, rfl, ?_, ?_, fun r h1 h2 => ?_⟩ <;> simp [exec, exec1, assign, *]

/-- The setup, as its parts. -/
theorem setupCode_eq (ls rs : Nat) :
    setupCode ls rs = (loadCode ls rs ++ transposeIn ++ swapIn) ++ inputStores 0 ++
      [.addImm left (16 * ls), .addImm right (16 * rs)] ++ (loadCode ls rs ++ transposeIn ++ swapIn) ++
      inputStores 1 ++ (ivCode 0 ++ ivCode 1) ++
      [.movReg words sp, .addImm words (wordsBase 0), .movReg consts tbl, .movImm blocks 6] := by
  simp only [setupCode, loadStore, inputStores, List.append_assoc]

/-- A word read through memory unchanged off the scratch area, from outside it, is the same word. -/
theorem readWord_kept (mem mem' : Nat → UInt8) (S a : Nat) (kept : ∀ x, x < S ∨ S + frame ≤ x → mem' x = mem x)
    (out : a + 4 ≤ S ∨ S + frame ≤ a) : readWord mem' a = readWord mem a := by
  simp only [readWord]
  rw [kept a (by omega), kept (a + 1) (by omega), kept (a + 2) (by omega), kept (a + 3) (by omega)]

/-- With no rounds yet, the working words are where they started. -/
theorem roundsTo_zero (st : Vector UInt32 8) (k w : Nat → UInt32) : roundsTo st k w 0 = st := rfl

set_option maxHeartbeats 1000000 in
/--
The setup: every lane meets the first-block invariant before round 0, for both batches' messages.

Only the scratch area changes in memory.
The left and right addresses move to the second batch, the loop pointers and count are set, and no other register changes.
-/
theorem setup_spec (ls rs : Nat) (s : State) (pre : SetupPre ls rs s) :
    let x := exec (setupCode ls rs) s
    (∀ l, FirstInv (s.gpr sp).toNat (s.gpr tbl).toNat l
      (msg s.mem (s.gpr left).toNat (s.gpr right).toNat ls rs l) 0 (view x l)) ∧
    (∀ a, a < (s.gpr sp).toNat ∨ (s.gpr sp).toNat + frame ≤ a → x.mem a = s.mem a) ∧
    x.gpr left = s.gpr left + (16 * ls).toUInt64 ∧ x.gpr right = s.gpr right + (16 * rs).toUInt64 ∧
    (x.gpr words).toNat = (s.gpr sp).toNat + wordsBase 0 ∧ (x.gpr consts).toNat = (s.gpr tbl).toNat ∧
    x.gpr blocks = 6 ∧
    (∀ r, r ≠ left → r ≠ right → r ≠ words → r ≠ consts → r ≠ blocks → x.gpr r = s.gpr r) := by
  intro x
  have table := pre.table
  have apart := pre.apart
  have inputs := pre.inputs
  generalize hS : (s.gpr sp).toNat = S at *
  generalize hT : (s.gpr tbl).toNat = T at *
  -- The parts, one after the other.
  have hx : x = exec [.movReg words sp, .addImm words (wordsBase 0), .movReg consts tbl, .movImm blocks 6]
      (exec (ivCode 0 ++ ivCode 1) (exec (inputStores 1) (exec (loadCode ls rs ++ transposeIn ++ swapIn)
        (exec [.addImm left (16 * ls), .addImm right (16 * rs)] (exec (inputStores 0)
          (exec (loadCode ls rs ++ transposeIn ++ swapIn) s)))))) := by
    simp only [x, setupCode_eq, exec_append]
  -- The first batch's loads and transpose.
  obtain ⟨ring1, g1, m1, -⟩ := prologue ls rs s (by rw [hT]; exact table)
  generalize hy1 : exec (loadCode ls rs ++ transposeIn ++ swapIn) s = y1 at ring1 g1 m1 hx
  -- The first batch's input-word stores.
  obtain ⟨v2, r2, k2, g2, -, -⟩ := exec_rows (inputStores 0) sp tbl (frame - 64) tableSize (inputStores_shape 0 (by omega))
    y1 S T 0 0 (by rw [g1, hS]; rfl) rfl (by simp [frame]) (by rw [g1, hT]; rfl) (by omega) apart
  generalize hy2 : exec (inputStores 0) y1 = y2 at v2 r2 k2 g2 hx
  -- The advance to the second batch.
  obtain ⟨v3, m3, l3, rr3, g3⟩ := advance_exec ls rs y2
  generalize hy3 : exec [.addImm left (16 * ls), .addImm right (16 * rs)] y2 = y3 at v3 m3 l3 rr3 g3 hx
  have k3 : ∀ a, a < S ∨ S + frame ≤ a → y3.mem a = s.mem a := fun a ha => by rw [m3, k2 a ha, m1]
  have sp3 : (y3.gpr sp).toNat = S := by rw [g3 _ (by decide) (by decide), g2, g1, hS]
  have tbl3 : (y3.gpr tbl).toNat = T := by rw [g3 _ (by decide) (by decide), g2, g1, hT]
  have left3 : (y3.gpr left).toNat = (s.gpr left).toNat + 16 * ls := by
    rw [l3, g2, g1, add_toNat _ _ pre.leftBound]
  have right3 : (y3.gpr right).toNat = (s.gpr right).toNat + 16 * rs := by
    rw [rr3, g2, g1, add_toNat _ _ pre.rightBound]
  -- The second batch's loads and transpose, from inputs the first batch's stores left alone.
  obtain ⟨ring4, g4, m4, -⟩ := prologue ls rs y3 (by rw [tbl3]; exact table_kept _ _ S T table apart k3)
  generalize hy4 : exec (loadCode ls rs ++ transposeIn ++ swapIn) y3 = y4 at ring4 g4 m4 hx
  -- The second batch's input-word stores.
  obtain ⟨v5, r5, k5, g5, -, -⟩ := exec_rows (inputStores 1) sp tbl (frame - 64) tableSize (inputStores_shape 1 (by omega))
    y4 S T 0 0 (by rw [g4, sp3]; rfl) rfl (by simp [frame]) (by rw [g4, tbl3]; rfl) (by omega) apart
  generalize hy5 : exec (inputStores 1) y4 = y5 at v5 r5 k5 g5 hx
  -- Both initial states.
  obtain ⟨v6, r6, k6, g6, -, -⟩ := exec_rows (ivCode 0 ++ ivCode 1) sp tbl (frame - 64) tableSize ivCode_shape
    y5 S T 0 0 (by rw [g5, g4, sp3]; rfl) rfl (by simp [frame]) (by rw [g5, g4, tbl3]; rfl) (by omega) apart
  generalize hy6 : exec (ivCode 0 ++ ivCode 1) y5 = y6 at v6 r6 k6 g6 hx
  obtain ⟨vx, mx, wx, cx, bx, gx⟩ := pointers_exec y6
  rw [← hx] at vx mx wx cx bx gx
  have k6s : ∀ a, a < S ∨ S + frame ≤ a → y6.mem a = s.mem a := fun a ha => by
    rw [k6 a ha, k5 a ha, m4, k3 a ha]
  have sp6 : y6.gpr sp = y3.gpr sp := by rw [g6, g5, g4]
  have tbl6 : y6.gpr tbl = y3.gpr tbl := by rw [g6, g5, g4]
  refine ⟨fun l => ?_, fun a ha => by rw [mx, k6s a ha], ?_, ?_, ?_, ?_, bx, fun r h1 h2 h3 h4 h5 => ?_⟩
  · -- Each lane: the table rows, the input words, and the initial states.
    have rows : ∀ (v : View), (∀ row < 149, v.mem (T + 64 * row) = readWord s.mem (T + 64 * row + 4 * l.val)) →
        TableRows T l v := fun v h row hrow => by rw [h row hrow, table_row _ T table l row hrow]
    have outT : ∀ row < 149, T + 64 * row + 4 * l.val + 4 ≤ S ∨ S + frame ≤ T + 64 * row + 4 * l.val := by
      intro row hrow
      have := l.isLt
      simp only [FrameApart, frame, tableSize] at apart ⊢
      omega
    have rowOut : ∀ row < 149, RowOrOut S (T + 64 * row) := by
      intro row hrow
      simp only [RowOrOut, FrameApart, frame, tableSize] at apart ⊢
      omega
    -- The table as the fifth part's lanes see it.
    have rows5 : TableRows T l (view y5 l) := rows _ fun row hrow =>
      readWord_kept _ _ S _ (fun a ha => by rw [k5 a ha, m4, k3 a ha]) (outT row hrow)
    have slotRow : ∀ b u, RowOrOut S (S + wordSlot b u) := fun b u => by
      simp only [RowOrOut, wordSlot, frame]; omega
    -- The stored words of both batches.
    have word1 : ∀ u < 16, (view y5 l).mem (S + wordSlot 1 u) =
        W (msg s.mem (s.gpr left).toNat (s.gpr right).toNat ls rs l 1) u := by
      intro u hu
      simp only [view]
      rw [r5 l _ (slotRow 1 u), ← sp3, ← g4, inputStores,
        viewRun_stores _ (wordSlot 1) ring 16 _ (fun a b ha hb e => by simp only [wordSlot, frame] at e; omega) u hu]
      simp only [view]
      rw [ring4 u hu l, Avx512.W_input _ u hu, msg, left3, right3,
        show (s.gpr left).toNat + 16 * ls + ls * l.val = (s.gpr left).toNat + ls * (16 * 1 + l.val) by
          rw [Nat.mul_add]; omega,
        show (s.gpr right).toNat + 16 * rs + rs * l.val = (s.gpr right).toNat + rs * (16 * 1 + l.val) by
          rw [Nat.mul_add]; omega,
        msg_kept s.mem y3.mem S _ _ k3 (inputs (16 * 1 + l.val) (by omega)).1 (inputs (16 * 1 + l.val) (by omega)).2]
    have word0 : ∀ u < 16, (view y5 l).mem (S + wordSlot 0 u) =
        W (msg s.mem (s.gpr left).toNat (s.gpr right).toNat ls rs l 0) u := by
      intro u hu
      simp only [view]
      rw [r5 l _ (slotRow 0 u), inputStores_other _ _ _ _ (fun u' _ e => by
        rw [g4, sp3] at e; simp only [wordSlot, frame] at e; omega)]
      simp only [view]
      rw [m4, m3, r2 l _ (slotRow 0 u), ← hS, ← g1, inputStores,
        viewRun_stores _ (wordSlot 0) ring 16 _ (fun a b ha hb e => by simp only [wordSlot, frame] at e; omega) u hu]
      simp only [view]
      rw [ring1 u hu l, Avx512.W_input _ u hu, msg, g1]
      simp only [Nat.mul_zero, Nat.zero_add]
    -- The final lanes are the sixth part's.
    have vxl : view x l = view y6 l := by simp only [view, vx, mx]
    have reg6 : ∀ r, (view y6 l).regs r = (viewRun y5.gpr (ivCode 0 ++ ivCode 1) (view y5 l)).regs r :=
      fun r => v6 r l
    have mem6 : ∀ a, RowOrOut S a → (view y6 l).mem a = (view y5 l).mem a := fun a ha => by
      simp only [view]
      rw [r6 l a ha, ivCode_mem]
      rfl
    have iv := ivCode_view y5.gpr T (by rw [g5, g4, tbl3]) l (view y5 l) rows5
    rw [vxl]
    refine ⟨?_, ?_, fun b hb u hu _ => ?_, fun row hrow => ?_⟩
    · apply Vector.ext; intro j hj
      simp only [Vector.getElem_ofFn, roundsTo_zero]
      rw [← home_eq_role j hj, reg6, (iv j hj).1, getElem!_pos Cryptography.Hash.Sha256.IV j hj]
    · apply Vector.ext; intro j hj
      simp only [Vector.getElem_ofFn, roundsTo_zero]
      rw [← home_eq_role j hj, reg6, (iv j hj).2, getElem!_pos Cryptography.Hash.Sha256.IV j hj]
    · rw [mem6 _ (slotRow b u)]
      rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
      · exact word0 u (by omega)
      · exact word1 u (by omega)
    · rw [mem6 _ (rowOut row hrow)]
      exact rows5 row hrow
  · rw [gx _ (by decide) (by decide) (by decide), g6, g5, g4, l3, g2, g1]
  · rw [gx _ (by decide) (by decide) (by decide), g6, g5, g4, rr3, g2, g1]
  · rw [wx, sp6, add_toNat _ _ (by rw [sp3]; have := pre.frameBound; simp only [wordsBase, frame] at this ⊢; omega),
      sp3]
  · rw [cx, tbl6, tbl3]
  · rw [gx r h3 h4 h5, g6, g5, g4, g3 r h1 h2, g2, g1]

end EthLib.Consensus.Ssz.Native.Kernel.Avx512x2
