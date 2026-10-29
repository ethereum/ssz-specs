import SszNative.Proofs.Asm.Machine
import SszNative.Proofs.Kernel.Avx512x2.Pair

/-!
The thirty-two-lane kernel, start to return.

The routine reserves its scratch area below the stack pointer, tests the count, and skips to the end when it is zero.
Each pass of its loop is a batch pair, then the pointer updates and the branch back while pairs remain.
At the end, it releases the scratch area, clears the upper vector state, and returns.
-/

namespace Ssz.Native.Kernel.Avx512x2

open Ssz.Sha256 Ssz.Native.Asm
open Ssz.Native.Kernel.Avx512 (tbl left right out count fetch step_jz step_jnz step_ret run_one add_toNat sub_toNat
  pairMessage_congr)

/-- The updates advance the three pointers, count one pair down, and set the zero flag on the last. -/
theorem tail_exec (ls rs : Nat) (x : State) :
    exec ([.addImm left (16 * ls), .addImm right (16 * rs), .addImm out 512, .subImm count 1] : List Instr) x =
      { x with
        gpr := assign (assign (assign (assign x.gpr left (x.gpr left + (16 * ls).toUInt64)) right
          (x.gpr right + (16 * rs).toUInt64)) out (x.gpr out + (512 : Nat).toUInt64)) count
          (x.gpr count - (1 : Nat).toUInt64)
        zf := x.gpr count - (1 : Nat).toUInt64 == 0
        cf := x.gpr count < (1 : Nat).toUInt64 } := by
  -- Each update writes one general register and sets the zero and carry flags.
  simp only [exec, exec1]
  simp [assign]

/-- The routine, cut before the updates of a pair. -/
theorem layout_tail (ls rs : Nat) : (program ls rs).toList =
    (opening ls rs ++ body ls rs) ++
      [.addImm left (16 * ls), .addImm right (16 * rs), .addImm out 512, .subImm count 1] ++
      (.jnz loopHead :: closingCode) := by
  rw [program_toList]; simp only [tailCode, List.append_assoc, List.cons_append, List.nil_append]

/-- One pass of the loop: a batch pair, the updates, and the branch back or out. -/
theorem iteration (ls rs : Nat) (s : State) (hpc : s.pc = loopHead) (running : s.status = .running)
    (pre : BatchPre ls rs s) : ∃ n y, PairDone ls rs s y ∧
      run (program ls rs) n s = { exec [.addImm left (16 * ls), .addImm right (16 * rs), .addImm out 512,
        .subImm count 1] y with pc := if (exec [.addImm left (16 * ls), .addImm right (16 * rs), .addImm out 512,
          .subImm count 1] y).zf then finishAt ls rs else loopHead } := by
  obtain ⟨n, done⟩ := pair_run ls rs s hpc running pre
  refine ⟨n + (4 + 1), run (program ls rs) n s, done, ?_⟩
  obtain ⟨st, pc, -⟩ := done
  rw [run_add]
  generalize run (program ls rs) n s = y at st pc ⊢
  have rb := run_block _ _ _ _ (layout_tail ls rs) (by simp [Instr.straight]) y
    (by rw [pc, List.length_append, opening_length]) st
  have f := fetch _ _ _ _ (show (program ls rs).toList = ((opening ls rs ++ body ls rs) ++
      [.addImm left (16 * ls), .addImm right (16 * rs), .addImm out 512, .subImm count 1]) ++
      .jnz loopHead :: closingCode by rw [layout_tail])
  simp only [List.length_append, List.length_cons, List.length_nil] at f rb
  rw [run_add, rb, run_one, step_jnz _ _ loopHead (by dsimp only; exact f) (by simpa using st)]
  rfl

/-- The closing instructions: release the scratch area, clear the upper vector state, zero the result, and return. -/
theorem closing (ls rs : Nat) (x : State) (hpc : x.pc = finishAt ls rs) (running : x.status = .running) :
    (run (program ls rs) 4 x).status = .returned ∧ (run (program ls rs) 4 x).mem = x.mem ∧
      (run (program ls rs) 4 x).gpr = assign (assign x.gpr sp (x.gpr sp + frame.toUInt64)) .rax 0 := by
  have layout4 : (program ls rs).toList =
      (opening ls rs ++ body ls rs ++ tailCode ls rs) ++ [.addImm sp frame, .vzeroupper, .zeroReg .rax] ++ [.ret] := by
    rw [program_toList]; simp only [closingCode, List.append_assoc, List.cons_append, List.nil_append]
  have pre : (opening ls rs ++ body ls rs ++ tailCode ls rs).length = finishAt ls rs := by
    simp only [List.length_append, opening_length, tailCode, List.length_cons, List.length_nil, finishAt]
  have f := fetch _ _ _ _ (show (program ls rs).toList = ((opening ls rs ++ body ls rs ++ tailCode ls rs) ++
    [.addImm sp frame, .vzeroupper, .zeroReg .rax]) ++ .ret :: [] by rw [layout4])
  rw [List.length_append, pre] at f
  rw [show 4 = [Instr.addImm sp frame, .vzeroupper, .zeroReg .rax].length + 1 from rfl, run_add,
    run_block _ _ _ _ layout4 (by simp [Instr.straight]) x (by rw [hpc, pre]) running, pre, run_one,
    step_ret _ _ (by simpa using f) (by simpa using running)]
  refine ⟨rfl, ?_, ?_⟩ <;> simp [exec, exec1]

/-- The opening instructions: reserve the scratch area, and skip to the closing ones when there is no pair. -/
theorem opening_run (ls rs : Nat) (s : State) (start : s.pc = 0) (running : s.status = .running) :
    let y := run (program ls rs) 3 s
    y.gpr = assign s.gpr sp (s.gpr sp - frame.toUInt64) ∧ y.vec = s.vec ∧ y.mem = s.mem ∧ y.cpu = s.cpu ∧
      y.status = s.status ∧ y.pc = (if s.gpr count == 0 then finishAt ls rs else loopHead) := by
  intro y
  have layout0 : (program ls rs).toList =
      [] ++ [.subImm sp frame, .test count] ++ (.jz (finishAt ls rs) :: (body ls rs ++ tailCode ls rs ++
        closingCode)) := by
    rw [program_toList]; simp only [opening, List.append_assoc, List.cons_append, List.nil_append]
  have f := fetch _ _ _ _ (show (program ls rs).toList = [.subImm sp frame, .test count] ++
    .jz (finishAt ls rs) :: (body ls rs ++ tailCode ls rs ++ closingCode) by rw [layout0]; rfl)
  have hy : y = run (program ls rs) 1 (run (program ls rs) [Instr.subImm sp frame, .test count].length s) := by
    simp only [y]; rw [← run_add]; rfl
  rw [hy, run_block _ _ _ _ layout0 (by simp [Instr.straight]) s (by simp [start]) running, run_one,
    step_jz _ _ (finishAt ls rs) (by simpa using f) (by simpa using running)]
  refine ⟨?_, rfl, rfl, rfl, by simp [running], ?_⟩
  · simp [exec, exec1, assign]
  · simp [exec, exec1, assign, loopHead]


/-- Where a run of batch pairs reads and writes: within reach, the output clear of the table, the inputs, and the scratch area. -/
structure Layout (ls rs : Nat) (s : State) (c : Nat) : Prop where
  /-- The constant table is in memory. -/
  table : TableAt s.mem (s.gpr tbl).toNat
  /-- The digests end within reach. -/
  outBound : (s.gpr out).toNat + 1024 * c ≤ addressBound
  /-- The left nodes end within reach. -/
  leftBound : (s.gpr left).toNat + 32 * ls * c ≤ addressBound
  /-- The right nodes end within reach. -/
  rightBound : (s.gpr right).toNat + 32 * rs * c ≤ addressBound
  /-- The table ends within reach. -/
  tableBound : (s.gpr tbl).toNat + tableSize ≤ addressBound
  /-- The scratch area ends within reach. -/
  frameBound : (s.gpr sp).toNat + frame ≤ addressBound
  /-- The digests miss the table. -/
  tableApart : Apart ((s.gpr out).toNat, 1024 * c) ((s.gpr tbl).toNat, tableSize)
  /-- The digests miss every input node. -/
  inputsApart : ∀ p < 32 * c, Apart ((s.gpr out).toNat, 1024 * c) ((s.gpr left).toNat + ls * p, 32) ∧
    Apart ((s.gpr out).toNat, 1024 * c) ((s.gpr right).toNat + rs * p, 32)
  /-- The scratch area misses the table. -/
  frameTable : FrameApart (s.gpr sp).toNat (s.gpr tbl).toNat
  /-- The scratch area misses the digests. -/
  frameOut : Apart ((s.gpr out).toNat, 1024 * c) ((s.gpr sp).toNat, frame)
  /-- The scratch area misses every input node. -/
  frameInputs : ∀ p < 32 * c, Apart ((s.gpr left).toNat + ls * p, 32) ((s.gpr sp).toNat, frame) ∧
    Apart ((s.gpr right).toNat + rs * p, 32) ((s.gpr sp).toNat, frame)

set_option maxRecDepth 10000 in
/-- A layout for at least one pair meets the first pair's needs. -/
theorem Layout.pre {ls rs : Nat} {s : State} {c : Nat} (h : Layout ls rs s (c + 1)) : BatchPre ls rs s := by
  have lb := h.leftBound
  have rb := h.rightBound
  have ob := h.outBound
  have f := h.frameOut
  have t := h.tableApart
  simp only [Apart] at f t
  -- A product with c + 1 is at least the product with one.
  have ml := Nat.mul_le_mul_left (32 * ls) (show 1 ≤ c + 1 by omega)
  have mr := Nat.mul_le_mul_left (32 * rs) (show 1 ≤ c + 1 by omega)
  refine ⟨⟨h.table, h.frameTable, fun p hp => h.frameInputs p (by omega), by omega, by omega, h.frameBound⟩,
    by simp only [Apart]; omega, by simp only [Apart]; omega, by omega, h.tableBound⟩

/-- A finished run of pairs: returned, every digest written, and memory off the digests and the scratch area kept. -/
def Done (ls rs : Nat) (s : State) (c : Nat) (f : State) : Prop :=
  f.status = .returned ∧
  (∀ p < 32 * c, ∀ k < 32, f.mem ((s.gpr out).toNat + 32 * p + k) =
    (Sha256.hash (pairMessage s.mem ((s.gpr left).toNat + ls * p) ((s.gpr right).toNat + rs * p))).get! k) ∧
  (∀ a, ¬ ((s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 32 * (32 * c)) →
    a < (s.gpr sp).toNat ∨ (s.gpr sp).toNat + frame ≤ a → f.mem a = s.mem a) ∧
  (∀ r ∈ calleeSaved, r ≠ sp → f.gpr r = s.gpr r) ∧ f.gpr sp = s.gpr sp + frame.toUInt64 ∧ f.gpr .rax = 0

/-- The saved registers are none of the ones a pair or the updates write. -/
theorem saved_ne {r : Gpr} (hr : r ∈ calleeSaved) (hsp : r ≠ sp) :
    r ≠ left ∧ r ≠ right ∧ r ≠ out ∧ r ≠ words ∧ r ≠ consts ∧ r ≠ blocks ∧ r ≠ count ∧ r ≠ .rax := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [left, right, out, words, consts, blocks, count]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The loop from its head with c + 1 pairs left. -/
theorem loop (ls rs : Nat) (c : Nat) : ∀ s : State, s.pc = loopHead → s.status = .running →
    (s.gpr count).toNat = c + 1 → Layout ls rs s (c + 1) →
    ∃ steps, Done ls rs s (c + 1) (run (program ls rs) steps s) := by
  induction c with
  | zero =>
    intro s hpc running counted layout
    have fr : frame = 10240 := rfl
    have ts : tableSize = 9584 := rfl
    obtain ⟨n, y, done, hrun⟩ := iteration ls rs s hpc running layout.pre
    obtain ⟨st, -, outs, kept, l1, r1, o1, others⟩ := done
    -- The count was one, so the countdown sets the zero flag and the loop exits.
    have one : s.gpr count = 1 := UInt64.toNat_inj.mp (by simpa using counted)
    have ycount : y.gpr count = s.gpr count :=
      others _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have zf : (exec [.addImm left (16 * ls), .addImm right (16 * rs), .addImm out 512, .subImm count 1] y).zf = true := by
      rw [tail_exec, ycount, one]; rfl
    rw [zf, if_pos rfl] at hrun
    obtain ⟨cst, cmem, cgpr⟩ := closing ls rs { exec [.addImm left (16 * ls), .addImm right (16 * rs),
      .addImm out 512, .subImm count 1] y with pc := finishAt ls rs } rfl (by simp only [exec_status]; exact st)
    refine ⟨n + 4, ?_⟩
    rw [run_add, hrun]
    refine ⟨cst, fun p hp k hk => ?_, fun a ha hf => ?_, fun r hr hsp => ?_, ?_, ?_⟩
    · rw [cmem, tail_exec]; exact outs p (by omega) k hk
    · rw [cmem, tail_exec]; exact kept a (by omega) hf
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := saved_ne hr hsp
      rw [cgpr, tail_exec]
      simp only [assign, if_neg h8, if_neg hsp, if_neg h7, if_neg h3, if_neg h2, if_neg h1]
      exact others r h1 h2 h3 h4 h5 h6
    · rw [cgpr, tail_exec]
      simp only [assign]
      simp [sp, count, out, left, right]
      exact others _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    · rw [cgpr]; simp [assign]
  | succ c ih =>
    intro s hpc running counted layout
    have fr : frame = 10240 := rfl
    have ts : tableSize = 9584 := rfl
    obtain ⟨n, y, done, hrun⟩ := iteration ls rs s hpc running layout.pre
    obtain ⟨st, -, outs, kept, l1, r1, o1, others⟩ := done
    have ycount : y.gpr count = s.gpr count :=
      others _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    -- The count was more than one, so the loop goes back.
    have zf : (exec [.addImm left (16 * ls), .addImm right (16 * rs), .addImm out 512, .subImm count 1] y).zf =
        false := by
      have ne : s.gpr count - (1 : Nat).toUInt64 ≠ 0 := fun h => by
        have := congrArg UInt64.toNat h
        rw [sub_toNat _ (by omega)] at this
        simp at this
        omega
      rw [tail_exec, ycount]
      simpa using ne
    rw [zf] at hrun
    simp only [Bool.false_eq_true, ↓reduceIte] at hrun
    -- The state at the loop head again, one pair further on.
    let z := { exec [.addImm left (16 * ls), .addImm right (16 * rs), .addImm out 512, .subImm count 1] y with
      pc := loopHead }
    have O := layout.outBound
    have Lb := layout.leftBound
    have Rb := layout.rightBound
    have zgpr : z.gpr = assign (assign (assign (assign y.gpr left (y.gpr left + (16 * ls).toUInt64)) right
        (y.gpr right + (16 * rs).toUInt64)) out (y.gpr out + (512 : Nat).toUInt64)) count
        (y.gpr count - (1 : Nat).toUInt64) := by simp only [z]; rw [tail_exec]
    have zmem : z.mem = y.mem := by simp only [z]; rw [tail_exec]
    have zst : z.status = .running := by simp only [z]; rw [tail_exec]; exact st
    have zout' : z.gpr out = y.gpr out + (512 : Nat).toUInt64 := by
      rw [zgpr]; rfl
    have zleft' : z.gpr left = y.gpr left + (16 * ls).toUInt64 := by
      rw [zgpr]; rfl
    have zright' : z.gpr right = y.gpr right + (16 * rs).toUInt64 := by
      rw [zgpr]; rfl
    have zcount' : z.gpr count = y.gpr count - (1 : Nat).toUInt64 := by
      rw [zgpr]; rfl
    have zout : (z.gpr out).toNat = (s.gpr out).toNat + 1024 := by
      rw [zout', o1, add_toNat _ _ (by rw [add_toNat _ _ (by omega)]; omega), add_toNat _ _ (by omega)]
    have lsplit : 16 * ls + 16 * ls = 32 * ls := by omega
    have rsplit : 16 * rs + 16 * rs = 32 * rs := by omega
    have bigL := Nat.mul_le_mul_left (32 * ls) (show 1 ≤ c + 1 + 1 by omega)
    have bigR := Nat.mul_le_mul_left (32 * rs) (show 1 ≤ c + 1 + 1 by omega)
    have zleft : (z.gpr left).toNat = (s.gpr left).toNat + 32 * ls := by
      rw [zleft', l1, add_toNat _ _ (by rw [add_toNat _ _ (by omega)]; omega), add_toNat _ _ (by omega)]
      omega
    have zright : (z.gpr right).toNat = (s.gpr right).toNat + 32 * rs := by
      rw [zright', r1, add_toNat _ _ (by rw [add_toNat _ _ (by omega)]; omega), add_toNat _ _ (by omega)]
      omega
    have zcount : (z.gpr count).toNat = c + 1 := by
      rw [zcount', ycount, sub_toNat _ (by omega), counted]; rfl
    have zkeep : ∀ r, r ≠ left → r ≠ right → r ≠ out → r ≠ words → r ≠ consts → r ≠ blocks → r ≠ count →
        z.gpr r = s.gpr r := fun r h1 h2 h3 h4 h5 h6 h7 => by
      rw [zgpr]; simp only [assign, if_neg h7, if_neg h3, if_neg h2, if_neg h1]; exact others r h1 h2 h3 h4 h5 h6
    have zsp : z.gpr sp = s.gpr sp := zkeep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
    have ztbl : z.gpr tbl = s.gpr tbl := zkeep _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    -- Memory the pair did not write still holds what it held.
    have zkept : ∀ a, ¬ ((s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 1024) →
        a < (s.gpr sp).toNat ∨ (s.gpr sp).toNat + frame ≤ a → z.mem a = s.mem a := fun a h1 h2 => by
      rw [zmem]; exact kept a h1 h2
    have apart := layout.inputsApart
    have tapart := layout.tableApart
    have fout := layout.frameOut
    have finp := layout.frameInputs
    have ftab := layout.frameTable
    simp only [Apart] at apart tapart fout finp
    simp only [FrameApart] at ftab
    have lnext : 32 * ls * (c + 1 + 1) = 32 * ls * (c + 1) + 32 * ls := Nat.mul_succ _ _
    have rnext : 32 * rs * (c + 1 + 1) = 32 * rs * (c + 1) + 32 * rs := Nat.mul_succ _ _
    have next : Layout ls rs z (c + 1) := by
      refine ⟨fun i hi => ?_, by omega, by rw [zleft]; omega, by rw [zright]; omega, by rw [ztbl]; exact
        layout.tableBound, by rw [zsp]; exact layout.frameBound, ?_, fun p hp => ?_, ?_, ?_, fun p hp => ?_⟩
      · rw [ztbl]
        simp only [tableSize] at hi
        rw [zkept _ (by simp only [tableSize] at tapart; omega) (by simp only [frame, tableSize] at ftab ⊢; omega)]
        exact layout.table i (by simp only [tableSize]; omega)
      · simp only [Apart, zout, ztbl]; omega
      · have := apart (32 + p) (by omega)
        simp only [Apart, zout, zleft, zright]
        simp only [Nat.mul_add] at this
        omega
      · simp only [FrameApart, zsp, ztbl]; omega
      · simp only [Apart, zout, zsp]; omega
      · have := finp (32 + p) (by omega)
        simp only [Apart, zsp, zleft, zright]
        simp only [Nat.mul_add] at this
        omega
    obtain ⟨steps, fst, fouts, fkept, fsaved, fsp, frax⟩ := ih z rfl zst zcount next
    refine ⟨n + steps, ?_⟩
    rw [run_add, hrun]
    refine ⟨fst, fun p hp k hk => ?_, fun a ha hf => ?_, fun r hr hsp => ?_, ?_, frax⟩
    · by_cases first : p < 32
      · -- This pair's digests: the later pairs write past them, and the scratch area misses them.
        refine (fkept _ (by rw [zout]; omega) (by rw [zsp]; omega)).trans ?_
        rw [zmem]
        exact outs p first k hk
      · -- A later pair's digests, from inputs this pair left alone.
        have := fouts (p - 32) (by omega) k hk
        rw [zout, zleft, zright, show (s.gpr out).toNat + 1024 + 32 * (p - 32) + k = (s.gpr out).toNat + 32 * p + k by
          omega] at this
        refine this.trans ?_
        have hp' : ls * p = 32 * ls + ls * (p - 32) := by
          have := Nat.mul_add ls 32 (p - 32); rw [show 32 + (p - 32) = p by omega] at this; omega
        have hr' : rs * p = 32 * rs + rs * (p - 32) := by
          have := Nat.mul_add rs 32 (p - 32); rw [show 32 + (p - 32) = p by omega] at this; omega
        rw [show (s.gpr left).toNat + 32 * ls + ls * (p - 32) = (s.gpr left).toNat + ls * p by omega,
          show (s.gpr right).toNat + 32 * rs + rs * (p - 32) = (s.gpr right).toNat + rs * p by omega]
        have a1 := apart p hp
        have a2 := finp p hp
        rw [pairMessage_congr z.mem s.mem _ _ (fun i hi => zkept _ (by omega) (by omega))
          (fun i hi => zkept _ (by omega) (by omega))]
    · rw [zsp] at fkept
      exact (fkept _ (by rw [zout]; omega) hf).trans (zkept _ (by omega) hf)
    · obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := saved_ne hr hsp
      exact (fsaved r hr hsp).trans (zkeep r h1 h2 h3 h4 h5 h6 h7)
    · rw [fsp, zsp]

/-- Reserving and releasing the scratch area gives the stack pointer back. -/
theorem sub_add_frame (x : UInt64) (room : frame ≤ x.toNat) : x - frame.toUInt64 + frame.toUInt64 = x := by
  apply UInt64.toNat_inj.mp
  have f : frame.toUInt64.toNat = frame := by simp [frame]
  rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, f]; exact room), f]
  have := x.toNat_lt
  omega

set_option maxRecDepth 100000 in
/--
The thirty-two-lane kernel hashes every pair it is given.

Started at its first instruction, with a count of batch pairs, it returns having written each pair's digest.
Pair p is the 32 bytes at the left address plus p times the left stride, then the 32 bytes at the right address plus p times the right stride.
Its digest lands 32 p bytes past the output address.
It uses a scratch area of 10240 bytes just below the stack pointer.
No other memory changes, the registers the calling convention saves keep their values, and the result register holds zero.

The output must sit clear of the table and of every input node, the scratch area clear of all of them, and every
region must lie within reach.
-/
theorem program_correct (ls rs : Nat) (s : State) (start : s.pc = 0) (running : s.status = .running)
    (table : TableAt s.mem (s.gpr tbl).toNat) (n : Nat) (pairs : n = 32 * (s.gpr count).toNat)
    (room : frame ≤ (s.gpr sp).toNat) (spBound : (s.gpr sp).toNat ≤ addressBound)
    (outBound : (s.gpr out).toNat + 32 * n ≤ addressBound)
    (leftBound : (s.gpr left).toNat + ls * n ≤ addressBound)
    (rightBound : (s.gpr right).toNat + rs * n ≤ addressBound)
    (tableBound : (s.gpr tbl).toNat + tableSize ≤ addressBound)
    (tableApart : Apart ((s.gpr out).toNat, 32 * n) ((s.gpr tbl).toNat, tableSize))
    (inputsApart : ∀ p < n, Apart ((s.gpr out).toNat, 32 * n) ((s.gpr left).toNat + ls * p, 32) ∧
      Apart ((s.gpr out).toNat, 32 * n) ((s.gpr right).toNat + rs * p, 32))
    (scratchTable : Apart ((s.gpr sp).toNat - frame, frame) ((s.gpr tbl).toNat, tableSize))
    (scratchOut : Apart ((s.gpr out).toNat, 32 * n) ((s.gpr sp).toNat - frame, frame))
    (scratchInputs : ∀ p < n, Apart ((s.gpr left).toNat + ls * p, 32) ((s.gpr sp).toNat - frame, frame) ∧
      Apart ((s.gpr right).toNat + rs * p, 32) ((s.gpr sp).toNat - frame, frame)) :
    ∃ steps,
      (run (program ls rs) steps s).status = .returned ∧
      (∀ p < n, ∀ k < 32, (run (program ls rs) steps s).mem ((s.gpr out).toNat + 32 * p + k) =
        (Sha256.hash (pairMessage s.mem ((s.gpr left).toNat + ls * p) ((s.gpr right).toNat + rs * p))).get! k) ∧
      (∀ a, ¬ ((s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 32 * n) →
        a < (s.gpr sp).toNat - frame ∨ (s.gpr sp).toNat ≤ a → (run (program ls rs) steps s).mem a = s.mem a) ∧
      (∀ r ∈ calleeSaved, (run (program ls rs) steps s).gpr r = s.gpr r) ∧
      (run (program ls rs) steps s).gpr .rax = 0 := by
  subst pairs
  have fr : frame = 10240 := rfl
  obtain ⟨og, ov, om, -, ost, opc⟩ := opening_run ls rs s start running
  generalize hx : run (program ls rs) 3 s = x at og ov om ost opc
  have xsp : (x.gpr sp).toNat = (s.gpr sp).toNat - frame := by
    rw [og]; simp only [assign, ↓reduceIte]
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp [frame]; omega)]
    simp [frame]
  have xkeep : ∀ r, r ≠ sp → x.gpr r = s.gpr r := fun r h => by rw [og]; simp only [assign, if_neg h]
  have xsaved : ∀ r ∈ calleeSaved, r ≠ sp → x.gpr r = s.gpr r := fun r _ h => xkeep r h
  have rspBack : x.gpr sp + frame.toUInt64 = s.gpr sp := by
    rw [og]; simp only [assign, ↓reduceIte]; exact sub_add_frame _ room
  cases h : (s.gpr count).toNat with
  | zero =>
    -- No pair: straight to the closing instructions.
    have zero : s.gpr count = 0 := UInt64.toNat_inj.mp (by simpa using h)
    rw [zero] at opc
    simp only [beq_self_eq_true, ↓reduceIte] at opc
    obtain ⟨st, mem, gpr⟩ := closing ls rs x opc (by rw [ost, running])
    refine ⟨3 + 4, ?_⟩
    rw [run_add, hx]
    refine ⟨st, fun p hp => absurd hp (by omega), fun a _ _ => by rw [mem, om], fun r hr => ?_, ?_⟩
    · rw [gpr]
      by_cases hsp : r = sp
      · subst hsp; simp only [assign]; rw [if_neg (by decide)]; simp only [↓reduceIte]; exact rspBack
      · obtain ⟨-, -, -, -, -, -, -, h8⟩ := saved_ne hr hsp
        simp only [assign, if_neg h8, if_neg hsp]; exact xkeep r hsp
    · rw [gpr]; simp [assign]
  | succ c =>
    -- At least one pair: the loop, from its head.
    have nonzero : (s.gpr count == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro zero
      rw [zero] at h
      simp at h
    rw [nonzero] at opc
    simp only [Bool.false_eq_true, ↓reduceIte] at opc
    have xcount : (x.gpr count).toNat = c + 1 := by rw [xkeep _ (by decide), h]
    have xout : x.gpr out = s.gpr out := xkeep _ (by decide)
    have xleft : x.gpr left = s.gpr left := xkeep _ (by decide)
    have xright : x.gpr right = s.gpr right := xkeep _ (by decide)
    have xtbl : x.gpr tbl = s.gpr tbl := xkeep _ (by decide)
    rw [h] at outBound leftBound rightBound tableApart inputsApart scratchOut scratchInputs
    simp only [Apart] at tableApart inputsApart scratchTable scratchOut scratchInputs
    have layout : Layout ls rs x (c + 1) := by
      refine ⟨by rw [xtbl, om]; exact table, by rw [xout]; omega, ?_, ?_, by rw [xtbl]; exact tableBound,
        by rw [xsp]; omega, by simp only [Apart, xout, xtbl]; omega, fun p hp => ?_,
        by simp only [FrameApart, xsp, xtbl]; omega, by simp only [Apart, xout, xsp]; omega, fun p hp => ?_⟩
      · rw [xleft, show 32 * ls * (c + 1) = ls * (32 * (c + 1)) by rw [Nat.mul_comm 32 ls, Nat.mul_assoc]]
        exact leftBound
      · rw [xright, show 32 * rs * (c + 1) = rs * (32 * (c + 1)) by rw [Nat.mul_comm 32 rs, Nat.mul_assoc]]
        exact rightBound
      · have := inputsApart p hp
        simp only [Apart, xout, xleft, xright]
        omega
      · have := scratchInputs p hp
        simp only [Apart, xsp, xleft, xright]
        omega
    obtain ⟨steps, fst, fouts, fkept, fsaved, fsp, frax⟩ := loop ls rs c x opc (by rw [ost, running]) xcount layout
    refine ⟨3 + steps, ?_⟩
    rw [run_add, hx]
    rw [xout, xleft, xright, om] at fouts
    rw [xout, om, xsp] at fkept
    refine ⟨fst, fouts, fun a ha hf => fkept a (by omega) (by omega), fun r hr => ?_, frax⟩
    by_cases hsp : r = sp
    · subst hsp; rw [fsp, rspBack]
    · rw [fsaved r hr hsp, xkeep r hsp]


/-- The thirty-two-lane kernel calls nothing. -/
theorem leaf (ls rs : Nat) : Leaf (program ls rs) := by
  intro i hi name
  rintro rfl
  rw [program_toList, body_eq] at hi
  -- Only the straight-line pieces could hold a call, and a call is not straight-line.
  simp only [opening, tailCode, closingCode, List.mem_append, List.mem_cons, reduceCtorEq, List.not_mem_nil,
    or_false, false_or] at hi
  obtain ⟨b1, b2, b3, b4, b5⟩ := blocks_straight
  have notStraight : (Instr.call name).straight = false := rfl
  rcases hi with ((((h | h) | h) | h) | h) | h <;>
    first
    | simpa [notStraight] using setup_straight ls rs _ h
    | simpa [notStraight] using List.all_eq_true.mp b1 _ h
    | simpa [notStraight] using List.all_eq_true.mp b2 _ h
    | simpa [notStraight] using List.all_eq_true.mp b3 _ h
    | simpa [notStraight] using List.all_eq_true.mp b4 _ h
    | simpa [notStraight] using List.all_eq_true.mp b5 _ h

end Ssz.Native.Kernel.Avx512x2
