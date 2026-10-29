import SszNative.Proofs.Kernel.Baseline.Batch
import SszNative.Proofs.Kernel.Avx512.Main
import SszNative.Proofs.Asm.Machine

/-!
The four-lane kernel, start to return.

The routine makes its scratch frame, tests the batch count, and skips to the end when it is zero.
Each batch runs straight-line pieces and three loops of eight-round blocks.
After a batch, the pointers advance, the count goes down, and the loop branches back while batches remain.
At the end, the routine drops its frame, zeroes its result, and returns.
-/

namespace Ssz.Native.Kernel.Baseline

open Ssz.Sha256 Ssz.Native.Asm
open Ssz.Native.Kernel.Avx512 (fetch step_jz step_jnz step_ret run_one add_toNat sub_toNat)

/-- A loop's body ending in a branch back to its first instruction, run once from that instruction. -/
theorem loop_once (p : Array Instr) (pre B post : List Instr) (layout : p.toList = pre ++ B ++ .jnz pre.length :: post)
    (straight : ∀ i ∈ B, i.straight) (x : State) (hpc : x.pc = pre.length) (running : x.status = .running) :
    run p (B.length + 1) x =
      { exec B x with pc := if (exec B x).zf then pre.length + B.length + 1 else pre.length } := by
  -- The body runs as a block, then the branch reads the zero flag.
  have f := fetch p (pre ++ B) post (.jnz pre.length) layout
  rw [List.length_append] at f
  rw [run_add, run_block p pre B _ layout straight x hpc running, run_one,
    step_jnz p _ pre.length f (by simpa using running), exec_with_pc]

/--
A loop run n times, from its head, with an invariant over its passes.

Each pass keeps the invariant one pass on, and sets the zero flag exactly on the last.
-/
theorem loop_run (p : Array Instr) (pre B post : List Instr) (layout : p.toList = pre ++ B ++ .jnz pre.length :: post)
    (straight : ∀ i ∈ B, i.straight) (n : Nat) (Inv : Nat → State → Prop)
    (step : ∀ i x, i < n → Inv i x → Inv (i + 1) (exec B x) ∧ ((exec B x).zf = true ↔ i + 1 = n))
    (pcFree : ∀ i x q, Inv i x → Inv i { x with pc := q }) (x : State) (hpc : x.pc = pre.length)
    (running : x.status = .running) (start : Inv 0 x) (hn : 0 < n) :
    ∃ steps, (run p steps x).pc = pre.length + B.length + 1 ∧ (run p steps x).status = .running ∧
      Inv n (run p steps x) := by
  -- Induction on the passes left, from any pass.
  suffices key : ∀ j i x, i + j + 1 = n → x.pc = pre.length → x.status = .running → Inv i x →
      ∃ steps, (run p steps x).pc = pre.length + B.length + 1 ∧ (run p steps x).status = .running ∧
        Inv n (run p steps x) from key (n - 1) 0 x (by omega) hpc running start
  intro j
  induction j with
  | zero =>
    intro i x hi hpc running inv
    obtain ⟨next, zf⟩ := step i x (by omega) inv
    refine ⟨B.length + 1, ?_⟩
    rw [loop_once p pre B post layout straight x hpc running, if_pos (zf.mpr (by omega))]
    exact ⟨rfl, by simpa using running, by rw [show n = i + 1 by omega]; exact pcFree _ _ _ next⟩
  | succ j ih =>
    intro i x hi hpc running inv
    obtain ⟨next, zf⟩ := step i x (by omega) inv
    have back : (exec B x).zf = false := by
      cases h : (exec B x).zf
      · rfl
      · exact absurd (zf.mp h) (by omega)
    obtain ⟨steps, pc', st', inv'⟩ := ih (i + 1) { exec B x with pc := pre.length } (by omega) rfl
      (by simpa using running) (pcFree _ _ _ next)
    refine ⟨B.length + 1 + steps, ?_⟩
    rw [run_add, loop_once p pre B post layout straight x hpc running, back]
    exact ⟨pc', st', inv'⟩

/-- The pointer and counter updates at the end of each batch. -/
def tailCode (ls rs : Nat) : List Instr :=
  [.addImm left (4 * ls), .addImm right (4 * rs), .addImm out 128, .subImm count 1]

/-- The index of the closing instructions. -/
def finishAt (ls rs : Nat) : Nat := loopHead + (body ls rs).length + 5

/-- The routine's instructions, piece by piece. -/
theorem program_toList (ls rs : Nat) :
    (program ls rs).toList =
      [.subImm sp frame, .test count, .jz (finishAt ls rs)] ++ setupCode ls rs ++ firstBlock true ++
        .jnz (firstHead ls rs) :: [.movImm blocks 2] ++ firstBlock false ++ .jnz (secondHead ls rs) :: [] ++
        middleCode ++ paddingBlock ++ .jnz (thirdHead ls rs) :: [] ++ outputCode ++ tailCode ls rs ++
        [.jnz loopHead, .addImm sp frame, .zeroReg .rax, .ret] := by
  -- The routine was built as these pieces, in this order.
  simp only [program, body, batchCode, finishAt, tailCode, List.toList_toArray, List.length_cons, List.length_nil,
    List.append_assoc, List.cons_append, List.nil_append]

/-- A machine subtraction that does not go below zero is the plain one. -/
theorem subN_toNat (x : UInt64) (n : Nat) (h : n ≤ x.toNat) : (x - n.toUInt64).toNat = x.toNat - n := by
  have lt := x.toNat_lt
  have hn : n.toUInt64.toNat = n := by simp; omega
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hn]; exact h), hn]

/-- A small count, less one, as a machine word. -/
theorem count_sub (c i : Nat) (h : i < c) (small : c < 2 ^ 63) :
    (c - i : Nat).toUInt64 - (1 : Nat).toUInt64 = (c - (i + 1) : Nat).toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [subN_toNat _ _ (by simp; omega)]
  simp; omega

/-- A small count, less one, is zero exactly when it was one. -/
theorem count_zero (c i : Nat) (h : i < c) (small : c < 2 ^ 63) :
    ((c - i : Nat).toUInt64 - (1 : Nat).toUInt64 == 0) = true ↔ i + 1 = c := by
  rw [count_sub c i h small]
  simp only [beq_iff_eq]
  constructor
  · intro e; have := congrArg UInt64.toNat e; simp at this; omega
  · intro e; apply UInt64.toNat_inj.mp; simp; omega

/-- A first-block loop's state before pass i: pointers, count, every lane's invariant, and memory outside kept. -/
def FirstLoop (ls rs : Nat) (s : State) (base n i : Nat) (x : State) : Prop :=
  (base + i < 8 → (x.gpr words).toNat = scratch s + wordsBase (base + i)) ∧
  (x.gpr consts).toNat = tableAt s + 512 * (base + i) ∧ x.gpr blocks = (n - i : Nat).toUInt64 ∧
  (∀ r, Kept r → x.gpr r = s.gpr r) ∧
  (∀ l : Fin 4, FirstInv (scratch s) (msg s ls rs l.val) (8 * (base + i)) (view x l)) ∧
  (∀ a, Outside (scratch s) a → x.mem a = s.mem a)

/-- A pass of a first-block loop keeps its state one pass on, and sets the zero flag on the last pass. -/
theorem firstLoop_step (ls rs : Nat) (s : State) (ctx : Ctx ls rs s) (base n : Nat) (hbn : base + n ≤ 8)
    (sched : Bool) (hs : ∀ i < n, sched = decide (base + i < 6)) :
    ∀ i x, i < n → FirstLoop ls rs s base n i x →
      FirstLoop ls rs s base n (i + 1) (exec (firstBlock sched) x) ∧
        ((exec (firstBlock sched) x).zf = true ↔ i + 1 = n) := by
  intro i x hi inv
  obtain ⟨wordsAt, constsAt, blocksAt, kept, lanes, outside⟩ := inv
  obtain ⟨lanes', outside', gpr', zf'⟩ := firstBlock_spec ls rs s ctx (base + i) (by omega) sched (hs i hi) x
    (wordsAt (by omega)) constsAt lanes outside
  have fb := ctx.frameBound
  have tb := ctx.tableBound
  simp only [tableSize, frame] at fb tb
  refine ⟨⟨fun h => ?_, ?_, ?_, fun r hr => ?_, fun l => ?_, outside'⟩, ?_⟩
  · -- The schedule pointer moves down one block.
    rw [gpr']; simp only [assign, if_neg (show words ≠ blocks by decide), if_neg (show words ≠ consts by decide), if_true]
    rw [subN_toNat _ _ (by rw [wordsAt (by omega)]; simp only [wordsBase]; omega), wordsAt (by omega)]
    simp only [wordsBase]; omega
  · -- The constants pointer moves up one block.
    rw [gpr']; simp only [assign, if_neg (show consts ≠ blocks by decide), if_true]
    rw [add_toNat _ _ (by rw [constsAt]; simp only [addressBound] at tb ⊢; omega), constsAt]; omega
  · rw [gpr']; simp only [assign, if_true, blocksAt]; exact count_sub n i hi (by omega)
  · obtain ⟨a, b, c⟩ := hr
    rw [gpr']; simp only [assign, if_neg c, if_neg b, if_neg a]; exact kept r ⟨a, b, c⟩
  · rw [show 8 * (base + (i + 1)) = 8 * (base + i) + 8 by omega]; exact lanes' l
  · rw [zf', blocksAt]; exact count_zero n i hi (by omega)

/-- The padding loop's state before pass i: pointer, count, every lane's invariant, and memory outside kept. -/
def PadLoop (ls rs : Nat) (s : State) (i : Nat) (x : State) : Prop :=
  (x.gpr consts).toNat = tableAt s + 4096 + 512 * i ∧ x.gpr blocks = (8 - i : Nat).toUInt64 ∧
  (∀ r, Kept r → x.gpr r = s.gpr r) ∧
  (∀ l : Fin 4, PadInv (scratch s) (middle s ls rs l.val) (8 * i) (view x l)) ∧
  (∀ a, Outside (scratch s) a → x.mem a = s.mem a)

/-- A pass of the padding loop keeps its state one pass on, and sets the zero flag on the last pass. -/
theorem padLoop_step (ls rs : Nat) (s : State) (ctx : Ctx ls rs s) :
    ∀ i x, i < 8 → PadLoop ls rs s i x →
      PadLoop ls rs s (i + 1) (exec paddingBlock x) ∧ ((exec paddingBlock x).zf = true ↔ i + 1 = 8) := by
  intro i x hi inv
  obtain ⟨constsAt, blocksAt, kept, lanes, outside⟩ := inv
  obtain ⟨lanes', mem', gpr', zf'⟩ := padBlock_spec ls rs s ctx i hi x constsAt lanes outside
  have tb := ctx.tableBound
  simp only [tableSize] at tb
  refine ⟨⟨?_, ?_, fun r hr => ?_, fun l => ?_, fun a ha => by rw [mem']; exact outside a ha⟩, ?_⟩
  · -- The constants pointer moves up one block.
    rw [gpr']; simp only [assign, if_neg (show consts ≠ blocks by decide), if_true]
    rw [add_toNat _ _ (by rw [constsAt]; simp only [addressBound] at tb ⊢; omega), constsAt]; omega
  · rw [gpr']; simp only [assign, if_true, blocksAt]; exact count_sub 8 i hi (by omega)
  · obtain ⟨a, b, c⟩ := hr
    rw [gpr']; simp only [assign, if_neg c, if_neg b]; exact kept r ⟨a, b, c⟩
  · rw [show 8 * (i + 1) = 8 * i + 8 by omega]; exact lanes' l
  · rw [zf', blocksAt]; exact count_zero 8 i hi (by omega)

/-- What one batch leaves: its digests written, memory outside the output and the scratch kept, and the registers. -/
def BatchDone (ls rs : Nat) (s y : State) : Prop :=
  y.status = .running ∧ y.pc = loopHead + (body ls rs).length ∧
  (∀ p < 4, ∀ k < 32, y.mem ((s.gpr out).toNat + 32 * p + k) = (Sha256.hash (msg s ls rs p)).get! k) ∧
  (∀ a, Outside (scratch s) a → ¬ ((s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 128) → y.mem a = s.mem a) ∧
  (∀ r, Kept r → y.gpr r = s.gpr r)


/-- The instructions before the setup: the frame, the count check, and its branch. -/
def pre0 (ls rs : Nat) : List Instr := [.subImm sp frame, .test count, .jz (finishAt ls rs)]

/-- The instructions before the first loop. -/
def pre1 (ls rs : Nat) : List Instr := pre0 ls rs ++ setupCode ls rs

/-- The instructions before the second loop's count. -/
def preM (ls rs : Nat) : List Instr := pre1 ls rs ++ firstBlock true ++ [.jnz (pre1 ls rs).length]

/-- The instructions before the second loop. -/
def pre2 (ls rs : Nat) : List Instr := preM ls rs ++ [.movImm blocks 2]

/-- The instructions before the first feed-forward. -/
def preD (ls rs : Nat) : List Instr := pre2 ls rs ++ firstBlock false ++ [.jnz (pre2 ls rs).length]

/-- The instructions before the third loop. -/
def pre3 (ls rs : Nat) : List Instr := preD ls rs ++ middleCode

/-- The instructions before the output. -/
def preO (ls rs : Nat) : List Instr := pre3 ls rs ++ paddingBlock ++ [.jnz (pre3 ls rs).length]

/-- The first loop's head is where its body starts. -/
theorem firstHead_eq (ls rs : Nat) : firstHead ls rs = (pre1 ls rs).length := by
  simp [firstHead, pre1, pre0, loopHead]; omega

/-- The second loop's head is where its body starts. -/
theorem secondHead_eq (ls rs : Nat) : secondHead ls rs = (pre2 ls rs).length := by
  simp [secondHead, pre2, preM, firstHead_eq]; omega

/-- The third loop's head is where its body starts. -/
theorem thirdHead_eq (ls rs : Nat) : thirdHead ls rs = (pre3 ls rs).length := by
  simp [thirdHead, pre3, preD, secondHead_eq]; omega

/-- The output ends where the batch body ends. -/
theorem output_end (ls rs : Nat) : (preO ls rs).length + outputCode.length = loopHead + (body ls rs).length := by
  simp [preO, pre3, preD, pre2, preM, pre1, pre0, body, batchCode, loopHead]; omega

/-- The instructions after the batch body. -/
def closing (ls rs : Nat) : List Instr :=
  tailCode ls rs ++ [.jnz loopHead, .addImm sp frame, .zeroReg .rax, .ret]

/-- The routine, cut before and after the setup. -/
theorem layout0 (ls rs : Nat) : (program ls rs).toList = pre0 ls rs ++ setupCode ls rs ++
    (firstBlock true ++ .jnz (pre1 ls rs).length :: [.movImm blocks 2] ++ firstBlock false ++
      .jnz (pre2 ls rs).length :: middleCode ++ paddingBlock ++ .jnz (pre3 ls rs).length :: outputCode ++
      closing ls rs) := by
  rw [program_toList, ← firstHead_eq, ← secondHead_eq, ← thirdHead_eq]
  simp only [pre0, closing, List.append_assoc, List.cons_append, List.nil_append]

/-- The routine, cut around the first loop's body. -/
theorem layout1 (ls rs : Nat) : (program ls rs).toList = pre1 ls rs ++ firstBlock true ++ .jnz (pre1 ls rs).length ::
    ([.movImm blocks 2] ++ firstBlock false ++ .jnz (pre2 ls rs).length :: middleCode ++ paddingBlock ++
      .jnz (pre3 ls rs).length :: outputCode ++ closing ls rs) := by
  rw [layout0]; simp only [pre1, List.append_assoc, List.cons_append, List.nil_append]

/-- The routine, cut around the second loop's count. -/
theorem layoutM (ls rs : Nat) : (program ls rs).toList = preM ls rs ++ [.movImm blocks 2] ++
    (firstBlock false ++ .jnz (pre2 ls rs).length :: middleCode ++ paddingBlock ++ .jnz (pre3 ls rs).length ::
      outputCode ++ closing ls rs) := by
  rw [layout1]; simp only [preM, List.append_assoc, List.cons_append, List.nil_append]

/-- The routine, cut around the second loop's body. -/
theorem layout2 (ls rs : Nat) : (program ls rs).toList = pre2 ls rs ++ firstBlock false ++ .jnz (pre2 ls rs).length ::
    (middleCode ++ paddingBlock ++ .jnz (pre3 ls rs).length :: outputCode ++ closing ls rs) := by
  rw [layoutM]; simp only [pre2, List.append_assoc, List.cons_append, List.nil_append]

/-- The routine, cut around the first feed-forward. -/
theorem layoutD (ls rs : Nat) : (program ls rs).toList = preD ls rs ++ middleCode ++
    (paddingBlock ++ .jnz (pre3 ls rs).length :: outputCode ++ closing ls rs) := by
  rw [layout2]; simp only [preD, List.append_assoc, List.cons_append, List.nil_append]

/-- The routine, cut around the third loop's body. -/
theorem layout3 (ls rs : Nat) : (program ls rs).toList = pre3 ls rs ++ paddingBlock ++ .jnz (pre3 ls rs).length ::
    (outputCode ++ closing ls rs) := by
  rw [layoutD]; simp only [pre3, List.append_assoc, List.cons_append]

/-- The routine, cut around the output. -/
theorem layoutO (ls rs : Nat) : (program ls rs).toList = preO ls rs ++ outputCode ++ closing ls rs := by
  rw [layout3]; simp only [preO, List.append_assoc, List.cons_append, List.nil_append]

/-- The setup never branches. -/
theorem setup_straight (ls rs : Nat) : ∀ i ∈ setupCode ls rs, i.straight := by
  -- No instruction of the copies, the loads, or the pointer updates is a branch.
  simp only [setupCode, loadWords, swapCopy, ivCode, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_cons,
    List.mem_range, List.not_mem_nil, or_false, or_imp, forall_and, forall_exists_index, and_imp]
  and_intros <;> intros <;> subst_vars <;> rfl

set_option maxRecDepth 100000 in
/-- The loop bodies, the feed-forward, and the output never branch. -/
theorem pieces_straight : (∀ b, (firstBlock b).all Instr.straight = true) ∧ middleCode.all Instr.straight = true ∧
    paddingBlock.all Instr.straight = true ∧ outputCode.all Instr.straight = true := by
  -- Checked by evaluation.
  decide +kernel

/-- Each register the loops do not use, by evaluation. -/
theorem kept_sp : Kept sp ∧ Kept tbl ∧ Kept out := ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩,
  ⟨by decide, by decide, by decide⟩⟩

/-- A first-block loop's state does not depend on the instruction index. -/
theorem FirstLoop.pc {ls rs : Nat} {s : State} {base n i : Nat} {x : State} (q : Nat) (h : FirstLoop ls rs s base n i x) :
    FirstLoop ls rs s base n i { x with pc := q } := h

/-- The padding loop's state does not depend on the instruction index. -/
theorem PadLoop.pc {ls rs : Nat} {s : State} {i : Nat} {x : State} (q : Nat) (h : PadLoop ls rs s i x) :
    PadLoop ls rs s i { x with pc := q } := h

/-- The setup and the first loop: six blocks with their schedule steps. -/
theorem batch_first (ls rs : Nat) (s : State) (ctx : Ctx ls rs s) (hpc : s.pc = loopHead)
    (running : s.status = .running) :
    ∃ steps, (run (program ls rs) steps s).pc = (preM ls rs).length ∧
      (run (program ls rs) steps s).status = .running ∧ FirstLoop ls rs s 0 6 6 (run (program ls rs) steps s) := by
  have r0 := run_block _ _ _ _ (layout0 ls rs) (setup_straight ls rs) s (by rw [hpc]; rfl) running
  obtain ⟨lanes0, out0, words0, consts0, blocks0, kept0⟩ := setup_spec ls rs s ctx
  generalize hx1 : run (program ls rs) (setupCode ls rs).length s = x1 at r0
  have pc1 : x1.pc = (pre1 ls rs).length := by rw [r0]; simp only [pre1, List.length_append]
  have st1 : x1.status = .running := by rw [r0]; simp [running]
  have start1 : FirstLoop ls rs s 0 6 0 x1 := by
    rw [r0]
    exact FirstLoop.pc _ ⟨fun _ => words0, by rw [consts0]; simp, by rw [blocks0]; simp, kept0, lanes0, out0⟩
  obtain ⟨n1, pc2, st2, inv2⟩ := loop_run _ (pre1 ls rs) (firstBlock true) _ (layout1 ls rs)
    (List.all_eq_true.mp (pieces_straight.1 true)) 6 (FirstLoop ls rs s 0 6)
    (firstLoop_step ls rs s ctx 0 6 (by omega) true (fun i hi => by simp <;> omega)) (fun _ _ _ h => h) x1 pc1 st1
    start1 (by omega)
  refine ⟨(setupCode ls rs).length + n1, ?_⟩
  rw [run_add, hx1]
  refine ⟨?_, st2, inv2⟩
  rw [pc2]; simp only [preM, List.length_append, List.length_cons, List.length_nil]

/-- The second loop's count and the second loop: two blocks without schedule steps. -/
theorem batch_second (ls rs : Nat) (s : State) (ctx : Ctx ls rs s) (x : State) (hpc : x.pc = (preM ls rs).length)
    (running : x.status = .running) (inv : FirstLoop ls rs s 0 6 6 x) :
    ∃ steps, (run (program ls rs) steps x).pc = (preD ls rs).length ∧
      (run (program ls rs) steps x).status = .running ∧ FirstLoop ls rs s 6 2 2 (run (program ls rs) steps x) := by
  have rM := run_block _ _ _ _ (layoutM ls rs) (by decide) x hpc running
  generalize hx3 : run (program ls rs) [Instr.movImm blocks 2].length x = x3 at rM
  have start3 : FirstLoop ls rs s 6 2 0 x3 := by
    obtain ⟨w, c, -, k, l, o⟩ := inv
    rw [rM]
    refine FirstLoop.pc _ ⟨fun h => w h, c, by simp [exec, exec1, assign], fun r hr => ?_, fun l' => l l', fun a ha => o a ha⟩
    simp only [exec, exec1, assign, if_neg hr.2.2]; exact k r hr
  obtain ⟨n2, pc4, st4, inv4⟩ := loop_run _ (pre2 ls rs) (firstBlock false) _ (layout2 ls rs)
    (List.all_eq_true.mp (pieces_straight.1 false)) 2 (FirstLoop ls rs s 6 2)
    (firstLoop_step ls rs s ctx 6 2 (by omega) false (fun i hi => by simp <;> omega)) (fun _ _ _ h => h) x3
    (by rw [rM]; simp only [pre2, List.length_append, List.length_cons, List.length_nil])
    (by rw [rM]; simp [running]) start3 (by omega)
  refine ⟨[Instr.movImm blocks 2].length + n2, ?_⟩
  rw [run_add, hx3]
  refine ⟨?_, st4, inv4⟩
  rw [pc4]; simp only [preD, List.length_append, List.length_cons, List.length_nil]

/-- The first feed-forward, the third loop's count, and the third loop: eight padding blocks. -/
theorem batch_third (ls rs : Nat) (s : State) (ctx : Ctx ls rs s) (x : State) (hpc : x.pc = (preD ls rs).length)
    (running : x.status = .running) (inv : FirstLoop ls rs s 6 2 2 x) :
    ∃ steps, (run (program ls rs) steps x).pc = (preO ls rs).length ∧
      (run (program ls rs) steps x).status = .running ∧ PadLoop ls rs s 8 (run (program ls rs) steps x) := by
  have rD := run_block _ _ _ _ (layoutD ls rs) (List.all_eq_true.mp pieces_straight.2.1) x hpc running
  obtain ⟨-, c4, -, k4, l4, o4⟩ := inv
  obtain ⟨lanes5, out5, gpr5⟩ := middle_spec ls rs s ctx x (k4 sp kept_sp.1) (k4 tbl kept_sp.2.1) l4 o4
  generalize hx5 : run (program ls rs) middleCode.length x = x5 at rD
  have start5 : PadLoop ls rs s 0 x5 := by
    rw [rD]
    refine PadLoop.pc _ ⟨?_, ?_, fun r hr => ?_, fun l => lanes5 l, fun a ha => out5 a ha⟩
    · rw [gpr5]; simp only [assign, if_neg (show consts ≠ blocks by decide)]; omega
    · rw [gpr5]; simp [assign]
    · rw [gpr5]; simp only [assign, if_neg hr.2.2]; exact k4 r hr
  obtain ⟨n3, pc6, st6, inv6⟩ := loop_run _ (pre3 ls rs) paddingBlock _ (layout3 ls rs)
    (List.all_eq_true.mp pieces_straight.2.2.1) 8 (PadLoop ls rs s) (padLoop_step ls rs s ctx) (fun _ _ _ h => h) x5
    (by rw [rD]; simp only [pre3, List.length_append]) (by rw [rD]; simp [running]) start5 (by omega)
  refine ⟨middleCode.length + n3, ?_⟩
  rw [run_add, hx5]
  refine ⟨?_, st6, inv6⟩
  rw [pc6]; simp only [preO, List.length_append, List.length_cons, List.length_nil]

set_option maxRecDepth 100000 in
/-- The output: the second feed-forward and the digest copies. -/
theorem batch_output (ls rs : Nat) (s : State) (ctx : Ctx ls rs s) (x : State) (hpc : x.pc = (preO ls rs).length)
    (running : x.status = .running) (inv : PadLoop ls rs s 8 x) :
    BatchDone ls rs s (run (program ls rs) outputCode.length x) := by
  have rO := run_block _ _ _ _ (layoutO ls rs) (List.all_eq_true.mp pieces_straight.2.2.2) x hpc running
  obtain ⟨-, -, k6, l6, o6⟩ := inv
  obtain ⟨digests, rest, gpr7⟩ := output_full ls rs s ctx x (k6 sp kept_sp.1) (k6 out kept_sp.2.2) l6
  rw [rO]
  have outAt : (x.gpr out).toNat = (s.gpr out).toNat := by rw [k6 out kept_sp.2.2]
  refine ⟨by simp [running], output_end ls rs, fun p hp k hk => ?_, fun a ha hout => ?_, fun r hr => ?_⟩
  · show (exec outputCode x).mem _ = _
    rw [← outAt]; exact digests p hp k hk
  · show (exec outputCode x).mem a = _
    rw [rest a ha (by rw [outAt]; exact hout)]; exact o6 a ha
  · show (exec outputCode x).gpr r = _
    rw [gpr7 r hr.2.2]; exact k6 r hr

/-- One batch, from the loop's head: four pairs hashed. -/
theorem batch_run (ls rs : Nat) (s : State) (ctx : Ctx ls rs s) (hpc : s.pc = loopHead)
    (running : s.status = .running) : ∃ steps, BatchDone ls rs s (run (program ls rs) steps s) := by
  obtain ⟨n1, p1, s1, i1⟩ := batch_first ls rs s ctx hpc running
  obtain ⟨n2, p2, s2, i2⟩ := batch_second ls rs s ctx _ p1 s1 i1
  obtain ⟨n3, p3, s3, i3⟩ := batch_third ls rs s ctx _ p2 s2 i2
  refine ⟨n1 + n2 + n3 + outputCode.length, ?_⟩
  rw [run_add, run_add, run_add]
  exact batch_output ls rs s ctx _ p3 s3 i3

/-- The routine, cut around the pointer updates. -/
theorem layoutT (ls rs : Nat) : (program ls rs).toList = (pre0 ls rs ++ body ls rs) ++ tailCode ls rs ++
    .jnz loopHead :: [.addImm sp frame, .zeroReg .rax, .ret] := by
  rw [program_toList]
  simp only [pre0, body, batchCode, tailCode, List.append_assoc, List.cons_append, List.nil_append]

/-- The pointer updates never branch. -/
theorem tail_straight (ls rs : Nat) : ∀ i ∈ tailCode ls rs, i.straight := by
  -- No update is a branch.
  simp [tailCode, Instr.straight]

/-- The updates advance the three pointers, count one batch down, and set the zero flag on the last. -/
theorem tail_exec (ls rs : Nat) (x : State) :
    exec (tailCode ls rs) x =
      { x with
        gpr := assign (assign (assign (assign x.gpr left (x.gpr left + (4 * ls).toUInt64)) right
          (x.gpr right + (4 * rs).toUInt64)) out (x.gpr out + (128 : Nat).toUInt64)) count
          (x.gpr count - (1 : Nat).toUInt64)
        zf := x.gpr count - (1 : Nat).toUInt64 == 0
        cf := x.gpr count < (1 : Nat).toUInt64 } := by
  -- Each update writes one general register and sets the zero and carry flags.
  simp only [tailCode, exec, exec1]
  simp [assign]

/-- After a batch, the updates and the branch: back to the loop's head, or on to the closing instructions. -/
theorem after_batch (ls rs : Nat) (y : State) (hpc : y.pc = loopHead + (body ls rs).length)
    (running : y.status = .running) :
    run (program ls rs) 5 y =
      { exec (tailCode ls rs) y with pc := if (exec (tailCode ls rs) y).zf then finishAt ls rs else loopHead } := by
  have hpre : (pre0 ls rs ++ body ls rs).length = loopHead + (body ls rs).length := by
    simp [pre0, loopHead]; omega
  have f := fetch _ (pre0 ls rs ++ body ls rs ++ tailCode ls rs) _ _ (layoutT ls rs)
  rw [List.length_append, hpre] at f
  -- The updates run as a block, then the branch reads the zero flag.
  rw [show 5 = (tailCode ls rs).length + 1 from rfl, run_add,
    run_block _ _ _ _ (layoutT ls rs) (tail_straight ls rs) y (by rw [hpc, hpre]) running, hpre, run_one,
    step_jnz (t := loopHead)]
  · rw [exec_with_pc, show loopHead + (body ls rs).length + (tailCode ls rs).length + 1 = finishAt ls rs by
      simp only [finishAt, tailCode, List.length_cons, List.length_nil]]
  · exact f
  · simpa using running

/-- The closing instructions: drop the frame, clear the upper vector state, zero the result, and return. -/
theorem close_run (ls rs : Nat) (x : State) (hpc : x.pc = finishAt ls rs) (running : x.status = .running) :
    (run (program ls rs) 3 x).status = .returned ∧ (run (program ls rs) 3 x).mem = x.mem ∧
      (run (program ls rs) 3 x).gpr = assign (assign x.gpr sp (x.gpr sp + frame.toUInt64)) .rax 0 := by
  have lay : (program ls rs).toList = (pre0 ls rs ++ body ls rs ++ tailCode ls rs ++ [.jnz loopHead]) ++
      [.addImm sp frame, .zeroReg .rax] ++ .ret :: [] := by
    rw [layoutT]; simp only [List.append_assoc, List.cons_append, List.nil_append]
  have pre : (pre0 ls rs ++ body ls rs ++ tailCode ls rs ++ [Instr.jnz loopHead]).length = finishAt ls rs := by
    simp only [pre0, tailCode, finishAt, loopHead, List.length_append, List.length_cons, List.length_nil]
  have f := fetch _ _ _ _ lay
  rw [List.length_append, pre] at f
  -- The three instructions touch no memory, then the return stops the routine.
  rw [show 3 = [Instr.addImm sp frame, .zeroReg .rax].length + 1 from rfl, run_add,
    run_block _ _ _ _ lay (by simp [Instr.straight]) x (by rw [hpc, pre]) running, pre, run_one, step_ret]
  · refine ⟨rfl, by simp [exec, exec1], ?_⟩
    simp [exec, exec1]
  · exact f
  · simpa using running

/-- The opening instructions: make the frame, then skip to the closing ones when there is no batch. -/
theorem opening (ls rs : Nat) (s : State) (start : s.pc = 0) (running : s.status = .running) :
    run (program ls rs) 3 s =
      { s with
        gpr := assign s.gpr sp (s.gpr sp - frame.toUInt64), zf := s.gpr count == 0, cf := false,
        pc := if s.gpr count == 0 then finishAt ls rs else loopHead } := by
  have lay0 : (program ls rs).toList = [] ++ [.subImm sp frame, .test count] ++ (.jz (finishAt ls rs) ::
      (body ls rs ++ tailCode ls rs ++ [.jnz loopHead, .addImm sp frame, .zeroReg .rax, .ret])) := by
    rw [layoutT]; simp only [pre0, List.append_assoc, List.cons_append, List.nil_append]
  have lay1 : (program ls rs).toList = [.subImm sp frame, .test count] ++ .jz (finishAt ls rs) ::
      (body ls rs ++ tailCode ls rs ++ [.jnz loopHead, .addImm sp frame, .zeroReg .rax, .ret]) := by
    rw [lay0]; rfl
  have f := fetch _ _ _ _ lay1
  -- The frame and the count check, then the branch reads the flag.
  rw [show 3 = [Instr.subImm sp frame, .test count].length + 1 from rfl, run_add,
    run_block _ _ _ _ lay0 (by simp [Instr.straight]) s (by simp [start]) running, run_one,
    step_jz _ _ (finishAt ls rs) f (by simpa using running)]
  simp [exec, exec1, assign, loopHead]

/-- Where a run of batches reads and writes: within reach, and every region clear of the others. -/
structure Layout (ls rs : Nat) (s : State) (c : Nat) : Prop where
  /-- The constant table is in memory. -/
  table : TableAt s.mem (tableAt s)
  /-- The scratch area ends within reach. -/
  frameBound : scratch s + frame ≤ addressBound
  /-- The table ends within reach. -/
  tableBound : tableAt s + tableSize ≤ addressBound
  /-- The digests end within reach. -/
  outBound : (s.gpr out).toNat + 128 * c ≤ addressBound
  /-- The left nodes end within reach. -/
  leftBound : (s.gpr left).toNat + 4 * ls * c ≤ addressBound
  /-- The right nodes end within reach. -/
  rightBound : (s.gpr right).toNat + 4 * rs * c ≤ addressBound
  /-- The scratch area misses the table. -/
  tableFrame : Apart (scratch s, frame) (tableAt s, tableSize)
  /-- The digests miss the table. -/
  tableOut : Apart ((s.gpr out).toNat, 128 * c) (tableAt s, tableSize)
  /-- The digests miss the scratch area. -/
  outFrame : Apart ((s.gpr out).toNat, 128 * c) (scratch s, frame)
  /-- The digests and the scratch area miss every input node. -/
  inputs : ∀ p < 4 * c,
    Apart ((s.gpr out).toNat, 128 * c) ((s.gpr left).toNat + ls * p, 32) ∧
    Apart ((s.gpr out).toNat, 128 * c) ((s.gpr right).toNat + rs * p, 32) ∧
    Apart (scratch s, frame) ((s.gpr left).toNat + ls * p, 32) ∧
    Apart (scratch s, frame) ((s.gpr right).toNat + rs * p, 32)

/-- A layout for at least one batch holds what one batch needs. -/
theorem Layout.ctx {ls rs : Nat} {s : State} {c : Nat} (lay : Layout ls rs s (c + 1)) : Ctx ls rs s :=
  ⟨lay.table, lay.frameBound, lay.tableBound, lay.tableFrame,
    by have := lay.outFrame; simp only [Apart] at this ⊢; omega, fun p hp => ⟨(lay.inputs p (by omega)).2.2.1, (lay.inputs p (by omega)).2.2.2⟩⟩

/--
A finished run of batches: returned, every digest written, nothing else in memory touched but the scratch area.

The saved registers keep their values, the stack pointer has its frame dropped, and the result register holds zero.
-/
def Done (ls rs : Nat) (s : State) (c : Nat) (f : State) : Prop :=
  f.status = .returned ∧
  (∀ p < 4 * c, ∀ k < 32, f.mem ((s.gpr out).toNat + 32 * p + k) =
    (Sha256.hash (pairMessage s.mem ((s.gpr left).toNat + ls * p) ((s.gpr right).toNat + rs * p))).get! k) ∧
  (∀ a, ¬ ((s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 32 * (4 * c)) → Outside (scratch s) a → f.mem a = s.mem a) ∧
  (∀ r ∈ calleeSaved, r ≠ sp → f.gpr r = s.gpr r) ∧ f.gpr sp = s.gpr sp + frame.toUInt64 ∧ f.gpr .rax = 0

/-- A saved register is none the loops use, and none the updates write. -/
theorem saved_kept (r : Gpr) (hr : r ∈ calleeSaved) : Kept r ∧ r ≠ left ∧ r ≠ right ∧ r ≠ out ∧ r ≠ count := by
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨⟨by decide, by decide, by decide⟩,
    by decide, by decide, by decide, by decide⟩

/-- The updates leave every register but the three pointers and the count. -/
theorem tail_other (ls rs : Nat) (x : State) (r : Gpr) (h : r ≠ left ∧ r ≠ right ∧ r ≠ out ∧ r ≠ count) :
    (exec (tailCode ls rs) x).gpr r = x.gpr r := by
  rw [tail_exec]; simp [assign, h.1, h.2.1, h.2.2.1, h.2.2.2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- The loop from its head with c + 1 batches left. -/
theorem loop (ls rs : Nat) (c : Nat) : ∀ s : State, s.pc = loopHead → s.status = .running →
    (s.gpr count).toNat = c + 1 → Layout ls rs s (c + 1) →
    ∃ steps, Done ls rs s (c + 1) (run (program ls rs) steps s) := by
  induction c with
  | zero =>
    -- One batch left: run it, the updates, and the closing instructions.
    intro s hpc running counted lay
    obtain ⟨n, st, pcY, digests, frameY, keptY⟩ := batch_run ls rs s lay.ctx hpc running
    generalize hy : run (program ls rs) n s = y at st pcY digests frameY keptY
    have one : s.gpr count = 1 := UInt64.toNat_inj.mp (by simpa using counted)
    have countY : y.gpr count = 1 := by rw [keptY count ⟨by decide, by decide, by decide⟩, one]
    have zf : (exec (tailCode ls rs) y).zf = true := by rw [tail_exec, countY]; rfl
    obtain ⟨st', mem', gpr'⟩ := close_run ls rs { exec (tailCode ls rs) y with pc := finishAt ls rs } rfl
      (by simp only []; rw [exec_status]; exact st)
    refine ⟨n + 5 + 3, ?_⟩
    rw [run_add, run_add, hy, after_batch ls rs y pcY st, zf, if_pos rfl]
    have tmem : (exec (tailCode ls rs) y).mem = y.mem := by rw [tail_exec]
    refine ⟨st', fun p hp k hk => ?_, fun a hout ha => ?_, fun r hr hsp => ?_, ?_, ?_⟩
    · rw [mem']; simp only []; rw [tmem]; exact digests p (by omega) k hk
    · rw [mem']; simp only []; rw [tmem]; exact frameY a ha (by omega)
    · rw [gpr']; simp only [assign, if_neg (show r ≠ .rax from fun e => by subst e; simp [calleeSaved] at hr), if_neg hsp]
      obtain ⟨kr, nl, nr, no, nc⟩ := saved_kept r hr
      rw [tail_other ls rs y r ⟨nl, nr, no, nc⟩, keptY r kr]
    · rw [gpr']; simp only [assign, if_neg (show sp ≠ .rax by decide), if_true]
      rw [tail_other ls rs y sp ⟨by decide, by decide, by decide, by decide⟩, keptY sp kept_sp.1]
    · rw [gpr']; simp [assign]
  | succ c ih =>
    -- More batches left: run one, then the rest from the loop head, by induction.
    intro s hpc running counted lay
    obtain ⟨n, st, pcY, digests, frameY, keptY⟩ := batch_run ls rs s lay.ctx hpc running
    generalize hy : run (program ls rs) n s = y at st pcY digests frameY keptY
    have kept : ∀ r, r ≠ left ∧ r ≠ right ∧ r ≠ out ∧ r ≠ count → Kept r →
        (exec (tailCode ls rs) y).gpr r = s.gpr r := fun r h k => by rw [tail_other ls rs y r h, keptY r k]
    have O := lay.outBound
    have Lb := lay.leftBound
    have Rb := lay.rightBound
    have tfr := lay.tableFrame
    have tou := lay.tableOut
    have ofr := lay.outFrame
    have inp := lay.inputs
    simp only [Apart] at tfr tou ofr inp
    let y' : State := { exec (tailCode ls rs) y with pc := loopHead }
    have kl : Kept left := ⟨by decide, by decide, by decide⟩
    have kr : Kept right := ⟨by decide, by decide, by decide⟩
    have ko : Kept out := ⟨by decide, by decide, by decide⟩
    have kc : Kept count := ⟨by decide, by decide, by decide⟩
    have yout : (y'.gpr out).toNat = (s.gpr out).toNat + 128 := by
      have e : y'.gpr out = y.gpr out + (128 : Nat).toUInt64 := by simp only [y']; rw [tail_exec]; rfl
      rw [e, keptY out ko, add_toNat _ _ (by omega)]
    have yleft : (y'.gpr left).toNat = (s.gpr left).toNat + 4 * ls := by
      have : 4 * ls ≤ 4 * ls * (c + 1 + 1) := Nat.le_mul_of_pos_right _ (by omega)
      have e : y'.gpr left = y.gpr left + (4 * ls).toUInt64 := by simp only [y']; rw [tail_exec]; rfl
      rw [e, keptY left kl, add_toNat _ _ (by omega)]
    have yright : (y'.gpr right).toNat = (s.gpr right).toNat + 4 * rs := by
      have : 4 * rs ≤ 4 * rs * (c + 1 + 1) := Nat.le_mul_of_pos_right _ (by omega)
      have e : y'.gpr right = y.gpr right + (4 * rs).toUInt64 := by simp only [y']; rw [tail_exec]; rfl
      rw [e, keptY right kr, add_toNat _ _ (by omega)]
    have ycount : (y'.gpr count).toNat = c + 1 := by
      have e : y'.gpr count = y.gpr count - (1 : Nat).toUInt64 := by simp only [y']; rw [tail_exec]; rfl
      rw [e, keptY count kc, sub_toNat _ (by omega), counted]; rfl
    have ysp : y'.gpr sp = s.gpr sp := by
      simp only [y']; exact kept sp ⟨by decide, by decide, by decide, by decide⟩ kept_sp.1
    have ytbl : y'.gpr tbl = s.gpr tbl := by
      simp only [y']; exact kept tbl ⟨by decide, by decide, by decide, by decide⟩ kept_sp.2.1
    have ymem : y'.mem = y.mem := by simp only [y']; rw [tail_exec]
    -- The count was more than one, so the loop goes back.
    have zf : (exec (tailCode ls rs) y).zf = false := by
      have ne : y.gpr count - (1 : Nat).toUInt64 ≠ 0 := fun h => by
        have := congrArg UInt64.toNat h
        rw [sub_toNat _ (by rw [keptY count kc]; omega), keptY count kc] at this
        simp at this
        omega
      rw [tail_exec]
      simpa using ne
    -- Products of a stride and a count, split off one batch.
    have lsplit : ∀ p, ls * (4 + p) = 4 * ls + ls * p := fun p => by rw [Nat.mul_add, Nat.mul_comm ls 4]
    have rsplit : ∀ p, rs * (4 + p) = 4 * rs + rs * p := fun p => by rw [Nat.mul_add, Nat.mul_comm rs 4]
    have lnext : 4 * ls * (c + 1 + 1) = 4 * ls + 4 * ls * (c + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    have rnext : 4 * rs * (c + 1 + 1) = 4 * rs + 4 * rs * (c + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    -- Memory the batch did not write still holds what it held.
    have kept_at : ∀ a, Outside (scratch s) a → ¬ ((s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 128) →
        y'.mem a = s.mem a := fun a ha hb => by rw [ymem]; exact frameY a ha hb
    have yS : scratch y' = scratch s := by simp only [scratch]; rw [ysp]
    have yT : tableAt y' = tableAt s := by simp only [tableAt]; rw [ytbl]
    have next : Layout ls rs y' (c + 1) := by
      refine ⟨fun i hi => ?_, by rw [yS]; exact lay.frameBound, by rw [yT]; exact lay.tableBound, by rw [yout]; omega,
        by rw [yleft]; omega, by rw [yright]; omega, by rw [yS, yT]; exact lay.tableFrame, ?_, ?_, fun p hp => ?_⟩
      · rw [yT, kept_at _ (by simp only [Outside, tableSize] at tfr hi ⊢; omega)
          (by simp only [tableSize] at tou hi ⊢; omega)]
        exact lay.table i hi
      · simp only [Apart, yout, yT]; omega
      · simp only [Apart, yout, yS]; omega
      · have := inp (4 + p) (by omega)
        rw [lsplit, rsplit] at this
        simp only [Apart, yout, yleft, yright, yS]
        omega
    obtain ⟨steps, st', outs, frame', saved, spF, rax⟩ :=
      ih y' rfl (by simp only [y']; rw [exec_status]; exact st) ycount next
    refine ⟨n + 5 + steps, ?_⟩
    rw [run_add, run_add, hy, after_batch ls rs y pcY st, zf]
    simp only [Bool.false_eq_true, ↓reduceIte]
    -- Each digest comes from this batch or a later one.
    refine ⟨st', fun p hp k hk => ?_, fun a ha hs => ?_, fun r hr hsp => ?_, ?_, rax⟩
    · by_cases first : p < 4
      · -- This batch's digests: the later batches write past them.
        refine (frame' _ (by rw [yout]; omega) (by rw [yS]; simp only [Outside, frame] at ofr ⊢; omega)).trans ?_
        rw [ymem]
        exact digests p first k hk
      · -- A later batch's digests, from inputs this batch left alone.
        have := outs (p - 4) (by omega) k hk
        rw [yout, yleft, yright, show (s.gpr out).toNat + 128 + 32 * (p - 4) + k = (s.gpr out).toNat + 32 * p + k by
          omega] at this
        refine this.trans ?_
        have hp' := lsplit (p - 4)
        have hr' := rsplit (p - 4)
        rw [show 4 + (p - 4) = p by omega] at hp' hr'
        rw [show (s.gpr left).toNat + 4 * ls + ls * (p - 4) = (s.gpr left).toNat + ls * p by omega,
          show (s.gpr right).toNat + 4 * rs + rs * (p - 4) = (s.gpr right).toNat + rs * p by omega]
        have := inp p hp
        rw [Avx512.pairMessage_congr y'.mem s.mem _ _
          (fun i hi => kept_at _ (by simp only [Outside, frame] at this ⊢; omega) (by omega))
          (fun i hi => kept_at _ (by simp only [Outside, frame] at this ⊢; omega) (by omega))]
    · exact (frame' _ (by rw [yout]; omega) (by rw [yS]; exact hs)).trans (kept_at _ hs (by omega))
    · refine (saved r hr hsp).trans ?_
      obtain ⟨kr', nl, nr, no, nc⟩ := saved_kept r hr
      exact kept r ⟨nl, nr, no, nc⟩ kr'
    · rw [spF, ysp]

set_option maxRecDepth 100000 in
/--
The four-lane kernel hashes every pair it is given.

Started at its first instruction, with a count of batches of four pairs, it returns having written each pair's digest.
Pair p is the 32 bytes at the left address plus p times the left stride, then the 32 bytes at the right address plus p times the right stride.
Its digest lands 32 p bytes past the output address.
No other memory changes but the scratch area just below the stack pointer.
The registers the calling convention saves keep their values, and the result register holds zero.

The output, the table, the inputs, and the scratch area must sit clear of each other where the routine writes,
and every region must lie within reach.
-/
theorem program_correct (ls rs : Nat) (s : State) (start : s.pc = 0) (running : s.status = .running)
    (table : TableAt s.mem (s.gpr tbl).toNat) (n : Nat) (pairs : n = 4 * (s.gpr count).toNat)
    (room : frame ≤ (s.gpr sp).toNat) (spBound : (s.gpr sp).toNat ≤ addressBound)
    (tableBound : (s.gpr tbl).toNat + tableSize ≤ addressBound)
    (outBound : (s.gpr out).toNat + 32 * n ≤ addressBound)
    (leftBound : (s.gpr left).toNat + ls * n ≤ addressBound)
    (rightBound : (s.gpr right).toNat + rs * n ≤ addressBound)
    (tableApart : Apart ((s.gpr out).toNat, 32 * n) ((s.gpr tbl).toNat, tableSize))
    (inputsApart : ∀ p < n, Apart ((s.gpr out).toNat, 32 * n) ((s.gpr left).toNat + ls * p, 32) ∧
      Apart ((s.gpr out).toNat, 32 * n) ((s.gpr right).toNat + rs * p, 32))
    (scratchApart : Apart ((s.gpr sp).toNat - frame, frame) ((s.gpr tbl).toNat, tableSize) ∧
      Apart ((s.gpr out).toNat, 32 * n) ((s.gpr sp).toNat - frame, frame) ∧
      ∀ p < n, Apart ((s.gpr sp).toNat - frame, frame) ((s.gpr left).toNat + ls * p, 32) ∧
        Apart ((s.gpr sp).toNat - frame, frame) ((s.gpr right).toNat + rs * p, 32)) :
    ∃ steps,
      (run (program ls rs) steps s).status = .returned ∧
      (∀ p < n, ∀ k < 32, (run (program ls rs) steps s).mem ((s.gpr out).toNat + 32 * p + k) =
        (Sha256.hash (pairMessage s.mem ((s.gpr left).toNat + ls * p) ((s.gpr right).toNat + rs * p))).get! k) ∧
      (∀ a, ¬ ((s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 32 * n) →
        ¬ ((s.gpr sp).toNat - frame ≤ a ∧ a < (s.gpr sp).toNat) → (run (program ls rs) steps s).mem a = s.mem a) ∧
      (∀ r ∈ calleeSaved, (run (program ls rs) steps s).gpr r = s.gpr r) ∧
      (run (program ls rs) steps s).gpr .rax = 0 := by
  subst pairs
  have opened := opening ls rs s start running
  have spNat : (s.gpr sp - frame.toUInt64).toNat = (s.gpr sp).toNat - frame := subN_toNat _ _ room
  have notRax : ∀ r ∈ calleeSaved, r ≠ .rax := fun r hr e => by subst e; simp [calleeSaved] at hr
  cases h : (s.gpr count).toNat with
  | zero =>
    -- No batch: straight to the closing instructions.
    have zero : s.gpr count = 0 := UInt64.toNat_inj.mp (by simpa using h)
    simp only [zero, beq_self_eq_true, ↓reduceIte] at opened
    obtain ⟨st, mem, gpr⟩ := close_run ls rs { s with
      gpr := assign s.gpr sp (s.gpr sp - frame.toUInt64), zf := true, cf := false, pc := finishAt ls rs } rfl running
    refine ⟨3 + 3, ?_⟩
    rw [run_add, opened]
    refine ⟨st, fun p hp => absurd hp (by omega), fun a _ _ => congrFun mem a, fun r hr => ?_, by rw [gpr]; simp [assign]⟩
    rw [gpr]
    by_cases hsp : r = sp
    · subst hsp; simp [assign]
    · simp [assign, hsp, notRax r hr]
  | succ c =>
    -- At least one batch: the loop, from its head.
    have nonzero : (s.gpr count == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro zero
      rw [zero] at h
      simp at h
    simp only [nonzero, Bool.false_eq_true, ↓reduceIte] at opened
    let x : State := { s with
      gpr := assign s.gpr sp (s.gpr sp - frame.toUInt64), zf := false, cf := false, pc := loopHead }
    have xg : ∀ r, r ≠ sp → x.gpr r = s.gpr r := fun r hr => by simp [x, assign, hr]
    have xS : scratch x = (s.gpr sp).toNat - frame := by simp only [scratch, x, assign, if_true]; exact spNat
    have xT : tableAt x = (s.gpr tbl).toNat := by simp only [tableAt]; rw [xg tbl (by decide)]
    obtain ⟨tA, oA, iA⟩ := scratchApart
    rw [h] at outBound leftBound rightBound tableApart inputsApart oA iA
    have layout : Layout ls rs x (c + 1) := by
      refine ⟨by rw [xT]; exact table, by rw [xS]; omega, by rw [xT]; exact tableBound, ?_, ?_, ?_,
        by rw [xS, xT]; exact tA, ?_, ?_, fun p hp => ?_⟩
      · rw [xg out (by decide)]; omega
      · rw [xg left (by decide), show 4 * ls * (c + 1) = ls * (4 * (c + 1)) by
          rw [Nat.mul_comm 4 ls, Nat.mul_assoc]]; exact leftBound
      · rw [xg right (by decide), show 4 * rs * (c + 1) = rs * (4 * (c + 1)) by
          rw [Nat.mul_comm 4 rs, Nat.mul_assoc]]; exact rightBound
      · rw [xg out (by decide), xT]; simp only [Apart] at tableApart ⊢; omega
      · rw [xg out (by decide), xS]; simp only [Apart] at oA ⊢; omega
      · have i1 := inputsApart p hp
        have i2 := iA p hp
        rw [xg out (by decide), xg left (by decide), xg right (by decide), xS]
        simp only [Apart] at i1 i2 ⊢
        omega
    have xc : (x.gpr count).toNat = c + 1 := by rw [xg count (by decide), h]
    obtain ⟨steps, st, outs, frame', saved, spF, rax⟩ := loop ls rs c x rfl running xc layout
    refine ⟨3 + steps, ?_⟩
    rw [run_add, opened]
    simp only [xg out (by decide), xg left (by decide), xg right (by decide), xS] at outs frame'
    refine ⟨st, fun p hp k hk => outs p (by omega) k hk, fun a ha hs => frame' a (by omega) ?_, fun r hr => ?_, rax⟩
    · simp only [Outside] at hs ⊢; omega
    · by_cases hsp : r = sp
      · subst hsp; rw [spF]; simp [x, assign]
      · exact (saved r hr hsp).trans (xg r hsp)

/-- The routine calls no other routine. -/
theorem leaf (ls rs : Nat) : Leaf (program ls rs) := by
  intro i hi name
  rintro rfl
  rw [program_toList] at hi
  -- Only the straight-line pieces could hold a call, and a call is not straight-line.
  simp only [List.mem_append, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_false, false_or] at hi
  obtain ⟨fb, mS, pS, oS⟩ := pieces_straight
  have notStraight : (Instr.call name).straight = false := rfl
  rcases hi with (((((h | h) | h) | h) | h) | h) | h
  · simpa [notStraight] using setup_straight ls rs _ h
  · simpa [notStraight] using List.all_eq_true.mp (fb true) _ h
  · simpa [notStraight] using List.all_eq_true.mp (fb false) _ h
  · simpa [notStraight] using List.all_eq_true.mp mS _ h
  · simpa [notStraight] using List.all_eq_true.mp pS _ h
  · simpa [notStraight] using List.all_eq_true.mp oS _ h
  · simpa [notStraight] using tail_straight ls rs _ h

end Ssz.Native.Kernel.Baseline
