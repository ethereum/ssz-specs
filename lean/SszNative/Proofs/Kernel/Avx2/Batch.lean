import SszNative.Proofs.Kernel.Avx2.Rounds
import SszNative.Proofs.Kernel.Avx2.Moves

/-!
The eight-lane kernel's straight-line pieces, each from its start to its end.

A batch reads its sixteen schedule words into the scratch area, then loops over three blocks of rounds,
with a feed-forward between the second and third loops, and ends with the stores of the digests.
Each piece below is one of those, or one pass of a loop's body.
-/

namespace EthLib.Consensus.Ssz.Native.Kernel.Avx2

open EthLib.Cryptography.Hash.Sha256 hiding K IV
open EthLib.Consensus.Ssz.Native.Asm
open EthLib.Consensus.Ssz.Native.Kernel.Avx512x2 (View addrOf)
open EthLib.Consensus.Ssz.Native.Kernel.Avx512 (assign_apply)

/-- The scratch area's address: the stack pointer, after the frame is made. -/
abbrev scratch (s : State) : Nat := (s.gpr sp).toNat

/-- The constant table's address. -/
abbrev tableAt (s : State) : Nat := (s.gpr tbl).toNat

/-- The message of pair l of a batch: its left node then its right node. -/
def msg (s : State) (ls rs l : Nat) : ByteArray :=
  pairMessage s.mem ((s.gpr left).toNat + ls * l) ((s.gpr right).toNat + rs * l)

/-- Where a batch reads and writes: the scratch area within reach, clear of the table and of every input node. -/
structure Ctx (ls rs : Nat) (s : State) : Prop where
  /-- The constant table is in memory. -/
  table : TableAt s.mem (tableAt s)
  /-- The scratch area ends within reach. -/
  frameBound : scratch s + frame ≤ addressBound
  /-- The table ends within reach. -/
  tableBound : tableAt s + tableSize ≤ addressBound
  /-- The scratch area misses the table. -/
  tableApart : Apart (scratch s, frame) (tableAt s, tableSize)
  /-- The scratch area misses every input node. -/
  inputsApart : ∀ p < 8, Apart (scratch s, frame) ((s.gpr left).toNat + ls * p, 32) ∧
    Apart (scratch s, frame) ((s.gpr right).toNat + rs * p, 32)

/-- Whether an address lies outside the scratch area. -/
def Outside (S a : Nat) : Prop := a < S ∨ S + frame ≤ a

/-- Memory that agrees outside the scratch area still holds the table. -/
theorem table_kept (mem mem' : Nat → UInt8) (S T : Nat) (table : TableAt mem T)
    (apart : Apart (S, frame) (T, tableSize)) (same : ∀ a, Outside S a → mem' a = mem a) : TableAt mem' T := by
  -- Every table byte lies outside the scratch area.
  intro i hi
  simp only [Apart] at apart
  rw [same _ (by simp only [Outside]; omega)]
  exact table i hi

/-- Lane l of a table row of sixteen equal words, read through a lane view, is that word. -/
theorem view_row (mem : Nat → UInt8) (T : Nat) (table : TableAt mem T) (row : Nat) (hrow : row < 149) (l : Fin 8) :
    readWord mem (T + 64 * row + 4 * l.val) = tableWord (16 * row + l.val) := by
  rw [show T + 64 * row + 4 * l.val = T + 4 * (16 * row + l.val) by omega]
  exact readWord_table _ _ table _ (by simp only [tableSize]; omega)

/-- The initial-state loads, lane by lane: register j holds word j of the initial state. -/
theorem ivCode_view (G : Gpr → UInt64) (v : View) (hiv : ∀ j < 8, v.mem ((G tbl).toNat + ivAvx512 j) = Cryptography.Hash.Sha256.IV[j]!) :
    (∀ j < 8, (viewRun G ivCode v).regs (home j) = Cryptography.Hash.Sha256.IV[j]!) ∧ (viewRun G ivCode v).mem = v.mem := by
  refine ⟨fun j hj => ?_, by funext a; exact viewRun_mem_other _ _ _ _ (by simp [ivCode, storeOf])⟩
  -- Each of the eight loads writes its own register.
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ivCode, List.range, List.range.loop, List.map, viewRun, viewStep, assign_apply, home, addrOf,
      tableEntry] <;> simp <;> first | exact hiv _ (by omega) | simpa using hiv _ (by decide : (0 : Nat) < 8)

/-- The setup's last four instructions: the schedule pointer, the constants pointer, and the first loop's count. -/
def pointerCode : List Instr :=
  [.movReg words sp, .addImm words (wordsBase 0), .movReg consts tbl, .movImm blocks 6]

/-- The setup is the two halves' loads, the initial state, and the pointers. -/
theorem setupCode_eq (ls rs : Nat) :
    setupCode ls rs = loadWords left ls 0 ++ loadWords right rs 8 ++ ivCode ++ pointerCode := by
  simp [setupCode, pointerCode, List.append_assoc]

/-- A register none of the loop pointers names. -/
def Kept (r : Gpr) : Prop := r ≠ words ∧ r ≠ consts ∧ r ≠ blocks

set_option maxHeartbeats 1000000 in
/--
The setup: every lane holds the initial state, the scratch area holds the sixteen input words, and the pointers are set.

Memory outside the scratch area, and every register the loops do not use, keep their values.
-/
theorem setup_spec (ls rs : Nat) (s : State) (ctx : Ctx ls rs s) :
    let x := exec (setupCode ls rs) s
    (∀ l : Fin 8, FirstInv (scratch s) (msg s ls rs l.val) 0 (view x l)) ∧
    (∀ a, Outside (scratch s) a → x.mem a = s.mem a) ∧
    (x.gpr words).toNat = scratch s + wordsBase 0 ∧ x.gpr consts = s.gpr tbl ∧ x.gpr blocks = 6 ∧
    (∀ r, Kept r → x.gpr r = s.gpr r) := by
  intro x
  have apartT := ctx.tableApart
  have apartI := ctx.inputsApart
  have bound := ctx.frameBound
  simp only [Apart] at apartT apartI
  -- The left halves.
  obtain ⟨w1, k1, f1, g1, -, -⟩ := loadWords_spec left ls 0 (by omega) s ctx.table
  let x1 := exec (loadWords left ls 0) s
  have outside1 : ∀ a, Outside (scratch s) a → x1.mem a = s.mem a := fun a ha => f1 a fun t ht => by
    simp only [Outside, wordSlot, frame, scratch] at ha ⊢; omega
  have table1 : TableAt x1.mem (x1.gpr tbl).toNat := by
    rw [show x1.gpr = s.gpr from g1]; exact table_kept _ _ _ _ ctx.table ctx.tableApart outside1
  -- The right halves.
  obtain ⟨w2, k2, f2, g2, -, -⟩ := loadWords_spec right rs 8 (by omega) x1 table1
  let x2 := exec (loadWords right rs 8) x1
  have gs2 : x2.gpr = s.gpr := g2.trans g1
  have w1' : ∀ t < 8, ∀ l : Fin 8, readWord x1.mem (scratch s + wordSlot t + 4 * l.val) =
      bswap (readWord s.mem ((s.gpr left).toNat + ls * l.val + 4 * t)) := fun t ht l => by
    simpa using w1 t ht l
  have w2' : ∀ t < 8, ∀ l : Fin 8, readWord x2.mem (scratch s + wordSlot (8 + t) + 4 * l.val) =
      bswap (readWord x1.mem ((s.gpr right).toNat + rs * l.val + 4 * t)) := fun t ht l => by
    have := w2 t ht l
    rw [show x1.gpr = s.gpr from g1] at this
    exact this
  have k2' : ∀ (q : Nat) (l : Fin 8), (∀ t < 8, scratch s + 32 * q ≠ scratch s + wordSlot (8 + t)) →
      readWord x2.mem (scratch s + 32 * q + 4 * l.val) = readWord x1.mem (scratch s + 32 * q + 4 * l.val) :=
    fun q l h => by
      have := k2 q l (by rw [show x1.gpr = s.gpr from g1]; exact h)
      rw [show x1.gpr = s.gpr from g1] at this
      exact this
  have outside2 : ∀ a, Outside (scratch s) a → x2.mem a = s.mem a := fun a ha => by
    rw [show x2.mem a = x1.mem a from f2 a fun t ht => by
      simp only [show x1.gpr = s.gpr from g1, Outside, wordSlot, frame, scratch] at ha ⊢; omega]
    exact outside1 a ha
  have table2 : TableAt x2.mem (x2.gpr tbl).toNat := by
    rw [gs2]; exact table_kept _ _ _ _ ctx.table ctx.tableApart outside2
  -- The initial state, lane by lane.
  obtain ⟨v3, m3, f3, g3, -, -⟩ := exec_view ivCode (by simp [ivCode, rowwise]) x2 (by simp [readsOf, ivCode, readOf,
    storesOf, storeOf, Clear])
  let x3 := exec ivCode x2
  have iv3 : ∀ j < 8, ∀ l : Fin 8, x3.vec (home j) (lane l) = Cryptography.Hash.Sha256.IV[j]! := fun j hj l => by
    rw [v3]
    refine (ivCode_view x2.gpr (view x2 l) fun j hj => ?_).1 j hj
    simp only [view, ivAvx512, gs2]
    rw [show (s.gpr tbl).toNat + (8192 + 64 * j) + 4 * l.val = (s.gpr tbl).toNat + 64 * (128 + j) + 4 * l.val by
      omega, ← gs2, view_row _ _ table2 _ (by omega), Avx512.tableWord_iv j l.val hj (by omega)]
  have mem3 : x3.mem = x2.mem := funext fun a => f3 a (by simp [storesOf, ivCode, storeOf])
  -- The pointers.
  have last : x = exec pointerCode x3 := by simp only [x, x3, x2, x1, setupCode_eq, exec_append]
  have xmem : x.mem = x3.mem := by rw [last]; simp [pointerCode, exec, exec1]
  have xvec : x.vec = x3.vec := by rw [last]; simp [pointerCode, exec, exec1]
  have xgpr : x.gpr = assign (assign (assign (assign x3.gpr words (x3.gpr sp)) words
      (x3.gpr sp + (wordsBase 0).toUInt64)) consts (x3.gpr tbl)) blocks 6 := by
    rw [last]; simp [pointerCode, exec, exec1, assign]
  rw [g3, gs2] at xgpr
  clear_value x x3 x2 x1
  refine ⟨fun l => ⟨?_, fun u hu hu' => ?_⟩, fun a ha => ?_, ?_, ?_, ?_, fun r hr => ?_⟩
  · -- Every working word is the initial state's.
    apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn, Avx512.roundsTo, List.range_zero, List.foldl_nil, view, xvec]
    rw [show role 0 j = home j by apply Fin.ext; simp only [role, home]; omega, iv3 j hj l,
      getElem!_pos Cryptography.Hash.Sha256.IV j hj]
  · -- The input words: the left node's below 8, the right node's from 8.
    simp only [view, xmem, mem3]
    rw [Avx512.W_input _ u (by omega), msg, Avx512.pairMessage_word _ _ _ u (by omega)]
    by_cases high : 8 ≤ u
    · obtain ⟨t, rfl⟩ : ∃ t, u = 8 + t := ⟨u - 8, by omega⟩
      have := apartI l.val l.isLt
      have same : readWord x1.mem ((s.gpr right).toNat + rs * l.val + 4 * t) =
          readWord s.mem ((s.gpr right).toNat + rs * l.val + 4 * t) := by
        simp only [readWord]
        rw [outside1 _ (by simp only [Outside]; omega), outside1 _ (by simp only [Outside]; omega),
          outside1 _ (by simp only [Outside]; omega), outside1 _ (by simp only [Outside]; omega)]
      rw [w2' t (by omega) l, ite_eq_right (by omega), show (8 + t) % 8 = t by omega, same]
    · obtain ⟨q, hq⟩ := wordSlot_mod u (by omega)
      have keep := k2' q l fun t ht e => by
        simp only [wordSlot, frame] at e hq; omega
      rw [hq, keep, ← hq, w1' u (by omega) l, ite_eq_left (by omega), Nat.mod_eq_of_lt (by omega : u < 8)]
  · rw [xmem, mem3]; exact outside2 a ha
  · rw [xgpr]; simp only [assign, ite_true, ite_eq_right (show words ≠ blocks by decide), ite_eq_right (show words ≠ consts by decide)]
    simp only [UInt64.toNat_add, wordsBase, scratch, addressBound] at bound ⊢
    simp
    omega
  · rw [xgpr]; simp [assign]
  · rw [xgpr]; simp [assign]
  · obtain ⟨a, b, c⟩ := hr
    rw [xgpr]; simp [assign, a, b, c]

/-- A schedule row through the schedule pointer: 32-byte aligned within the 24 words a block reaches. -/
def frameOp (m : Mem) : Bool := m.base == words && m.disp % 32 == 0 && m.disp + 32 ≤ 768

/-- A table row through the constants pointer, among the eight a block reaches. -/
def constOp (m : Mem) : Bool := m.base == consts && m.disp % 64 == 0 && m.disp < 512

/-- Whether an instruction in a loop reads only schedule or table rows, and stores only schedule rows. -/
def loopOps : Instr → Bool
  | .yaddMem _ _ m | .vloadHalf _ m => frameOp m || constOp m
  | .vstoreHalf m _ => frameOp m
  | _ => true

/-- Every read of a loop's body is a schedule row or a table row. -/
theorem loopOps_reads (G : Gpr → UInt64) (body : List Instr) (h : body.all loopOps = true) (a : Nat)
    (ha : a ∈ readsOf G body) :
    (∃ d, d % 32 = 0 ∧ d + 32 ≤ 768 ∧ a = (G words).toNat + d) ∨
      (∃ d, d % 64 = 0 ∧ d < 512 ∧ a = (G consts).toNat + d) := by
  simp only [readsOf, List.mem_filterMap] at ha
  obtain ⟨i, hi, hr⟩ := ha
  have ok := List.all_eq_true.mp h i hi
  -- Only the two reading instructions name a row, through one of the two pointers.
  cases i <;> simp only [readOf, reduceCtorEq] at hr <;> simp only [loopOps, frameOp, constOp, Bool.or_eq_true,
    Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok <;> simp only [Option.some.injEq, addrOf] at hr <;>
    rcases ok with ⟨⟨b, d1⟩, d2⟩ | ⟨⟨b, d1⟩, d2⟩ <;> rw [b] at hr <;>
    first | exact .inl ⟨_, d1, d2, hr.symm⟩ | exact .inr ⟨_, d1, d2, hr.symm⟩

/-- Every store of a loop's body is a schedule row. -/
theorem loopOps_stores (G : Gpr → UInt64) (body : List Instr) (h : body.all loopOps = true) (A : Nat)
    (hA : A ∈ storesOf G body) : ∃ d, d % 32 = 0 ∧ d + 32 ≤ 768 ∧ A = (G words).toNat + d := by
  simp only [storesOf, List.mem_filterMap] at hA
  obtain ⟨i, hi, hr⟩ := hA
  have ok := List.all_eq_true.mp h i hi
  -- Only a store names a row to write, through the schedule pointer.
  cases i <;> simp only [storeOf, reduceCtorEq] at hr
  simp only [loopOps, frameOp, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  simp only [Option.some.injEq, addrOf] at hr
  obtain ⟨⟨b, d1⟩, d2⟩ := ok
  rw [b] at hr
  exact ⟨_, d1, d2, hr.symm⟩

/-- In a loop's body, every read is clear of every store: schedule rows share the grid, and table rows lie apart. -/
theorem loopOps_clear (G : Gpr → UInt64) (body : List Instr) (h : body.all loopOps = true) (S T i : Nat)
    (hi : i < 8) (wordsAt : (G words).toNat = S + wordsBase i) (constsIn : T ≤ (G consts).toNat)
    (constsEnd : (G consts).toNat + 512 ≤ T + tableSize) (apart : Apart (S, frame) (T, tableSize)) :
    ∀ a ∈ readsOf G body, Clear (storesOf G body) a := by
  intro a ha A hA
  obtain ⟨dA, mA, bA, rfl⟩ := loopOps_stores G body h A hA
  simp only [Apart] at apart
  rcases loopOps_reads G body h a ha with ⟨d, m, b, rfl⟩ | ⟨d, m, b, rfl⟩
  · -- Two schedule rows share the 32-byte grid.
    left; rw [wordsAt]; simp only [wordsBase]; omega
  · -- A table row lies outside the scratch area, which holds every store.
    right; rw [wordsAt]; simp only [wordsBase, frame] at apart ⊢; omega

/-- Eight first-block rounds of the loop's body, without the pointer updates. -/
def firstLanes (sched : Bool) : List Instr :=
  (List.range 8).flatMap fun k => firstRound k ++ (if sched then scheduleStep k else [])

/-- A first-block pass is its rounds, then the pointer updates. -/
theorem firstBlock_eq (sched : Bool) :
    firstBlock sched = firstLanes sched ++ [.subImm words 256, .addImm consts 512, .subImm blocks 1] := rfl

/-- The first-block rounds read and store only schedule and table rows. -/
theorem firstLanes_ops : ∀ b, (firstLanes b).all loopOps = true := by
  -- Both cases, checked by evaluation.
  decide +kernel

/-- The first-block rounds act on each lane alone. -/
theorem firstLanes_rowwise : ∀ b, (firstLanes b).all rowwise = true := by
  -- Both cases, checked by evaluation.
  decide +kernel

/-- The invariant reads only the working words and the schedule rows. -/
theorem FirstInv.congr {S : Nat} {m : ByteArray} {t : Nat} {v w : View} (inv : FirstInv S m t v)
    (regs : ∀ r, w.regs r = v.regs r) (mem : ∀ u < 64, w.mem (S + wordSlot u) = v.mem (S + wordSlot u)) :
    FirstInv S m t w := by
  obtain ⟨roles, words'⟩ := inv
  refine ⟨?_, fun u hu hu' => (mem u hu).trans (words' u hu hu')⟩
  rw [← roles]; simp only [regs]

/-- Schedule rows share the 32-byte grid with every store of a loop's body. -/
theorem slot_clear (G : Gpr → UInt64) (body : List Instr) (h : body.all loopOps = true) (S i u : Nat) (hi : i < 8)
    (wordsAt : (G words).toNat = S + wordsBase i) : Clear (storesOf G body) (S + wordSlot u) := by
  intro A hA
  obtain ⟨d, m, _, rfl⟩ := loopOps_stores G body h A hA
  left; rw [wordsAt]; simp only [wordsBase, wordSlot, frame]; omega

/-- A loop's body stores only inside the scratch area. -/
theorem outside_kept (G : Gpr → UInt64) (body : List Instr) (h : body.all loopOps = true) (S i a : Nat) (hi : i < 8)
    (wordsAt : (G words).toNat = S + wordsBase i) (ha : Outside S a) :
    ∀ A ∈ storesOf G body, a < A ∨ A + 32 ≤ a := by
  intro A hA
  obtain ⟨d, _, b, rfl⟩ := loopOps_stores G body h A hA
  rw [wordsAt]
  simp only [Outside, wordsBase, frame] at ha ⊢
  omega

set_option maxHeartbeats 1000000 in
/--
One pass of a first-block loop: every lane's invariant eight rounds on, and the pointers and count updated.

Memory outside the scratch area, and every register the loops do not use, keep their values.
-/
theorem firstBlock_spec (ls rs : Nat) (s : State) (ctx : Ctx ls rs s) (i : Nat) (hi : i < 8) (sched : Bool)
    (hs : sched = decide (i < 6)) (x : State) (wordsAt : (x.gpr words).toNat = scratch s + wordsBase i)
    (constsAt : (x.gpr consts).toNat = tableAt s + 512 * i)
    (inv : ∀ l : Fin 8, FirstInv (scratch s) (msg s ls rs l.val) (8 * i) (view x l))
    (outside : ∀ a, Outside (scratch s) a → x.mem a = s.mem a) :
    let y := exec (firstBlock sched) x
    (∀ l : Fin 8, FirstInv (scratch s) (msg s ls rs l.val) (8 * i + 8) (view y l)) ∧
    (∀ a, Outside (scratch s) a → y.mem a = s.mem a) ∧
    y.gpr = assign (assign (assign x.gpr words (x.gpr words - (256 : Nat).toUInt64)) consts
      (x.gpr consts + (512 : Nat).toUInt64)) blocks (x.gpr blocks - (1 : Nat).toUInt64) ∧
    y.zf = (x.gpr blocks - (1 : Nat).toUInt64 == 0) := by
  intro y
  have apart := ctx.tableApart
  have tb := ctx.tableBound
  have table : TableAt x.mem (tableAt s) := table_kept _ _ _ _ ctx.table apart outside
  have ops := firstLanes_ops sched
  obtain ⟨v, m, f, g, -, -⟩ := exec_view (firstLanes sched) (List.all_eq_true.mp (firstLanes_rowwise sched)) x
    (loopOps_clear x.gpr _ ops (scratch s) (tableAt s) i hi wordsAt (by omega)
      (by rw [constsAt]; simp only [tableSize]; omega) apart)
  let x' := exec (firstLanes sched) x
  have whole : y = exec [.subImm words 256, .addImm consts 512, .subImm blocks 1] x' := by
    simp only [y, x', firstBlock_eq, exec_append]
  have ymem : y.mem = x'.mem := by rw [whole]; simp [exec, exec1]
  have yvec : y.vec = x'.vec := by rw [whole]; simp [exec, exec1]
  have xg : x'.gpr = x.gpr := g
  refine ⟨fun l => ?_, fun a ha => ?_, ?_, ?_⟩
  · -- Each lane runs its eight rounds, reading the table's constants.
    have konst : ∀ k < 8, (view x l).mem ((x.gpr consts).toNat + 64 * k) = Avx512.K (8 * i + k) := fun k hk => by
      simp only [view]
      rw [constsAt, show tableAt s + 512 * i + 64 * k = tableAt s + 64 * (8 * i + k) by omega,
        view_row _ _ table _ (by omega), Avx512.tableWord_k _ _ (by omega) (by omega)]
    have far : ∀ k < 8, ∀ u < 64, (x.gpr consts).toNat + 64 * k ≠ scratch s + wordSlot u := fun k hk u hu => by
      simp only [Apart] at apart
      rw [constsAt]; simp only [wordSlot, frame, tableSize] at apart ⊢; omega
    obtain ⟨next, -⟩ := first_block x.gpr (view x l) (scratch s) (msg s ls rs l.val) i hi sched hs wordsAt konst far
      (inv l)
    refine next.congr (fun r => ?_) (fun u _ => ?_)
    · simp only [view, yvec]; exact v r l
    · simp only [view, ymem]
      exact m l _ (slot_clear x.gpr _ ops (scratch s) i u hi wordsAt)
  · rw [ymem, f a (outside_kept x.gpr _ ops (scratch s) i a hi wordsAt ha)]
    exact outside a ha
  · rw [whole]; simp only [exec, exec1, xg]; rfl
  · rw [whole]; simp only [exec, exec1, xg]; simp [assign]

/-- Eight padding rounds of the loop's body, without the pointer updates. -/
def padLanes : List Instr := (List.range 8).flatMap paddingRound

/-- A padding pass is its rounds, then the pointer updates. -/
theorem paddingBlock_eq : paddingBlock = padLanes ++ [.addImm consts 512, .subImm blocks 1] := rfl

/-- The padding rounds read only table rows, and act on each lane alone. -/
theorem padLanes_ops : padLanes.all loopOps = true ∧ padLanes.all rowwise = true := by
  -- Checked by evaluation.
  decide +kernel

/-- Whether an instruction is not a store. -/
def noStore : Instr → Bool
  | .vstoreHalf .. => false
  | _ => true

/-- The padding rounds store nothing. -/
theorem padLanes_stores (G : Gpr → UInt64) : storesOf G padLanes = [] := by
  -- No instruction of a round is a store, as evaluation checks.
  have h : padLanes.all noStore = true := by decide +kernel
  simp only [storesOf, List.filterMap_eq_nil_iff]
  intro i hi
  have := List.all_eq_true.mp h i hi
  cases i <;> simp_all [noStore, storeOf]

/-- The padding invariant reads only the working words and the stored state. -/
theorem PadInv.congr {S : Nat} {mid : Vector UInt32 8} {t : Nat} {v w : View} (inv : PadInv S mid t v)
    (regs : ∀ r, w.regs r = v.regs r) (mem : ∀ j < 8, w.mem (S + midSlot j) = v.mem (S + midSlot j)) :
    PadInv S mid t w := by
  obtain ⟨roles, mids⟩ := inv
  refine ⟨?_, fun j hj => (mem j hj).trans (mids j hj)⟩
  rw [← roles]; simp only [regs]

/-- Lane l's state after the first block. -/
def middle (s : State) (ls rs l : Nat) : Vector UInt32 8 := compress Cryptography.Hash.Sha256.IV (msg s ls rs l) 0

/-- One pass of the padding loop: every lane's invariant eight rounds on, and the pointer and count updated. -/
theorem padBlock_spec (ls rs : Nat) (s : State) (ctx : Ctx ls rs s) (i : Nat) (hi : i < 8) (x : State)
    (constsAt : (x.gpr consts).toNat = tableAt s + 4096 + 512 * i)
    (inv : ∀ l : Fin 8, PadInv (scratch s) (middle s ls rs l.val) (8 * i) (view x l))
    (outside : ∀ a, Outside (scratch s) a → x.mem a = s.mem a) :
    let y := exec paddingBlock x
    (∀ l : Fin 8, PadInv (scratch s) (middle s ls rs l.val) (8 * i + 8) (view y l)) ∧ y.mem = x.mem ∧
    y.gpr = assign (assign x.gpr consts (x.gpr consts + (512 : Nat).toUInt64)) blocks (x.gpr blocks - (1 : Nat).toUInt64) ∧
    y.zf = (x.gpr blocks - (1 : Nat).toUInt64 == 0) := by
  intro y
  have table : TableAt x.mem (tableAt s) := table_kept _ _ _ _ ctx.table ctx.tableApart outside
  obtain ⟨v, m, f, g, -, -⟩ := exec_view padLanes (List.all_eq_true.mp padLanes_ops.2) x
    (by rw [padLanes_stores]; intro a _ A hA; simp at hA)
  let x' := exec padLanes x
  have whole : y = exec [.addImm consts 512, .subImm blocks 1] x' := by
    simp only [y, x', paddingBlock_eq, exec_append]
  have xmem : x'.mem = x.mem := funext fun a => f a (by rw [padLanes_stores]; simp)
  have ymem : y.mem = x'.mem := by rw [whole]; simp [exec, exec1]
  have yvec : y.vec = x'.vec := by rw [whole]; simp [exec, exec1]
  have xg : x'.gpr = x.gpr := g
  have xv : ∀ r l, x'.vec r (lane l) = (viewRun x.gpr padLanes (view x l)).regs r := v
  have xm : ∀ (l : Fin 8) a, Clear (storesOf x.gpr padLanes) a →
      readWord x'.mem (a + 4 * l.val) = (viewRun x.gpr padLanes (view x l)).mem a := m
  clear_value y x'
  refine ⟨fun l => ?_, ymem.trans xmem, ?_, ?_⟩
  · -- Each lane runs its eight rounds, reading the table's precomputed words and constants.
    have konst : ∀ k < 8, (view x l).mem ((x.gpr consts).toNat + 64 * k) =
        Avx512.K (8 * i + k) + Avx512.PW (8 * i + k) := fun k hk => by
      simp only [view]
      rw [constsAt, show tableAt s + 4096 + 512 * i + 64 * k = tableAt s + 64 * (64 + (8 * i + k)) by omega,
        view_row _ _ table _ (by omega), Avx512.tableWord_pad _ _ (by omega) (by omega)]
    obtain ⟨next, -⟩ := pad_block x.gpr (view x l) (scratch s) (middle s ls rs l.val) i konst (inv l)
    rw [show (List.range 8).flatMap paddingRound = padLanes from rfl] at next
    refine next.congr (fun r => ?_) (fun j _ => ?_)
    · exact (congrFun (congrFun yvec r) (lane l)).trans (xv r l)
    · have clear : Clear (storesOf x.gpr padLanes) (scratch s + midSlot j) := by
        rw [padLanes_stores]; intro A hA; simp at hA
      have hm : readWord x'.mem (scratch s + midSlot j + 4 * l.val) =
          (viewRun x.gpr padLanes (view x l)).mem (scratch s + midSlot j) := xm l _ clear
      exact (congrArg (fun mm => readWord mm (scratch s + midSlot j + 4 * l.val)) ymem).trans hm
  · rw [whole]; simp only [exec, exec1, xg]; rfl
  · rw [whole]; simp only [exec, exec1, xg]; simp [assign]

/-- The feed-forward of working word j: add the initial state's word, and store the sum. -/
def feedStep (j : Nat) : List Instr :=
  [.yaddMem (home j) (home j) (tableEntry (ivAvx512 j)), .vstoreHalf ⟨sp, midSlot j⟩ (home j)]

/-- The feed-forward is its eight steps. -/
theorem feedCode_eq : feedCode = (List.range 8).flatMap feedStep := rfl

/-- The working-word registers are distinct. -/
theorem home_inj (j k : Nat) (hj : j < 8) (hk : k < 8) (e : home j = home k) : j = k := by
  simp only [home, Fin.ext_iff] at e; omega

/-- The feed-forward, lane by lane: each working word gains its initial-state word, and the sum is stored. -/
theorem feed_view (G : Gpr → UInt64) (v : View) (S T : Nat) (hS : (G sp).toNat = S) (hT : (G tbl).toNat = T)
    (far : ∀ j < 8, ∀ k < 8, T + ivAvx512 k ≠ S + midSlot j) (n : Nat) (hn : n ≤ 8) :
    let w := viewRun G ((List.range n).flatMap feedStep) v
    (∀ j < n, w.regs (home j) = v.regs (home j) + v.mem (T + ivAvx512 j) ∧
      w.mem (S + midSlot j) = v.regs (home j) + v.mem (T + ivAvx512 j)) ∧
    (∀ j, n ≤ j → j < 8 → w.regs (home j) = v.regs (home j)) ∧ (∀ k < 8, w.mem (T + ivAvx512 k) = v.mem (T + ivAvx512 k)) := by
  intro w
  induction n with
  | zero => exact ⟨fun _ h => absurd h (by omega), fun _ _ _ => rfl, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨done, rest, ivs⟩ := ih (by omega)
    simp only [w]
    rw [viewRun_flatMap_succ]
    generalize viewRun G ((List.range n).flatMap feedStep) v = u at done rest ivs
    -- Step n reads the initial state's row, which no store has touched, and writes its own register and row.
    simp only [feedStep, viewRun, viewStep, addrOf, tableEntry, hS, hT, assign_apply]
    refine ⟨fun j hj => ?_, fun j hj hj8 => ?_, fun k hk => ?_⟩
    · by_cases last : j = n
      · subst last
        rw [ivs j (by omega), rest j (by omega) (by omega)]
        simp
      · have ne : home j ≠ home n := fun e => last (home_inj j n (by omega) (by omega) e)
        have ne' : S + midSlot j ≠ S + midSlot n := by simp only [midSlot]; omega
        simp only [ne, ne', ite_false]
        exact done j (by omega)
    · have ne : home j ≠ home n := fun e => by have := home_inj j n hj8 (by omega) e; omega
      simp only [ne, ite_false]
      exact rest j (by omega) hj8
    · rw [ite_eq_right (far n (by omega) k hk)]
      exact ivs k hk

/-- The stored-state rows share the 32-byte grid. -/
theorem midSlot_clear (S j j' : Nat) : (S + midSlot j) % 32 = (S + midSlot j') % 32 := by
  simp only [midSlot]; omega

/-- Whether an instruction of the feed-forward reads an initial-state row and stores a stored-state row. -/
def feedOps : Instr → Bool
  | .yaddMem _ _ m => m.base == tbl && 8192 ≤ m.disp && m.disp + 32 ≤ 8704
  | .vstoreHalf m _ => m.base == sp && m.disp % 32 == 0 && m.disp + 32 ≤ 256
  | .vloadHalf _ _ => false
  | _ => true

/-- The feed-forward reads only the table's initial-state rows and stores only the stored-state rows. -/
theorem feedCode_ops : feedCode.all feedOps = true ∧ feedCode.all rowwise = true := by
  -- Checked by evaluation.
  decide +kernel

/-- In the feed-forward, every read is a table row, apart from every store in the scratch area. -/
theorem feed_clear (G : Gpr → UInt64) (S T : Nat) (hS : (G sp).toNat = S) (hT : (G tbl).toNat = T)
    (apart : Apart (S, frame) (T, tableSize)) : ∀ a ∈ readsOf G feedCode, Clear (storesOf G feedCode) a := by
  intro a ha A hA
  simp only [readsOf, storesOf, List.mem_filterMap] at ha hA
  obtain ⟨i, hi, hr⟩ := ha
  obtain ⟨i', hi', hr'⟩ := hA
  have ok := List.all_eq_true.mp feedCode_ops.1 i hi
  have ok' := List.all_eq_true.mp feedCode_ops.1 i' hi'
  simp only [Apart] at apart
  -- The read is a table row and the store a scratch row, so neither overlaps the other.
  cases i <;> simp only [readOf, reduceCtorEq] at hr <;> simp only [feedOps, reduceCtorEq] at ok <;>
    cases i' <;> simp only [storeOf, reduceCtorEq] at hr' <;> simp only [feedOps] at ok'
  all_goals
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok ok'
    simp only [Option.some.injEq, addrOf] at hr hr'
    obtain ⟨⟨b, l1⟩, l2⟩ := ok
    obtain ⟨⟨b', l3⟩, l4⟩ := ok'
    rw [b] at hr
    rw [b'] at hr'
    subst hr hr'
    right
    simp only [frame, tableSize] at apart
    omega

/-- The stored-state rows sit apart from the table's initial-state rows. -/
theorem iv_far (S T : Nat) (apart : Apart (S, frame) (T, tableSize)) :
    ∀ j < 8, ∀ k < 8, T + ivAvx512 k ≠ S + midSlot j := by
  intro j hj k hk
  simp only [Apart, frame, tableSize] at apart
  simp only [ivAvx512, midSlot]; omega

/-- Lane l of the first block's result. -/
theorem middle_get (s : State) (ls rs l : Nat) (v : View)
    (roles : (Vector.ofFn fun j : Fin 8 => v.regs (role 64 j)) =
      Avx512.roundsTo Cryptography.Hash.Sha256.IV Avx512.K (Avx512.W (msg s ls rs l)) 64) (j : Nat) (hj : j < 8) :
    (middle s ls rs l)[j] = v.regs (home j) + Cryptography.Hash.Sha256.IV[j]! := by
  -- The first compression is the initial state plus the working words after sixty-four rounds.
  have := congrArg (·[j]) roles
  simp only [Vector.getElem_ofFn] at this
  rw [middle, Avx512.compress_rounds, Vector.getElem_zipWith, ← this,
    show role 64 j = home j by apply Fin.ext; simp only [role, home]; omega, getElem!_pos Cryptography.Hash.Sha256.IV j hj,
    UInt32.add_comm]

/-- Setting a general register leaves memory and the vector registers alone. -/
theorem movImm_frame {r : Gpr} {v : UInt64} {x : State} :
    (exec [.movImm r v] x).mem = x.mem ∧ (exec [.movImm r v] x).vec = x.vec := ⟨rfl, rfl⟩

/-- Between the second and third loops: every lane's padding invariant holds, with the first block's result stored. -/
theorem middle_spec (ls rs : Nat) (s : State) (ctx : Ctx ls rs s) (x : State)
    (spAt : x.gpr sp = s.gpr sp) (tblAt : x.gpr tbl = s.gpr tbl)
    (inv : ∀ l : Fin 8, FirstInv (scratch s) (msg s ls rs l.val) 64 (view x l))
    (outside : ∀ a, Outside (scratch s) a → x.mem a = s.mem a) :
    let y := exec middleCode x
    (∀ l : Fin 8, PadInv (scratch s) (middle s ls rs l.val) 0 (view y l)) ∧
    (∀ a, Outside (scratch s) a → y.mem a = s.mem a) ∧ y.gpr = assign x.gpr blocks 8 := by
  intro y
  have apart := ctx.tableApart
  have table : TableAt x.mem (tableAt s) := table_kept _ _ _ _ ctx.table apart outside
  have hS : (x.gpr sp).toNat = scratch s := by rw [spAt]
  have hT : (x.gpr tbl).toNat = tableAt s := by rw [tblAt]
  obtain ⟨v, m, f, g, -, -⟩ := exec_view feedCode (List.all_eq_true.mp feedCode_ops.2) x
    (feed_clear x.gpr _ _ hS hT apart)
  -- The feed-forward's result, kept opaque so that no check unfolds its sixteen instructions.
  have whole : y = exec [.movImm blocks 8] (exec feedCode x) := by simp only [y, middleCode, exec_append]
  clear_value y
  generalize exec feedCode x = x' at v m f g whole
  have ymem : y.mem = x'.mem := by rw [whole]; exact movImm_frame.1
  have yvec : y.vec = x'.vec := by rw [whole]; exact movImm_frame.2
  have xv : ∀ r l, x'.vec r (lane l) = (viewRun x.gpr feedCode (view x l)).regs r := v
  have xm : ∀ (l : Fin 8) a, Clear (storesOf x.gpr feedCode) a →
      readWord x'.mem (a + 4 * l.val) = (viewRun x.gpr feedCode (view x l)).mem a := m
  have xf : ∀ a, (∀ A ∈ storesOf x.gpr feedCode, a < A ∨ A + 32 ≤ a) → x'.mem a = x.mem a := f
  have xg : x'.gpr = x.gpr := g
  -- Every store of the feed-forward is a stored-state row of the scratch area.
  have storeAt : ∀ A ∈ storesOf x.gpr feedCode, ∃ j < 8, A = scratch s + midSlot j := by
    intro A hA
    simp only [storesOf, List.mem_filterMap] at hA
    obtain ⟨i, hi, hr⟩ := hA
    have ok := List.all_eq_true.mp feedCode_ops.1 i hi
    cases i <;> simp only [storeOf, reduceCtorEq] at hr
    rename_i mm _
    simp only [feedOps, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
    simp only [Option.some.injEq, addrOf] at hr
    obtain ⟨⟨b, l1⟩, l2⟩ := ok
    rw [b, hS] at hr
    exact ⟨mm.disp / 32, by omega, by simp only [midSlot]; omega⟩
  refine ⟨fun l => ?_, fun a ha => ?_, ?_⟩
  · obtain ⟨roles, -⟩ := inv l
    obtain ⟨fed, -, -⟩ := feed_view x.gpr (view x l) (scratch s) (tableAt s) hS hT (iv_far _ _ apart) 8 (Nat.le_refl _)
    rw [← feedCode_eq] at fed
    have ivRow : ∀ j < 8, (view x l).mem (tableAt s + ivAvx512 j) = Cryptography.Hash.Sha256.IV[j]! := fun j hj => by
      simp only [view, ivAvx512]
      rw [show tableAt s + (8192 + 64 * j) + 4 * l.val = tableAt s + 64 * (128 + j) + 4 * l.val by omega,
        view_row _ _ table _ (by omega), Avx512.tableWord_iv j l.val hj (by omega)]
    refine ⟨?_, fun j hj => ?_⟩
    · -- The working words start the padding block as the first block's result.
      apply Vector.ext
      intro j hj
      simp only [Vector.getElem_ofFn, Avx512.roundsTo, List.range_zero, List.foldl_nil]
      rw [show role 0 j = home j by apply Fin.ext; simp only [role, home]; omega]
      show y.vec (home j) (lane l) = _
      rw [yvec, xv, (fed j hj).1, ivRow j hj, middle_get s ls rs l.val (view x l) roles j hj]
    · -- The stored state is the same sum.
      show readWord y.mem (scratch s + midSlot j + 4 * l.val) = _
      rw [ymem, xm l _ (fun A hA => by obtain ⟨j', _, rfl⟩ := storeAt A hA; left; exact midSlot_clear _ _ _),
        (fed j hj).2, ivRow j hj, getElem!_pos (middle s ls rs l.val) j hj,
        middle_get s ls rs l.val (view x l) roles j hj]
  · rw [ymem, xf a fun A hA => by
      obtain ⟨j, hj, rfl⟩ := storeAt A hA
      simp only [Outside, midSlot, frame] at ha ⊢; omega]
    exact outside a ha
  · rw [whole]; simp only [exec, exec1, xg]

/-- The second feed-forward, lane by lane: each working word gains the stored state's word. -/
theorem finish_view (G : Gpr → UInt64) (v : View) (j : Nat) (hj : j < 8) :
    (viewRun G finishCode v).regs (home j) = v.regs (home j) + v.mem ((G sp).toNat + midSlot j) := by
  -- Each of the eight additions writes its own register.
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [finishCode, List.range, List.range.loop, List.map, viewRun, viewStep, assign_apply, home, addrOf] <;>
    simp

/-- The second feed-forward stores nothing, and acts on each lane alone. -/
theorem finishCode_ops : finishCode.all noStore = true ∧ finishCode.all rowwise = true := by
  -- Checked by evaluation.
  decide +kernel

/-- The second feed-forward stores nothing. -/
theorem finish_stores (G : Gpr → UInt64) : storesOf G finishCode = [] := by
  simp only [storesOf, List.filterMap_eq_nil_iff]
  intro i hi
  have := List.all_eq_true.mp finishCode_ops.1 i hi
  -- An instruction that is not a store stores nothing.
  cases i <;> simp_all [noStore, storeOf]

/-- A pair's message is 64 bytes. -/
theorem msg_size (s : State) (ls rs l : Nat) : (msg s ls rs l).size = 64 := by
  -- The message is built from 64 bytes.
  simp [msg, pairMessage, ByteArray.size]

/--
The output: every pair's digest, 32 bytes per pair from the output address, and nothing else written.

Each lane's state is the second compression, so its digest is the hash of the lane's pair.
-/
theorem output_full (ls rs : Nat) (s : State) (ctx : Ctx ls rs s) (x : State)
    (spAt : x.gpr sp = s.gpr sp) (tblAt : x.gpr tbl = s.gpr tbl)
    (inv : ∀ l : Fin 8, PadInv (scratch s) (middle s ls rs l.val) 64 (view x l))
    (outside : ∀ a, Outside (scratch s) a → x.mem a = s.mem a) :
    let y := exec outputCode x
    (∀ p < 8, ∀ k < 32, y.mem ((x.gpr out).toNat + 32 * p + k) = (Cryptography.Hash.Sha256.hash (msg s ls rs p)).get! k) ∧
    (∀ a, ¬ ((x.gpr out).toNat ≤ a ∧ a < (x.gpr out).toNat + 256) → y.mem a = x.mem a) ∧ y.gpr = x.gpr := by
  intro y
  have table : TableAt x.mem (tableAt s) := table_kept _ _ _ _ ctx.table ctx.tableApart outside
  obtain ⟨v, -, f, g, -, -⟩ := exec_view finishCode (List.all_eq_true.mp finishCode_ops.2) x
    (by rw [finish_stores]; intro a _ A hA; simp at hA)
  have whole : y = exec (outMoves ++ outStores) (exec finishCode x) := by
    simp only [y, outputCode_eq, exec_append, List.append_assoc]
  clear_value y
  generalize exec finishCode x = x1 at v f g whole
  have m1 : x1.mem = x.mem := funext fun a => f a (by rw [finish_stores]; simp)
  obtain ⟨digests, rest, g2, -, -⟩ := output_spec x1 (by rw [m1, g, tblAt]; exact table)
  rw [← whole, g] at digests rest
  refine ⟨fun p hp k hk => ?_, fun a ha => (rest a ha).trans (congrFun m1 a), by rw [whole]; exact g2.trans g⟩
  rw [digests p hp k hk, hash_pair _ (msg_size _ _ _ _)]
  congr 2
  -- Each lane's state is the second compression of its pair.
  apply Vector.ext
  intro j hj
  obtain ⟨roles, mids⟩ := inv ⟨p, hp⟩
  have := congrArg (·[j]) roles
  simp only [Vector.getElem_ofFn] at this
  rw [Vector.getElem_ofFn, show (⟨p, by omega⟩ : Fin 16) = lane ⟨p, hp⟩ from rfl, v, finish_view _ _ j hj,
    show role 64 j = home j by apply Fin.ext; simp only [role, home]; omega] at *
  rw [this, spAt, mids j hj, Avx512.compress_rounds, Vector.getElem_zipWith, getElem!_pos _ j hj, UInt32.add_comm]
  rfl

end EthLib.Consensus.Ssz.Native.Kernel.Avx2
