import SszNative.Proofs.Kernel.Avx512x2.Batch

/-!
One batch pair of the thirty-two-lane kernel on the machine: the setup, the three loops, and the output, in order.
-/

namespace EthLib.Consensus.Ssz.Native.Kernel.Avx512x2

open EthLib.Cryptography.Hash.Sha256 hiding K IV
open EthLib.Consensus.Ssz.Native.Asm
open EthLib.Consensus.Ssz.Native.Kernel.Avx512 (tbl left right out count home transposeOut storeCode add_toNat roundsTo K W PW
  home_eq_role home_eq_role64 compress_rounds pairMessage_size)

/-- Memory and registers before a batch pair, as the whole pair needs them. -/
structure BatchPre (ls rs : Nat) (s : State) : Prop extends SetupPre ls rs s where
  /-- The digests miss the scratch area. -/
  outApart : Apart ((s.gpr out).toNat, 1024) ((s.gpr sp).toNat, frame)
  /-- The digests miss the table. -/
  outTable : Apart ((s.gpr out).toNat, 1024) ((s.gpr tbl).toNat, tableSize)
  /-- The digests end within reach. -/
  outBound : (s.gpr out).toNat + 1024 ≤ addressBound
  /-- The table ends within reach. -/
  tableBound : (s.gpr tbl).toNat + tableSize ≤ addressBound

/-- A finished batch pair: at the pointer updates, its thirty-two digests written, and nothing else off the scratch area touched. -/
def PairDone (ls rs : Nat) (s y : State) : Prop :=
  y.status = .running ∧ y.pc = loopHead + (body ls rs).length ∧
  (∀ p < 32, ∀ k < 32, y.mem ((s.gpr out).toNat + 32 * p + k) =
    (Cryptography.Hash.Sha256.hash (pairMessage s.mem ((s.gpr left).toNat + ls * p) ((s.gpr right).toNat + rs * p))).get! k) ∧
  (∀ a, ¬ ((s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 1024) →
    a < (s.gpr sp).toNat ∨ (s.gpr sp).toNat + frame ≤ a → y.mem a = s.mem a) ∧
  y.gpr left = s.gpr left + (16 * ls).toUInt64 ∧ y.gpr right = s.gpr right + (16 * rs).toUInt64 ∧
  y.gpr out = s.gpr out + (512 : Nat).toUInt64 ∧
  (∀ r, r ≠ left → r ≠ right → r ≠ out → r ≠ words → r ≠ consts → r ≠ blocks → y.gpr r = s.gpr r)

/-- The setup never branches. -/
theorem setup_straight (ls rs : Nat) : ∀ i ∈ setupCode ls rs, i.straight := by
  rw [← List.all_eq_true]
  simp [setupCode, loadStore, Avx512.loadCode, Avx512.transposeIn, Avx512.swapIn, ivCode, forBatch, rename,
    Instr.straight]

/-- The blocks between the branches never branch. -/
theorem blocks_straight : (firstBlock true).all Instr.straight = true ∧ (firstBlock false).all Instr.straight = true ∧
    middleCode.all Instr.straight = true ∧ paddingBlock.all Instr.straight = true ∧
    outputCode.all Instr.straight = true := by
  -- Every instruction, checked by evaluation.
  decide +kernel

/-- A state with only its instruction index changed has the same lanes. -/
theorem view_pc (x : State) (pc : Nat) (l : Fin 16) : view { x with pc := pc } l = view x l := rfl

/-- The first-block loop invariant ignores the instruction index. -/
theorem firstLoop_pc {S T : Nat} {m : Fin 16 → Nat → ByteArray} {G0 : Gpr → UInt64} {M0 : Nat → UInt8}
    {i0 n i : Nat} {x : State} (pc : Nat) (h : FirstLoop S T m G0 M0 i0 n i x) :
    FirstLoop S T m G0 M0 i0 n i { x with pc := pc } :=
  ⟨h.wordsAt, h.constsAt, h.blocksLeft, h.others, h.lanes, h.kept⟩

/-- The padding loop invariant ignores the instruction index. -/
theorem padLoop_pc {S T : Nat} {mid : Fin 16 → Nat → Vector UInt32 8} {G0 : Gpr → UInt64} {M0 : Nat → UInt8}
    {i : Nat} {x : State} (pc : Nat) (h : PadLoop S T mid G0 M0 i x) : PadLoop S T mid G0 M0 i { x with pc := pc } :=
  ⟨h.constsAt, h.blocksLeft, h.others, h.lanes, h.mids, h.kept⟩

/-- A compression, word by word: the state plus the working words after sixty-four rounds. -/
theorem compress_get (st : Vector UInt32 8) (b : ByteArray) (j : Nat) (hj : j < 8) :
    (compress st b 0)[j]! = st[j]! + (roundsTo st K (fun i => (schedule b 0)[i]!) 64)[j]! := by
  rw [compress_rounds, getElem!_pos _ j hj, Vector.getElem_zipWith, getElem!_pos st j hj, getElem!_pos _ j hj]


/-- The instructions before the first loop. -/
def pre2 (ls rs : Nat) : List Instr := opening ls rs ++ setupCode ls rs

/-- The instructions before the second loop. -/
def pre4 (ls rs : Nat) : List Instr :=
  pre2 ls rs ++ firstBlock true ++ [.jnz (pre2 ls rs).length, .movImm blocks 2]

/-- The instructions before the third loop. -/
def pre6 (ls rs : Nat) : List Instr :=
  pre4 ls rs ++ firstBlock false ++ [.jnz (pre4 ls rs).length] ++ middleCode

/-- The instructions after the third loop. -/
def post6 (ls rs : Nat) : List Instr := outputCode ++ tailCode ls rs ++ closingCode

/-- The instructions after the first feed-forwards. -/
def post5 (ls rs : Nat) : List Instr := paddingBlock ++ .jnz (pre6 ls rs).length :: post6 ls rs

/-- The instructions after the second loop's count. -/
def post3 (ls rs : Nat) : List Instr := firstBlock false ++ .jnz (pre4 ls rs).length :: (middleCode ++ post5 ls rs)

/-- The routine's instructions, the jump targets written as lengths of what precedes them. -/
theorem program_parts (ls rs : Nat) :
    (program ls rs).toList = pre2 ls rs ++ firstBlock true ++ .jnz (pre2 ls rs).length :: .movImm blocks 2 ::
      post3 ls rs := by
  have e1 : firstHead ls rs = (pre2 ls rs).length := by
    simp only [firstHead, pre2, List.length_append, opening_length]
  have e2 : secondHead ls rs = (pre4 ls rs).length := by
    simp only [secondHead, firstHead, pre4, pre2, List.length_append, opening_length, List.length_cons,
      List.length_nil]
  have e3 : thirdHead ls rs = (pre6 ls rs).length := by
    simp only [thirdHead, secondHead, firstHead, pre6, pre4, pre2, List.length_append, opening_length,
      List.length_cons, List.length_nil]
  rw [program_toList, body_eq, e1, e2, e3]
  simp only [pre2, post3, post5, post6, List.append_assoc, List.cons_append, List.nil_append]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- One batch pair, from the loop head: thirty-two digests written, and the pointers ready for the updates. -/
theorem pair_run (ls rs : Nat) (s : State) (hpc : s.pc = loopHead) (running : s.status = .running)
    (pre : BatchPre ls rs s) : ∃ n, PairDone ls rs s (run (program ls rs) n s) := by
  obtain ⟨S, hS⟩ : ∃ S, (s.gpr sp).toNat = S := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, (s.gpr tbl).toNat = T := ⟨_, rfl⟩
  obtain ⟨O, hO⟩ : ∃ O, (s.gpr out).toNat = O := ⟨_, rfl⟩
  have apart : FrameApart S T := by rw [← hS, ← hT]; exact pre.apart
  have tBound : T + tableSize ≤ addressBound := by rw [← hT]; exact pre.tableBound
  have table : TableAt s.mem T := by rw [← hT]; exact pre.table
  have outApart : Apart (O, 1024) (S, frame) := by rw [← hS, ← hO]; exact pre.outApart
  have outTable : Apart (O, 1024) (T, tableSize) := by rw [← hT, ← hO]; exact pre.outTable
  have outBound : O + 1024 ≤ addressBound := by rw [← hO]; exact pre.outBound
  let m : Fin 16 → Nat → ByteArray := msg s.mem (s.gpr left).toNat (s.gpr right).toNat ls rs
  let mid : Fin 16 → Nat → Vector UInt32 8 := fun l b => compress Cryptography.Hash.Sha256.IV (m l b) 0
  obtain ⟨b1, b2, b3, b4, b5⟩ := blocks_straight
  -- The setup.
  obtain ⟨lanes1, kept1, left1, right1, words1, consts1, blocks1, others1⟩ := setup_spec ls rs s pre.toSetupPre
  simp only [hS, hT] at lanes1 kept1 words1 consts1
  have run1 := run_block (program ls rs) (opening ls rs) (setupCode ls rs)
    (firstBlock true ++ .jnz (pre2 ls rs).length :: .movImm blocks 2 :: post3 ls rs)
    (by rw [program_parts]; simp only [pre2, List.append_assoc]) (setup_straight ls rs) s (by rw [hpc]; rfl) running
  generalize hx1 : exec (setupCode ls rs) s = x1 at lanes1 kept1 left1 right1 words1 consts1 blocks1 others1 run1
  have sp1 : (x1.gpr sp).toNat = S := by rw [others1 _ (by decide) (by decide) (by decide) (by decide) (by decide), hS]
  have stat1 : x1.status = .running := by rw [← hx1, exec_status, running]
  -- The first loop: six blocks of rounds with schedule steps.
  have L2 : (program ls rs).toList = pre2 ls rs ++ firstBlock true ++
      .jnz (pre2 ls rs).length :: (.movImm blocks 2 :: post3 ls rs) := program_parts ls rs
  have step1 : ∀ i < 6, ∀ x, FirstLoop S T m x1.gpr s.mem 0 6 i x →
      FirstLoop S T m x1.gpr s.mem 0 6 (i + 1) (exec (firstBlock true) x) ∧
      ((exec (firstBlock true) x).zf = true ↔ i + 1 = 6) :=
    firstLoop_step S T m x1.gpr s.mem 0 6 true (by omega) (fun i hi => by simp <;> omega) sp1 apart tBound
  have pc1 : ({ x1 with pc := (opening ls rs).length + (setupCode ls rs).length } : State).pc = (pre2 ls rs).length := by
    simp only [pre2, List.length_append]
  have inv0 : FirstLoop S T m x1.gpr s.mem 0 6 0 { x1 with pc := (opening ls rs).length + (setupCode ls rs).length } :=
    firstLoop_pc _ ⟨fun _ => words1, by rw [consts1]; rfl, by rw [blocks1]; rfl, fun _ _ _ _ => rfl, lanes1, kept1⟩
  obtain ⟨y1, inv1, sty1, pcy1, run2⟩ := loop_run (program ls rs) (pre2 ls rs) (firstBlock true)
    (.movImm blocks 2 :: post3 ls rs) L2 (List.all_eq_true.mp b1)
    (fun i x => FirstLoop S T m x1.gpr s.mem 0 6 i x) 6 (by decide) (fun i hi x _ _ h => step1 i hi x h)
    { x1 with pc := (opening ls rs).length + (setupCode ls rs).length } pc1 stat1 inv0
  -- The second loop's count.
  have run3 := run_block (program ls rs) (pre2 ls rs ++ firstBlock true ++ [.jnz (pre2 ls rs).length])
    [.movImm blocks 2] (post3 ls rs)
    (by rw [program_parts]; simp only [List.append_assoc, List.cons_append, List.nil_append])
    (by simp [Instr.straight]) { y1 with pc := (pre2 ls rs).length + (firstBlock true).length + 1 }
    (by simp only [List.length_append, List.length_cons, List.length_nil]) sty1
  rw [exec_with_pc] at run3
  have g2 : (exec [.movImm blocks 2] y1).gpr = assign y1.gpr blocks 2 := by simp [exec, exec1]
  have vm2 : (exec [.movImm blocks 2] y1).vec = y1.vec ∧ (exec [.movImm blocks 2] y1).mem = y1.mem := by
    simp [exec, exec1]
  have st2 : (exec [.movImm blocks 2] y1).status = .running := by rw [exec_status, sty1]
  generalize hx2 : exec [.movImm blocks 2] y1 = x2 at run3 g2 vm2 st2
  -- The second loop: two blocks of rounds without schedule steps.
  have L4 : (program ls rs).toList = pre4 ls rs ++ firstBlock false ++
      .jnz (pre4 ls rs).length :: (middleCode ++ post5 ls rs) := by
    rw [program_parts]; simp only [pre4, post3, List.append_assoc, List.cons_append, List.nil_append]
  have step2 : ∀ i < 2, ∀ x, FirstLoop S T m x1.gpr s.mem 6 2 i x →
      FirstLoop S T m x1.gpr s.mem 6 2 (i + 1) (exec (firstBlock false) x) ∧
      ((exec (firstBlock false) x).zf = true ↔ i + 1 = 2) :=
    firstLoop_step S T m x1.gpr s.mem 6 2 false (by omega) (fun i hi => by simp <;> omega) sp1 apart tBound
  have pc2 : ({ x2 with pc := (pre2 ls rs ++ firstBlock true ++ [Instr.jnz (pre2 ls rs).length]).length +
      [Instr.movImm blocks 2].length } : State).pc = (pre4 ls rs).length := by
    simp only [pre4, List.length_append, List.length_cons, List.length_nil]
  have inv20 : FirstLoop S T m x1.gpr s.mem 6 2 0 x2 :=
    ⟨fun _ => by rw [g2]; exact inv1.wordsAt (by omega), by rw [g2]; exact inv1.constsAt, by rw [g2]; rfl,
      fun r h1 h2 h3 => by rw [g2]; simp only [assign, ite_eq_right h3]; exact inv1.others r h1 h2 h3,
      fun l => by simp only [view, vm2.1, vm2.2]; exact inv1.lanes l,
      fun a ha => by rw [vm2.2]; exact inv1.kept a ha⟩
  obtain ⟨y2, inv2, sty2, pcy2, run4⟩ := loop_run (program ls rs) (pre4 ls rs) (firstBlock false)
    (middleCode ++ post5 ls rs) L4 (List.all_eq_true.mp b2)
    (fun i x => FirstLoop S T m x1.gpr s.mem 6 2 i x) 2 (by decide) (fun i hi x _ _ h => step2 i hi x h)
    _ pc2 st2 (firstLoop_pc _ inv20)
  have sp2 : (y2.gpr sp).toNat = S := by
    rw [inv2.others _ (by decide) (by decide) (by decide), sp1]
  have tbl2 : (y2.gpr tbl).toNat = T := by
    rw [inv2.others _ (by decide) (by decide) (by decide), others1 _ (by decide) (by decide) (by decide) (by decide)
      (by decide), hT]
  -- The first feed-forwards.
  have run5 := run_block (program ls rs) (pre4 ls rs ++ firstBlock false ++ [.jnz (pre4 ls rs).length]) middleCode
    (post5 ls rs) (by rw [program_parts]; simp only [pre4, post3, List.append_assoc, List.cons_append,
      List.nil_append])
    (List.all_eq_true.mp b3) { y2 with pc := (pre4 ls rs).length + (firstBlock false).length + 1 }
    (by simp only [List.length_append, List.length_cons, List.length_nil]) sty2
  rw [exec_with_pc] at run5
  obtain ⟨v5, r5, k5, g5, -, -⟩ := exec_rows (feedCode 0 ++ feedCode 1) sp tbl (frame - 64) tableSize feedCode_shape
    y2 S T 0 0 (by rw [sp2]; rfl) rfl (by simp [frame]) (by rw [tbl2]; rfl) (by simp [tableSize]) apart
  have hmid : exec middleCode y2 = exec [.movImm blocks 8] (exec (feedCode 0 ++ feedCode 1) y2) := by
    simp only [middleCode, exec_append, List.append_assoc]
  have g5' : (exec middleCode y2).gpr = assign y2.gpr blocks 8 := by
    rw [hmid]; simp [exec, exec1, g5]
  have vm5 : (exec middleCode y2).vec = (exec (feedCode 0 ++ feedCode 1) y2).vec ∧
      (exec middleCode y2).mem = (exec (feedCode 0 ++ feedCode 1) y2).mem := by
    rw [hmid]; simp [exec, exec1]
  have st5 : (exec middleCode y2).status = .running := by rw [exec_status, sty2]
  -- Each lane: the first compressions, and their copies kept.
  have firstWords : ∀ l, ∀ b < 2, ∀ j < 8,
      y2.vec (if b = 0 then home j else swapReg (home j)) l + Cryptography.Hash.Sha256.IV[j]! = (mid l b)[j]! := by
    intro l b hb j hj
    obtain ⟨rolesA, rolesB, -, -⟩ := inv2.lanes l
    have rA := congrArg (·[j]) rolesA
    have rB := congrArg (·[j]) rolesB
    simp only [Vector.getElem_ofFn] at rA rB
    rw [← home_eq_role64 j hj] at rA rB
    simp only [mid]
    rw [compress_get _ _ j hj, UInt32.add_comm]
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
    · simp only [ite_true]
      rw [getElem!_pos (roundsTo Cryptography.Hash.Sha256.IV K (fun i => (schedule (m l 0) 0)[i]!) 64) j hj]
      exact congrArg _ rA
    · simp only [show ¬ (1 = 0) from by decide, ite_false]
      rw [getElem!_pos (roundsTo Cryptography.Hash.Sha256.IV K (fun i => (schedule (m l 1) 0)[i]!) 64) j hj]
      exact congrArg _ rB
  have pad0 : PadLoop S T mid y2.gpr s.mem 0 (exec middleCode y2) := by
    refine ⟨by rw [g5']; simp only [assign]; exact inv2.constsAt, by rw [g5']; rfl,
      fun r h1 h2 => by rw [g5']; simp only [assign, ite_eq_right h2], fun l => ?_, fun l b hb j hj => ?_,
      fun a ha => by rw [vm5.2, k5 a ha, inv2.kept a ha]⟩
    · have rows := (inv2.lanes l).2.2.2
      refine ⟨?_, ?_, fun row hrow => ?_⟩
      · apply Vector.ext; intro j hj
        simp only [Vector.getElem_ofFn]
        rw [← home_eq_role j hj]
        show (exec middleCode y2).vec (home j) l = (mid l 0)[j]
        rw [vm5.1, v5, (feed_view y2.gpr S T sp2 tbl2 l (view y2 l) rows apart j hj).1, ← getElem!_pos _ j hj]
        exact firstWords l 0 (by omega) j hj
      · apply Vector.ext; intro j hj
        simp only [Vector.getElem_ofFn]
        rw [← home_eq_role j hj]
        show (exec middleCode y2).vec (swapReg (home j)) l = (mid l 1)[j]
        rw [vm5.1, v5, (feed_view y2.gpr S T sp2 tbl2 l (view y2 l) rows apart j hj).2.1, ← getElem!_pos _ j hj]
        exact firstWords l 1 (by omega) j hj
      · simp only [view]
        have := l.isLt
        rw [vm5.2, r5 l _ (by simp only [RowOrOut, FrameApart, frame, tableSize] at apart ⊢; omega),
          feed_other _ _ _ (fun b _ j _ => by
            rw [sp2]; simp only [midSlot, FrameApart, frame, tableSize] at apart ⊢; omega)]
        exact rows row hrow
    · have rows := (inv2.lanes l).2.2.2
      have fv := feed_view y2.gpr S T sp2 tbl2 l (view y2 l) rows apart j hj
      simp only [view]
      rw [vm5.2, r5 l _ (by simp only [RowOrOut, midSlot]; omega)]
      rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
      · rw [fv.2.2.1]; exact firstWords l 0 (by omega) j hj
      · rw [fv.2.2.2]; exact firstWords l 1 (by omega) j hj
  generalize hx3 : exec middleCode y2 = x3 at run5 pad0 st5
  -- The third loop: eight blocks of padding rounds.
  have L6 : (program ls rs).toList = pre6 ls rs ++ paddingBlock ++ .jnz (pre6 ls rs).length :: post6 ls rs := by
    rw [program_parts]; simp only [pre6, pre4, post3, post5, List.append_assoc, List.cons_append, List.nil_append]
  have step3 : ∀ i < 8, ∀ x, PadLoop S T mid y2.gpr s.mem i x →
      PadLoop S T mid y2.gpr s.mem (i + 1) (exec paddingBlock x) ∧ ((exec paddingBlock x).zf = true ↔ i + 1 = 8) :=
    padLoop_step S T mid y2.gpr s.mem sp2 apart tBound
  have pc3 : ({ x3 with pc := (pre4 ls rs ++ firstBlock false ++ [Instr.jnz (pre4 ls rs).length]).length +
      middleCode.length } : State).pc = (pre6 ls rs).length := by
    simp only [pre6, List.length_append, List.length_cons, List.length_nil]
  obtain ⟨y3, inv3, sty3, pcy3, run6⟩ := loop_run (program ls rs) (pre6 ls rs) paddingBlock (post6 ls rs) L6
    (List.all_eq_true.mp b4) (fun i x => PadLoop S T mid y2.gpr s.mem i x) 8 (by decide)
    (fun i hi x _ _ h => step3 i hi x h) _ pc3 st5 (padLoop_pc _ pad0)
  -- The output.
  have L7 : (program ls rs).toList = (pre6 ls rs ++ paddingBlock ++ [Instr.jnz (pre6 ls rs).length]) ++
      outputCode ++ (tailCode ls rs ++ closingCode) := by
    rw [program_parts]
    simp only [pre6, pre4, post3, post5, post6, List.append_assoc, List.cons_append, List.nil_append]
  have run7 := run_block (program ls rs) _ outputCode _ L7 (List.all_eq_true.mp b5)
    { y3 with pc := (pre6 ls rs).length + paddingBlock.length + 1 }
    (by simp only [List.length_append, List.length_cons, List.length_nil]) sty3
  rw [exec_with_pc] at run7
  have sp3 : (y3.gpr sp).toNat = S := by rw [inv3.others _ (by decide) (by decide), sp2]
  have tbl3 : (y3.gpr tbl).toNat = T := by rw [inv3.others _ (by decide) (by decide), tbl2]
  -- The registers the loops never write, from the start.
  have keep3 : ∀ r, r ≠ words → r ≠ consts → r ≠ blocks → y3.gpr r = x1.gpr r := fun r h1 h2 h3 => by
    rw [inv3.others r h2 h3, inv2.others r h1 h2 h3]
  have out3 : (y3.gpr out).toNat = O := by
    rw [keep3 _ (by decide) (by decide) (by decide), others1 _ (by decide) (by decide) (by decide) (by decide)
      (by decide), hO]
  have table3 : TableAt y3.mem T := fun i hi => by
    simp only [tableSize] at hi
    rw [inv3.kept _ (by simp only [FrameApart, frame, tableSize] at apart ⊢; omega)]
    exact table i hi
  -- Each lane's final words: the padding rounds plus the kept first compression.
  have final : ∀ b < 2, ∀ l, ∀ j < 8,
      y3.vec (if b = 0 then home j else swapReg (home j)) l + (view y3 l).mem (S + midSlot b j) =
        (compress (mid l b) Kernel.paddingBlock 0)[j]! := by
    intro b hb l j hj
    obtain ⟨rolesA, rolesB, -⟩ := inv3.lanes l
    have rA := congrArg (·[j]) rolesA
    have rB := congrArg (·[j]) rolesB
    simp only [Vector.getElem_ofFn] at rA rB
    rw [← home_eq_role64 j hj] at rA rB
    have hv : y3.vec (if b = 0 then home j else swapReg (home j)) l =
        (roundsTo (mid l b) K (fun i => (schedule Kernel.paddingBlock 0)[i]!) 64)[j]! := by
      rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
      · simp only [ite_true]
        rw [getElem!_pos (roundsTo (mid l 0) K (fun i => (schedule Kernel.paddingBlock 0)[i]!) 64) j hj]
        exact rA
      · simp only [show ¬ (1 = 0) from by decide, ite_false]
        rw [getElem!_pos (roundsTo (mid l 1) K (fun i => (schedule Kernel.paddingBlock 0)[i]!) 64) j hj]
        exact rB
    rw [inv3.mids l b hb j hj, compress_get (mid l b) Kernel.paddingBlock j hj, hv, UInt32.add_comm]
  obtain ⟨dA, dB, kz, oz, gz⟩ := output_spec y3 S T O sp3 tbl3 out3 table3 apart outApart outTable outBound
    (fun l => compress (mid l 0) Kernel.paddingBlock 0) (fun l => compress (mid l 1) Kernel.paddingBlock 0)
    (fun l j hj => by simpa using final 0 (by omega) l j hj) (fun l j hj => by simpa using final 1 (by omega) l j hj)
  -- The whole pair, as its parts' steps.
  refine ⟨(setupCode ls rs).length + 6 * ((firstBlock true).length + 1) + [Instr.movImm blocks 2].length +
    2 * ((firstBlock false).length + 1) + middleCode.length + 8 * (paddingBlock.length + 1) + outputCode.length, ?_⟩
  simp only [run_add]
  rw [run1, run2, run3, run4, run5, run6, run7]
  -- Each byte of each digest is its pair's hash.
  have digest_eq : ∀ l : Fin 16, ∀ b < 2, digest (compress (mid l b) Kernel.paddingBlock 0) =
      Cryptography.Hash.Sha256.hash (pairMessage s.mem ((s.gpr left).toNat + ls * (16 * b + l.val))
        ((s.gpr right).toNat + rs * (16 * b + l.val))) := fun l b _ => by
    rw [hash_pair _ (pairMessage_size _ _ _)]
    rfl
  refine ⟨by simp only [exec_status]; exact sty3, ?_, fun p hp k hk => ?_, fun a ha hf => ?_, ?_, ?_, ?_,
    fun r h1 h2 h3 h4 h5 h6 => ?_⟩
  · simp only [pre6, pre4, pre2, body_eq, List.length_append, List.length_cons, List.length_nil, opening_length]
    omega
  · simp only
    rw [hO]
    by_cases first : p < 16
    · rw [dA ⟨p, first⟩ k hk, digest_eq ⟨p, first⟩ 0 (by omega)]
      simp only [Nat.mul_zero, Nat.zero_add]
    · have := dB ⟨p - 16, by omega⟩ k hk
      simp only at this
      rw [show O + 512 + 32 * (p - 16) + k = O + 32 * p + k by omega, digest_eq ⟨p - 16, by omega⟩ 1 (by omega)] at this
      rw [this]
      simp only
      rw [show 16 * 1 + (p - 16) = p by omega]
  · simp only
    rw [hO, hS] at *
    rw [kz a ha hf, inv3.kept a hf]
  · simp only; rw [gz _ (by decide), keep3 _ (by decide) (by decide) (by decide), left1]
  · simp only; rw [gz _ (by decide), keep3 _ (by decide) (by decide) (by decide), right1]
  · simp only; rw [oz, keep3 _ (by decide) (by decide) (by decide),
      others1 _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · simp only; rw [gz r h3, keep3 r h4 h5 h6, others1 r h1 h2 h4 h5 h6]

end EthLib.Consensus.Ssz.Native.Kernel.Avx512x2
