import Asm.Sha256.Exit

/-! The whole compression routine, read against FIPS 180-4 and the RISC-V calling convention. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm

theorem Machine.load_of_mem {m m' : Machine} {a : BitVec 64} {n : Nat} (same : m.mem = m'.mem) :
    m.load a n = m'.load a n :=
  load_congr fun _ _ => by rw [same]

theorem Machine.word32_of_mem {m m' : Machine} {a : BitVec 64} (same : m.mem = m'.mem) :
    m.word32 a = m'.word32 a := by
  simp only [word32, load_of_mem same]

/-- The bytes of a range agree between machines that agree on that range. -/
theorem Machine.bytes_congr {m m' : Machine} {a : BitVec 64} {n : Nat}
    (same : ∀ k, k < n → m.mem (a + BitVec.ofNat 64 k) = m'.mem (a + BitVec.ofNat 64 k)) :
    m.bytes a n = m'.bytes a n := by
  simp only [bytes]
  congr 2
  funext i
  rw [same i.val i.isLt]

/-- The word at an address agrees between machines that agree on its four bytes. -/
theorem Machine.stateAt_of_mem {m m' : Machine} {a : BitVec 64} (same : m.mem = m'.mem) :
    m.stateAt a = m'.stateAt a := by
  simp only [stateAt, word32_of_mem same]

theorem Machine.word32_congr {m m' : Machine} {a : BitVec 64}
    (same : ∀ k, k < 4 → m.mem (a + BitVec.ofNat 64 k) = m'.mem (a + BitVec.ofNat 64 k)) :
    m.word32 a = m'.word32 a := by
  simp only [word32, load_congr same]

end Ssz.Asm

namespace Ssz.Asm.Sha256

open Ssz.Sha256 (Spec.State Spec.rounds Spec.compression Spec.inputWords Spec.messageWord
  Spec.addState)

/-- Registers a caller finds unchanged: the return address, the stack, gp, tp, and s0 to s11. -/
def preserved : List Reg :=
  [1, 2, 3, 4, 8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The stack frame's base, below the caller's stack pointer. -/
def frameBase (m : Machine) : BitVec 64 :=
  m.read sp - BitVec.ofNat 64 frameSize

theorem stateWord_stateAt {m : Machine} {a : BitVec 64} {j : Nat} (small : j < 8) :
    stateWord (m.stateAt a) j = m.word32 (a + BitVec.ofNat 64 (4 * j)) := by
  simp only [Nat.lt_succ_iff_lt_or_eq] at small
  repeat' rcases small with small | rfl
  all_goals try (exfalso; omega)
  all_goals rfl

theorem stateAt_eq {m : Machine} {a : BitVec 64} {s : Spec.State}
    (words : ∀ j, j < 8 → m.word32 (a + BitVec.ofNat 64 (4 * j)) = stateWord s j) :
    m.stateAt a = s := by
  -- Two states with the same eight words are the same state.
  have w0 := words 0 (by omega)
  have w1 := words 1 (by omega)
  have w2 := words 2 (by omega)
  have w3 := words 3 (by omega)
  have w4 := words 4 (by omega)
  have w5 := words 5 (by omega)
  have w6 := words 6 (by omega)
  have w7 := words 7 (by omega)
  cases s
  simp only [Machine.stateAt, stateWord, Spec.State.words] at *
  simp_all

theorem prologue_spec (m : Machine) :
    let m' := execBlock prologueCode m
    m'.read sp = frameBase m ∧ (∀ r, r ≠ sp → m'.read r = m.read r) ∧
      (∀ y, ¬Within y (frameBase m) frameSize → m'.mem y = m.mem y) ∧
      ∀ s ∈ frameSlots, m'.load (frameBase m + BitVec.ofNat 64 s.2) 8 = m.read s.1 := by
  intro m'
  -- Opening the frame moves the stack pointer down by the frame size.
  have opened : (Instr.addi sp sp (BitVec.ofInt 12 (-(frameSize : Int)))).run m =
      m.write sp (frameBase m) := by
    have down : (BitVec.ofInt 12 (-(frameSize : Int))).signExtend 64 = 0 - BitVec.ofNat 64 frameSize := by
      decide
    have moved : m.read sp + (0 - BitVec.ofNat 64 frameSize) = m.read sp - BitVec.ofNat 64 frameSize := by
      bv_omega
    simp only [Instr.run, frameBase, down, moved]
  have small : ∀ s ∈ frameSlots, s.2 < 2048 := by decide
  have inside : ∀ s ∈ frameSlots, s.2 + 8 ≤ frameSize := by decide
  have notSp : ∀ s ∈ frameSlots, s.1 ≠ sp := by decide
  have apart : SlotsApart frameSlots := by unfold SlotsApart; decide
  simp only [m', prologueCode, execBlock_cons, opened]
  refine ⟨?_, fun r other => ?_, fun y outside => ?_, fun s mem => ?_⟩
  · rw [spills_read]
    exact Machine.read_write_self (by decide)
  · rw [spills_read, Machine.read_write_ne other]
  · -- Every slot lies inside the frame, so a byte outside it is never stored to.
    rw [spills_mem small fun s mem within => outside (within_sub (by
        rwa [Machine.read_write_self (by decide)] at within) (inside s mem) (by decide)),
      Machine.mem_write]
  · have loaded := spills_load (base := sp) (m := m.write sp (frameBase m)) apart s mem
    rwa [Machine.read_write_self (by decide), Machine.read_write_ne (notSp s mem)] at loaded

theorem messageWord_early {input : Vector (BitVec 32) 16} {t : Nat} (early : t < 16) :
    Spec.messageWord input t = input[t] := by
  rw [Spec.messageWord, dif_pos early]

theorem inputWords_get {block : ByteArray} {t : Nat} (early : t < 16) :
    (Spec.inputWords block 0)[t] = Ssz.Sha256.Spec.inputWord block (4 * t) := by
  rw [Spec.inputWords, Vector.getElem_ofFn, Nat.zero_add]

/-- The code that runs before the first round. -/
def entryCode : List Instr :=
  prologueCode ++ loadBlockCode ++ loadStateCode ++ [.xor (carry 0) (wordHome 0 1) (wordHome 0 2)]

/-- Just before the first round, the block and the state sit where the rounds expect them. -/
theorem entry_spec (m : Machine)
    (stateClear : Disjoint (m.read a0) 32 (frameBase m) frameSize)
    (blockClear : Disjoint (m.read a1) 64 (frameBase m) frameSize) :
    let m' := execBlock entryCode m
    RoundsInv (Spec.inputWords (m.bytes (m.read a1) 64) 0) (m.stateAt (m.read a0)) m' 0 (by omega) m' ∧
      m'.read sp = frameBase m ∧ (∀ r, r ∉ workRegs → r ≠ sp → m'.read r = m.read r) ∧
      (∀ y, ¬Within y (frameBase m) frameSize → m'.mem y = m.mem y) ∧
      ∀ s ∈ frameSlots, m'.load (frameBase m + BitVec.ofNat 64 s.2) 8 = m.read s.1 := by
  intro m'
  simp only [m', entryCode, execBlock_append, loadBlockCode]
  obtain ⟨spP, regsP, memP, slotsP⟩ := prologue_spec m
  generalize execBlock prologueCode m = m2 at spP regsP memP slotsP
  obtain ⟨ring, memL, frameL⟩ := loadBlock_upto (m := m2) 16 (by omega)
  generalize execBlock ((List.range 16).flatMap loadWordCode) m2 = m3 at ring memL frameL
  obtain ⟨homes, memS, frameS⟩ := loadState_spec (m := m3)
  generalize execBlock loadStateCode m3 = m4 at homes memS frameS
  simp only [execBlock_cons, execBlock_nil, Instr.run]
  -- The block and state addresses are the caller's, and their bytes lie outside the frame.
  have a1Same : m2.read a1 = m.read a1 := regsP a1 (by decide)
  have a0Same : m3.read a0 = m.read a0 := by
    rw [frameL a0 (by decide) (by decide), regsP a0 (by decide)]
  have bytesSame : m2.bytes (m.read a1) 64 = m.bytes (m.read a1) 64 :=
    Machine.bytes_congr fun k below => memP _ (blockClear _ ((within_offset (by omega)).mpr below))
  have wordSame (j : Nat) (small : j < 8) :
      m3.word32 (m.read a0 + BitVec.ofNat 64 (4 * j)) =
        m.word32 (m.read a0 + BitVec.ofNat 64 (4 * j)) := by
    rw [Machine.word32_of_mem memL]
    apply Machine.word32_congr
    intro k below
    apply memP
    apply stateClear
    rw [show m.read a0 + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 k =
        m.read a0 + BitVec.ofNat 64 (4 * j + k) by rw [BitVec.add_assoc, BitVec.ofNat_add]]
    exact (within_offset (by omega)).mpr (by omega)
  -- The carry is written last, so every home keeps the word just loaded into it.
  have home (j : Nat) (small : j < 8) :
      Holds (m4.write (carry 0) (m4.read (wordHome 0 1) ^^^ m4.read (wordHome 0 2))) (wordHome 0 j)
        (m.word32 (m.read a0 + BitVec.ofNat 64 (4 * j))) := by
    rw [Holds, Machine.read_write_ne (wordHome_ne 0 j 0 0).2.1, homes j small, a0Same, wordSame j small]
  refine ⟨⟨home 0 (by omega), home 1 (by omega), home 2 (by omega), home 3 (by omega),
    home 4 (by omega), home 5 (by omega), home 6 (by omega), home 7 (by omega), ?_,
    fun t near => ?_, rfl, fun _ _ => rfl⟩, ?_, fun r outside notSp => ?_, fun y outside => ?_,
    fun s inside => ?_⟩
  · -- Round zero's carry is b xor c of the incoming state.
    rw [Holds, Machine.read_write_self (nonzero 0 0 0 0).2.2.symm]
    have b := home 1 (by omega)
    have c := home 2 (by omega)
    rw [Holds, Machine.read_write_ne (wordHome_ne 0 1 0 0).2.1] at b
    rw [Holds, Machine.read_write_ne (wordHome_ne 0 2 0 0).2.1] at c
    rw [b, c, BitVec.signExtend_xor]
    rfl
  · -- The first sixteen schedule words are the block's own words.
    have early : t < 16 := by simp [window] at near; omega
    rw [Holds, Machine.read_write_ne (ringSlot_ne t 0).1, frameS _ (ringSlot_not_state t),
      messageWord_early early]
    have := ring t early
    rw [a1Same, bytesSame] at this
    rw [inputWords_get early]
    exact this
  · rw [Machine.read_write_ne (by decide), frameS sp (by decide), frameL sp (by decide) (by decide), spP]
  · have notState : r ∉ stateRegs.toList := fun inside => outside (by simp [workRegs, inside])
    have notWord : r ∉ wordRegs.toList := fun inside => outside (by simp [workRegs, inside])
    have notCarry : r ≠ carry 0 := ne_of_not_mem outside (carry_mem 0)
    have notT0 : r ≠ t0 := ne_of_not_mem outside (by simp [workRegs])
    rw [Machine.read_write_ne notCarry, frameS r notState, frameL r notWord notT0, regsP r notSp]
  · rw [Machine.mem_write, memS, memL, memP y outside]
  · rw [Machine.load_write, Machine.load_of_mem memS, Machine.load_of_mem memL, slotsP s inside]

/--
The straight-line body computes one SHA-256 compression and honours the calling convention.

The frame is the 112 bytes just below the caller's stack pointer, which the convention frees.
-/
theorem compress_spec (m : Machine)
    (stateClear : Disjoint (m.read a0) 32 (frameBase m) frameSize)
    (blockClear : Disjoint (m.read a1) 64 (frameBase m) frameSize) :
    let final := execBlock compressBody m
    final.stateAt (m.read a0) =
        Spec.compression (Spec.inputWords (m.bytes (m.read a1) 64) 0) (m.stateAt (m.read a0)) ∧
      (∀ r ∈ preserved, final.read r = m.read r) ∧
      ∀ y, ¬Within y (frameBase m) frameSize → ¬Within y (m.read a0) 32 → final.mem y = m.mem y := by
  intro final
  have body : compressBody = entryCode ++ (roundsCode 64 ++ (feedForwardCode ++ epilogueCode)) := by
    simp only [compressBody, entryCode, List.append_assoc, List.singleton_append, List.cons_append]
  simp only [final, body, execBlock_append]
  obtain ⟨inv0, spE, regsE, memE, slotsE⟩ := entry_spec m stateClear blockClear
  generalize execBlock entryCode m = m5 at inv0 spE regsE memE slotsE
  have inv := rounds_all inv0 64 (by omega)
  generalize execBlock (roundsCode 64) m5 = m6 at inv
  -- The input, the incoming state, and the working state after all sixty-four rounds.
  generalize Spec.inputWords (m.bytes (m.read a1) 64) 0 = input at inv
  generalize hInit : m.stateAt (m.read a0) = init at inv
  -- The feed-forward first reads the state address back from its slot.
  have spR : m6.read sp = frameBase m := by rw [inv.frame sp (by decide), spE]
  have pointer : m6.load (m6.read sp + (104 : BitVec 12).signExtend 64) 8 = m.read a0 := by
    rw [spR, show (104 : BitVec 12).signExtend 64 = BitVec.ofNat 64 104 by decide,
      Machine.load_of_mem inv.mem, slotsE (a0, 104) (by decide)]
  simp only [feedForwardCode, execBlock_cons, Instr.run, pointer]
  have homeLast (j : Nat) : wordHome 64 j = wordHome 0 j := by simp [wordHome]
  have stateBytes (j k : Nat) (small : j < 8) (below : k < 4) :
      ¬Within (m.read a0 + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 k) (frameBase m) frameSize := by
    apply stateClear
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact (within_offset (by omega)).mpr (by omega)
  obtain ⟨-, -, written, memF, frameF⟩ := feedForward_upto (m := m6.write t1 (m.read a0))
    (st := m.read a0) (init := init) (work := Spec.rounds input init 64 (by omega))
    (Machine.read_write_self (by decide))
    (fun j small => by
      rw [Holds, Machine.read_write_ne (wordHome_ne 0 j 0 0).2.2.2, ← homeLast]
      simp only [Nat.lt_succ_iff_lt_or_eq] at small
      repeat' rcases small with small | rfl
      all_goals try (exfalso; omega)
      all_goals
        first
        | exact inv.a | exact inv.b | exact inv.c | exact inv.d
        | exact inv.e | exact inv.f | exact inv.g | exact inv.h)
    (fun j small => by
      rw [Machine.word32_write, Machine.word32_of_mem inv.mem, ← hInit, stateWord_stateAt small]
      exact Machine.word32_congr fun k below => memE _ (stateBytes j k small below))
    8 (by omega)
  generalize execBlock ((List.range 8).flatMap feedWordCode) (m6.write t1 (m.read a0)) = m7
    at written memF frameF
  -- The epilogue reloads the saved registers from the frame and closes it.
  simp only [epilogueCode, execBlock_append, execBlock_cons, execBlock_nil, Instr.run]
  obtain ⟨memR, loadedR, keptR⟩ := reloads_spec (base := sp) (slots := savedSlots) (m := m7)
    (by decide) (by decide) (by decide)
  generalize execBlock (reloads sp savedSlots) m7 = m8 at memR loadedR keptR
  have sp7 : m7.read sp = frameBase m := by
    rw [frameF sp (by decide) (by decide), Machine.read_write_ne (by decide), spR]
  have sp8 : m8.read sp = frameBase m := by rw [keptR sp (by decide), sp7]
  -- A frame byte lies outside the state, so the feed-forward never overwrote a saved register.
  have frameBytes (s : Reg × Nat) (inside : s ∈ frameSlots) (k : Nat) (below : k < 8) :
      ¬Within (frameBase m + BitVec.ofNat 64 s.2 + BitVec.ofNat 64 k) (m.read a0) 32 := by
    have fits : s.2 + 8 ≤ frameSize := by revert s; decide
    simp only [frameSize] at fits
    apply stateClear.symm
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact (within_offset (by omega)).mpr (by simp only [frameSize]; omega)
  have saved (s : Reg × Nat) (inside : s ∈ savedSlots) :
      m8.read s.1 = m.read s.1 := by
    have slot : s ∈ frameSlots := by simp [frameSlots, inside]
    rw [loadedR s inside, sp7, Machine.load_congr fun k below => memF _ (frameBytes s slot k below),
      Machine.load_write, Machine.load_of_mem inv.mem, slotsE s slot]
  refine ⟨?_, fun r inside => ?_, fun y outFrame outState => ?_⟩
  · -- Each written word is the incoming word plus the working word, which is the feed-forward.
    rw [Machine.stateAt_of_mem (m := m8.write sp _) (m' := m7) (by rw [Machine.mem_write, memR])]
    apply stateAt_eq
    intro j small
    rw [written j small]
    simp only [Nat.lt_succ_iff_lt_or_eq] at small
    repeat' rcases small with small | rfl
    all_goals try (exfalso; omega)
    all_goals rfl
  · have savedRegs : ∀ r ∈ savedSlots.map Prod.fst, m8.read r = m.read r := by
      intro r inside
      obtain ⟨s, mem, rfl⟩ := List.mem_map.mp inside
      exact saved s mem
    -- gp and tp are never written at all.
    have untouched (r : Reg) (notSaved : r ∉ savedSlots.map Prod.fst) (notState : r ∉ stateRegs.toList)
        (notT0 : r ≠ t0) (notT1 : r ≠ t1) (notWork : r ∉ workRegs) (notSp : r ≠ sp) :
        m8.read r = m.read r := by
      rw [keptR r notSaved, frameF r notState notT0, Machine.read_write_ne notT1,
        inv.frame r notWork, regsE r notWork notSp]
    simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    -- The stack pointer moves back up by the frame size.
    case inr.inl =>
      rw [Machine.read_write_self (by decide), sp8,
        show (BitVec.ofNat 12 frameSize).signExtend 64 = BitVec.ofNat 64 frameSize by decide, frameBase,
        BitVec.sub_add_cancel]
    all_goals rw [Machine.read_write_ne (by decide)]
    all_goals first
      | exact savedRegs _ (by decide)
      | exact untouched _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · rw [Machine.mem_write, memR, memF y outState, Machine.mem_write, inv.mem, memE y outFrame]

theorem roundsCode_straight : ∀ n, (roundsCode n).all Instr.straight
  | 0 => rfl
  | n + 1 => by
    -- Every generated instruction is arithmetic, logic, or a constant.
    simp only [roundsCode, List.all_append, roundsCode_straight n, Bool.true_and]
    split <;> simp [scheduleCode, scheduleCodeWith, roundCode, roundCodeWith, rotations2Code,
      rotations3Code, Instr.straight]

theorem compressBody_straight : ∀ i ∈ compressBody, i.straight := by
  apply List.all_eq_true.mp
  simp [compressBody, prologueCode, spills, loadBlockCode, loadWordCode, loadWordFrom, loadStateCode,
    feedForwardCode, feedWordCode, epilogueCode, reloads, roundsCode_straight, Instr.straight,
    List.all_flatMap, List.all_map]

/--
Run from its first instruction, the routine reaches its return having compressed one block.

The step count is the instruction count, since the code has no branch.
-/
theorem compress_correct (m : Machine)
    (stateClear : Disjoint (m.read a0) 32 (frameBase m) frameSize)
    (blockClear : Disjoint (m.read a1) 64 (frameBase m) frameSize) :
    let s := runFor compressProgram compressBody.length ⟨m, 0⟩
    returned compressProgram s ∧
      s.m.stateAt (m.read a0) =
        Spec.compression (Spec.inputWords (m.bytes (m.read a1) 64) 0) (m.stateAt (m.read a0)) ∧
      (∀ r ∈ preserved, s.m.read r = m.read r) ∧
      ∀ y, ¬Within y (frameBase m) frameSize → ¬Within y (m.read a0) 32 → s.m.mem y = m.mem y := by
  intro s
  -- The body sits at the start of the program, with the return right after it.
  have placed : ∀ k (within : k < compressBody.length),
      compressProgram[(⟨m, 0⟩ : Cpu).pc + k]? = some compressBody[k] := by
    intro k within
    rw [show (⟨m, 0⟩ : Cpu).pc + k = k from Nat.zero_add k]
    simp only [compressProgram, List.getElem?_toArray, List.getElem?_append_left within,
      List.getElem?_eq_getElem within]
  have ran := runFor_block compressBody ⟨m, 0⟩ placed compressBody_straight
  have last : compressProgram[compressBody.length]? = some .ret := by
    simp only [compressProgram, List.getElem?_toArray]
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  refine ⟨?_, ?_⟩
  · simp only [s, returned, ran, Nat.zero_add, last]
  · simp only [s, ran]
    exact compress_spec m stateClear blockClear

end Ssz.Asm.Sha256
