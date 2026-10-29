import SszNative.Proofs.Kernel.Avx512x2.Setup

/-!
One pass of each of the thirty-two-lane kernel's three loops, on the whole machine.

Each pass runs a block of rowwise code lane by lane, then moves its pointers and counts one block down.
The lanes keep their invariants, because those read only registers, scratch rows, and table rows.
-/

namespace EthLib.Consensus.Ssz.Native.Kernel.Avx512x2

open EthLib.Cryptography.Hash.Sha256 hiding K IV
open EthLib.Consensus.Ssz.Native.Asm
open EthLib.Consensus.Ssz.Native.Kernel.Avx512 (tbl add_toNat roundsTo K W PW role)

/-- The first-block invariant reads only registers, scratch rows, and table rows. -/
theorem FirstInv.congr {S T : Nat} {l : Fin 16} {m : Nat → ByteArray} {t : Nat} {v v' : View}
    (inv : FirstInv S T l m t v) (regs : ∀ r, v'.regs r = v.regs r) (mem : ∀ a, RowOrOut S a → v'.mem a = v.mem a)
    (apart : FrameApart S T) : FirstInv S T l m t v' := by
  obtain ⟨a, b, c, d⟩ := inv
  refine ⟨by simpa only [regs] using a, by simpa only [regs] using b, fun b' hb u hu h64 => ?_, fun row hrow => ?_⟩
  · rw [mem _ (by simp only [RowOrOut, wordSlot, frame]; omega)]
    exact c b' hb u hu h64
  · rw [mem _ (by simp only [RowOrOut, FrameApart, frame, tableSize] at apart ⊢; omega)]
    exact d row hrow

/-- The padding invariant reads only registers and table rows. -/
theorem PadInv.congr {S T : Nat} {l : Fin 16} {mid : Nat → Vector UInt32 8} {t : Nat} {v v' : View}
    (inv : PadInv T l mid t v) (regs : ∀ r, v'.regs r = v.regs r) (mem : ∀ a, RowOrOut S a → v'.mem a = v.mem a)
    (apart : FrameApart S T) : PadInv T l mid t v' := by
  obtain ⟨a, b, d⟩ := inv
  refine ⟨by simpa only [regs] using a, by simpa only [regs] using b, fun row hrow => ?_⟩
  rw [mem _ (by simp only [RowOrOut, FrameApart, frame, tableSize] at apart ⊢; omega)]
  exact d row hrow

/-- A lane of a state whose vectors and memory are another's. -/
theorem view_eq {x y : State} (hv : x.vec = y.vec) (hm : x.mem = y.mem) (l : Fin 16) : view x l = view y l := by
  simp only [view, hv, hm]

/-- The first-block loops' rounds, without the pointer updates. -/
def firstLanes (sched : Bool) : List Instr := (List.range 8).flatMap (firstStep sched)

/-- A first-block loop's block is its rounds, then three pointer updates. -/
theorem firstBlock_eq (sched : Bool) :
    firstBlock sched = firstLanes sched ++ [.subImm words 1024, .addImm consts 512, .subImm blocks 1] := rfl

/-- The padding loop's rounds, without the pointer updates. -/
def padLanes : List Instr := (List.range 8).flatMap padStep

/-- The padding loop's block is its rounds, then two pointer updates. -/
theorem paddingBlock_eq : paddingBlock = padLanes ++ [.addImm consts 512, .subImm blocks 1] := rfl

/-- The first-block loops' rounds read scratch rows through the schedule pointer, and table rows through the table pointer. -/
theorem firstLanes_shape : (firstLanes true).all (shapeOK words consts 3008 512) = true ∧
    (firstLanes false).all (shapeOK words consts 3008 512) = true := by
  -- Every instruction, checked by evaluation.
  decide +kernel

/-- The padding loop's rounds read only table rows through the table pointer. -/
theorem padLanes_shape : padLanes.all (shapeOK sp consts (frame - 64) 512) = true := by
  -- Every instruction, checked by evaluation.
  decide +kernel

/-- The first-block loops' pointer updates. -/
theorem firstUpdates_exec (x : State) :
    let y := exec [.subImm words 1024, .addImm consts 512, .subImm blocks 1] x
    y.vec = x.vec ∧ y.mem = x.mem ∧ y.gpr words = x.gpr words - (1024 : Nat).toUInt64 ∧
      y.gpr consts = x.gpr consts + (512 : Nat).toUInt64 ∧ y.gpr blocks = x.gpr blocks - (1 : Nat).toUInt64 ∧
      y.zf = (x.gpr blocks - (1 : Nat).toUInt64 == 0) ∧
      ∀ r, r ≠ words → r ≠ consts → r ≠ blocks → y.gpr r = x.gpr r := by
  -- Three register updates; the last sets the flag.
  refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, fun r h1 h2 h3 => ?_⟩ <;> simp [exec, exec1, assign, *]

/-- The padding loop's pointer updates. -/
theorem padUpdates_exec (x : State) :
    let y := exec [.addImm consts 512, .subImm blocks 1] x
    y.vec = x.vec ∧ y.mem = x.mem ∧ y.gpr consts = x.gpr consts + (512 : Nat).toUInt64 ∧
      y.gpr blocks = x.gpr blocks - (1 : Nat).toUInt64 ∧ y.zf = (x.gpr blocks - (1 : Nat).toUInt64 == 0) ∧
      ∀ r, r ≠ consts → r ≠ blocks → y.gpr r = x.gpr r := by
  -- Two register updates; the last sets the flag.
  refine ⟨rfl, rfl, ?_, ?_, rfl, fun r h1 h2 => ?_⟩ <;> simp [exec, exec1, assign, *]

/-- A small count minus one, as a machine word, and whether it reaches zero. -/
theorem count_down (c : Nat) (hc : 1 ≤ c) (small : c < 2 ^ 32) :
    (c.toUInt64 - (1 : Nat).toUInt64) = (c - 1).toUInt64 ∧ ((c.toUInt64 - (1 : Nat).toUInt64 == 0) = true ↔ c = 1) := by
  have e : c.toUInt64 - (1 : Nat).toUInt64 = (c - 1).toUInt64 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le]
    · simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
    · rw [UInt64.le_iff_toNat_le]; simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
  refine ⟨e, ?_⟩
  rw [e]
  simp only [beq_iff_eq]
  constructor
  · intro h
    have := congrArg UInt64.toNat h
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.toNat_zero] at this
    omega
  · intro h; subst h; rfl

/-- Where the first-block loops are after i of their n blocks, started at block i0. -/
structure FirstLoop (S T : Nat) (m : Fin 16 → Nat → ByteArray) (G0 : Gpr → UInt64) (M0 : Nat → UInt8)
    (i0 n i : Nat) (x : State) : Prop where
  /-- The schedule pointer, while it is used. -/
  wordsAt : i0 + i < 8 → (x.gpr words).toNat = S + wordsBase (i0 + i)
  /-- The table pointer. -/
  constsAt : (x.gpr consts).toNat = T + 512 * (i0 + i)
  /-- The blocks left. -/
  blocksLeft : x.gpr blocks = (n - i).toUInt64
  /-- Every other register. -/
  others : ∀ r, r ≠ words → r ≠ consts → r ≠ blocks → x.gpr r = G0 r
  /-- Every lane's rounds so far. -/
  lanes : ∀ l, FirstInv S T l (m l) (8 * (i0 + i)) (view x l)
  /-- Memory off the scratch area. -/
  kept : ∀ a, a < S ∨ S + frame ≤ a → x.mem a = M0 a

set_option maxHeartbeats 1000000 in
/-- One pass of a first-block loop keeps its invariant, and sets the zero flag on the last pass. -/
theorem firstLoop_step (S T : Nat) (m : Fin 16 → Nat → ByteArray) (G0 : Gpr → UInt64) (M0 : Nat → UInt8)
    (i0 n : Nat) (sched : Bool) (hn : i0 + n ≤ 8) (hs : ∀ i < n, sched = true ↔ i0 + i < 6)
    (hsp : (G0 sp).toNat = S) (apart : FrameApart S T)
    (tBound : T + tableSize ≤ addressBound) :
    ∀ i < n, ∀ x, FirstLoop S T m G0 M0 i0 n i x →
      FirstLoop S T m G0 M0 i0 n (i + 1) (exec (firstBlock sched) x) ∧
      ((exec (firstBlock sched) x).zf = true ↔ i + 1 = n) := by
  intro i hi x inv
  rw [firstBlock_eq, exec_append]
  have shape : (firstLanes sched).all (shapeOK words consts 3008 512) = true := by
    cases sched
    · exact firstLanes_shape.2
    · exact firstLanes_shape.1
  obtain ⟨v1, r1, k1, g1, -, -⟩ := exec_rows (firstLanes sched) words consts 3008 512 shape x S T
    (wordsBase (i0 + i)) (512 * (i0 + i)) (inv.wordsAt (by omega)) (by simp only [wordsBase]; omega)
    (by simp only [wordsBase, frame]; omega) inv.constsAt (by simp only [tableSize]; omega) apart
  generalize hy : exec (firstLanes sched) x = y at v1 r1 k1 g1
  obtain ⟨vz, mz, wz, cz, bz, zz, gz⟩ := firstUpdates_exec y
  have down := count_down (n - i) (by omega) (by omega)
  refine ⟨⟨fun h => ?_, ?_, ?_, fun r h1 h2 h3 => ?_, fun l => ?_, fun a ha => ?_⟩, ?_⟩
  · -- The schedule pointer moves down one block.
    rw [wz, g1]
    have := inv.wordsAt (by omega)
    apply (show ∀ z : UInt64, z.toNat = S + wordsBase (i0 + i) →
        (z - (1024 : Nat).toUInt64).toNat = S + wordsBase (i0 + (i + 1)) from fun z hz => by
      rw [UInt64.toNat_sub_of_le]
      · simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', hz, wordsBase]; omega
      · rw [UInt64.le_iff_toNat_le]; simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', hz, wordsBase]; omega)
    exact this
  · -- The table pointer moves up one block.
    rw [cz, g1, add_toNat _ _ (by rw [inv.constsAt]; simp only [tableSize] at tBound; omega), inv.constsAt]
    omega
  · rw [bz, g1, inv.blocksLeft, down.1, Nat.sub_sub]
  · rw [gz r h1 h2 h3, g1, inv.others r h1 h2 h3]
  · -- Each lane: eight more rounds, carried over to the machine's lanes.
    have hb := first_block x.gpr S T l (m l) (i0 + i) (view x l) sched (by omega) (hs i hi)
      (inv.wordsAt (by omega)) inv.constsAt apart (inv.lanes l)
    rw [view_eq vz mz]
    rw [show 8 * (i0 + (i + 1)) = 8 * (i0 + i) + 8 by omega]
    exact FirstInv.congr hb (fun r => v1 r l) (fun a ha => r1 l a ha) apart
  · rw [mz, k1 a ha, inv.kept a ha]
  · rw [zz, g1, inv.blocksLeft]
    exact down.2.trans ⟨fun h => by omega, fun h => by omega⟩

/-- Where the padding loop is after i of its eight blocks. -/
structure PadLoop (S T : Nat) (mid : Fin 16 → Nat → Vector UInt32 8) (G0 : Gpr → UInt64) (M0 : Nat → UInt8)
    (i : Nat) (x : State) : Prop where
  /-- The table pointer. -/
  constsAt : (x.gpr consts).toNat = T + 512 * (8 + i)
  /-- The blocks left. -/
  blocksLeft : x.gpr blocks = (8 - i).toUInt64
  /-- Every other register. -/
  others : ∀ r, r ≠ consts → r ≠ blocks → x.gpr r = G0 r
  /-- Every lane's rounds so far. -/
  lanes : ∀ l, PadInv T l (mid l) (8 * i) (view x l)
  /-- Every lane's first-block results, kept in the scratch area. -/
  mids : ∀ l, ∀ b < 2, ∀ j < 8, (view x l).mem (S + midSlot b j) = (mid l b)[j]!
  /-- Memory off the scratch area. -/
  kept : ∀ a, a < S ∨ S + frame ≤ a → x.mem a = M0 a

set_option maxHeartbeats 1000000 in
/-- One pass of the padding loop keeps its invariant, and sets the zero flag on the last pass. -/
theorem padLoop_step (S T : Nat) (mid : Fin 16 → Nat → Vector UInt32 8) (G0 : Gpr → UInt64) (M0 : Nat → UInt8)
    (hsp : (G0 sp).toNat = S) (apart : FrameApart S T) (tBound : T + tableSize ≤ addressBound) :
    ∀ i < 8, ∀ x, PadLoop S T mid G0 M0 i x →
      PadLoop S T mid G0 M0 (i + 1) (exec paddingBlock x) ∧ ((exec paddingBlock x).zf = true ↔ i + 1 = 8) := by
  intro i hi x inv
  rw [paddingBlock_eq, exec_append]
  obtain ⟨v1, r1, k1, g1, -, -⟩ := exec_rows padLanes sp consts (frame - 64) 512 padLanes_shape x S T
    0 (512 * (8 + i)) (by rw [inv.others _ (by decide) (by decide), hsp]; rfl) rfl (by simp [frame]) inv.constsAt
    (by simp only [tableSize]; omega) apart
  generalize hy : exec padLanes x = y at v1 r1 k1 g1
  obtain ⟨vz, mz, cz, bz, zz, gz⟩ := padUpdates_exec y
  have down := count_down (8 - i) (by omega) (by omega)
  refine ⟨⟨?_, ?_, fun r h1 h2 => ?_, fun l => ?_, fun l b hb j hj => ?_, fun a ha => ?_⟩, ?_⟩
  · rw [cz, g1, add_toNat _ _ (by rw [inv.constsAt]; simp only [tableSize] at tBound; omega), inv.constsAt]
    omega
  · rw [bz, g1, inv.blocksLeft, down.1, Nat.sub_sub]
  · rw [gz r h1 h2, g1, inv.others r h1 h2]
  · -- Each lane: eight more rounds, carried over to the machine's lanes.
    have hb := pad_block x.gpr T l (mid l) i (view x l) hi inv.constsAt (inv.lanes l)
    rw [view_eq vz mz, show 8 * (i + 1) = 8 * i + 8 by omega]
    exact PadInv.congr (S := S) hb (fun r => v1 r l) (fun a ha => r1 l a ha) apart
  · -- The kept results: no padding round stores.
    rw [view_eq vz mz]
    simp only [view]
    rw [r1 l _ (by simp only [RowOrOut, midSlot]; omega), padLanes, pad_block_mem]
    exact inv.mids l b hb j hj
  · rw [mz, k1 a ha, inv.kept a ha]
  · rw [zz, g1, inv.blocksLeft]
    exact down.2.trans ⟨fun h => by omega, fun h => by omega⟩

end EthLib.Consensus.Ssz.Native.Kernel.Avx512x2
