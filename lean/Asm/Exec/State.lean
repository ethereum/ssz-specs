import Asm.Frame
import Asm.Sha256.PairMain
import Asm.Exec.Layout
import Asm.Root.Reads
import Asm.Merkle.State

/-! The executor's states, and the facts every one of them shares. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Exec

open Ssz.Asm.Sha256 (sp t0 t1 a0 a1 a2 savedSlots pairCode workRegs)
open Ssz.Asm.Root (Step runPlan ReadsBelow WritesBelow)

/-- The stack frame's base, below the caller's stack pointer. -/
def base (m0 : Machine) : BitVec 64 :=
  m0.read sp - BitVec.ofNat 64 frameSize

/-- The scratch area's address. -/
def scratch (m0 : Machine) : BitVec 64 :=
  m0.read a0

/-- The plan's address. -/
def planAddr (m0 : Machine) : BitVec 64 :=
  m0.read a1

/-- The scratch area's bytes, as a plan reads them. -/
def view (m : Machine) (area : BitVec 64) : Root.Scratch :=
  fun a => ⟨m.mem (area + BitVec.ofNat 64 a)⟩

/-- Word j of a step's four-word encoding. -/
def stepWord : Step → Nat → Nat
  | .chunk _ _ _, 0 => 0
  | .chunk dst _ _, 1 => dst
  | .chunk _ src _, 2 => src
  | .chunk _ _ len, _ => len
  | .hash _ _ _, 0 => 1
  | .hash dst _ _, 1 => dst
  | .hash _ left _, 2 => left
  | .hash _ _ right, _ => right

/-- What a caller must provide: the plan in memory, sound offsets, and disjoint regions. -/
structure Valid (m0 : Machine) (steps : List Step) (size : Nat) : Prop where
  /-- The step count argument is the plan's length. -/
  count : (m0.read a2).toNat = steps.length
  /-- The plan's words are in memory, four per step. -/
  encoded : ∀ k (within : k < steps.length) j, j < 4 →
    m0.load (planAddr m0 + BitVec.ofNat 64 (32 * k + 8 * j)) 8 = BitVec.ofNat 64 (stepWord steps[k] j)
  /-- Every step reads below its own slot. -/
  reads : ReadsBelow steps
  /-- Every step writes inside the scratch area. -/
  writes : WritesBelow steps size
  /-- The scratch area is comfortably small. -/
  small : size < 2 ^ 60
  /-- The plan is comfortably small. -/
  short : 32 * steps.length < 2 ^ 60
  /-- The scratch area and the frame share no byte. -/
  scratchFrame : Disjoint (scratch m0) size (base m0) frameSize
  /-- The plan and the frame share no byte. -/
  planFrame : Disjoint (planAddr m0) (32 * steps.length) (base m0) frameSize
  /-- The plan and the scratch area share no byte. -/
  planScratch : Disjoint (planAddr m0) (32 * steps.length) (scratch m0) size

/-- The facts every state of the executor shares, after the frame is open. -/
structure Steady (m0 : Machine) (size : Nat) (m : Machine) : Prop where
  /-- The stack pointer sits at the frame's base. -/
  stack : m.read sp = base m0
  /-- The scratch area's address is in its slot. -/
  scratchStored : m.load (base m0 + BitVec.ofNat 64 scratchSlot) 8 = scratch m0
  /-- The plan's address is in its slot. -/
  planStored : m.load (base m0 + BitVec.ofNat 64 planSlot) 8 = planAddr m0
  /-- The step count is in its slot. -/
  stepsStored : m.load (base m0 + BitVec.ofNat 64 stepsSlot) 8 = m0.read a2
  /-- Each saved register is in its slot. -/
  savedStored : ∀ s ∈ savedSlots, m.load (base m0 + BitVec.ofNat 64 s.2) 8 = m0.read s.1
  /-- Memory outside the frame and the scratch area is untouched. -/
  untouched : ∀ y, ¬Within y (base m0) frameSize → ¬Within y (scratch m0) size → m.mem y = m0.mem y
  /-- The global pointer is untouched. -/
  globalPointer : m.read 3 = m0.read 3
  /-- The thread pointer is untouched. -/
  threadPointer : m.read 4 = m0.read 4

/-- The frame slots the loop rewrites. -/
def dynamicSlots : List Nat :=
  [outSlot, indexSlot]

theorem Steady.write {m0 m : Machine} {size : Nat} (steady : Steady m0 size m) {r : Reg} {v : BitVec 64}
    (notSp : r ≠ sp) (notGp : r ≠ 3) (notTp : r ≠ 4) : Steady m0 size (m.write r v) where
  stack := by rw [Machine.read_write_ne (Ne.symm notSp)]; exact steady.stack
  scratchStored := by rw [Machine.load_write]; exact steady.scratchStored
  planStored := by rw [Machine.load_write]; exact steady.planStored
  stepsStored := by rw [Machine.load_write]; exact steady.stepsStored
  savedStored := fun s inside => by rw [Machine.load_write]; exact steady.savedStored s inside
  untouched := fun y frame area => by rw [Machine.mem_write]; exact steady.untouched y frame area
  globalPointer := by rw [Machine.read_write_ne (Ne.symm notGp)]; exact steady.globalPointer
  threadPointer := by rw [Machine.read_write_ne (Ne.symm notTp)]; exact steady.threadPointer

/-- A frame slot's bytes lie in the frame. -/
theorem slot_within {m0 : Machine} {c k : Nat} (fits : c + 8 ≤ frameSize) (below : k < 8) :
    Within (base m0 + BitVec.ofNat 64 c + BitVec.ofNat 64 k) (base m0) frameSize := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, within_offset (by unfold frameSize at fits; omega)]
  omega

theorem Steady.store {m0 m : Machine} {size : Nat} (steady : Steady m0 size m) {c : Nat} {v : BitVec 64}
    (inside : c ∈ dynamicSlots) : Steady m0 size (m.store (base m0 + BitVec.ofNat 64 c) 8 v) := by
  have dyn : c = outSlot ∨ c = indexSlot := by simpa [dynamicSlots] using inside
  have fits : c + 8 ≤ frameSize := by rcases dyn with h | h <;> subst h <;> decide
  have apartFixed (c' : Nat) (away : c' + 8 ≤ c ∨ c + 8 ≤ c') (fits' : c' + 8 ≤ frameSize) :
      (m.store (base m0 + BitVec.ofNat 64 c) 8 v).load (base m0 + BitVec.ofNat 64 c') 8 =
        m.load (base m0 + BitVec.ofNat 64 c') 8 :=
    Machine.load_store_of_disjoint (disjoint_offsets (by unfold frameSize at fits fits'; omega)
      (by unfold frameSize at fits fits'; omega)) (by decide)
  refine ⟨steady.stack, ?_, ?_, ?_, fun s mem => ?_, fun y frame area => ?_, steady.globalPointer,
    steady.threadPointer⟩
  · rw [apartFixed scratchSlot (by rcases dyn with h | h <;> subst h <;> decide) (by decide)]
    exact steady.scratchStored
  · rw [apartFixed planSlot (by rcases dyn with h | h <;> subst h <;> decide) (by decide)]
    exact steady.planStored
  · rw [apartFixed stepsSlot (by rcases dyn with h | h <;> subst h <;> decide) (by decide)]
    exact steady.stepsStored
  · have below : s.2 + 8 ≤ 104 := by revert s; decide
    rw [apartFixed s.2 (by rcases dyn with h | h <;> subst h <;> simp [outSlot, indexSlot] <;> omega)
      (by unfold frameSize; omega)]
    exact steady.savedStored s mem
  · rw [Machine.mem_store_of_not_within fun within => frame (within_sub within fits (by decide))]
    exact steady.untouched y frame area

/-- The shared facts depend only on memory and on sp, gp, and tp. -/
theorem Steady.of_mem {m0 m m' : Machine} {size : Nat} (steady : Steady m0 size m) (mem : m'.mem = m.mem)
    (stack : m'.read sp = m.read sp) (gp : m'.read 3 = m.read 3) (tp : m'.read 4 = m.read 4) :
    Steady m0 size m' where
  stack := stack.trans steady.stack
  scratchStored := (Machine.load_of_mem mem).trans steady.scratchStored
  planStored := (Machine.load_of_mem mem).trans steady.planStored
  stepsStored := (Machine.load_of_mem mem).trans steady.stepsStored
  savedStored := fun s inside => (Machine.load_of_mem mem).trans (steady.savedStored s inside)
  untouched := fun y frame area => by rw [mem]; exact steady.untouched y frame area
  globalPointer := gp.trans steady.globalPointer
  threadPointer := tp.trans steady.threadPointer

/-- The shared facts survive any write confined to the scratch area. -/
theorem Steady.of_scratch {m0 m m' : Machine} {size : Nat} (valid : Disjoint (scratch m0) size (base m0) frameSize)
    (steady : Steady m0 size m) (mem : ∀ y, ¬Within y (scratch m0) size → m'.mem y = m.mem y)
    (stack : m'.read sp = m.read sp) (gp : m'.read 3 = m.read 3) (tp : m'.read 4 = m.read 4) :
    Steady m0 size m' := by
  have slot (c : Nat) (fits : c + 8 ≤ frameSize) :
      m'.load (base m0 + BitVec.ofNat 64 c) 8 = m.load (base m0 + BitVec.ofNat 64 c) 8 :=
    Machine.load_congr fun k below => mem _ fun inArea => valid _ inArea (slot_within fits below)
  exact {
    stack := stack.trans steady.stack
    scratchStored := (slot scratchSlot (by decide)).trans steady.scratchStored
    planStored := (slot planSlot (by decide)).trans steady.planStored
    stepsStored := (slot stepsSlot (by decide)).trans steady.stepsStored
    savedStored := fun s inside => by
      have : s.2 + 8 ≤ frameSize := by revert s; decide
      exact (slot s.2 this).trans (steady.savedStored s inside)
    untouched := fun y frame area => (mem y area).trans (steady.untouched y frame area)
    globalPointer := gp.trans steady.globalPointer
    threadPointer := tp.trans steady.threadPointer }

/-- A word of the plan reads as on entry, since the plan lies outside the frame and the scratch area. -/
theorem planWord {m0 m : Machine} {steps : List Step} {size : Nat} (valid : Valid m0 steps size)
    (steady : Steady m0 size m) {k j : Nat} (within : k < steps.length) (below : j < 4) :
    m.load (planAddr m0 + BitVec.ofNat 64 (32 * k + 8 * j)) 8 = BitVec.ofNat 64 (stepWord steps[k] j) := by
  rw [← valid.encoded k within j below]
  apply Machine.load_congr
  intro b bb
  have inPlan : Within (planAddr m0 + BitVec.ofNat 64 (32 * k + 8 * j) + BitVec.ofNat 64 b) (planAddr m0)
      (32 * steps.length) := by
    have := valid.short
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, within_offset (by omega)]
    omega
  exact steady.untouched _ (valid.planFrame _ inPlan) (valid.planScratch _ inPlan)

end Ssz.Asm.Exec
