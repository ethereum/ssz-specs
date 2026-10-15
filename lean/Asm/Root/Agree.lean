import Asm.Root.Reads

/-! Plans only read inside the scratch area, so scratches agreeing there stay in agreement. -/

namespace Ssz.Asm.Root

open Ssz

/-- Two scratches agree below an offset. -/
def Agree (s s' : Scratch) (size : Nat) : Prop :=
  ∀ a, a < size → s a = s' a

theorem readSlot_congr {s s' : Scratch} {size offset : Nat} (agree : Agree s s' size)
    (fits : offset + 32 ≤ size) : readSlot s offset = readSlot s' offset := by
  unfold readSlot
  congr 1
  funext i
  exact agree _ (by omega)

theorem step_congr {step : Step} {s s' : Scratch} {size : Nat} (reads : step.readsBelow)
    (fits : step.dst + 32 ≤ size) (agree : Agree s s' size) : Agree (step.run s) (step.run s') size := by
  intro a below
  cases step with
  | chunk dst src len =>
    simp only [Step.readsBelow, Step.dst] at reads fits
    simp only [Step.run]
    split
    · split
      · exact agree _ (by omega)
      · rfl
    · exact agree a below
  | hash dst left right =>
    simp only [Step.readsBelow, Step.dst] at reads fits
    simp only [Step.run]
    split
    · rw [readSlot_congr agree (by omega : left + 32 ≤ size), readSlot_congr agree (by omega : right + 32 ≤ size)]
    · exact agree a below

theorem runPlan_congr {size : Nat} : ∀ {steps : List Step} {s s' : Scratch}, ReadsBelow steps →
    WritesBelow steps size → Agree s s' size → Agree (runPlan steps s) (runPlan steps s') size
  | [], _, _, _, _, agree => agree
  | step :: steps, s, s', reads, writes, agree => by
    rw [runPlan_cons, runPlan_cons]
    exact runPlan_congr (fun t mem => reads t (by simp [mem])) (fun t mem => writes t (by simp [mem]))
      (step_congr (reads step (by simp)) (writes step (by simp)) agree)

theorem agree_trans {s s' s'' : Scratch} {size : Nat} (a : Agree s s' size) (b : Agree s' s'' size) :
    Agree s s'' size :=
  fun x below => (a x below).trans (b x below)

end Ssz.Asm.Root
