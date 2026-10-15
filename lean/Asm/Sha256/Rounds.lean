import Asm.Sha256.Regs

/-! All sixty-four rounds of the kernel, read against the FIPS 180-4 round recurrence. -/

namespace Ssz.Asm.Sha256

open Ssz.Sha256 (Spec.State Spec.step Spec.rounds Spec.messageWord Spec.small0 Spec.small1)

/-- Every register the rounds may overwrite. -/
def workRegs : List Reg :=
  stateRegs.toList ++ wordRegs.toList ++ carryRegs.toList ++ [t0, t1]

theorem wordHome_mem (i j : Nat) : wordHome i j ∈ workRegs := by
  simp [workRegs, wordHome, Vector.getElem_mem]

theorem ringSlot_mem (t : Nat) : ringSlot t ∈ workRegs := by
  simp [workRegs, ringSlot, Vector.getElem_mem]

theorem carry_mem (i : Nat) : carry i ∈ workRegs := by
  simp [workRegs, carry, Vector.getElem_mem]

/-- A register outside the working set differs from one inside it. -/
theorem ne_of_not_mem {x r : Reg} (outside : x ∉ workRegs) (inside : r ∈ workRegs) : x ≠ r := by
  rintro rfl
  exact outside inside

/-- The schedule words a round can see: the sixteen before it, or the block itself early on. -/
def window (i t : Nat) : Prop :=
  max i 16 - 16 ≤ t ∧ t < max i 16

/--
The registers between two rounds, read against the FIPS 180-4 state after i rounds.

    homes    the eight working words, rotated by i
    carry    b xor c, for the next majority
    ring     the schedule words of the window, each in its slot
-/
structure RoundsInv (input : Vector (BitVec 32) 16) (init : Spec.State) (m0 : Machine) (i : Nat)
    (bound : i ≤ 64) (m : Machine) : Prop where
  /-- The first working word. -/
  a : Holds m (wordHome i 0) (Spec.rounds input init i bound).a
  /-- The second working word. -/
  b : Holds m (wordHome i 1) (Spec.rounds input init i bound).b
  /-- The third working word. -/
  c : Holds m (wordHome i 2) (Spec.rounds input init i bound).c
  /-- The fourth working word. -/
  d : Holds m (wordHome i 3) (Spec.rounds input init i bound).d
  /-- The fifth working word. -/
  e : Holds m (wordHome i 4) (Spec.rounds input init i bound).e
  /-- The sixth working word. -/
  f : Holds m (wordHome i 5) (Spec.rounds input init i bound).f
  /-- The seventh working word. -/
  g : Holds m (wordHome i 6) (Spec.rounds input init i bound).g
  /-- The eighth working word. -/
  h : Holds m (wordHome i 7) (Spec.rounds input init i bound).h
  /-- The majority carry. -/
  carry : Holds m (carry i)
    ((Spec.rounds input init i bound).b ^^^ (Spec.rounds input init i bound).c)
  /-- The schedule words in reach. -/
  ring : ∀ t, window i t → Holds m (ringSlot t) (Spec.messageWord input t)
  /-- Memory, which no round touches. -/
  mem : m.mem = m0.mem
  /-- Registers outside the working set. -/
  frame : ∀ x, x ∉ workRegs → m.read x = m0.read x

/-- The round constant of round i, as the code builds it. -/
def constant (i : Nat) : BitVec 32 :=
  (Ssz.Sha256.roundConstants[i % 64]'(Nat.mod_lt _ (by decide))).toBitVec

theorem messageWord_late (input : Vector (BitVec 32) 16) {t : Nat} (late : 16 ≤ t) :
    Spec.messageWord input t =
      Spec.messageWord input (t - 16) + Spec.small0 (Spec.messageWord input (t - 15)) +
        Spec.messageWord input (t - 7) + Spec.small1 (Spec.messageWord input (t - 2)) := by
  rw [Spec.messageWord, dif_neg (by omega)]

/-- The ring slot of a word is that of any word a multiple of sixteen away. -/
theorem ringSlot_shift {t u : Nat} (same : t % 16 = u % 16) : ringSlot t = ringSlot u := by
  rw [← ringSlot_mod t, ← ringSlot_mod u, same]

/--
The schedule step of round i, where there is one, leaves word i in its slot.

Every other register the rounds track keeps its value.
-/
theorem schedule_step {input : Vector (BitVec 32) 16} {init : Spec.State} {m0 m : Machine} {i : Nat}
    (bound : i < 64) (inv : RoundsInv input init m0 i (by omega) m) :
    let m1 := execBlock (if 16 ≤ i then scheduleCode i else []) m
    (∀ j, j < 8 → m1.read (wordHome i j) = m.read (wordHome i j)) ∧
      m1.read (carry i) = m.read (carry i) ∧
      (∀ t, window (i + 1) t → Holds m1 (ringSlot t) (Spec.messageWord input t)) ∧
      m1.mem = m.mem ∧ (∀ x, x ∉ workRegs → m1.read x = m.read x) := by
  intro m1
  by_cases late : 16 ≤ i
  · -- From round 16 on, slot i mod 16 trades word i - 16 for word i.
    have words := schedule_spec (m := m) (schedule_distinct i)
      (by rw [ringSlot_shift (u := i - 16) (by omega)]; exact inv.ring (i - 16) (by simp [window]; omega))
      (by rw [ringSlot_shift (u := i - 2) (by omega)]; exact inv.ring (i - 2) (by simp [window]; omega))
      (by rw [ringSlot_shift (u := i - 15) (by omega)]; exact inv.ring (i - 15) (by simp [window]; omega))
      (by rw [ringSlot_shift (u := i - 7) (by omega)]; exact inv.ring (i - 7) (by simp [window]; omega))
    simp only [m1, if_pos late, scheduleCode] at words ⊢
    obtain ⟨fresh, mem, frame⟩ := words
    refine ⟨fun j small => frame _ ?_ (wordHome_ne i j 0 0).2.2.1 (wordHome_ne i j 0 0).2.2.2,
      frame _ (Ne.symm (ringSlot_ne i i).1) (carry_ne i).1 (carry_ne i).2, fun t near => ?_, mem,
      fun x outside => frame x (ne_of_not_mem outside (ringSlot_mem i))
        (ne_of_not_mem outside (by simp [workRegs])) (ne_of_not_mem outside (by simp [workRegs]))⟩
    · exact (wordHome_ne i j i 0).1
    · -- Word i is the fresh one, and every other word in reach was already in its slot.
      by_cases now : t = i
      · subst now
        rw [messageWord_late input late]
        exact fresh
      · rw [Holds, frame _ (ringSlot_ne_ringSlot (by simp [window] at near; omega))
          (ringSlot_ne t 0).2.1 (ringSlot_ne t 0).2.2]
        exact inv.ring t (by simp [window] at near ⊢; omega)
  · -- The first sixteen words are the block itself, loaded before the rounds.
    have same : m1 = m := by simp [m1, late]
    rw [same]
    refine ⟨fun _ _ => rfl, rfl, fun t near => inv.ring t ?_, rfl, fun _ _ => rfl⟩
    simp [window] at near ⊢
    omega

/-- Every round constant survives its split into two immediates. -/
theorem constant_rebuilds : ∀ i, i < 64 → Rebuilds (constant i) := by
  -- Sixty-four constants, each checked by evaluation.
  unfold Rebuilds
  decide

theorem constant_eq {i : Nat} (bound : i < 64) :
    constant i = (Ssz.Sha256.roundConstants[i]'bound).toBitVec := by
  simp [constant, Nat.mod_eq_of_lt bound]

/-- A round keeps every working word except the two it updates, h and d. -/
theorem home_kept {i j : Nat} (small : j < 8) (notH : j ≠ 7) (notD : j ≠ 3) :
    wordHome i j ≠ wordHome i 7 ∧ wordHome i j ≠ wordHome i 3 ∧ wordHome i j ≠ carry (i + 1) ∧
      wordHome i j ≠ carry i ∧ wordHome i j ≠ t0 ∧ wordHome i j ≠ t1 :=
  ⟨wordHome_ne_wordHome small (by omega) notH, wordHome_ne_wordHome small (by omega) notD,
    (wordHome_ne i j 0 (i + 1)).2.1, (wordHome_ne i j 0 i).2.1, (wordHome_ne i j 0 0).2.2.1,
    (wordHome_ne i j 0 0).2.2.2⟩

/-- One schedule step and one round carry the invariant from round i to round i + 1. -/
theorem rounds_step {input : Vector (BitVec 32) 16} {init : Spec.State} {m0 m : Machine} {i : Nat}
    (bound : i < 64) (inv : RoundsInv input init m0 i (by omega) m) :
    RoundsInv input init m0 (i + 1) bound
      (execBlock ((if 16 ≤ i then scheduleCode i else []) ++ roundCode i (constant i)) m) := by
  rw [execBlock_append]
  obtain ⟨homes, carried, ring, mem1, frame1⟩ := schedule_step bound inv
  generalize execBlock (if 16 ≤ i then scheduleCode i else []) m = m1 at homes carried ring mem1 frame1
  -- Before the round, every input of it sits where the round looks for it.
  have before (j : Nat) (small : j < 8) (word : BitVec 32) (held : Holds m (wordHome i j) word) :
      Holds m1 (wordHome i j) word := by
    rw [Holds, homes j small]
    exact held
  have round := round_spec (m := m1) (round_distinct i) (constant_rebuilds i bound)
    (before 0 (by omega) _ inv.a) (before 1 (by omega) _ inv.b) (before 3 (by omega) _ inv.d)
    (before 4 (by omega) _ inv.e) (before 5 (by omega) _ inv.f) (before 6 (by omega) _ inv.g)
    (before 7 (by omega) _ inv.h) (ring i (by simp [window]; omega))
    (by rw [Holds, carried]; exact inv.carry)
  simp only [roundCode]
  obtain ⟨newA, newE, newCarry, mem2, frame2⟩ := round
  -- Round i + 1 of the specification is round i's state stepped once.
  have next : Spec.rounds input init (i + 1) bound =
      Spec.step (Spec.rounds input init i (by omega)) (constant i) (Spec.messageWord input i) := by
    rw [constant_eq bound]
    rfl
  -- The six words the round does not update keep their homes' values, one position along.
  have kept (j : Nat) (small : j < 8) (notH : j ≠ 7) (notD : j ≠ 3) (word : BitVec 32)
      (held : Holds m (wordHome i j) word) :
      Holds (execBlock (roundCodeWith (wordHome i 0) (wordHome i 1) (wordHome i 3) (wordHome i 4)
        (wordHome i 5) (wordHome i 6) (wordHome i 7) (ringSlot i) (carry i) (carry (i + 1))
        (constant i)) m1) (wordHome i j) word := by
    obtain ⟨h7, h3, p, q, z0, z1⟩ := home_kept (i := i) small notH notD
    rw [Holds, frame2 _ h7 h3 p q z0 z1]
    exact before j small word held
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun t near => ?_, ?_, fun x outside => ?_⟩
  · rw [wordHome_succ_zero, next]
    exact newA
  · rw [wordHome_succ i 0 (by omega), next]
    exact kept 0 (by omega) (by omega) (by omega) _ inv.a
  · rw [wordHome_succ i 1 (by omega), next]
    exact kept 1 (by omega) (by omega) (by omega) _ inv.b
  · rw [wordHome_succ i 2 (by omega), next]
    exact kept 2 (by omega) (by omega) (by omega) _ inv.c
  · rw [wordHome_succ i 3 (by omega), next]
    exact newE
  · rw [wordHome_succ i 4 (by omega), next]
    exact kept 4 (by omega) (by omega) (by omega) _ inv.e
  · rw [wordHome_succ i 5 (by omega), next]
    exact kept 5 (by omega) (by omega) (by omega) _ inv.f
  · rw [wordHome_succ i 6 (by omega), next]
    exact kept 6 (by omega) (by omega) (by omega) _ inv.g
  · rw [next]
    exact newCarry
  · -- No round writes a ring slot, so the words in reach stay put.
    rw [Holds, frame2 _ (Ne.symm (wordHome_ne i 7 t 0).1) (Ne.symm (wordHome_ne i 3 t 0).1)
      (ringSlot_ne t (i + 1)).1 (ringSlot_ne t i).1 (ringSlot_ne t 0).2.1 (ringSlot_ne t 0).2.2]
    exact ring t near
  · rw [mem2, mem1, inv.mem]
  · rw [frame2 x (ne_of_not_mem outside (wordHome_mem i 7)) (ne_of_not_mem outside (wordHome_mem i 3))
      (ne_of_not_mem outside (carry_mem _)) (ne_of_not_mem outside (carry_mem _))
      (ne_of_not_mem outside (by simp [workRegs])) (ne_of_not_mem outside (by simp [workRegs])),
      frame1 x outside, inv.frame x outside]

/-- The rounds below any count carry the invariant from round zero to that count. -/
theorem rounds_all {input : Vector (BitVec 32) 16} {init : Spec.State} {m0 m : Machine}
    (start : RoundsInv input init m0 0 (by omega) m) :
    ∀ n (bound : n ≤ 64), RoundsInv input init m0 n bound (execBlock (roundsCode n) m)
  | 0, _ => start
  | n + 1, bound => by
    -- The rounds so far, then this round's schedule step and the round itself.
    rw [roundsCode, List.append_assoc, execBlock_append]
    exact rounds_step bound (rounds_all start n (by omega))

end Ssz.Asm.Sha256
