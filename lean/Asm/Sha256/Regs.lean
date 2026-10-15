import Asm.Sha256.Round

/-! The register allocation of the kernel: which homes never collide, and how they rotate. -/

namespace Ssz.Asm.Sha256

theorem wordHome_mod (i j : Nat) : wordHome (i % 16) j = wordHome i j := by
  -- A home depends on the round only modulo 8, which divides 16.
  simp only [wordHome, Nat.mod_mod_of_dvd i (by decide : 8 ∣ 16)]

theorem ringSlot_mod (t : Nat) : ringSlot (t % 16) = ringSlot t := by
  simp [ringSlot]

theorem carry_mod (i : Nat) : carry (i % 16) = carry i := by
  -- A carry depends on the round only modulo 2, which divides 16.
  simp only [carry, Nat.mod_mod_of_dvd i (by decide : 2 ∣ 16)]

theorem carry_succ_mod (i : Nat) : carry (i % 16 + 1) = carry (i + 1) := by
  simp only [carry]
  congr 1
  omega

theorem round_distinct (i : Nat) :
    Distinct [wordHome i 0, wordHome i 1, wordHome i 3, wordHome i 4, wordHome i 5, wordHome i 6,
      wordHome i 7, ringSlot i, carry i, carry (i + 1), t0, t1] := by
  -- Sixteen register assignments repeat forever, and each is checked by evaluation.
  rw [← wordHome_mod i 0, ← wordHome_mod i 1, ← wordHome_mod i 3, ← wordHome_mod i 4,
    ← wordHome_mod i 5, ← wordHome_mod i 6, ← wordHome_mod i 7, ← ringSlot_mod, ← carry_mod,
    ← carry_succ_mod]
  have below := Nat.mod_lt i (by decide : 16 > 0)
  generalize i % 16 = k at below ⊢
  unfold Distinct
  revert k
  decide

theorem schedule_distinct (t : Nat) :
    Distinct [ringSlot t, ringSlot (t + 14), ringSlot (t + 1), ringSlot (t + 9), t0, t1] := by
  -- The four slots are 16, 2, 15, and 7 words back, all different modulo 16.
  have shift (k : Nat) : ringSlot (t + k) = ringSlot (t % 16 + k) := by
    simp only [ringSlot]
    congr 1
    omega
  rw [shift 14, shift 1, shift 9, ← ringSlot_mod t]
  have below := Nat.mod_lt t (by decide : 16 > 0)
  generalize t % 16 = k at below ⊢
  unfold Distinct
  revert k
  decide

/-- A state home is never a ring slot, a carry, or a temporary. -/
theorem wordHome_ne (i j t c : Nat) :
    wordHome i j ≠ ringSlot t ∧ wordHome i j ≠ carry c ∧ wordHome i j ≠ t0 ∧ wordHome i j ≠ t1 := by
  -- The three groups of registers are disjoint by construction.
  have all : ∀ a (_ : a < 8) b (_ : b < 16) c (_ : c < 2),
      stateRegs[a] ≠ wordRegs[b] ∧ stateRegs[a] ≠ carryRegs[c] ∧ stateRegs[a] ≠ t0 ∧
        stateRegs[a] ≠ t1 := by decide
  have := all ((j + 8 - i % 8) % 8) (Nat.mod_lt _ (by decide)) (t % 16) (Nat.mod_lt _ (by decide))
    (c % 2) (Nat.mod_lt _ (by decide))
  simpa [wordHome, ringSlot, carry] using this

/-- A ring slot is never a carry or a temporary. -/
theorem ringSlot_ne (t c : Nat) : ringSlot t ≠ carry c ∧ ringSlot t ≠ t0 ∧ ringSlot t ≠ t1 := by
  have all : ∀ b (_ : b < 16) c (_ : c < 2),
      wordRegs[b] ≠ carryRegs[c] ∧ wordRegs[b] ≠ t0 ∧ wordRegs[b] ≠ t1 := by decide
  have := all (t % 16) (Nat.mod_lt _ (by decide)) (c % 2) (Nat.mod_lt _ (by decide))
  simpa [ringSlot, carry] using this

/-- A carry is never a temporary. -/
theorem carry_ne (c : Nat) : carry c ≠ t0 ∧ carry c ≠ t1 := by
  have all : ∀ c (_ : c < 2), carryRegs[c] ≠ t0 ∧ carryRegs[c] ≠ t1 := by decide
  have := all (c % 2) (Nat.mod_lt _ (by decide))
  simpa [carry] using this

/-- No home, slot, or carry is the zero register, whose writes are lost. -/
theorem nonzero (i j t c : Nat) : (0 : Reg) ≠ wordHome i j ∧ (0 : Reg) ≠ ringSlot t ∧ (0 : Reg) ≠ carry c := by
  have all : ∀ a (_ : a < 8) b (_ : b < 16) c (_ : c < 2),
      (0 : Reg) ≠ stateRegs[a] ∧ (0 : Reg) ≠ wordRegs[b] ∧ (0 : Reg) ≠ carryRegs[c] := by decide
  have := all ((j + 8 - i % 8) % 8) (Nat.mod_lt _ (by decide)) (t % 16) (Nat.mod_lt _ (by decide))
    (c % 2) (Nat.mod_lt _ (by decide))
  simpa [wordHome, ringSlot, carry] using this

/-- A ring slot is never a state home. -/
theorem ringSlot_not_state (t : Nat) : ringSlot t ∉ stateRegs.toList := by
  have all : ∀ b (_ : b < 16), wordRegs[b] ∉ stateRegs.toList := by decide
  exact all (t % 16) (Nat.mod_lt _ (by decide))

/-- Two ring slots coincide only for words a multiple of sixteen apart. -/
theorem ringSlot_ne_ringSlot {t t' : Nat} (apart : t % 16 ≠ t' % 16) : ringSlot t ≠ ringSlot t' := by
  have all : ∀ a (_ : a < 16) b (_ : b < 16), a ≠ b → wordRegs[a] ≠ wordRegs[b] := by decide
  have := all (t % 16) (Nat.mod_lt _ (by decide)) (t' % 16) (Nat.mod_lt _ (by decide)) apart
  simpa [ringSlot] using this

/-- Two state homes in one round coincide only for the same working word. -/
theorem wordHome_ne_wordHome {i j j' : Nat} (small : j < 8) (small' : j' < 8) (apart : j ≠ j') :
    wordHome i j ≠ wordHome i j' := by
  have all : ∀ a (_ : a < 8) b (_ : b < 8), a ≠ b → stateRegs[a] ≠ stateRegs[b] := by decide
  have := all ((j + 8 - i % 8) % 8) (Nat.mod_lt _ (by decide)) ((j' + 8 - i % 8) % 8)
    (Nat.mod_lt _ (by decide)) (by omega)
  simpa [wordHome] using this

/-- The next round finds each working word one home along, with the new a in the old h's home. -/
theorem wordHome_succ (i j : Nat) (small : j < 7) : wordHome (i + 1) (j + 1) = wordHome i j := by
  simp only [wordHome]
  congr 1
  omega

theorem wordHome_succ_zero (i : Nat) : wordHome (i + 1) 0 = wordHome i 7 := by
  simp only [wordHome]
  congr 1
  omega

end Ssz.Asm.Sha256
