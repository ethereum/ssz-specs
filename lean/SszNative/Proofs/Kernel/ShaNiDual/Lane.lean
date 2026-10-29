import SszNative.Proofs.Kernel.ShaNi.Main
import SszNative.Kernel.ShaNiDual

/-! The two register sets of the interleaved kernel: what each one holds, and that they never meet. -/

namespace Ssz.Native.Kernel.ShaNiDual

open Ssz.Native.Asm

/-- The shared registers' numbers. -/
theorem wk_val : wk.val = 0 := rfl

@[inherit_doc wk_val] theorem tmp_val : tmp.val = 7 := rfl

@[inherit_doc wk_val] theorem bswap_val : bswap.val = 10 := rfl

/-- The first pair's register numbers. -/
theorem first_vals (r : Nat) : first.abef.val = 1 ∧ first.cdgh.val = 2 ∧ (first.msg r).val = 3 + r % 4 :=
  ⟨rfl, rfl, rfl⟩

/-- The second pair's register numbers. -/
theorem second_vals (r : Nat) : second.abef.val = 8 ∧ second.cdgh.val = 9 ∧ (second.msg r).val = 11 + r % 4 :=
  ⟨rfl, rfl, rfl⟩

/-- The register numbers a set of registers needs to be usable: its own registers apart, and apart from the shared ones. -/
structure Good (g : Lane) : Prop where
  /-- The schedule vectors are four consecutive registers. -/
  msg_val : ∀ r, (g.msg r).val = (g.msg 0).val + r % 4
  /-- The first block's state is kept in the first schedule vector. -/
  mid_abef : g.midAbef = g.msg 0
  /-- The first block's state is kept in the second schedule vector. -/
  mid_cdgh : g.midCdgh = g.msg 1
  /-- The two state registers differ. -/
  state : g.abef.val ≠ g.cdgh.val
  /-- The first state register lies outside the schedule vectors. -/
  abef_msg : g.abef.val < (g.msg 0).val ∨ (g.msg 0).val + 4 ≤ g.abef.val
  /-- The second state register lies outside the schedule vectors. -/
  cdgh_msg : g.cdgh.val < (g.msg 0).val ∨ (g.msg 0).val + 4 ≤ g.cdgh.val
  /-- The first state register is none of the shared ones. -/
  abef_shared : g.abef.val ≠ 0 ∧ g.abef.val ≠ 7 ∧ g.abef.val ≠ 10
  /-- The second state register is none of the shared ones. -/
  cdgh_shared : g.cdgh.val ≠ 0 ∧ g.cdgh.val ≠ 7 ∧ g.cdgh.val ≠ 10
  /-- The schedule vectors avoid the shared registers. -/
  msg_shared : (0 < (g.msg 0).val ∧ (g.msg 0).val + 4 ≤ 7) ∨ 10 < (g.msg 0).val

/-- The first pair's registers are usable. -/
theorem good_first : Good first where
  msg_val r := by rw [(first_vals r).2.2, (first_vals 0).2.2]
  mid_abef := rfl
  mid_cdgh := rfl
  state := by decide
  abef_msg := by decide
  cdgh_msg := by decide
  abef_shared := by decide
  cdgh_shared := by decide
  msg_shared := by decide

/-- The second pair's registers are usable. -/
theorem good_second : Good second where
  msg_val r := by rw [(second_vals r).2.2, (second_vals 0).2.2]
  mid_abef := rfl
  mid_cdgh := rfl
  state := by decide
  abef_msg := by decide
  cdgh_msg := by decide
  abef_shared := by decide
  cdgh_shared := by decide
  msg_shared := by decide

/-- The registers one pair's code writes: its own state and schedule, and the two shared scratch registers. -/
def Touches (g : Lane) (v : Vreg) : Prop :=
  v = wk ∨ v = tmp ∨ v = g.abef ∨ v = g.cdgh ∨ ∃ r, v = g.msg r

/-- The registers one pair's rounds read across groups: its state and its schedule. -/
def Holds (g : Lane) (v : Vreg) : Prop :=
  v = g.abef ∨ v = g.cdgh ∨ ∃ r, v = g.msg r

/-- The register numbers the first pair writes are at most 7. -/
theorem first_touches (v : Vreg) (h : Touches first v) : v.val ≤ 7 := by
  rcases h with e | e | e | e | ⟨r, e⟩ <;> subst e
  · rw [wk_val]; omega
  · rw [tmp_val]; omega
  · rw [(first_vals 0).1]; omega
  · rw [(first_vals 0).2.1]; omega
  · rw [(first_vals r).2.2]; omega

/-- The register numbers the first pair keeps lie between 1 and 6. -/
theorem first_holds (v : Vreg) (h : Holds first v) : 1 ≤ v.val ∧ v.val ≤ 6 := by
  rcases h with e | e | ⟨r, e⟩ <;> subst e
  · rw [(first_vals 0).1]; omega
  · rw [(first_vals 0).2.1]; omega
  · rw [(first_vals r).2.2]; omega

/-- The register numbers the second pair writes: 0, 7, 8, 9, and 11 to 14. -/
theorem second_touches (v : Vreg) (h : Touches second v) : v.val = 0 ∨ 7 ≤ v.val := by
  rcases h with e | e | e | e | ⟨r, e⟩ <;> subst e
  · rw [wk_val]; omega
  · rw [tmp_val]; omega
  · rw [(second_vals 0).1]; omega
  · rw [(second_vals 0).2.1]; omega
  · rw [(second_vals r).2.2]; omega

/-- The register numbers the second pair keeps: 8, 9, and 11 to 14. -/
theorem second_holds (v : Vreg) (h : Holds second v) : 8 ≤ v.val := by
  rcases h with e | e | ⟨r, e⟩ <;> subst e
  · rw [(second_vals 0).1]; omega
  · rw [(second_vals 0).2.1]; omega
  · rw [(second_vals r).2.2]; omega

/-- What the second pair keeps is never written by the first pair's code. -/
theorem second_apart (v : Vreg) (h : Holds second v) : ¬ Touches first v := fun t => by
  -- The second pair keeps registers from 8 up, and the first pair writes registers up to 7.
  have := second_holds v h
  have := first_touches v t
  omega

/-- What the first pair keeps is never written by the second pair's code. -/
theorem first_apart (v : Vreg) (h : Holds first v) : ¬ Touches second v := fun t => by
  -- The first pair keeps registers 1 to 6, and the second pair writes register 0 and registers from 7 up.
  have := first_holds v h
  have := second_touches v t
  omega

/-- The mask register is never written by either pair's code. -/
theorem bswap_untouched (g : Lane) (hg : Good g) : ¬ Touches g bswap := by
  -- The mask is register 10, which no usable set writes.
  have := hg.abef_shared
  have := hg.cdgh_shared
  have := hg.msg_shared
  have := hg.msg_val
  rintro (e | e | e | e | ⟨r, e⟩) <;> have e := congrArg Fin.val e <;>
    simp only [bswap_val, wk_val, tmp_val] at e <;> (try have := hg.msg_val r) <;> omega

/-- Two schedule vectors of a usable set differ when their indices differ modulo four. -/
theorem msg_ne (g : Lane) (hg : Good g) (r q : Nat) (h : r % 4 ≠ q % 4) : g.msg r ≠ g.msg q := by
  -- Their register numbers differ by the indices' difference.
  intro e
  have := congrArg Fin.val e
  rw [hg.msg_val r, hg.msg_val q] at this
  omega

/-- A schedule vector is neither state register, nor a shared register. -/
theorem msg_apart (g : Lane) (hg : Good g) (r : Nat) :
    g.msg r ≠ g.abef ∧ g.msg r ≠ g.cdgh ∧ g.msg r ≠ wk ∧ g.msg r ≠ tmp ∧ g.msg r ≠ bswap := by
  -- The schedule vectors are four consecutive registers clear of the others.
  have m := hg.msg_val r
  have := hg.abef_msg
  have := hg.cdgh_msg
  have := hg.msg_shared
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
    (have := congrArg Fin.val e; (try simp only [wk_val, tmp_val, bswap_val] at this); omega)

/-- The state registers differ from each other and from the shared registers. -/
theorem state_apart (g : Lane) (hg : Good g) :
    g.abef ≠ g.cdgh ∧ g.abef ≠ wk ∧ g.abef ≠ tmp ∧ g.abef ≠ bswap ∧
    g.cdgh ≠ wk ∧ g.cdgh ≠ tmp ∧ g.cdgh ≠ bswap := by
  -- Each pair of numbers differs by the set's facts.
  have := hg.state
  have := hg.abef_shared
  have := hg.cdgh_shared
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩ <;>
    (have := congrArg Fin.val e; (try simp only [wk_val, tmp_val, bswap_val] at this); omega)

end Ssz.Native.Kernel.ShaNiDual
