import SszNative.Proofs.Driver.TreeStore.Basic

/-!
A loop copying one node per pass, from a source to a destination its index picks.

Every copy loop of the tree drivers has this shape: two addresses computed, 32 bytes copied, the index stepped.
Destinations miss each other and every source, so each copy lands and stays.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir

/-- Variables as at the start, except the index and the two addresses. -/
def Agree (e0 e : Env) (I D S : Nat) : Prop :=
  ∀ y, y ≠ I → y ≠ D → y ≠ S → e y = e0 y

/-- Memory as at the start, outside every destination of a run of copies. -/
def KeptOut (mem mm : Memory) (dst : Nat → Nat) (i0 n : Nat) : Prop :=
  ∀ a, (∀ i, i0 ≤ i → i < n → ¬ (dst i ≤ a ∧ a < dst i + 32)) → mm a = mem a

set_option maxHeartbeats 1000000 in
/--
A copy loop over indices i0 to n puts each source's node at its destination.

Memory changes only at the destinations, and only the index and the two address variables change.
-/
theorem copy_loop {m : Module} {w : World} {sp : Nat} {e0 : Env} {mem : Memory} {I D S : Nat} {N DE SE : Expr}
    {i0 n : Nat} (dst src : Nat → Nat) (dI : D ≠ I) (sI : S ≠ I) (sD : S ≠ D)
    (hN : ∀ e mm, Agree e0 e I D S → eval w e mm N = some (UInt64.ofNat n))
    (hD : ∀ e mm i, Agree e0 e I D S → e I = UInt64.ofNat i → i0 ≤ i → i < n → KeptOut mem mm dst i0 n →
      eval w e mm DE = some (UInt64.ofNat (dst i)))
    (hS : ∀ e mm i, Agree e0 e I D S → e I = UInt64.ofNat i → i0 ≤ i → i < n → KeptOut mem mm dst i0 n →
      eval w e mm SE = some (UInt64.ofNat (src i)))
    (start : e0 I = UInt64.ofNat i0) (le : i0 ≤ n) (nb : n < 2 ^ 63)
    (dAcc : ∀ i, i0 ≤ i → i < n → w.access (dst i) 32 = true)
    (sAcc : ∀ i, i0 ≤ i → i < n → w.access (src i) 32 = true)
    (ds : ∀ i j, i0 ≤ i → i < n → i0 ≤ j → j < n → Apart (dst i, 32) (src j, 32))
    (dd : ∀ i j, i0 ≤ i → i < j → j < n → Apart (dst i, 32) (dst j, 32)) :
    Ends m w sp e0 mem (.loop (Expr.lt (.var I) N) (.block ([Stmt.assign ⟨D⟩ DE, Stmt.assign ⟨S⟩ SE] ++
      copy32 (.var D) (.var S) ++ [Stmt.assign ⟨I⟩ (.var I + 1)])))
      fun e mm => Agree e0 e I D S ∧ e I = UInt64.ofNat n ∧
        (∀ i, i0 ≤ i → i < n → nodeAt mm (dst i) = nodeAt mem (src i)) ∧ KeptOut mem mm dst i0 n := by
  refine Ends.mono (Ends.loop (fun e mm => Agree e0 e I D S ∧ ∃ i, i0 ≤ i ∧ i ≤ n ∧ e I = UInt64.ofNat i ∧
      (∀ j, i0 ≤ j → j < i → nodeAt mm (dst j) = nodeAt mem (src j)) ∧
      ∀ a, (∀ j, i0 ≤ j → j < i → ¬ (dst j ≤ a ∧ a < dst j + 32)) → mm a = mem a)
    (fun e _ => n - (e I).toNat)
    ⟨fun _ _ _ _ => rfl, i0, Nat.le_refl _, le, start, fun j a b => absurd b (by omega),
      fun _ _ => rfl⟩ ?_ ?_) ?_
  · rintro e mm ⟨ag, i, _, hi, iv, _, _⟩
    exact ⟨_, eval_lt (eval_var iv) (hN e mm ag) (by omega) (by omega)⟩
  · rintro e mm v ⟨ag, i, li, hi, iv, done, fr⟩ hv nz
    have hv := Option.some.inj (hv.symm.trans (eval_lt (eval_var iv) (hN e mm ag) (by omega) (by omega)))
    have below : i < n := by
      by_cases hb : i < n
      · exact hb
      · rw [ite_eq_right hb] at hv; exact absurd hv nz
    -- Memory outside every destination is as at the start.
    have kept : KeptOut mem mm dst i0 n := fun a ha => fr a fun j a1 a2 => ha j a1 (by omega)
    have ed := hD e mm i ag iv li below kept
    have ag1 : Agree e0 (Asm.assign e D (UInt64.ofNat (dst i))) I D S := fun y a b c => by
      rw [assign_ne b]; exact ag y a b c
    have es := hS _ mm i ag1 ((assign_ne (Ne.symm dI)).trans iv) li below kept
    have bd := access_bound (dAcc i li below)
    have bs := access_bound (sAcc i li below)
    have dsi := ds i i li below li below
    refine Ends.append (Q := fun e' mm' =>
        e' = Asm.assign (Asm.assign e D (UInt64.ofNat (dst i))) S (UInt64.ofNat (src i)) ∧
        mm' = copied mm (dst i) (src i) 32)
      (Ends.step (Runs.set _ _ _ _ _ _ _ _ ed) (Ends.step (Runs.set _ _ _ _ _ _ _ _ es)
        (Ends.of_runs (copy32_runs (fun _ => eval_var ((assign_ne (Ne.symm sD)).trans assign_eq))
          (fun _ => eval_var assign_eq) (dAcc i li below) (sAcc i li below) dsi) ⟨rfl, rfl⟩))) ?_
    rintro e2 mm2 ⟨rfl, rfl⟩
    have iv2 : Asm.assign (Asm.assign e D (UInt64.ofNat (dst i))) S (UInt64.ofNat (src i)) I = UInt64.ofNat i :=
      (assign_ne (Ne.symm sI)).trans ((assign_ne (Ne.symm dI)).trans iv)
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_add (eval_var iv2) (eval_lit 1))) (Ends.nil ⟨⟨fun y a b c => ?_,
      i + 1, by omega, by omega, assign_eq, fun j a1 a2 => ?_, fun a ha => ?_⟩, ?_⟩)
    · rw [assign_ne a, assign_ne c, assign_ne b]; exact ag y a b c
    · by_cases hj : j = i
      · subst hj
        rw [nodeAt_copied]
        exact nodeAt_congr fun q hq => by
          refine fr _ fun j' b1 b2 => ?_
          have := ds j' j b1 (by omega) a1 (by omega)
          simp only [Apart] at this
          omega
      · have dji := dd j i a1 (by omega) below
        simp only [Apart] at dji
        rw [nodeAt_congr (m₂ := mm) fun q hq => copied_out (by omega)]
        exact done j a1 (by omega)
    · have := ha i li (by omega)
      rw [copied_out this]
      exact fr a fun j b1 b2 => ha j b1 (by omega)
    · rw [assign_eq, iv, ofNat_toNat (by omega), ofNat_toNat (by omega)]
      omega
  · rintro e mm ⟨⟨ag, i, li, hi, iv, done, fr⟩, ex⟩
    have ex := Option.some.inj (ex.symm.trans (eval_lt (eval_var iv) (hN e mm ag) (by omega) (by omega)))
    have hin : i = n := by
      by_cases hb : i < n
      · rw [ite_eq_left hb] at ex; exact absurd ex (by decide)
      · omega
    subst hin
    exact ⟨ag, iv, done, fun a ha => fr a fun j b1 b2 => ha j b1 b2⟩

end EthLib.Consensus.Ssz.Native.Driver
