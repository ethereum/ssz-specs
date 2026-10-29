import SszNative.Proofs.Kernel.Baseline.View
import SszNative.Proofs.Kernel.Avx512.Rounds

/-!
The four-lane kernel's rounds and schedule steps, on one lane.

SSE2 has no rotation, so the code builds each mixing function from shifts.
A right rotation is a right shift or'ed with a left shift, and the two never share a bit.
So the three rotations of a mixing function fold into six shifts joined by exclusive or.
Each shift continues an earlier one in the same direction, so the counts add up along a chain.
-/

namespace EthLib.Consensus.Ssz.Native.Kernel.Baseline

open EthLib.Cryptography.Hash.Sha256 hiding K IV
open EthLib.Consensus.Ssz.Native.Asm
open EthLib.Consensus.Ssz.Native.Kernel.Avx512x2 (View addrOf)
open EthLib.Consensus.Ssz.Native.Kernel.Avx512 (roundT roundsTo roundsTo_succ assign_apply assign_same assign_ne)

/-- Exclusive or of bits can swap its first two terms. -/
theorem bne_left_comm (a b c : Bool) : (a != (b != c)) = (b != (a != c)) := by
  -- Every pattern of the three bits.
  cases a <;> cases b <;> cases c <;> rfl

/-- The round mixing of the fifth working word, as six chained shifts. -/
theorem bigSigma1_shifts (e : UInt32) :
    e >>> (6 : Nat).toUInt32 ^^^ e >>> (6 : Nat).toUInt32 >>> (5 : Nat).toUInt32 ^^^
      e >>> (6 : Nat).toUInt32 >>> (5 : Nat).toUInt32 >>> (14 : Nat).toUInt32 ^^^ e <<< (7 : Nat).toUInt32 ^^^
      e <<< (7 : Nat).toUInt32 <<< (14 : Nat).toUInt32 ^^^
      e <<< (7 : Nat).toUInt32 <<< (14 : Nat).toUInt32 <<< (5 : Nat).toUInt32 = bigSigma1 e := by
  -- Bit by bit, each rotation is its two shifts.
  apply word_ext
  simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
  simp [bigSigma1, rotr, Bool.bne_assoc, bne_comm, bne_left_comm]

/-- The round mixing of the first working word, as six chained shifts. -/
theorem bigSigma0_shifts (a : UInt32) :
    a >>> (2 : Nat).toUInt32 ^^^ a >>> (2 : Nat).toUInt32 >>> (11 : Nat).toUInt32 ^^^
      a >>> (2 : Nat).toUInt32 >>> (11 : Nat).toUInt32 >>> (9 : Nat).toUInt32 ^^^ a <<< (10 : Nat).toUInt32 ^^^
      a <<< (10 : Nat).toUInt32 <<< (9 : Nat).toUInt32 ^^^
      a <<< (10 : Nat).toUInt32 <<< (9 : Nat).toUInt32 <<< (11 : Nat).toUInt32 = bigSigma0 a := by
  -- Bit by bit, each rotation is its two shifts.
  apply word_ext
  simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
  simp [bigSigma0, rotr, Bool.bne_assoc, bne_comm, bne_left_comm]

/-- The schedule mixing of the word two places back, as five chained shifts. -/
theorem sigma1_shifts (w : UInt32) :
    w >>> (10 : Nat).toUInt32 ^^^ w >>> (17 : Nat).toUInt32 ^^^ w >>> (17 : Nat).toUInt32 >>> (2 : Nat).toUInt32 ^^^
      w <<< (13 : Nat).toUInt32 ^^^ w <<< (13 : Nat).toUInt32 <<< (2 : Nat).toUInt32 = smallSigma1 w := by
  -- Bit by bit, each rotation is its two shifts.
  apply word_ext
  simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
  simp [smallSigma1, rotr, shr, Bool.bne_assoc, bne_comm, bne_left_comm]

/-- The schedule mixing of the word fifteen places back, as five chained shifts. -/
theorem sigma0_shifts (w : UInt32) :
    w >>> (3 : Nat).toUInt32 ^^^ w >>> (7 : Nat).toUInt32 ^^^ w >>> (7 : Nat).toUInt32 >>> (11 : Nat).toUInt32 ^^^
      w <<< (14 : Nat).toUInt32 ^^^ w <<< (14 : Nat).toUInt32 <<< (11 : Nat).toUInt32 = smallSigma0 w := by
  -- Bit by bit, each rotation is its two shifts.
  apply word_ext
  simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
  simp [smallSigma0, rotr, shr, Bool.bne_assoc, bne_comm, bne_left_comm]

/-- Majority is c where a and b differ, and their common bit elsewhere. -/
theorem majority_split (a b c : UInt32) : (a ^^^ b) &&& c ^^^ a &&& b = maj a b c := by
  -- Bit by bit, on every pattern of the three inputs.
  apply word_ext
  intro i hi
  simp [maj, hi]
  cases a.toBitVec[i] <;> cases b.toBitVec[i] <;> cases c.toBitVec[i] <;> rfl

/-- Two working-word registers of one round are the same exactly when their words are. -/
theorem role_eq_iff (t j j' : Nat) : (role t j = role t j') = (j % 8 = j' % 8) := by
  -- Both are taken modulo 8.
  apply propext
  simp only [role, home, Fin.ext_iff]
  omega

/-- No working word is a round temporary or a schedule temporary. -/
theorem role_val (t j : Nat) : (role t j).val < 8 := by
  -- Roles are taken modulo 8.
  simp only [role, home]; omega

/-- The next round's word 0 is this round's register for word 7, where the new A is written. -/
theorem role_succ_zero (t : Nat) : role (t + 1) 0 = role t 7 := by
  apply Fin.ext; simp only [role, home]; omega

/-- The next round's word j + 1 is this round's word j. -/
theorem role_succ (t j : Nat) (hj : j < 7) : role (t + 1) (j + 1) = role t j := by
  apply Fin.ext; simp only [role, home]; omega

/-- A register below 8 is none of the round's or the schedule's temporaries. -/
theorem low_ne (r : Vreg) (low : r.val < 8) :
    (r = t1) = False ∧ (t1 = r) = False ∧ (r = x) = False ∧ (x = r) = False ∧ (r = y) = False ∧ (y = r) = False ∧
      (r = z) = False ∧ (z = r) = False := by
  -- The temporaries are registers 8 to 11, so their numbers differ from any below 8.
  have apart : ∀ s : Vreg, 8 ≤ s.val → (r = s) = False ∧ (s = r) = False := fun s hs =>
    ⟨eq_false fun e => by rw [e] at low; omega, eq_false fun e => by rw [← e] at low; omega⟩
  obtain ⟨a1, a2⟩ := apart t1 (by decide)
  obtain ⟨b1, b2⟩ := apart x (by decide)
  obtain ⟨c1, c2⟩ := apart y (by decide)
  obtain ⟨d1, d2⟩ := apart z (by decide)
  exact ⟨a1, a2, b1, b2, c1, c2, d1, d2⟩

/-- The round's temporaries are four distinct registers. -/
theorem temps_ne :
    (x = t1) = False ∧ (t1 = x) = False ∧ (y = t1) = False ∧ (t1 = y) = False ∧ (z = t1) = False ∧
      (t1 = z) = False ∧ (x = y) = False ∧ (y = x) = False ∧ (x = z) = False ∧ (z = x) = False ∧
      (y = z) = False ∧ (z = y) = False := by
  -- Registers 8 to 11, compared by evaluation.
  simp only [eq_iff_iff, iff_false]
  decide

set_option maxHeartbeats 4000000 in
/-- A round's tail on one lane: the new A in word 7's register, the new E in word 3's, and the rest kept. -/
theorem tail_regs (G : Gpr → UInt64) (v : View) (t : Nat) :
    let w := fun j => v.regs (role t j)
    let sum := v.regs t1 + ch (w 4) (w 5) (w 6) + bigSigma1 (w 4)
    (viewRun G (roundTail t) v).regs (role t 7) = sum + (bigSigma0 (w 0) + maj (w 0) (w 1) (w 2)) ∧
    (viewRun G (roundTail t) v).regs (role t 3) = w 3 + sum ∧
    ∀ j, j < 7 → j ≠ 3 → (viewRun G (roundTail t) v).regs (role t j) = w j := by
  intro w sum
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩ := temps_ne
  have ne := fun i => low_ne (role t i) (role_val t i)
  -- Each register read resolves to one earlier write, the shifts fold into the mixing functions, and the sums agree.
  refine ⟨?_, ?_, fun j hj h3 => ?_⟩
  rotate_right
  · have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [roundTail, mix, List.cons_append, List.nil_append, viewRun, viewStep, assign_apply, role_eq_iff,
      n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, (ne _).1, (ne _).2.1, (ne _).2.2.1, (ne _).2.2.2.1,
      (ne _).2.2.2.2.1, (ne _).2.2.2.2.2.1, (ne _).2.2.2.2.2.2.1, (ne _).2.2.2.2.2.2.2, ite_true, ite_false,
      Nat.reduceMod, Nat.reduceEqDiff, w]
  all_goals
    simp only [roundTail, mix, List.cons_append, List.nil_append, viewRun, viewStep, assign_apply, role_eq_iff,
      n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, (ne _).1, (ne _).2.1, (ne _).2.2.1, (ne _).2.2.2.1,
      (ne _).2.2.2.2.1, (ne _).2.2.2.2.2.1, (ne _).2.2.2.2.2.2.1, (ne _).2.2.2.2.2.2.2, ite_true, ite_false,
      Nat.reduceSub, Nat.reduceLT, Nat.reduceMod, Nat.reduceEqDiff, bigSigma1_shifts, bigSigma0_shifts]
    try rw [majority_split]
    simp only [sum, w, ch]
    ac_rfl

/-- A round's tail on one lane takes the working words one round on, from the seeded sum. -/
theorem tail_view (G : Gpr → UInt64) (v : View) (t : Nat) :
    (Vector.ofFn fun j : Fin 8 => (viewRun G (roundTail t) v).regs (role (t + 1) j)) =
      roundT (Vector.ofFn fun j : Fin 8 => v.regs (role t j)) (v.regs t1) := by
  obtain ⟨h7, h3, keep⟩ := tail_regs G v t
  -- The new A sits in word 7's register, the new E in word 3's, and every other word one place along.
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn, roundT]
  match j, hj with
  | 0, _ => rw [role_succ_zero, h7]; simp
  | 1, _ => rw [role_succ t 0 (by omega), keep 0 (by omega) (by omega)]; simp
  | 2, _ => rw [role_succ t 1 (by omega), keep 1 (by omega) (by omega)]; simp
  | 3, _ => rw [role_succ t 2 (by omega), keep 2 (by omega) (by omega)]; simp
  | 4, _ => rw [role_succ t 3 (by omega), h3]; simp
  | 5, _ => rw [role_succ t 4 (by omega), keep 4 (by omega) (by omega)]; simp
  | 6, _ => rw [role_succ t 5 (by omega), keep 5 (by omega) (by omega)]; simp
  | 7, _ => rw [role_succ t 6 (by omega), keep 6 (by omega) (by omega)]; simp

/-- A round's tail stores nothing. -/
theorem tail_mem (G : Gpr → UInt64) (v : View) (t : Nat) : (viewRun G (roundTail t) v).mem = v.mem := by
  -- No instruction of a round is a store.
  funext a
  apply viewRun_mem_other
  simp [roundTail, mix, storeOf]

/-- A round's tail leaves the schedule step's registers alone. -/
theorem tail_high (G : Gpr → UInt64) (v : View) (t : Nat) (r : Vreg) (high : 12 ≤ r.val) :
    (viewRun G (roundTail t) v).regs r = v.regs r := by
  -- A round writes only working words and registers 8 to 11.
  apply viewRun_regs_other
  have h0 := role_val t 0
  have h3 := role_val t 3
  have h7 := role_val t 7
  simp only [roundTail, mix, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, destOf, ne_eq, Option.some.injEq, Fin.ext_iff, t1, x, y, z]
  and_intros <;> (try simp) <;> omega

/-- Roles depend only on the round modulo 8. -/
theorem role_mod (i k j : Nat) (hk : k < 8) : role (8 * i + k) j = role k j := by
  apply Fin.ext; simp only [role, home]; omega

/-- One lane of the first block before round t: the working words, and the schedule words stored so far. -/
def FirstInv (S : Nat) (m : ByteArray) (t : Nat) (v : View) : Prop :=
  (Vector.ofFn fun j : Fin 8 => v.regs (role t j)) = roundsTo Cryptography.Hash.Sha256.IV Avx512.K (Avx512.W m) t ∧
  ∀ u < 64, u < t + 16 → v.mem (S + wordSlot u) = Avx512.W m u

/-- Word 8i + m of block i, read through the schedule pointer, is the scratch area's word. -/
theorem wordRel_slot (S i m : Nat) (hi : i < 8) (hm : m < 24) :
    S + wordsBase i + wordRel m = S + wordSlot (8 * i + m) := by
  simp only [wordsBase, wordRel, wordSlot, frame]; omega

/-- Distinct schedule words sit in distinct rows. -/
theorem wordSlot_inj (S u u' : Nat) (hu : u < 80) (hu' : u' < 80) (h : S + wordSlot u = S + wordSlot u') : u = u' := by
  simp only [wordSlot, frame] at h; omega

/-- The schedule step's reads and its store, on one lane: the next word from four earlier ones. -/
theorem schedule_view (G : Gpr → UInt64) (v : View) (k : Nat) :
    (viewRun G (scheduleStep k) v).mem = assign v.mem ((G words).toNat + wordRel (k + 16))
      (smallSigma1 (v.mem ((G words).toNat + wordRel (k + 14))) + smallSigma0 (v.mem ((G words).toNat + wordRel (k + 1))) +
        v.mem ((G words).toNat + wordRel k) + v.mem ((G words).toNat + wordRel (k + 9))) ∧
    ∀ r : Vreg, r.val < 12 → (viewRun G (scheduleStep k) v).regs r = v.regs r := by
  have r12 : ∀ r : Vreg, r.val < 12 → (r = sa) = False ∧ (r = sb) = False ∧ (r = sc) = False ∧ (r = sd) = False :=
    fun r hr => ⟨eq_false fun e => by subst e; exact absurd hr (by decide),
      eq_false fun e => by subst e; exact absurd hr (by decide),
      eq_false fun e => by subst e; exact absurd hr (by decide), eq_false fun e => by subst e; exact absurd hr (by decide)⟩
  refine ⟨?_, fun r hr => ?_⟩
  · -- The two mixings are computed into registers, summed with two more words, and stored.
    simp only [scheduleStep, viewRun, viewStep, assign_apply, addrOf]
    simp (config := { decide := true }) only [sa, sb, sc, sd, ite_true, ite_false]
    rw [sigma1_shifts, sigma0_shifts]
  · obtain ⟨a1, a2, a3, a4⟩ := r12 r hr
    simp only [scheduleStep, viewRun, viewStep, assign_apply, a1, a2, a3, a4, ite_false]

/-- One first-block round and, early on, its schedule step keep the invariant one round on. -/
theorem first_step (G : Gpr → UInt64) (v : View) (S : Nat) (m : ByteArray) (i k : Nat) (hi : i < 8) (hk : k < 8)
    (sched : Bool) (hs : sched = decide (i < 6)) (wordsAt : (G words).toNat = S + wordsBase i)
    (konst : v.mem ((G consts).toNat + 64 * k) = Avx512.K (8 * i + k)) (inv : FirstInv S m (8 * i + k) v) :
    FirstInv S m (8 * i + k + 1) (viewRun G (firstRound k ++ (if sched then scheduleStep k else [])) v) ∧
    ∀ a, (∀ u < 64, a ≠ S + wordSlot u) →
      (viewRun G (firstRound k ++ (if sched then scheduleStep k else [])) v).mem a = v.mem a := by
  obtain ⟨roles, words'⟩ := inv
  have t1ne : ∀ j, (role k j = t1) = False := fun j => (low_ne _ (role_val k j)).1
  -- The seeds: the schedule word, plus H, plus the constant.
  let v1 := viewRun G [.movdqu t1 ⟨words, wordRel k⟩, .paddd t1 (role k 7), .padddMem t1 ⟨consts, 64 * k⟩] v
  have v1t1 : v1.regs t1 = Avx512.W m (8 * i + k) + v.regs (role k 7) + Avx512.K (8 * i + k) := by
    simp only [v1, viewRun, viewStep, assign_apply, ite_true, t1ne, ite_false, addrOf]
    rw [← konst, show (G words).toNat + wordRel k = S + wordSlot (8 * i + k) by
      rw [wordsAt]; exact wordRel_slot S i k hi (by omega), words' _ (by omega) (by omega)]
  have v1roles : ∀ j, v1.regs (role k j) = v.regs (role k j) := fun j => by
    simp only [v1, viewRun, viewStep, assign_apply, t1ne, ite_false]
  have v1mem : v1.mem = v.mem := rfl
  have split : firstRound k =
    [.movdqu t1 ⟨words, wordRel k⟩, .paddd t1 (role k 7), .padddMem t1 ⟨consts, 64 * k⟩] ++ roundTail k := rfl
  -- The schedule step changes no working word.
  let v2 := viewRun G (roundTail k) v1
  have hv2 : viewRun G (firstRound k ++ (if sched then scheduleStep k else [])) v =
      viewRun G (if sched then scheduleStep k else []) v2 := by
    rw [viewRun_append, split, viewRun_append]
  have schedRegs : ∀ r : Vreg, r.val < 12 → (viewRun G (if sched then scheduleStep k else []) v2).regs r = v2.regs r :=
    fun r hr => by split; exact (schedule_view G v2 k).2 r hr; rfl
  have v2def : v2 = viewRun G (roundTail k) v1 := rfl
  have v2mem : v2.mem = v.mem := by rw [v2def, tail_mem, v1mem]
  clear_value v2 v1
  refine ⟨⟨?_, ?_⟩, fun a ha => ?_⟩
  · -- The working words take one round, from the seeded sum.
    rw [hv2]
    have e : ∀ j : Fin 8, (viewRun G (if sched then scheduleStep k else []) v2).regs (role (8 * i + k + 1) j) =
        v2.regs (role (k + 1) j) := fun j => by
      rw [schedRegs _ (by have := role_val (8 * i + k + 1) j; omega)]
      rw [show role (8 * i + k + 1) j = role (k + 1) j by apply Fin.ext; simp only [role, home]; omega]
    have st : (Vector.ofFn fun j : Fin 8 => v1.regs (role k j)) =
        Vector.ofFn fun j : Fin 8 => v.regs (role (8 * i + k) j) := by
      apply Vector.ext; intro j hj; simp only [Vector.getElem_ofFn, v1roles, role_mod i k _ hk]
    have sum : v1.regs t1 = (Vector.ofFn fun j : Fin 8 => v.regs (role (8 * i + k) j))[7] +
        Avx512.K (8 * i + k) + Avx512.W m (8 * i + k) := by
      rw [v1t1, Vector.getElem_ofFn, role_mod i k _ hk]; ac_rfl
    simp only [e]
    rw [v2def, tail_view, Avx512.roundsTo_succ, ← roles, Avx512.round_eq_roundT, st, sum]
  · -- Each stored word is kept, or is the word the schedule step just computed.
    intro u hu hut
    rw [hv2]
    split
    · rename_i on
      have early : 8 * i + k < 48 := by rw [hs] at on; simp at on; omega
      rw [(schedule_view G v2 k).1, v2mem, assign_apply]
      have at16 : (G words).toNat + wordRel (k + 16) = S + wordSlot (8 * i + k + 16) := by
        rw [wordsAt]; exact wordRel_slot S i (k + 16) hi (by omega)
      rw [at16]
      split
      · rename_i same
        have := wordSlot_inj S u (8 * i + k + 16) (by omega) (by omega) same
        subst this
        have a14 : (G words).toNat + wordRel (k + 14) = S + wordSlot (8 * i + k + 14) := by
          rw [wordsAt]; exact wordRel_slot S i (k + 14) hi (by omega)
        have a1 : (G words).toNat + wordRel (k + 1) = S + wordSlot (8 * i + k + 1) := by
          rw [wordsAt]; exact wordRel_slot S i (k + 1) hi (by omega)
        have a0 : (G words).toNat + wordRel k = S + wordSlot (8 * i + k) := by
          rw [wordsAt]; exact wordRel_slot S i k hi (by omega)
        have a9 : (G words).toNat + wordRel (k + 9) = S + wordSlot (8 * i + k + 9) := by
          rw [wordsAt]; exact wordRel_slot S i (k + 9) hi (by omega)
        rw [a14, a1, a0, a9, words' _ (by omega) (by omega), words' _ (by omega) (by omega),
          words' _ (by omega) (by omega), words' _ (by omega) (by omega), Avx512.W_next m _ early]
        ac_rfl
      · rename_i other
        have : u < 8 * i + k + 16 := by
          by_cases lt : u < 8 * i + k + 16
          · exact lt
          · exact absurd (by omega : u = 8 * i + k + 16) (fun e => other (by rw [e]))
        exact words' u hu (by omega)
    · rename_i off
      have late : 48 ≤ 8 * i + k := by rw [hs] at off; simp at off; omega
      simp only [viewRun]
      rw [v2mem]
      exact words' u hu (by omega)
  · -- No other row changes.
    rw [hv2]
    split
    · rename_i on
      have early : 8 * i + k < 48 := by rw [hs] at on; simp at on; omega
      rw [(schedule_view G v2 k).1, v2mem, assign_apply, wordsAt, wordRel_slot S i (k + 16) hi (by omega),
        ite_eq_right (ha _ (by omega))]
    · simp only [viewRun]; rw [v2mem]

/-- Eight first-block rounds keep the invariant eight rounds on, and change no row outside the schedule words. -/
theorem first_block (G : Gpr → UInt64) (v : View) (S : Nat) (m : ByteArray) (i : Nat) (hi : i < 8)
    (sched : Bool) (hs : sched = decide (i < 6)) (wordsAt : (G words).toNat = S + wordsBase i)
    (konst : ∀ k < 8, v.mem ((G consts).toNat + 64 * k) = Avx512.K (8 * i + k))
    (far : ∀ k < 8, ∀ u < 64, (G consts).toNat + 64 * k ≠ S + wordSlot u) (inv : FirstInv S m (8 * i) v) :
    let body := (List.range 8).flatMap fun k => firstRound k ++ (if sched then scheduleStep k else [])
    FirstInv S m (8 * i + 8) (viewRun G body v) ∧
    ∀ a, (∀ u < 64, a ≠ S + wordSlot u) → (viewRun G body v).mem a = v.mem a := by
  intro body
  -- Induction on the rounds within the block, one step at a time.
  suffices key : ∀ n ≤ 8, FirstInv S m (8 * i + n)
      (viewRun G ((List.range n).flatMap fun k => firstRound k ++ (if sched then scheduleStep k else [])) v) ∧
      ∀ a, (∀ u < 64, a ≠ S + wordSlot u) →
        (viewRun G ((List.range n).flatMap fun k => firstRound k ++ (if sched then scheduleStep k else [])) v).mem a =
          v.mem a from key 8 (Nat.le_refl _)
  intro n hn
  induction n with
  | zero => exact ⟨inv, fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨inv', other⟩ := ih (by omega)
    rw [viewRun_flatMap_succ]
    obtain ⟨next, other'⟩ := first_step G _ S m i n hi (by omega) sched hs wordsAt
      (by rw [other _ (far n (by omega))]; exact konst n (by omega)) inv'
    exact ⟨next, fun a ha => (other' a ha).trans (other a ha)⟩

/-- One lane of the padding block before round t: the working words, and the first block's result in memory. -/
def PadInv (S : Nat) (mid : Vector UInt32 8) (t : Nat) (v : View) : Prop :=
  (Vector.ofFn fun j : Fin 8 => v.regs (role t j)) = roundsTo mid Avx512.K Avx512.PW t ∧
  ∀ j < 8, v.mem (S + midSlot j) = mid[j]!

/-- A padding round keeps the invariant one round on, and stores nothing. -/
theorem pad_step (G : Gpr → UInt64) (v : View) (S : Nat) (mid : Vector UInt32 8) (i k : Nat) (hk : k < 8)
    (konst : v.mem ((G consts).toNat + 64 * k) = Avx512.K (8 * i + k) + Avx512.PW (8 * i + k))
    (inv : PadInv S mid (8 * i + k) v) :
    PadInv S mid (8 * i + k + 1) (viewRun G (paddingRound k) v) ∧ (viewRun G (paddingRound k) v).mem = v.mem := by
  obtain ⟨roles, mids⟩ := inv
  have t1ne : ∀ j, (role k j = t1) = False := fun j => (low_ne _ (role_val k j)).1
  -- The seed: H plus the table's precomputed word and constant.
  let v1 := viewRun G [.movdqa t1 (role k 7), .padddMem t1 ⟨consts, 64 * k⟩] v
  have v1t1 : v1.regs t1 = v.regs (role k 7) + (Avx512.K (8 * i + k) + Avx512.PW (8 * i + k)) := by
    simp only [v1, viewRun, viewStep, assign_apply, ite_true, addrOf]; rw [konst]
  have v1roles : ∀ j, v1.regs (role k j) = v.regs (role k j) := fun j => by
    simp only [v1, viewRun, viewStep, assign_apply, t1ne, ite_false]
  have v1mem : v1.mem = v.mem := rfl
  have run : viewRun G (paddingRound k) v = viewRun G (roundTail k) v1 := rfl
  clear_value v1
  have mem : (viewRun G (paddingRound k) v).mem = v.mem := by rw [run, tail_mem, v1mem]
  refine ⟨⟨?_, fun j hj => by rw [mem]; exact mids j hj⟩, mem⟩
  have st : (Vector.ofFn fun j : Fin 8 => v1.regs (role k j)) =
      Vector.ofFn fun j : Fin 8 => v.regs (role (8 * i + k) j) := by
    apply Vector.ext; intro j hj; simp only [Vector.getElem_ofFn, v1roles, role_mod i k _ hk]
  have sum : v1.regs t1 = (Vector.ofFn fun j : Fin 8 => v.regs (role (8 * i + k) j))[7] +
      Avx512.K (8 * i + k) + Avx512.PW (8 * i + k) := by
    rw [v1t1, Vector.getElem_ofFn, role_mod i k _ hk]; ac_rfl
  have e : ∀ j : Fin 8, (viewRun G (roundTail k) v1).regs (role (8 * i + k + 1) j) =
      (viewRun G (roundTail k) v1).regs (role (k + 1) j) := fun j => by
    rw [show role (8 * i + k + 1) j = role (k + 1) j by apply Fin.ext; simp only [role, home]; omega]
  rw [run]
  simp only [e]
  rw [tail_view, Avx512.roundsTo_succ, ← roles, Avx512.round_eq_roundT, st, sum]

/-- Eight padding rounds keep the invariant eight rounds on, and store nothing. -/
theorem pad_block (G : Gpr → UInt64) (v : View) (S : Nat) (mid : Vector UInt32 8) (i : Nat)
    (konst : ∀ k < 8, v.mem ((G consts).toNat + 64 * k) = Avx512.K (8 * i + k) + Avx512.PW (8 * i + k))
    (inv : PadInv S mid (8 * i) v) :
    PadInv S mid (8 * i + 8) (viewRun G ((List.range 8).flatMap paddingRound) v) ∧
      (viewRun G ((List.range 8).flatMap paddingRound) v).mem = v.mem := by
  -- Induction on the rounds within the block, one step at a time.
  suffices key : ∀ n ≤ 8, PadInv S mid (8 * i + n) (viewRun G ((List.range n).flatMap paddingRound) v) ∧
      (viewRun G ((List.range n).flatMap paddingRound) v).mem = v.mem from key 8 (Nat.le_refl _)
  intro n hn
  induction n with
  | zero => exact ⟨inv, rfl⟩
  | succ n ih =>
    obtain ⟨inv', same⟩ := ih (by omega)
    rw [viewRun_flatMap_succ]
    obtain ⟨next, same'⟩ := pad_step G _ S mid i n (by omega) (by rw [same]; exact konst n (by omega)) inv'
    exact ⟨next, same'.trans same⟩

end EthLib.Consensus.Ssz.Native.Kernel.Baseline
