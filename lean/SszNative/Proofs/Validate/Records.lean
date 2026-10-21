import SszNative.Proofs.Validate.Fixed

/-! Records of a fixed-size type, checked in one loop, refused exactly as deserializing each would. -/

namespace Ssz.Native

open Ssz

/-- Probes that all pass are refused nowhere. -/
theorem probesPass_ok (b : ByteArray) (start : Nat) :
    ∀ probes, probesPass b start probes = true → checkProbes b start probes = .ok ()
  -- No probes refuse nothing.
  | [], _ => rfl
  -- A passing boolean byte is zero or one, and the rest pass by induction.
  | .bit offset :: rest, pass => by
    simp only [probesPass, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at pass
    simp only [checkProbes, Probe.check, Bind.bind, Except.bind]
    rcases pass.1 with byte | byte <;> simp [byte, probesPass_ok b start rest pass.2]
  -- A passing padding byte has its padding bits clear, and the rest pass by induction.
  | .padding offset bits :: rest, pass => by
    simp only [probesPass, Bool.and_eq_true, beq_iff_eq] at pass
    simp [checkProbes, Probe.check, Bind.bind, Except.bind, pass.1, probesPass_ok b start rest pass.2]

/-- Probes that do not all pass give some refusal. -/
theorem probesPass_fail (b : ByteArray) (start : Nat) :
    ∀ probes, probesPass b start probes = false → ∃ e, checkProbes b start probes = .error e
  -- No probes never fail.
  | [], fail => by simp [probesPass] at fail
  -- A failing boolean probe refuses here, and otherwise the failure is further on.
  | .bit offset :: rest, fail => by
    simp only [checkProbes, Probe.check, Bind.bind, Except.bind]
    by_cases bad : (b.get! (start + offset) != 0 && b.get! (start + offset) != 1) = true
    · simp [bad]
    · simp only [bad, Bool.false_eq_true, ↓reduceIte]
      have : probesPass b start rest = false := by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at bad
        simp only [probesPass, Bool.and_eq_false_iff, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at fail
        rcases fail with ⟨zero, one⟩ | rest
        · exact absurd (bad zero) one
        · exact rest
      exact probesPass_fail b start rest this
  -- A failing padding probe refuses here, and otherwise the failure is further on.
  | .padding offset bits :: rest, fail => by
    simp only [checkProbes, Probe.check, Bind.bind, Except.bind]
    by_cases bad : (b.get! (start + offset) >>> UInt8.ofNat bits != 0) = true
    · simp [bad]
    · simp only [bad, Bool.false_eq_true, ↓reduceIte]
      have : probesPass b start rest = false := by
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at bad
        simp [probesPass, bad] at fail
        exact fail
      exact probesPass_fail b start rest this

/-- The record loop runs the probes repeated over every record. -/
theorem checkRecords_eq (b : ByteArray) (width : Nat) (probes : List Probe) (start : Nat) :
    ∀ index count, checkRecords b width probes (start + index * width) count =
      checkProbes b start (repeatProbes probes width index count)
  -- No records refuse nothing.
  | _, 0 => rfl
  | index, count + 1 => by
    simp only [checkRecords, repeatProbes, checkProbes_append, checkProbes_shift]
    -- A failing record refuses with its probes, and a passing one moves the loop on by one record.
    cases pass : probesPass b (start + index * width) probes
    · obtain ⟨e, refused⟩ := probesPass_fail b _ probes pass
      simp [refused, Bind.bind, Except.bind]
    · rw [probesPass_ok b _ probes pass]
      simp only [↓reduceIte, Bind.bind, Except.bind]
      rw [← checkRecords_eq b width probes start (index + 1) count, Nat.succ_mul, Nat.add_assoc]

/-- Records that all pass are refused nowhere. -/
theorem recordsPass_ok (b : ByteArray) (width : Nat) (probes : List Probe) :
    ∀ start count, recordsPass b width probes start count = true → checkRecords b width probes start count = .ok ()
  | _, 0, _ => rfl
  | start, count + 1, pass => by
    -- The first record passes, so the loop moves on to the rest, which pass too.
    simp only [recordsPass] at pass
    split at pass
    · rename_i first
      simp only [checkRecords, first, ↓reduceIte]
      exact recordsPass_ok b width probes (start + width) count pass
    · exact absurd pass Bool.false_ne_true

/-- A run of records passes when its first part and the rest each pass. -/
theorem recordsPass_append (b : ByteArray) (width : Nat) (probes : List Probe) :
    ∀ start m n, recordsPass b width probes start m = true →
      recordsPass b width probes (start + width * m) n = true → recordsPass b width probes start (m + n) = true
  | start, 0, n, _, rest => by simpa using rest
  | start, m + 1, n, first, rest => by
    -- Peel the first record off both sides.
    simp only [recordsPass] at first
    split at first
    · rename_i head
      rw [Nat.add_right_comm, recordsPass, if_pos head]
      have shifted : start + width + width * m = start + width * (m + 1) := by rw [Nat.mul_succ]; omega
      exact recordsPass_append b width probes (start + width) m n first (by rw [shifted]; exact rest)
    · exact absurd first Bool.false_ne_true

/-- Every run of records passing makes all of them pass. -/
theorem recordsPass_runs (b : ByteArray) (width : Nat) (probes : List Probe) (start count : Nat) :
    ∀ runs, count ≤ recordsPerTask * runs →
      (∀ k < runs, recordsPass b width probes (start + width * (recordsPerTask * k))
        (min recordsPerTask (count - recordsPerTask * k)) = true) →
      recordsPass b width probes start count = true
  | 0, small, _ => by
    -- No runs cover only the empty count.
    have : count = 0 := by omega
    subst this; rfl
  | runs + 1, small, each => by
    by_cases short : count ≤ recordsPerTask * runs
    · exact recordsPass_runs b width probes start count runs short (fun k lt => each k (by omega))
    · -- The last run holds what the earlier runs leave.
      have last := each runs (by omega)
      have head := recordsPass_runs b width probes start (recordsPerTask * runs) runs (Nat.le_refl _)
        (fun k lt => by
          have := each k (by omega)
          rwa [show min recordsPerTask (recordsPerTask * runs - recordsPerTask * k) =
            min recordsPerTask (count - recordsPerTask * k) by
              have : recordsPerTask ≤ recordsPerTask * runs - recordsPerTask * k := by
                rw [← Nat.mul_sub]; exact Nat.le_mul_of_pos_right _ (by omega)
              have : recordsPerTask ≤ count - recordsPerTask * k := by
                have : recordsPerTask * (k + 1) ≤ recordsPerTask * runs := Nat.mul_le_mul_left _ (by omega)
                rw [Nat.mul_succ] at this; omega
              omega])
      have split : count = recordsPerTask * runs + (count - recordsPerTask * runs) := by omega
      rw [split]
      exact recordsPass_append b width probes start _ _ head (by
        rwa [show min recordsPerTask (count - recordsPerTask * runs) = count - recordsPerTask * runs by
          have : count ≤ recordsPerTask * (runs + 1) := small
          rw [Nat.mul_succ] at this; omega] at last)

/-- Checking runs of records in parallel refuses exactly what the record loop refuses. -/
theorem checkAllRecords_eq (b : ByteArray) (width : Nat) (probes : List Probe) (start count : Nat) :
    checkAllRecords b width probes start count = checkRecords b width probes start count := by
  simp only [checkAllRecords]
  split
  · rfl
  split
  · rename_i all
    -- Every run passed, so the whole loop passes too.
    simp only [List.all_eq_true, List.mem_map, List.mem_range] at all
    refine (recordsPass_ok b width probes start count (recordsPass_runs b width probes start count
      ((count + recordsPerTask - 1) / recordsPerTask) (by unfold recordsPerTask; omega) fun k lt => ?_)).symm
    exact all _ ⟨k, lt, rfl⟩
  · rfl

end Ssz.Native
