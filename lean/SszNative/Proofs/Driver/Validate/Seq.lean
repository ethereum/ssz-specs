import SszNative.Proofs.Driver.Validate.Each
import SszNative.Proofs.Validate.Records

/-!
Sequences: a fixed count of variable-size elements, and a counted sequence of either kind.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr

/-- A table whose spans were accepted is in order, its last offset within the size. -/
theorem spans_ok_facts : ∀ (l : List Nat) (size : Nat) (sp : List Nat), offsetSpans l size = .ok sp →
    OrdUpTo l l.length ∧ (l ≠ [] → l[l.length - 1]! ≤ size)
  | [], _, _, _ => ⟨fun k _ ki _ => absurd ki (by simp), fun h => absurd rfl h⟩
  | [s], size, sp, h => by
    simp only [offsetSpans] at h
    split at h
    · cases h
    · exact ⟨fun k kp ki _ => absurd ki (by simp; omega), fun _ => by simp; omega⟩
  | s :: n :: rest, size, sp, h => by
    simp only [offsetSpans] at h
    split at h
    · cases h
    · rename_i sn
      cases hr : offsetSpans (n :: rest) size with
      | error x => rw [hr] at h; cases h
      | ok sp' =>
        obtain ⟨ord, last⟩ := spans_ok_facts (n :: rest) size sp' hr
        refine ⟨fun k kp ki kl => ?_, fun _ => ?_⟩
        · by_cases k1 : k = 1
          · subst k1; simp; omega
          · have := ord (k - 1) (by omega) (by simp at ki ⊢; omega) (by simp at kl ⊢; omega)
            rw [cons_getElem! s (n :: rest) k kp, cons_getElem! s (n :: rest) (k - 1) (by omega)]
            simpa [show k - 1 - 1 = k - 2 by omega] using this
        · have := last (by simp)
          simpa [show rest.length + 1 + 1 - 1 = rest.length + 1 by omega] using this

/-- The listed elements of a table that checks out: the bodies of its spans, offset to offset. -/
theorem validate_bodies (e : Desc) (b : ByteArray) (start size : Nat) (l : List Nat) :
    (do let spans ← offsetSpans l size; validateEach e b (bodies start l spans)) =
      match spansOutcome l size with
      | .error x => .error x
      | .ok _ => validateEach e b ((List.range l.length).map (bodyRange l size start)) := by
  cases h : offsetSpans l size with
  | error x => simp [spansOutcome, h, Bind.bind, Except.bind, Except.map]
  | ok sp =>
    obtain ⟨ord, last⟩ := spans_ok_facts l size sp h
    obtain ⟨sp', h', hb⟩ := offsetSpans_ok start l size ord last
    rw [h] at h'; cases h'
    simp [spansOutcome, h, Bind.bind, Except.bind, Except.map, hb]

/-- A fixed count of variable-size elements, refused case by case. -/
theorem vector_outcome (e : Desc) (n : Nat) (b : ByteArray) (start stop : Nat) (hw : hasWidth e = false) :
    (do let r ← vectorRanges e n b start stop; validateRanges e b r) =
      if 2 ^ 32 ≤ stop - start then .error (.offsetOverflow (stop - start))
      else if stop - start < n * 4 then .error (.scopeTooSmall (n * 4) (stop - start))
      else if n = 0 then .ok ()
      else if offsetAt b start ≠ n * 4 then .error (.firstOffset (n * 4) (offsetAt b start))
      else match spansOutcome (tableOffsets b start n) (stop - start) with
        | .error x => .error x
        | .ok _ => validateEach e b ((List.range n).map
            (bodyRange (tableOffsets b start n) (stop - start) start)) := by
  have none : e.fixedSize = none := by rw [fixedSize_eq, hw]; rfl
  have ob : offsetBound = 2 ^ 32 := rfl
  simp only [vectorRanges, none, ob, bytesPerOffset]
  by_cases o : 2 ^ 32 ≤ stop - start
  · simp [o, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  · simp only [o, ite_false]
    by_cases s : stop - start < n * 4
    · simp [s, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    · simp only [s, ite_false]
      by_cases z : n = 0
      · subst z; simp [Bind.bind, Except.bind, pure, Except.pure, validateRanges, validateEach]
      · have first : ((List.range n).map fun i => offsetAt b (start + i * 4))[0]! = offsetAt b start := by
          rw [getElem!_pos _ 0 (by simp; omega)]; simp
        by_cases f : offsetAt b start ≠ n * 4
        · simp [z, first, f, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
        · simp only [ne_eq, Decidable.not_not] at f
          have tl := tableOffsets_length b start n
          have key := validate_bodies e b start (stop - start) (tableOffsets b start n)
          rw [tl] at key
          simp only [tableOffsets, bytesPerOffset] at key ⊢
          simp only [z, first, f, ite_false, ne_eq, not_true_eq_false, beq_iff_eq]
          rw [← key]
          cases offsetSpans ((List.range n).map fun i => offsetAt b (start + i * 4)) (stop - start) <;>
            simp [Bind.bind, Except.bind, pure, Except.pure, validateRanges]

/-- The spans' outcome, when accepted, leaves the table in order with its last offset within the size. -/
theorem spansOutcome_ok (l : List Nat) (size : Nat) (h : spansOutcome l size = .ok ()) :
    OrdUpTo l l.length ∧ (l ≠ [] → l[l.length - 1]! ≤ size) := by
  cases hs : offsetSpans l size with
  | error x => simp [spansOutcome, hs, Except.map] at h
  | ok sp => exact spans_ok_facts l size sp hs

set_option maxHeartbeats 2000000 in
/-- Checking a fixed count of variable-size elements natively refuses exactly as the Lean check does. -/
theorem vector_calls {m : Module} {w : World} (hm : Loaded m) (e : Desc) (n : Nat) (ih : RangeOk m w e)
    (fit : fitsNative (.vector e n) = true) (hw : hasWidth e = false) (p sp : Nat) (mem : Memory) (base : Nat)
    (b : ByteArray) (start stop err : Nat) (hp : PlanAt w mem p (Plan.words (.vector e n)))
    (cp : Clear err p (8 * (Plan.words (.vector e n)).length)) (hd : DataAt w mem base b) (cd : Clear err base b.size)
    (ok : w.access err 32 = true) (hle : start ≤ stop) (hs : stop ≤ b.size) (small : b.size < 2 ^ 60)
    (room : Room w sp (Desc.vector e n).nesting 3) :
    Calls m w "ssz_validate_vector" sp [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (base + stop),
      UInt64.ofNat err] mem
      (res (do let r ← vectorRanges e n b start stop; validateRanges e b r))
      (after mem err (do let r ← vectorRanges e n b start stop; validateRanges e b r)) := by
  have hb := hp.bound
  have db := hd.bound
  have eb : err + 32 ≤ 2 ^ 63 := by
    have := ok; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  have r1 := hp.read 8 rfl (by simp [Plan.words])
  have a1 := hp.readable 8 rfl (by simp [Plan.words])
  simp [Plan.words] at r1 hb
  simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
  have he : PlanAt w mem (p + 16) (Plan.words e) := by
    have := hp.right (a := [7, n]) (b := Plan.words e); simpa using this
  have ce : Clear err (p + 16) (8 * (Plan.words e).length) := by
    simp [Plan.words] at cp; unfold Clear at cp ⊢; omega
  have hsz : base + stop - (base + start) = stop - start := by omega
  rw [vector_outcome e n b start stop hw]
  refine Calls.body 13 hm.vector rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [vectorFn]
  wsteps [hsz]
  by_cases o : 2 ^ 32 ≤ stop - start
  · wsteps [hsz, o]
    wfail []
    wsteps []
    wfin [o, res, after, wrote_eq]
  · wsteps [hsz, o, r1, a1]
    by_cases s : stop - start < n * 4
    · wsteps [s]
      wfail []
      wsteps []
      wfin [o, s, res, after, wrote_eq]
    · by_cases z : n = 0
      · subst z
        wsteps [s]
        wfin [o, s, res, after]
      · have r0 := hd.offset start (by omega)
        have a0 := hd.offsetOk start (by omega)
        have o0 := offsetAt_lt b start
        by_cases f : offsetAt b start ≠ n * 4
        · wsteps [s, z, r0, a0, f]
          wfail [r0, a0]
          wsteps []
          wfin [o, s, z, f, res, after, wrote_eq]
        · simp only [ne_eq, Decidable.not_not] at f
          have spans := spans_calls hm mem base b start n (stop - start) err (sp - 8 - 8 * 13) (by omega) (by omega)
            hd ok (by simp only [Room] at room ⊢; omega)
          wsteps [s, z, r0, a0, f]
          wcall spans []
          rcases hS : spansOutcome (tableOffsets b start n) (stop - start) with x | u
          · wsteps [res]
            wfin [o, s, z, f, hS, res, after]
          · obtain ⟨ord, last⟩ := spansOutcome_ok _ _ hS
            rw [tableOffsets_length] at ord last
            have each := each_calls hm e ih fit.1.1 (p + 16) (sp - 8 - 8 * 13) mem base b start n (stop - start) err
              he ce hd cd ok (by omega) (by omega) small ord (fun nz => last (by
                intro h; have := congrArg List.length h; simp [tableOffsets_length] at this; omega))
              (by simp only [Room, Desc.nesting] at room ⊢; omega)
            wsteps [res]
            wcall each []
            wsteps []
            wfin [o, s, z, f, hS, res, after]

/-- Records with no probes refuse nothing. -/
theorem seqR_nil (b : ByteArray) (w : Nat) : ∀ s c, seqR b w [] s c = .ok ()
  | _, 0 => rfl
  | s, c + 1 => by simp only [seqR, checkProbes]; exact seqR_nil b w (s + w) c

/-- Elements one width apart are checked by the element's probes over every record. -/
theorem validateRanges_stride (e : Desc) (b : ByteArray) (start w count : Nat) :
    validateRanges e b (.stride start w count) = seqR b w (plan e) start count := by
  rw [validateRanges]
  split
  · rename_i h; rw [h, seqR_nil]
  · rw [checkAllRecords_eq]
    have := checkRecords_eq b w (plan e) start 0 count
    simp only [Nat.zero_mul, Nat.add_zero] at this
    rw [this, checkProbes_repeat, Nat.zero_mul, Nat.add_zero]

/-- Whether a count is past a limit given as its presence and its value. -/
def Over (has lim count : Nat) : Prop := has ≠ 0 ∧ lim < count

/-- Whether the property holds, decided. -/
instance (has lim count : Nat) : Decidable (Over has lim count) := by unfold Over; infer_instance

/-- A counted sequence, refused case by case. -/
theorem list_outcome (e : Desc) (has lim : Nat) (b : ByteArray) (start stop : Nat) :
    (do let r ← listRanges e (Plan.readBound has lim) b start stop; validateRanges e b r) =
      if 2 ^ 32 ≤ stop - start then .error (.offsetOverflow (stop - start))
      else if stop - start = 0 then .ok ()
      else if hasWidth e then
        if fixedWidth e = 0 then .error .scopeWidthless
        else if (stop - start) % fixedWidth e ≠ 0 then .error (.scopeUndivided (stop - start) (fixedWidth e))
        else if Over has lim ((stop - start) / fixedWidth e) then
          .error (.overLimit lim ((stop - start) / fixedWidth e))
        else seqR b (fixedWidth e) (plan e) start ((stop - start) / fixedWidth e)
      else if stop - start < 4 then .error (.scopeTooSmall 4 (stop - start))
      else if offsetAt b start < 4 then .error .offsetBelowTable
      else if offsetAt b start % 4 ≠ 0 then .error .offsetUnaligned
      else if stop - start < offsetAt b start then .error .offsetPastScope
      else if Over has lim (offsetAt b start / 4) then .error (.overLimit lim (offsetAt b start / 4))
      else match spansOutcome (tableOffsets b start (offsetAt b start / 4)) (stop - start) with
        | .error x => .error x
        | .ok _ => validateEach e b ((List.range (offsetAt b start / 4)).map
            (bodyRange (tableOffsets b start (offsetAt b start / 4)) (stop - start) start)) := by
  have ob : offsetBound = 2 ^ 32 := rfl
  by_cases o : 2 ^ 32 ≤ stop - start
  · simp [listRanges, ob, o, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  by_cases z : stop - start = 0
  · simp [listRanges, ob, z, Bind.bind, Except.bind, pure, Except.pure, validateRanges, validateEach]
  by_cases hw : hasWidth e = true
  · have fs : e.fixedSize = some (fixedWidth e) := by rw [fixedSize_eq, ite_eq_left hw]
    by_cases w0 : fixedWidth e = 0
    · simp [listRanges, ob, o, z, fs, w0, hw, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    have hmod : (stop - start) % fixedWidth e ≤ stop - start := Nat.mod_le _ _
    have cnt : (stop - start) / fixedWidth e ≤ stop - start := Nat.div_le_self _ _
    by_cases d : (stop - start) % fixedWidth e ≠ 0
    · simp [listRanges, ob, o, z, fs, w0, hw, d, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    simp only [ne_eq, Decidable.not_not] at d
    simp only [listRanges, ob, fs, ge_iff_le, o, ite_false, beq_iff_eq, z, w0, bne_iff_ne, ne_eq, d,
      not_true_eq_false, hw, ite_true]
    simp only [Bind.bind, Except.bind, pure, Except.pure, Over, Plan.readBound]
    by_cases hh : has = 0
    · simp [hh, validateRanges_stride]
    · by_cases oo : lim < (stop - start) / fixedWidth e
      · simp [hh, oo, throw, throwThe, MonadExceptOf.throw]
      · simp [hh, oo, validateRanges_stride]
  · have fs : e.fixedSize = none := by rw [fixedSize_eq, ite_eq_right hw]
    simp only [listRanges, ob, fs, ge_iff_le, o, ite_false, beq_iff_eq, z, hw, bytesPerOffset, Bool.false_eq_true]
    by_cases s4 : stop - start < 4
    · simp [s4, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    by_cases f4 : offsetAt b start < 4
    · simp [s4, f4, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    by_cases fa : offsetAt b start % 4 ≠ 0
    · simp [s4, f4, fa, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    simp only [ne_eq, Decidable.not_not] at fa
    by_cases fp : stop - start < offsetAt b start
    · simp [s4, f4, fa, fp, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    have key := validate_bodies e b start (stop - start) (tableOffsets b start (offsetAt b start / 4))
    rw [tableOffsets_length] at key
    simp only [tableOffsets, bytesPerOffset] at key
    simp only [s4, f4, fa, fp, ite_false, bne_iff_ne, ne_eq, not_true_eq_false, gt_iff_lt, Over, Plan.readBound,
      Bind.bind, Except.bind, pure, Except.pure, tableOffsets, bytesPerOffset]
    by_cases hh : has = 0
    · simp only [hh, beq_self_eq_true, ite_true]
      rw [← key]
      cases offsetSpans ((List.range (offsetAt b start / 4)).map fun i => offsetAt b (start + i * 4)) (stop - start) <;>
        simp [Bind.bind, Except.bind, validateRanges]
    · by_cases oo : lim < offsetAt b start / 4
      · simp [hh, oo, throw, throwThe, MonadExceptOf.throw]
      · simp only [hh, oo, beq_iff_eq, ite_false, and_false, not_false_eq_true]
        rw [← key]
        cases offsetSpans ((List.range (offsetAt b start / 4)).map fun i => offsetAt b (start + i * 4)) (stop - start) <;>
          simp [Bind.bind, Except.bind, validateRanges]

set_option maxHeartbeats 4000000 in
/-- Checking a counted sequence natively refuses exactly as the Lean check does. -/
theorem list_calls {m : Module} {w : World} (hm : Loaded m) (e : Desc) (ih : RangeOk m w e)
    (fit : fitsNative e = true) (has lim : Nat) (hhas : has < 2 ^ 64) (hlim : lim < 2 ^ 64) (p sp : Nat)
    (mem : Memory) (base : Nat) (b : ByteArray) (start stop err : Nat) (hp : PlanAt w mem p (Plan.words e))
    (cp : Clear err p (8 * (Plan.words e).length)) (hd : DataAt w mem base b) (cd : Clear err base b.size)
    (ok : w.access err 32 = true) (hle : start ≤ stop) (hs : stop ≤ b.size) (small : b.size < 2 ^ 60)
    (room : Room w sp (e.nesting + 1) 3) :
    Calls m w "ssz_validate_list" sp [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (base + stop),
      UInt64.ofNat has, UInt64.ofNat lim, UInt64.ofNat err] mem
      (res (do let r ← listRanges e (Plan.readBound has lim) b start stop; validateRanges e b r))
      (after mem err (do let r ← listRanges e (Plan.readBound has lim) b start stop; validateRanges e b r)) := by
  have hb := hp.bound
  have db := hd.bound
  have eb : err + 32 ≤ 2 ^ 63 := by
    have := ok; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  have hsz : base + stop - (base + start) = stop - start := by omega
  have hroom : Room w (sp - 8 - 8 * 17) e.nesting 5 := by simp only [Room] at room ⊢; omega
  have width := width_calls hm e fit p (sp - 8 - 8 * 17) mem hp (by simp only [Room] at hroom ⊢; omega)
  rw [list_outcome e has lim b start stop]
  refine Calls.body 17 hm.list rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [listFn]
  wsteps [hsz]
  by_cases o : 2 ^ 32 ≤ stop - start
  · wsteps [hsz, o]
    wfail []
    wsteps []
    wfin [o, res, after, wrote_eq]
  by_cases z : stop - start = 0
  · wsteps [hsz, o, z]
    wfin [o, z, res, after]
  by_cases hw : hasWidth e = true
  · simp only [widthWord, ite_eq_left hw] at width
    have fw := fixedWidth_lt e fit hw
    have hne : fixedWidth e ≠ 18446744073709551615 := by omega
    wsteps [hsz, o, z]
    wcall width []
    wsteps [hne]
    by_cases w0 : fixedWidth e = 0
    · wsteps [w0]
      wfail []
      wsteps []
      wfin [o, z, hw, w0, res, after, wrote_eq]
    have hmod : (stop - start) % fixedWidth e ≤ stop - start := Nat.mod_le _ _
    have cnt : (stop - start) / fixedWidth e ≤ stop - start := Nat.div_le_self _ _
    by_cases d : (stop - start) % fixedWidth e ≠ 0
    · wsteps [w0, hsz, d]
      wfail [hsz]
      wsteps []
      wfin [o, z, hw, w0, d, res, after, wrote_eq]
    simp only [ne_eq, Decidable.not_not] at d
    by_cases ov : Over has lim ((stop - start) / fixedWidth e)
    · have ov' := ov
      unfold Over at ov'
      wsteps [w0, hsz, d, ov'.1, ov'.2]
      wfail [hsz]
      wsteps []
      wfin [o, z, hw, w0, d, ov, res, after, wrote_eq]
    · have ov' : has = 0 ∨ ¬ lim < (stop - start) / fixedWidth e := by unfold Over at ov; omega
      have probes := hasProbes_calls hm e fit p (sp - 8 - 8 * 17) mem hp (by simp only [Room] at hroom ⊢; omega)
      by_cases none : plan e = []
      · simp only [probeBit, ite_eq_left none] at probes
        rcases ov' with h0 | lt
        · wsteps [w0, hsz, d, h0]
          wcall probes []
          wsteps []
          wfin [o, z, hw, w0, d, ov, none, seqR_nil, res, after]
        · wsteps [w0, hsz, d, lt]
          wcall probes []
          wsteps []
          wfin [o, z, hw, w0, d, ov, none, seqR_nil, res, after]
      · simp only [probeBit, ite_eq_right none] at probes
        have recs := records_calls hm e (probe_calls hm e) fit hw p (sp - 8 - 8 * 17) mem base b start
          ((stop - start) / fixedWidth e) err (by omega) hp cp hd cd ok
          (by rw [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero d)]; omega) (by simp only [Room] at hroom ⊢; omega)
        rcases ov' with h0 | lt
        · wsteps [w0, hsz, d, h0]
          wcall probes []
          wsteps []
          wcall recs [hsz]
          wsteps []
          wfin [o, z, hw, w0, d, ov]
        · wsteps [w0, hsz, d, lt]
          wcall probes []
          wsteps []
          wcall recs [hsz]
          wsteps []
          wfin [o, z, hw, w0, d, ov]
  · simp only [widthWord, ite_eq_right hw] at width
    wsteps [hsz, o, z]
    wcall width []
    wsteps []
    by_cases s4 : stop - start < 4
    · wsteps [hsz, s4]
      wfail [hsz]
      wsteps []
      wfin [o, z, hw, s4, res, after, wrote_eq]
    have r0 := hd.offset start (by omega)
    have a0 := hd.offsetOk start (by omega)
    have o0 := offsetAt_lt b start
    have fq : offsetAt b start / 4 ≤ offsetAt b start := Nat.div_le_self _ _
    have fr : offsetAt b start % 4 < 4 := Nat.mod_lt _ (by omega)
    by_cases f4 : offsetAt b start < 4
    · wsteps [hsz, s4, r0, a0, f4]
      wfail []
      wsteps []
      wfin [o, z, hw, s4, f4, res, after, wrote_eq]
    by_cases fa : offsetAt b start % 4 ≠ 0
    · wsteps [hsz, s4, r0, a0, f4, fa]
      wfail []
      wsteps []
      wfin [o, z, hw, s4, f4, fa, res, after, wrote_eq]
    simp only [ne_eq, Decidable.not_not] at fa
    by_cases fp : stop - start < offsetAt b start
    · wsteps [hsz, s4, r0, a0, f4, fa, fp]
      wfail []
      wsteps []
      wfin [o, z, hw, s4, f4, fa, fp, res, after, wrote_eq]
    by_cases ov : Over has lim (offsetAt b start / 4)
    · have ov' := ov
      unfold Over at ov'
      wsteps [hsz, s4, r0, a0, f4, fa, fp, ov'.1, ov'.2]
      wfail []
      wsteps []
      wfin [o, z, hw, s4, f4, fa, fp, ov, res, after, wrote_eq]
    have ov' : has = 0 ∨ ¬ lim < offsetAt b start / 4 := by unfold Over at ov; omega
    have spans := spans_calls hm mem base b start (offsetAt b start / 4) (stop - start) err (sp - 8 - 8 * 17)
      (by omega) (by omega) hd ok (by simp only [Room] at room ⊢; omega)
    rcases hS : spansOutcome (tableOffsets b start (offsetAt b start / 4)) (stop - start) with x | u
    · rw [hS] at spans
      rcases ov' with h0 | lt
      · wsteps [hsz, s4, r0, a0, f4, fa, fp, h0]
        wcall spans []
        wsteps [res]
        wfin [o, z, hw, s4, f4, fa, fp, ov, hS, res, after]
      · wsteps [hsz, s4, r0, a0, f4, fa, fp, lt]
        wcall spans []
        wsteps [res]
        wfin [o, z, hw, s4, f4, fa, fp, ov, hS, res, after]
    · rw [hS] at spans
      obtain ⟨ord, last⟩ := spansOutcome_ok _ _ hS
      rw [tableOffsets_length] at ord last
      have each := each_calls hm e ih fit p (sp - 8 - 8 * 17) mem base b start (offsetAt b start / 4)
        (stop - start) err hp cp hd cd ok (by omega) (by omega) small ord (fun nz => last (by
          intro h; have := congrArg List.length h; simp [tableOffsets_length] at this; omega)) hroom
      rcases ov' with h0 | lt
      · wsteps [hsz, s4, r0, a0, f4, fa, fp, h0]
        wcall spans []
        wsteps [res]
        wcall each []
        wsteps []
        wfin [o, z, hw, s4, f4, fa, fp, ov, hS]
      · wsteps [hsz, s4, r0, a0, f4, fa, fp, lt]
        wcall spans []
        wsteps [res]
        wcall each []
        wsteps []
        wfin [o, z, hw, s4, f4, fa, fp, ov, hS]

end EthLib.Consensus.Ssz.Native.Driver.Validate
