import SszNative.Proofs.Driver.Validate.Fail

/-!
Running a fixed-size type's probes on a value, read from its plan.

The probes run field by field and record by record, in the order the probe list names them.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr

/-! The probes, in the order the native walk runs them. -/

/-- Each field's probes from its own start, in order. -/
def seqF (b : ByteArray) : Nat → List Desc → Except Err Unit
  | _, [] => .ok ()
  | s, f :: fs => do checkProbes b s (plan f); seqF b (s + fixedWidth f) fs

/-- The same probes over a count of records one width apart, in order. -/
def seqR (b : ByteArray) (w : Nat) (ps : List Probe) : Nat → Nat → Except Err Unit
  | _, 0 => .ok ()
  | s, c + 1 => do checkProbes b s ps; seqR b w ps (s + w) c

/-- A check followed by nothing is the check. -/
theorem bind_unit (x : Except Err Unit) : (do x; pure ()) = x := by cases x <;> rfl

/-- A struct's probes run field by field, each from its own offset. -/
theorem checkProbes_fieldsPlan (b : ByteArray) :
    ∀ (fs : List Desc) (start off : Nat), checkProbes b start (fieldsPlan fs off) = seqF b (start + off) fs
  | [], _, _ => by simp [fieldsPlan, checkProbes, seqF]
  | f :: fs, start, off => by
    rw [fieldsPlan_cons, checkProbes_append, checkProbes_shift, checkProbes_fieldsPlan b fs, seqF, Nat.add_assoc]

/-- Repeated probes run record by record. -/
theorem checkProbes_repeat (b : ByteArray) (w : Nat) (ps : List Probe) (start : Nat) :
    ∀ i c, checkProbes b start (repeatProbes ps w i c) = seqR b w ps (start + i * w) c
  | _, 0 => by simp [repeatProbes, checkProbes, seqR]
  | i, c + 1 => by
    rw [repeatProbes, checkProbes_append, checkProbes_shift, checkProbes_repeat b w ps start (i + 1) c, seqR,
      Nat.succ_mul, Nat.add_assoc]

/-- Records run as a first stretch, then the rest. -/
theorem seqR_add (b : ByteArray) (w : Nat) (ps : List Probe) :
    ∀ s j c, seqR b w ps s (j + c) = (do seqR b w ps s j; seqR b w ps (s + j * w) c)
  | s, 0, c => by simp [seqR]; rfl
  | s, j + 1, c => by
    rw [show j + 1 + c = (j + c) + 1 by omega, seqR, seqR, seqR_add b w ps (s + w) j c]
    cases checkProbes b s ps <;> simp [Bind.bind, Except.bind, Nat.succ_mul, Nat.add_assoc, Nat.add_comm w]

/-- Fields run as a first stretch, then the rest. -/
theorem seqF_append (b : ByteArray) :
    ∀ (a c : List Desc) s, seqF b s (a ++ c) = (do seqF b s a; seqF b (s + fieldsWidth a) c)
  | [], c, s => by simp [seqF, fieldsWidth]; rfl
  | f :: a, c, s => by
    simp only [List.cons_append, seqF, seqF_append b a c, fieldsWidth, Nat.add_assoc]
    cases checkProbes b s (plan f) <;> simp [Bind.bind, Except.bind]

/-- A byte of the encoding, read at its address as a word. -/
theorem DataAt.byteAt {w : World} {mem : Memory} {base : Nat} {b : ByteArray} (h : DataAt w mem base b) (i : Nat)
    (hi : i < b.size) : readLE mem (base + i) 1 = UInt64.ofNat (b.get! i).toNat := by
  rw [h.byte i hi]; apply u64_eq; simp

/-- A byte of the encoding is readable. -/
theorem DataAt.byteOk {w : World} {mem : Memory} {base : Nat} {b : ByteArray} (h : DataAt w mem base b) (i : Nat)
    (hi : i < b.size) : w.access (base + i) 1 = true :=
  access_sub h.1 (by omega) (by omega)

/-- The encoding ends below the address bound. -/
theorem DataAt.bound {w : World} {mem : Memory} {base : Nat} {b : ByteArray} (h : DataAt w mem base b) :
    base + b.size ≤ 2 ^ 63 := by
  have := h.1; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1

/-- The memory a refused check leaves, written as the native refusal writes it. -/
theorem after_error (mem : Memory) (err : Nat) (e : Err) : after mem err (.error e) = wrote mem err e := rfl

/-- What running a node's probes computes. -/
def ProbeOk (m : Module) (w : World) (d : Desc) : Prop :=
  fitsNative d = true → hasWidth d = true → ∀ (p sp : Nat) (mem : Memory) (base : Nat) (b : ByteArray)
    (start err : Nat), PlanAt w mem p (Plan.words d) → Clear err p (8 * (Plan.words d).length) →
    DataAt w mem base b → Clear err base b.size → w.access err 32 = true → start + fixedWidth d ≤ b.size →
    Room w sp d.nesting 2 →
    Calls m w "ssz_validate_probe" sp [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat err] mem
      (res (checkProbes b start (plan d))) (after mem err (checkProbes b start (plan d)))

/-- Running the same probes over a count of records one width apart, stopping at the first refusal. -/
theorem records_calls {m : Module} {w : World} (hm : Loaded m) (e : Desc) (ih : ProbeOk m w e)
    (fit : fitsNative e = true) (has : hasWidth e = true) (p sp : Nat) (mem : Memory) (base : Nat) (b : ByteArray)
    (start count err : Nat) (hc : count < 2 ^ 32) (hp : PlanAt w mem p (Plan.words e)) (cp : Clear err p (8 * (Plan.words e).length))
    (hd : DataAt w mem base b) (cd : Clear err base b.size) (ok : w.access err 32 = true)
    (inside : start + count * fixedWidth e ≤ b.size) (room : Room w sp e.nesting 3) :
    Calls m w "ssz_validate_records" sp [UInt64.ofNat p, UInt64.ofNat (fixedWidth e), UInt64.ofNat (base + start),
      UInt64.ofNat count, UInt64.ofNat err] mem
      (res (seqR b (fixedWidth e) (plan e) start count)) (after mem err (seqR b (fixedWidth e) (plan e) start count)) := by
  have hb := hp.bound
  have db := hd.bound
  have eb : err + 32 ≤ 2 ^ 63 := by
    have := ok; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  have fw := fixedWidth_lt e fit has
  refine Calls.body 9 hm.records rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [recordsFn]
  apply Wp.set (by wev [])
  refine Wp.loop (wp_loop (fun env mem' => ∃ j, j ≤ count ∧
      env 2 = UInt64.ofNat (base + start + j * fixedWidth e) ∧ env 3 = UInt64.ofNat (count - j) ∧
      env 0 = UInt64.ofNat p ∧ env 1 = UInt64.ofNat (fixedWidth e) ∧ env 4 = UInt64.ofNat err ∧
      ((env 5 = 0 ∧ mem' = mem ∧ seqR b (fixedWidth e) (plan e) start j = .ok ()) ∨
       (env 5 = 1 ∧ ∃ x, seqR b (fixedWidth e) (plan e) start count = .error x ∧ mem' = wrote mem err x)))
    (fun env _ => (env 3).toNat) ⟨0, Nat.zero_le _, by simp [entryEnv, Asm.assign], by simp [entryEnv, Asm.assign],
      by simp [entryEnv, Asm.assign], by simp [entryEnv, Asm.assign], by simp [entryEnv, Asm.assign],
      Or.inl ⟨by simp [Asm.assign], rfl, rfl⟩⟩ ?_)
  rintro env mem' ⟨j, hj, h2, h3, h0, h1, h4, st⟩
  rcases st with ⟨h5, hmem, sofar⟩ | ⟨h5, x, fails, hmem⟩
  · subst mem'
    refine ⟨_, by wev [h3, h5], fun nz => ?_, fun z => ?_⟩
    · have hjc : j < count := by
        rcases Nat.lt_or_ge j count with h | h
        · exact h
        · simp [show count - j = 0 by omega] at nz
      have more : j * fixedWidth e + fixedWidth e ≤ count * fixedWidth e := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hjc
      have step := ih fit has p (sp - 8 - 8 * 9) mem base b (start + j * fixedWidth e) err hp cp hd cd ok
        (by omega) (by simp only [Room] at room ⊢; omega)
      have split : seqR b (fixedWidth e) (plan e) start count =
          (do seqR b (fixedWidth e) (plan e) start j; seqR b (fixedWidth e) (plan e) (start + j * fixedWidth e) ((count - j - 1) + 1)) := by
        rw [← seqR_add, show j + (count - j - 1 + 1) = count by omega]
      rcases hX : checkProbes b (start + j * fixedWidth e) (plan e) with x | u
      · rw [hX] at step
        wcall step [h0, h1, h2, h4]
        wsteps [h0, h1, h2, h3, h4]
        refine ⟨⟨j + 1, by omega, by wfin [Nat.succ_mul], by wfin [], by wfin [h0], by wfin [h1], by wfin [h4],
          Or.inr ⟨by wfin [res], x, ?_, rfl⟩⟩, by wfin [h3]⟩
        rw [split, sofar]; simp [seqR, hX, Bind.bind, Except.bind]
      · rw [hX] at step
        wcall step [h0, h1, h2, h4]
        wsteps [h0, h1, h2, h3, h4]
        refine ⟨⟨j + 1, by omega, by wfin [Nat.succ_mul], by wfin [], by wfin [h0], by wfin [h1], by wfin [h4],
          Or.inl ⟨by wfin [res], rfl, ?_⟩⟩, by wfin [h3]⟩
        rw [seqR_add, sofar]; simp [seqR, hX, Bind.bind, Except.bind]
    · have hjc : j = count := by
        rcases Nat.lt_or_ge j count with h | h
        · simp [show count - j ≠ 0 by omega] at z
        · omega
      subst hjc
      exact Wp.done ⟨by wonly [h5, sofar, res], by simp [after, sofar]⟩
  · subst mem'
    refine ⟨_, by wev [h3, h5], fun nz => absurd (by wonly []) nz, fun _ => ?_⟩
    exact Wp.done ⟨by wonly [h5, fails, res], by simp [after, fails]⟩

/-- Each field of a list of fixed fields is fixed. -/
theorem allHaveWidth_getElem (fs : List Desc) (all : allHaveWidth fs = true) (j : Nat) (hj : j < fs.length) :
    hasWidth fs[j] = true := by
  have := List.take_append_drop j fs
  rw [List.drop_eq_getElem_cons hj] at this
  rw [← this, allHaveWidth_append] at all
  simp [allHaveWidth] at all
  exact all.2.1

/-- The memory a refusal leaves, as the four words written. -/
theorem wrote_eq (mem : Memory) (err : Nat) (x : Err) : wrote mem err x = wrote4 mem err
    (UInt64.ofNat (x.toWords[0]!)) (UInt64.ofNat (x.toWords[1]!)) (UInt64.ofNat (x.toWords[2]!))
    (UInt64.ofNat (x.toWords[3]!)) := rfl

/-- Running each fixed field's probes at its offset, stopping at the first refusal. -/
theorem fieldsProbe_calls {m : Module} {w : World} (hm : Loaded m) (fs : List Desc)
    (ih : ∀ f ∈ fs, ProbeOk m w f) (fit : allFitNative fs = true) (all : allHaveWidth fs = true)
    (p sp : Nat) (mem : Memory) (base : Nat) (b : ByteArray) (start err : Nat)
    (hp : PlanAt w mem p (Plan.wordsAll fs)) (cp : Clear err p (8 * (Plan.wordsAll fs).length))
    (hd : DataAt w mem base b) (cd : Clear err base b.size) (ok : w.access err 32 = true)
    (inside : start + fieldsWidth fs ≤ b.size) (room : Room w sp (Desc.deepestNesting fs + 1) 1) :
    Calls m w "ssz_validate_fields_probe" sp [UInt64.ofNat p, UInt64.ofNat fs.length, UInt64.ofNat (base + start),
      UInt64.ofNat err] mem (res (seqF b start fs)) (after mem err (seqF b start fs)) := by
  have hb := hp.bound
  have db := hd.bound
  have hl := length_le_wordsAll fs
  have eb : err + 32 ≤ 2 ^ 63 := by
    have := ok; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  refine Calls.body 9 hm.fieldsProbe rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [fieldsProbeFn]
  apply Wp.set (by wev [])
  refine Wp.loop (wp_loop (fun env mem' => ∃ j, j ≤ fs.length ∧
      env 0 = UInt64.ofNat (p + 8 * (Plan.wordsAll (fs.take j)).length) ∧ env 1 = UInt64.ofNat (fs.length - j) ∧
      env 2 = UInt64.ofNat (base + start + fieldsWidth (fs.take j)) ∧ env 3 = UInt64.ofNat err ∧
      ((env 4 = 0 ∧ mem' = mem ∧ seqF b start (fs.take j) = .ok ()) ∨
       (env 4 = 1 ∧ ∃ x, seqF b start fs = .error x ∧ mem' = wrote mem err x)))
    (fun env _ => (env 1).toNat) ⟨0, Nat.zero_le _, by simp [entryEnv, Asm.assign, Plan.wordsAll],
      by simp [entryEnv, Asm.assign], by simp [entryEnv, Asm.assign, fieldsWidth], by simp [entryEnv, Asm.assign],
      Or.inl ⟨by simp [Asm.assign], rfl, by simp [seqF]⟩⟩ ?_)
  rintro env mem' ⟨j, hj, h0, h1, h2, h3, st⟩
  have hjl := wordsAll_take_le fs j
  have fwl : fieldsWidth (fs.take j) ≤ fieldsWidth fs := by
    conv => rhs; rw [← List.take_append_drop j fs]
    rw [fieldsWidth_append]; omega
  rcases st with ⟨h4, hmem, sofar⟩ | ⟨h4, x, fails, hmem⟩
  · subst mem'
    refine ⟨_, by wev [h1, h4], fun nz => ?_, fun z => ?_⟩
    · have hjf : j < fs.length := by
        rcases Nat.lt_or_ge j fs.length with h | h
        · exact h
        · simp [show fs.length - j = 0 by omega] at nz
      have split := wordsAll_split fs j hjf
      have slen := congrArg List.length split
      simp only [List.length_append] at slen
      have hpj : PlanAt w mem (p + 8 * (Plan.wordsAll (fs.take j)).length) (Plan.words fs[j]) := by
        rw [split] at hp; exact hp.left.right
      have cpj : Clear err (p + 8 * (Plan.wordsAll (fs.take j)).length) (8 * (Plan.words fs[j]).length) := by
        unfold Clear at cp ⊢; omega
      have nest := nesting_le_deepest fs fs[j] (List.getElem_mem hjf)
      have hroom : Room w (sp - 8 - 8 * 9) fs[j].nesting 2 := by
        simp only [Room] at room ⊢
        omega
      have hasj := allHaveWidth_getElem fs all j hjf
      have fitj := fits_getElem fs fit j hjf
      have fwj : fieldsWidth (fs.take (j + 1)) = fieldsWidth (fs.take j) + fixedWidth fs[j] := by
        rw [take_succ_append fs j hjf, fieldsWidth_append]; simp [fieldsWidth]
      have fwl' : fieldsWidth (fs.take (j + 1)) ≤ fieldsWidth fs := by
        conv => rhs; rw [← List.take_append_drop (j + 1) fs]
        rw [fieldsWidth_append]; omega
      have leadfs := leadingWidth_of_all fs all
      have step := ih fs[j] (List.getElem_mem hjf) fitj hasj _ (sp - 8 - 8 * 9) mem base b
        (start + fieldsWidth (fs.take j)) err hpj cpj hd cd ok (by omega) hroom
      have sofar' : seqF b start (fs.take (j + 1)) =
          checkProbes b (start + fieldsWidth (fs.take j)) (plan fs[j]) := by
        rw [take_succ_append fs j hjf, seqF_append, sofar]
        simp [seqF, Bind.bind, Except.bind]
        cases checkProbes b (start + fieldsWidth (fs.take j)) (plan fs[j]) <;> rfl
      rcases hX : checkProbes b (start + fieldsWidth (fs.take j)) (plan fs[j]) with x | u
      · rw [hX] at step
        have hpj' := hpj.wrote4 err cpj (UInt64.ofNat (x.toWords[0]!)) (UInt64.ofNat (x.toWords[1]!))
          (UInt64.ofNat (x.toWords[2]!)) (UInt64.ofNat (x.toWords[3]!))
        have width := width_calls hm fs[j] fitj _ (sp - 8 - 8 * 9) _ hpj' hroom
        have skip := skip_calls hm fs[j] fitj _ (sp - 8 - 8 * 9) _ hpj' hroom
        simp only [widthWord, ite_eq_left hasj] at width
        simp only [res, after, wrote_eq] at step
        wcall step [h0, h1, h2, h3]
        wcall width [h0]
        wsteps [h0, h1, h2, h3]
        wcall skip [h0]
        wsteps [h0, h1, h2, h3]
        refine ⟨⟨j + 1, by omega, ?_, by wfin [], by wfin [fwj], by wfin [h3], Or.inr ⟨by wfin [], x, ?_, rfl⟩⟩,
          by wfin [h1]⟩
        · wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
        · rw [← List.take_append_drop (j + 1) fs, seqF_append, sofar', hX]; rfl
      · rw [hX] at step
        have width := width_calls hm fs[j] fitj _ (sp - 8 - 8 * 9) _ hpj hroom
        have skip := skip_calls hm fs[j] fitj _ (sp - 8 - 8 * 9) _ hpj hroom
        simp only [widthWord, ite_eq_left hasj] at width
        simp only [res, after] at step
        wcall step [h0, h1, h2, h3]
        wcall width [h0]
        wsteps [h0, h1, h2, h3]
        wcall skip [h0]
        wsteps [h0, h1, h2, h3]
        refine ⟨⟨j + 1, by omega, ?_, by wfin [], by wfin [fwj], by wfin [h3], Or.inl ⟨by wfin [], trivial, ?_⟩⟩,
          by wfin [h1]⟩
        · wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
        · rw [sofar', hX]
    · have hjc : j = fs.length := by
        rcases Nat.lt_or_ge j fs.length with h | h
        · simp [show fs.length - j ≠ 0 by omega] at z
        · omega
      subst hjc
      simp only [List.take_length] at sofar
      exact Wp.done ⟨by wonly [h4, sofar, res], by simp [after, sofar]⟩
  · subst mem'
    refine ⟨_, by wev [h1, h4], fun nz => absurd (by wonly []) nz, fun _ => ?_⟩
    exact Wp.done ⟨by wonly [h4, fails, res], by simp [after, fails]⟩

/-- Shifting a word right by one halves it. -/
theorem ofNat_shr_one (v : Nat) (h : v < 2 ^ 64) : UInt64.ofNat v >>> (1 : Nat).toUInt64 = UInt64.ofNat (v / 2) := by
  apply u64_eq
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)]

/-- A byte shifted right by a count below eight is the byte over that power of two. -/
theorem byte_shr (x : UInt8) (k : Nat) (hk : k < 8) : (x >>> UInt8.ofNat k).toNat = x.toNat / 2 ^ k := by
  rw [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  congr
  simp; omega

/-- A boolean's probe refuses a byte other than zero or one. -/
theorem checkProbes_bool (b : ByteArray) (s : Nat) :
    checkProbes b s (plan .bool) =
      if 1 < (b.get! s).toNat then .error (.notABit (b.get! s).toNat) else .ok () := by
  simp only [plan, checkProbes, Probe.check, Nat.add_zero]
  by_cases h : 1 < (b.get! s).toNat
  · have h0 : (b.get! s != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; intro e; rw [e] at h; simp at h
    have h1 : (b.get! s != 1) = true := by
      simp only [bne_iff_ne, ne_eq]; intro e; rw [e] at h; simp at h
    simp [h0, h1, h, Bind.bind, Except.bind]
  · have : b.get! s = 0 ∨ b.get! s = 1 := by
      have := (b.get! s).toNat_lt
      rcases Nat.lt_or_ge (b.get! s).toNat 1 with l | l
      · left; apply UInt8.toNat_inj.mp; simp; omega
      · right; apply UInt8.toNat_inj.mp; simp; omega
    rcases this with e | e <;> simp [e, Bind.bind, Except.bind]

/-- A bit vector's probe refuses set padding bits in its last byte. -/
theorem checkProbes_bitVector (b : ByteArray) (s n : Nat) :
    checkProbes b s (plan (.bitVector n)) =
      if n % 8 = 0 then .ok () else
        if (b.get! (s + ((n + 7) / 8 - 1))).toNat / 2 ^ (n % 8) ≠ 0 then .error .paddingBits else .ok () := by
  by_cases h : n % 8 = 0
  · simp [plan, h, checkProbes]
  · have pos : 0 < (n + 7) / 8 := by omega
    have shr := byte_shr (b.get! (s + ((n + 7) / 8 - 1))) (n % 8) (by omega)
    have hp : plan (.bitVector n) = [.padding ((n + 7) / 8 - 1) (n % 8)] := by simp [plan, h, pos]
    rw [hp, ite_eq_right h]
    simp only [checkProbes, Probe.check]
    by_cases z : (b.get! (s + ((n + 7) / 8 - 1))).toNat / 2 ^ (n % 8) = 0
    · have : b.get! (s + ((n + 7) / 8 - 1)) >>> UInt8.ofNat (n % 8) = 0 := by
        apply UInt8.toNat_inj.mp; rw [shr, z]; rfl
      simp [this, z, Bind.bind, Except.bind]
    · have : b.get! (s + ((n + 7) / 8 - 1)) >>> UInt8.ofNat (n % 8) ≠ 0 := by
        intro e; have := congrArg UInt8.toNat e; rw [shr] at this; exact z this
      simp [this, z, Bind.bind, Except.bind]

set_option hygiene false in
/-- Opens a proof about one node's probes. -/
macro "probe_open" : tactic => `(tactic| (
  intro fit has p sp mem base b start err hp cp hd cd ok inside room
  have hb := hp.bound
  have db := hd.bound
  have eb : err + 32 ≤ 2 ^ 63 := by
    have := ok; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  have r0 := hp.read0 (words_length_pos _)
  have a0 := hp.readable0 (words_length_pos _)
  simp [Plan.words] at r0 a0 hb))

set_option maxHeartbeats 1000000 in
/-- Running a node's probes refuses exactly where its probe list does, with the same refusal. -/
theorem probe_calls {m : Module} {w : World} (hm : Loaded m) (d : Desc) : ProbeOk m w d := by
  induction d using Desc.rec (motive_2 := fun fs => ∀ f ∈ fs, ProbeOk m w f) with
  | nil => rename_i h; simp at h
  | cons f fs ihf ihfs =>
    rename_i g h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ihf
    · exact ihfs g h
  | bool =>
    probe_open
    simp only [fixedWidth] at inside
    have rb := hd.byteAt start (by omega)
    have ab := hd.byteOk start (by omega)
    refine Calls.body 15 hm.probe rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [probeFn]
    wsteps [r0, a0, rb, ab]
    rw [checkProbes_bool]
    have hbyte := (b.get! start).toNat_lt
    by_cases hv : 1 < (b.get! start).toNat
    · wsteps [r0, a0, rb, ab, hv]
      wfail []
      wsteps []
      wfin [res, after, wrote_eq, hv]
    · wsteps [r0, a0, rb, ab, hv]
      wfin [res, after, hv]
  | uint _ | byteVector _ =>
    probe_open
    refine Calls.body 15 hm.probe rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [probeFn]
    wsteps [r0, a0]
    wfin [res, after, plan, checkProbes]
  | bitVector n =>
    probe_open
    have r1 := hp.read 8 rfl (by simp [Plan.words])
    have a1 := hp.readable 8 rfl (by simp [Plan.words])
    simp [Plan.words] at r1
    simp [fitsNative] at fit
    simp only [fixedWidth] at inside
    refine Calls.body 15 hm.probe rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [probeFn]
    wsteps [r0, a0, r1, a1]
    rw [checkProbes_bitVector]
    by_cases h : n % 8 = 0
    · wsteps [h]
      wfin [res, after, h]
    · have pos : 0 < (n + 7) / 8 := by omega
      have rb : readLE mem (base + start + (n + 7) / 8 - 1) 1 =
          UInt64.ofNat (b.get! (start + ((n + 7) / 8 - 1))).toNat := by
        rw [show base + start + (n + 7) / 8 - 1 = base + (start + ((n + 7) / 8 - 1)) by omega]
        exact hd.byteAt _ (by omega)
      have ab : w.access (base + start + (n + 7) / 8 - 1) 1 = true := by
        rw [show base + start + (n + 7) / 8 - 1 = base + (start + ((n + 7) / 8 - 1)) by omega]
        exact hd.byteOk _ (by omega)
      have hbyte := (b.get! (start + ((n + 7) / 8 - 1))).toNat_lt
      generalize hy : (b.get! (start + ((n + 7) / 8 - 1))).toNat = y at rb hbyte ⊢
      have hm8 : n % 8 < 8 := Nat.mod_lt _ (by omega)
      wsteps [h, rb, ab]
      refine Wp.loop (wp_loop (fun env mem' => mem' = mem ∧ ∃ k, k ≤ n % 8 ∧ env 6 = UInt64.ofNat k ∧
          env 7 = UInt64.ofNat (y / 2 ^ (n % 8 - k)) ∧ env 4 = 0 ∧ env 2 = UInt64.ofNat err)
        (fun env _ => (env 6).toNat) ⟨rfl, n % 8, Nat.le_refl _, by wfin [], by wfin [Nat.sub_self, Nat.pow_zero, Nat.div_one],
          by wfin [], by wfin []⟩ ?_)
      rintro env mem' ⟨hmem, k, hk, h6, h7, h4, h2⟩
      subst mem'
      have yb : y / 2 ^ (n % 8 - k) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      refine ⟨_, by wev [h6], fun nz => ?_, fun z => ?_⟩
      · have kpos : 0 < k := by
          rcases Nat.eq_zero_or_pos k with e | e
          · subst e; simp at nz
          · exact e
        have hpow : 2 ^ (n % 8 - (k - 1)) = 2 ^ (n % 8 - k) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
        have hdiv : y / 2 ^ (n % 8 - (k - 1)) = y / 2 ^ (n % 8 - k) / 2 := by rw [hpow, Nat.div_div_eq_div_mul]
        wsteps [h6, h7, ofNat_shr_one _ yb]
        refine ⟨⟨trivial, k - 1, by omega, by wfin [], by wfin [hdiv], by wfin [h4], by wfin [h2]⟩, by wfin [h6]⟩
      · have k0 : k = 0 := by
          rcases Nat.eq_zero_or_pos k with e | e
          · exact e
          · simp [show k ≠ 0 by omega] at z
        subst k0
        simp only [Nat.sub_zero] at h7
        by_cases zz : y / 2 ^ (n % 8) = 0
        · wsteps [h7, zz]
          wfin [res, after, h, zz, h4]
        · wsteps [h7, zz]
          wfail [h2]
          wsteps []
          wfin [res, after, h, zz, wrote_eq]
  | vector e n ih =>
    probe_open
    have r1 := hp.read 8 rfl (by simp [Plan.words])
    have a1 := hp.readable 8 rfl (by simp [Plan.words])
    simp [Plan.words] at r1
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at fit
    simp only [hasWidth] at has
    simp only [fixedWidth] at inside
    have he : PlanAt w mem (p + 16) (Plan.words e) := by
      have := hp.right (a := [7, n]) (b := Plan.words e); simpa using this
    have ce : Clear err (p + 16) (8 * (Plan.words e).length) := by
      simp [Plan.words] at cp; unfold Clear at cp ⊢; omega
    have fw := fixedWidth_lt e fit.1.1 has
    have prod : fixedWidth e * n < 2 ^ 32 := by
      rcases fit.2 with h | h
      · simp [h] at has
      · exact h
    have hroom : Room w (sp - 8 - 8 * 15) e.nesting 3 := by simp only [Room, Desc.nesting] at room ⊢; omega
    have probes := hasProbes_calls hm e fit.1.1 (p + 16) (sp - 8 - 8 * 15) mem he
      (by simp only [Room] at hroom ⊢; omega)
    refine Calls.body 15 hm.probe rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [probeFn]
    wsteps [r0, a0, r1, a1]
    rw [plan_vector, checkProbes_repeat, Nat.zero_mul, Nat.add_zero]
    by_cases none : plan e = []
    · simp only [probeBit, ite_eq_left none] at probes
      wcall probes []
      wsteps []
      have nil : ∀ s c, seqR b (fixedWidth e) [] s c = .ok () := by
        intro s c
        induction c generalizing s with
        | zero => rfl
        | succ c ihc => simp only [seqR, checkProbes]; exact ihc _
      rw [none, nil]
      wfin [res, after]
    · simp only [probeBit, ite_eq_right none] at probes
      have width := width_calls hm e fit.1.1 (p + 16) (sp - 8 - 8 * 15) mem he
        (by simp only [Room] at hroom ⊢; omega)
      simp only [widthWord, ite_eq_left has] at width
      have recs := records_calls hm e ih fit.1.1 has (p + 16) (sp - 8 - 8 * 15) mem base b start n err (by omega)
        he ce hd cd ok (by rw [Nat.mul_comm]; omega) hroom
      wcall probes []
      wsteps []
      wcall width []
      wcall recs [r1, a1]
      wsteps []
      wfin []
  | container names fs ih =>
    probe_open
    have r1 := hp.read 8 rfl (by simp [Plan.words])
    have a1 := hp.readable 8 rfl (by simp [Plan.words])
    simp [Plan.words] at r1
    have hf : PlanAt w mem (p + 16) (Plan.wordsAll fs) := by
      have := hp.right (a := [10, fs.length]) (b := Plan.wordsAll fs); simpa using this
    have cf : Clear err (p + 16) (8 * (Plan.wordsAll fs).length) := by
      simp [Plan.words] at cp; unfold Clear at cp ⊢; omega
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
    simp only [hasWidth] at has
    simp only [fixedWidth] at inside
    have step := fieldsProbe_calls hm fs ih fit.1.1 has (p + 16) (sp - 8 - 8 * 15) mem base b start err
      hf cf hd cd ok inside (by simp only [Room, Desc.nesting] at room ⊢; omega)
    refine Calls.body 15 hm.probe rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [probeFn]
    wsteps [r0, a0, r1, a1]
    wcall step [r1, a1]
    wsteps []
    wfin [plan, checkProbes_fieldsPlan]
  | progressiveContainer active names fs ih =>
    probe_open
    have r1 := hp.read 8 rfl (by simp [Plan.words])
    have a1 := hp.readable 8 rfl (by simp [Plan.words])
    simp [Plan.words] at r1
    have r2 := hp.read (16 + 8 * active.length) (by omega) (by simp [Plan.words]; omega)
    have a2 := hp.readable (16 + 8 * active.length) (by omega) (by simp [Plan.words]; omega)
    rw [← Nat.add_assoc] at r2 a2
    have r2' : readLE mem (p + 16 + 8 * active.length) 8 = UInt64.ofNat fs.length := by
      rw [r2, show (16 + 8 * active.length) / 8 = active.length + 2 by omega]
      simp only [Plan.words, getElem!_def, List.append_assoc]
      rw [List.getElem?_append_right (by simp)]
      simp
    have e : Plan.words (.progressiveContainer active names fs) =
        ([11, active.length] ++ active.map (fun b => if b then 1 else 0) ++ [fs.length]) ++ Plan.wordsAll fs := by
      simp [Plan.words]
    have hf : PlanAt w mem (p + 24 + 8 * active.length) (Plan.wordsAll fs) := by
      rw [e] at hp
      refine hp.right.at_eq ?_
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]
      omega
    have cf : Clear err (p + 24 + 8 * active.length) (8 * (Plan.wordsAll fs).length) := by
      rw [e] at cp; simp at cp; unfold Clear at cp ⊢; omega
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
    simp only [hasWidth] at has
    simp only [fixedWidth] at inside
    have step := fieldsProbe_calls hm fs ih fit.1.1 has (p + 24 + 8 * active.length) (sp - 8 - 8 * 15) mem
      base b start err hf cf hd cd ok inside (by simp only [Room, Desc.nesting] at room ⊢; omega)
    refine Calls.body 15 hm.probe rfl (by simp only [Room] at room; omega) rfl ?_
    simp only [probeFn]
    wsteps [r0, a0, r1, a1, r2', a2]
    wcall step [r1, a1, r2', a2]
    wsteps []
    wfin [plan, checkProbes_fieldsPlan]
  | byteList _ | bitList _ | progressiveBitList _ | list _ _ _ | progressiveList _ _ _ | compatibleUnion _ _ _ =>
    intro _ has; simp [hasWidth] at has

end EthLib.Consensus.Ssz.Native.Driver.Validate
