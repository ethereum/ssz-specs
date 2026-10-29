import SszNative.Proofs.Driver.Validate.StructSpec

/-!
A struct's fields walked natively: fixed fields in place, the table as a whole, then every field in order.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr

/-- The fields from one on are that field, then the rest. -/
theorem drop_cons (fs : List Desc) (j : Nat) (hj : j < fs.length) : fs.drop j = fs[j] :: fs.drop (j + 1) :=
  List.drop_eq_getElem_cons hj

/-- One more field adds its slot to the fixed part. -/
theorem leading_succ (fs : List Desc) (j : Nat) (hj : j < fs.length) :
    Desc.leadingWidth (fs.take (j + 1)) = Desc.leadingWidth (fs.take j) + slot fs[j] := by
  rw [take_succ_append fs j hj, leadingWidth_append, leadingWidth_slot [fs[j]]]; simp

/-- The facts a walk over fields keeps about the field it stands on. -/
structure FieldAt (w : World) (mem : Memory) (fs : List Desc) (p j : Nat) : Prop where
  lt : j < fs.length
  plan : PlanAt w mem (p + 8 * (Plan.wordsAll (fs.take j)).length) (Plan.words fs[j])
  len : (Plan.wordsAll fs).length =
    (Plan.wordsAll (fs.take j)).length + (Plan.words fs[j]).length + (Plan.wordsAll (fs.drop (j + 1))).length

/-- A field of a plan in memory, with the words around it. -/
theorem fieldAt {w : World} {mem : Memory} {fs : List Desc} {p : Nat} (hp : PlanAt w mem p (Plan.wordsAll fs))
    (j : Nat) (hj : j < fs.length) : FieldAt w mem fs p j := by
  have split := wordsAll_split fs j hj
  have slen := congrArg List.length split
  simp only [List.length_append] at slen
  exact ⟨hj, by rw [split] at hp; exact hp.left.right, slen⟩

set_option maxHeartbeats 4000000 in
/-- Checking each fixed field in place, stopping at the first refusal. -/
theorem inline_calls {m : Module} {w : World} (hm : Loaded m) (fs : List Desc) (ih : ∀ f ∈ fs, RangeOk m w f)
    (fit : allFitNative fs = true) (p sp : Nat) (mem : Memory) (base : Nat) (b : ByteArray) (start err : Nat)
    (hp : PlanAt w mem p (Plan.wordsAll fs)) (cp : Clear err p (8 * (Plan.wordsAll fs).length))
    (hd : DataAt w mem base b) (cd : Clear err base b.size) (ok : w.access err 32 = true)
    (inside : start + Desc.leadingWidth fs ≤ b.size) (small : b.size < 2 ^ 60)
    (room : Room w sp (Desc.deepestNesting fs + 1) 1) :
    Calls m w "ssz_validate_inline" sp [UInt64.ofNat p, UInt64.ofNat fs.length, UInt64.ofNat (base + start),
      UInt64.ofNat err] mem
      (res (validateInline fs b (placesFrom b start fs 0))) (after mem err (validateInline fs b (placesFrom b start fs 0))) := by
  have hb := hp.bound
  have db := hd.bound
  have hl := length_le_wordsAll fs
  have eb : err + 32 ≤ 2 ^ 63 := by
    have := ok; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  generalize hX : validateInline fs b (placesFrom b start fs 0) = X
  refine Calls.body 11 hm.inline rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [inlineFn]
  wsteps []
  refine Wp.loop (wp_loop (fun env mem' => ∃ j, j ≤ fs.length ∧
      env 0 = UInt64.ofNat (p + 8 * (Plan.wordsAll (fs.take j)).length) ∧ env 1 = UInt64.ofNat (fs.length - j) ∧
      env 6 = UInt64.ofNat (Desc.leadingWidth (fs.take j)) ∧ env 2 = UInt64.ofNat (base + start) ∧
      env 3 = UInt64.ofNat err ∧
      ((env 4 = 0 ∧ mem' = mem ∧
          X = validateInline (fs.drop j) b (placesFrom b start (fs.drop j) (Desc.leadingWidth (fs.take j)))) ∨
       (env 4 = 1 ∧ ∃ x, X = .error x ∧ mem' = wrote mem err x)))
    (fun env _ => (env 1).toNat)
    ⟨0, Nat.zero_le _, by wfin [Plan.wordsAll], by wfin [], by wfin [Desc.leadingWidth], by wfin [], by wfin [],
      Or.inl ⟨by wfin [], rfl, by simp [Desc.leadingWidth, hX]⟩⟩ ?_)
  rintro env mem' ⟨j, hj, h0, h1, h6, h2, h3, st⟩
  have hjl := wordsAll_take_le fs j
  have lj := leadingWidth_take_le fs j
  rcases st with ⟨h4, hmem, rest⟩ | ⟨h4, x, fails, hmem⟩
  · subst mem'
    refine ⟨_, by wev [h1, h4], fun nz => ?_, fun z => ?_⟩
    · have hjf : j < fs.length := by
        rcases Nat.lt_or_ge j fs.length with h | h
        · exact h
        · simp [show fs.length - j = 0 by omega] at nz
      obtain ⟨_, hpj, slen⟩ := fieldAt hp j hjf
      have cpj : Clear err (p + 8 * (Plan.wordsAll (fs.take j)).length) (8 * (Plan.words fs[j]).length) := by
        unfold Clear at cp ⊢; omega
      have nest := nesting_le_deepest fs fs[j] (List.getElem_mem hjf)
      have fitj := fits_getElem fs fit j hjf
      have hroom : Room w (sp - 8 - 8 * 11) fs[j].nesting 4 := by simp only [Room] at room ⊢; omega
      have width := width_calls hm fs[j] fitj _ (sp - 8 - 8 * 11) mem hpj (by simp only [Room] at hroom ⊢; omega)
      have succ := leading_succ fs j hjf
      have lj1 := leadingWidth_take_le fs (j + 1)
      rw [drop_cons fs j hjf] at rest
      by_cases hw : hasWidth fs[j] = true
      · simp only [widthWord, ite_eq_left hw] at width
        have fw := fixedWidth_lt fs[j] fitj hw
        have hne : fixedWidth fs[j] ≠ 18446744073709551615 := by omega
        have sl : slot fs[j] = fixedWidth fs[j] := by simp [slot, hw]
        have step := ih fs[j] (List.getElem_mem hjf) fitj _ (sp - 8 - 8 * 11) mem base b
          (start + Desc.leadingWidth (fs.take j)) (start + Desc.leadingWidth (fs.take j) + fixedWidth fs[j]) err
          hpj cpj hd cd ok (by omega) (by omega) small hroom
        simp only [placesFrom, hw, ite_true, validateInline] at rest
        rcases hR : validateRange fs[j] b (start + Desc.leadingWidth (fs.take j))
            (start + Desc.leadingWidth (fs.take j) + fixedWidth fs[j]) with y | u
        · rw [hR] at step rest
          have hpj' := hpj.wrote4 err cpj (UInt64.ofNat (y.toWords[0]!)) (UInt64.ofNat (y.toWords[1]!))
            (UInt64.ofNat (y.toWords[2]!)) (UInt64.ofNat (y.toWords[3]!))
          have skip := skip_calls hm fs[j] fitj _ (sp - 8 - 8 * 11) _ hpj'
            (by simp only [Room] at hroom ⊢; omega)
          simp only [res, after, wrote_eq] at step
          wcall width [h0]
          wsteps [hne]
          wcall step [h0, h2, h3, h6]
          wsteps [h6]
          wcall skip [h0]
          wsteps [h1]
          refine ⟨⟨j + 1, by omega, ?_, by wfin [], by wfin [succ, sl], by wfin [h2], by wfin [h3],
            Or.inr ⟨by wfin [], y, ?_, rfl⟩⟩, by wfin [h1]⟩
          · wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
          · rw [rest]; rfl
        · rw [hR] at step rest
          have skip := skip_calls hm fs[j] fitj _ (sp - 8 - 8 * 11) _ hpj (by simp only [Room] at hroom ⊢; omega)
          simp only [res, after] at step
          wcall width [h0]
          wsteps [hne]
          wcall step [h0, h2, h3, h6]
          wsteps [h6]
          wcall skip [h0]
          wsteps [h1]
          refine ⟨⟨j + 1, by omega, ?_, by wfin [], by wfin [succ, sl], by wfin [h2], by wfin [h3],
            Or.inl ⟨by wfin [], trivial, ?_⟩⟩, by wfin [h1]⟩
          · wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
          · rw [rest, succ, sl]; rfl
      · simp only [widthWord, ite_eq_right hw] at width
        have sl : slot fs[j] = 4 := by simp [slot, hw]
        have skip := skip_calls hm fs[j] fitj _ (sp - 8 - 8 * 11) _ hpj (by simp only [Room] at hroom ⊢; omega)
        simp only [placesFrom, hw, Bool.false_eq_true, ite_false, validateInline] at rest
        wcall width [h0]
        wsteps [h6]
        wcall skip [h0]
        wsteps [h1]
        refine ⟨⟨j + 1, by omega, ?_, by wfin [], by wfin [succ, sl], by wfin [h2], by wfin [h3],
          Or.inl ⟨by wfin [], trivial, ?_⟩⟩, by wfin [h1]⟩
        · wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
        · rw [rest, succ, sl]
    · have hjc : j = fs.length := by
        rcases Nat.lt_or_ge j fs.length with h | h
        · simp [show fs.length - j ≠ 0 by omega] at z
        · omega
      subst hjc
      simp only [List.drop_length, placesFrom] at rest
      have : validateInline [] b [] = .ok () := by rw [validateInline]
      rw [this] at rest
      exact Wp.done ⟨by wonly [h4, rest, res], by simp [after, rest]⟩
  · subst mem'
    refine ⟨_, by wev [h1, h4], fun nz => absurd (by wonly []) nz, fun _ => ?_⟩
    exact Wp.done ⟨by wonly [h4, fails, res], by simp [after, fails]⟩

/-- Two lists of fields name their bodies one after the other. -/
theorem varOffs_append (b : ByteArray) (start : Nat) : ∀ (a c : List Desc) (pos : Nat),
    varOffs b start (a ++ c) pos = varOffs b start a pos ++ varOffs b start c (pos + Desc.leadingWidth a)
  | [], c, pos => by simp [varOffs, Desc.leadingWidth]
  | f :: a, c, pos => by
    rw [List.cons_append, leadingWidth_cons]
    by_cases hw : hasWidth f = true
    · simp only [varOffs, hw, ite_true, varOffs_append b start a c, slot]; congr 2; omega
    · simp only [varOffs, hw, Bool.false_eq_true, ite_false, varOffs_append b start a c, slot, List.cons_append]
      congr 3; omega

/-- The fields' bodies, split around a field. -/
theorem varOffs_split (b : ByteArray) (start : Nat) (fs : List Desc) (pos j : Nat) :
    varOffs b start fs pos =
      varOffs b start (fs.take j) pos ++ varOffs b start (fs.drop j) (pos + Desc.leadingWidth (fs.take j)) := by
  conv => lhs; rw [← List.take_append_drop j fs]
  rw [varOffs_append]

set_option maxHeartbeats 4000000 in
/-- Where the next body begins: the first variable field's offset from here on, or the size. -/
theorem nextBody_calls {m : Module} {w : World} (hm : Loaded m) (fs : List Desc) (fit : allFitNative fs = true)
    (p sp : Nat) (mem : Memory) (base : Nat) (b : ByteArray) (start pos size : Nat)
    (hp : PlanAt w mem p (Plan.wordsAll fs)) (hd : DataAt w mem base b)
    (inside : start + pos + Desc.leadingWidth fs ≤ b.size)
    (room : Room w sp (Desc.deepestNesting fs + 1) 1) :
    Calls m w "ssz_validate_next_body" sp [UInt64.ofNat p, UInt64.ofNat fs.length, UInt64.ofNat (base + start + pos),
      UInt64.ofNat size] mem (UInt64.ofNat (nextOff b start size fs pos)) mem := by
  have hb := hp.bound
  have db := hd.bound
  have hl := length_le_wordsAll fs
  refine Calls.body 7 hm.nextBody rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [nextBodyFn]
  wsteps []
  refine Wp.loop (wp_loop (fun env mem' => mem' = mem ∧ ∃ j, j ≤ fs.length ∧
      ((allHaveWidth (fs.take j) = true ∧
        env 0 = UInt64.ofNat (p + 8 * (Plan.wordsAll (fs.take j)).length) ∧ env 1 = UInt64.ofNat (fs.length - j) ∧
        env 2 = UInt64.ofNat (base + start + pos + Desc.leadingWidth (fs.take j)) ∧ env 4 = UInt64.ofNat size) ∨
       (env 1 = 0 ∧ env 4 = UInt64.ofNat (nextOff b start size fs pos))))
    (fun env _ => (env 1).toNat)
    ⟨rfl, 0, Nat.zero_le _, Or.inl ⟨by simp [allHaveWidth], by wfin [Plan.wordsAll], by wfin [],
      by wfin [Desc.leadingWidth], by wfin []⟩⟩ ?_)
  rintro env mem' ⟨hmem, j, hj, st⟩
  subst mem'
  have hjl := wordsAll_take_le fs j
  have lj := leadingWidth_take_le fs j
  rcases st with ⟨all, h0, h1, h2, h4⟩ | ⟨h1, h4⟩
  · refine ⟨_, by wev [h1], fun nz => ?_, fun z => ?_⟩
    · have hjf : j < fs.length := by
        rcases Nat.lt_or_ge j fs.length with h | h
        · exact h
        · simp [show fs.length - j = 0 by omega] at nz
      obtain ⟨_, hpj, slen⟩ := fieldAt hp j hjf
      have nest := nesting_le_deepest fs fs[j] (List.getElem_mem hjf)
      have fitj := fits_getElem fs fit j hjf
      have hroom : Room w (sp - 8 - 8 * 7) fs[j].nesting 2 := by simp only [Room] at room ⊢; omega
      have width := width_calls hm fs[j] fitj _ _ mem hpj hroom
      have succ := leading_succ fs j hjf
      have lj1 := leadingWidth_take_le fs (j + 1)
      have split := varOffs_split b start fs pos j
      rw [varOffs_all b start _ pos all, List.nil_append, drop_cons fs j hjf] at split
      by_cases hw : hasWidth fs[j] = true
      · simp only [widthWord, ite_eq_left hw] at width
        have fw := fixedWidth_lt fs[j] fitj hw
        have hne : fixedWidth fs[j] ≠ 18446744073709551615 := by omega
        have sl : slot fs[j] = fixedWidth fs[j] := by simp [slot, hw]
        have skip := skip_calls hm fs[j] fitj _ _ mem hpj hroom
        wcall width [h0]
        wsteps [hne, h2]
        wcall skip [h0]
        wsteps [h1]
        refine ⟨⟨trivial, j + 1, by omega, Or.inl ⟨?_, ?_, by wfin [], by wfin [succ, sl], by wfin [h4]⟩⟩, by wfin [h1]⟩
        · rw [take_succ_append fs j hjf, allHaveWidth_append]; simp [all, allHaveWidth, hw]
        · wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
      · simp only [widthWord, ite_eq_right hw] at width
        have sl : slot fs[j] = 4 := by simp [slot, hw]
        rw [succ, sl] at lj1
        have r := hd.offset (start + pos + Desc.leadingWidth (fs.take j)) (by omega)
        have a := hd.offsetOk (start + pos + Desc.leadingWidth (fs.take j)) (by omega)
        simp only [← Nat.add_assoc] at r a
        have ol := offsetAt_lt b (start + pos + Desc.leadingWidth (fs.take j))
        wcall width [h0]
        wsteps [h2, r, a]
        refine ⟨⟨trivial, j + 1, by omega, Or.inr ⟨by wfin [], ?_⟩⟩, by wfin [h1]⟩
        wfin [nextOff, split, varOffs, hw, Nat.add_assoc]
    · have hjc : j = fs.length := by
        rcases Nat.lt_or_ge j fs.length with h | h
        · simp [show fs.length - j ≠ 0 by omega] at z
        · omega
      subst hjc
      simp only [List.take_length] at all
      exact Wp.done ⟨by wonly [h4, nextOff, varOffs_all b start fs pos all, List.headD_nil], rfl⟩
  · refine ⟨_, by wev [h1], fun nz => absurd (by wonly []) nz, fun _ => Wp.done ⟨by wonly [h4], rfl⟩⟩

/-- An entry of the first list of a join. -/
theorem getElem!_append_left (V W : List Nat) (i : Nat) (h : i < V.length) : (V ++ W)[i]! = V[i]! := by
  simp [List.getElem?_append_left h]

/-- The entry right after the first list of a join. -/
theorem getElem!_append_mid (V W : List Nat) (o : Nat) : (V ++ o :: W)[V.length]! = o := by
  simp

/-- Offsets in order stay in order with more after them. -/
theorem ord_prefix (V W : List Nat) (ord : OrdUpTo V V.length) : OrdUpTo (V ++ W) V.length := by
  intro k kp ki kl
  rw [getElem!_append_left V W k ki, getElem!_append_left V W (k - 1) (by omega)]
  exact ord k kp ki ki

/-- Every offset a fixed part names fits below 2^32. -/
theorem varOffs_lt (b : ByteArray) (start : Nat) : ∀ (fs : List Desc) (pos : Nat), ∀ x ∈ varOffs b start fs pos,
    x < 2 ^ 32
  | [], _, x, h => by simp [varOffs] at h
  | f :: fs, pos, x, h => by
    by_cases hw : hasWidth f = true
    · simp only [varOffs, hw, ite_true] at h; exact varOffs_lt b start fs _ x h
    · simp only [varOffs, hw, Bool.false_eq_true, ite_false, List.mem_cons] at h
      rcases h with rfl | h
      · exact offsetAt_lt b _
      · exact varOffs_lt b start fs _ x h

/-- Every entry of a list under a bound is under it. -/
theorem getElem!_lt (l : List Nat) (B : Nat) (pos : 0 < B) (h : ∀ x ∈ l, x < B) (i : Nat) : l[i]! < B := by
  rw [getElem!_def]
  cases hi : l[i]? with
  | none => simpa using pos
  | some x => exact h x (List.mem_of_getElem? hi)

/-- Offsets in order stay in order with one no earlier after them. -/
theorem ord_snoc (V : List Nat) (o : Nat) (ord : OrdUpTo V V.length) (last : V ≠ [] → V[V.length - 1]! ≤ o) :
    OrdUpTo (V ++ [o]) (V ++ [o]).length := by
  intro k kp ki kl
  simp only [List.length_append, List.length_singleton] at ki
  by_cases hk : k < V.length
  · rw [getElem!_append_left V [o] k hk, getElem!_append_left V [o] (k - 1) (by omega)]
    exact ord k kp hk hk
  · have e : k = V.length := by omega
    subst e
    have := getElem!_append_mid V [] o
    rw [this, getElem!_append_left V [o] (V.length - 1) (by omega)]
    exact last (by intro h; simp [h] at kp)

set_option maxHeartbeats 8000000 in
/-- Checking a struct's table as a whole: the first body at the fixed part's end, the rest in order and in scope. -/
theorem structSpans_calls {m : Module} {w : World} (hm : Loaded m) (fs : List Desc) (fit : allFitNative fs = true)
    (some : allHaveWidth fs = false) (p sp : Nat) (mem : Memory) (base : Nat) (b : ByteArray) (start size err : Nat)
    (hp : PlanAt w mem p (Plan.wordsAll fs)) (cp : Clear err p (8 * (Plan.wordsAll fs).length))
    (hd : DataAt w mem base b) (ok : w.access err 32 = true)
    (inside : start + Desc.leadingWidth fs ≤ b.size) (hsize : size < 2 ^ 32) (lead : Desc.leadingWidth fs < 2 ^ 32)
    (room : Room w sp (Desc.deepestNesting fs + 1) 1) :
    Calls m w "ssz_validate_struct_spans" sp [UInt64.ofNat p, UInt64.ofNat fs.length, UInt64.ofNat (base + start),
      UInt64.ofNat size, UInt64.ofNat (Desc.leadingWidth fs), UInt64.ofNat err] mem
      (res (if (varOffs b start fs 0)[0]! ≠ Desc.leadingWidth fs then
          .error (.firstOffset (Desc.leadingWidth fs) (varOffs b start fs 0)[0]!)
        else spansOutcome (varOffs b start fs 0) size))
      (after mem err (if (varOffs b start fs 0)[0]! ≠ Desc.leadingWidth fs then
          .error (.firstOffset (Desc.leadingWidth fs) (varOffs b start fs 0)[0]!)
        else spansOutcome (varOffs b start fs 0) size)) := by
  have hb := hp.bound
  have db := hd.bound
  have hl := length_le_wordsAll fs
  have eb : err + 32 ≤ 2 ^ 63 := by
    have := ok; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  generalize hX : (if (varOffs b start fs 0)[0]! ≠ Desc.leadingWidth fs then
      .error (.firstOffset (Desc.leadingWidth fs) (varOffs b start fs 0)[0]!)
    else spansOutcome (varOffs b start fs 0) size) = X
  refine Calls.body 17 hm.structSpans rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [structSpansFn]
  wsteps []
  refine Wp.loop (wp_loop (fun env mem' => ∃ j, j ≤ fs.length ∧
      env 0 = UInt64.ofNat (p + 8 * (Plan.wordsAll (fs.take j)).length) ∧ env 1 = UInt64.ofNat (fs.length - j) ∧
      env 8 = UInt64.ofNat (Desc.leadingWidth (fs.take j)) ∧ env 2 = UInt64.ofNat (base + start) ∧
      env 3 = UInt64.ofNat size ∧ env 4 = UInt64.ofNat (Desc.leadingWidth fs) ∧ env 5 = UInt64.ofNat err ∧
      ((env 6 = 0 ∧ mem' = mem ∧
          (varOffs b start (fs.take j) 0 = [] → env 9 = 0 ∧ env 10 = 0) ∧
          (varOffs b start (fs.take j) 0 ≠ [] → env 9 = 1 ∧
            (varOffs b start (fs.take j) 0)[0]! = Desc.leadingWidth fs ∧
            env 10 = UInt64.ofNat (varOffs b start (fs.take j) 0)[(varOffs b start (fs.take j) 0).length - 1]! ∧
            OrdUpTo (varOffs b start (fs.take j) 0) (varOffs b start (fs.take j) 0).length)) ∨
       (env 6 = 1 ∧ ∃ x, X = .error x ∧ mem' = wrote mem err x)))
    (fun env _ => (env 1).toNat)
    ⟨0, Nat.zero_le _, by wfin [Plan.wordsAll], by wfin [], by wfin [Desc.leadingWidth], by wfin [], by wfin [],
      by wfin [], by wfin [],
      Or.inl ⟨by wfin [], rfl, fun _ => ⟨by wfin [], by wfin []⟩, fun h => absurd (by simp [varOffs]) h⟩⟩ ?_)
  rintro env mem' ⟨j, hj, h0, h1, h8, h2, h3, h4, h5, st⟩
  have hjl := wordsAll_take_le fs j
  have lj := leadingWidth_take_le fs j
  rcases st with ⟨h6, hmem, empty, full⟩ | ⟨h6, x, fails, hmem⟩
  · subst mem'
    refine ⟨_, by wev [h1, h6], fun nz => ?_, fun z => ?_⟩
    · have hjf : j < fs.length := by
        rcases Nat.lt_or_ge j fs.length with h | h
        · exact h
        · simp [show fs.length - j = 0 by omega] at nz
      obtain ⟨_, hpj, slen⟩ := fieldAt hp j hjf
      have cpj : Clear err (p + 8 * (Plan.wordsAll (fs.take j)).length) (8 * (Plan.words fs[j]).length) := by
        unfold Clear at cp ⊢; omega
      have nest := nesting_le_deepest fs fs[j] (List.getElem_mem hjf)
      have fitj := fits_getElem fs fit j hjf
      have hroom : Room w (sp - 8 - 8 * 17) fs[j].nesting 2 := by simp only [Room] at room ⊢; omega
      have width := width_calls hm fs[j] fitj _ _ mem hpj hroom
      have succ := leading_succ fs j hjf
      have lj1 := leadingWidth_take_le fs (j + 1)
      have vnext : varOffs b start (fs.take (j + 1)) 0 =
          varOffs b start (fs.take j) 0 ++ varOffs b start [fs[j]] (Desc.leadingWidth (fs.take j)) := by
        rw [take_succ_append fs j hjf, varOffs_append]; simp
      have vall : varOffs b start fs 0 = varOffs b start (fs.take j) 0 ++
          varOffs b start (fs[j] :: fs.drop (j + 1)) (Desc.leadingWidth (fs.take j)) := by
        rw [varOffs_split b start fs 0 j, drop_cons fs j hjf, Nat.zero_add]
      have vlt := varOffs_lt b start (fs.take j) 0
      generalize hV : varOffs b start (fs.take j) 0 = V at empty full vnext vall vlt
      have lastlt := getElem!_lt V (2 ^ 32) (by decide) vlt (V.length - 1)
      by_cases hw : hasWidth fs[j] = true
      · simp only [widthWord, ite_eq_left hw] at width
        have fw := fixedWidth_lt fs[j] fitj hw
        have hne : fixedWidth fs[j] ≠ 18446744073709551615 := by omega
        have sl : slot fs[j] = fixedWidth fs[j] := by simp [slot, hw]
        have skip := skip_calls hm fs[j] fitj _ _ mem hpj hroom
        simp only [varOffs, hw, ite_true, List.append_nil] at vnext
        wcall width [h0]
        wsteps [hne, h8]
        wcall skip [h0]
        wsteps [h1]
        refine ⟨⟨j + 1, by omega, ?_, by wfin [], by wfin [succ, sl, h8], by wfin [h2], by wfin [h3], by wfin [h4],
          by wfin [h5], Or.inl ⟨by wfin [h6], trivial, ?_, ?_⟩⟩, by wfin [h1]⟩
        · wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
        · intro e; rw [vnext] at e; obtain ⟨a, c⟩ := empty e; exact ⟨by wfin [a], by wfin [c]⟩
        · intro e; rw [vnext] at e ⊢; obtain ⟨a, c, d, f⟩ := full e; exact ⟨by wfin [a], c, by wfin [d], f⟩
      · simp only [widthWord, ite_eq_right hw] at width
        have sl : slot fs[j] = 4 := by simp [slot, hw]
        rw [succ, sl] at lj1
        have skip := skip_calls hm fs[j] fitj _ _ mem hpj hroom
        have r := hd.offset (start + Desc.leadingWidth (fs.take j)) (by omega)
        have a := hd.offsetOk (start + Desc.leadingWidth (fs.take j)) (by omega)
        simp only [← Nat.add_assoc] at r a
        have ol := offsetAt_lt b (start + Desc.leadingWidth (fs.take j))
        generalize ho : offsetAt b (start + Desc.leadingWidth (fs.take j)) = o at r ol
        have vo : varOffs b start [fs[j]] (Desc.leadingWidth (fs.take j)) = [o] := by
          simp [varOffs, hw, ho]
        rw [vo] at vnext
        have vrest : varOffs b start (fs[j] :: fs.drop (j + 1)) (Desc.leadingWidth (fs.take j)) =
            o :: varOffs b start (fs.drop (j + 1)) (Desc.leadingWidth (fs.take j) + 4) := by
          simp [varOffs, hw, ho, slot]
        rw [vrest] at vall
        by_cases ve : V = []
        · obtain ⟨s0, p0⟩ := empty ve
          subst ve
          simp only [List.nil_append] at vall vnext
          by_cases fo : o ≠ Desc.leadingWidth fs
          · rw [vall] at hX
            simp only [getElem!_def, List.getElem?_cons_zero, ne_eq, fo, not_false_eq_true,
              ite_true] at hX
            wcall width [h0]
            wsteps [h8, h2, r, a, s0, fo, h4]
            wfail [h4, h5]
            wsteps []
            wcall (skip_calls hm fs[j] fitj _ _ _ (hpj.wrote4 err cpj _ _ _ _) hroom) [h0]
            wsteps [h1]
            refine ⟨⟨j + 1, by omega, ?_, by wfin [], by wfin [succ, sl, h8], by wfin [h2], by wfin [h3], by wfin [h4],
              by wfin [h5], Or.inr ⟨by wfin [], _, hX.symm, by simp [wrote_eq]⟩⟩, by wfin [h1]⟩
            wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
          · simp only [ne_eq, Decidable.not_not] at fo
            wcall width [h0]
            wsteps [h8, h2, r, a, s0, fo, h4]
            wcall skip [h0]
            wsteps [h1]
            refine ⟨⟨j + 1, by omega, ?_, by wfin [], by wfin [succ, sl, h8], by wfin [h2], by wfin [h3], by wfin [h4],
              by wfin [h5], Or.inl ⟨by wfin [h6], trivial, fun e => by rw [vnext] at e; simp at e, fun _ => ?_⟩⟩,
              by wfin [h1]⟩
            · wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
            · rw [vnext]
              refine ⟨by wfin [], by simp [fo], by wfin [fo], ?_⟩
              intro k kp ki _; simp at ki; omega
        · obtain ⟨s1, first, plast, ord⟩ := full ve
          by_cases un : o < V[V.length - 1]!
          · have bad : X = .error .offsetUnordered := by
              rw [← hX, vall]
              have f0 : (V ++ o :: varOffs b start (fs.drop (j + 1)) (Desc.leadingWidth (fs.take j) + 4))[0]! =
                  Desc.leadingWidth fs := by
                rw [getElem!_append_left V _ 0 (by cases V with | nil => exact absurd rfl ve | cons _ _ => simp)]
                exact first
              rw [f0, ite_eq_right (by simp)]
              have vl : 0 < V.length := by cases V with | nil => exact absurd rfl ve | cons _ _ => simp
              refine spans_unordered _ size V.length vl (by simp) (ord_prefix V _ ord) ?_
              rw [getElem!_append_mid, getElem!_append_left V _ (V.length - 1) (by omega)]
              exact un
            wcall width [h0]
            wsteps [h8, h2, r, a, s1, plast, un, h4]
            wfail [h5]
            wsteps []
            wcall (skip_calls hm fs[j] fitj _ _ _ (hpj.wrote4 err cpj _ _ _ _) hroom) [h0]
            wsteps [h1]
            refine ⟨⟨j + 1, by omega, ?_, by wfin [], by wfin [succ, sl, h8], by wfin [h2], by wfin [h3], by wfin [h4],
              by wfin [h5], Or.inr ⟨by wfin [], _, bad, by simp [wrote_eq]⟩⟩, by wfin [h1]⟩
            wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
          · have pl := (V[V.length - 1]!)
            wcall width [h0]
            wsteps [h8, h2, r, a, s1, plast, un, h4]
            wcall skip [h0]
            wsteps [h1]
            refine ⟨⟨j + 1, by omega, ?_, by wfin [], by wfin [succ, sl, h8], by wfin [h2], by wfin [h3], by wfin [h4],
              by wfin [h5], Or.inl ⟨by wfin [h6], trivial, fun e => by rw [vnext] at e; simp at e, fun _ => ?_⟩⟩,
              by wfin [h1]⟩
            · wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
            · rw [vnext]
              have vl : 0 < V.length := by cases V with | nil => exact absurd rfl ve | cons _ _ => simp
              refine ⟨by wfin [], by rw [getElem!_append_left V [o] 0 vl]; exact first, ?_,
                ord_snoc V o ord (fun _ => by omega)⟩
              have := getElem!_append_mid V [] o
              simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
              rw [this]; wfin []
    · have hjc : j = fs.length := by
        rcases Nat.lt_or_ge j fs.length with h | h
        · simp [show fs.length - j ≠ 0 by omega] at z
        · omega
      subst hjc
      simp only [List.take_length] at empty full
      have ne := varOffs_some b start fs 0 some
      obtain ⟨s1, first, plast, ord⟩ := full ne
      rw [← hX, ite_eq_right (by simp [first]), spans_ordered _ size ord]
      have lastlt := getElem!_lt _ (2 ^ 32) (by decide) (varOffs_lt b start fs 0)
        ((varOffs b start fs 0).length - 1)
      by_cases past : size < (varOffs b start fs 0)[(varOffs b start fs 0).length - 1]!
      · wsteps [h6, h3, plast, past]
        wfail [h5]
        wsteps []
        wfin [ne, past, res, after, wrote_eq]
      · wsteps [h6, h3, plast, past]
        wfin [h6, ne, past, res, after]
  · subst mem'
    refine ⟨_, by wev [h1, h6], fun nz => absurd (by wonly []) nz, fun _ => ?_⟩
    wsteps [h6]
    wfin [h6, fails, res, after]

/-- A list nests no deeper than a bound each of its types meets. -/
theorem deepest_le : ∀ (l : List Desc) (D : Nat), (∀ f ∈ l, f.nesting ≤ D) → Desc.deepestNesting l ≤ D
  | [], _, _ => Nat.zero_le _
  | f :: l, D, h => by
    simp only [Desc.deepestNesting]
    have := h f (by simp); have := deepest_le l D (fun g hg => h g (by simp [hg])); omega

/-- A list of types each fitting fits as a whole. -/
theorem allFit_of : ∀ (l : List Desc), (∀ f ∈ l, fitsNative f = true) → allFitNative l = true
  | [], _ => rfl
  | f :: l, h => by
    simp only [allFitNative, Bool.and_eq_true]
    exact ⟨h f (by simp), allFit_of l (fun g hg => h g (by simp [hg]))⟩

/-- Offsets in order never decrease, however far apart. -/
theorem ord_mono (l : List Nat) (ord : OrdUpTo l l.length) (i k : Nat) (hik : i ≤ k) (hk : k < l.length) :
    l[i]! ≤ l[k]! := by
  induction k with
  | zero => rw [show i = 0 by omega]; exact Nat.le_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · have := ord (k + 1) (by omega) hk hk
      simp only [Nat.add_sub_cancel] at this
      have := ih (by omega) (by omega); omega
    · rw [show i = k + 1 by omega]; exact Nat.le_refl _

set_option maxHeartbeats 8000000 in
/-- Every field's range checked in declaration order, stopping at the first refusal. -/
theorem fields_calls {m : Module} {w : World} (hm : Loaded m) (fs : List Desc) (ih : ∀ f ∈ fs, RangeOk m w f)
    (fit : allFitNative fs = true) (p sp : Nat) (mem : Memory) (base : Nat) (b : ByteArray) (start size err : Nat)
    (hp : PlanAt w mem p (Plan.wordsAll fs)) (cp : Clear err p (8 * (Plan.wordsAll fs).length))
    (hd : DataAt w mem base b) (cd : Clear err base b.size) (ok : w.access err 32 = true)
    (inside : start + size ≤ b.size) (small : b.size < 2 ^ 60) (lead : Desc.leadingWidth fs ≤ size)
    (ord : OrdUpTo (varOffs b start fs 0) (varOffs b start fs 0).length)
    (last : varOffs b start fs 0 ≠ [] → (varOffs b start fs 0)[(varOffs b start fs 0).length - 1]! ≤ size)
    (room : Room w sp (Desc.deepestNesting fs + 1) 2) :
    Calls m w "ssz_validate_fields" sp [UInt64.ofNat p, UInt64.ofNat fs.length, UInt64.ofNat (base + start),
      UInt64.ofNat size, UInt64.ofNat err] mem
      (res (validateFields fs b (rangesFrom b start size fs 0)))
      (after mem err (validateFields fs b (rangesFrom b start size fs 0))) := by
  have hb := hp.bound
  have db := hd.bound
  have hl := length_le_wordsAll fs
  have eb : err + 32 ≤ 2 ^ 63 := by
    have := ok; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  generalize hX : validateFields fs b (rangesFrom b start size fs 0) = X
  refine Calls.body 15 hm.fields rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [fieldsFn]
  wsteps []
  refine Wp.loop (wp_loop (fun env mem' => ∃ j, j ≤ fs.length ∧
      env 0 = UInt64.ofNat (p + 8 * (Plan.wordsAll (fs.take j)).length) ∧ env 1 = UInt64.ofNat (fs.length - j) ∧
      env 7 = UInt64.ofNat (Desc.leadingWidth (fs.take j)) ∧ env 2 = UInt64.ofNat (base + start) ∧
      env 3 = UInt64.ofNat size ∧ env 4 = UInt64.ofNat err ∧
      ((env 5 = 0 ∧ mem' = mem ∧
          X = validateFields (fs.drop j) b (rangesFrom b start size (fs.drop j) (Desc.leadingWidth (fs.take j)))) ∨
       (env 5 = 1 ∧ ∃ x, X = .error x ∧ mem' = wrote mem err x)))
    (fun env _ => (env 1).toNat)
    ⟨0, Nat.zero_le _, by wfin [Plan.wordsAll], by wfin [], by wfin [Desc.leadingWidth], by wfin [], by wfin [],
      by wfin [], Or.inl ⟨by wfin [], rfl, by simp [Desc.leadingWidth, hX]⟩⟩ ?_)
  rintro env mem' ⟨j, hj, h0, h1, h7, h2, h3, h4, st⟩
  have hjl := wordsAll_take_le fs j
  have lj := leadingWidth_take_le fs j
  rcases st with ⟨h5, hmem, rest⟩ | ⟨h5, x, fails, hmem⟩
  · subst mem'
    refine ⟨_, by wev [h1, h5], fun nz => ?_, fun z => ?_⟩
    · have hjf : j < fs.length := by
        rcases Nat.lt_or_ge j fs.length with h | h
        · exact h
        · simp [show fs.length - j = 0 by omega] at nz
      obtain ⟨_, hpj, slen⟩ := fieldAt hp j hjf
      have cpj : Clear err (p + 8 * (Plan.wordsAll (fs.take j)).length) (8 * (Plan.words fs[j]).length) := by
        unfold Clear at cp ⊢; omega
      have nest := nesting_le_deepest fs fs[j] (List.getElem_mem hjf)
      have fitj := fits_getElem fs fit j hjf
      have hroom : Room w (sp - 8 - 8 * 15) fs[j].nesting 4 := by simp only [Room] at room ⊢; omega
      have width := width_calls hm fs[j] fitj _ (sp - 8 - 8 * 15) mem hpj (by simp only [Room] at hroom ⊢; omega)
      have skip := skip_calls hm fs[j] fitj _ (sp - 8 - 8 * 15) mem hpj (by simp only [Room] at hroom ⊢; omega)
      have succ := leading_succ fs j hjf
      have lj1 := leadingWidth_take_le fs (j + 1)
      have whole : Desc.leadingWidth fs =
          Desc.leadingWidth (fs.take (j + 1)) + Desc.leadingWidth (fs.drop (j + 1)) := by
        conv => lhs; rw [← List.take_append_drop (j + 1) fs]
        rw [leadingWidth_append]
      rw [drop_cons fs j hjf] at rest
      simp only [rangesFrom] at rest
      by_cases hw : hasWidth fs[j] = true
      · simp only [widthWord, ite_eq_left hw] at width
        have fw := fixedWidth_lt fs[j] fitj hw
        have hne : fixedWidth fs[j] ≠ 18446744073709551615 := by omega
        have sl : slot fs[j] = fixedWidth fs[j] := by simp [slot, hw]
        rw [succ, sl] at lj1 whole
        simp only [rangeOf, hw, ite_true] at rest
        rw [validateFields] at rest
        have step := ih fs[j] (List.getElem_mem hjf) fitj _ (sp - 8 - 8 * 15) mem base b
          (start + Desc.leadingWidth (fs.take j)) (start + Desc.leadingWidth (fs.take j) + fixedWidth fs[j]) err
          hpj cpj hd cd ok (by omega) (by omega) small hroom
        rcases hR : validateRange fs[j] b (start + Desc.leadingWidth (fs.take j))
            (start + Desc.leadingWidth (fs.take j) + fixedWidth fs[j]) with y | u
        · rw [hR] at step rest
          simp only [res, after, wrote_eq] at step
          wcall width [h0]
          wcall skip [h0]
          wsteps [hne]
          wcall step [h0, h2, h4, h7]
          wsteps [h7, h1]
          refine ⟨⟨j + 1, by omega, ?_, by wfin [], by wfin [succ, sl, h7], by wfin [h2], by wfin [h3],
            by wfin [h4], Or.inr ⟨by wfin [], y, ?_, rfl⟩⟩, by wfin [h1]⟩
          · wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
          · rw [rest]; rfl
        · rw [hR] at step rest
          simp only [res, after] at step
          wcall width [h0]
          wcall skip [h0]
          wsteps [hne]
          wcall step [h0, h2, h4, h7]
          wsteps [h7, h1]
          refine ⟨⟨j + 1, by omega, ?_, by wfin [], by wfin [succ, sl, h7], by wfin [h2], by wfin [h3],
            by wfin [h4], Or.inl ⟨by wfin [], trivial, ?_⟩⟩, by wfin [h1]⟩
          · wfin [take_succ_append fs j hjf, wordsAll_append, Plan.wordsAll]
          · rw [rest, succ, sl]; rfl
      · simp only [widthWord, ite_eq_right hw] at width
        have sl : slot fs[j] = 4 := by simp [slot, hw]
        rw [succ, sl] at lj1 whole
        simp only [rangeOf, hw, Bool.false_eq_true, ite_false] at rest
        rw [validateFields] at rest
        -- The body's end: the next body's start, or the size, never before its own start.
        have vall : varOffs b start fs 0 = varOffs b start (fs.take j) 0 ++
            offsetAt b (start + Desc.leadingWidth (fs.take j)) ::
              varOffs b start (fs.drop (j + 1)) (Desc.leadingWidth (fs.take j) + 4) := by
          rw [varOffs_split b start fs 0 j, drop_cons fs j hjf, Nat.zero_add]
          simp [varOffs, hw, slot]
        have r := hd.offset (start + Desc.leadingWidth (fs.take j)) (by omega)
        have a := hd.offsetOk (start + Desc.leadingWidth (fs.take j)) (by omega)
        simp only [← Nat.add_assoc] at r a
        have ol := offsetAt_lt b (start + Desc.leadingWidth (fs.take j))
        generalize ho : offsetAt b (start + Desc.leadingWidth (fs.take j)) = o at r ol vall rest
        generalize hV : varOffs b start (fs.take j) 0 = V at vall
        generalize hR' : varOffs b start (fs.drop (j + 1)) (Desc.leadingWidth (fs.take j) + 4) = R at vall
        have bounds : o ≤ R.headD size ∧ R.headD size ≤ size := by
          rw [vall] at ord last
          have lo : (V ++ o :: R)[V.length]! = o := getElem!_append_mid V R o
          cases R with
          | nil =>
            have := last (by simp)
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            rw [show V.length + (0 + 1) - 1 = V.length by omega, lo] at this
            simp; omega
          | cons r0 R0 =>
            have l1 : (V ++ o :: r0 :: R0)[V.length + 1]! = r0 := by
              simp
            have step1 := ord (V.length + 1) (by omega) (by simp) (by simp)
            simp only [Nat.add_sub_cancel, lo, l1] at step1
            have step2 := ord_mono _ ord (V.length + 1) ((V ++ o :: r0 :: R0).length - 1) (by simp) (by simp)
            have := last (by simp)
            rw [l1] at step2
            simp; omega
        have hpn : PlanAt w mem (p + 8 * (Plan.wordsAll (fs.take (j + 1))).length) (Plan.wordsAll (fs.drop (j + 1))) := by
          have := hp; rw [← List.take_append_drop (j + 1) fs, wordsAll_append] at this; exact this.right
        have hin : start + (Desc.leadingWidth (fs.take j) + 4) + Desc.leadingWidth (fs.drop (j + 1)) ≤ b.size := by
          omega
        have nb := nextBody_calls hm (fs.drop (j + 1))
          (allFit_of _ (fun f hf => allFitNative_mem fs fit f (List.mem_of_mem_drop hf)))
          _ (sp - 8 - 8 * 15) mem base b start (Desc.leadingWidth (fs.take j) + 4) size hpn hd hin
          (by
            have := deepest_le (fs.drop (j + 1)) (Desc.deepestNesting fs)
              (fun f hf => nesting_le_deepest fs f (List.mem_of_mem_drop hf))
            simp only [Room] at room ⊢; omega)
        simp only [nextOff, hR'] at nb
        have tl : (Plan.wordsAll (fs.take (j + 1))).length =
            (Plan.wordsAll (fs.take j)).length + (Plan.words fs[j]).length := by
          rw [wordsAll_take_succ fs j hjf]; simp
        have dl : (fs.drop (j + 1)).length = fs.length - (j + 1) := List.length_drop
        have step := ih fs[j] (List.getElem_mem hjf) fitj _ (sp - 8 - 8 * 15) mem base b
          (start + o) (start + R.headD size) err hpj cpj hd cd ok (by omega) (by omega) small hroom
        simp only [nextOff, hR'] at rest
        rcases hR : validateRange fs[j] b (start + o) (start + R.headD size) with y | u
        · rw [hR] at step rest
          simp only [res, after, wrote_eq] at step
          wcall width [h0]
          wcall skip [h0]
          wsteps []
          wcall nb [h0, h1, h2, h3, h7, tl, dl]
          wsteps [h2, h7, r, a]
          wcall step [h0, h2, h4, h7, r, a]
          wsteps [h7, h1]
          refine ⟨⟨j + 1, by omega, ?_, by wfin [], by wfin [succ, sl, h7], by wfin [h2], by wfin [h3],
            by wfin [h4], Or.inr ⟨by wfin [], y, ?_, rfl⟩⟩, by wfin [h1]⟩
          · wfin [tl]
          · rw [rest]; rfl
        · rw [hR] at step rest
          simp only [res, after] at step
          wcall width [h0]
          wcall skip [h0]
          wsteps []
          wcall nb [h0, h1, h2, h3, h7, tl, dl]
          wsteps [h2, h7, r, a]
          wcall step [h0, h2, h4, h7, r, a]
          wsteps [h7, h1]
          refine ⟨⟨j + 1, by omega, ?_, by wfin [], by wfin [succ, sl, h7], by wfin [h2], by wfin [h3],
            by wfin [h4], Or.inl ⟨by wfin [], trivial, ?_⟩⟩, by wfin [h1]⟩
          · wfin [tl]
          · rw [rest, succ, sl]; rfl
    · have hjc : j = fs.length := by
        rcases Nat.lt_or_ge j fs.length with h | h
        · simp [show fs.length - j ≠ 0 by omega] at z
        · omega
      subst hjc
      simp only [List.drop_length, rangesFrom] at rest
      have : validateFields [] b [] = .ok () := by rw [validateFields]
      rw [this] at rest
      exact Wp.done ⟨by wonly [h5, rest, res], by simp [after, rest]⟩
  · subst mem'
    refine ⟨_, by wev [h1, h5], fun nz => absurd (by wonly []) nz, fun _ => ?_⟩
    exact Wp.done ⟨by wonly [h5, fails, res], by simp [after, fails]⟩

set_option maxHeartbeats 8000000 in
/-- Checking a struct natively refuses exactly as the Lean check does. -/
theorem struct_calls {m : Module} {w : World} (hm : Loaded m) (fs : List Desc) (ih : ∀ f ∈ fs, RangeOk m w f)
    (fit : allFitNative fs = true) (lead : Desc.leadingWidth fs < 2 ^ 32) (p sp : Nat) (mem : Memory) (base : Nat)
    (b : ByteArray) (start stop err : Nat)
    (hp : PlanAt w mem p (Plan.wordsAll fs)) (cp : Clear err p (8 * (Plan.wordsAll fs).length))
    (hd : DataAt w mem base b) (cd : Clear err base b.size) (ok : w.access err 32 = true)
    (hle : start ≤ stop) (hs : stop ≤ b.size) (small : b.size < 2 ^ 60)
    (room : Room w sp (Desc.deepestNesting fs + 1) 3) :
    Calls m w "ssz_validate_struct" sp [UInt64.ofNat p, UInt64.ofNat fs.length, UInt64.ofNat (base + start),
      UInt64.ofNat (base + stop), UInt64.ofNat err] mem
      (res (validateStruct fs b start stop)) (after mem err (validateStruct fs b start stop)) := by
  have hb := hp.bound
  have db := hd.bound
  have hl := length_le_wordsAll fs
  have eb : err + 32 ≤ 2 ^ 63 := by
    have := ok; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  have hsz : base + stop - (base + start) = stop - start := by omega
  have fwl : fieldsWidth fs ≤ Desc.leadingWidth fs ∨ allHaveWidth fs = false := by
    by_cases a : allHaveWidth fs = true
    · left; rw [leadingWidth_of_all fs a]; exact Nat.le_refl _
    · right; simpa using a
  rw [struct_outcome]
  have fwc := fieldsWidth_calls hm fs (fun f hf => width_calls hm f) fit lead p (sp - 8 - 8 * 15) mem hp
    (by simp only [Room] at room ⊢; omega)
  refine Calls.body 15 hm.struct rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [structFn]
  wsteps [hsz]
  by_cases o : 2 ^ 32 ≤ stop - start
  · wsteps [hsz, o]
    wfail []
    wsteps []
    wfin [o, res, after, wrote_eq]
  wsteps [hsz, o]
  by_cases all : allHaveWidth fs = true
  · simp only [fieldsWord, ite_eq_left all] at fwc
    have fw : fieldsWidth fs < 2 ^ 32 := by rw [← leadingWidth_of_all fs all]; exact lead
    have hne : fieldsWidth fs ≠ 18446744073709551615 := by omega
    wcall fwc []
    wsteps [hne]
    by_cases sc : stop - start ≠ fieldsWidth fs
    · wsteps [sc]
      wfail []
      wsteps []
      wfin [o, all, sc, res, after, wrote_eq]
    · simp only [ne_eq, Decidable.not_not] at sc
      have none := varOffs_all b start fs 0 all
      have flds := fields_calls hm fs ih fit p (sp - 8 - 8 * 15) mem base b start (stop - start) err hp cp hd cd ok
        (by omega) small (by rw [leadingWidth_of_all fs all]; omega)
        (by rw [none]; intro k _ ki; simp at ki) (by rw [none]; intro h; exact absurd rfl h)
        (by simp only [Room] at room ⊢; omega)
      wsteps [sc]
      have hfw : ¬ 4294967296 ≤ fieldsWidth fs := by omega
      wcall flds []
      wsteps []
      wfin [o, all, sc, hfw]
  · simp only [Bool.not_eq_true] at all
    simp only [fieldsWord, all, Bool.false_eq_true, ite_false] at fwc
    have lc := leading_calls hm fs fit p (sp - 8 - 8 * 15) mem hp (by simp only [Room] at room ⊢; omega)
    wcall fwc []
    wsteps []
    wcall lc []
    by_cases tl : stop - start < Desc.leadingWidth fs
    · wsteps [tl]
      wfail []
      wsteps []
      wfin [o, all, tl, res, after, wrote_eq]
    · have il := inline_calls hm fs ih fit p (sp - 8 - 8 * 15) mem base b start err hp cp hd cd ok (by omega) small
        (by simp only [Room] at room ⊢; omega)
      wsteps [tl]
      wcall il []
      rcases hI : validateInline fs b (placesFrom b start fs 0) with x | u
      · wsteps [res]
        wfin [o, all, tl, hI, res, after, Bind.bind, Except.bind]
      · have ss := structSpans_calls hm fs fit all p (sp - 8 - 8 * 15) mem base b start (stop - start) err hp cp hd
          ok (by omega) (by omega) lead (by simp only [Room] at room ⊢; omega)
        by_cases c : (varOffs b start fs 0)[0]! ≠ Desc.leadingWidth fs
        · rw [ite_eq_left c] at ss
          wsteps [res]
          wcall ss []
          wsteps [res]
          wfin [o, all, tl, hI, c, res, after, Bind.bind, Except.bind]
        · rw [ite_eq_right c] at ss
          simp only [ne_eq, Decidable.not_not] at c
          rcases hS : spansOutcome (varOffs b start fs 0) (stop - start) with y | v
          · rw [hS] at ss
            wsteps [res]
            wcall ss []
            wsteps [res]
            wfin [o, all, tl, hI, c, hS, res, after, Bind.bind, Except.bind]
          · rw [hS] at ss
            obtain ⟨ord, last⟩ := spansOutcome_ok _ _ hS
            have flds := fields_calls hm fs ih fit p (sp - 8 - 8 * 15) mem base b start (stop - start) err hp cp hd
              cd ok (by omega) small (by omega) ord last (by simp only [Room] at room ⊢; omega)
            wsteps [res]
            wcall ss []
            wsteps [res]
            wcall flds []
            wsteps []
            wfin [o, all, tl, hI, c, hS, Bind.bind, Except.bind]

end EthLib.Consensus.Ssz.Native.Driver.Validate
