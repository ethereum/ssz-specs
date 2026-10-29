import SszNative.Proofs.Driver.Root.Fields
import SszNative.Proofs.Driver.Root.Union

/-!
The container driver writes the Lean root of a container whose fields are rooted one by one.

The fields driver writes the field roots into the scratch, and the tree driver folds them into the root.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Asm

/-! ### Roots of fields -/

/-- The roots of a struct's fields, one per field, each the root of its range. -/
theorem fieldRoots_get (b : ByteArray) : ∀ (fields : List Desc) (rl : List (Nat × Nat)),
    rl.length = fields.length → (fieldRoots fields b rl).length = fields.length ∧
      ∀ i (h : i < fields.length) (h' : i < (fieldRoots fields b rl).length),
        (fieldRoots fields b rl)[i] = rootOf fields[i] b (rl.getD i (0, 0)).1 (rl.getD i (0, 0)).2
  | [], rl, _ => by rw [fieldRoots.eq_def]; simp
  | f :: fs, [], h => by simp at h
  | f :: fs, (s, e) :: rest, h => by
    obtain ⟨len, each⟩ := fieldRoots_get b fs rest (by simpa using h)
    rw [fieldRoots.eq_def]
    refine ⟨by simp [len], fun i hi hi' => ?_⟩
    cases i with
    | zero => rfl
    | succ i => simpa using each i (by simpa using hi) (by simpa [len] using hi)

/-- The roots of a struct's fields: one node each, field j's from its range. -/
theorem fieldRoots_nodes {fields : List Desc} {b : ByteArray} {start stop : Nat}
    (sound : ∀ f ∈ fields, f.wellFormed = .ok ()) (inside : stop ≤ b.size) (small : RootProof.Small b)
    (ranges : ∀ j (_ : j < fields.length), start ≤ (fieldRg fields b start stop j).1 ∧
      (fieldRg fields b start stop j).1 ≤ (fieldRg fields b start stop j).2 ∧
      (fieldRg fields b start stop j).2 ≤ stop ∧
      ∃ v, deserialize fields[j] (slice b (fieldRg fields b start stop j).1 (fieldRg fields b start stop j).2) =
        .ok v) :
    (fieldRoots fields b (rangesOf start (stop - start) (placesFrom fields b start 0))).length = fields.length ∧
      (∀ r ∈ fieldRoots fields b (rangesOf start (stop - start) (placesFrom fields b start 0)), r.size = 32) ∧
      ∀ i (h : i < fields.length) (h' : i < (fieldRoots fields b
        (rangesOf start (stop - start) (placesFrom fields b start 0))).length),
        (fieldRoots fields b (rangesOf start (stop - start) (placesFrom fields b start 0)))[i] =
          rootOf fields[i] b (fieldRg fields b start stop i).1 (fieldRg fields b start stop i).2 := by
  obtain ⟨len, each⟩ := fieldRoots_get b fields (rangesOf start (stop - start) (placesFrom fields b start 0))
    (by rw [rangesOf_length, placesFrom_length])
  refine ⟨len, fun r mem => ?_, each⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mem
  have hi' : i < fields.length := by omega
  rw [each i hi' hi]
  obtain ⟨-, ord, stp, acc⟩ := ranges i hi'
  exact rootOf_size (sound _ (List.getElem_mem hi')) ord (Nat.le_trans stp inside) small acc

/-! ### The container driver -/

/-- The container driver's frame holds fifteen words. -/
theorem containerFrame : RootContainer.fn.frame = 15 := by decide

/-- A container's stack is a level more than its deepest field's. -/
theorem rootStack_container (names : List String) (fields : List Desc) :
    rootStack (.container names fields) = 12288 + 1024 * Desc.deepestNesting fields + 1024 := by
  simp only [rootStack, Desc.nesting]; omega

/-- A field finds its stack below the container's frame and the fields driver's. -/
theorem container_room {lo sp n D : Nat} (hn : n ≤ D) (h : lo + (12288 + 1024 * D + 1024) + 0 ≤ sp) :
    lo + 176 + (12288 + 1024 * n) + 256 ≤ sp - 128 ∧ lo + 176 ≤ sp - 128 ∧ lo + 8 + 8 * 15 ≤ sp ∧
      lo + 10552 ≤ sp - 128 := by
  omega

/-- A container's scratch below the cap: the field roots and the table then a field's scratch, or the tree's. -/
theorem varNeed_container {names : List String} {fields : List Desc} {size : Nat}
    (notPlain : plain (.container names fields) = false) (below : varNeed (.container names fields) size < scratchCap) :
    varNeed (.container names fields) size = max (56 * fields.length + fieldsVarNeed fields size 0)
      (32 * fields.length + 32 + (2560 + 2048 + 32 * fields.length)) := by
  simp only [varNeed, notPlain, Bool.false_eq_true, ite_false, treeNeed, RootProgressive.spineBytes, zeroHeights,
    sadd, smul, sat] at below ⊢
  have := cap_eq
  omega

set_option maxHeartbeats 8000000 in
/-- The container driver writes the Lean root of a container whose fields are rooted one by one. -/
theorem rootContainer_ok {m : Module} {w : World} (hash : HashingOk m w) (fns : RangeFns m) {names : List String}
    {fields : List Desc} (ih : ∀ f ∈ fields, RootOfOk m w f) (notPlain : plain (.container names fields) = false) :
    RangeOk m w "ssz_root_container" (.container names fields) := by
  intro sp mem p base start stop out scratch ctx table zeros pad mask b room pre
  have usize := pre.usize
  have small := pre.small
  unfold RootProof.Small at small
  rw [usize] at small
  have ordered := pre.ordered
  have inside := pre.inside
  have bound : addressBound = 2 ^ 63 := rfl
  have zh : zeroHeights = 64 := rfl
  have soundF : ∀ f ∈ fields, f.wellFormed = .ok () := Validate.allWellFormed_mem fields (wellFormed_container pre.sound)
  have thinAll : narrowAll fields = true := by
    have := pre.thin; simp only [narrow, Bool.and_eq_true] at this; exact this.2
  -- What decoding gives: the fields' ranges, inside the struct, each decoding.
  obtain ⟨v, read⟩ := pre.accepted
  simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i values read'
  obtain ⟨cut, lead, ranges⟩ := struct_decoded ordered inside read'
  -- The scratch: the field roots and the table, then a field's scratch or the tree's.
  obtain ⟨F, hF⟩ : ∃ F, fieldsVarNeed fields (stop - start) 0 = F := ⟨_, rfl⟩
  have need : varNeed (.container names fields) (stop - start) =
      max (56 * fields.length + F) (32 * fields.length + 32 + (2560 + 2048 + 32 * fields.length)) := by
    rw [← hF]; exact varNeed_container notPlain pre.below
  have sAcc := pre.sAcc
  have sB := pre.sB
  have sPad := pre.sPad
  have sCtx := pre.sCtx
  have sTable := pre.sTable
  have sZeros := pre.sZeros
  have sOut := pre.sOut
  have sPlan := pre.sPlan
  have sSlack := pre.sSlack
  have below := pre.below
  rw [need] at sAcc sB sPad sCtx sTable sZeros sOut sPlan sSlack below
  have as := access_bound sAcc
  -- The fields' plans follow the container's two words.
  have words : Plan.words (.container names fields) = [10, fields.length] ++ Plan.wordsAll fields := by
    rw [Plan.words]
  have planF : WordsAt w mem (p + 16) (Plan.wordsAll fields) := by
    have := (wordsAt_split (by rw [← words]; exact pre.plan)).2
    simpa using this
  have planIn : p ≤ p + 16 ∧ p + 16 + 8 * (Plan.wordsAll fields).length ≤
      p + 8 * (Plan.words (.container names fields)).length := by
    rw [words, List.length_append]; simp; omega
  have fitsF : Fits (Plan.wordsAll fields) := by
    have := pre.fits; rw [words] at this; exact (fits_split this).2
  -- The stack.
  let sp' := sp - 8 - 8 * RootContainer.fn.frame
  have spEq : sp' = sp - 128 := by simp only [sp', containerFrame]; omega
  rw [rootStack_container] at room
  have roomF : w.stackLo + 176 ≤ sp' := by rw [spEq]; exact (container_room (Nat.le_refl _) room).2.1
  have room' : ∀ f ∈ fields, w.stackLo + 176 + rootStack f + 256 ≤ sp' := fun f mf => by
    rw [spEq]; exact (container_room (nesting_le_deepest fields f mf) room).1
  have treeRoom : w.stackLo + treeStack ≤ sp' := by
    rw [spEq]; exact (container_room (Nat.le_refl _) room).2.2.2
  have ev := rangeEnv_entry p (base + start) (stop - start) out scratch ctx
  -- The field count.
  have nw : eval w (entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (stop - start),
      UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx]) mem (ld (RootContainer.p + 8)) =
      some (UInt64.ofNat fields.length) :=
    eval_word pre.plan 1 (by simp [Plan.words]) (e := RootContainer.p + 8) (eval_add (eval_var ev.p) (eval_lit 8))
  have s1 := Runs.set' (m := m) (w := w) (sp := sp') (x := 6) nw
  have ev1 := ev.write (x := 6) (UInt64.ofNat fields.length) (by decide)
  have l1 : Asm.assign (entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (stop - start),
      UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx]) 6 (UInt64.ofNat fields.length) 6 =
      UInt64.ofNat fields.length := assign_eq
  generalize Asm.assign (entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (stop - start),
    UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx]) 6 (UInt64.ofNat fields.length) = E1 at s1 ev1 l1
  -- The field roots, into the scratch.
  have fpre : FieldsPre w mem fields (p + 16) base start stop scratch (56 * fields.length + F) ctx table zeros pad
      mask b :=
    { ready := pre.ready, plan := planF, fits := fitsF, holds := pre.holds, bAcc := pre.bAcc, ordered := ordered,
      inside := inside, small := pre.small, spread := pre.spread, sound := soundF,
      thin := narrowAll_mem fields thinAll, lead := lead, ranges := ranges,
      room := by rw [hF]; exact Nat.le_refl _, below := by rw [hF]; omega,
      rAcc := access_sub sAcc (by omega) (by omega), rSlack := by omega,
      rB := apart_sub sB (by omega) (by omega), rPad := apart_sub sPad (by omega) (by omega),
      rCtx := apart_sub sCtx (by omega) (by omega), rTable := apart_sub sTable (by omega) (by omega),
      rZeros := apart_sub sZeros (by omega) (by omega),
      rPlan := apart_sub' (apart_sub sPlan (by omega) (by omega)) planIn.1 planIn.2, bPad := pre.bPad,
      planPad := apart_comm (apart_sub' (apart_comm pre.planPad) planIn.1 planIn.2), usize := usize }
  obtain ⟨mem1, call1, roots, ready1, keep1⟩ := rootFields_calls fns ih roomF room' fpre
  have r2 := Runs.call (m := m) (sp := sp') (env := E1) (mem := mem) (dst := 8)
    (args := [RootContainer.p + 16, RootContainer.n, RootContainer.src, RootContainer.size, RootContainer.scratch,
      RootContainer.ctx])
    (by
      simp only [List.mapM_cons, List.mapM_nil, eval_add (eval_var ev1.p) (eval_lit 16), eval_var l1,
        eval_var ev1.src, eval_var ev1.size, eval_var ev1.scratch, eval_var ev1.ctx]
      rfl) call1
  have ev2 := ev1.write (x := 8) 0 (by decide)
  have l2 : Asm.assign E1 8 0 6 = UInt64.ofNat fields.length := by rw [assign_ne (by decide)]; exact l1
  generalize Asm.assign E1 8 0 = E2 at r2 ev2 l2
  -- The tree's depth.
  have lsmall : fields.length < 2 ^ 64 := by omega
  have dframe : DepthFor.fn.frame = 5 := by decide
  have dcall := depthFor_calls (m := m) (w := w) fns.roots.plan.depth (sp := sp') (by rw [dframe]; omega)
    (UInt64.ofNat fields.length) mem1
  rw [ofNat_toNat lsmall] at dcall
  have r3 := Runs.call (m := m) (sp := sp') (env := E2) (mem := mem1) (dst := 7) (args := [RootContainer.n])
    (by simp only [List.mapM_cons, List.mapM_nil, eval_var l2]; rfl) dcall
  have ev3 := ev2.write (x := 7) (depthFor fields.length).toUInt64 (by decide)
  have l3 : Asm.assign E2 7 (depthFor fields.length).toUInt64 6 = UInt64.ofNat fields.length := by
    rw [assign_ne (by decide)]; exact l2
  have d3 : Asm.assign E2 7 (depthFor fields.length).toUInt64 7 = UInt64.ofNat (depthFor fields.length) := assign_eq
  generalize Asm.assign E2 7 (depthFor fields.length).toUInt64 = E3 at r3 ev3 l3 d3
  -- The tree over the field roots, into the output.
  have deep : depthFor fields.length ≤ 64 := depthFor_le_of_le_two_pow (by omega)
  have tpre : TreePre w mem1 scratch fields.length (depthFor fields.length) out (scratch + 32 * fields.length + 32)
      ctx table zeros pad mask :=
    { ctxAccess := ready1.ctxAccess, maskAt := ready1.maskAt, tableAt := ready1.tableAt, zerosAt := ready1.zerosAt,
      padAt := ready1.padAt, tableBytes := ready1.tableHeld, tableAccess := ready1.tableAccess,
      zeroRoots := ready1.zeroRoots, zerosAccess := ready1.zerosAccess, deep := by rw [zh]; omega,
      fits := le_two_pow_depthFor _, nodesAccess := access_sub sAcc (by omega) (by omega),
      outAccess := pre.oAcc, scratchAccess := access_sub sAcc (by omega) (by omega),
      padAccess := ready1.padAccess, scratchNodes := by simp only [Apart]; omega,
      scratchOut := apart_sub sOut (by omega) (by omega), scratchCtx := apart_sub sCtx (by omega) (by omega),
      scratchTable := apart_sub sTable (by omega) (by omega), scratchZeros := apart_sub sZeros (by omega) (by omega),
      scratchPad := apart_sub sPad (by omega) (by omega),
      padNodes := apart_comm (apart_sub sPad (by omega) (by omega)), padCtx := ready1.padCtx,
      padTable := ready1.padTable, padZeros := ready1.padZeros, nodesReach := by omega,
      outNodes := apart_comm (apart_sub sOut (by omega) (by omega)), outZeros := pre.oZeros }
  obtain ⟨mem2, call2, root2, keep2⟩ := treeCalls_native hash.merkleize (sp := sp') tpre ready1.kernels treeRoom
    (by rw [usize]; omega)
  have r4 := Runs.call (m := m) (sp := sp') (env := E3) (mem := mem1) (dst := 8)
    (args := [RootContainer.scratch, RootContainer.n, RootContainer.d, RootContainer.out,
      RootContainer.scratch + 32 * RootContainer.n + 32, RootContainer.ctx])
    (by
      simp only [List.mapM_cons, List.mapM_nil, eval_var ev3.scratch, eval_var l3, eval_var d3, eval_var ev3.out,
        eval_add (eval_add (eval_var ev3.scratch) (eval_mul (eval_lit 32) (eval_var l3))) (eval_lit 32),
        eval_var ev3.ctx]
      rfl) call2
  have body : Runs m w sp' (entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (stop - start),
      UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx]) mem RootContainer.fn.body (Asm.assign E3 8 0) mem2 :=
    Runs.block_cons s1 (Runs.block_cons r2 (Runs.block_cons r3 (Runs.block_cons r4 (Runs.block_nil _ _ _ _ _))))
  have frame : ∀ a, ¬ (out ≤ a ∧ a < out + 32) →
      ¬ (scratch ≤ a ∧ a < scratch + varNeed (.container names fields) (stop - start)) →
      ¬ (pad ≤ a ∧ a < pad + 1536) → mem2 a = mem a := fun a o s pd => by
    rw [need] at s
    rw [keep2 a (fun h => s ⟨by omega, by omega⟩) pd o]
    exact keep1 a (fun h => s ⟨by omega, by omega⟩) pd
  refine ⟨mem2, Calls.fn fns.container (by rw [containerFrame]; exact (container_room (Nat.le_refl _) room).2.2.1)
    rfl body rfl, ?_, pre.readyAfter frame, frame⟩
  -- The root: the tree over the field roots.
  obtain ⟨rlen, sized, each⟩ := fieldRoots_nodes soundF inside pre.small ranges
  have nodes : ∀ i (h : i < (fieldRoots fields b (rangesOf start (stop - start) (placesFrom fields b start 0))).length),
      nodeAt mem1 (scratch + 32 * i) =
        (fieldRoots fields b (rangesOf start (stop - start) (placesFrom fields b start 0)))[i].data := by
    intro i h
    rw [roots i (by omega), each i (by omega) h]
  have code : rootOf (.container names fields) b start stop = merkleizeDepth
      (joinNodes (fieldRoots fields b (rangesOf start (stop - start) (placesFrom fields b start 0))))
      fields.length (depthFor fields.length) := by
    rw [rootOf]
    simp only [notPlain, Bool.false_eq_true, ite_false, merkleizeCapacity, cut, Except.toOption, Option.getD_some]
  rw [root2, code]
  exact merkleizeDepth_of_nodes rlen sized nodes (le_two_pow_depthFor _) (by rw [usize]; omega)

end EthLib.Consensus.Ssz.Native.Driver
