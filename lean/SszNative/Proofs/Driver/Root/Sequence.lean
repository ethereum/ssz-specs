import EthLib.Consensus.Proofs.Ssz.Codec.DecodeFits
import SszNative.Proofs.Driver.Root.Elements

/-!
The vector driver writes the Lean root of a vector whose elements are rooted one by one.

The elements driver writes the element roots into the scratch, and the tree driver folds them into the root.
The facts here about element roots and their tree serve the list and container drivers too.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Asm

/-! ### Roots of ranges -/

/-- The root of a range that decodes is one node. -/
theorem rootOf_size {d : Desc} (sound : d.wellFormed = .ok ()) {b : ByteArray} {start stop : Nat}
    (ordered : start ≤ stop) (inside : stop ≤ b.size) (small : RootProof.Small b)
    (accepted : ∃ v, deserialize d (slice b start stop) = .ok v) : (rootOf d b start stop).size = 32 := by
  obtain ⟨v, read⟩ := accepted
  have := RootProof.agrees RootProof.facts_hold d sound b start stop v ordered inside small read
  rw [← ByteArray.size_data]
  exact hashTreeRoot_size d v _ this

/-- The roots of ranges are the root of each range, in order. -/
theorem variableRoots_eq_map (element : Desc) (b : ByteArray) :
    ∀ ranges : List (Nat × Nat), variableRoots element b ranges = ranges.map fun p => rootOf element b p.1 p.2
  | [] => by rw [variableRoots.eq_def]; rfl
  | (s, e) :: rest => by rw [variableRoots.eq_def]; simp [variableRoots_eq_map element b rest]

/--
The tree over nodes memory holds is the tree over the same nodes joined into a buffer.

Node i in memory is buffer i of the list, and every buffer is one node.
-/
theorem merkleizeDepth_of_nodes {mem : Memory} {a n depth : Nat} {rs : List ByteArray} (len : rs.length = n)
    (sized : ∀ r ∈ rs, r.size = 32) (nodes : ∀ i (h : i < rs.length), nodeAt mem (a + 32 * i) = rs[i].data)
    (fits : n ≤ 2 ^ depth) (small : 32 * n + 64 < USize.size) :
    (merkleizeDepth (bytesAt mem a (32 * n)) n depth).data = (merkleizeDepth (joinNodes rs) n depth).data := by
  obtain ⟨joined, size⟩ := RootProof.joinNodes_nodes rs sized
  rw [len] at joined size
  have bsize : (bytesAt mem a (32 * n)).size = 32 * n := by simp [bytesAt, ByteArray.size]
  rw [(merkleizeDepth_spec _ n depth fits (by omega) (by omega)).2,
    (merkleizeDepth_spec _ n depth fits (by omega) (by omega)).2]
  congr 1
  have e : nodesFrom (joinNodes rs) 0 n = (rs.map ByteArray.data).toArray := joined
  rw [e]
  apply Array.ext
  · simp [len]
  · intro i hi _
    have hi' : i < n := by simpa using hi
    simp only [nodesFrom, Array.getElem_ofFn, List.getElem_toArray, List.getElem_map]
    rw [nodeOf_bytesAt mem a n i hi', nodes i (by omega)]

/-- The ranges a sequence's decoding cut give each element a range inside the sequence that decodes. -/
theorem ranges_of_cut {element : Desc} {b : ByteArray} {start stop count : Nat} {rl : List (Nat × Nat)}
    {values : List Value} (hr : elementRanges element b start stop count = rl) (len : rl.length = count)
    (within : ∀ p ∈ rl, start ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ stop)
    (decoded : deserializeEach element (rl.map fun p => slice b p.1 p.2) = .ok values) :
    ∀ i < count, start ≤ (elemRange element b start stop count i).1 ∧
      (elemRange element b start stop count i).1 ≤ (elemRange element b start stop count i).2 ∧
      (elemRange element b start stop count i).2 ≤ stop ∧
      ∃ v, deserialize element (slice b (elemRange element b start stop count i).1
        (elemRange element b start stop count i).2) = .ok v := by
  intro i hi
  have at_ : elemRange element b start stop count i = rl[i]'(by omega) := by
    simp only [elemRange, hr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < rl.length by omega),
      Option.getD_some]
  rw [at_]
  obtain ⟨a, b', c⟩ := within _ (List.getElem_mem _)
  obtain ⟨lengths, each⟩ := RootProof.deserializeEach_get element _ values decoded
  refine ⟨a, b', c, values[i]'(by simp at lengths; omega), ?_⟩
  have := each i (by simp; omega) (by simp at lengths; omega)
  simpa using this

/-- The roots of a sequence's elements, read range by range. -/
theorem elemRoots_getElem (element : Desc) (b : ByteArray) (start stop count : Nat) (i : Nat)
    (hi : i < (variableRoots element b (elementRanges element b start stop count)).length) :
    (variableRoots element b (elementRanges element b start stop count))[i] =
      rootOf element b (elemRange element b start stop count i).1 (elemRange element b start stop count i).2 := by
  have hi' : i < (elementRanges element b start stop count).length := by
    rw [variableRoots_eq_map, List.length_map] at hi; exact hi
  simp only [variableRoots_eq_map, List.getElem_map, elemRange, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi', Option.getD_some]

/-- What decoding a vector gives its root: each element's range decodes, and offsets fit when there are any. -/
theorem vector_decoded {element : Desc} {length : Nat} {b : ByteArray} {start stop : Nat}
    (sound : element.wellFormed = .ok ()) (ordered : start ≤ stop) (inside : stop ≤ b.size) (accepted : ∃ v, deserialize (.vector element length) (slice b start stop) = .ok v) :
    (∀ i < length, start ≤ (elemRange element b start stop length i).1 ∧
      (elemRange element b start stop length i).1 ≤ (elemRange element b start stop length i).2 ∧
      (elemRange element b start stop length i).2 ≤ stop ∧
      ∃ v, deserialize element (slice b (elemRange element b start stop length i).1
        (elemRange element b start stop length i).2) = .ok v) ∧
    (hasWidth element = false → 4 * length ≤ stop - start) ∧ length ≤ stop - start ∧
    (elementRanges element b start stop length).length = length := by
  obtain ⟨v, read⟩ := accepted
  simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i slices cut
  split at read
  · cases read
  rename_i values decoded
  have agree := vectorRanges_cut element length b start stop ordered inside
  rw [cut] at agree
  cases ranged : vectorRanges element length b start stop with
  | error e => simp [ranged, Except.map, CutAgree] at agree
  | ok r =>
    simp only [ranged, Except.map, CutAgree] at agree
    obtain ⟨sliced, within⟩ := agree
    have rangesEq := RootProof.elementRanges_vector element length b start stop r ranged
    have len : r.toList.length = length := by
      rw [← vectorSlices_length cut, sliced, List.length_map]
    subst sliced
    have size := slice_size b start stop inside
    refine ⟨ranges_of_cut rangesEq len within decoded, fun fx => ?_, ?_, by rw [rangesEq, len]⟩
    · have := vectorSlices_offsets (by rw [fixedSize_eq, ite_eq_right (by simp [fx])]) cut
      rw [size] at this
      simp only [bytesPerOffset] at this
      omega
    · have := RootProof.vector_count_le sound cut
      rwa [size] at this


/-! ### The vector driver -/

/-- A vector's stack is a level more than its element's. -/
theorem rootStack_vector (e : Desc) (l : Nat) : rootStack (.vector e l) = rootStack e + 1024 := by
  have h : (Desc.vector e l).nesting = e.nesting + 1 := by simp [Desc.nesting]
  unfold rootStack; rw [h]; omega

/-- The vector driver's frame holds fifteen words. -/
theorem vectorFrame : RootVector.fn.frame = 15 := by decide

set_option maxHeartbeats 4000000 in
/-- The vector driver writes the Lean root of a vector whose elements are rooted one by one. -/
theorem rootVector_ok {m : Module} {w : World} (hash : HashingOk m w) (fns : RangeFns m) {element : Desc}
    {length : Nat} (ih : RootOfOk m w element) (notPlain : plain (.vector element length) = false) :
    RangeOk m w "ssz_root_vector" (.vector element length) := by
  intro sp mem p base start stop out scratch ctx table zeros pad mask b room pre
  have usize := pre.usize
  have small := pre.small
  unfold RootProof.Small at small
  rw [usize] at small
  have ordered := pre.ordered
  have inside := pre.inside
  have bound : addressBound = 2 ^ 63 := rfl
  have zh : zeroHeights = 64 := rfl
  have stack := rootStack_vector element length
  have sound := wellFormed_vector pre.sound
  have thin : narrow element = true := by
    have := pre.thin; simp only [narrow, Bool.and_eq_true] at this; exact this.2
  obtain ⟨ranges, offsets, few, -⟩ := vector_decoded sound ordered inside pre.accepted
  -- The scratch: the element roots, then an element's scratch or the tree's.
  generalize hsize : stop - start = size at few offsets
  have need : varNeed (.vector element length) size =
      32 * length + max (varNeed element size) (32 + (2560 + 2048 + 32 * length)) := by
    have below := pre.below
    rw [hsize] at below
    simp only [varNeed, notPlain, Bool.false_eq_true, ite_false] at below ⊢
    have satLen : sat length = length := sat_of_lt (by simp only [sat]; have := cap_eq; omega)
    rw [satLen] at below ⊢
    simp only [treeNeed, RootProgressive.spineBytes, zeroHeights] at below ⊢
    simp only [sadd, smul, sat] at below ⊢
    have := cap_eq
    omega
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
  rw [hsize, need] at sAcc sB sPad sCtx sTable sZeros sOut sPlan sSlack below
  have as := access_bound sAcc
  -- The element's plan follows the vector's two words.
  have words : Plan.words (.vector element length) = [7, length] ++ Plan.words element := by rw [Plan.words]
  have planE : WordsAt w mem (p + 16) (Plan.words element) := by
    have := (wordsAt_split (by rw [← words]; exact pre.plan)).2
    simpa using this
  have planIn : p ≤ p + 16 ∧ p + 16 + 8 * (Plan.words element).length ≤
      p + 8 * (Plan.words (.vector element length)).length := by
    rw [words, List.length_append]; simp; omega
  have fitsE : Fits (Plan.words element) := by
    have := pre.fits; rw [words] at this; exact (fits_split this).2
  let sp' := sp - 8 - 8 * RootVector.fn.frame
  have room' : w.stackLo + 176 + rootStack element + 256 ≤ sp' := by
    show w.stackLo + 176 + rootStack element + 256 ≤ sp - 8 - 8 * RootVector.fn.frame; rw [vectorFrame]; have h := stack; omega
  have treeRoom : w.stackLo + treeStack ≤ sp' := by
    simp only [sp', vectorFrame, treeStack, hashStack, rootStack] at room ⊢; omega
  have ev := rangeEnv_entry p (base + start) size out scratch ctx
  -- The length.
  have lw : eval w (entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat size, UInt64.ofNat out,
      UInt64.ofNat scratch, UInt64.ofNat ctx]) mem (ld (RootVector.p + 8)) = some (UInt64.ofNat length) :=
    eval_word pre.plan 1 (by simp [Plan.words]) (e := RootVector.p + 8) (eval_add (eval_var ev.p) (eval_lit 8))
  have s1 := Runs.set' (m := m) (w := w) (sp := sp') (x := 6) lw
  have ev1 := ev.write (x := 6) (UInt64.ofNat length) (by decide)
  have l1 : Asm.assign (entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat size, UInt64.ofNat out,
      UInt64.ofNat scratch, UInt64.ofNat ctx]) 6 (UInt64.ofNat length) 6 = UInt64.ofNat length := assign_eq
  generalize Asm.assign (entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat size, UInt64.ofNat out,
    UInt64.ofNat scratch, UInt64.ofNat ctx]) 6 (UInt64.ofNat length) = E1 at s1 ev1 l1
  -- The element roots, into the scratch.
  have epre : ElemPre w mem element (p + 16) base start stop length scratch (32 * length + varNeed element size) ctx
      table zeros pad mask b :=
    { ready := pre.ready, plan := planE, fits := fitsE, holds := pre.holds, bAcc := pre.bAcc, ordered := ordered,
      inside := inside, small := pre.small, spread := pre.spread, sound := sound, thin := thin, ranges := ranges,
      offsets := fun fx _ => by rw [hsize]; exact offsets fx,
      room := by rw [hsize]; exact Nat.le_refl _, below := by rw [hsize]; omega,
      rAcc := access_sub sAcc (by omega) (by omega), rSlack := by omega,
      rB := apart_sub sB (by omega) (by omega), rPad := apart_sub sPad (by omega) (by omega),
      rCtx := apart_sub sCtx (by omega) (by omega), rTable := apart_sub sTable (by omega) (by omega),
      rZeros := apart_sub sZeros (by omega) (by omega),
      rPlan := apart_sub' (apart_sub sPlan (by omega) (by omega)) planIn.1 planIn.2, bPad := pre.bPad,
      planPad := apart_comm (apart_sub' (apart_comm pre.planPad) planIn.1 planIn.2), usize := usize }
  obtain ⟨mem1, call1, roots, ready1, keep1⟩ := rootElements_calls fns (sp := sp') ih room' epre
  rw [hsize] at call1
  have r2 := Runs.call (m := m) (sp := sp') (env := E1) (mem := mem) (dst := 8)
    (args := [RootVector.p + 16, RootVector.src, RootVector.size, RootVector.len, RootVector.scratch, RootVector.ctx])
    (by
      simp only [List.mapM_cons, List.mapM_nil, eval_add (eval_var ev1.p) (eval_lit 16), eval_var ev1.src,
        eval_var ev1.size, eval_var l1, eval_var ev1.scratch, eval_var ev1.ctx]
      rfl) call1
  have ev2 := ev1.write (x := 8) 0 (by decide)
  have l2 : Asm.assign E1 8 0 6 = UInt64.ofNat length := by rw [assign_ne (by decide)]; exact l1
  generalize Asm.assign E1 8 0 = E2 at r2 ev2 l2
  -- The tree's depth.
  have lsmall : length < 2 ^ 64 := by omega
  have dframe : DepthFor.fn.frame = 5 := by decide
  have dcall := depthFor_calls (m := m) (w := w) fns.roots.plan.depth (sp := sp') (by rw [dframe]; omega)
    (UInt64.ofNat length) mem1
  rw [ofNat_toNat lsmall] at dcall
  have r3 := Runs.call (m := m) (sp := sp') (env := E2) (mem := mem1) (dst := 7) (args := [RootVector.len])
    (by simp only [List.mapM_cons, List.mapM_nil, eval_var l2]; rfl) dcall
  have ev3 := ev2.write (x := 7) (depthFor length).toUInt64 (by decide)
  have l3 : Asm.assign E2 7 (depthFor length).toUInt64 6 = UInt64.ofNat length := by
    rw [assign_ne (by decide)]; exact l2
  have d3 : Asm.assign E2 7 (depthFor length).toUInt64 7 = UInt64.ofNat (depthFor length) := assign_eq
  generalize Asm.assign E2 7 (depthFor length).toUInt64 = E3 at r3 ev3 l3 d3
  -- The tree over the element roots, into the output.
  have deep : depthFor length ≤ 64 := depthFor_le_of_le_two_pow (by omega)
  have tpre : TreePre w mem1 scratch length (depthFor length) out (scratch + 32 * length + 32) ctx table zeros pad
      mask :=
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
    (args := [RootVector.scratch, RootVector.len, RootVector.d, RootVector.out,
      RootVector.scratch + 32 * RootVector.len + 32, RootVector.ctx])
    (by
      simp only [List.mapM_cons, List.mapM_nil, eval_var ev3.scratch, eval_var l3, eval_var d3, eval_var ev3.out,
        eval_add (eval_add (eval_var ev3.scratch) (eval_mul (eval_lit 32) (eval_var l3))) (eval_lit 32),
        eval_var ev3.ctx]
      rfl) call2
  have body : Runs m w sp' (entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat size,
      UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx]) mem RootVector.fn.body (Asm.assign E3 8 0) mem2 :=
    Runs.block_cons s1 (Runs.block_cons r2 (Runs.block_cons r3 (Runs.block_cons r4 (Runs.block_nil _ _ _ _ _))))
  have frame : ∀ a, ¬ (out ≤ a ∧ a < out + 32) →
      ¬ (scratch ≤ a ∧ a < scratch + varNeed (.vector element length) size) →
      ¬ (pad ≤ a ∧ a < pad + 1536) → mem2 a = mem a := fun a o s pd => by
    rw [need] at s
    rw [keep2 a (fun h => s ⟨by omega, by omega⟩) pd o]
    exact keep1 a (fun h => s ⟨by omega, by omega⟩) pd
  refine ⟨mem2, ?_, ?_, pre.readyAfter (by rw [hsize]; exact frame), frame⟩
  · rw [← hsize] at body ⊢
    exact Calls.fn fns.vector (by rw [vectorFrame]; rw [stack] at room; simp only [rootStack] at room; omega) rfl body
      rfl
  · -- The root: the tree over the element roots.
    let rs := variableRoots element b (elementRanges element b start stop length)
    have rlen : rs.length = length := by
      simp only [rs, variableRoots_eq_map, List.length_map]
      exact (vector_decoded sound ordered inside pre.accepted).2.2.2
    have sized : ∀ r ∈ rs, r.size = 32 := by
      intro r mem'
      simp only [rs, variableRoots_eq_map, List.mem_map] at mem'
      obtain ⟨q, qm, rfl⟩ := mem'
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem qm
      have hi' : i < length := by rw [← (vector_decoded sound ordered inside pre.accepted).2.2.2]; exact hi
      obtain ⟨_, ord, stp, acc⟩ := ranges i hi'
      have at_ : elemRange element b start stop length i = (elementRanges element b start stop length)[i] := by
        simp only [elemRange, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      rw [at_] at ord stp acc
      exact rootOf_size sound ord (by omega) pre.small acc
    have nodes : ∀ i (h : i < rs.length), nodeAt mem1 (scratch + 32 * i) = rs[i].data := by
      intro i h
      rw [roots i (by omega)]
      simp only [rs]
      rw [elemRoots_getElem]
    have code : rootOf (.vector element length) b start stop =
        merkleizeDepth (joinNodes rs) length (depthFor length) := by
      rw [rootOf]
      simp only [notPlain, Bool.false_eq_true, ite_false, merkleizeCapacity, rs]
    rw [root2, code]
    exact merkleizeDepth_of_nodes rlen sized nodes (le_two_pow_depthFor _) (by rw [usize]; omega)

end EthLib.Consensus.Ssz.Native.Driver
