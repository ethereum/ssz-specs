import SszNative.Proofs.Driver.Root.Size

/-!
One vector of composite elements is rooted by its elements' roots side by side, then their tree.

The roots driver writes the vector's root at the output and the element roots right after it.
The chunked driver roots the elements a chunk at a time, each chunk by a call to the roots driver on the element type.
What that call does is the induction hypothesis on the element type, taken here as an argument.
The tree driver then folds the element roots into the root, with its scratch past them.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Asm

/-! ### The room it takes -/

/-- The bytes the element roots take from their start: one run of chunks, or the roots and a full chunk's room. -/
def oneSpan (element : Desc) (length : Nat) : Nat :=
  if length ≤ recordsPerChunk then rootsNeed element length else 32 * length + rootsNeed element recordsPerChunk

/--
Below the cap, the bound of one vector covers its root, the element roots and their room, and the tree's scratch.

The tree's scratch starts a node past the element roots, and holds a node per element and per level.
-/
theorem vectorOne_need {element : Desc} {length : Nat} (nb : element.isBasic = false)
    (below : rootsNeed (.vector element length) 1 < scratchCap) :
    32 * length < scratchCap ∧ 32 + oneSpan element length ≤ rootsNeed (.vector element length) 1 ∧
      64 + 64 * length + 32 * zeroHeights ≤ rootsNeed (.vector element length) 1 := by
  have need : rootsNeed (.vector element length) 1 = sadd 32 (max
      (if sat length ≤ recordsPerChunk then rootsNeed element (sat length)
        else sadd (smul 32 (sat length)) (rootsNeed element recordsPerChunk))
      (sadd (sadd (smul 32 (sat length)) 32) (treeNeed (sat length)))) := by
    simp [rootsNeed, nb]
  rw [need] at below ⊢
  -- The length is below the cap, so no step of the bound saturates.
  have part : smul 32 (sat length) < scratchCap := by simp only [sadd, sat] at below ⊢; omega
  have satLen : sat length = length := by
    have := part
    rw [smul_of_lt this] at this
    exact sat_of_lt (by omega)
  rw [satLen] at below ⊢
  rw [smul_of_lt (by rw [← satLen]; exact part)] at below ⊢
  simp only [oneSpan, treeNeed, RootProgressive.spineBytes, zeroHeights] at below ⊢
  generalize rootsNeed element length = R at *
  generalize rootsNeed element recordsPerChunk = F at *
  simp only [sadd, smul, sat] at below ⊢
  generalize scratchCap = C at *
  split <;> split at below <;> omega

/-! ### The context after a call -/

/--
The context stays filled after a step that changes memory only inside the output region and the padding area.

The step may be a part of the call, writing only part of the output region.
-/
theorem RootsPre.readyWithin {w : World} {mem mem' : Memory} {d : Desc}
    {p base start stride count out ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : RootsPre w mem d p base start stride count out ctx table zeros pad mask b) {o n : Nat} (lo : out ≤ o)
    (hi : o + n ≤ out + rootsNeed d count)
    (keep : ∀ a, ¬ (o ≤ a ∧ a < o + n) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a) :
    RootReady w ctx table zeros pad mask mem' := by
  refine pre.ready.frame fun a held => ?_
  simp only [RootReady.Held] at held
  rcases held with h | h | h
  · exact keep a (outside_of_apart (apart_sub pre.oCtx lo hi) h.1 h.2)
      (outside_of_apart' (apart_comm pre.ready.padCtx) h.1 h.2)
  · exact keep a (outside_of_apart (apart_sub pre.oTable lo hi) h.1 h.2)
      (outside_of_apart' (apart_comm pre.ready.padTable) h.1 h.2)
  · exact keep a (outside_of_apart (apart_sub pre.oZeros lo hi) h.1 h.2)
      (outside_of_apart' (apart_comm pre.ready.padZeros) h.1 h.2)

/-! ### The path -/

/-- The statements that root one vector of composite elements: the element roots, the depth, then the tree. -/
abbrev vectorOnePath : List Stmt :=
  [RootsOf.r ::= RootsOf.out + 32, callInto RootsOf.sink "ssz_roots_chunked"
      [RootsOf.e, RootsOf.src, RootsOf.w, RootsOf.len, RootsOf.r, RootsOf.ctx],
    callInto RootsOf.d "ssz_depth_for" [RootsOf.len],
    callInto RootsOf.sink "ssz_merkleize"
      [RootsOf.r, RootsOf.len, RootsOf.d, RootsOf.out, RootsOf.r + 32 * RootsOf.len + 32, RootsOf.ctx]]

/-- The driver takes the one-value path for a vector of composite elements once the node and width are read. -/
theorem vectorOne_body : ∃ packed one many other, RootsOf.fn.body = .block [RootsOf.tag ::= ld RootsOf.p,
    ifElse (eq RootsOf.tag 7) [RootsOf.len ::= ld (RootsOf.p + 8), RootsOf.e ::= RootsOf.p + 16,
      ifElse (le (ld RootsOf.e) 1) packed [callInto RootsOf.w "ssz_plan_fixed_width" [RootsOf.e],
        ifElse (eq RootsOf.count 1) one many]] other] ∧ one = vectorOnePath :=
  ⟨_, _, _, _, rfl, rfl⟩

/--
One vector of composite elements is rooted by the chunked driver on its elements, then the tree driver over their roots.

What a call to the roots driver does on the element type is a hypothesis, the induction on the type.
The element roots start a node past the output, and the tree's scratch a node past them.
The stack holds a chunked call and an element call below it, and separately a call to the tree driver.
-/
theorem vectorOne_runs {m : Module} {w : World} (hash : HashingOk m w) (fns : RootsFns m)
    {element : Desc} {length : Nat} (ih : RootsOfOk m w element) {sp : Nat} {mem : Memory}
    {p base start stride out ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : RootsPre w mem (.vector element length) p base start stride 1 out ctx table zeros pad mask b)
    (ok : Rootable (.vector element length)) (nb : element.isBasic = false)
    (room : w.stackLo + 8 + 8 * RootsChunked.fn.frame + rootsStack element ≤ sp) (treeRoom : w.stackLo + treeStack ≤ sp)
    {env : Env} (ev : RootsEnv env p (base + start) stride 1 out ctx) (hl : env 7 = UInt64.ofNat length)
    (he : env 8 = UInt64.ofNat (p + 16)) (hw : env 9 = UInt64.ofNat (fixedWidth element)) :
    ∃ env' mem', Runs m w sp env mem (.block vectorOnePath) env' mem' ∧
      RootsPost w mem mem' out (rootsNeed (.vector element length) 1) ctx table zeros pad mask
        (rootsOf (.vector element length) b start stride 1) := by
  obtain ⟨pl, wf, thin⟩ := ok
  have pe : plain element = true := by simpa [plain] using pl
  have se := wellFormed_vector wf
  have ne : narrow element = true := by simp only [narrow, Bool.and_eq_true] at thin; exact thin.2
  have okE : Rootable element := ⟨pe, se, ne⟩
  have nz : 1 ≤ length := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    simp [Desc.wellFormed, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at wf
  have capv := cap_eq
  have bound : addressBound = 2 ^ 63 := rfl
  have chunk : recordsPerChunk = 1024 := rfl
  have zh : zeroHeights = 64 := rfl
  have width : fixedWidth (.vector element length) = fixedWidth element * length := rfl
  have wide := width_narrow _ pl thin
  rw [width] at wide
  have we := width_pos element pe se
  have wl : fixedWidth element ≤ fixedWidth element * length := Nat.le_mul_of_pos_right _ nz
  obtain ⟨small, spanIn, treeIn⟩ := vectorOne_need nb pre.below
  have slack := pre.slack
  have below := pre.below
  have usize := pre.usize
  -- The tree over the element roots is at most sixty-two levels deep.
  have deep : depthFor length ≤ 62 := depthFor_le_of_le_two_pow (by omega)
  -- A chunk needs at most the element roots' room, past the chunks before it.
  have chunkNeed : ∀ done c, done < length → done % recordsPerChunk = 0 → c = min recordsPerChunk (length - done) →
      rootsNeed element c < scratchCap ∧ 32 * done + rootsNeed element c ≤ oneSpan element length := by
    intro done c lt al hc
    by_cases few : length ≤ recordsPerChunk
    · have : done = 0 := by rw [chunk] at al few; omega
      subst this
      have : c = length := by rw [hc, chunk]; rw [chunk] at few; omega
      subst this
      simp only [oneSpan, ite_eq_left few] at spanIn ⊢
      omega
    · have top := rootsNeed_chunk element (show c ≤ recordsPerChunk by rw [hc]; exact Nat.min_le_left _ _)
      simp only [oneSpan, ite_eq_right few] at spanIn ⊢
      omega
  -- The element roots fit their room.
  have fits : 32 * length ≤ oneSpan element length := by
    unfold oneSpan
    split
    · have := rootsNeed_roots element length
      simp only [sat] at this
      omega
    · omega
  -- The element type's plan follows the vector's two words.
  have words : Plan.words (.vector element length) = [7, length] ++ Plan.words element := by rw [Plan.words]
  have planE : WordsAt w mem (p + 16) (Plan.words element) := by
    have := (wordsAt_split (by rw [← words]; exact pre.plan)).2
    simpa using this
  have planIn : p ≤ p + 16 ∧ p + 16 + 8 * (Plan.words element).length ≤
      p + 8 * (Plan.words (.vector element length)).length := by
    rw [words, List.length_append]; simp; omega
  have first := pre.inside 0 (by omega)
  rw [width, Nat.mul_zero, Nat.add_zero] at first
  have gap := pre.gap
  rw [width] at gap
  have spread := pre.spread
  rw [width] at spread
  -- The output's root, then the element roots.
  let E1 := Asm.assign env 11 (UInt64.ofNat (out + 32))
  have s0 : Runs m w sp env mem (RootsOf.r ::= RootsOf.out + 32) E1 mem :=
    Runs.set' (eval_add (eval_var ev.out) (eval_lit 32))
  let f := fun done c => rootsOf element b (start + fixedWidth element * done) (fixedWidth element) c
  obtain ⟨mem1, call1, held1, keep1⟩ := rootsChunked_calls (m := m) (w := w) fns.chunked (sp := sp)
    (by omega) (mem0 := mem) (p := p + 16) (src := base + start) (stride := fixedWidth element)
    (count := length) (out := out + 32) (ctx := ctx) (pad := pad) (span := oneSpan element length) f
    (fun done c lt al hc => rootsOf_size element okE usize b _ _ c (by rw [hc, chunk]; omega)
      (chunkNeed done c lt al hc).1)
    (by omega) (by omega) (apart_sub pre.oPad (by omega) (by omega)) fits
    (fun mem' done c agree lt al hc => by
      obtain ⟨need, inRoom⟩ := chunkNeed done c lt al hc
      have cpos : 1 ≤ c := by rw [hc, chunk]; omega
      have cle : done + c ≤ length := by rw [hc, chunk]; omega
      -- The chunk's values lie inside the vector's bytes.
      have span : fixedWidth element * (done + c) ≤ fixedWidth element * length := Nat.mul_le_mul_left _ cle
      rw [Nat.mul_add] at span
      have child := pre.child (mem₂ := mem') (start₂ := start + fixedWidth element * done)
        (stride₂ := fixedWidth element) (count₂ := c) (out₂ := out + 32 + 32 * done)
        (fun a o pd => agree a (fun h => o ⟨by omega, by omega⟩) pd) planE planIn (Nat.le_refl _) (by omega) cpos
        (fun i hi => by
          have := Nat.mul_le_mul_left (fixedWidth element) (show done + i + 1 ≤ length by omega)
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at this
          omega)
        (by omega) need (by omega)
      obtain ⟨mem'', calls, held, _, keep⟩ := ih (sp - 8 - 8 * RootsChunked.fn.frame) mem' (p + 16) base
        (start + fixedWidth element * done) (fixedWidth element) c (out + 32 + 32 * done) ctx table zeros pad mask b
        (by omega) child
      refine ⟨mem'', ?_, held, fun a o pd => keep a (fun h => o ⟨h.1, by omega⟩) pd⟩
      rw [show base + start + fixedWidth element * done = base + (start + fixedWidth element * done) by omega]
      exact calls)
  -- The chunks joined are the chunked roots.
  have joined : (if length ≤ recordsPerChunk then f 0 length
      else chunkJoin f length ((length + recordsPerChunk - 1) / recordsPerChunk)) =
      chunkedRoots element b start (fixedWidth element) length := by
    split
    · rename_i few
      rw [chunkedRoots, ite_eq_left few]
      simp only [f, Nat.mul_zero, Nat.add_zero]
    · rename_i many
      rw [chunkedRoots_join _ _ _ _ _ many]
  rw [joined] at held1
  have rootsSize : (chunkedRoots element b start (fixedWidth element) length).size = 32 * length :=
    chunkedRoots_size element (rootsOf_size element okE usize) b start _ length nz (by
      by_cases few : length ≤ recordsPerChunk
      · rw [Nat.min_eq_left few]
        exact (chunkNeed 0 length (by omega) (Nat.zero_mod _) (by rw [chunk] at few ⊢; omega)).1
      · rw [Nat.min_eq_right (by omega)]
        exact (chunkNeed 0 recordsPerChunk (by omega) (Nat.zero_mod _) (by rw [chunk] at few ⊢; omega)).1)
  have e1 : ∀ x, x ≠ 11 → E1 x = env x := fun x hx => assign_ne hx
  have r1 := Runs.call (m := m) (sp := sp) (env := E1) (mem := mem) (dst := 10)
    (args := [RootsOf.e, RootsOf.src, RootsOf.w, RootsOf.len, RootsOf.r, RootsOf.ctx])
    (by
      simp only [List.mapM_cons, List.mapM_nil, eval_var ((e1 8 (by decide)).trans he),
        eval_var ((e1 1 (by decide)).trans ev.src), eval_var ((e1 9 (by decide)).trans hw),
        eval_var ((e1 7 (by decide)).trans hl), eval_var (show E1 11 = UInt64.ofNat (out + 32) from assign_eq),
        eval_var ((e1 5 (by decide)).trans ev.ctx)]
      rfl) call1
  -- The depth of the element tree.
  let E2 := Asm.assign E1 10 0
  have e2 : ∀ x, x ≠ 10 → x ≠ 11 → E2 x = env x := fun x h10 h11 => by
    simp only [E2]; rw [assign_ne h10, e1 x h11]
  have dframe : DepthFor.fn.frame = 5 := by decide
  have tstack : treeStack = 160 + 10392 := rfl
  have dcall := depthFor_calls (m := m) (w := w) fns.plan.depth (sp := sp) (by rw [dframe]; omega) (UInt64.ofNat length) mem1
  rw [ofNat_toNat (by omega)] at dcall
  have r2 := Runs.call (m := m) (sp := sp) (env := E2) (mem := mem1) (dst := 12) (args := [RootsOf.len])
    (by simp only [List.mapM_cons, List.mapM_nil, eval_var ((e2 7 (by decide) (by decide)).trans hl)]; rfl) dcall
  -- The tree over the element roots, with its scratch past them.
  let E3 := Asm.assign E2 12 (depthFor length).toUInt64
  have ready1 := pre.readyWithin (o := out + 32) (n := oneSpan element length) (by omega) (by omega)
    (fun a o pd => keep1 a o pd)
  have tpre : TreePre w mem1 (out + 32) length (depthFor length) out (out + 32 + 32 * length + 32) ctx table zeros pad
      mask :=
    { ctxAccess := ready1.ctxAccess, maskAt := ready1.maskAt, tableAt := ready1.tableAt, zerosAt := ready1.zerosAt,
      padAt := ready1.padAt, tableBytes := ready1.tableHeld, tableAccess := ready1.tableAccess,
      zeroRoots := ready1.zeroRoots, zerosAccess := ready1.zerosAccess, deep := by simp only [zeroHeights]; omega,
      fits := le_two_pow_depthFor _, nodesAccess := access_sub pre.acc (by omega) (by omega),
      outAccess := access_sub pre.acc (by omega) (by omega), scratchAccess := access_sub pre.acc (by omega) (by omega),
      padAccess := ready1.padAccess, scratchNodes := by simp only [Apart]; omega,
      scratchOut := by simp only [Apart]; omega, scratchCtx := apart_sub pre.oCtx (by omega) (by omega),
      scratchTable := apart_sub pre.oTable (by omega) (by omega),
      scratchZeros := apart_sub pre.oZeros (by omega) (by omega), scratchPad := apart_sub pre.oPad (by omega) (by omega),
      padNodes := apart_comm (apart_sub (o₂ := out + 32) (n₂ := 32 * length) pre.oPad (by omega) (by omega)),
      padCtx := ready1.padCtx,
      padTable := ready1.padTable, padZeros := ready1.padZeros, nodesReach := by omega,
      outNodes := by simp only [Apart]; omega, outZeros := apart_sub pre.oZeros (by omega) (by omega) }
  obtain ⟨mem2, call2, root2, keep2⟩ := treeCalls_native hash.merkleize tpre ready1.kernels treeRoom
    (by rw [usize]; omega)
  have e3 : ∀ x, x ≠ 10 → x ≠ 11 → x ≠ 12 → E3 x = env x := fun x h10 h11 h12 => by
    simp only [E3]; rw [assign_ne h12, e2 x h10 h11]
  have e3r : E3 11 = UInt64.ofNat (out + 32) := by
    simp only [E3, E2]; rw [assign_ne (by decide), assign_ne (by decide)]; exact assign_eq
  have e3l : E3 7 = UInt64.ofNat length := (e3 7 (by decide) (by decide) (by decide)).trans hl
  have r3 := Runs.call (m := m) (sp := sp) (env := E3) (mem := mem1) (dst := 10)
    (args := [RootsOf.r, RootsOf.len, RootsOf.d, RootsOf.out, RootsOf.r + 32 * RootsOf.len + 32, RootsOf.ctx])
    (by
      simp only [List.mapM_cons, List.mapM_nil, eval_var e3r, eval_var e3l,
        eval_var (show E3 12 = UInt64.ofNat (depthFor length) from assign_eq),
        eval_var ((e3 4 (by decide) (by decide) (by decide)).trans ev.out),
        eval_add (eval_add (eval_var e3r) (eval_mul (eval_lit 32) (eval_var e3l))) (eval_lit 32),
        eval_var ((e3 5 (by decide) (by decide) (by decide)).trans ev.ctx)]
      rfl) call2
  -- Memory changed only inside the output region and the padding area.
  have frame : ∀ a, ¬ (out ≤ a ∧ a < out + rootsNeed (.vector element length) 1) → ¬ (pad ≤ a ∧ a < pad + 1536) →
      mem2 a = mem a := fun a o pd => by
    rw [keep2 a (fun h => o ⟨by omega, by omega⟩) pd (fun h => o ⟨h.1, by omega⟩),
      keep1 a (fun h => o ⟨by omega, by omega⟩) pd]
  -- The root is the tree over the element roots.
  have code : rootsOf (.vector element length) b start stride 1 =
      merkleizeDepth (chunkedRoots element b start (fixedWidth element) length) length (depthFor length) := by
    simp [rootsOf, nb]
  have rootSize := pre.sized ⟨pl, wf, thin⟩
  rw [bytesAt_of_holds rootsSize held1, ← code] at root2
  refine ⟨_, mem2, Runs.block_cons s0 (Runs.block_cons r1 (Runs.block_cons r2 (Runs.block_cons r3
    (Runs.block_nil _ _ _ _ _)))), holds_of_nodes rootSize fun i hi => ?_,
    pre.readyWithin (o := out) (n := rootsNeed (.vector element length) 1) (Nat.le_refl _) (Nat.le_refl _) frame,
    frame⟩
  have : i = 0 := by omega
  subst this
  rw [Nat.mul_zero, Nat.add_zero, root2, nodeOf_single _ (by rw [rootSize])]

end EthLib.Consensus.Ssz.Native.Driver
