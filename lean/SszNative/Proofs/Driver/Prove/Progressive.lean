import SszNative.Proofs.Driver.Prove.Bounded
import SszNative.Proofs.Driver.Prove.Spine
import SszNative.Proofs.Driver.Prove.SpineWalk

/-!
The compiled progressive walk roots the node of a progressive tree an index names, as the Lean walk does.

The walk down the spine either turns into one level's bounded subtree, or stops on the spine.
A node on the spine is the progressive root of every leaf from the level reached on.
The calls rooting values under the leaves, and the walk to a node of one value, are taken as contracts.
-/

namespace Ssz.Native.Driver.ProveProof

set_option maxRecDepth 20000

open Ssz Ssz.Native Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Ir.Stmt Ssz.Native.Ir.Expr Ssz.Native.Plan

/-! ### The Lean walk, step by step -/

/-- From a level the walk reaches, it stops on a level it reaches too, with no more turns left than it had. -/
theorem spineWalk_level (count index : Nat) : ∀ (depth j : Nat) (s : SpineStop),
    (j = 0 ∨ spineStart (j - 1) < count) → spineWalk count index depth (spineStart j) (4 ^ j) = .ok s →
    ∃ j', s.leavesFrom = spineStart j' ∧ s.capacity = 4 ^ j' ∧ (j' = 0 ∨ spineStart (j' - 1) < count) ∧
      s.depth ≤ depth
  | 0, j, s, reached, h => by
    simp only [spineWalk, Except.ok.injEq] at h
    subst h
    exact ⟨j, rfl, rfl, reached, Nat.le_refl _⟩
  | depth + 1, j, s, reached, h => by
    by_cases past : spineStart j ≥ count
    · simp [spineWalk, past] at h
      cases h
    · by_cases bit : gindexBit index depth = true
      · have next : spineWalk count index depth (spineStart (j + 1)) (4 ^ (j + 1)) = .ok s := by
          simpa [spineWalk, past, bit, spineStart, Nat.pow_succ] using h
        obtain ⟨j', a, c, r, d⟩ := spineWalk_level count index depth (j + 1) s (.inr (by simpa using past)) next
        exact ⟨j', a, c, r, by omega⟩
      · simp [spineWalk, past, bit] at h
        cases h
        exact ⟨j, rfl, rfl, reached, Nat.le_succ _⟩

/-- A level the spine reaches starts at most one past four times the leaf count. -/
theorem spineStart_le_of_reached {j count : Nat} (reached : j = 0 ∨ spineStart (j - 1) < count) :
    spineStart j ≤ 4 * count + 1 := by
  cases j with
  | zero => simp [spineStart]
  | succ i =>
    have h : spineStart i < count := by simpa using reached
    have := spineStart_pow i
    simp only [spineStart]
    omega

/-- A progressive walk is the spine walk, then the bounded walk or the progressive root of the leaves left. -/
theorem progressiveNode_eq (budget : Nat) (b : ByteArray) (layout : EncodedLayout) (index depth start cap : Nat) :
    progressiveNode budget b layout index depth start cap =
      match spineWalk layout.count index depth start cap with
      | .error e => .error e
      | .ok s =>
        if s.turnedLeft then boundedNode budget b layout index s.depth s.leavesFrom s.capacity
        else .ok (merkleizeProgressive (leavesIn b layout s.leavesFrom layout.count).1
          (leavesIn b layout s.leavesFrom layout.count).2 s.capacity) := by
  rw [progressiveNode]
  cases spineWalk layout.count index depth start cap <;> rfl

/-! ### Records kept outside the scratch -/

/-- A layout record stays laid out where memory agrees outside the scratch. -/
theorem LaidOut.keep {w : World} {mem mm : Memory} {lay data lo hi top out ctx free span table zeros pad n : Nat}
    {mask : UInt64} {b : ByteArray} {layout : EncodedLayout} (laid : LaidOut w mem lay data b n lo hi top layout)
    (pre : WalkPre w mem lay data lo hi top out ctx free span table zeros pad mask b)
    (same : ∀ a, ¬ (free ≤ a ∧ a < free + span) → mm a = mem a) : LaidOut w mm lay data b n lo hi top layout := by
  have base := pre.base
  have foot : ∀ a, Footprint lay top lo hi data b.size a → mm a = mem a := fun a h =>
    same a fun hf => pre.away a (.inl hf) h
  have word : ∀ k, k + 8 ≤ 144 → readLE mm (lay + k) 8 = readLE mem (lay + k) 8 := fun k hk =>
    read_keep foot fun i hi => .inl ⟨by omega, by omega⟩
  have db := BranchProof.access_bound pre.readable
  exact { count := by rw [word 8 (by omega)]; exact laid.count
          bounded := by rw [word 16 (by omega)]; exact laid.bounded
          capacity := fun c h => by rw [word 24 (by omega)]; exact laid.capacity c h
          mixed := by rw [word 32 (by omega)]; exact laid.mixed
          word := fun x h => by
            rw [BranchProof.readNode_congr fun i hi => foot _ (.inl ⟨by omega, by omega⟩)]
            exact laid.word x h
          encoding := by rw [word 72 (by omega)]; exact laid.encoding
          leaves := laid.leaves.keep base laid.encoding (by omega) fun a h => foot a (by
            simp only [RecordFoot] at h; simp only [Footprint]; omega) }

/-- What a walk inside a record needs stays where memory agrees outside the scratch. -/
theorem WalkPre.keep {w : World} {mem mm : Memory} {lay data lo hi top out ctx free span table zeros pad : Nat}
    {mask : UInt64} {b : ByteArray} (pre : WalkPre w mem lay data lo hi top out ctx free span table zeros pad mask b)
    (same : ∀ a, ¬ (free ≤ a ∧ a < free + span) → mm a = mem a) :
    WalkPre w mm lay data lo hi top out ctx free span table zeros pad mask b := by
  have base := pre.base
  have foot : ∀ a, Footprint lay top lo hi data b.size a → mm a = mem a := fun a h =>
    same a fun hf => pre.away a (.inl hf) h
  have word : ∀ k, k + 8 ≤ 144 → readLE mm (lay + k) 8 = readLE mem (lay + k) 8 := fun k hk =>
    read_keep foot fun i hi => .inl ⟨by omega, by omega⟩
  have da := pre.dataApart
  exact { pre with
    ready := pre.ready.within pre.freeCtx pre.freeTable pre.freeZeros fun a o _ => same a o
    bytes := fun k hk => by rw [same _ (by omega)]; exact pre.bytes k hk
    outW := by rw [word 128 (by omega)]; exact pre.outW
    ctxW := by rw [word 136 (by omega)]; exact pre.ctxW
    freeW := by rw [word 120 (by omega)]; exact pre.freeW }

/-- The walk to a node of one value starts the same from memory changed only in the scratch's first 48 bytes. -/
theorem ChildCalls.keep {m : Module} {w : World} {sp : Nat} {mem mm : Memory} {budget : Nat} {b : ByteArray}
    {slots : Slots} {data out ctx free span pad lo hi : Nat}
    (h : ChildCalls m w sp mem budget b slots data out ctx free span pad lo hi)
    (same : ∀ a, ¬ (free ≤ a ∧ a < free + 48) → mm a = mem a) :
    ChildCalls m w sp mm budget b slots data out ctx free span pad lo hi :=
  fun m' i d s e q idx hslot keep => h m' i d s e q idx hslot fun a o => (keep a o).trans (same a o)

/-! ### The driver -/

/-- The stack the progressive walk needs below its own frame: the bounded walk's call, which needs the most. -/
abbrev progressiveRoom (n : Nat) : Nat := 8 + 8 * ProveBounded.fn.frame + boundedRoom n

set_option maxHeartbeats 8000000 in
/--
A call of the progressive walk from a level the spine reaches answers what the Lean walk answers, and writes the node
when there is one.

The record holds the layout, and the walk needs what the contracts give.
The calls rooting values are taken for the two buffers the leaves go to, from any stack at least as high as the deepest
call, and from memory changed only where the walk's stop goes.
Memory changes only at the node, in the scratch past the record, and in the padding area.
-/
theorem progressive_calls {m : Module} {w : World} (linked : HasCodec m) (gmod : GatherModule m) (hash : HashingOk m w)
    (hf : m.fns.lookup "ssz_prove_progressive" = some ProveProgressive.fn)
    (hwk : m.fns.lookup "ssz_prove_spine_walk" = some ProveSpineWalk.fn)
    (hbd : m.fns.lookup "ssz_prove_bounded" = some ProveBounded.fn)
    (hsp : m.fns.lookup "ssz_prove_spine" = some ProveSpine.fn)
    (hlv : m.fns.lookup "ssz_branch_level" = some Level.fn)
    (hd : m.fns.lookup "ssz_depth_for" = some DepthFor.fn)
    (hp : m.fns.lookup "ssz_prove_pow2" = some ProvePow2.fn)
    (hsh : m.fns.lookup "ssz_prove_shr" = some ProveShr.fn)
    (hl : m.fns.lookup "ssz_prove_leaves" = some ProveLeaves.fn)
    (hs : m.fns.lookup "ssz_prove_slot" = some ProveSlot.fn) {sp n : Nat}
    (room : w.stackLo + 8 + 8 * ProveProgressive.fn.frame + progressiveRoom n ≤ sp)
    {mem : Memory} {lay data lo hi top out ctx free span table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    {layout : EncodedLayout} (laid : LaidOut w mem lay data b n lo hi top layout)
    (pre : WalkPre w mem lay data lo hi top out ctx free span table zeros pad mask b)
    (wide : 64 * layout.count + 4672 ≤ span) (countSmall : layout.count < 2 ^ 57)
    (budget index depth j : Nat) (indexSmall : index < 2 ^ 64) (shallow : depth < 64)
    (reached : j = 0 ∨ spineStart (j - 1) < layout.count)
    (chunked : ∀ s mm buf span' first last slots,
      sp - 8 - 8 * ProveProgressive.fn.frame - 8 - 8 * ProveBounded.fn.frame - 8 - 8 * ProveLeaves.fn.frame ≤ s →
      (buf = free ∧ span' = span) ∨ (buf = free + 32 ∧ span' = span - 32) →
      (∀ a, ¬ (free ≤ a ∧ a < free + 32) → mm a = mem a) → layout.leaves = .nested slots →
      ChunkCalls m w s mm b slots data first (min last layout.count - first) buf span' pad ctx lo hi)
    (roots : ∀ s mm buf span' first last slots,
      sp - 8 - 8 * ProveProgressive.fn.frame - 8 - 8 * ProveBounded.fn.frame - 8 - 8 * ProveLeaves.fn.frame ≤ s →
      (buf = free ∧ span' = span) ∨ (buf = free + 32 ∧ span' = span - 32) →
      (∀ a, ¬ (free ≤ a ∧ a < free + 32) → mm a = mem a) → layout.leaves = .nested slots →
      (∀ element start width count, slots = .stride element start width count → plain element = false) →
      RootCalls m w s mm b slots data first (min last layout.count - first) buf span' pad ctx lo hi)
    (child : ∀ slots, layout.leaves = .nested slots →
      ChildCalls m w (sp - 8 - 8 * ProveProgressive.fn.frame - 8 - 8 * ProveBounded.fn.frame) mem budget b slots
        data out ctx free span pad lo hi) :
    ∃ r mem', Calls m w "ssz_prove_progressive" sp [UInt64.ofNat lay, UInt64.ofNat index, UInt64.ofNat depth,
        UInt64.ofNat (spineStart j), UInt64.ofNat (4 ^ j)] mem r mem' ∧
      r = proveCode (progressiveNode budget b layout index depth (spineStart j) (4 ^ j)) ∧
      (∀ node, progressiveNode budget b layout index depth (spineStart j) (4 ^ j) = .ok node →
        nodeAt mem' out = node.data) ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (free ≤ a ∧ a < free + span) → ¬ (pad ≤ a ∧ a < pad + 1536) →
        mem' a = mem a := by
  have bb := BranchProof.access_bound pre.freeAcc
  have ob := BranchProof.access_bound pre.outAcc
  have lb := BranchProof.access_bound pre.fixedPart
  have db := BranchProof.access_bound pre.readable
  have acc : ∀ k, k + 8 ≤ 144 → w.access (lay + k) 8 = true := fun k hk =>
    BranchProof.access_sub pre.fixedPart (by omega)
  have outW := pre.outW
  have ctxW := pre.ctxW
  have freeW := pre.freeW
  have counted := laid.count
  have j30 : j ≤ 30 := by
    rcases reached with h | h
    · omega
    · have := level_few h countSmall; omega
  have startPow := spineStart_pow j
  have wideJ := level_wide j30
  have e60 : (2 : Nat) ^ 60 < 2 ^ 64 := by decide
  generalize hX : progressiveNode budget b layout index depth (spineStart j) (4 ^ j) = X
  suffices body : Wp m w (sp - 8 - 8 * ProveProgressive.fn.frame) ProveProgressive.fn.body
      (entryEnv [UInt64.ofNat lay, UInt64.ofNat index, UInt64.ofNat depth, UInt64.ofNat (spineStart j),
        UInt64.ofNat (4 ^ j)]) mem
      (fun env' mem' => eval w env' mem' ProveProgressive.fn.result = some (proveCode X) ∧
        (∀ node, X = .ok node → nodeAt mem' out = node.data) ∧
        ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (free ≤ a ∧ a < free + span) → ¬ (pad ≤ a ∧ a < pad + 1536) →
          mem' a = mem a) by
    obtain ⟨mem', c, p⟩ := calls_of_wp hf (by omega) rfl body
    exact ⟨_, mem', c, rfl, p⟩
  -- The stack below the walk's frame, named before the frame is unfolded.
  have fP : ProveProgressive.fn.frame = 19 := by decide
  have fB : ProveBounded.fn.frame = 29 := by decide
  have fL : ProveLeaves.fn.frame = 23 := by decide
  have fW : ProveSpineWalk.fn.frame = 11 := by decide
  have fPw : ProvePow2.fn.frame = 5 := by decide
  have ts : treeStack = 10552 := rfl
  rw [fP] at room chunked roots child ⊢
  generalize hspP : sp - 8 - 8 * 19 = spP at chunked roots child
  simp only [progressiveRoom, boundedRoom, fB, fL, ts] at room
  generalize hSR : slotRoom n = SR at room
  have sWalk : w.stackLo + 8 + 8 * ProveSpineWalk.fn.frame + 8 + 8 * ProvePow2.fn.frame ≤ spP := by
    rw [fW, fPw]; clear fP fB fL fW fPw ts; omega
  have sBound : w.stackLo + 8 + 8 * ProveBounded.fn.frame + boundedRoom n ≤ spP := by
    simp only [boundedRoom, fB, fL, hSR, ts]
    generalize (10552 : Nat) = T at room ⊢
    clear fP fB fL fW fPw ts sWalk; omega
  have sLeaves : w.stackLo + 8 + 8 * ProveLeaves.fn.frame + slotRoom n ≤ spP := by
    rw [fL, hSR]; clear fP fB fL fW fPw ts sWalk sBound; omega
  have sSpine' : w.stackLo + 8 + 8 * 19 + 10552 ≤ spP := by
    generalize (10552 : Nat) = T at room ⊢
    clear fP fB fL fW fPw ts sWalk sBound sLeaves hSR; omega
  have sSpine : w.stackLo + 8 + 8 * ProveSpine.fn.frame + treeStack ≤ spP := by rw [spineFrame, ts]; exact sSpine'
  have lowB : spP - 8 - 8 * ProveBounded.fn.frame - 8 - 8 * ProveLeaves.fn.frame ≤
      spP - 8 - 8 * ProveBounded.fn.frame - 8 - 8 * ProveLeaves.fn.frame := Nat.le_refl _
  have lowS : spP - 8 - 8 * ProveBounded.fn.frame - 8 - 8 * ProveLeaves.fn.frame ≤ spP - 8 - 8 * ProveLeaves.fn.frame := by
    rw [fB, fL]; clear fP fB fL fW fPw ts sWalk sBound sLeaves sSpine sSpine' hSR; omega
  clear room hspP fP fB fL fW fPw ts hSR sSpine'
  simp only [ProveProgressive.fn]
  refine Wp.set (by wev [acc, outW]) (Wp.set (by wev [acc, ctxW]) (Wp.set (by wev [acc, freeW]) ?_))
  -- The walk down the spine.
  have startLe := spineStart_le_of_reached reached
  have fAcc32 : w.access free 32 = true := BranchProof.access_prefix pre.freeAcc (by omega)
  have tC : (UInt64.ofNat layout.count).toNat = layout.count := Validate.toNat_ofNat_lt (by omega)
  have tI : (UInt64.ofNat index).toNat = index := Validate.toNat_ofNat_lt indexSmall
  have tD : (UInt64.ofNat depth).toNat = depth := Validate.toNat_ofNat_lt (by omega)
  have tS : (UInt64.ofNat (spineStart j)).toNat = spineStart j := Validate.toNat_ofNat_lt (by omega)
  have tW : (UInt64.ofNat (4 ^ j)).toNat = 4 ^ j := Validate.toNat_ofNat_lt (by omega)
  have tF : (UInt64.ofNat free).toNat = free := Validate.toNat_ofNat_lt (by omega)
  obtain ⟨r1, mem1, wcall, wans, wframe⟩ := spine_walk_calls (w := w) hwk hp sWalk (UInt64.ofNat layout.count)
    (UInt64.ofNat index) (UInt64.ofNat depth) (UInt64.ofNat (spineStart j)) (UInt64.ofNat (4 ^ j))
    (UInt64.ofNat free) mem (by rw [tF]; exact fAcc32) (by rw [tC]; omega) (by rw [tD]; exact shallow)
    (by rw [tS, tC]; exact startLe) (by rw [tW, tS]; omega)
  rw [tC, tI, tD, tS, tW, tF] at wans
  rw [tF] at wframe
  refine Wp.call (values := [UInt64.ofNat layout.count, UInt64.ofNat index, UInt64.ofNat depth,
    UInt64.ofNat (spineStart j), UInt64.ofNat (4 ^ j), UInt64.ofNat free]) (by wev [acc, counted]) wcall ?_
  have hX' := hX
  rw [progressiveNode_eq] at hX'
  have lvl := spineWalk_level layout.count index depth j
  generalize hW : spineWalk layout.count index depth (spineStart j) (4 ^ j) = W at wans hX' lvl
  cases W with
  | error e =>
    obtain ⟨r15, rfl⟩ := wans
    subst r15 hX'
    refine Wp.when_f (by wev []) (Wp.done ⟨by wev [], ?_, ?_⟩)
    · intro node h; simp at h
    · intro a h1 h2 h3
      exact wframe a fun h => h2 ⟨h.1, by omega⟩
  | ok st =>
    obtain ⟨r0, words⟩ := wans
    subst r0
    obtain ⟨j', lf, cp, reached', dle⟩ := lvl st reached rfl
    have j'30 : j' ≤ 30 := by
      rcases reached' with h | h
      · omega
      · have := level_few h countSmall; omega
    have startPow' := spineStart_pow j'
    have wideJ' := level_wide j'30
    simp only [List.range, List.range.loop, List.map_cons, List.map_nil, stopWords, List.cons.injEq, and_true,
      Nat.mul_zero, Nat.add_zero] at words
    obtain ⟨w0, w8, w16, w24⟩ := words
    have m0 : readLE mem1 free 8 = UInt64.ofNat st.depth := by rw [← w0, UInt64.ofNat_toNat]
    have m8 : readLE mem1 (free + 8) 8 = UInt64.ofNat (spineStart j') := by rw [← lf, ← w8, UInt64.ofNat_toNat]
    have m16 : readLE mem1 (free + 16) 8 = UInt64.ofNat (4 ^ j') := by rw [← cp, ← w16, UInt64.ofNat_toNat]
    have m24 : readLE mem1 (free + 24) 8 = UInt64.ofNat (if st.turnedLeft then 1 else 0) := by
      rw [← w24, UInt64.ofNat_toNat]
    have f0 : w.access free 8 = true := BranchProof.access_prefix pre.freeAcc (by omega)
    have f8 : w.access (free + 8) 8 = true := BranchProof.access_sub pre.freeAcc (by omega)
    have f16 : w.access (free + 16) 8 = true := BranchProof.access_sub pre.freeAcc (by omega)
    have f24 : w.access (free + 24) 8 = true := BranchProof.access_sub pre.freeAcc (by omega)
    have same1 : ∀ a, ¬ (free ≤ a ∧ a < free + span) → mem1 a = mem a := fun a h =>
      wframe a fun h' => h ⟨h'.1, by omega⟩
    have same48 : ∀ a, ¬ (free ≤ a ∧ a < free + 48) → mem1 a = mem a := fun a h =>
      wframe a fun h' => h ⟨h'.1, by omega⟩
    have laid1 := laid.keep pre same1
    have pre1 := pre.keep same1
    refine Wp.when_t (v := 1) (by wev []) (by decide) ?_
    simp only [List.append_nil]
    cases ht : st.turnedLeft
    · -- The walk stops on the spine: the progressive root of the leaves from the level reached.
      simp only [ht, Bool.false_eq_true, if_false] at m24 hX'
      rw [lf, cp] at hX'
      refine Wp.ifElse_f (by wev [m24, f24]) ?_
      simp only [List.append_nil]
      refine Wp.set (by wev [m16, f16]) ?_
      have lfLow : spineStart j' < 2 ^ 62 := by omega
      have counted1 := laid1.count
      obtain ⟨mem2, lcall, lnodes, lkept⟩ := leaves_calls (first := spineStart j') (last := layout.count)
        (buf := free + 32) (span := span - 32) (ctx := ctx) (pad := pad) linked gmod hl hs sLeaves laid1.count
        laid1.encoding laid1.leaves pre.fixedPart pre.base pre1.bytes pre.readable pre.small pre.usize (by omega)
        (by omega) (by omega) (access_sub pre.freeAcc (by omega) (by omega)) (by omega)
        (fun a h => pre.away a (h.elim (fun h => .inl ⟨by omega, by omega⟩) fun h => .inr (.inl h)))
        (by have := pre.freePad; simp only [Apart] at this; omega) (by have := pre.dataApart; omega)
        (fun slots hn => chunked _ mem1 (free + 32) (span - 32) _ _ slots lowS (.inr ⟨rfl, rfl⟩) wframe hn)
        (fun slots hn notChunked =>
          roots _ mem1 (free + 32) (span - 32) _ _ slots lowS (.inr ⟨rfl, rfl⟩) wframe hn notChunked)
      have cntIs := leavesIn_count b layout (spineStart j') layout.count
      generalize hc : (leavesIn b layout (spineStart j') layout.count).2 = cnt at lcall lnodes cntIs
      have cntLe : cnt ≤ layout.count := by omega
      refine Wp.call (values := [UInt64.ofNat lay, UInt64.ofNat (spineStart j'), UInt64.ofNat layout.count,
        UInt64.ofNat (free + 32), UInt64.ofNat ctx]) (by wev [m8, f8, acc, counted1]) lcall ?_
      -- The spine over those leaves, its scratch past them.
      have keep2 : ∀ a, ¬ (free ≤ a ∧ a < free + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem2 a = mem a :=
        fun a o pd => (lkept a (fun h => o ⟨by omega, by omega⟩) pd).trans (same1 a o)
      have pspan : progressiveSpan cnt = 4608 + 32 * cnt := rfl
      have bound : addressBound = 2 ^ 63 := rfl
      have ppre : ProgPre w mem2 (free + 32) cnt out (free + 32 * cnt + 64) ctx table zeros pad mask
          (bytesAt mem2 (free + 32) (32 * cnt)) :=
        { ready := pre.ready.within pre.freeCtx pre.freeTable pre.freeZeros keep2, held := holds_bytesAt _ _ _,
          inside := by simp [bytesAt, ByteArray.size],
          small := by simp only [bytesAt, ByteArray.size, Array.size_ofFn]; rw [pre.usize]; omega,
          few := by omega, nAcc := access_sub pre.freeAcc (by omega) (by omega), nReach := by omega,
          oAcc := pre.outAcc, sAcc := access_sub pre.freeAcc (by omega) (by omega),
          sN := by simp only [Apart, bytesAt, ByteArray.size, Array.size_ofFn]; omega,
          sO := by have := pre.outFree; simp only [Apart] at this ⊢; omega,
          sPad := apart_sub pre.freePad (by omega) (by omega), sCtx := apart_sub pre.freeCtx (by omega) (by omega),
          sTable := apart_sub pre.freeTable (by omega) (by omega),
          sZeros := apart_sub pre.freeZeros (by omega) (by omega),
          oPad := pre.outPad, oCtx := pre.outCtx, oTable := pre.outTable, oZeros := pre.outZeros,
          nPad := by
            have := apart_sub (o₂ := free + 32) (n₂ := 32 * cnt) pre.freePad (by omega) (by omega)
            simpa [bytesAt, ByteArray.size] using this }
      obtain ⟨mem3, scall, sroot, -, sframe⟩ := spine_calls hash hsp hlv sSpine ppre j'30
      refine Wp.call (values := [UInt64.ofNat (free + 32), UInt64.ofNat cnt, UInt64.ofNat (4 ^ j'), UInt64.ofNat out,
        UInt64.ofNat (free + 32 * cnt + 64), UInt64.ofNat ctx]) (by wev []) scall (Wp.done ⟨?_, ?_, ?_⟩)
      · subst hX'; wev []
      · intro node h
        subst hX'
        cases h
        rw [sroot, lnodes, hc]
      · intro a h1 h2 h3
        rw [sframe a h1 (fun h => h2 ⟨by omega, by omega⟩) h3, keep2 a h2 h3]
    · -- The walk turns into a level's subtree: the bounded walk roots the node.
      simp only [ht, if_true] at m24 hX'
      refine Wp.ifElse_t (v := 1) (by wev [m24, f24]) (by decide) ?_
      simp only [List.append_nil]
      obtain ⟨rb, mb, bcall, brc, bnode, bframe⟩ := bounded_calls linked gmod hash hbd hd hp hsh hl hs sBound
        laid1 pre1 (by omega) (by omega) budget index st.depth st.leavesFrom st.capacity indexSmall (by omega)
        (by rw [lf]; omega) (by rw [cp]; omega)
        (fun first last slots hn => chunked _ mem1 free span first last slots lowB (.inl ⟨rfl, rfl⟩) wframe hn)
        (fun first last slots hn notChunked =>
          roots _ mem1 free span first last slots lowB (.inl ⟨rfl, rfl⟩) wframe hn notChunked)
        (fun slots hn => (child slots hn).keep same48)
      refine Wp.call (values := [UInt64.ofNat lay, UInt64.ofNat index, UInt64.ofNat st.depth,
        UInt64.ofNat st.leavesFrom, UInt64.ofNat st.capacity]) (by wev [m0, m8, m16, f0, f8, f16, lf, cp]) bcall
        (Wp.done ⟨?_, ?_, ?_⟩)
      · subst hX'; rw [brc]; wev []
      · intro node h; subst hX'; exact bnode node h
      · intro a h1 h2 h3; rw [bframe a h1 h2 h3, same1 a h2]

end Ssz.Native.Driver.ProveProof
