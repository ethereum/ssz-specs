import SszNative.Proofs.Driver.Prove.Need
import SszNative.Proofs.Driver.Prove.Multiproof
import SszNative.Proofs.Driver.Branch.Copy

/-!
The compiled walk to a node answers what the Lean walk answers, for every type, by induction on its nesting.

The root of the range is the root driver's.
Any other node is found under the range's layout record: a mixed-in word, a node of the bounded or progressive tree, or
a node of one value under it, which the walk of that value's type roots one level down.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.ProveProof

set_option maxRecDepth 20000

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Plan

/-- The functions the walk to a node calls, each under its name. -/
structure ProveFns (m : Module) : Prop where
  /-- The root drivers. -/
  range : RangeFns m
  /-- The gathering drivers. -/
  gather : GatherModule m
  /-- The layout driver. -/
  layout : m.fns.lookup "ssz_prove_layout" = some ProveLayout.fn
  /-- The slot reader. -/
  slot : m.fns.lookup "ssz_prove_slot" = some ProveSlot.fn
  /-- The leaves driver. -/
  leaves : m.fns.lookup "ssz_prove_leaves" = some ProveLeaves.fn
  /-- The walk down a spine. -/
  spineWalk : m.fns.lookup "ssz_prove_spine_walk" = some ProveSpineWalk.fn
  /-- The progressive root of a run of nodes. -/
  spine : m.fns.lookup "ssz_prove_spine" = some ProveSpine.fn
  /-- The bounded walk. -/
  bounded : m.fns.lookup "ssz_prove_bounded" = some ProveBounded.fn
  /-- The progressive walk. -/
  progressive : m.fns.lookup "ssz_prove_progressive" = some ProveProgressive.fn
  /-- The walk to a node. -/
  nodeAt : m.fns.lookup "ssz_prove_node_at" = some ProveNodeAt.fn
  /-- An index's level. -/
  level : m.fns.lookup "ssz_branch_level" = some Level.fn
  /-- Powers of two. -/
  pow2 : m.fns.lookup "ssz_prove_pow2" = some ProvePow2.fn
  /-- Right shifts. -/
  shr : m.fns.lookup "ssz_prove_shr" = some ProveShr.fn

/-- The stack the walk to a node of a type needs: a fixed part, and a few frames per level of nesting. -/
def nodeStack (d : Desc) : Nat := 16384 + 2048 * d.nesting

/--
What the walk to a node of the value a range of an encoding holds needs.

The context is filled, the plan and the encoding are in memory, and the range decodes.
The job holds where the node goes, the scratch right past the job, and the context.
The scratch holds what each level of the walk needs, and the node and the scratch miss each other and everything
else the walk reads.
-/
structure NodePre (w : World) (mem : Memory) (d : Desc) (b : ByteArray) (p data s e job out ctx table zeros pad : Nat)
    (mask : UInt64) (span : Nat) : Prop where
  /-- The context is filled. -/
  ready : RootReady w ctx table zeros pad mask mem
  /-- The type's plan is in memory. -/
  planned : PlanAt w mem p (words d)
  /-- Its words fit a word. -/
  fits : Fits (words d)
  /-- The encoding is in memory. -/
  bytes : BytesAt mem data b
  /-- The encoding is usable. -/
  readable : w.access data b.size = true
  /-- Eight bits per byte of the encoding, and more, stay below the word size. -/
  small : 64 * b.size + 128 < 2 ^ 64
  /-- A machine word holds a full 64-bit size. -/
  usize : USize.size = 2 ^ 64
  /-- Twice the encoding's size past its address stays below the address bound. -/
  spread : data + 2 * b.size ≤ addressBound
  /-- The type is legal. -/
  sound : d.wellFormed = .ok ()
  /-- Every fixed-size type inside it is far below the word size. -/
  thin : narrow d = true
  /-- The range runs forward. -/
  ordered : s ≤ e
  /-- It lies inside the encoding. -/
  inside : e ≤ b.size
  /-- It decodes. -/
  accepted : ∃ v, deserialize d (slice b s e) = .ok v
  /-- The job's words are usable. -/
  jobAcc : w.access job 24 = true
  /-- Where the node goes. -/
  outW : readLE mem job 8 = UInt64.ofNat out
  /-- The scratch, right past the job. -/
  scrW : readLE mem (job + 8) 8 = UInt64.ofNat (job + 24)
  /-- The context. -/
  ctxW : readLE mem (job + 16) 8 = UInt64.ofNat ctx
  /-- The node is usable. -/
  outAcc : w.access out 32 = true
  /-- The scratch is usable. -/
  scrAcc : w.access (job + 24) span = true
  /-- The scratch ends a node short of the address bound. -/
  slack : job + 24 + span + 32 ≤ addressBound
  /-- The scratch holds each level's needs. -/
  room : walkNeed d b.size ≤ span
  /-- What the type needs at once is below the cap. -/
  below : walkMost d b.size < scratchCap
  /-- The scratch misses the encoding. -/
  sData : Apart (job + 24, span) (data, b.size)
  /-- It misses the padding area. -/
  sPad : Apart (job + 24, span) (pad, 1536)
  /-- It misses the context. -/
  sCtx : Apart (job + 24, span) (ctx, 32)
  /-- It misses the table. -/
  sTable : Apart (job + 24, span) (table, Kernel.tableSize)
  /-- It misses the zero roots. -/
  sZeros : Apart (job + 24, span) (zeros, 32 * (zeroHeights + 1))
  /-- It misses the plan. -/
  sPlan : Apart (job + 24, span) (p, 8 * (words d).length)
  /-- It misses the node. -/
  sOut : Apart (job + 24, span) (out, 32)
  /-- The node misses the encoding. -/
  oData : Apart (out, 32) (data, b.size)
  /-- It misses the padding area. -/
  oPad : Apart (out, 32) (pad, 1536)
  /-- It misses the context. -/
  oCtx : Apart (out, 32) (ctx, 32)
  /-- It misses the table. -/
  oTable : Apart (out, 32) (table, Kernel.tableSize)
  /-- It misses the zero roots. -/
  oZeros : Apart (out, 32) (zeros, 32 * (zeroHeights + 1))
  /-- It misses the plan. -/
  oPlan : Apart (out, 32) (p, 8 * (words d).length)
  /-- The encoding misses the padding area. -/
  dataPad : Apart (data, b.size) (pad, 1536)
  /-- The plan misses the padding area. -/
  planPad : Apart (p, 8 * (words d).length) (pad, 1536)

/--
The walk to a node of a type answers what the Lean walk answers, writes the node when there is one, and changes
nothing but the node, the scratch, and the padding area.
-/
def NodeAtSpec (m : Module) (w : World) (d : Desc) : Prop :=
  ∀ (sp : Nat) (mem : Memory) (b : ByteArray) (p data s e job out ctx table zeros pad : Nat) (mask : UInt64)
    (span idx : Nat), w.stackLo + nodeStack d ≤ sp →
    NodePre w mem d b p data s e job out ctx table zeros pad mask span → idx < 2 ^ 64 →
    ∃ r mem', Calls m w "ssz_prove_node_at" sp [UInt64.ofNat p, UInt64.ofNat data, UInt64.ofNat s, UInt64.ofNat e,
        UInt64.ofNat idx, UInt64.ofNat job] mem r mem' ∧
      r = proveCode (nodeRootAt d.nesting d b s e idx) ∧
      (∀ node, nodeRootAt d.nesting d b s e idx = .ok node → nodeAt mem' out = node.data) ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (job + 24 ≤ a ∧ a < job + 24 + span) → ¬ (pad ≤ a ∧ a < pad + 1536) →
        mem' a = mem a

/-! ### The Lean walk, step by step -/

/-- Index zero names no node. -/
theorem nodeRootAt_zero (B : Nat) (d : Desc) (b : ByteArray) (s e : Nat) :
    nodeRootAt (B + 1) d b s e 0 = .error (.notAGindex 0) := by
  simp [nodeRootAt, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- The root sits on no branch, but it is still a node. -/
theorem nodeRootAt_one (B : Nat) (d : Desc) (b : ByteArray) (s e : Nat) :
    nodeRootAt (B + 1) d b s e 1 = .ok (rootOf d b s e) := by
  simp [nodeRootAt, pure, Except.pure]

/-- A layout record's bytes are at most the type's layout room and a constant. -/
theorem layoutRoom_le (d : Desc) : layoutRoom d ≤ 288 + 256 * d.nesting := by
  have wl : walkLevel = 112 := by decide
  have fv : fieldsView.frame = 19 := by decide
  have fw : planFieldsWidth.frame = 7 := by decide
  have fl : planLeading.frame = 7 := by decide
  have pw : planWidth.frame = 9 := by decide
  have wd : widthLevel = 144 := by decide
  cases d <;> simp only [layoutRoom, Desc.nesting, fieldsRoom, wl, fv, fw, fl, wd] <;> omega

/-- The root call's needs, from the walk's: the scratch holds the root's scratch bound. -/
theorem NodePre.rangePre {w : World} {mem : Memory} {d : Desc} {b : ByteArray}
    {p data s e job out ctx table zeros pad : Nat} {mask : UInt64} {span : Nat}
    (pre : NodePre w mem d b p data s e job out ctx table zeros pad mask span) :
    RangePre w mem d p data s e out (job + 24) ctx table zeros pad mask b := by
  have v1 := varNeed_mono d (show e - s ≤ b.size by have := pre.inside; omega)
  have v2 : varNeed d b.size ≤ walkMost d b.size := Nat.le_max_left _ _
  have v3 := pre.room
  have v4 := pre.below
  simp only [walkNeed] at v3
  have fit : job + 24 + varNeed d (e - s) ≤ job + 24 + span := by omega
  have sl := pre.slack
  exact ⟨pre.ready, pre.planned, pre.fits, pre.bytes, pre.readable, pre.ordered, pre.inside,
    by simp only [RootProof.Small]; rw [pre.usize]; exact pre.small, pre.spread, pre.sound, pre.thin, pre.accepted,
    by omega, Driver.access_sub pre.scrAcc (Nat.le_refl _) fit, by omega, pre.outAcc,
    apart_sub pre.sData (Nat.le_refl _) fit, apart_sub pre.sPad (Nat.le_refl _) fit,
    apart_sub pre.sCtx (Nat.le_refl _) fit, apart_sub pre.sTable (Nat.le_refl _) fit,
    apart_sub pre.sZeros (Nat.le_refl _) fit, apart_sub pre.sPlan (Nat.le_refl _) fit,
    apart_sub pre.sOut (Nat.le_refl _) fit, pre.oData, pre.oPad, pre.oCtx, pre.oTable, pre.oZeros, pre.oPlan,
    pre.dataPad, pre.planPad, pre.usize⟩

/-- The walk inside a layout's tree, from a depth: the bounded walk, or the progressive one. -/
def treeWalk (budget : Nat) (b : ByteArray) (layout : EncodedLayout) (index depth : Nat) : Except Err ByteArray :=
  match layout.limit with
  | some capacity => boundedNode budget b layout index depth 0 capacity
  | none => progressiveNode budget b layout index depth 0 1

/-- Past the root, the walk reads a mixed-in word, or walks the layout's tree one level down when a word is mixed in. -/
theorem nodeRootAt_eq {B : Nat} {d : Desc} {b : ByteArray} {s e idx : Nat} {layout : EncodedLayout}
    (laid : layoutOf d b s e = .ok layout) (two : 2 ≤ idx) :
    nodeRootAt (B + 1) d b s e idx =
      match layout.mixin with
      | some word =>
        if idx.testBit (Nat.log2 idx - 1) then
          (if Nat.log2 idx - 1 ≠ 0 then .error .pathIntoMixin else .ok word)
        else treeWalk B b layout idx (Nat.log2 idx - 1)
      | none => treeWalk B b layout idx (Nat.log2 idx) := by
  rw [nodeRootAt]
  simp only [show ¬ idx < 1 by omega, show (idx == 1) = false by simp; omega, laid, Ssz.gindexLength_of_two two]
  cases hm : layout.mixin <;> cases hl : layout.limit <;>
    simp [hm, hl, bind, Except.bind, pure, Except.pure, treeWalk, gindexBit, throw, throwThe, MonadExceptOf.throw]

/-- A layout record stays laid out where memory agrees on what its values are read from and on its words. -/
theorem LaidOut.keepFoot {w : World} {mem mm : Memory} {lay data : Nat} {b : ByteArray} {n lo hi top : Nat}
    {layout : EncodedLayout} (laid : LaidOut w mem lay data b n lo hi top layout) (base : lay + 144 ≤ top)
    (dataSmall : data < 2 ^ 64) (same : ∀ a, RecordFoot lay top lo hi data b.size a → mm a = mem a) :
    LaidOut w mm lay data b n lo hi top layout := by
  have word : ∀ k, k + 8 ≤ 120 → readLE mm (lay + k) 8 = readLE mem (lay + k) 8 := fun k hk =>
    read_keep same fun i hi => by simp only [RecordFoot]; omega
  exact { count := by rw [word 8 (by omega)]; exact laid.count
          bounded := by rw [word 16 (by omega)]; exact laid.bounded
          capacity := fun c h => by rw [word 24 (by omega)]; exact laid.capacity c h
          mixed := by rw [word 32 (by omega)]; exact laid.mixed
          word := fun x h => by
            rw [BranchProof.readNode_congr fun i hi => same _ (by simp only [RecordFoot]; omega)]
            exact laid.word x h
          encoding := by rw [word 72 (by omega)]; exact laid.encoding
          leaves := laid.leaves.keep base laid.encoding dataSmall same }

/-- A tree's capacity for a basic sequence: its nodes are at most its count of values. -/
theorem basic_chunks {el : Desc} (basic : el.isBasic = true) (sound : el.wellFormed = .ok ()) {n : Nat}
    (hn : n < 2 ^ 64) : chunksForBytes (n * el.itemLength) < 2 ^ 64 := by
  obtain ⟨-, hw, -⟩ := basic_width basic sound
  have : el.itemLength ≤ 32 := by simp at hw; omega
  have := Nat.mul_le_mul_left n this
  simp only [chunksForBytes, bytesPerChunk]
  omega

/-- A bounded tree's capacity fits a word. -/
theorem limit_small {d : Desc} {b : ByteArray} {s e : Nat} {layout : EncodedLayout}
    (laid : layoutOf d b s e = .ok layout) (fits : Fits (words d)) (sound : d.wellFormed = .ok ())
    (small : 64 * b.size + 128 < 2 ^ 64) (inside : e ≤ b.size) : ∀ c, layout.limit = some c → c < 2 ^ 64 := by
  intro c hc
  have w1 : ∀ x ∈ words d, x < 2 ^ 64 := fits
  cases d with
  | bool | uint _ | byteVector _ =>
    simp only [layoutOf] at laid; cases laid; cases hc; simp only [nodesFor]; omega
  | byteList l =>
    have := w1 l (by simp [words])
    simp only [layoutOf] at laid; cases laid; cases hc; simp only [chunksForBytes, bytesPerChunk]; omega
  | bitVector l | bitList l =>
    have := w1 l (by simp [words])
    simp only [layoutOf] at laid; cases laid; cases hc; simp only [chunksForBits, bytesPerChunk]; omega
  | progressiveBitList _ => simp only [layoutOf] at laid; cases laid; cases hc
  | vector el n | list el n =>
    have := w1 n (by simp [words])
    simp only [layoutOf] at laid; cases laid
    simp only [encodedSequence] at hc
    split at hc
    · rename_i basic
      simp only [Option.map_some, Option.some.injEq] at hc; subst hc
      first | exact basic_chunks basic (wellFormed_vector sound) this | exact basic_chunks basic (wellFormed_list sound) this
    · cases hc; exact this
  | progressiveList _ _ =>
    simp only [layoutOf] at laid; cases laid
    simp only [encodedSequence] at hc
    split at hc <;> cases hc
  | container names fs =>
    have := w1 fs.length (by simp [words])
    simp only [layoutOf, Bind.bind, Except.bind] at laid
    split at laid
    · cases laid
    · simp only [pure, Except.pure, Except.ok.injEq] at laid; subst laid; cases hc; exact this
  | progressiveContainer _ _ _ =>
    simp only [layoutOf, Bind.bind, Except.bind] at laid
    split at laid
    · cases laid
    · simp only [pure, Except.pure, Except.ok.injEq] at laid; subst laid; cases hc
  | compatibleUnion _ _ =>
    simp only [layoutOf, Bind.bind, Except.bind] at laid
    split at laid
    · cases laid
    · simp only [pure, Except.pure, Except.ok.injEq] at laid; subst laid; cases hc; decide

/-- The walk's stack holds the progressive walk's. -/
theorem progressive_stack {lo n spN : Nat} (one : 1 ≤ n) (h : lo + 16384 + 2048 * n - 176 ≤ spN) :
    lo + 8 + 8 * ProveProgressive.fn.frame + progressiveRoom (n - 1) ≤ spN := by
  have fB : ProveBounded.fn.frame = 29 := by decide
  have fL : ProveLeaves.fn.frame = 23 := by decide
  have fP : ProveProgressive.fn.frame = 19 := by decide
  have fS : ProveSlot.fn.frame = 19 := by decide
  have fK : planSkip.frame = 5 := by decide
  have wl : walkLevel = 112 := by decide
  have ts : treeStack = 10552 := rfl
  simp only [progressiveRoom, boundedRoom, slotRoom, fB, fL, fS, fK, fP, wl, ts]
  clear fB fL fP fS fK wl ts
  omega

set_option maxHeartbeats 8000000 in
/-- The walk to a node of a type, from the walks to nodes of its children. -/
theorem node_at_step {m : Module} {w : World} (fns : ProveFns m) (hash : HashingOk m w) (d : Desc)
    (ih : ∀ c, c.nesting < d.nesting → NodeAtSpec m w c) : NodeAtSpec m w d := by
  intro sp mem b p data s e job out ctx table zeros pad mask span idx stack pre idxSmall
  obtain ⟨B, hB⟩ : ∃ B, d.nesting = B + 1 := ⟨d.nesting - 1, by have := nesting_pos d; omega⟩
  have jb := BranchProof.access_bound pre.jobAcc
  have sb := BranchProof.access_bound pre.scrAcc
  have ob := BranchProof.access_bound pre.outAcc
  have db := BranchProof.access_bound pre.readable
  have acc0 : w.access job 8 = true := BranchProof.access_prefix pre.jobAcc (by omega)
  have acc8 : w.access (job + 8) 8 = true := BranchProof.access_sub pre.jobAcc (by omega)
  have acc16 : w.access (job + 16) 8 = true := BranchProof.access_sub pre.jobAcc (by omega)
  have outW := pre.outW
  have scrW := pre.scrW
  have ctxW := pre.ctxW
  have ins := pre.inside
  have ord := pre.ordered
  have sml := pre.small
  generalize hX : nodeRootAt d.nesting d b s e idx = X
  have fN : ProveNodeAt.fn.frame = 21 := by decide
  suffices body : Wp m w (sp - 8 - 8 * ProveNodeAt.fn.frame) ProveNodeAt.fn.body
      (entryEnv [UInt64.ofNat p, UInt64.ofNat data, UInt64.ofNat s, UInt64.ofNat e, UInt64.ofNat idx,
        UInt64.ofNat job]) mem
      (fun env' mem' => eval w env' mem' ProveNodeAt.fn.result = some (proveCode X) ∧
        (∀ node, X = .ok node → nodeAt mem' out = node.data) ∧
        ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (job + 24 ≤ a ∧ a < job + 24 + span) →
          ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a) by
    obtain ⟨mem', c, q⟩ := calls_of_wp fns.nodeAt (by rw [fN]; simp only [nodeStack] at stack; omega) rfl body
    exact ⟨_, mem', c, rfl, q⟩
  rw [fN]
  have spRoom : w.stackLo + 16384 + 2048 * d.nesting - 176 ≤ sp - 8 - 8 * 21 := by
    simp only [nodeStack] at stack; omega
  generalize sp - 8 - 8 * 21 = spN at spRoom
  clear stack fN
  simp only [ProveNodeAt.fn]
  refine Wp.set (by wev [acc0, outW]) (Wp.set (by wev [acc8, scrW]) (Wp.set (by wev [acc16, ctxW])
    (Wp.set (by wev []) ?_)))
  by_cases nz : idx = 0
  · -- Index zero names no node.
    subst nz
    refine Wp.ifElse_t (v := 1) (by wev []) (by decide) (Wp.set (by wev []) (Wp.done ⟨?_, ?_, fun _ _ _ _ => rfl⟩))
    · rw [← hX, hB, nodeRootAt_zero]; wev []
    · intro node h; rw [← hX, hB, nodeRootAt_zero] at h; cases h
  refine Wp.ifElse_f (by wev [nz]) ?_
  by_cases o : idx = 1
  · -- The root: the root driver's.
    subst o
    have rs : w.stackLo + rootStack d + 256 ≤ spN := by simp only [rootStack]; omega
    obtain ⟨mem', call, root, _, keep⟩ := rootOf_ok hash fns.gather fns.range d spN mem p data s e out (job + 24)
      ctx table zeros pad mask b rs pre.rangePre
    refine Wp.ifElse_t (v := 1) (by wev []) (by decide) ?_
    refine Wp.call (values := [UInt64.ofNat p, UInt64.ofNat (data + s), UInt64.ofNat (e - s), UInt64.ofNat out,
      UInt64.ofNat (job + 24), UInt64.ofNat ctx]) (by wev []) call (Wp.done ⟨?_, ?_, ?_⟩)
    · rw [← hX, hB, nodeRootAt_one]; wev []
    · intro node h; rw [← hX, hB, nodeRootAt_one] at h; cases h; exact root
    · intro a h1 h2 h3
      have v1 := varNeed_mono d (show e - s ≤ b.size by omega)
      have v2 : varNeed d b.size ≤ walkMost d b.size := Nat.le_max_left _ _
      have v3 := pre.room
      simp only [walkNeed] at v3
      exact keep a h1 (fun h => h2 ⟨h.1, by omega⟩) h3
  refine Wp.ifElse_f (by wev [o]) ?_
  have two : 2 ≤ idx := by omega
  -- The range's layout, and the scratch it leaves past its record.
  obtain ⟨v, read⟩ := pre.accepted
  obtain ⟨layout, L, laidE, -, -⟩ := BranchProof.laysOut d pre.sound b s e v ord ins
    (by simp only [RootProof.Small]; rw [pre.usize]; exact sml) read
  have dec : Decoded d b s e layout := ⟨pre.sound, pre.thin, pre.fits, ord, ins, pre.accepted, laidE⟩
  obtain ⟨cs, wideN, need⟩ := layout_need dec sml pre.usize pre.below
  have room := pre.room
  generalize hrb : recordBytes d = rb at wideN need
  have rbBig : 144 ≤ rb := by rw [← hrb]; cases d <;> simp [recordBytes, layoutBytes] <;> omega
  have rbIn : rb + 64 * layout.count + 4704 ≤ span := by omega
  have sl := pre.slack
  have sPlan := pre.sPlan
  have sData := pre.sData
  simp only [Apart] at sPlan sData
  have input : LayoutInput w mem d b p data s e (job + 24) :=
    ⟨pre.planned, pre.fits, by rw [hrb]; omega, Driver.access_sub pre.scrAcc (Nat.le_refl _) (by rw [hrb]; omega),
      ord, ins, sml, pre.bytes, pre.readable, by rw [hrb]; omega⟩
  have lroom : w.stackLo + 8 + 8 * ProveLayout.fn.frame + layoutRoom d ≤ spN := by
    have := layoutRoom_le d
    have f : ProveLayout.fn.frame = 31 := by decide
    rw [f]; omega
  obtain ⟨mem1, lcall, laid1, free1, frame1⟩ :=
    layout_calls_of_decoded fns.range.roots.plan fns.layout lroom laidE input pre.sound pre.thin pre.accepted
  rw [hrb] at laid1 free1 frame1
  refine Wp.call (values := [UInt64.ofNat p, UInt64.ofNat data, UInt64.ofNat s, UInt64.ofNat e,
    UInt64.ofNat (job + 24)]) (by wev []) lcall ?_
  -- Where the node goes and the context, written into the record.
  have a128 : w.access (job + 24 + 128) 8 = true := Driver.access_sub pre.scrAcc (by omega) (by omega)
  have a136 : w.access (job + 24 + 136) 8 = true := Driver.access_sub pre.scrAcc (by omega) (by omega)
  refine Wp.store (x := UInt64.ofNat (job + 24 + 128)) (y := UInt64.ofNat out) (by wev []) (by wev [])
    (by rw [Validate.toNat_ofNat_lt (by omega)]; exact a128) ?_
  refine Wp.store (x := UInt64.ofNat (job + 24 + 136)) (y := UInt64.ofNat ctx) (by wev []) (by wev [])
    (by rw [Validate.toNat_ofNat_lt (by omega)]; exact a136) ?_
  simp only [Validate.toNat_ofNat_lt (show job + 24 + 128 < 2 ^ 64 by omega),
    Validate.toNat_ofNat_lt (show job + 24 + 136 < 2 ^ 64 by omega), Width.bytes]
  generalize hm3 : store (store mem1 (job + 24 + 128) 8 (qwordByte (UInt64.ofNat out))) (job + 24 + 136) 8
    (qwordByte (UInt64.ofNat ctx)) = mem3
  have st3 : ∀ a, ¬ (job + 24 + 128 ≤ a ∧ a < job + 24 + 144) → mem3 a = mem1 a := fun a h => by
    rw [← hm3, store_outside (by omega), store_outside (by omega)]
  have out3 : readLE mem3 (job + 24 + 128) 8 = UInt64.ofNat out := by
    rw [← hm3, read_store_apart _ _ _ _ _ (by omega), readLE_store8]
  have ctx3 : readLE mem3 (job + 24 + 136) 8 = UInt64.ofNat ctx := by rw [← hm3, readLE_store8]
  have laid3 : LaidOut w mem3 (job + 24) data b (d.nesting - 1) p (p + 8 * (words d).length) (job + 24 + rb)
      layout := laid1.keepFoot (by omega) (by omega) fun a h => st3 a (by simp only [RecordFoot] at h; omega)
  have free3 : readLE mem3 (job + 24 + 120) 8 = UInt64.ofNat (job + 24 + rb) := by
    rw [read_keep (fun a h => st3 a h) (fun i hi => by omega)]; exact free1
  -- What changed so far: the record only.
  have keep3 : ∀ a, ¬ (job + 24 ≤ a ∧ a < job + 24 + rb) → mem3 a = mem a := fun a h => by
    rw [st3 a (by omega), frame1 a h]
  -- The index's level, the mixed-in flag, and the depth of the tree's walk.
  have lv : Calls m w "ssz_branch_level" spN [UInt64.ofNat idx] mem3 (UInt64.ofNat (Nat.log2 idx)) mem3 := by
    have := BranchProof.level_calls (w := w) fns.level (sp := spN) (by omega) (UInt64.ofNat idx) mem3
    rwa [Validate.toNat_ofNat_lt idxSmall] at this
  have lg : Nat.log2 idx < 64 := by
    have := BranchProof.log2_lt_64 (UInt64.ofNat idx); rwa [Validate.toNat_ofNat_lt idxSmall] at this
  have lg1 : 1 ≤ Nat.log2 idx := (Nat.le_log2 (by omega)).mpr (by simpa using two)
  refine Wp.call (values := [UInt64.ofNat idx]) (by wev []) lv ?_
  generalize hmb : (if layout.mixin.isSome then 1 else 0 : Nat) = mb
  have mbLe : mb ≤ 1 := by rw [← hmb]; split <;> omega
  have a32 : w.access (job + 24 + 32) 8 = true := Driver.access_sub pre.scrAcc (by omega) (by omega)
  have mx3 : readLE mem3 (job + 24 + 32) 8 = UInt64.ofNat mb := by
    rw [laid3.mixed, ← hmb]; split <;> rfl
  refine Wp.set (v := UInt64.ofNat mb) (by wev [a32, mx3]) ?_
  refine Wp.set (v := UInt64.ofNat (Nat.log2 idx - mb)) (by wev []) ?_
  generalize hD : Nat.log2 idx - mb = D
  have pw : Calls m w "ssz_prove_pow2" spN [UInt64.ofNat D] mem3 (UInt64.ofNat (2 ^ D)) mem3 := by
    have := pow2_calls (w := w) fns.pow2 (sp := spN) (by have f : ProvePow2.fn.frame = 5 := (by decide); omega)
      (UInt64.ofNat D) mem3
    rwa [Validate.toNat_ofNat_lt (by omega)] at this
  refine Wp.call (values := [UInt64.ofNat D]) (by wev []) pw ?_
  have lean := nodeRootAt_eq (B := B) laidE two
  rw [← hB, hX] at lean
  by_cases hit : mb = 1 ∧ idx.testBit D = true
  · -- A mixed-in word on the path: the word itself, or a turn into it.
    obtain ⟨m1, bit⟩ := hit
    have bitNe : UInt64.ofNat idx &&& UInt64.ofNat (2 ^ D) ≠ 0 := by
      rw [and_pow_ne _ (by omega), Validate.toNat_ofNat_lt idxSmall]; exact bit
    refine Wp.ifElse_t (v := 1) (by wev [m1, bitNe]) (by decide) ?_
    obtain ⟨word, hw⟩ : ∃ word, layout.mixin = some word := by
      cases hmm : layout.mixin with
      | none => simp [hmm] at hmb; omega
      | some x => exact ⟨x, rfl⟩
    have Dmb : Nat.log2 idx - 1 = D := by omega
    rw [hw] at lean
    simp only [Dmb, bit, ite_true] at lean
    have sOut := pre.sOut
    simp only [Apart] at sOut
    by_cases dz : D = 0
    · -- The word itself, copied out of the record.
      simp only [dz, ne_eq, not_true_eq_false, ite_false] at lean
      have dz' : (UInt64.ofNat D) = 0 := by rw [dz]; rfl
      refine Wp.ifElse_f (by wev [dz']) ?_
      have aw : w.access (job + 24 + 40) 32 = true := Driver.access_sub pre.scrAcc (by omega) (by omega)
      refine BranchProof.copy32_wp (d := UInt64.ofNat out) (s := UInt64.ofNat (job + 24 + 40))
        (fun _ => by wev []) (fun _ => by wev [])
        (by rw [Validate.toNat_ofNat_lt (by omega)]; exact pre.outAcc)
        (by rw [Validate.toNat_ofNat_lt (by omega)]; exact aw)
        (by rw [Validate.toNat_ofNat_lt (by omega), Validate.toNat_ofNat_lt (by omega)]; simp only [Apart]; omega)
        fun mem' copied fr => ⟨by rw [lean]; wev [], fun node h => ?_, fun a h1 h2 h3 => ?_⟩
      · rw [lean] at h
        cases h
        rw [← laid3.word word hw]
        simp only [BranchProof.readNode, nodeAt]
        congr 1
        funext i
        have := copied i.val i.isLt
        rwa [Validate.toNat_ofNat_lt (by omega), Validate.toNat_ofNat_lt (by omega)] at this
      · rw [Validate.toNat_ofNat_lt (by omega)] at fr
        rw [fr a h1, keep3 a (fun h => h2 ⟨h.1, by omega⟩)]
    · -- A turn below the word, which has no parts.
      simp only [dz, ne_eq, not_false_eq_true, ite_true] at lean
      have dz' : (UInt64.ofNat D) ≠ 0 := by
        intro h; have := congrArg UInt64.toNat h; rw [Validate.toNat_ofNat_lt (by omega)] at this; exact dz this
      refine Wp.ifElse_t (v := 1) (by wev [dz']) (by decide) ?_
      refine Wp.set (by wev []) (Wp.done ⟨by rw [lean]; wev [], fun node h => ?_, fun a h1 h2 h3 => ?_⟩)
      · rw [lean] at h; cases h
      · exact keep3 a (fun h => h2 ⟨h.1, by omega⟩)
  · -- No word on the path: the walk inside the layout's tree, from the depth past any word.
    refine Wp.ifElse_f ?_ ?_
    · rcases (show mb = 0 ∨ mb = 1 by omega) with h | h
      · wonly [h]; split <;> rfl
      · have bz : UInt64.ofNat idx &&& UInt64.ofNat (2 ^ D) = 0 := by
          rcases Decidable.em (UInt64.ofNat idx &&& UInt64.ofNat (2 ^ D) = 0) with hz | hc
          · exact hz
          · exact absurd ⟨h, by
              have := (and_pow_ne (UInt64.ofNat idx) (i := D) (by omega)).mp hc
              rwa [Validate.toNat_ofNat_lt idxSmall] at this⟩ hit
        wev [h, bz]
    have xw : X = treeWalk B b layout idx D := by
      cases hmm : layout.mixin with
      | none =>
        simp [hmm] at hmb
        rw [hmm] at lean; rw [lean, ← hD, ← hmb, Nat.sub_zero]
      | some word =>
        simp [hmm] at hmb
        rw [hmm] at lean
        have nb : idx.testBit D = false := by
          cases h : idx.testBit D
          · rfl
          · exact absurd ⟨by omega, h⟩ hit
        rw [lean, show Nat.log2 idx - 1 = D by omega, nb]
        rfl
    -- What the tree's walk needs: the record holds the layout, and the scratch past it is free.
    have sOut := pre.sOut
    have sPad := pre.sPad
    have oData := pre.oData
    have oPlan := pre.oPlan
    have oPad := pre.oPad
    have dPad := pre.dataPad
    have pPad := pre.planPad
    simp only [Apart] at sOut sPad oData oPlan oPad dPad pPad
    have wpre : WalkPre w mem3 (job + 24) data p (p + 8 * (words d).length) (job + 24 + rb) out ctx (job + 24 + rb)
        (span - rb) table zeros pad mask b :=
      { ready := pre.ready.within pre.sCtx pre.sTable pre.sZeros fun a h1 _ => keep3 a fun h => h1 ⟨h.1, by omega⟩
        bytes := fun k hk => by rw [keep3 _ (by omega)]; exact pre.bytes k hk
        readable := pre.readable
        small := sml
        usize := pre.usize
        fixedPart := Driver.access_sub pre.scrAcc (Nat.le_refl _) (by omega)
        base := by omega
        outW := out3
        ctxW := ctx3
        freeW := free3
        freeAcc := Driver.access_sub pre.scrAcc (by omega) (by omega)
        outAcc := pre.outAcc
        away := fun a h => by simp only [Footprint]; omega
        dataApart := by omega
        freeCtx := apart_sub pre.sCtx (by omega) (by omega)
        freeTable := apart_sub pre.sTable (by omega) (by omega)
        freeZeros := apart_sub pre.sZeros (by omega) (by omega)
        freePad := apart_sub pre.sPad (by omega) (by omega)
        outCtx := pre.oCtx
        outTable := pre.oTable
        outZeros := pre.oZeros
        outPad := pre.oPad
        outFree := by simp only [Apart]; omega }
    -- The walk to a node of one value under the tree, one level down.
    have child : ∀ spC, w.stackLo + 16384 + 2048 * d.nesting - 576 ≤ spC → ∀ slots, layout.leaves = .nested slots →
        ChildCalls m w spC mem3 B b slots data out ctx (job + 24 + rb) (span - rb) pad p
          (p + 8 * (words d).length) := by
      intro spC hspC slots nested mm i c s' e' q idx' hslot hsame hplan hlo hhi hout hscr hctx hi1 hi2
      have kid := layout_children pre.sound ord ins (by simp only [RootProof.Small]; rw [pre.usize]; exact sml)
        ⟨v, read⟩ laidE nested hslot
      have shallow := kid.shallow
      have wc := walkNeed_child kid.child b.size pre.below
      have wm := walkMost_child kid.child b.size pre.below
      rw [hrb] at wc
      have wp := words_pos c
      have far : ∀ a, ¬ (job + 24 ≤ a ∧ a < job + 24 + span) → mm a = mem a := fun a h => by
        rw [hsame a (by omega), keep3 a (by omega)]
      have cpre : NodePre w mm c b q data s' e' (job + 24 + rb + 24) out ctx table zeros pad mask (span - rb - 48) :=
        { ready := pre.ready.within pre.sCtx pre.sTable pre.sZeros fun a h1 _ => far a h1
          planned := hplan
          fits := kid.child.fits pre.fits
          bytes := fun k hk => by rw [far _ (by omega)]; exact pre.bytes k hk
          readable := pre.readable
          small := sml
          usize := pre.usize
          spread := pre.spread
          sound := kid.sound
          thin := kid.child.narrow pre.thin
          ordered := kid.ordered
          inside := kid.inside
          accepted := kid.accepted
          jobAcc := Driver.access_sub pre.scrAcc (by omega) (by omega)
          outW := hout
          scrW := by
            rw [show job + 24 + rb + 24 + 8 = job + 24 + rb + 32 by omega,
              show job + 24 + rb + 24 + 24 = job + 24 + rb + 48 by omega]
            exact hscr
          ctxW := by rw [show job + 24 + rb + 24 + 16 = job + 24 + rb + 40 by omega]; exact hctx
          outAcc := pre.outAcc
          scrAcc := Driver.access_sub pre.scrAcc (by omega) (by omega)
          slack := by omega
          room := by omega
          below := Nat.lt_of_le_of_lt wm pre.below
          sData := apart_sub pre.sData (by omega) (by omega)
          sPad := apart_sub pre.sPad (by omega) (by omega)
          sCtx := apart_sub pre.sCtx (by omega) (by omega)
          sTable := apart_sub pre.sTable (by omega) (by omega)
          sZeros := apart_sub pre.sZeros (by omega) (by omega)
          sPlan := by simp only [Apart]; omega
          sOut := apart_sub pre.sOut (by omega) (by omega)
          oData := pre.oData
          oPad := pre.oPad
          oCtx := pre.oCtx
          oTable := pre.oTable
          oZeros := pre.oZeros
          oPlan := by simp only [Apart]; omega
          dataPad := pre.dataPad
          planPad := by simp only [Apart]; omega }
      obtain ⟨r, mm', call, rc, rnode, rframe⟩ := ih c shallow spC mm b q data s' e' (job + 24 + rb + 24) out ctx
        table zeros pad mask (span - rb - 48) idx' (by simp only [nodeStack]; omega) cpre hi2
      have budget := nodeRootAt_budget c b s' e' idx' (n := c.nesting) (n' := B) (Nat.le_refl _) (by omega)
      exact ⟨r, mm', call, by rw [rc, budget], fun node h => rnode node (by rw [budget]; exact h),
        fun a h1 h2 h3 => rframe a h1 (fun h => h2 ⟨by omega, by omega⟩) h3⟩
    -- The stack each tree walk needs, with the frames named as numbers.
    have fB : ProveBounded.fn.frame = 29 := by decide
    have fL : ProveLeaves.fn.frame = 23 := by decide
    have fP : ProveProgressive.fn.frame = 19 := by decide
    have fS : ProveSlot.fn.frame = 19 := by decide
    have fK : planSkip.frame = 5 := by decide
    have wl : walkLevel = 112 := by decide
    have ts : treeStack = 10552 := rfl
    have one' := nesting_pos d
    have broom : w.stackLo + 8 + 8 * ProveBounded.fn.frame + boundedRoom (d.nesting - 1) ≤ spN := by
      simp only [boundedRoom, slotRoom, fB, fL, fS, fK, wl, ts]; omega
    have proom := progressive_stack (lo := w.stackLo) one' spRoom
    have bstack : w.stackLo + rootStack d + 256 ≤ spN - 8 - 8 * ProveBounded.fn.frame - 8 - 8 * ProveLeaves.fn.frame := by
      simp only [rootStack, fB, fL]; omega
    have pstack : w.stackLo + rootStack d + 256 ≤ spN - 8 - 8 * ProveProgressive.fn.frame - 8 -
        8 * ProveBounded.fn.frame - 8 - 8 * ProveLeaves.fn.frame := by
      simp only [rootStack, fB, fL, fP]; omega
    have a16 : w.access (job + 24 + 16) 8 = true := Driver.access_sub pre.scrAcc (by omega) (by omega)
    have a24 : w.access (job + 24 + 24) 8 = true := Driver.access_sub pre.scrAcc (by omega) (by omega)
    have bd3 := laid3.bounded
    cases hl : layout.limit with
    | some cap =>
      -- A bounded tree.
      have capS := limit_small laidE pre.fits pre.sound sml ins cap hl
      simp only [treeWalk, hl] at xw
      have cap3 := laid3.capacity cap hl
      simp only [hl, Option.isSome_some, ite_true] at bd3
      refine Wp.ifElse_t (v := 1) (by wev [a16, bd3]) (by decide) ?_
      obtain ⟨r, mb', bcall, brc, bnode, bframe⟩ := bounded_calls_decoded fns.range.roots.plan.codec fns.gather hash
        fns.range fns.bounded fns.range.roots.plan.depth fns.pow2 fns.shr fns.leaves fns.slot broom laid3 wpre
        (by omega) (by omega) B idx D 0 cap idxSmall (by omega) (by decide) capS dec pre.spread (by omega) pre.dataPad
        bstack (need.mono (by omega)) (fun slots h => child _ (by rw [fB]; omega) slots h)
      refine Wp.call (values := [UInt64.ofNat (job + 24), UInt64.ofNat idx, UInt64.ofNat D, UInt64.ofNat 0,
        UInt64.ofNat cap]) (by wev [a24, cap3]) bcall
        (Wp.done ⟨by rw [xw, brc]; wev [], fun node h => bnode node (xw ▸ h), fun a h1 h2 h3 => ?_⟩)
      rw [bframe a h1 (fun h => h2 ⟨by omega, by omega⟩) h3, keep3 a (fun h => h2 ⟨h.1, by omega⟩)]
    | none =>
      -- A progressive tree, from its first level.
      simp only [treeWalk, hl] at xw
      simp only [hl, Option.isSome_none, Bool.false_eq_true, ite_false] at bd3
      refine Wp.ifElse_f (by wev [a16, bd3]) ?_
      obtain ⟨r, mb', pcall, prc, pnode, pframe⟩ := progressive_calls_decoded fns.range.roots.plan.codec fns.gather
        hash fns.range fns.progressive fns.spineWalk fns.bounded fns.spine fns.level fns.range.roots.plan.depth
        fns.pow2 fns.shr fns.leaves fns.slot proom laid3 wpre (by omega) cs B idx D 0 idxSmall (by omega) (.inl rfl)
        dec pre.spread (by omega) pre.dataPad pstack (need.mono (by omega))
        (fun slots h => child _ (by rw [fB, fP]; omega) slots h)
      have j0 : spineStart 0 = 0 := rfl
      have p0 : (4 : Nat) ^ 0 = 1 := rfl
      rw [j0, p0] at pcall prc pnode
      refine Wp.call (values := [UInt64.ofNat (job + 24), UInt64.ofNat idx, UInt64.ofNat D, UInt64.ofNat 0,
        UInt64.ofNat 1]) (by wev []) pcall
        (Wp.done ⟨by rw [xw, prc]; wev [], fun node h => pnode node (xw ▸ h), fun a h1 h2 h3 => ?_⟩)
      rw [pframe a h1 (fun h => h2 ⟨by omega, by omega⟩) h3, keep3 a (fun h => h2 ⟨h.1, by omega⟩)]

/-- The walk to a node of every type, by induction on how deeply it nests. -/
theorem node_at_nesting {m : Module} {w : World} (fns : ProveFns m) (hash : HashingOk m w) :
    ∀ n d, d.nesting ≤ n → NodeAtSpec m w d
  | 0, d, h => absurd h (by have := nesting_pos d; omega)
  | n + 1, d, _ => node_at_step fns hash d fun c hc => node_at_nesting fns hash n c (by omega)

/-- The walk to a node of a type answers what the Lean walk answers. -/
theorem node_at_ok {m : Module} {w : World} (fns : ProveFns m) (hash : HashingOk m w) (d : Desc) :
    NodeAtSpec m w d :=
  node_at_nesting fns hash d.nesting d (Nat.le_refl _)

/-! ### The walk's contract, discharged -/

/--
An address a proving driver may write: none of the context, the table, the zero roots, the padding area, the plan,
or the encoding with the byte past it.
-/
def ProveFree (ctx table zeros pad plan planLen data size : Nat) (a : Nat) : Prop :=
  ¬ ((ctx ≤ a ∧ a < ctx + 32) ∨ (table ≤ a ∧ a < table + Kernel.tableSize) ∨
    (zeros ≤ a ∧ a < zeros + 32 * (zeroHeights + 1)) ∨ (pad ≤ a ∧ a < pad + 1536) ∨
    (plan ≤ a ∧ a < plan + planLen) ∨ (data ≤ a ∧ a < data + size + 1))

/-- What memory holds while a proving driver runs: the filled context, the type's plan, and the encoding. -/
def ProveReady (w : World) (d : Desc) (b : ByteArray) (plan data ctx table zeros pad : Nat) (mask : UInt64)
    (mem : Memory) : Prop :=
  RootReady w ctx table zeros pad mask mem ∧ PlanAt w mem plan (words d) ∧ BytesAt mem data b

/--
What a proving driver's walks need of the type, the encoding, and the context, beyond what memory holds.

The encoding is one validation accepts, the type nests at most 64 deep, and the prover's scratch bound is below the cap.
-/
structure ProveStatic (w : World) (d : Desc) (b : ByteArray) (plan data ctx table zeros pad : Nat) : Prop where
  /-- The plan's words fit a word. -/
  fits : Fits (words d)
  /-- The encoding is usable. -/
  readable : w.access data b.size = true
  /-- Eight bits per byte of the encoding, and more, stay below the word size. -/
  small : 64 * b.size + 128 < 2 ^ 64
  /-- A machine word holds a full 64-bit size. -/
  usize : USize.size = 2 ^ 64
  /-- Twice the encoding's size past its address stays below the address bound. -/
  spread : data + 2 * b.size ≤ addressBound
  /-- The type is legal. -/
  sound : d.wellFormed = .ok ()
  /-- Every fixed-size type inside it is far below the word size. -/
  thin : narrow d = true
  /-- Validation accepts the encoding. -/
  valid : validate d b = .ok ()
  /-- The type nests at most 64 deep. -/
  deep : d.nesting ≤ 64
  /-- The prover's scratch bound is below the cap. -/
  below : proveScratch d b.size < scratchCap
  /-- The encoding misses the padding area. -/
  dataPad : Apart (data, b.size) (pad, 1536)
  /-- The plan misses the padding area. -/
  planPad : Apart (plan, 8 * (words d).length) (pad, 1536)

/-- A nonempty run of addresses a proving driver may write misses everything else. -/
theorem free_apart {ctx table zeros pad plan planLen data size o n : Nat}
    (h : ∀ k < n, ProveFree ctx table zeros pad plan planLen data size (o + k)) (pos : 0 < n) (planPos : 0 < planLen) :
    Apart (o, n) (ctx, 32) ∧ Apart (o, n) (table, Kernel.tableSize) ∧
      Apart (o, n) (zeros, 32 * (zeroHeights + 1)) ∧ Apart (o, n) (pad, 1536) ∧ Apart (o, n) (plan, planLen) ∧
      Apart (o, n) (data, size) := by
  have each : ∀ a, o ≤ a → a < o + n → ProveFree ctx table zeros pad plan planLen data size a := fun a h1 h2 => by
    have := h (a - o) (by omega); rwa [Nat.add_sub_cancel' h1] at this
  have ts : 0 < Kernel.tableSize := by decide
  simp only [ProveFree] at each
  simp only [Apart]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | exact run_apart (fun a h1 h2 => by have := each a h1 h2; omega) (Nat.le_refl o) (Nat.le_refl _) pos
        (by omega)
    | (have := run_apart (lo := o) (hi := o + n) (x := o) (n := n) (o := data) (k := size + 1)
        (fun a h1 h2 => by have := each a h1 h2; omega) (Nat.le_refl o) (Nat.le_refl _) pos (by omega)
       omega)

set_option maxHeartbeats 4000000 in
/--
The walk to one node keeps its contract, on an encoding validation accepts and a type nesting at most 64 deep, with
the prover's scratch bound past the walk's job.
-/
theorem nodeAtOk_of {m : Module} {w : World} (fns : ProveFns m) (hash : HashingOk m w) {d : Desc} {b : ByteArray}
    {plan data ctx table zeros pad : Nat} {mask : UInt64} (st : ProveStatic w d b plan data ctx table zeros pad) :
    NodeAtOk m w d b (UInt64.ofNat plan) (UInt64.ofNat data) (UInt64.ofNat ctx) pad
      (ProveReady w d b plan data ctx table zeros pad mask)
      (ProveFree ctx table zeros pad plan (8 * (words d).length) data b.size) (proveScratch d b.size - 24)
      (nodeStack d) where
  node := by
    intro sp mem index out scr ready stack outAcc scrAcc outFree scrFree apart w0 w8 w16
    obtain ⟨rr, planned, bytes⟩ := ready
    obtain ⟨most, need⟩ := proveScratch_need st.below st.deep
    have wp := words_pos d
    have so := BranchProof.access_bound scrAcc
    have oo := BranchProof.access_bound outAcc
    have sl : addressBound = 2 ^ 63 := rfl
    have aS := free_apart scrFree (by omega) (by omega)
    have aO := free_apart outFree (by omega) (by omega)
    have ap := apart
    simp only [Apart] at aS aO ap
    have scr24 : (scr + 24).toNat = scr.toNat + 24 := BranchProof.toNat_add_of_lt _ _ (by simp; omega)
    have fit : scr.toNat + 24 + (proveScratch d b.size - 56) ≤ scr.toNat + 24 + (proveScratch d b.size - 24) := by
      omega
    have pre : NodePre w mem d b plan data 0 b.size scr.toNat out.toNat ctx table zeros pad mask
        (proveScratch d b.size - 56) :=
      { ready := rr, planned := planned, fits := st.fits, bytes := bytes, readable := st.readable, small := st.small,
        usize := st.usize, spread := st.spread, sound := st.sound, thin := st.thin, ordered := Nat.zero_le _,
        inside := Nat.le_refl _, accepted := by simpa using accepted_of_validate st.valid
        jobAcc := BranchProof.access_prefix scrAcc (by omega)
        outW := by rw [w0, UInt64.ofNat_toNat]
        scrW := by rw [w8, ← scr24, UInt64.ofNat_toNat]
        ctxW := w16
        outAcc := outAcc
        scrAcc := Driver.access_sub scrAcc (by omega) (by omega)
        slack := by omega
        room := by omega
        below := most
        sData := by simp only [Apart]; omega
        sPad := by simp only [Apart]; omega
        sCtx := by simp only [Apart]; omega
        sTable := by simp only [Apart]; omega
        sZeros := by simp only [Apart]; omega
        sPlan := by simp only [Apart]; omega
        sOut := by simp only [Apart]; omega
        oData := by simp only [Apart]; omega
        oPad := by simp only [Apart]; omega
        oCtx := by simp only [Apart]; omega
        oTable := by simp only [Apart]; omega
        oZeros := by simp only [Apart]; omega
        oPlan := by simp only [Apart]; omega
        dataPad := st.dataPad
        planPad := st.planPad }
    obtain ⟨r, mem', call, rc, rnode, rframe⟩ := node_at_ok fns hash d sp mem b plan data 0 b.size scr.toNat out.toNat
      ctx table zeros pad mask (proveScratch d b.size - 56) index.toNat (by omega) pre index.toNat_lt
    refine ⟨r, mem', by simpa using call, ?_, fun node h => ?_, fun a h1 h2 h3 => rframe a h1 (by omega) h3⟩
    · rw [rc, walkNode, walkNode_nesting]
    · rw [walkNode, walkNode_nesting] at h
      have := rnode node h
      cases node
      show (⟨nodeAt mem' out.toNat⟩ : ByteArray) = _
      rw [this]
  ready_frame := by
    intro mem mem' ⟨rr, planned, bytes⟩ same
    have pc := rr.padCtx
    have pt := rr.padTable
    have pz := rr.padZeros
    have dp := st.dataPad
    have pp := st.planPad
    simp only [Apart] at pc pt pz dp pp
    refine ⟨rr.frame fun a h => same a (by simp only [ProveFree]; simp only [RootReady.Held] at h; omega)
      (by simp only [RootReady.Held] at h; omega), PlanAt.frame planned fun a h1 h2 => same a
        (by simp only [ProveFree]; omega) (by omega), fun k hk => ?_⟩
    rw [same _ (by simp only [ProveFree]; omega) (by omega)]
    exact bytes k hk
  padKept := fun a h1 h2 => by simp only [ProveFree]; omega

end EthLib.Consensus.Ssz.Native.Driver.ProveProof
