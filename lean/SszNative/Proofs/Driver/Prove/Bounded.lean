import SszNative.Proofs.Driver.Prove.Leaves
import SszNative.Proofs.Driver.Prove.Small

/-!
The compiled bounded walk roots the node of a bounded subtree an index names, as the Lean walk does.

A node inside the subtree is the tree over the leaves it spans.
A node below the subtree's leaves is a node of the value at one leaf, which the walk to a node of that value roots.
That walk, and the calls rooting values under the leaves, are taken as contracts.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.ProveProof

set_option maxRecDepth 20000

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Plan

/-! ### The Lean walk, step by step -/

/-- Leaves cut at the same place are the same leaves. -/
theorem leavesIn_congr (b : ByteArray) (layout : EncodedLayout) (first : Nat) {l l' : Nat}
    (same : min l layout.count = min l' layout.count) : leavesIn b layout first l = leavesIn b layout first l' := by
  simp only [leavesIn, same]

/-- No leaves are a tree of zeros, whatever the buffer. -/
theorem merkleizeDepth_none (x y : ByteArray) (depth : Nat) : merkleizeDepth x 0 depth = merkleizeDepth y 0 depth := by
  simp [merkleizeDepth, merkleizeAt]

/-- A node inside a bounded subtree is the tree over the leaves it spans. -/
theorem boundedNode_inside (budget : Nat) (b : ByteArray) (layout : EncodedLayout) (index depth leavesFrom capacity : Nat)
    (inside : depth ≤ depthFor capacity) :
    boundedNode budget b layout index depth leavesFrom capacity =
      .ok (merkleizeDepth
        (leavesIn b layout (leavesFrom + index % 2 ^ depth * 2 ^ (depthFor capacity - depth))
          (leavesFrom + index % 2 ^ depth * 2 ^ (depthFor capacity - depth) + 2 ^ (depthFor capacity - depth))).1
        (leavesIn b layout (leavesFrom + index % 2 ^ depth * 2 ^ (depthFor capacity - depth))
          (leavesFrom + index % 2 ^ depth * 2 ^ (depthFor capacity - depth) + 2 ^ (depthFor capacity - depth))).2
        (depthFor capacity - depth)) := by
  have width : 2 ^ depthFor capacity >>> depth = 2 ^ (depthFor capacity - depth) := by
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_div inside (by decide)]
  rw [boundedNode]
  simp only [nextPow2, Nat.log2_two_pow, ite_eq_left inside, width, depthFor_pow, gindexBelow]
  rfl

/-- A node below a bounded subtree's leaves is a node of the value at one leaf, or a refusal. -/
theorem boundedNode_below (budget : Nat) (b : ByteArray) (layout : EncodedLayout) (index depth leavesFrom capacity : Nat)
    (below : depthFor capacity < depth) :
    boundedNode budget b layout index depth leavesFrom capacity =
      match layout.leaves with
      | .packed _ _ => .error .pathIntoPacked
      | .nested slots =>
        match slots.at (leavesFrom + (index >>> (depth - depthFor capacity)) % 2 ^ depthFor capacity) with
        | some (some (d, s, e)) => nodeRootAt budget d b s e (gindexRebase index (depth - depthFor capacity))
        | _ => .error .pathIntoGap := by
  rw [boundedNode]
  simp only [nextPow2, Nat.log2_two_pow, ite_eq_right (show ¬ depth ≤ depthFor capacity by omega), gindexBelow]
  rfl

/-! ### The driver -/

/-- A word masked by two to a power less one is its remainder by that power. -/
theorem and_mask (x : UInt64) {d : Nat} (hd : d ≤ 64) :
    (x &&& (UInt64.ofNat (2 ^ d) - 1)) = UInt64.ofNat (x.toNat % 2 ^ d) := by
  apply UInt64.toNat_inj.mp
  have xs := x.toNat_lt
  rw [UInt64.toNat_and, Validate.toNat_ofNat_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) xs)]
  rcases Nat.lt_or_ge d 64 with h | h
  · have p : 2 ^ d < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) h
    have one : (1 : UInt64) ≤ UInt64.ofNat (2 ^ d) := by
      rw [UInt64.le_iff_toNat_le, Validate.toNat_ofNat_lt p]; simpa using Nat.one_le_two_pow
    rw [UInt64.toNat_sub_of_le _ _ one, Validate.toNat_ofNat_lt p, UInt64.toNat_one, Nat.and_two_pow_sub_one_eq_mod]
  · obtain rfl : d = 64 := by omega
    rw [Nat.mod_eq_of_lt xs]
    have : (UInt64.ofNat (2 ^ 64) - 1).toNat = 2 ^ 64 - 1 := by decide
    rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt xs]

/--
What a walk inside a layout record needs: the context filled, the encoding in memory, the record's words for the node,
the context and the free scratch, and the node and the scratch usable and apart from everything else.
-/
structure WalkPre (w : World) (mem : Memory) (lay data lo hi top out ctx free span table zeros pad : Nat)
    (mask : UInt64) (b : ByteArray) : Prop where
  /-- The context is filled. -/
  ready : RootReady w ctx table zeros pad mask mem
  /-- The encoding is in memory. -/
  bytes : BytesAt mem data b
  /-- The encoding is usable. -/
  readable : w.access data b.size = true
  /-- Eight bits per byte of the encoding, and more, stay below the word size. -/
  small : 64 * b.size + 128 < 2 ^ 64
  /-- A machine word holds a full 64-bit size. -/
  usize : USize.size = 2 ^ 64
  /-- The record's fixed part is usable. -/
  fixedPart : w.access lay 144 = true
  /-- The record's fixed part ends by its end. -/
  base : lay + 144 ≤ top
  /-- Where the node goes. -/
  outW : readLE mem (lay + 128) 8 = UInt64.ofNat out
  /-- The context. -/
  ctxW : readLE mem (lay + 136) 8 = UInt64.ofNat ctx
  /-- The scratch past the record. -/
  freeW : readLE mem (lay + 120) 8 = UInt64.ofNat free
  /-- The scratch is usable. -/
  freeAcc : w.access free span = true
  /-- The node is usable. -/
  outAcc : w.access out 32 = true
  /-- The scratch, the padding area and the node miss the record, the type's plan and the encoding. -/
  away : ∀ a, (free ≤ a ∧ a < free + span) ∨ (pad ≤ a ∧ a < pad + 1536) ∨ (out ≤ a ∧ a < out + 32) →
    ¬ Footprint lay top lo hi data b.size a
  /-- The scratch misses the encoding. -/
  dataApart : free + span ≤ data ∨ data + b.size ≤ free
  /-- The scratch misses the context. -/
  freeCtx : Apart (free, span) (ctx, 32)
  /-- The scratch misses the table. -/
  freeTable : Apart (free, span) (table, Kernel.tableSize)
  /-- The scratch misses the zero roots. -/
  freeZeros : Apart (free, span) (zeros, 32 * (zeroHeights + 1))
  /-- The scratch misses the padding area. -/
  freePad : Apart (free, span) (pad, 1536)
  /-- The node misses the context. -/
  outCtx : Apart (out, 32) (ctx, 32)
  /-- The node misses the table. -/
  outTable : Apart (out, 32) (table, Kernel.tableSize)
  /-- The node misses the zero roots. -/
  outZeros : Apart (out, 32) (zeros, 32 * (zeroHeights + 1))
  /-- The node misses the padding area. -/
  outPad : Apart (out, 32) (pad, 1536)
  /-- The node misses the scratch. -/
  outFree : Apart (out, 32) (free, span)

/--
What the walk to a node of the value at one leaf does, from memory changed only in the scratch's first 48 bytes, with
the walk's 24-byte job written past the slot reader's answer.

It answers what the Lean walk answers, writes the node when there is one, and changes nothing but the node, the scratch
past the job, and the padding area.
-/
def ChildCalls (m : Module) (w : World) (sp : Nat) (mem : Memory) (budget : Nat) (b : ByteArray) (slots : Slots)
    (data out ctx free span pad lo hi : Nat) : Prop :=
  ∀ (mm : Memory) (i : Nat) (d : Desc) (s e q idx : Nat), slots.at i = some (some (d, s, e)) →
    (∀ a, ¬ (free ≤ a ∧ a < free + 48) → mm a = mem a) → PlanAt w mm q (words d) → lo ≤ q →
    q + 8 * (words d).length ≤ hi → readLE mm (free + 24) 8 = UInt64.ofNat out →
    readLE mm (free + 32) 8 = UInt64.ofNat (free + 48) → readLE mm (free + 40) 8 = UInt64.ofNat ctx → 1 ≤ idx →
    idx < 2 ^ 64 →
    ∃ r mm', Calls m w "ssz_prove_node_at" sp [UInt64.ofNat q, UInt64.ofNat data, UInt64.ofNat s, UInt64.ofNat e,
        UInt64.ofNat idx, UInt64.ofNat (free + 24)] mm r mm' ∧
      r = proveCode (nodeRootAt budget d b s e idx) ∧
      (∀ node, nodeRootAt budget d b s e idx = .ok node → nodeAt mm' out = node.data) ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (free + 48 ≤ a ∧ a < free + span) → ¬ (pad ≤ a ∧ a < pad + 1536) →
        mm' a = mm a

/-- The stack the bounded walk needs below its own frame: the leaves driver's calls, and the tree's. -/
abbrev boundedRoom (n : Nat) : Nat := 8 + 8 * ProveLeaves.fn.frame + slotRoom n + treeStack

set_option maxHeartbeats 8000000 in
/--
A call of the bounded walk answers what the Lean walk answers for a node of a bounded subtree of a layout, and writes
the node when there is one.

The record holds the layout, and the walk needs what the contracts above give.
Memory changes only at the node, in the scratch past the record, and in the padding area.
-/
theorem bounded_calls {m : Module} {w : World} (linked : HasCodec m) (gmod : GatherModule m) (hash : HashingOk m w)
    (hf : m.fns.lookup "ssz_prove_bounded" = some ProveBounded.fn)
    (hd : m.fns.lookup "ssz_depth_for" = some DepthFor.fn)
    (hp : m.fns.lookup "ssz_prove_pow2" = some ProvePow2.fn)
    (hsh : m.fns.lookup "ssz_prove_shr" = some ProveShr.fn)
    (hl : m.fns.lookup "ssz_prove_leaves" = some ProveLeaves.fn)
    (hs : m.fns.lookup "ssz_prove_slot" = some ProveSlot.fn) {sp n : Nat}
    (room : w.stackLo + 8 + 8 * ProveBounded.fn.frame + boundedRoom n ≤ sp)
    {mem : Memory} {lay data lo hi top out ctx free span table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    {layout : EncodedLayout} (laid : LaidOut w mem lay data b n lo hi top layout)
    (pre : WalkPre w mem lay data lo hi top out ctx free span table zeros pad mask b)
    (wide : 64 * layout.count + 4096 ≤ span) (countSmall : layout.count < 2 ^ 62)
    (budget index depth leavesFrom capacity : Nat) (indexSmall : index < 2 ^ 64) (shallow : depth < 64)
    (fromSmall : leavesFrom < 2 ^ 62) (capSmall : capacity < 2 ^ 64)
    (chunked : ∀ first last slots, layout.leaves = .nested slots →
      ChunkCalls m w (sp - 8 - 8 * ProveBounded.fn.frame - 8 - 8 * ProveLeaves.fn.frame) mem b slots data first
        (min last layout.count - first) free span pad ctx lo hi)
    (roots : ∀ first last slots, layout.leaves = .nested slots →
      (∀ element start width count, slots = .stride element start width count → plain element = false) →
      RootCalls m w (sp - 8 - 8 * ProveBounded.fn.frame - 8 - 8 * ProveLeaves.fn.frame) mem b slots data first
        (min last layout.count - first) free span pad ctx lo hi)
    (child : ∀ slots, layout.leaves = .nested slots →
      ChildCalls m w (sp - 8 - 8 * ProveBounded.fn.frame) mem budget b slots data out ctx free span pad lo hi) :
    ∃ r mem', Calls m w "ssz_prove_bounded" sp [UInt64.ofNat lay, UInt64.ofNat index, UInt64.ofNat depth,
        UInt64.ofNat leavesFrom, UInt64.ofNat capacity] mem r mem' ∧
      r = proveCode (boundedNode budget b layout index depth leavesFrom capacity) ∧
      (∀ node, boundedNode budget b layout index depth leavesFrom capacity = .ok node →
        nodeAt mem' out = node.data) ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (free ≤ a ∧ a < free + span) → ¬ (pad ≤ a ∧ a < pad + 1536) →
        mem' a = mem a := by
  have bb := BranchProof.access_bound pre.freeAcc
  have ob := BranchProof.access_bound pre.outAcc
  have lb := BranchProof.access_bound pre.fixedPart
  have db := BranchProof.access_bound pre.readable
  have acc : ∀ k, k + 8 ≤ 144 → w.access (lay + k) 8 = true := fun k hk =>
    BranchProof.access_sub pre.fixedPart (by omega)
  have acc0 : w.access lay 8 = true := BranchProof.access_prefix pre.fixedPart (by omega)
  have outW := pre.outW
  have ctxW := pre.ctxW
  have freeW := pre.freeW
  have counted := laid.count
  have tdLe : depthFor capacity ≤ 64 := by
    have := depthFor_word (UInt64.ofNat capacity)
    rwa [Validate.toNat_ofNat_lt capSmall] at this
  generalize hX : boundedNode budget b layout index depth leavesFrom capacity = X
  suffices body : Wp m w (sp - 8 - 8 * ProveBounded.fn.frame) ProveBounded.fn.body
      (entryEnv [UInt64.ofNat lay, UInt64.ofNat index, UInt64.ofNat depth, UInt64.ofNat leavesFrom,
        UInt64.ofNat capacity]) mem
      (fun env' mem' => eval w env' mem' ProveBounded.fn.result = some (proveCode X) ∧
        (∀ node, X = .ok node → nodeAt mem' out = node.data) ∧
        ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (free ≤ a ∧ a < free + span) → ¬ (pad ≤ a ∧ a < pad + 1536) →
          mem' a = mem a) by
    obtain ⟨mem', c, p⟩ := calls_of_wp hf (by omega) rfl body
    exact ⟨_, mem', c, rfl, p⟩
  -- The stack below the walk's frame, named before the frame is unfolded.
  have fB : ProveBounded.fn.frame = 29 := by decide
  have fL : ProveLeaves.fn.frame = 23 := by decide
  have fP : ProvePow2.fn.frame = 5 := by decide
  have fS : ProveShr.fn.frame = 5 := by decide
  have fD : DepthFor.fn.frame = 5 := by decide
  have ts : treeStack = 10552 := rfl
  rw [fB] at room chunked roots child ⊢
  simp only [boundedRoom, fL, ts] at room chunked roots
  generalize hspB : sp - 8 - 8 * 29 = spB at chunked roots child
  -- The slot reader's stack, named so that arithmetic does not unfold it.
  generalize hSR : slotRoom n = SR at room
  have sPow : w.stackLo + 8 + 8 * ProvePow2.fn.frame ≤ spB := by rw [fP]; clear fB fL fP fS fD ts; omega
  have sShr : w.stackLo + 8 + 8 * ProveShr.fn.frame ≤ spB := by rw [fS]; clear fB fL fP fS fD ts sPow; omega
  have sDep : w.stackLo + 8 + 8 * DepthFor.fn.frame ≤ spB := by
    rw [fD]; clear fB fL fP fS fD ts sPow sShr; omega
  have sLeaves : w.stackLo + 8 + 8 * ProveLeaves.fn.frame + slotRoom n ≤ spB := by
    rw [fL, hSR]; clear fB fL fP fS fD ts sPow sShr sDep; omega
  have sSlot : w.stackLo + slotRoom n ≤ spB := by
    rw [hSR]; clear fB fL fP fS fD ts sPow sShr sDep sLeaves; omega
  have sTree' : w.stackLo + 10552 ≤ spB := by
    generalize (10552 : Nat) = T at room ⊢
    clear fB fL fP fS fD ts sPow sShr sDep sLeaves sSlot hSR; omega
  have sTree : w.stackLo + treeStack ≤ spB := ts ▸ sTree'
  clear room hspB fB fL fP fS fD ts hSR sTree'
  have hdc := depthFor_calls (w := w) hd sDep (UInt64.ofNat capacity) mem
  rw [Validate.toNat_ofNat_lt capSmall] at hdc
  simp only [ProveBounded.fn]
  refine Wp.set (by wev [acc, outW]) (Wp.set (by wev [acc, ctxW]) (Wp.set (by wev [acc, freeW])
    (Wp.set (by wev [acc, counted]) (Wp.set (by wev []) ?_))))
  refine Wp.call (values := [UInt64.ofNat capacity]) (by wev []) hdc ?_
  generalize htd : depthFor capacity = td at hdc tdLe
  have tdv : (td.toUInt64 : UInt64) = UInt64.ofNat td := rfl
  by_cases inside : depth ≤ td
  · -- A node inside the subtree: the tree over the leaves it spans.
    have xIs : X = .ok (merkleizeDepth
        (leavesIn b layout (leavesFrom + index % 2 ^ depth * 2 ^ (td - depth))
          (leavesFrom + index % 2 ^ depth * 2 ^ (td - depth) + 2 ^ (td - depth))).1
        (leavesIn b layout (leavesFrom + index % 2 ^ depth * 2 ^ (td - depth))
          (leavesFrom + index % 2 ^ depth * 2 ^ (td - depth) + 2 ^ (td - depth))).2 (td - depth)) := by
      rw [← hX, boundedNode_inside budget b layout index depth leavesFrom capacity (by omega), htd]
    have tdSmall : td < 2 ^ 64 := by omega
    refine Wp.ifElse_t (by wev [inside]) (by decide) ?_
    simp only [List.append_nil]
    refine Wp.set (by wev []) ?_
    refine Wp.call (values := [UInt64.ofNat depth]) (by wev []) (pow2_calls hp sPow _ mem) ?_
    refine Wp.set (v := UInt64.ofNat (index % 2 ^ depth)) (by
      wonly [Validate.toNat_ofNat_lt (show depth < 2 ^ 64 by omega)]
      rw [and_mask _ (by omega), Validate.toNat_ofNat_lt indexSmall]) ?_
    refine Wp.call (values := [UInt64.ofNat (td - depth)]) (by wev []) (pow2_calls hp sPow _ mem) ?_
    -- Where the node's leaves start, as the driver and the Lean walk name them.
    generalize hk : td - depth = k at xIs
    have kLe : k ≤ 64 := by omega
    have belowLt : index % 2 ^ depth < 2 ^ depth := Nat.mod_lt _ (Nat.two_pow_pos _)
    have offLt : index % 2 ^ depth * 2 ^ k < 2 ^ 64 := by
      have : index % 2 ^ depth * 2 ^ k < 2 ^ depth * 2 ^ k := Nat.mul_lt_mul_of_pos_right belowLt (Nat.two_pow_pos _)
      rw [← Nat.pow_add, show depth + k = td by omega] at this
      exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) tdLe)
    generalize hoff : index % 2 ^ depth * 2 ^ k = off at xIs offLt
    have kv : UInt64.ofNat (2 ^ (UInt64.ofNat k).toNat) = UInt64.ofNat (2 ^ k) := by
      rw [Validate.toNat_ofNat_lt (by omega)]
    refine Wp.set (v := UInt64.ofNat off) (by wev [kv, ← hoff]) ?_
    -- The leaves the node spans, then the tree over them.
    suffices cont : ∀ env, env 0 = UInt64.ofNat lay → env 5 = UInt64.ofNat out → env 6 = UInt64.ofNat ctx →
        env 7 = UInt64.ofNat free → env 9 = UInt64.ofNat k → env 18 = 0 → ∀ first' last',
        env 14 = UInt64.ofNat first' → env 15 = UInt64.ofNat last' → first' < 2 ^ 64 → last' < 2 ^ 64 →
        min last' layout.count - first' ≤ 2 ^ k →
        merkleizeDepth (leavesIn b layout first' last').1 (leavesIn b layout first' last').2 k =
          merkleizeDepth (leavesIn b layout (leavesFrom + off) (leavesFrom + off + 2 ^ k)).1
            (leavesIn b layout (leavesFrom + off) (leavesFrom + off + 2 ^ k)).2 k →
        Wp m w spB (.block [callInto ProveBounded.cnt "ssz_prove_leaves" [ProveBounded.lay, ProveBounded.first,
            ProveBounded.last, ProveBounded.free, ProveBounded.ctx],
          callInto ProveBounded.sink "ssz_merkleize" [ProveBounded.free, ProveBounded.cnt, ProveBounded.k,
            ProveBounded.out, ProveBounded.free + 32 * ProveBounded.cnt + 32, ProveBounded.ctx]]) env mem
          (fun env' mem' => eval w env' mem' (Expr.var 18) = some (proveCode X) ∧
            (∀ node, X = .ok node → nodeAt mem' out = node.data) ∧
            ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (free ≤ a ∧ a < free + span) → ¬ (pad ≤ a ∧ a < pad + 1536) →
              mem' a = mem a) by
      refine Wp.set (by wev []) ?_
      have kpos : 0 < 2 ^ k := Nat.two_pow_pos k
      by_cases hlt : off < layout.count
      · refine Wp.when_t (by wev [hlt]) (by decide) (Wp.set (by wev []) (Wp.set (by wev []) ?_))
        by_cases hA : k < 64 ∧ leavesFrom + off < layout.count
        · have pk : 2 ^ k < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hA.1
          refine Wp.when_t (by wev [hA.1, hA.2]) (by decide) ?_
          by_cases hB : 2 ^ k < layout.count - (leavesFrom + off)
          · refine Wp.when_t (by wev [kv, hB]) (by decide) (Wp.set (by wev [kv]) ?_)
            exact cont _ (by wev []) (by wev []) (by wev []) (by wev []) (by wev []) (by wev []) _
              (leavesFrom + off + 2 ^ k) (by wev []) (by wev [kv]) (by omega)
              (by generalize 2 ^ k = K at *; omega) (by generalize 2 ^ k = K at *; omega) rfl
          · refine Wp.when_f (by wev [kv, hB]) ?_
            have e1 : min layout.count layout.count = min (leavesFrom + off + 2 ^ k) layout.count := by
              generalize 2 ^ k = K at *; omega
            exact cont _ (by wev []) (by wev []) (by wev []) (by wev []) (by wev []) (by wev []) _ layout.count
              (by wev []) (by wev []) (by omega) (by omega) (by generalize 2 ^ k = K at *; omega)
              (by rw [leavesIn_congr b layout _ e1])
        · have c : k < 64 → ¬ leavesFrom + off < layout.count := fun h c => hA ⟨h, c⟩
          have big : layout.count ≤ leavesFrom + off + 2 ^ k ∧ layout.count - (leavesFrom + off) ≤ 2 ^ k := by
            rcases Nat.lt_or_ge k 64 with h | h
            · have := c h
              generalize 2 ^ k = K at *; omega
            · have : 2 ^ 64 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) h
              generalize 2 ^ k = K at *; omega
          refine Wp.when_f (by
            wonly []
            rcases Nat.lt_or_ge k 64 with h | h
            · simp [c h]
            · simp [show ¬ k < 64 by omega]) ?_
          have e1 : min layout.count layout.count = min (leavesFrom + off + 2 ^ k) layout.count := by
            generalize 2 ^ k = K at *; omega
          exact cont _ (by wev []) (by wev []) (by wev []) (by wev []) (by wev []) (by wev []) _ layout.count
            (by wev []) (by wev []) (by omega) (by omega) (by generalize 2 ^ k = K at *; omega)
            (by rw [leavesIn_congr b layout _ e1])
      · refine Wp.when_f (by wev [hlt]) (Wp.set (by wev []) (Wp.when_f (by wonly []; simp) ?_))
        exact cont _ (by wev []) (by wev []) (by wev []) (by wev []) (by wev []) (by wev []) layout.count
          layout.count (by wev []) (by wev []) (by omega) (by omega) (by simp)
          (by
            rw [leavesIn_count, leavesIn_count, show min layout.count layout.count - layout.count = 0 by omega,
              show min (leavesFrom + off + 2 ^ k) layout.count - (leavesFrom + off) = 0 by
                generalize 2 ^ k = K at *; omega]
            exact merkleizeDepth_none _ _ _)
    intro env e0 e5 e6 e7 e9 e18 first' last' e14 e15 fs ls fitsK same
    have cntLe : min last' layout.count - first' ≤ layout.count := by omega
    generalize hc : min last' layout.count - first' = cnt at fitsK cntLe
    obtain ⟨mem1, call1, nodes1, kept1⟩ := leaves_calls linked gmod hl hs sLeaves laid.count laid.encoding laid.leaves
      pre.fixedPart pre.base pre.bytes pre.readable pre.small pre.usize countSmall fs ls pre.freeAcc
      (by rw [hc]; omega) (fun a h => pre.away a (h.elim .inl fun h => .inr (.inl h))) pre.freePad pre.dataApart
      (chunked first' last') (roots first' last')
    rw [leavesIn_count, hc] at call1 nodes1
    refine Wp.call (values := [UInt64.ofNat lay, UInt64.ofNat first', UInt64.ofNat last', UInt64.ofNat free,
      UInt64.ofNat ctx]) (by wev [e0, e14, e15, e7, e6]) call1 ?_
    have fp := pre.freePad
    have fc := pre.freeCtx
    have ft := pre.freeTable
    have fz := pre.freeZeros
    have oc := pre.outFree
    have ozs := pre.outZeros
    simp only [Apart] at fp fc ft fz oc ozs
    have ready1 := pre.ready.within (o := free) (n := span) pre.freeCtx pre.freeTable pre.freeZeros
      fun a o p => kept1 a o p
    have ac : ∀ x n, free ≤ x → x + n ≤ free + span → w.access x n = true := fun x n h1 h2 => by
      have := BranchProof.access_sub (k := x - free) (j := n) pre.freeAcc (by omega)
      rwa [Nat.add_sub_cancel' h1] at this
    have tpre : TreePre w mem1 free cnt k out (free + 32 * cnt + 32) ctx table zeros pad mask :=
      { ctxAccess := ready1.ctxAccess, maskAt := ready1.maskAt, tableAt := ready1.tableAt, zerosAt := ready1.zerosAt,
        padAt := ready1.padAt, tableBytes := ready1.tableHeld, tableAccess := ready1.tableAccess,
        zeroRoots := ready1.zeroRoots, zerosAccess := ready1.zerosAccess, deep := by simp only [zeroHeights]; omega,
        fits := fitsK, nodesAccess := ac _ _ (by omega) (by omega), outAccess := pre.outAcc,
        scratchAccess := ac _ _ (by omega) (by omega), padAccess := ready1.padAccess,
        scratchNodes := by simp only [Apart]; omega, scratchOut := by simp only [Apart]; omega,
        scratchCtx := by simp only [Apart]; omega, scratchTable := by simp only [Apart]; omega,
        scratchZeros := by simp only [Apart]; omega, scratchPad := by simp only [Apart]; omega,
        padNodes := by simp only [Apart]; omega, padCtx := ready1.padCtx, padTable := ready1.padTable,
        padZeros := ready1.padZeros, nodesReach := by omega, outNodes := by simp only [Apart]; omega,
        outZeros := pre.outZeros }
    obtain ⟨mem2, call2, root2, keep2⟩ := treeCalls_native hash.merkleize tpre ready1.kernels sTree
      (by rw [pre.usize]; omega)
    refine Wp.call (values := [UInt64.ofNat free, UInt64.ofNat cnt, UInt64.ofNat k, UInt64.ofNat out,
      UInt64.ofNat (free + 32 * cnt + 32), UInt64.ofNat ctx]) (by wev [e7, e9, e5, e6]) call2 (Wp.done ⟨?_, ?_, ?_⟩)
    · rw [xIs]; wev [e18]
    · intro node hn
      rw [xIs] at hn
      cases hn
      rw [root2, nodes1, ← same, leavesIn_count, hc]
    · intro a h1 h2 h3
      rw [keep2 a (by omega) h3 h1, kept1 a h2 h3]
  · -- A node below the subtree's leaves: a node of the value at one leaf.
    have xIs := hX.symm
    rw [boundedNode_below budget b layout index depth leavesFrom capacity (by omega), htd] at xIs
    refine Wp.ifElse_f (by wev [inside]) ?_
    simp only [List.append_nil]
    have lv := laid.leaves
    cases hlv : layout.leaves with
    | packed nodes c =>
      rw [hlv] at lv xIs
      cases lv with
      | packed _ _ _ kind =>
        refine Wp.ifElse_t (by wev [acc0, kind]) (by decide) (Wp.set (by wev []) (Wp.done ⟨?_, ?_, ?_⟩))
        · rw [xIs]; wev []
        · intro node h; rw [xIs] at h; cases h
        · intro _ _ _ _; rfl
    | nested slots =>
      rw [hlv] at lv xIs
      cases lv with
      | nested _ held plainFlag =>
      have k0 : readLE mem lay 8 ≠ 0 := by
        cases slots with
        | stride => rw [held.stride_facts.1]; decide
        | listed => exact held.listed_kind.1
      refine Wp.ifElse_f (by wonly [acc0]; simp [k0]) ?_
      have kLt : depth - td < 64 := by omega
      obtain ⟨q0, q0v, shrCall⟩ := shr_calls hsh sShr (UInt64.ofNat index) (UInt64.ofNat (depth - td)) mem
      rw [Validate.toNat_ofNat_lt indexSmall, Validate.toNat_ofNat_lt (by omega)] at q0v
      refine Wp.set (by wev []) (Wp.call (values := [UInt64.ofNat index, UInt64.ofNat (depth - td)]) (by wev [])
        shrCall (Wp.call (values := [UInt64.ofNat td]) (by wev []) (pow2_calls hp sPow _ mem) ?_))
      have leafLt : (index / 2 ^ (depth - td)) % 2 ^ td < 2 ^ td := Nat.mod_lt _ (Nat.two_pow_pos _)
      have tdPow : 2 ^ td ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) tdLe
      generalize hleaf : leavesFrom + (index >>> (depth - td)) % 2 ^ td = leaf at xIs
      have leafIs : leaf = leavesFrom + (index / 2 ^ (depth - td)) % 2 ^ td := by
        rw [← hleaf, Nat.shiftRight_eq_div_pow]
      refine Wp.set (v := UInt64.ofNat leaf) (by
        wonly [Validate.toNat_ofNat_lt (show td < 2 ^ 64 by omega)]
        rw [and_mask _ tdLe, q0v, leafIs]
        rw [Validate.ofNat_add_ofNat]) ?_
      have tdPow' : 2 ^ td ≤ 2 ^ 62 := Nat.pow_le_pow_right (by decide) (by omega)
      have leafSmall : leaf < 2 ^ 63 := by
        rw [leafIs]; clear hleaf; generalize 2 ^ td = T at *; omega
      have slotAcc : w.access free 24 = true := BranchProof.access_prefix pre.freeAcc (by omega)
      have slot := slot_calls linked hs sSlot held pre.fixedPart leaf free leafSmall slotAcc
      have base := pre.base
      have rf : lay + 144 ≤ free ∨ free + span ≤ lay := by
        rcases Nat.lt_or_ge free lay with h | h
        · by_cases h' : free + span ≤ lay
          · exact .inr h'
          · exact absurd (.inl ⟨by omega, by omega⟩) (pre.away lay (.inl ⟨by omega, by omega⟩))
        · by_cases h' : lay + 144 ≤ free
          · exact .inl h'
          · exact absurd (.inl ⟨h, by omega⟩) (pre.away free (.inl ⟨by omega, by omega⟩))
      cases hsl : slots.at leaf with
      | some x =>
        cases x with
        | some v =>
          obtain ⟨d, s', e'⟩ := v
          rw [hsl] at slot; simp only [hsl] at xIs
          obtain ⟨q, planned, qlo, qhi, call⟩ := slot
          refine Wp.call (values := [UInt64.ofNat lay, UInt64.ofNat leaf, UInt64.ofNat free]) (by wev []) call ?_
          refine Wp.ifElse_f (by wev []) ?_
          refine Wp.call (values := [UInt64.ofNat (depth - td)]) (by wev []) (pow2_calls hp sPow _ _) ?_
          rw [Validate.toNat_ofNat_lt (show depth - td < 2 ^ 64 by omega)]
          have a24 : w.access (free + 24) 8 = true := BranchProof.access_sub pre.freeAcc (by omega)
          have a32 : w.access (free + 24 + 8) 8 = true := by
            rw [Nat.add_assoc]; exact BranchProof.access_sub pre.freeAcc (by omega)
          have a40 : w.access (free + 24 + 16) 8 = true := by
            rw [Nat.add_assoc]; exact BranchProof.access_sub pre.freeAcc (by omega)
          refine Wp.set (by wev []) (Wp.store (by wev []) (by wev []) (by wonly [a24]) (Wp.store (by wev [])
            (by wev []) (by wonly [a32]) (Wp.store (by wev []) (by wev []) (by wonly [a40]) ?_)))
          simp only [Validate.toNat_ofNat_lt (show free + 24 < 2 ^ 64 by omega),
            Validate.toNat_ofNat_lt (show free + 24 + 8 < 2 ^ 64 by omega),
            Validate.toNat_ofNat_lt (show free + 24 + 16 < 2 ^ 64 by omega), Width.bytes]
          generalize hm1 : written3 mem free (UInt64.ofNat q) (UInt64.ofNat s') (UInt64.ofNat e') = mem1
          have ⟨r0, r8, r16, out1⟩ := record_words mem free (free + 8) (free + 16) (UInt64.ofNat q)
            (UInt64.ofNat s') (UInt64.ofNat e') rfl rfl mem1 hm1.symm
          have ⟨r24, r32, r40, out2⟩ := record_words mem1 (free + 24) (free + 24 + 8) (free + 24 + 16)
            (UInt64.ofNat out) (UInt64.ofNat (free + 24 + 24)) (UInt64.ofNat ctx) rfl rfl _ rfl
          generalize hm2 : store (store (store mem1 (free + 24) 8 (qwordByte (UInt64.ofNat out))) (free + 24 + 8) 8
            (qwordByte (UInt64.ofNat (free + 24 + 24)))) (free + 24 + 16) 8 (qwordByte (UInt64.ofNat ctx)) = mem2
            at r24 r32 r40 out2
          have keep2 : ∀ a, ¬ (free ≤ a ∧ a < free + 48) → mem2 a = mem a := fun a h => by
            rw [out2 a (by omega), out1 a (by omega)]
          have read2 : ∀ x, x + 8 ≤ free ∨ free + 48 ≤ x → readLE mem2 x 8 = readLE mem x 8 := fun x h =>
            readLE_congr _ _ _ 8 fun i hi => keep2 _ (by omega)
          have planned2 : PlanAt w mem2 q (words d) := PlanAt.keep planned ⟨qlo, qhi⟩ fun a h1 h2 =>
            keep2 a fun h => pre.away a (.inl ⟨h.1, by omega⟩) (.inr (.inl ⟨h1, h2⟩))
          obtain ⟨r, mm, call2, rc, rnode, rframe⟩ := child slots hlv mem2 leaf d s' e' q
            (2 ^ (depth - td) + index % 2 ^ (depth - td)) hsl keep2 planned2 qlo qhi
            (by rw [show free + 24 = free + 24 by rfl]; exact r24) (by rw [show free + 32 = free + 24 + 8 by omega]; exact r32)
            (by rw [show free + 40 = free + 24 + 16 by omega]; exact r40) (by have := Nat.two_pow_pos (depth - td); omega)
            (by
              have := Nat.mod_lt index (Nat.two_pow_pos (depth - td))
              have : 2 ^ (depth - td) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
              generalize 2 ^ (depth - td) = P at *; omega)
          have pv : 2 ^ (depth - td) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) kLt
          refine Wp.call (values := [UInt64.ofNat q, UInt64.ofNat data, UInt64.ofNat s', UInt64.ofNat e',
            UInt64.ofNat (2 ^ (depth - td) + index % 2 ^ (depth - td)), UInt64.ofNat (free + 24)]) (by
              have m0 : readLE mem2 free 8 = UInt64.ofNat q := by
                rw [readLE_congr mem2 mem1 free 8 fun i hi => out2 _ (by omega)]; exact r0
              have m8 : readLE mem2 (free + 8) 8 = UInt64.ofNat s' := by
                rw [readLE_congr mem2 mem1 (free + 8) 8 fun i hi => out2 _ (by omega)]; exact r8
              have m16 : readLE mem2 (free + 16) 8 = UInt64.ofNat e' := by
                rw [readLE_congr mem2 mem1 (free + 16) 8 fun i hi => out2 _ (by omega)]; exact r16
              have m72 : readLE mem2 (lay + 72) 8 = UInt64.ofNat data := by
                rw [read2 _ (by omega)]; exact laid.encoding
              have f0 : w.access free 8 = true := BranchProof.access_prefix pre.freeAcc (by omega)
              have f8 : w.access (free + 8) 8 = true := BranchProof.access_sub pre.freeAcc (by omega)
              have f16 : w.access (free + 16) 8 = true := BranchProof.access_sub pre.freeAcc (by omega)
              have hand : (UInt64.ofNat index &&& (UInt64.ofNat (2 ^ (depth - td)) - 1)) =
                  UInt64.ofNat (index % 2 ^ (depth - td)) := by
                rw [and_mask _ (by omega), Validate.toNat_ofNat_lt indexSmall]
              wev [m0, m8, m16, m72, f0, f8, f16, acc, hand]) call2 (Wp.done ⟨?_, ?_, ?_⟩)
          · rw [xIs, rc]; wev []
          · intro node h; rw [xIs] at h; exact rnode node h
          · intro a h1 h2 h3
            rw [rframe a h1 (by omega) h3, keep2 a (by omega)]
        | none =>
          rw [hsl] at slot; simp only [hsl] at xIs
          refine Wp.call (values := [UInt64.ofNat lay, UInt64.ofNat leaf, UInt64.ofNat free]) (by wev []) slot ?_
          refine Wp.ifElse_t (by wev []) (by decide) (Wp.set (by wev []) (Wp.done ⟨?_, ?_, ?_⟩))
          · rw [xIs]; wev []
          · intro node h; rw [xIs] at h; cases h
          · intro _ _ _ _; rfl
      | none =>
        rw [hsl] at slot; simp only [hsl] at xIs
        refine Wp.call (values := [UInt64.ofNat lay, UInt64.ofNat leaf, UInt64.ofNat free]) (by wev []) slot ?_
        refine Wp.ifElse_t (by wev []) (by decide) (Wp.set (by wev []) (Wp.done ⟨?_, ?_, ?_⟩))
        · rw [xIs]; wev []
        · intro node h; rw [xIs] at h; cases h
        · intro _ _ _ _; rfl

end EthLib.Consensus.Ssz.Native.Driver.ProveProof
