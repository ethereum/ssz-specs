import SszNative.Proofs.Driver.Root.Range

/-!
The progressive tree driver writes the Lean progressive root of a run of nodes.

The Lean spine roots subtrees of 1, 4, 16, and so on nodes, and hashes each against the spine after it.
The driver roots the subtrees first, each into the left half of a pair of nodes in its scratch.
It then closes the spine with a zero node and folds it from the last pair up, each parent landing in the right half of
the pair before.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Asm

/-! ### The spine, level by level -/

/-- The first node of the subtree at a level of the spine. -/
def spineStart : Nat → Nat
  | 0 => 0
  | k + 1 => spineStart k + 4 ^ k

/-- The subtrees before a level hold a third of its width, rounded down. -/
theorem spineStart_pow : ∀ k, 3 * spineStart k + 1 = 4 ^ k
  | 0 => rfl
  | k + 1 => by rw [spineStart, Nat.pow_succ, ← spineStart_pow k]; omega

/-- Each level starts at least as many nodes in as its index. -/
theorem le_spineStart : ∀ k, k ≤ spineStart k
  | 0 => Nat.le_refl _
  | k + 1 => by
    have := le_spineStart k
    have := Nat.pow_pos (n := k) (show 0 < 4 by decide)
    rw [spineStart]; omega

/-- Levels up to thirty are at most 2^60 wide. -/
theorem level_wide {k : Nat} (hk : k ≤ 30) : 4 ^ k ≤ 2 ^ 60 :=
  Nat.le_trans (Nat.pow_le_pow_right (by decide) hk) (by rw [four_pow_eq]; exact Nat.le_refl _)

/-- A level starting below 2^57 nodes is one of the first thirty. -/
theorem level_few {k count : Nat} (h : spineStart k < count) (c : count < 2 ^ 57) : k ≤ 29 := by
  refine Nat.le_of_not_lt fun big => ?_
  have := Nat.pow_le_pow_right (show 0 < 4 by decide) (show 30 ≤ k by omega)
  have := spineStart_pow k
  have e : 4 ^ 30 = 2 ^ 60 := by rw [four_pow_eq]
  omega

/-- The spine from a level on, as the Lean progressive tree computes it. -/
def spineFrom (x : ByteArray) (count k : Nat) : ByteArray :=
  spine x count (spineStart k) (4 ^ k) (count + 1 - k)

/-- The subtree at a level of the spine. -/
def spineTree (x : ByteArray) (count k : Nat) : ByteArray :=
  merkleizeAt x (32 * spineStart k) (min (4 ^ k) (count - spineStart k)) (2 * k)

/-- The progressive root is the spine from its first level. -/
theorem merkleizeProgressive_spineFrom (x : ByteArray) (count : Nat) :
    merkleizeProgressive x count = spineFrom x count 0 := by
  simp [merkleizeProgressive, spineFrom, spineStart]

/-- A level with nodes left is its subtree hashed with the spine after it. -/
theorem spineFrom_step (x : ByteArray) {count k : Nat} (hk : spineStart k < count) :
    spineFrom x count k = hashPair (spineTree x count k) (spineFrom x count (k + 1)) := by
  have le := le_spineStart k
  have hl : Nat.log2 (4 ^ k) = 2 * k := by rw [four_pow_eq, Nat.log2_two_pow]
  have fuel : count + 1 - k = (count - k) + 1 := by omega
  simp only [spineFrom, spineTree, fuel, spine, hl]
  rw [ite_eq_right (by omega), spineStart, show 4 * 4 ^ k = 4 ^ (k + 1) by rw [Nat.pow_succ, Nat.mul_comm],
    show count + 1 - (k + 1) = count - k by omega]

/-- A level past the nodes is the zero node. -/
theorem spineFrom_done (x : ByteArray) {count k : Nat} (hk : k ≤ count) (h : count ≤ spineStart k) :
    spineFrom x count k = zeroNode := by
  have fuel : count + 1 - k = (count - k) + 1 := by omega
  simp only [spineFrom, fuel, spine]
  rw [ite_eq_left h]

/-- The spine from a level is one node. -/
theorem spineFrom_size {x : ByteArray} {count : Nat} (inside : 32 * count ≤ x.size) (small : x.size < USize.size)
    {k : Nat} (hk : k ≤ count) : (spineFrom x count k).size = 32 :=
  (spine_spec x count inside small (count + 1 - k) (spineStart k) k (by have := le_spineStart k; omega)).1

/-- A subtree of the spine is one node. -/
theorem spineTree_size {x : ByteArray} {count : Nat} (inside : 32 * count ≤ x.size) (small : x.size < USize.size)
    {k : Nat} (h : spineStart k < count) : (spineTree x count k).size = 32 :=
  (merkleizeAt_spec x _ _ _ (by rw [← four_pow_eq]; exact Nat.min_le_left _ _) (by
    have := Nat.min_le_right (4 ^ k) (count - spineStart k); omega) small).1

/-! ### The spine from a later first level -/

/-- The spine from a level on, when its first level is the one at a given index. -/
def spineFromAt (j : Nat) (x : ByteArray) (count k : Nat) : ByteArray :=
  spine x count (4 ^ j * spineStart k) (4 ^ (j + k)) (count + 1 - k)

/-- The subtree at a level of the spine, when its first level is the one at a given index. -/
def spineTreeAt (j : Nat) (x : ByteArray) (count k : Nat) : ByteArray :=
  merkleizeAt x (32 * (4 ^ j * spineStart k)) (min (4 ^ (j + k)) (count - 4 ^ j * spineStart k)) (2 * (j + k))

/-- From the first level, the spine is the one above. -/
theorem spineFromAt_zero (x : ByteArray) (count k : Nat) : spineFromAt 0 x count k = spineFrom x count k := by
  simp [spineFromAt, spineFrom]

/-- From the first level, a subtree is the one above. -/
theorem spineTreeAt_zero (x : ByteArray) (count k : Nat) : spineTreeAt 0 x count k = spineTree x count k := by
  simp [spineTreeAt, spineTree]

/-- The levels before one hold a third of its width, scaled by the first level's width. -/
theorem startFrom_pow (j k : Nat) : 3 * (4 ^ j * spineStart k) + 4 ^ j = 4 ^ (j + k) := by
  rw [Nat.pow_add, ← spineStart_pow k, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm]

/-- The next level starts one width further in. -/
theorem startFrom_succ (j k : Nat) : 4 ^ j * spineStart (k + 1) = 4 ^ j * spineStart k + 4 ^ (j + k) := by
  rw [spineStart, Nat.mul_add, Nat.pow_add]

/-- Each level starts at least as many nodes in as its index. -/
theorem le_startFrom (j k : Nat) : k ≤ 4 ^ j * spineStart k :=
  Nat.le_trans (le_spineStart k) (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide)))

/-- The progressive root from a level's width is the spine from that level. -/
theorem merkleizeProgressive_spineFromAt (j : Nat) (x : ByteArray) (count : Nat) :
    merkleizeProgressive x count (4 ^ j) = spineFromAt j x count 0 := by
  simp [merkleizeProgressive, spineFromAt, spineStart]

/-- A level with nodes left is its subtree hashed with the spine after it. -/
theorem spineFromAt_step (j : Nat) (x : ByteArray) {count k : Nat} (hk : 4 ^ j * spineStart k < count) :
    spineFromAt j x count k = hashPair (spineTreeAt j x count k) (spineFromAt j x count (k + 1)) := by
  have le := le_startFrom j k
  have hl : Nat.log2 (4 ^ (j + k)) = 2 * (j + k) := by rw [four_pow_eq, Nat.log2_two_pow]
  have fuel : count + 1 - k = (count - k) + 1 := by omega
  simp only [spineFromAt, spineTreeAt, fuel, spine, hl]
  rw [ite_eq_right (by omega), startFrom_succ,
    show 4 * 4 ^ (j + k) = 4 ^ (j + (k + 1)) by rw [← Nat.add_assoc, Nat.pow_succ, Nat.mul_comm],
    show count + 1 - (k + 1) = count - k by omega]

/-- A level past the nodes is the zero node. -/
theorem spineFromAt_done (j : Nat) (x : ByteArray) {count k : Nat} (hk : k ≤ count)
    (h : count ≤ 4 ^ j * spineStart k) : spineFromAt j x count k = zeroNode := by
  have fuel : count + 1 - k = (count - k) + 1 := by omega
  simp only [spineFromAt, fuel, spine]
  rw [ite_eq_left h]

/-- The spine from a level is one node. -/
theorem spineFromAt_size {x : ByteArray} {count : Nat} (inside : 32 * count ≤ x.size) (small : x.size < USize.size)
    (j : Nat) {k : Nat} (hk : k ≤ count) : (spineFromAt j x count k).size = 32 := by
  have h := (spine_spec x count inside small (count + 1 - k) (4 ^ j * spineStart k) (j + k)
    (by have := le_startFrom j k; omega)).1
  exact h

/-- A subtree of the spine is one node. -/
theorem spineTreeAt_size {x : ByteArray} {count : Nat} (inside : 32 * count ≤ x.size) (small : x.size < USize.size)
    (j : Nat) {k : Nat} (h : 4 ^ j * spineStart k < count) : (spineTreeAt j x count k).size = 32 :=
  (merkleizeAt_spec x _ _ _ (by rw [← four_pow_eq]; exact Nat.min_le_left _ _) (by
    have := Nat.min_le_right (4 ^ (j + k)) (count - 4 ^ j * spineStart k); omega) small).1

/-- A level starting below 2^57 nodes, counted from a first level of at most thirty, is at most the thirtieth. -/
theorem levelFrom_few {j k count : Nat} (jle : j ≤ 30) (h : 4 ^ j * spineStart k < count) (c : count < 2 ^ 57) :
    j + k ≤ 30 := by
  cases k with
  | zero => omega
  | succ k =>
    refine Nat.le_of_not_lt fun big => ?_
    have grow : 4 ^ (j + k) ≤ 4 ^ j * spineStart (k + 1) := by
      rw [startFrom_succ]; omega
    have := Nat.pow_le_pow_right (show 0 < 4 by decide) (show 29 ≤ j + k by omega)
    have e : 4 ^ 29 = 2 ^ 58 := by rw [four_pow_eq]
    omega

/-- The levels a run of fewer than 2^57 nodes reaches, from a first level of at most thirty, end by the 31st. -/
theorem levelsFrom_le {j k count : Nat} (jle : j ≤ 30) (c : count < 2 ^ 57)
    (h : k = 0 ∨ 4 ^ j * spineStart (k - 1) < count) : j + k ≤ 31 := by
  rcases h with rfl | h
  · omega
  · have := levelFrom_few jle h c; omega

/-- Levels up to the 31st are at most 2^62 wide. -/
theorem level_wide' {k : Nat} (hk : k ≤ 31) : 4 ^ k ≤ 2 ^ 62 :=
  Nat.le_trans (Nat.pow_le_pow_right (by decide) hk) (by rw [four_pow_eq]; exact Nat.le_refl _)

/-- A level up to the 31st starts below 2^62 nodes in. -/
theorem startFrom_lt {j k : Nat} (h : j + k ≤ 31) : 4 ^ j * spineStart k < 2 ^ 62 := by
  have pw := startFrom_pow j k
  have wide := level_wide' h
  have pos := Nat.pow_pos (n := j) (show 0 < 4 by decide)
  generalize 4 ^ j * spineStart k = A at *
  generalize 4 ^ (j + k) = W at *
  generalize 4 ^ j = P at *
  omega

/-! ### The driver -/

/-- The progressive tree driver's arguments. -/
structure ProgEnv (env : Env) (nodes count out scratch ctx : Nat) : Prop where
  /-- The first node. -/
  nodes : env 0 = UInt64.ofNat nodes
  /-- The count. -/
  count : env 1 = UInt64.ofNat count
  /-- The output. -/
  out : env 2 = UInt64.ofNat out
  /-- The scratch. -/
  scratch : env 3 = UInt64.ofNat scratch
  /-- The context. -/
  ctx : env 4 = UInt64.ofNat ctx

/-- Writing a variable past the arguments keeps them. -/
theorem ProgEnv.write {env : Env} {nodes count out scratch ctx : Nat} (h : ProgEnv env nodes count out scratch ctx)
    {x : Nat} (v : UInt64) (hx : 5 ≤ x) : ProgEnv (Asm.assign env x v) nodes count out scratch ctx :=
  ⟨by rw [assign_ne (by omega), h.nodes], by rw [assign_ne (by omega), h.count], by rw [assign_ne (by omega), h.out],
    by rw [assign_ne (by omega), h.scratch], by rw [assign_ne (by omega), h.ctx]⟩

/-- The progressive tree driver's frame holds nineteen words. -/
theorem progressiveFrame : RootProgressive.fn.frame = 19 := by decide

/-- The bytes the progressive tree driver uses from its scratch on: the pairs, then one subtree's levels. -/
abbrev progressiveSpan (count : Nat) : Nat := 2560 + 2048 + 32 * count

/-- What the progressive tree driver needs, besides its stack. -/
structure ProgPre (w : World) (mem : Memory) (nodes count out scratch ctx table zeros pad : Nat) (mask : UInt64)
    (x : ByteArray) : Prop where
  /-- The context is filled. -/
  ready : RootReady w ctx table zeros pad mask mem
  /-- The nodes are in memory. -/
  held : Holds mem nodes x
  /-- The buffer holds the nodes. -/
  inside : 32 * count ≤ x.size
  /-- The buffer has machine-sized offsets. -/
  small : x.size < USize.size
  /-- There are fewer than 2^57 nodes. -/
  few : count < 2 ^ 57
  /-- The nodes are usable. -/
  nAcc : w.access nodes (32 * count) = true
  /-- The nodes end a node short of the address bound. -/
  nReach : nodes + 32 * (count + 1) ≤ addressBound
  /-- The output is usable. -/
  oAcc : w.access out 32 = true
  /-- The scratch is usable. -/
  sAcc : w.access scratch (progressiveSpan count) = true
  /-- The scratch misses the nodes. -/
  sN : Apart (scratch, progressiveSpan count) (nodes, x.size)
  /-- It misses the output. -/
  sO : Apart (scratch, progressiveSpan count) (out, 32)
  /-- It misses the padding area. -/
  sPad : Apart (scratch, progressiveSpan count) (pad, 1536)
  /-- It misses the context. -/
  sCtx : Apart (scratch, progressiveSpan count) (ctx, 32)
  /-- It misses the table. -/
  sTable : Apart (scratch, progressiveSpan count) (table, Kernel.tableSize)
  /-- It misses the zero roots. -/
  sZeros : Apart (scratch, progressiveSpan count) (zeros, 32 * (zeroHeights + 1))
  /-- The output misses the padding area. -/
  oPad : Apart (out, 32) (pad, 1536)
  /-- It misses the context. -/
  oCtx : Apart (out, 32) (ctx, 32)
  /-- It misses the table. -/
  oTable : Apart (out, 32) (table, Kernel.tableSize)
  /-- It misses the zero roots. -/
  oZeros : Apart (out, 32) (zeros, 32 * (zeroHeights + 1))
  /-- The nodes miss the padding area. -/
  nPad : Apart (nodes, x.size) (pad, 1536)

/-- The subtree loop of the progressive tree driver. -/
abbrev progLoop : Stmt :=
  while_ (lt RootProgressive.start RootProgressive.count) [
    RootProgressive.here ::= RootProgressive.count - RootProgressive.start,
    when (lt RootProgressive.width RootProgressive.here) [RootProgressive.here ::= RootProgressive.width],
    callInto RootProgressive.sink "ssz_merkleize"
      [RootProgressive.nodes + 32 * RootProgressive.start, RootProgressive.here, RootProgressive.lg,
        RootProgressive.scratch + 64 * RootProgressive.k,
        RootProgressive.scratch + (RootProgressive.spineBytes : Nat), RootProgressive.ctx],
    RootProgressive.k ::= RootProgressive.k + 1,
    RootProgressive.start ::= RootProgressive.start + RootProgressive.width,
    RootProgressive.width ::= 4 * RootProgressive.width, RootProgressive.lg ::= RootProgressive.lg + 2]

/-- The subtree loop's state after a number of subtrees. -/
def ProgAt (mem0 : Memory) (nodes count out scratch ctx pad : Nat) (x : ByteArray) (env : Env)
    (mem : Memory) (k : Nat) : Prop :=
  ProgEnv env nodes count out scratch ctx ∧ env 5 = UInt64.ofNat k ∧ env 6 = UInt64.ofNat (spineStart k) ∧
    env 7 = UInt64.ofNat (4 ^ k) ∧ env 8 = UInt64.ofNat (2 * k) ∧ (k = 0 ∨ spineStart (k - 1) < count) ∧
    (∀ j < k, nodeAt mem (scratch + 64 * j) = (spineTree x count j).data) ∧
    ∀ a, ¬ (scratch ≤ a ∧ a < scratch + progressiveSpan count) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem a = mem0 a

/-- The levels a run of fewer than 2^57 nodes reaches are at most thirty. -/
theorem levels_le {k count : Nat} (c : count < 2 ^ 57) (h : k = 0 ∨ spineStart (k - 1) < count) : k ≤ 30 := by
  rcases h with rfl | h
  · omega
  · have := level_few h c; omega

/-! ### The subtree loop, from any first level -/

/-- The parts of a progressive tree driver's state, each held in a variable of its own. -/
inductive SpineRole
  | nodes | count | out | scratch | ctx | k | start | width | lg | here | sink | i
  deriving DecidableEq

/-- Which variable holds each part of a progressive tree driver's state. -/
structure SpineVars where
  /-- The variable holding a part. -/
  slot : SpineRole → Nat
  /-- No two parts share a variable. -/
  apart : ∀ a b, slot a = slot b → a = b

/-- Two distinct parts sit in two distinct variables. -/
theorem SpineVars.ne (v : SpineVars) (a b : SpineRole) (h : a ≠ b := by decide) : v.slot a ≠ v.slot b :=
  fun e => h (v.apart a b e)

/-- The variable holding a part, in the small language. -/
abbrev SpineVars.var (v : SpineVars) (r : SpineRole) : Var := ⟨v.slot r⟩

/-- Where the driver over a run of nodes keeps each part. -/
def rootVars : SpineVars where
  slot
    | .nodes => 0 | .count => 1 | .out => 2 | .scratch => 3 | .ctx => 4 | .k => 5 | .start => 6
    | .width => 7 | .lg => 8 | .here => 9 | .sink => 10 | .i => 11
  apart a b h := by cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- A progressive tree driver's arguments. -/
structure SpineEnv (v : SpineVars) (env : Env) (nodes count out scratch ctx : Nat) : Prop where
  /-- The first node. -/
  nodes : env (v.slot .nodes) = UInt64.ofNat nodes
  /-- The count. -/
  count : env (v.slot .count) = UInt64.ofNat count
  /-- The output. -/
  out : env (v.slot .out) = UInt64.ofNat out
  /-- The scratch. -/
  scratch : env (v.slot .scratch) = UInt64.ofNat scratch
  /-- The context. -/
  ctx : env (v.slot .ctx) = UInt64.ofNat ctx

/-- Writing a variable that holds no argument keeps the arguments. -/
theorem SpineEnv.write {v : SpineVars} {env : Env} {nodes count out scratch ctx : Nat}
    (h : SpineEnv v env nodes count out scratch ctx) (r : SpineRole) (val : UInt64)
    (hr : r ≠ .nodes ∧ r ≠ .count ∧ r ≠ .out ∧ r ≠ .scratch ∧ r ≠ .ctx := by decide) :
    SpineEnv v (Asm.assign env (v.slot r) val) nodes count out scratch ctx :=
  ⟨by rw [assign_ne (v.ne _ _ hr.1.symm), h.nodes], by rw [assign_ne (v.ne _ _ hr.2.1.symm), h.count],
    by rw [assign_ne (v.ne _ _ hr.2.2.1.symm), h.out], by rw [assign_ne (v.ne _ _ hr.2.2.2.1.symm), h.scratch],
    by rw [assign_ne (v.ne _ _ hr.2.2.2.2.symm), h.ctx]⟩

/-- The arguments of the driver over a run of nodes are those of the general driver. -/
theorem ProgEnv.spine {env : Env} {nodes count out scratch ctx : Nat} (h : ProgEnv env nodes count out scratch ctx) :
    SpineEnv rootVars env nodes count out scratch ctx :=
  ⟨h.nodes, h.count, h.out, h.scratch, h.ctx⟩

/-- The arguments of the general driver, kept as the driver over a run of nodes keeps them. -/
theorem SpineEnv.prog {env : Env} {nodes count out scratch ctx : Nat}
    (h : SpineEnv rootVars env nodes count out scratch ctx) : ProgEnv env nodes count out scratch ctx :=
  ⟨h.nodes, h.count, h.out, h.scratch, h.ctx⟩

/-- The subtree loop of a progressive tree driver. -/
abbrev spineLoop (v : SpineVars) : Stmt :=
  while_ (lt (v.var .start) (v.var .count)) [
    v.var .here ::= v.var .count - v.var .start,
    when (lt (v.var .width) (v.var .here)) [v.var .here ::= v.var .width],
    callInto (v.var .sink) "ssz_merkleize"
      [v.var .nodes + 32 * v.var .start, v.var .here, v.var .lg, v.var .scratch + 64 * v.var .k,
        v.var .scratch + (RootProgressive.spineBytes : Nat), v.var .ctx],
    v.var .k ::= v.var .k + 1, v.var .start ::= v.var .start + v.var .width,
    v.var .width ::= 4 * v.var .width, v.var .lg ::= v.var .lg + 2]

/-- The subtree loop's state after a number of subtrees, from a first level. -/
def SpineAt (v : SpineVars) (j : Nat) (mem0 : Memory) (nodes count out scratch ctx pad : Nat) (x : ByteArray)
    (env : Env) (mem : Memory) (k : Nat) : Prop :=
  SpineEnv v env nodes count out scratch ctx ∧ env (v.slot .k) = UInt64.ofNat k ∧
    env (v.slot .start) = UInt64.ofNat (4 ^ j * spineStart k) ∧ env (v.slot .width) = UInt64.ofNat (4 ^ (j + k)) ∧
    env (v.slot .lg) = UInt64.ofNat (2 * (j + k)) ∧ (k = 0 ∨ 4 ^ j * spineStart (k - 1) < count) ∧
    (∀ i < k, nodeAt mem (scratch + 64 * i) = (spineTreeAt j x count i).data) ∧
    ∀ a, ¬ (scratch ≤ a ∧ a < scratch + progressiveSpan count) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem a = mem0 a

set_option maxHeartbeats 2000000 in
/-- Each pass of the subtree loop roots the next subtree into the left half of its pair, from any first level. -/
theorem spineLoop_ends {m : Module} {w : World} (hash : HashingOk m w) {sp : Nat}
    (room : w.stackLo + treeStack ≤ sp) {mem0 : Memory} {nodes count out scratch ctx table zeros pad : Nat}
    {mask : UInt64} {x : ByteArray} (pre : ProgPre w mem0 nodes count out scratch ctx table zeros pad mask x)
    (v : SpineVars) {j : Nat} (jle : j ≤ 30) {env : Env} {mem : Memory}
    (start : SpineAt v j mem0 nodes count out scratch ctx pad x env mem 0) :
    Ends m w sp env mem (spineLoop v) fun e mm => ∃ k, SpineAt v j mem0 nodes count out scratch ctx pad x e mm k ∧
      count ≤ 4 ^ j * spineStart k := by
  have few := pre.few
  have sAcc := pre.sAcc
  have bs := access_bound sAcc
  have bn := access_bound pre.nAcc
  have nReach := pre.nReach
  have bound : addressBound = 2 ^ 63 := rfl
  have zh : zeroHeights = 64 := rfl
  have span : progressiveSpan count = 4608 + 32 * count := rfl
  have xin := pre.inside
  refine (Ends.loop (fun e mm => ∃ k, SpineAt v j mem0 nodes count out scratch ctx pad x e mm k)
    (fun e _ => count - (e (v.slot .start)).toNat) ⟨0, start⟩ ?_ ?_).mono ?_
  · rintro e mm ⟨k, ev, -, hs, -, -, lev, -⟩
    have k31 := levelsFrom_le jle few lev
    have pw := startFrom_pow j k
    have wide := level_wide' k31
    have alow := startFrom_lt k31
    exact ⟨_, eval_lt (eval_var hs) (eval_var ev.count) (by omega) (by omega)⟩
  · rintro e mm val ⟨k, ev, hk, hs, hw, hl, lev, roots, frame⟩ hv nz
    have k31 := levelsFrom_le jle few lev
    have pw := startFrom_pow j k
    have wide := level_wide' k31
    have alow := startFrom_lt k31
    have c := eval_lt (w := w) (env := e) (mem := mm) (eval_var hs) (eval_var ev.count) (by omega) (by omega)
    rw [hv] at c
    have more : 4 ^ j * spineStart k < count := by
      by_cases h : 4 ^ j * spineStart k < count
      · exact h
      · rw [ite_eq_right h] at c; cases c; exact absurd rfl nz
    have k30 := levelFrom_few jle more few
    have pw1 := startFrom_pow j (k + 1)
    have wide1 := level_wide' (show j + (k + 1) ≤ 31 by omega)
    have succ := startFrom_succ j k
    have pos := Nat.pow_pos (n := j + k) (show 0 < 4 by decide)
    -- The subtree's node count: what is left, at most the level's width.
    have s0 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mm) (x := v.slot .here) (env := e)
      (eval_sub (eval_var ev.count) (eval_var hs) (Nat.le_of_lt more))
    let here := min (4 ^ (j + k)) (count - 4 ^ j * spineStart k)
    have hw' : Asm.assign e (v.slot .here) (UInt64.ofNat (count - 4 ^ j * spineStart k)) (v.slot .width) =
        UInt64.ofNat (4 ^ (j + k)) := by
      rw [assign_ne (v.ne .width .here)]; exact hw
    have s1 : Runs m w sp (Asm.assign e (v.slot .here) (UInt64.ofNat (count - 4 ^ j * spineStart k))) mm
        (when (lt (v.var .width) (v.var .here)) [v.var .here ::= v.var .width])
        (Asm.assign e (v.slot .here) (UInt64.ofNat here)) mm := by
      have cc := eval_lt (w := w) (env := Asm.assign e (v.slot .here)
        (UInt64.ofNat (count - 4 ^ j * spineStart k))) (mem := mm)
        (a := v.var .width) (b := v.var .here) (eval_var hw') (eval_var assign_eq) (by omega) (by omega)
      by_cases full : 4 ^ (j + k) < count - 4 ^ j * spineStart k
      · rw [ite_eq_left full] at cc
        rw [show here = 4 ^ (j + k) from Nat.min_eq_left (by omega)]
        have := Runs.when_true (m := m) (sp := sp) (body := [v.var .here ::= v.var .width]) 1 cc
          (by decide) (Runs.block_cons (Runs.set' (eval_var hw')) (Runs.block_nil _ _ _ _ _))
        simpa only [assign_assign] using this
      · rw [ite_eq_right full] at cc
        rw [show here = count - 4 ^ j * spineStart k from Nat.min_eq_right (by omega)]
        exact Runs.when_false cc
    let F := Asm.assign e (v.slot .here) (UInt64.ofNat here)
    have fv : ∀ r, r ≠ .here → F (v.slot r) = e (v.slot r) := fun r hr => assign_ne (v.ne _ _ hr)
    have hereLe : here ≤ count - 4 ^ j * spineStart k := Nat.min_le_right _ _
    have hereW : here ≤ 4 ^ (j + k) := Nat.min_le_left _ _
    -- The subtree, rooted by the tree driver into the left half of its pair.
    have ready := pre.ready.within (o := scratch) (n := progressiveSpan count) pre.sCtx pre.sTable pre.sZeros
      fun a o pd => frame a o pd
    have tpre : TreePre w mm (nodes + 32 * (4 ^ j * spineStart k)) here (2 * (j + k)) (scratch + 64 * k)
        (scratch + 2560) ctx table zeros pad mask :=
      { ctxAccess := ready.ctxAccess, maskAt := ready.maskAt, tableAt := ready.tableAt, zerosAt := ready.zerosAt,
        padAt := ready.padAt, tableBytes := ready.tableHeld, tableAccess := ready.tableAccess,
        zeroRoots := ready.zeroRoots, zerosAccess := ready.zerosAccess, deep := by rw [zh]; omega,
        fits := by rw [← four_pow_eq]; exact hereW, nodesAccess := access_sub pre.nAcc (by omega) (by omega),
        outAccess := access_sub sAcc (by omega) (by omega), scratchAccess := access_sub sAcc (by omega) (by omega),
        padAccess := ready.padAccess,
        scratchNodes := apart_sub' (apart_sub pre.sN (by omega) (by omega)) (by omega) (by omega),
        scratchOut := by simp only [Apart]; omega, scratchCtx := apart_sub pre.sCtx (by omega) (by omega),
        scratchTable := apart_sub pre.sTable (by omega) (by omega),
        scratchZeros := apart_sub pre.sZeros (by omega) (by omega),
        scratchPad := apart_sub pre.sPad (by omega) (by omega),
        padNodes := apart_comm (apart_sub pre.nPad (by omega) (by omega)), padCtx := ready.padCtx,
        padTable := ready.padTable, padZeros := ready.padZeros, nodesReach := by omega,
        outNodes := apart_sub' (apart_sub pre.sN (by omega) (by omega)) (by omega) (by omega),
        outZeros := apart_sub pre.sZeros (by omega) (by omega) }
    obtain ⟨mm', call, root, keep⟩ := treeCalls_native hash.merkleize (sp := sp) tpre ready.kernels room
      (by have := pre.small; omega)
    have r2 := Runs.call (m := m) (sp := sp) (env := F) (mem := mm) (dst := v.slot .sink)
      (args := [v.var .nodes + 32 * v.var .start, v.var .here, v.var .lg, v.var .scratch + 64 * v.var .k,
        v.var .scratch + (RootProgressive.spineBytes : Nat), v.var .ctx])
      (by
        simp only [List.mapM_cons, List.mapM_nil,
          eval_add (eval_var ((fv .nodes (by decide)).trans ev.nodes)) (eval_mul (eval_lit 32)
            (eval_var ((fv .start (by decide)).trans hs))),
          eval_var (show F (v.slot .here) = UInt64.ofNat here from assign_eq),
          eval_var ((fv .lg (by decide)).trans hl),
          eval_add (eval_var ((fv .scratch (by decide)).trans ev.scratch)) (eval_mul (eval_lit 64)
            (eval_var ((fv .k (by decide)).trans hk))),
          eval_add (eval_var ((fv .scratch (by decide)).trans ev.scratch)) (eval_cast 2560),
          eval_var ((fv .ctx (by decide)).trans ev.ctx)]
        rfl) call
    let G := Asm.assign F (v.slot .sink) 0
    have gv : ∀ r, r ≠ .here → r ≠ .sink → G (v.slot r) = e (v.slot r) := fun r h9 h10 => by
      simp only [G]; rw [assign_ne (v.ne _ _ h10), fv r h9]
    have s3 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mm') (x := v.slot .k) (env := G)
      (eval_add (eval_var ((gv .k (by decide) (by decide)).trans hk)) (eval_lit 1))
    let G1 := Asm.assign G (v.slot .k) (UInt64.ofNat (k + 1))
    have s4 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mm') (x := v.slot .start) (env := G1)
      (eval_add (eval_var (show G1 (v.slot .start) = UInt64.ofNat (4 ^ j * spineStart k) by
          simp only [G1]; rw [assign_ne (v.ne .start .k)]; exact (gv .start (by decide) (by decide)).trans hs))
        (eval_var (show G1 (v.slot .width) = UInt64.ofNat (4 ^ (j + k)) by
          simp only [G1]; rw [assign_ne (v.ne .width .k)]; exact (gv .width (by decide) (by decide)).trans hw)))
    let G2 := Asm.assign G1 (v.slot .start) (UInt64.ofNat (4 ^ j * spineStart k + 4 ^ (j + k)))
    have s5 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mm') (x := v.slot .width) (env := G2)
      (eval_mul (eval_lit 4) (eval_var (show G2 (v.slot .width) = UInt64.ofNat (4 ^ (j + k)) by
          simp only [G2, G1]; rw [assign_ne (v.ne .width .start), assign_ne (v.ne .width .k)]
          exact (gv .width (by decide) (by decide)).trans hw)))
    let G3 := Asm.assign G2 (v.slot .width) (UInt64.ofNat (4 * 4 ^ (j + k)))
    have s6 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mm') (x := v.slot .lg) (env := G3)
      (eval_add (eval_var (show G3 (v.slot .lg) = UInt64.ofNat (2 * (j + k)) by
          simp only [G3, G2, G1]
          rw [assign_ne (v.ne .lg .width), assign_ne (v.ne .lg .start), assign_ne (v.ne .lg .k)]
          exact (gv .lg (by decide) (by decide)).trans hl)) (eval_lit 2))
    refine ⟨_, mm', Runs.block_cons s0 (Runs.block_cons s1 (Runs.block_cons r2 (Runs.block_cons s3
      (Runs.block_cons s4 (Runs.block_cons s5 (Runs.block_cons s6 (Runs.block_nil _ _ _ _ _))))))), ⟨k + 1, ?_⟩, ?_⟩
    · refine ⟨((((((ev.write .here _).write .sink _).write .k _).write .start _).write .width _).write .lg _),
        ?_, ?_, ?_, ?_, Or.inr (by simpa using more), fun i hi => ?_, fun a o pd => ?_⟩
      · simp only [G3, G2, G1]
        rw [assign_ne (v.ne .k .lg), assign_ne (v.ne .k .width), assign_ne (v.ne .k .start), assign_eq]
      · simp only [G3, G2]
        rw [assign_ne (v.ne .start .lg), assign_ne (v.ne .start .width), assign_eq, startFrom_succ]
      · simp only [G3]
        rw [assign_ne (v.ne .width .lg), assign_eq, ← Nat.add_assoc, Nat.pow_succ, Nat.mul_comm]
      · rw [assign_eq, show 2 * (j + k) + 2 = 2 * (j + (k + 1)) by omega]
      · -- The new subtree is the last one, and the earlier ones lie below its levels.
        by_cases last : i = k
        · subst last
          rw [root, merkleizeAt_of_holds (pre.held.congr fun q hq => frame _ (by
              have := pre.sN; simp only [Apart] at this; omega) (by
              have := pre.nPad; simp only [Apart] at this; omega)) (by omega)
              (by rw [← four_pow_eq]; exact hereW) pre.small]
          rfl
        · rw [nodeAt_congr (m₂ := mm) fun q hq => keep _ (by omega) (by
              have := pre.sPad; simp only [Apart] at this; omega) (by omega)]
          exact roots i (by omega)
      · rw [keep a (fun h => o ⟨by omega, by omega⟩) pd (fun h => o ⟨by omega, by omega⟩)]
        exact frame a o pd
    · have e6 : Asm.assign G3 (v.slot .lg) (UInt64.ofNat (2 * (j + k) + 2)) (v.slot .start) =
          UInt64.ofNat (4 ^ j * spineStart k + 4 ^ (j + k)) := by
        simp only [G3, G2]; rw [assign_ne (v.ne .start .lg), assign_ne (v.ne .start .width), assign_eq]
      rw [e6, hs, ofNat_toNat (by omega), ofNat_toNat (by omega)]
      omega
  · rintro e mm ⟨⟨k, at_⟩, exit⟩
    obtain ⟨ev, -, hs, -, -, lev, -, -⟩ := id at_
    have k31 := levelsFrom_le jle few lev
    have pw := startFrom_pow j k
    have wide := level_wide' k31
    have alow := startFrom_lt k31
    rw [eval_lt (eval_var hs) (eval_var ev.count) (by omega) (by omega)] at exit
    refine ⟨k, at_, Nat.le_of_not_lt fun h => ?_⟩
    rw [ite_eq_left h] at exit
    cases exit

/-- The subtree loop's state of the driver over a run of nodes is the general one from the first level. -/
theorem ProgAt.spine {mem0 : Memory} {nodes count out scratch ctx pad : Nat} {x : ByteArray} {env : Env}
    {mem : Memory} {k : Nat} (h : ProgAt mem0 nodes count out scratch ctx pad x env mem k) :
    SpineAt rootVars 0 mem0 nodes count out scratch ctx pad x env mem k := by
  obtain ⟨ev, hk, hs, hw, hl, lev, roots, frame⟩ := h
  refine ⟨ev.spine, hk, ?_, ?_, ?_, ?_, fun i hi => ?_, frame⟩
  · rw [Nat.pow_zero, Nat.one_mul]; exact hs
  · rw [Nat.zero_add]; exact hw
  · rw [Nat.zero_add]; exact hl
  · rw [Nat.pow_zero, Nat.one_mul]; exact lev
  · rw [spineTreeAt_zero]; exact roots i hi

/-- The general subtree loop's state from the first level is that of the driver over a run of nodes. -/
theorem SpineAt.prog {mem0 : Memory} {nodes count out scratch ctx pad : Nat} {x : ByteArray} {env : Env}
    {mem : Memory} {k : Nat} (h : SpineAt rootVars 0 mem0 nodes count out scratch ctx pad x env mem k) :
    ProgAt mem0 nodes count out scratch ctx pad x env mem k := by
  obtain ⟨ev, hk, hs, hw, hl, lev, roots, frame⟩ := h
  rw [Nat.pow_zero, Nat.one_mul] at hs lev
  rw [Nat.zero_add] at hw hl
  refine ⟨ev.prog, hk, hs, hw, hl, lev, fun i hi => ?_, frame⟩
  rw [← spineTreeAt_zero]; exact roots i hi

/-- Each pass of the subtree loop roots the next subtree into the left half of its pair. -/
theorem progLoop_ends {m : Module} {w : World} (hash : HashingOk m w) {sp : Nat}
    (room : w.stackLo + treeStack ≤ sp) {mem0 : Memory} {nodes count out scratch ctx table zeros pad : Nat}
    {mask : UInt64} {x : ByteArray} (pre : ProgPre w mem0 nodes count out scratch ctx table zeros pad mask x)
    {env : Env} {mem : Memory} (start : ProgAt mem0 nodes count out scratch ctx pad x env mem 0) :
    Ends m w sp env mem progLoop fun e mm => ∃ k, ProgAt mem0 nodes count out scratch ctx pad x e mm k ∧
      count ≤ spineStart k := by
  refine (spineLoop_ends hash room pre rootVars (j := 0) (by decide) start.spine).mono ?_
  rintro e mm ⟨k, at_, done⟩
  exact ⟨k, at_.prog, by simpa using done⟩


/-- Later levels start further in. -/
theorem spineStart_mono {j k : Nat} (h : j ≤ k) : spineStart j ≤ spineStart k := by
  induction k with
  | zero => obtain rfl : j = 0 := by omega
            exact Nat.le_refl _
  | succ k ih =>
    rcases Nat.lt_or_eq_of_le h with lt | rfl
    · have := ih (by omega); have := Nat.zero_le (4 ^ k); rw [spineStart]; omega
    · exact Nat.le_refl _

/-- The fold loop of the progressive tree driver. -/
abbrev foldLoop : Stmt :=
  while_ (lt 0 RootProgressive.i) [
    callInto RootProgressive.sink "ssz_hash_pairs"
      [RootProgressive.scratch + 64 * RootProgressive.i - 32, RootProgressive.scratch + 64 * RootProgressive.i,
        RootProgressive.scratch + 64 * RootProgressive.i + 32, 1, RootProgressive.ctx],
    RootProgressive.i ::= RootProgressive.i - 1]

/-- The fold loop's state at a pair: every subtree in place, and the spine after the pair in its right half. -/
def FoldAt (mem0 : Memory) (nodes count out scratch ctx pad : Nat) (x : ByteArray) (env : Env) (mem : Memory)
    (k i : Nat) : Prop :=
  ProgEnv env nodes count out scratch ctx ∧ env 11 = UInt64.ofNat i ∧ i < k ∧
    (∀ j < k, nodeAt mem (scratch + 64 * j) = (spineTree x count j).data) ∧
    nodeAt mem (scratch + 64 * i + 32) = (spineFrom x count (i + 1)).data ∧
    ∀ a, ¬ (scratch ≤ a ∧ a < scratch + progressiveSpan count) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem a = mem0 a

/-- The fold loop of a progressive tree driver. -/
abbrev spineFold (v : SpineVars) : Stmt :=
  while_ (lt 0 (v.var .i)) [
    callInto (v.var .sink) "ssz_hash_pairs"
      [v.var .scratch + 64 * v.var .i - 32, v.var .scratch + 64 * v.var .i, v.var .scratch + 64 * v.var .i + 32, 1,
        v.var .ctx],
    v.var .i ::= v.var .i - 1]

/-- The fold loop's state at a pair, from a first level: every subtree in place, and the spine after the pair. -/
def SpineFoldAt (v : SpineVars) (j : Nat) (mem0 : Memory) (nodes count out scratch ctx pad : Nat) (x : ByteArray)
    (env : Env) (mem : Memory) (k i : Nat) : Prop :=
  SpineEnv v env nodes count out scratch ctx ∧ env (v.slot .i) = UInt64.ofNat i ∧ i < k ∧
    (∀ l < k, nodeAt mem (scratch + 64 * l) = (spineTreeAt j x count l).data) ∧
    nodeAt mem (scratch + 64 * i + 32) = (spineFromAt j x count (i + 1)).data ∧
    ∀ a, ¬ (scratch ≤ a ∧ a < scratch + progressiveSpan count) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem a = mem0 a

set_option maxHeartbeats 1000000 in
/-- The fold loop hashes each pair into the right half of the pair before, down to the first pair. -/
theorem spineFold_ends {m : Module} {w : World} (hash : HashingOk m w) {sp : Nat}
    (room : w.stackLo + hashStack ≤ sp) {mem0 : Memory} {nodes count out scratch ctx table zeros pad : Nat}
    {mask : UInt64} {x : ByteArray} (pre : ProgPre w mem0 nodes count out scratch ctx table zeros pad mask x)
    (v : SpineVars) {j k : Nat} (k31 : k ≤ 31) (less : ∀ l < k, 4 ^ j * spineStart l < count) {env : Env}
    {mem : Memory} {i : Nat} (start : SpineFoldAt v j mem0 nodes count out scratch ctx pad x env mem k i) :
    Ends m w sp env mem (spineFold v) fun e mm => SpineFoldAt v j mem0 nodes count out scratch ctx pad x e mm k 0 := by
  have span : progressiveSpan count = 4608 + 32 * count := rfl
  have bs := access_bound pre.sAcc
  have bound : addressBound = 2 ^ 63 := rfl
  have xin := pre.inside
  have xs := pre.small
  refine (Ends.loop (fun e mm => ∃ i, SpineFoldAt v j mem0 nodes count out scratch ctx pad x e mm k i)
    (fun e _ => (e (v.slot .i)).toNat) ⟨i, start⟩ ?_ ?_).mono ?_
  · rintro e mm ⟨i, ev, hi, lt, -⟩
    exact ⟨_, eval_lt (eval_lit 0) (eval_var hi) (by decide) (by omega)⟩
  · rintro e mm val ⟨i, ev, hi, lt, roots, right, frame⟩ hv nz
    have c := eval_lt (w := w) (env := e) (mem := mm) (eval_lit 0) (eval_var hi) (by decide) (by omega)
    rw [hv] at c
    have pos : 0 < i := by
      by_cases h : 0 < i
      · exact h
      · rw [ite_eq_right h] at c; cases c; exact absurd rfl nz
    have ready := pre.ready.within (o := scratch) (n := progressiveSpan count) pre.sCtx pre.sTable pre.sZeros
      fun a o pd => frame a o pd
    obtain ⟨mm', call, node, keep⟩ := pairInto_runs (m := m) (w := w) hash (sp := sp) room (env := e) (mem := mm)
      (dst := v.slot .sink) (out := scratch + 64 * i - 32) (left := scratch + 64 * i)
      (args := [v.var .scratch + 64 * v.var .i - 32, v.var .scratch + 64 * v.var .i,
        v.var .scratch + 64 * v.var .i + 32, 1, v.var .ctx]) ready
      (access_sub pre.sAcc (by omega) (by omega)) (by omega) (access_sub pre.sAcc (by omega) (by omega))
      (by simp only [Apart]; omega) (apart_sub pre.sPad (by omega) (by omega))
      (apart_sub pre.sPad (by omega) (by omega)) (apart_sub pre.sCtx (by omega) (by omega))
      (apart_sub pre.sTable (by omega) (by omega))
      (by
        simp only [List.mapM_cons, List.mapM_nil,
          eval_sub (eval_add (eval_var ev.scratch) (eval_mul (eval_lit 64) (eval_var hi))) (eval_lit 32)
            (show 32 ≤ scratch + 64 * i by omega),
          eval_add (eval_var ev.scratch) (eval_mul (eval_lit 64) (eval_var hi)),
          eval_add (eval_add (eval_var ev.scratch) (eval_mul (eval_lit 64) (eval_var hi))) (eval_lit 32),
          eval_var ev.ctx]
        rfl)
    have s2 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mm') (x := v.slot .i)
      (env := Asm.assign e (v.slot .sink) 0)
      (eval_sub (eval_var (show Asm.assign e (v.slot .sink) 0 (v.slot .i) = UInt64.ofNat i by
        rw [assign_ne (v.ne .i .sink)]; exact hi)) (eval_lit 1) pos)
    refine ⟨_, mm', Runs.block_cons call (Runs.block_cons s2 (Runs.block_nil _ _ _ _ _)),
      ⟨i - 1, (ev.write .sink 0).write .i _, assign_eq, by omega, fun l hl => ?_, ?_,
        fun a o pd => ?_⟩, ?_⟩
    · rw [nodeAt_congr (m₂ := mm) fun q hq => keep _ (by omega) (by
        have := pre.sPad; simp only [Apart] at this; omega)]
      exact roots l hl
    · -- The new parent is the spine from this pair's level.
      rw [show scratch + 64 * (i - 1) + 32 = scratch + 64 * i - 32 by omega, node, roots i lt, right,
        show i - 1 + 1 = i by omega, spineFromAt_step j x (less i lt),
        RootProof.hashPair_data _ _ (spineTreeAt_size xin xs j (less i lt)) (spineFromAt_size xin xs j (by
          have := le_startFrom j i; have := less i lt; omega))]
    · rw [keep a (fun h => o ⟨by omega, by omega⟩) pd]; exact frame a o pd
    · rw [assign_eq]
      rw [hi, ofNat_toNat (by omega), ofNat_toNat (by omega)]
      omega
  · rintro e mm ⟨⟨i, at_⟩, exit⟩
    obtain ⟨ev, hi, -⟩ := id at_
    have lt := at_.2.2.1
    rw [eval_lt (eval_lit 0) (eval_var hi) (by decide) (by omega)] at exit
    have : i = 0 := by
      by_cases h : 0 < i
      · rw [ite_eq_left h] at exit; cases exit
      · omega
    subst this
    exact at_

/-- The fold loop's state of the driver over a run of nodes is the general one from the first level. -/
theorem FoldAt.spine {mem0 : Memory} {nodes count out scratch ctx pad : Nat} {x : ByteArray} {env : Env}
    {mem : Memory} {k i : Nat} (h : FoldAt mem0 nodes count out scratch ctx pad x env mem k i) :
    SpineFoldAt rootVars 0 mem0 nodes count out scratch ctx pad x env mem k i := by
  obtain ⟨ev, hi, lt, roots, right, frame⟩ := h
  refine ⟨ev.spine, hi, lt, fun l hl => ?_, ?_, frame⟩
  · rw [spineTreeAt_zero]; exact roots l hl
  · rw [spineFromAt_zero]; exact right

/-- The general fold loop's state from the first level is that of the driver over a run of nodes. -/
theorem SpineFoldAt.prog {mem0 : Memory} {nodes count out scratch ctx pad : Nat} {x : ByteArray} {env : Env}
    {mem : Memory} {k i : Nat} (h : SpineFoldAt rootVars 0 mem0 nodes count out scratch ctx pad x env mem k i) :
    FoldAt mem0 nodes count out scratch ctx pad x env mem k i := by
  obtain ⟨ev, hi, lt, roots, right, frame⟩ := h
  refine ⟨ev.prog, hi, lt, fun l hl => ?_, ?_, frame⟩
  · rw [← spineTreeAt_zero]; exact roots l hl
  · rw [← spineFromAt_zero]; exact right

/-- The fold loop hashes each pair into the right half of the pair before, down to the first pair. -/
theorem foldLoop_ends {m : Module} {w : World} (hash : HashingOk m w) {sp : Nat}
    (room : w.stackLo + hashStack ≤ sp) {mem0 : Memory} {nodes count out scratch ctx table zeros pad : Nat}
    {mask : UInt64} {x : ByteArray} (pre : ProgPre w mem0 nodes count out scratch ctx table zeros pad mask x)
    {k : Nat} (k30 : k ≤ 30) (less : ∀ j < k, spineStart j < count) {env : Env} {mem : Memory} {i : Nat}
    (start : FoldAt mem0 nodes count out scratch ctx pad x env mem k i) :
    Ends m w sp env mem foldLoop fun e mm => FoldAt mem0 nodes count out scratch ctx pad x e mm k 0 :=
  (spineFold_ends hash room pre rootVars (j := 0) (by omega) (fun l hl => by simpa using less l hl)
    start.spine).mono fun _ _ h => h.prog

set_option maxHeartbeats 2000000 in
/--
The progressive tree driver writes the Lean progressive root of a run of nodes.

Memory changes only at the output, in the scratch, and in the padding area.
-/
theorem rootProgressive_calls {m : Module} {w : World} (hash : HashingOk m w)
    (hf : m.fns.lookup "ssz_root_progressive" = some RootProgressive.fn) {sp : Nat}
    (room : w.stackLo + 8 + 8 * 19 + treeStack ≤ sp) {mem : Memory}
    {nodes count out scratch ctx table zeros pad : Nat} {mask : UInt64} {x : ByteArray}
    (pre : ProgPre w mem nodes count out scratch ctx table zeros pad mask x) :
    ∃ mem', Calls m w "ssz_root_progressive" sp [UInt64.ofNat nodes, UInt64.ofNat count, UInt64.ofNat out,
        UInt64.ofNat scratch, UInt64.ofNat ctx] mem 0 mem' ∧
      nodeAt mem' out = (merkleizeProgressive x count).data ∧ RootReady w ctx table zeros pad mask mem' ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (scratch ≤ a ∧ a < scratch + progressiveSpan count) →
        ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a := by
  have span : progressiveSpan count = 4608 + 32 * count := rfl
  have bs := access_bound pre.sAcc
  have bo := access_bound pre.oAcc
  have bound : addressBound = 2 ^ 63 := rfl
  have xin := pre.inside
  have xs := pre.small
  have few := pre.few
  have treeH : treeStack = 160 + hashStack := rfl
  let sp' := sp - 8 - 8 * RootProgressive.fn.frame
  have room' : w.stackLo + treeStack ≤ sp' := by simp only [sp', progressiveFrame]; omega
  let E0 := entryEnv [UInt64.ofNat nodes, UInt64.ofNat count, UInt64.ofNat out, UInt64.ofNat scratch,
    UInt64.ofNat ctx]
  have ev0 : ProgEnv E0 nodes count out scratch ctx := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have s1 := Runs.set' (m := m) (w := w) (sp := sp') (env := E0) (mem := mem) (x := 5) (eval_lit 0)
  have s2 := Runs.set' (m := m) (w := w) (sp := sp') (env := Asm.assign E0 5 (UInt64.ofNat 0)) (mem := mem) (x := 6)
    (eval_lit 0)
  have s3 := Runs.set' (m := m) (w := w) (sp := sp') (env := Asm.assign (Asm.assign E0 5 (UInt64.ofNat 0)) 6
    (UInt64.ofNat 0)) (mem := mem) (x := 7) (eval_lit 1)
  have s4 := Runs.set' (m := m) (w := w) (sp := sp') (env := Asm.assign (Asm.assign (Asm.assign E0 5
    (UInt64.ofNat 0)) 6 (UInt64.ofNat 0)) 7 (UInt64.ofNat 1)) (mem := mem) (x := 8) (eval_lit 0)
  have at0 : ProgAt mem nodes count out scratch ctx pad x (Asm.assign (Asm.assign (Asm.assign (Asm.assign E0 5
      (UInt64.ofNat 0)) 6 (UInt64.ofNat 0)) 7 (UInt64.ofNat 1)) 8 (UInt64.ofNat 0)) mem 0 :=
    ⟨(((ev0.write _ (by decide)).write _ (by decide)).write _ (by decide)).write _ (by decide),
      by simp [Asm.assign], by simp [Asm.assign, spineStart], by simp [Asm.assign], by simp [Asm.assign],
      Or.inl rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl⟩
  obtain ⟨e1, mm1, run1, k, ⟨ev, hk, hs, -, -, lev, roots, frame⟩, done⟩ := progLoop_ends hash room' pre at0
  have k30 := levels_le few lev
  have ready1 := pre.ready.within (o := scratch) (n := progressiveSpan count) pre.sCtx pre.sTable pre.sZeros
    fun a o pd => frame a o pd
  have c := eval_eq (w := w) (env := e1) (mem := mm1) (a := RootProgressive.k) (b := 0) (eval_var hk) (eval_lit 0)
    (by omega) (by decide)
  have lead : ∀ {r : List Stmt} {e' : Env} {mm' : Memory}, Runs m w sp' e1 mm1 (.block r) e' mm' →
      Runs m w sp' E0 mem (.block ([RootProgressive.k ::= 0, RootProgressive.start ::= 0, RootProgressive.width ::= 1,
        RootProgressive.lg ::= 0, progLoop] ++ r)) e' mm' := fun h =>
    Runs.block_append (Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons s3 (Runs.block_cons s4
      (Runs.block_cons run1 (Runs.block_nil _ _ _ _ _)))))) h
  by_cases empty : k = 0
  · -- No subtree: the root is the zero node.
    subst empty
    rw [ite_eq_left rfl] at c
    have z := zero32_at (m := m) (sp := sp') (env := e1) (mem := mm1) (dst := RootProgressive.out)
      (fun _ => eval_var ev.out) pre.oAcc
    have body : Runs m w sp' E0 mem RootProgressive.fn.body e1 (zeroed mm1 out) :=
      lead (Runs.block_cons (Runs.ifElse_true 1 c (by decide) z) (Runs.block_nil _ _ _ _ _))
    have none : count = 0 := by simp only [spineStart] at done; omega
    refine ⟨_, Calls.fn hf (by rw [progressiveFrame]; omega) rfl body rfl, ?_, ?_, fun a o s pd => ?_⟩
    · rw [nodeAt_zeroed, merkleizeProgressive_spineFrom, spineFrom_done x (by omega) (by omega)]
    · exact ready1.within (o := out) (n := 32) pre.oCtx pre.oTable pre.oZeros fun a o _ => zeroed_outside o
    · rw [zeroed_outside o]; exact frame a s pd
  · -- The spine closes with a zero node, then folds from the last pair up.
    rw [ite_eq_right (by omega)] at c
    have less : ∀ j < k, spineStart j < count := fun j hj => by
      rcases lev with h | h
      · omega
      · exact Nat.lt_of_le_of_lt (spineStart_mono (by omega)) h
    have kc : k ≤ count := by have := le_spineStart (k - 1); have := less (k - 1) (by omega); omega
    have z := zero32_at (m := m) (sp := sp') (env := e1) (mem := mm1)
      (dst := RootProgressive.scratch + 64 * RootProgressive.k - 32) (a := scratch + 64 * k - 32)
      (fun _ => eval_sub (eval_add (eval_var ev.scratch) (eval_mul (eval_lit 64) (eval_var hk))) (eval_lit 32)
        (by omega)) (access_sub pre.sAcc (by omega) (by omega))
    have si := Runs.set' (m := m) (w := w) (sp := sp') (env := e1) (mem := zeroed mm1 (scratch + 64 * k - 32))
      (x := 11) (eval_sub (eval_var hk) (eval_lit 1) (by omega))
    have fold0 : FoldAt mem nodes count out scratch ctx pad x (Asm.assign e1 11 (UInt64.ofNat (k - 1)))
        (zeroed mm1 (scratch + 64 * k - 32)) k (k - 1) := by
      refine ⟨ev.write _ (by decide), assign_eq, by omega, fun j hj => ?_, ?_, fun a o pd => ?_⟩
      · rw [nodeAt_congr (m₂ := mm1) fun q hq => zeroed_outside (by omega)]; exact roots j hj
      · rw [show scratch + 64 * (k - 1) + 32 = scratch + 64 * k - 32 by omega, nodeAt_zeroed,
          show k - 1 + 1 = k by omega, spineFrom_done x kc done]
      · rw [zeroed_outside (by omega)]; exact frame a o pd
    obtain ⟨e2, mm2, run2, ⟨ev2, -, -, roots2, right2, frame2⟩⟩ := foldLoop_ends hash (sp := sp')
      (by omega) pre k30 less fold0
    have ready2 := pre.ready.within (o := scratch) (n := progressiveSpan count) pre.sCtx pre.sTable pre.sZeros
      fun a o pd => frame2 a o pd
    obtain ⟨mm3, call, node, keep⟩ := pairInto_runs (m := m) (w := w) hash (sp := sp') (by omega) (env := e2)
      (mem := mm2) (dst := 10) (out := out) (left := scratch)
      (args := [RootProgressive.out, RootProgressive.scratch, RootProgressive.scratch + 32, 1, RootProgressive.ctx])
      ready2 (access_sub pre.sAcc (by omega) (by omega)) (by omega) pre.oAcc
      (apart_sub pre.sO (by omega) (by omega)) (apart_sub pre.sPad (by omega) (by omega)) pre.oPad pre.oCtx
      pre.oTable
      (by
        simp only [List.mapM_cons, List.mapM_nil, eval_var ev2.out, eval_var ev2.scratch,
          eval_add (eval_var ev2.scratch) (eval_lit 32), eval_var ev2.ctx]
        rfl)
    have body : Runs m w sp' E0 mem RootProgressive.fn.body (Asm.assign e2 10 0) mm3 :=
      lead (Runs.block_cons (Runs.ifElse_false c (Runs.block_append z (Runs.block_cons si (Runs.block_cons run2
        (Runs.block_cons call (Runs.block_nil _ _ _ _ _)))))) (Runs.block_nil _ _ _ _ _))
    refine ⟨_, Calls.fn hf (by rw [progressiveFrame]; omega) rfl body rfl, ?_, ?_, fun a o s pd => ?_⟩
    · have r0 := roots2 0 (by omega)
      simp only [Nat.mul_zero, Nat.add_zero] at r0 right2
      rw [node, r0, right2, merkleizeProgressive_spineFrom, spineFrom_step x (less 0 (by omega)),
        RootProof.hashPair_data _ _ (spineTree_size xin xs (less 0 (by omega))) (spineFrom_size xin xs (by omega))]
    · exact ready2.within (o := out) (n := 32) pre.oCtx pre.oTable pre.oZeros fun a o pd => keep a o pd
    · rw [keep a o pd]; exact frame2 a s pd

end EthLib.Consensus.Ssz.Native.Driver
