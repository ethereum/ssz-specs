import SszNative.Proofs.Driver.TreeStore.Copy

/-!
The build driver leaves a whole tree in memory over its leaves.

It rounds the count up to a power of two, puts the leaves in, fills the rest of the leaf level with zero nodes, then
writes one level per pass, bottom up.
A pass hashes the pairs over data in one call and fills the rest of the level with the zero tree of its height.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir

/--
What the build driver needs: its context, a tree buffer for the width, and the leaves.

The width is 2^K, the count rounded up to a power of two.
The leaves already sit where the tree keeps them, or lie apart from the tree.
-/
structure BuildPre (w : World) (mem : Memory) (tree leaves count K ctx table zeros pad : Nat) (mask : UInt64) :
    Prop where
  /-- The context, its tables, and the padding area. -/
  ctxOk : StoreCtx w mem ctx table zeros pad mask
  /-- The width fits a word with room to spare. -/
  narrow : K < 58
  /-- The leaves fit the width. -/
  covers : count ≤ 2 ^ K
  /-- No smaller power of two holds them. -/
  least : ∀ k < K, 2 ^ k < count
  /-- The tree buffer lies in memory the program may use. -/
  treeAccess : w.access tree (64 * 2 ^ K) = true
  /-- The leaves sit at the tree's leaf level, or lie in usable memory apart from the tree. -/
  leavesOk : leaves = tree + 32 * 2 ^ K ∨
    (w.access leaves (32 * count) = true ∧ Apart (leaves, 32 * count) (tree, 64 * 2 ^ K))
  /-- A node past the tree's end is still within reach, as the kernels' moved pointers need. -/
  treeReach : tree + 64 * 2 ^ K + 32 ≤ 2 ^ 63
  /-- The tree misses the zero-tree roots. -/
  treeZeros : Apart (tree, 64 * 2 ^ K) (zeros, 32 * (zeroHeights + 1))
  /-- It misses the constant table. -/
  treeTable : Apart (tree, 64 * 2 ^ K) (table, Kernel.tableSize)
  /-- It misses the context. -/
  treeCtx : Apart (ctx, 32) (tree, 64 * 2 ^ K)
  /-- It misses the padding area. -/
  treePad : Apart (pad, 1536) (tree, 64 * 2 ^ K)

/-- The build driver's variables that never change. -/
def BuildVals (e : Env) (tree leaves count ctx zeros : Nat) : Prop :=
  e 0 = UInt64.ofNat tree ∧ e 1 = UInt64.ofNat leaves ∧ e 2 = UInt64.ofNat count ∧ e 3 = UInt64.ofNat ctx ∧
    e 4 = UInt64.ofNat zeros

/-- Writing a working variable keeps the fixed ones. -/
theorem BuildVals.assign {e : Env} {tree leaves count ctx zeros x : Nat} {v : UInt64}
    (r : BuildVals e tree leaves count ctx zeros) (hx : 5 ≤ x) :
    BuildVals (Asm.assign e x v) tree leaves count ctx zeros := by
  obtain ⟨a, b, c, d, f⟩ := r
  exact ⟨(assign_ne (by omega)).trans a, (assign_ne (by omega)).trans b, (assign_ne (by omega)).trans c,
    (assign_ne (by omega)).trans d, (assign_ne (by omega)).trans f⟩

/-- Fixed variables survive a copy loop that writes only working ones. -/
theorem BuildVals.agree {e0 e : Env} {tree leaves count ctx zeros I D S : Nat}
    (r : BuildVals e0 tree leaves count ctx zeros) (ag : Agree e0 e I D S) (hI : 5 ≤ I) (hD : 5 ≤ D) (hS : 5 ≤ S) :
    BuildVals e tree leaves count ctx zeros := by
  obtain ⟨a, b, c, d, f⟩ := r
  exact ⟨(ag 0 (by omega) (by omega) (by omega)).trans a, (ag 1 (by omega) (by omega) (by omega)).trans b,
    (ag 2 (by omega) (by omega) (by omega)).trans c, (ag 3 (by omega) (by omega) (by omega)).trans d,
    (ag 4 (by omega) (by omega) (by omega)).trans f⟩

/-- Memory as at the start, outside the tree buffer and the padding area. -/
def BuildFrame (mem mm : Memory) (tree K pad : Nat) : Prop :=
  ∀ a, ¬ (tree ≤ a ∧ a < tree + 64 * 2 ^ K) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm a = mem a

/-- The context still holds in memory changed only in the tree and the padding area. -/
theorem BuildPre.ctxAt {w : World} {mem mm : Memory} {tree leaves count K ctx table zeros pad : Nat} {mask : UInt64}
    (pre : BuildPre w mem tree leaves count K ctx table zeros pad mask) (fr : BuildFrame mem mm tree K pad) :
    StoreCtx w mm ctx table zeros pad mask := by
  have pc := pre.ctxOk.padCtx
  have ptab := pre.ctxOk.padTable
  have pz := pre.ctxOk.padZeros
  have tz := pre.treeZeros
  have tt := pre.treeTable
  have tc := pre.treeCtx
  simp only [Apart] at pc ptab pz tz tt tc
  exact pre.ctxOk.congr fun a ha => fr a (by omega) (by omega)

/--
The build loop's state at a height h: the level there has n nodes over data, and every level up to it is written.
-/
structure BuildLevel (mem mm : Memory) (arr : Array Bytes) (tree leaves count K ctx zeros pad : Nat) (e : Env)
    (h n : Nat) : Prop where
  /-- The fixed variables. -/
  vals : BuildVals e tree leaves count ctx zeros
  /-- The result so far. -/
  status : e 10 = 0
  /-- The level's width. -/
  widthV : e 5 = UInt64.ofNat (2 ^ (K - h))
  /-- Its nodes over data. -/
  liveV : e 6 = UInt64.ofNat n
  /-- Its height. -/
  heightV : e 8 = UInt64.ofNat h
  /-- No higher than the tree. -/
  height : h ≤ K
  /-- The nodes over data cover the leaves. -/
  covers : count ≤ n * 2 ^ h
  /-- They fit the level. -/
  fitsN : n ≤ 2 ^ (K - h)
  /-- Every level up to this one holds the subtrees' roots. -/
  nodes : ∀ g ≤ h, ∀ j < 2 ^ (K - g), nodeAt mm (tree + 32 * (2 ^ (K - g) + j)) = subtreeAt arr g (j * 2 ^ g)
  /-- Memory is as at the start, outside the tree and the padding area. -/
  frame : BuildFrame mem mm tree K pad

/-- A level of a tree of height K sits at or past its width in the heap, below twice it. -/
theorem level_bounds (K g : Nat) (hg : g ≤ K) : 1 ≤ 2 ^ (K - g) ∧ 2 ^ (K - g) ≤ 2 ^ K :=
  ⟨Nat.one_le_two_pow, Nat.pow_le_pow_right (by decide) (by omega)⟩

/-- A lower level sits past the levels above it in the heap. -/
theorem level_below (K g h : Nat) (hg : g ≤ h) : 2 ^ (K - h) ≤ 2 ^ (K - g) :=
  Nat.pow_le_pow_right (by decide) (by omega)

set_option maxHeartbeats 4000000 in
/-- One pass of the build loop writes the level one height up. -/
theorem build_level {m : Module} {w : World} {sp : Nat} {mem : Memory}
    {tree leaves count K ctx table zeros pad : Nat} {mask : UInt64} (okP : HashCalls m w .pairs)
    (pre : BuildPre w mem tree leaves count K ctx table zeros pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + hashStack ≤ sp)
    {arr : Array Bytes} (size : arr.size = count) {e : Env} {mm : Memory} {h n : Nat}
    (lv : BuildLevel mem mm arr tree leaves count K ctx zeros pad e h n) (below : h < K) :
    Ends m w sp e mm (.block TreeBuild.level) fun e' mm' =>
      BuildLevel mem mm' arr tree leaves count K ctx zeros pad e' (h + 1) ((n + 1) / 2) := by
  obtain ⟨v0, v1, v2, v3, v4⟩ := lv.vals
  have bt := access_bound pre.treeAccess
  have tr := pre.treeReach
  have tz := pre.treeZeros
  have tt := pre.treeTable
  have tc := pre.treeCtx
  have tp := pre.treePad
  simp only [Apart] at tz tt tc tp
  have hz : zeroHeights = 64 := rfl
  have narrow := pre.narrow
  have wK : 2 ^ K < 2 ^ 58 := Nat.pow_lt_pow_right (by decide) narrow
  have hb := level_bounds K h lv.height
  have hb1 := level_bounds K (h + 1) (by omega)
  -- The level's width is twice the next one's.
  have twice : 2 ^ (K - h) = 2 * 2 ^ (K - (h + 1)) := by
    rw [show K - h = (K - (h + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  generalize hs : 2 ^ (K - h) = s at twice hb
  generalize hf : 2 ^ (K - (h + 1)) = f at twice hb1
  have fitsN := lv.fitsN
  have covers := lv.covers
  rw [hs] at fitsN
  have upLe : (n + 1) / 2 ≤ f := by omega
  have ctxm := pre.ctxAt lv.frame
  -- The halved width, then the nodes over data one height up.
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_shr1' (eval_var (lv.widthV.trans (by rw [hs]))) (by omega))) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_shr1' (eval_add (eval_var ((assign_ne (by decide)).trans
    lv.liveV)) (eval_lit 1)) (by omega))) ?_
  rw [show s / 2 = f by omega]
  generalize hu : (n + 1) / 2 = u at upLe ⊢
  have cu : count ≤ u * 2 ^ (h + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ h) 2, ← Nat.mul_assoc, Nat.mul_comm u 2]
    exact Nat.le_trans covers (Nat.mul_le_mul_right _ (by omega))
  -- The environment after the two assignments.
  generalize he1 : Asm.assign (Asm.assign e 9 (UInt64.ofNat f)) 12 (UInt64.ofNat u) = e1
  have e1v : ∀ y, y ≠ 9 → y ≠ 12 → e1 y = e y := fun y a b => by
    rw [← he1, assign_ne b, assign_ne a]
  have e1f : e1 9 = UInt64.ofNat f := by rw [← he1, assign_ne (by decide), assign_eq]
  have e1u : e1 12 = UInt64.ofNat u := by rw [← he1, assign_eq]
  -- The pairs over data, hashed in one call, or nothing when there are none.
  refine Ends.cons (Q := fun e2 mm1 => (∀ y, y ≠ 11 → e2 y = e1 y) ∧ e2 10 = 0 ∧
      (∀ p < u, nodeAt mm1 (tree + 32 * (f + p)) = subtreeAt arr (h + 1) (p * 2 ^ (h + 1))) ∧
      ∀ a, ¬ (tree + 32 * f ≤ a ∧ a < tree + 32 * f + 32 * u) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm1 a = mm a)
    (Ends.when _ (eval_ne (eval_var e1u) (eval_lit 0)) (fun v => ?_) (fun v => ?_)) ?_
  · have u0 : u ≠ 0 := fun z => ite_ne_zero v (by rw [z])
    have run := StoreCtx.runPre (lo := tree + 32 * s) (len := 32 * s) (lo' := tree + 32 * s) (len' := 32 * s)
      (ls := 64) (rs := 64) (left := tree + 32 * s) (right := tree + 32 * s + 32) (n := u) (out := tree + 32 * f)
      ctxm (access_sub pre.treeAccess (by omega) (by omega)) (access_sub pre.treeAccess (by omega) (by omega))
      (access_sub pre.treeAccess (by omega) (by omega))
      (fun p hp => ⟨Or.inl ⟨by omega, by omega⟩, Or.inl ⟨by omega, by omega⟩⟩) ⟨by omega, by omega⟩
      (by simp only [Apart]; omega) (by simp only [Apart]; omega) (by simp only [Apart]; omega)
      (by simp only [Apart]; omega) (by simp only [Apart]; omega) (by simp only [Apart]; omega)
      (by simp only [Apart]; omega) (by simp only [Apart]; omega)
    have w5 : e1 5 = UInt64.ofNat s := (e1v 5 (by decide) (by decide)).trans (lv.widthV.trans (by rw [hs]))
    obtain ⟨mm1, r1, h1⟩ := hash_call (name := "ssz_hash_pairs") okP rfl rfl rfl run kernels room
      (eval_five (eval_add (eval_var ((e1v 0 (by decide) (by decide)).trans v0)) (eval_mul (eval_lit 32)
          (eval_var e1f)))
        (eval_add (eval_var ((e1v 0 (by decide) (by decide)).trans v0)) (eval_mul (eval_lit 32) (eval_var w5)))
        (eval_add (eval_add (eval_var ((e1v 0 (by decide) (by decide)).trans v0)) (eval_mul (eval_lit 32)
          (eval_var w5))) (eval_lit 32))
        (eval_var e1u) (eval_var ((e1v 3 (by decide) (by decide)).trans v3)))
    refine Ends.step r1 (Ends.of_runs (Runs.set _ _ _ _ _ _ _ _ (eval_or (eval_var ((assign_ne (by decide)).trans
      ((e1v 10 (by decide) (by decide)).trans lv.status))) (eval_var assign_eq)))
      ⟨fun y hy => ?_, rfl, fun p hp => ?_, fun a ha hp => ?_⟩)
    · by_cases y10 : y = 10
      · subst y10
        rw [assign_eq, ← he1, assign_ne (by decide), assign_ne (by decide), lv.status]
        rfl
      · rw [assign_ne y10, assign_ne hy]
    · -- A parent of two written nodes is the subtree one height up.
      rw [nodeAt_congr (m₂ := hashed mm (tree + 32 * f) (tree + 32 * s) (tree + 32 * s + 32) u 64 64)
        fun i hi => h1 _ (by omega), show tree + 32 * (f + p) = tree + 32 * f + 32 * p by omega,
        nodeAt_hashed _ _ _ _ _ _ _ _ hp, ← parent_pair,
        show tree + 32 * s + 64 * p = tree + 32 * (2 ^ (K - h) + 2 * p) by omega,
        show tree + 32 * s + 32 + 64 * p = tree + 32 * (2 ^ (K - h) + (2 * p + 1)) by omega,
        lv.nodes h (Nat.le_refl _) _ (by omega), lv.nodes h (Nat.le_refl _) _ (by omega)]
    · rw [h1 a hp, hashed_outside (by omega)]
  · exact ⟨fun y _ => rfl, (e1v 10 (by decide) (by decide)).trans lv.status, fun p hp => absurd hp (by
      have := ite_eq_zero v
      have := (ofNat_inj (show u < 2 ^ 64 by omega) (show 0 < 2 ^ 64 by decide)).mp this
      omega), fun _ _ _ => rfl⟩
  rintro e2 mm1 ⟨e2v, st2, hashedNodes, fr1⟩
  have e2h : e2 8 = UInt64.ofNat h := (e2v 8 (by decide)).trans ((e1v 8 (by decide) (by decide)).trans lv.heightV)
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_add (eval_var e2h) (eval_lit 1))) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_var ((assign_ne (by decide)).trans ((e2v 12 (by decide)).trans
    e1u)))) ?_
  generalize he3 : Asm.assign (Asm.assign e2 8 (UInt64.ofNat (h + 1))) 7 (UInt64.ofNat u) = e3
  have e3v : ∀ y, y ≠ 7 → y ≠ 8 → y ≠ 11 → e3 y = e1 y := fun y a b c => by
    rw [← he3, assign_ne a, assign_ne b, e2v y c]
  have e3h : e3 8 = UInt64.ofNat (h + 1) := by rw [← he3, assign_ne (by decide), assign_eq]
  have e3i : e3 7 = UInt64.ofNat u := by rw [← he3, assign_eq]
  -- The rest of the level is the zero tree of its height.
  have zr := (pre.ctxAt (mm := mm1) fun a ha hp => by
    rw [fr1 a (by omega) hp]; exact lv.frame a ha hp).zeroAt (h + 1) (by omega)
  refine Ends.cons (copy_loop (I := 7) (D := 13) (S := 14) (i0 := u) (n := f) (fun i => tree + 32 * f + 32 * i)
    (fun _ => zeros + 32 * (h + 1)) (by decide) (by decide) (by decide)
    (fun e' mm' ag => eval_var ((ag 9 (by decide) (by decide) (by decide)).trans
      ((e3v 9 (by decide) (by decide) (by decide)).trans e1f)))
    (fun e' mm' i ag iv _ _ _ => eval_add (eval_add (eval_var ((ag 0 (by decide) (by decide) (by decide)).trans
      ((e3v 0 (by decide) (by decide) (by decide)).trans ((e1v 0 (by decide) (by decide)).trans v0))))
      (eval_mul (eval_lit 32) (eval_var ((ag 9 (by decide) (by decide) (by decide)).trans
        ((e3v 9 (by decide) (by decide) (by decide)).trans e1f))))) (eval_mul (eval_lit 32) (eval_var iv)))
    (fun e' mm' i ag _ _ _ _ => eval_add (eval_var ((ag 4 (by decide) (by decide) (by decide)).trans
      ((e3v 4 (by decide) (by decide) (by decide)).trans ((e1v 4 (by decide) (by decide)).trans v4))))
      (eval_mul (eval_lit 32) (eval_var ((ag 8 (by decide) (by decide) (by decide)).trans e3h))))
    e3i upLe (by omega)
    (fun i _ hi => access_sub pre.treeAccess (by omega) (by omega))
    (fun i _ _ => access_sub pre.ctxOk.zerosAccess (by omega) (by omega))
    (fun i j _ _ _ _ => by simp only [Apart]; omega) (fun i j _ _ _ => by simp only [Apart]; omega)) ?_
  rintro e4 mm2 ⟨ag4, i4, filled, kept⟩
  have e4v : ∀ y, y ≠ 7 → y ≠ 8 → y ≠ 11 → y ≠ 13 → y ≠ 14 → e4 y = e1 y := fun y a b c d f' =>
    (ag4 y a d f').trans (e3v y a b c)
  -- The width and the nodes over data move up.
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_var ((e4v 9 (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans e1f))) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_var ((assign_ne (by decide)).trans ((e4v 12 (by decide)
    (by decide) (by decide) (by decide) (by decide)).trans e1u)))) (Ends.nil ?_)
  -- Memory outside the new level is as before the pass.
  have same : ∀ a, ¬ (tree + 32 * f ≤ a ∧ a < tree + 32 * f + 32 * f) → ¬ (pad ≤ a ∧ a < pad + 1536) →
      mm2 a = mm a := fun a ha hp => by
    rw [kept a fun i _ hi => show ¬ (tree + 32 * f + 32 * i ≤ a ∧ a < tree + 32 * f + 32 * i + 32) by omega,
      fr1 a (by omega) hp]
  have eq4 : ∀ y, y < 5 → Asm.assign (Asm.assign e4 5 (UInt64.ofNat f)) 6 (UInt64.ofNat u) y = e y := fun y hy => by
    rw [assign_ne (by omega), assign_ne (by omega), e4v y (by omega) (by omega) (by omega) (by omega) (by omega),
      e1v y (by omega) (by omega)]
  refine ⟨⟨(eq4 0 (by decide)).trans v0, (eq4 1 (by decide)).trans v1, (eq4 2 (by decide)).trans v2,
    (eq4 3 (by decide)).trans v3, (eq4 4 (by decide)).trans v4⟩, ?_, ?_, assign_eq, ?_, by omega, cu,
    by rw [hf]; exact upLe, fun g hg j hj => ?_, fun a ha hp => ?_⟩
  · rw [assign_ne (by decide), assign_ne (by decide), e4v 10 (by decide) (by decide) (by decide) (by decide)
      (by decide), e1v 10 (by decide) (by decide)]
    exact lv.status
  · rw [assign_ne (by decide), assign_eq, hf]
  · rw [assign_ne (by decide), assign_ne (by decide), ag4 8 (by decide) (by decide) (by decide)]
    exact e3h
  · by_cases top : g = h + 1
    · subst top
      rw [hf] at hj ⊢
      by_cases low : j < u
      · rw [nodeAt_congr (m₂ := mm1) fun q hq => kept _ fun i hi _ =>
          show ¬ (tree + 32 * f + 32 * i ≤ _ ∧ _ < tree + 32 * f + 32 * i + 32) by omega]
        exact hashedNodes j low
      · rw [show tree + 32 * (f + j) = tree + 32 * f + 32 * j by omega, filled j (by omega) hj, zr,
          subtreeAt_past _ _ _ (by rw [size]; exact Nat.le_trans cu (Nat.mul_le_mul_right _ (by omega)))]
    · have lb := level_below K g h (by omega)
      have gb := level_bounds K g (by omega)
      rw [hs] at lb
      rw [nodeAt_congr (m₂ := mm) fun q hq => same _ (by omega) (by omega)]
      exact lv.nodes g (by omega) j hj
  · rw [same a (by omega) hp]
    exact lv.frame a ha hp

set_option maxHeartbeats 4000000 in
/--
The build driver ends with the whole tree over the leaves in memory, and a zero result.

Memory changes only in the tree buffer and the padding area.
-/
theorem build_ends {m : Module} {w : World} {sp : Nat} {mem : Memory}
    {tree leaves count K ctx table zeros pad : Nat} {mask : UInt64} (okP : HashCalls m w .pairs)
    (pre : BuildPre w mem tree leaves count K ctx table zeros pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + hashStack ≤ sp) :
    Ends m w sp (entryEnv [UInt64.ofNat tree, UInt64.ofNat leaves, UInt64.ofNat count, UInt64.ofNat ctx]) mem
      TreeBuild.fn.body fun env mem' =>
        env 10 = 0 ∧ TreeAt mem' tree K (nodesFrom (bytesAt mem leaves (32 * count)) 0 count) ∧
        BuildFrame mem mem' tree K pad := by
  have bt := access_bound pre.treeAccess
  have bx := access_bound pre.ctxOk.ctxAccess
  have tr := pre.treeReach
  have tz := pre.treeZeros
  have tt := pre.treeTable
  have tc := pre.treeCtx
  have tp := pre.treePad
  simp only [Apart] at tz tt tc tp
  have hz : zeroHeights = 64 := rfl
  have narrow := pre.narrow
  have covers := pre.covers
  have wK : 2 ^ K < 2 ^ 58 := Nat.pow_lt_pow_right (by decide) narrow
  have one : 1 ≤ 2 ^ K := Nat.one_le_two_pow
  -- The leaves are the nodes read from memory at the start.
  have leaf : ∀ j < count, subtreeAt (nodesFrom (bytesAt mem leaves (32 * count)) 0 count) 0 j =
      nodeAt mem (leaves + 32 * j) := fun j hj => by
    rw [subtreeAt_leaf, nodesFrom_get?, ite_eq_left hj, Option.getD_some, nodeOf_bytesAt _ _ _ _ hj]
  have size : (nodesFrom (bytesAt mem leaves (32 * count)) 0 count).size = count := nodesFrom_size _ _ _
  generalize nodesFrom (bytesAt mem leaves (32 * count)) 0 count = arr at leaf size ⊢
  simp only [TreeBuild.fn]
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ ((eval_ld (eval_add (eval_var rfl) (eval_lit 16))
    (access_sub pre.ctxOk.ctxAccess (by omega) (by omega))).trans (congrArg some pre.ctxOk.zerosAt))) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 0)) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 1)) ?_
  -- The width: doubled until it holds the leaves.
  refine Ends.cons (Ends.loop (fun e mm => mem = mm ∧ BuildVals e tree leaves count ctx zeros ∧ e 10 = 0 ∧
      ∃ k ≤ K, e 5 = UInt64.ofNat (2 ^ k)) (fun e _ => 2 ^ K - (e 5).toNat)
    ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, 0, Nat.zero_le _, rfl⟩ ?_ ?_) ?_
  · rintro e mm ⟨_, vs, _, k, hk, kv⟩
    have : 2 ^ k ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) hk
    exact ⟨_, eval_lt (eval_var kv) (eval_var vs.2.2.1) (by omega) (by omega)⟩
  · rintro e mm v ⟨rfl, vs, st, k, hk, kv⟩ hv nz
    have : 2 ^ k ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) hk
    have hv := Option.some.inj (hv.symm.trans (eval_lt (eval_var kv) (eval_var vs.2.2.1) (by omega) (by omega)))
    have lt : 2 ^ k < count := by
      by_cases hb : 2 ^ k < count
      · exact hb
      · rw [ite_eq_right hb] at hv; exact absurd hv nz
    have kK : k < K := by
      by_cases hb : k < K
      · exact hb
      · have : k = K := by omega
        subst this; omega
    have up : 2 ^ (k + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) kK
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_add (eval_var kv) (eval_var kv))) (Ends.nil ⟨⟨rfl,
      vs.assign (by decide), (assign_ne (by decide)).trans st, k + 1, kK,
      by rw [assign_eq, Nat.pow_succ]; congr 1; omega⟩, ?_⟩)
    rw [assign_eq, kv, ofNat_toNat (by omega), ofNat_toNat (by omega)]
    have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega
  rintro e1 mm1 ⟨⟨rfl, vs1, st1, k, hk, kv⟩, done⟩
  have : 2 ^ k ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) hk
  have done := Option.some.inj (done.symm.trans (eval_lt (eval_var kv) (eval_var vs1.2.2.1) (by omega) (by omega)))
  have kK : k = K := by
    by_cases hb : k < K
    · rw [ite_eq_left (pre.least k hb)] at done; exact absurd done (by decide)
    · omega
  rw [kK] at kv
  obtain ⟨v0, v1, v2, v3, v4⟩ := vs1
  generalize hW : 2 ^ K = W at kv one wK covers tz tt tc tp bt tr
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 0)) ?_
  -- The leaves, copied in unless they are already in place.
  refine Ends.cons (Q := fun e mm => BuildVals e tree leaves count ctx zeros ∧ e 10 = 0 ∧ e 5 = UInt64.ofNat W ∧
      (∀ j < count, nodeAt mm (tree + 32 * W + 32 * j) = nodeAt mem (leaves + 32 * j)) ∧
      ∀ a, ¬ (tree + 32 * W ≤ a ∧ a < tree + 32 * W + 32 * count) → mm a = mem a)
    (Ends.when _ (eval_ne (eval_var ((assign_ne (by decide)).trans v1)) (eval_add (eval_var ((assign_ne
      (by decide)).trans v0)) (eval_mul (eval_lit 32) (eval_var ((assign_ne (by decide)).trans kv)))))
      (fun v => ?_) (fun v => ?_)) ?_
  · have apartL : w.access leaves (32 * count) = true ∧ Apart (leaves, 32 * count) (tree, 64 * W) := by
      rcases pre.leavesOk with eq | ok
      · exact absurd (ite_ne_zero v) (by rw [eq, hW]; exact fun h => h rfl)
      · rw [← hW]; exact ok
    obtain ⟨la, lap⟩ := apartL
    have bl := access_bound la
    simp only [Apart] at lap
    refine Ends.mono (copy_loop (I := 7) (D := 13) (S := 14) (i0 := 0) (n := count)
      (fun i => tree + 32 * W + 32 * i) (fun i => leaves + 32 * i) (by decide) (by decide) (by decide)
      (fun e mm ag => eval_var ((ag 2 (by decide) (by decide) (by decide)).trans ((assign_ne (by decide)).trans v2)))
      (fun e mm i ag iv _ _ _ => eval_add (eval_add (eval_var ((ag 0 (by decide) (by decide) (by decide)).trans
        ((assign_ne (by decide)).trans v0))) (eval_mul (eval_lit 32) (eval_var ((ag 5 (by decide) (by decide)
          (by decide)).trans ((assign_ne (by decide)).trans kv))))) (eval_mul (eval_lit 32) (eval_var iv)))
      (fun e mm i ag iv _ _ _ => eval_add (eval_var ((ag 1 (by decide) (by decide) (by decide)).trans
        ((assign_ne (by decide)).trans v1))) (eval_mul (eval_lit 32) (eval_var iv)))
      assign_eq (Nat.zero_le _) (by omega)
      (fun i _ hi => access_sub pre.treeAccess (by omega) (by omega))
      (fun i _ hi => access_sub la (by omega) (by omega))
      (fun i j _ _ _ _ => by simp only [Apart]; omega) (fun i j _ _ _ => by simp only [Apart]; omega))
      fun e mm ⟨ag, _, filled, kept⟩ => ⟨BuildVals.agree (BuildVals.assign ⟨v0, v1, v2, v3, v4⟩ (by decide)) ag
        (by decide) (by decide) (by decide), (ag 10 (by decide) (by decide) (by decide)).trans ((assign_ne
          (by decide)).trans st1), (ag 5 (by decide) (by decide) (by decide)).trans ((assign_ne (by decide)).trans kv),
        fun j hj => filled j (Nat.zero_le _) hj, fun a ha => kept a fun i _ hi =>
          show ¬ (tree + 32 * W + 32 * i ≤ a ∧ a < tree + 32 * W + 32 * i + 32) by omega⟩
  · have eq : leaves = tree + 32 * W := by
      rcases pre.leavesOk with eq | ⟨la, _⟩
      · rw [← hW]; exact eq
      · have bl := access_bound la
        exact (ofNat_inj (by omega) (by omega)).mp (ite_eq_zero v)
    exact ⟨BuildVals.assign ⟨v0, v1, v2, v3, v4⟩ (by decide), (assign_ne (by decide)).trans st1,
      (assign_ne (by decide)).trans kv, fun j _ => by rw [eq], fun _ _ => rfl⟩
  rintro e2 mm2 ⟨vs2, st2, w2, copiedIn, fr2⟩
  obtain ⟨u0, u1, u2, u3, u4⟩ := vs2
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_var u2)) ?_
  -- The rest of the leaf level is zero nodes.
  have frame2 : BuildFrame mem mm2 tree K pad := fun a ha _ => fr2 a (by rw [hW] at ha; omega)
  have z0 := (pre.ctxAt frame2).zeroAt 0 (by omega)
  rw [Nat.mul_zero, Nat.add_zero] at z0
  refine Ends.cons (copy_loop (I := 7) (D := 13) (S := 14) (i0 := count) (n := W)
    (fun i => tree + 32 * W + 32 * i) (fun _ => zeros) (by decide) (by decide) (by decide)
    (fun e mm ag => eval_var ((ag 5 (by decide) (by decide) (by decide)).trans ((assign_ne (by decide)).trans w2)))
    (fun e mm i ag iv _ _ _ => eval_add (eval_add (eval_var ((ag 0 (by decide) (by decide) (by decide)).trans
      ((assign_ne (by decide)).trans u0))) (eval_mul (eval_lit 32) (eval_var ((ag 5 (by decide) (by decide)
        (by decide)).trans ((assign_ne (by decide)).trans w2))))) (eval_mul (eval_lit 32) (eval_var iv)))
    (fun e mm i ag _ _ _ _ => eval_var ((ag 4 (by decide) (by decide) (by decide)).trans ((assign_ne
      (by decide)).trans u4)))
    assign_eq covers (by omega)
    (fun i _ hi => access_sub pre.treeAccess (by omega) (by omega))
    (fun i _ _ => access_sub pre.ctxOk.zerosAccess (by omega) (by omega))
    (fun i j _ _ _ _ => by simp only [Apart]; omega) (fun i j _ _ _ => by simp only [Apart]; omega)) ?_
  rintro e3 mm3 ⟨ag3, _, filled, kept⟩
  have e3v : ∀ y, y ≠ 7 → y ≠ 13 → y ≠ 14 → e3 y = e2 y := fun y a b c => by
    rw [ag3 y a b c, assign_ne a]
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_var ((e3v 2 (by decide) (by decide) (by decide)).trans u2))) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 0)) ?_
  -- The levels, one height up per pass.
  have e4 : ∀ y, y < 5 ∨ y = 10 ∨ y = 5 →
      Asm.assign (Asm.assign e3 6 (UInt64.ofNat count)) 8 (UInt64.ofNat 0) y = e2 y := fun y hy => by
    rw [assign_ne (by omega), assign_ne (by omega), e3v y (by omega) (by omega) (by omega)]
  have frame3 : BuildFrame mem mm3 tree K pad := fun a ha hp => by
    rw [kept a fun i _ hi => show ¬ (tree + 32 * W + 32 * i ≤ a ∧ a < tree + 32 * W + 32 * i + 32) by
      rw [hW] at ha; omega]
    exact frame2 a ha hp
  refine Ends.cons (Ends.loop (fun e mm => ∃ h n, BuildLevel mem mm arr tree leaves count K ctx zeros pad e h n)
    (fun e _ => K - (e 8).toNat)
    ⟨0, count, ⟨⟨(e4 0 (by omega)).trans u0, (e4 1 (by omega)).trans u1, (e4 2 (by omega)).trans u2,
      (e4 3 (by omega)).trans u3, (e4 4 (by omega)).trans u4⟩, (e4 10 (by omega)).trans st2,
      by rw [e4 5 (by omega), w2, Nat.sub_zero, hW], by rw [assign_ne (by decide), assign_eq], assign_eq,
      Nat.zero_le _, by simp, by rw [Nat.sub_zero, hW]; exact covers, fun g hg j hj => ?_, frame3⟩⟩ ?_ ?_) ?_
  · obtain rfl : g = 0 := by omega
    rw [Nat.sub_zero, hW] at hj ⊢
    rw [Nat.pow_zero, Nat.mul_one, show tree + 32 * (W + j) = tree + 32 * W + 32 * j by omega]
    by_cases low : j < count
    · rw [nodeAt_congr (m₂ := mm2) fun q hq => kept _ fun i hi _ =>
        show ¬ (tree + 32 * W + 32 * i ≤ _ ∧ _ < tree + 32 * W + 32 * i + 32) by omega, copiedIn j low, leaf j low]
    · rw [filled j (by omega) hj, z0, subtreeAt_past _ _ _ (by omega)]
  · rintro e mm ⟨h, n, lv⟩
    have := level_bounds K h lv.height
    exact ⟨_, eval_lt (eval_lit 1) (eval_var lv.widthV) (by decide) (by omega)⟩
  · rintro e mm v ⟨h, n, lv⟩ hv nz
    have := level_bounds K h lv.height
    have hv := Option.some.inj (hv.symm.trans (eval_lt (eval_lit 1) (eval_var lv.widthV) (by decide) (by omega)))
    have below : h < K := by
      by_cases hb : 1 < 2 ^ (K - h)
      · by_cases hk : h < K
        · exact hk
        · rw [show K - h = 0 by omega] at hb; exact absurd hb (by decide)
      · rw [ite_eq_right hb] at hv; exact absurd hv nz
    refine Ends.mono (build_level okP pre kernels room size lv below) fun e' mm' lv' => ⟨⟨_, _, lv'⟩, ?_⟩
    rw [lv'.heightV, lv.heightV, ofNat_toNat (by omega), ofNat_toNat (by omega)]
    omega
  rintro e mm ⟨⟨h, n, lv⟩, done⟩
  have := level_bounds K h lv.height
  have done := Option.some.inj (done.symm.trans (eval_lt (eval_lit 1) (eval_var lv.widthV) (by decide) (by omega)))
  have hK : h = K := by
    by_cases hk : h < K
    · rw [ite_eq_left (Nat.one_lt_two_pow (by omega))] at done; exact absurd done (by decide)
    · exact Nat.le_antisymm lv.height (by omega)
  subst hK
  exact Ends.nil ⟨lv.status, fun g hg j hj => lv.nodes g hg j hj, lv.frame⟩

end EthLib.Consensus.Ssz.Native.Driver
