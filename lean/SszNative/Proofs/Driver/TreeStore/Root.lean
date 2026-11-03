import SszNative.Proofs.Driver.TreeStore.Basic

/-!
The root driver writes the root of a stored tree at the declared depth, with a word mixed in or not.

It copies the stored top out, counts the tree's height by halving the width, then climbs one height per pass
against the zero tree of that height.
Each hash lands in the tree's first 32 bytes, which hold no node, and is copied back to the output.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir

/-- A root, with a word hashed in as its right sibling, or alone. -/
def withMixin (root : Bytes) (word : Option Bytes) : Bytes :=
  match word with
  | none => root
  | some w => mixIn root w

/--
What the root driver needs: its context, the tree's first two nodes, an output, and the word to mix in.

The tree's first 32 bytes hold no node, and the driver overwrites them.
-/
structure RootPre (w : World) (mem : Memory) (tree K depth mixin out ctx table zeros pad : Nat) (mask : UInt64) :
    Prop where
  /-- The context, its tables, and the padding area. -/
  ctxOk : StoreCtx w mem ctx table zeros pad mask
  /-- The depth has a zero tree in the table. -/
  deep : depth ≤ zeroHeights
  /-- The tree fits the depth. -/
  tall : K ≤ depth
  /-- Its width fits a word. -/
  narrow : K < 63
  /-- The tree's first two nodes lie in memory the program may use. -/
  treeAccess : w.access tree 64 = true
  /-- So does the output. -/
  outAccess : w.access out 32 = true
  /-- So does the word to mix in, if any. -/
  mixinAccess : mixin ≠ 0 → w.access mixin 32 = true
  /-- The tree's first two nodes miss the output. -/
  treeOut : Apart (tree, 64) (out, 32)
  /-- The first misses the zero-tree roots. -/
  treeZeros : Apart (tree, 32) (zeros, 32 * (zeroHeights + 1))
  /-- It misses the constant table. -/
  treeTable : Apart (tree, 32) (table, Kernel.tableSize)
  /-- It misses the context. -/
  treeCtx : Apart (ctx, 32) (tree, 32)
  /-- It misses the padding area. -/
  treePad : Apart (pad, 1536) (tree, 32)
  /-- The output misses the zero-tree roots. -/
  outZeros : Apart (out, 32) (zeros, 32 * (zeroHeights + 1))
  /-- It misses the constant table. -/
  outTable : Apart (out, 32) (table, Kernel.tableSize)
  /-- It misses the context. -/
  outCtx : Apart (ctx, 32) (out, 32)
  /-- It misses the padding area. -/
  outPad : Apart (pad, 1536) (out, 32)
  /-- The word to mix in misses the tree's first node. -/
  mixinTree : mixin ≠ 0 → Apart (tree, 32) (mixin, 32)
  /-- It misses the output. -/
  mixinOut : mixin ≠ 0 → Apart (out, 32) (mixin, 32)
  /-- It misses the padding area. -/
  mixinPad : mixin ≠ 0 → Apart (pad, 1536) (mixin, 32)

/-- The root driver's variables that never change. -/
def RootVals (e : Env) (tree depth mixin out ctx zeros : Nat) : Prop :=
  e 0 = UInt64.ofNat tree ∧ e 2 = UInt64.ofNat depth ∧ e 3 = UInt64.ofNat mixin ∧ e 4 = UInt64.ofNat out ∧
    e 5 = UInt64.ofNat ctx ∧ e 6 = UInt64.ofNat zeros

/-- Writing a working variable keeps the fixed ones. -/
theorem RootVals.assign {e : Env} {tree depth mixin out ctx zeros x : Nat} {v : UInt64}
    (r : RootVals e tree depth mixin out ctx zeros) (hx : 7 ≤ x) :
    RootVals (Asm.assign e x v) tree depth mixin out ctx zeros := by
  obtain ⟨a, b, c, d, f, g⟩ := r
  exact ⟨(assign_ne (by omega)).trans a, (assign_ne (by omega)).trans b, (assign_ne (by omega)).trans c,
    (assign_ne (by omega)).trans d, (assign_ne (by omega)).trans f, (assign_ne (by omega)).trans g⟩

/-- Memory as at the start, outside the tree's first node, the output, and the padding area. -/
def RootFrame (mem mm : Memory) (tree out pad : Nat) : Prop :=
  ∀ a, ¬ (tree ≤ a ∧ a < tree + 32) → ¬ (out ≤ a ∧ a < out + 32) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm a = mem a

set_option maxHeartbeats 1000000 in
/--
One hash of the output against a node, into the tree's first node, copied back to the output.

The node is a zero-tree root or the word to mix in, and the output ends as the two combined.
-/
theorem root_hash_back {m : Module} {w : World} {sp : Nat} {mem : Memory}
    {tree K depth mixin out ctx table zeros pad : Nat} {mask : UInt64} (okF : HashCalls m w .fixed)
    (pre : RootPre w mem tree K depth mixin out ctx table zeros pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + hashStack ≤ sp)
    {e : Env} {mm : Memory} (vals : RootVals e tree depth mixin out ctx zeros) (st : e 9 = 0)
    (frame : RootFrame mem mm tree out pad) {right : Expr} {r : Nat}
    (hr : eval w e mm right = some (UInt64.ofNat r))
    (rightOk : (zeros ≤ r ∧ r + 32 ≤ zeros + 32 * (zeroHeights + 1)) ∨
      (mixin ≠ 0 ∧ r = mixin)) :
    Ends m w sp e mm (.block ([Stmt.callInto ⟨10⟩ "ssz_hash_fixed" [Expr.var 0, Expr.var 4, right, 1, Expr.var 5],
      Stmt.assign ⟨9⟩ (Expr.var 9 ||| Expr.var 10)] ++ copy32 (Expr.var 4) (Expr.var 0)))
      fun e' mm' => RootVals e' tree depth mixin out ctx zeros ∧ e' 9 = 0 ∧ e' 7 = e 7 ∧
        nodeAt mm' out = combine (nodeAt mm out) (nodeAt mm r) ∧ RootFrame mem mm' tree out pad := by
  obtain ⟨v0, v2, v3, v4, v5, v6⟩ := vals
  have to := pre.treeOut
  have tz := pre.treeZeros
  have tt := pre.treeTable
  have tc := pre.treeCtx
  have tp := pre.treePad
  have oz := pre.outZeros
  have ot := pre.outTable
  have oc := pre.outCtx
  have op := pre.outPad
  have pc := pre.ctxOk.padCtx
  have ptab := pre.ctxOk.padTable
  have pz := pre.ctxOk.padZeros
  simp only [Apart] at to tz tt tc tp oz ot oc op pc ptab pz
  have bt := access_bound pre.treeAccess
  have bo := access_bound pre.outAccess
  have bz := access_bound pre.ctxOk.zerosAccess
  have hz : zeroHeights = 64 := rfl
  -- The context still holds: none of its bytes was written.
  have c := pre.ctxOk.congr (mm := mm) fun a ha => frame a (by omega) (by omega) (by omega)
  -- The word to mix in, when it is the node, sits apart from all the call writes.
  have mixApart : mixin ≠ 0 → mixin + 32 ≤ 2 ^ 63 ∧ (tree + 32 ≤ mixin ∨ mixin + 32 ≤ tree) ∧
      (out + 32 ≤ mixin ∨ mixin + 32 ≤ out) ∧ (pad + 1536 ≤ mixin ∨ mixin + 32 ≤ pad) := fun nz => by
    have := pre.mixinTree nz
    have := pre.mixinOut nz
    have := pre.mixinPad nz
    have := access_bound (pre.mixinAccess nz)
    simp only [Apart] at *
    omega
  have rr : r + 32 ≤ 2 ^ 63 := by
    rcases rightOk with h | ⟨nz, rfl⟩
    · omega
    · exact (mixApart nz).1
  -- The node read on the right: a zero root, or the word to mix in.
  have rAcc : w.access r 32 = true := by
    rcases rightOk with h | ⟨nz, rfl⟩
    · exact access_sub pre.ctxOk.zerosAccess (by omega) (by omega)
    · exact pre.mixinAccess nz
  have rApart : (tree + 32 ≤ r ∨ r + 32 ≤ tree) ∧ (pad + 1536 ≤ r ∨ r + 32 ≤ pad) := by
    rcases rightOk with h | ⟨nz, rfl⟩
    · omega
    · have := mixApart nz; omega
  have run := StoreCtx.runPre (lo := out) (len := 32) (lo' := r) (len' := 32) (ls := 32) (rs := 0) (left := out)
    (right := r) (n := 1) (out := tree) c pre.outAccess rAcc (access_sub pre.treeAccess (by omega) (by omega))
    (fun p hp => ⟨Or.inl ⟨by omega, by omega⟩, Or.inr (Or.inl ⟨by omega, by omega⟩)⟩)
    (by omega) (by simp only [Apart]; omega) (by simp only [Apart]; omega)
    (by simp only [Apart]; omega) (by simp only [Apart]; omega) (by simp only [Apart]; omega)
    (by simp only [Apart]; omega) (by simp only [Apart]; omega) (by simp only [Apart]; omega)
  obtain ⟨mm1, r1, h1⟩ := hash_call (name := "ssz_hash_fixed") okF rfl rfl rfl run kernels room
    (eval_five (eval_var v0) (eval_var v4) hr (eval_lit 1) (eval_var v5))
  have node1 : nodeAt mm1 tree = combine (nodeAt mm out) (nodeAt mm r) := by
    have e := nodeAt_hashed mm tree out r 1 32 0 0 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at e
    rw [nodeAt_congr (m₂ := hashed mm tree out r 1 32 0) fun i hi => h1 _ (by omega), e]
  refine Ends.append (Q := fun e' mm' => e' = Asm.assign (Asm.assign e 10 0) 9 (0 ||| 0) ∧ mm' = mm1)
    (Ends.step r1 (Ends.step (Runs.set _ _ _ _ _ _ _ _
      (eval_or (eval_var ((assign_ne (by decide)).trans st)) (eval_var assign_eq))) (Ends.nil ⟨rfl, rfl⟩))) ?_
  rintro e1 mm2 ⟨rfl, rfl⟩
  -- Copying back to the output.
  refine Ends.of_runs (copy32_runs (fun _ => eval_var ((assign_ne (by decide)).trans ((assign_ne (by decide)).trans v4)))
    (fun _ => eval_var ((assign_ne (by decide)).trans ((assign_ne (by decide)).trans v0))) pre.outAccess
    (access_sub pre.treeAccess (by omega) (by omega)) (by simp only [Apart]; omega))
    ⟨(RootVals.assign (RootVals.assign ⟨v0, v2, v3, v4, v5, v6⟩ (by decide)) (by decide)), rfl,
      (assign_ne (by decide)).trans (assign_ne (by decide)), ?_, fun a ht ho hp => ?_⟩
  · rw [nodeAt_copied, node1]
  · rw [copied_out ho, h1 a hp, hashed_outside (by omega)]
    exact frame a ht ho hp

set_option maxHeartbeats 2000000 in
/--
The root driver ends with the root of the tree at the depth, mixed with the word if one is given, and a zero result.

Memory changes only in the tree's first node, the output, and the padding area.
-/
theorem root_ends {m : Module} {w : World} {sp : Nat} {mem : Memory}
    {tree K depth mixin out ctx table zeros pad : Nat} {mask : UInt64} (okF : HashCalls m w .fixed)
    (pre : RootPre w mem tree K depth mixin out ctx table zeros pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + hashStack ≤ sp)
    {leaves : Array Bytes} (top : nodeAt mem (tree + 32) = subtreeAt leaves K 0) (fits : leaves.size ≤ 2 ^ K) :
    Ends m w sp (entryEnv [UInt64.ofNat tree, UInt64.ofNat (2 ^ K), UInt64.ofNat depth, UInt64.ofNat mixin,
      UInt64.ofNat out, UInt64.ofNat ctx]) mem TreeRoot.fn.body fun env mem' =>
        env 9 = 0 ∧ nodeAt mem' out =
          withMixin (subtreeAt leaves depth 0) (if mixin = 0 then none else some (nodeAt mem mixin)) ∧
        RootFrame mem mem' tree out pad := by
  have bt := access_bound pre.treeAccess
  have bo := access_bound pre.outAccess
  have bx := access_bound pre.ctxOk.ctxAccess
  have to := pre.treeOut
  simp only [Apart] at to
  have hz : zeroHeights = 64 := rfl
  have deep := pre.deep
  have tall := pre.tall
  have narrow := pre.narrow
  have wideK : 2 ^ K < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  simp only [TreeRoot.fn]
  refine Ends.append (Q := fun e mm => RootVals e tree depth mixin out ctx zeros ∧ e 1 = UInt64.ofNat (2 ^ K) ∧
      e 9 = 0 ∧ nodeAt mm out = subtreeAt leaves K 0 ∧ RootFrame mem mm tree out pad) ?_ ?_
  · -- The zero roots' address, a zero result, and the stored top copied out.
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ ((eval_ld (eval_add (eval_var rfl) (eval_lit 16))
      (access_sub pre.ctxOk.ctxAccess (by omega) (by omega))).trans (congrArg some pre.ctxOk.zerosAt))) ?_
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 0)) ?_
    exact Ends.of_runs (copy32_runs (fun _ => eval_var (x := 4) (v := UInt64.ofNat out) rfl)
      (fun _ => eval_add (eval_var (x := 0) (v := UInt64.ofNat tree) rfl) (eval_lit 32)) pre.outAccess
      (access_sub pre.treeAccess (by omega) (by omega)) (by simp only [Apart]; omega))
      ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by rw [nodeAt_copied, top], fun a _ ho _ => copied_out ho⟩
  rintro e mm ⟨vals, wv, st, node, frame⟩
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 0)) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_var ((assign_ne (by decide)).trans wv))) ?_
  -- The tree's height, counted by halving its width down to one.
  refine Ends.cons (Ends.loop (fun e' mm' => mm' = mm ∧ RootVals e' tree depth mixin out ctx zeros ∧ e' 9 = 0 ∧
      ∃ g ≤ K, e' 7 = UInt64.ofNat g ∧ e' 8 = UInt64.ofNat (2 ^ (K - g)))
    (fun e' _ => K - (e' 7).toNat)
    ⟨rfl, (vals.assign (by decide)).assign (by decide),
      (assign_ne (by decide)).trans ((assign_ne (by decide)).trans st), 0, Nat.zero_le _,
      (assign_ne (by decide)).trans assign_eq, by rw [Nat.sub_zero]; exact assign_eq⟩ ?_ ?_) ?_
  · rintro e' mm' ⟨_, _, _, g, hg, gv, sv⟩
    have : 2 ^ (K - g) ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) (by omega)
    exact ⟨_, eval_lt (eval_lit 1) (eval_var sv) (by decide) (by omega)⟩
  · rintro e' mm' v ⟨rfl, vs, st', g, hg, gv, sv⟩ hv nz
    have : 2 ^ (K - g) ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) (by omega)
    have hv := Option.some.inj (hv.symm.trans (eval_lt (eval_lit 1) (eval_var sv) (by decide) (by omega)))
    have below : g < K := by
      by_cases hb : 1 < 2 ^ (K - g)
      · by_cases hk : g < K
        · exact hk
        · rw [show K - g = 0 by omega] at hb; exact absurd hb (by decide)
      · rw [ite_eq_right hb] at hv; exact absurd hv nz
    have half : 2 ^ (K - g) / 2 = 2 ^ (K - (g + 1)) := by
      rw [show K - g = (K - (g + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by decide)]
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_shr1' (eval_var sv) (by omega))) ?_
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_add (eval_var ((assign_ne (by decide)).trans gv))
      (eval_lit 1))) ?_
    refine Ends.nil ⟨⟨rfl, (vs.assign (by decide)).assign (by decide),
      (assign_ne (by decide)).trans ((assign_ne (by decide)).trans st'), g + 1, by omega, assign_eq,
      by rw [assign_ne (by decide), assign_eq, half]⟩, ?_⟩
    rw [assign_eq, gv, ofNat_toNat (by omega), ofNat_toNat (by omega)]
    omega
  rintro e1 mm1 ⟨⟨rfl, vs, st1, g, hg, gv, sv⟩, done⟩
  have : 2 ^ (K - g) ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) (by omega)
  have done := Option.some.inj (done.symm.trans (eval_lt (eval_lit 1) (eval_var sv) (by decide) (by omega)))
  have gK : g = K := by
    by_cases hk : g < K
    · have : 1 < 2 ^ (K - g) := Nat.one_lt_two_pow (by omega)
      rw [ite_eq_left this] at done; exact absurd done (by decide)
    · omega
  rw [gK] at gv
  -- The climb, one height per pass, against the zero tree of that height.
  refine Ends.cons (Ends.loop (fun e' mm' => RootVals e' tree depth mixin out ctx zeros ∧ e' 9 = 0 ∧
      (∃ g, K ≤ g ∧ g ≤ depth ∧ e' 7 = UInt64.ofNat g ∧ nodeAt mm' out = subtreeAt leaves g 0) ∧
      RootFrame mem mm' tree out pad)
    (fun e' _ => depth - (e' 7).toNat)
    ⟨vs, st1, ⟨K, Nat.le_refl _, tall, gv, node⟩, frame⟩ ?_ ?_) ?_
  · rintro e' mm' ⟨vs', _, ⟨h, _, hd, hv, _⟩, _⟩
    exact ⟨_, eval_lt (eval_var hv) (eval_var vs'.2.1) (by omega) (by omega)⟩
  · rintro e' mm' v ⟨vs', st', ⟨h, hk, hd, hv, nd⟩, fr⟩ hc nz
    have hc := Option.some.inj (hc.symm.trans (eval_lt (eval_var hv) (eval_var vs'.2.1) (by omega) (by omega)))
    have below : h < depth := by
      by_cases hb : h < depth
      · exact hb
      · rw [ite_eq_right hb] at hc; exact absurd hc nz
    have zr := (pre.ctxOk.congr (mm := mm') fun a ha => by
      have pc := pre.ctxOk.padCtx
      have ptab := pre.ctxOk.padTable
      have pz := pre.ctxOk.padZeros
      have tz := pre.treeZeros
      have tt := pre.treeTable
      have tc := pre.treeCtx
      have oz := pre.outZeros
      have ot := pre.outTable
      have oc := pre.outCtx
      simp only [Apart] at pc ptab pz tz tt tc oz ot oc
      exact fr a (by omega) (by omega) (by omega)).zeroAt h (by omega)
    refine Ends.append (root_hash_back okF pre kernels room vs' st' fr
      (eval_add (eval_var vs'.2.2.2.2.2) (eval_mul (eval_lit 32) (eval_var hv)))
      (Or.inl ⟨by omega, by omega⟩)) ?_
    rintro e2 mm2 ⟨vs2, st2, h7, nd2, fr2⟩
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_add (eval_var (h7.trans hv)) (eval_lit 1))) (Ends.nil ⟨⟨
      vs2.assign (by decide), (assign_ne (by decide)).trans st2, ⟨h + 1, by omega, by omega, assign_eq, ?_⟩, fr2⟩, ?_⟩)
    · rw [nd2, nd, zr, climb_step leaves h (Nat.le_trans fits (Nat.pow_le_pow_right (by decide) hk))]
    · rw [assign_eq, hv, ofNat_toNat (by omega), ofNat_toNat (by omega)]
      omega
  rintro e3 mm3 ⟨⟨vs3, st3, ⟨h, _, hd, hv, nd⟩, fr3⟩, done⟩
  have done := Option.some.inj (done.symm.trans (eval_lt (eval_var hv) (eval_var vs3.2.1) (by omega) (by omega)))
  have hD : h = depth := by
    by_cases hb : h < depth
    · rw [ite_eq_left hb] at done; exact absurd done (by decide)
    · omega
  rw [hD] at nd
  -- The word to mix in, if any.
  have mixBound : mixin ≠ 0 → mixin < 2 ^ 64 := fun nz => by
    have := access_bound (pre.mixinAccess nz); omega
  refine Ends.cons (Ends.when _ (eval_ne (eval_var vs3.2.2.1) (eval_lit 0)) (fun v => ?_) (fun v => ?_))
    fun _ _ h => Ends.nil h
  · have nz : mixin ≠ 0 := by
      intro z
      exact ite_ne_zero v (by rw [z])
    refine Ends.mono (root_hash_back okF pre kernels room vs3 st3 fr3 (eval_var vs3.2.2.1)
      (Or.inr ⟨nz, rfl⟩)) fun e4 mm4 ⟨_, st4, _, nd4, fr4⟩ => ⟨st4, ?_, fr4⟩
    have mx := pre.mixinTree nz
    have mo := pre.mixinOut nz
    have mp := pre.mixinPad nz
    simp only [Apart] at mx mo mp
    rw [nd4, nd, ite_eq_right nz, nodeAt_congr (m₂ := mem) fun i hi => fr3 _ (by omega) (by omega) (by omega)]
    rfl
  · have z : mixin = 0 := by
      have e0 := ite_eq_zero v
      exact Classical.byContradiction fun nz => nz ((ofNat_inj (mixBound nz) (by decide)).mp e0)
    exact ⟨st3, by rw [nd, ite_eq_left z]; rfl, fr3⟩

end EthLib.Consensus.Ssz.Native.Driver
