import SszNative.Proofs.Driver.Root.Packed
import SszNative.Proofs.Root.Columns

/-!
The column tree driver computes the Lean tree over columns.

Column c of a level holds, for every record, the root of that record's subtree at position c of the level.
The driver hashes the columns pairwise, one level after the next, and an odd column out against the zero tree.
It then climbs the one column left against the zero trees, up to the depth asked for.
The proof keeps, at each level, every record's subtree roots in memory, read node by node.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Asm

/-! ### Leaves and kept variables -/

/-- Each record's leaves, read from the columns: leaf c of record i is node i of column c. -/
def colLeaves (mem : Memory) (cols cs n i : Nat) : Array Bytes :=
  Array.ofFn (n := n) fun c => nodeAt mem (cols + c.val * cs + 32 * i)

/-- A record has one leaf per column. -/
@[simp] theorem colLeaves_size (mem : Memory) (cols cs n i : Nat) : (colLeaves mem cols cs n i).size = n := by
  simp [colLeaves]

/-- A record's leaf, as a tree of height zero, is the node its column holds for the record. -/
theorem colLeaves_leaf (mem : Memory) (cols cs n i : Nat) {c : Nat} (hc : c < n) :
    subtreeAt (colLeaves mem cols cs n i) 0 (c * 2 ^ 0) = nodeAt mem (cols + c * cs + 32 * i) := by
  rw [Nat.pow_zero, Nat.mul_one, subtreeAt_leaf]
  simp [colLeaves, hc]

/-- The variables the column tree driver keeps from its start: the arguments, the output, and the tree's shape. -/
structure ColEnv (env : Env) (out n count depth ctx zeros : Nat) : Prop where
  /-- The first column's address. -/
  colsV : env 0 = UInt64.ofNat (out + 32 * count)
  /-- The column count. -/
  nV : env 1 = UInt64.ofNat n
  /-- The nodes per column. -/
  countV : env 2 = UInt64.ofNat count
  /-- The depth. -/
  depthV : env 3 = UInt64.ofNat depth
  /-- The context. -/
  ctxV : env 4 = UInt64.ofNat ctx
  /-- The output, right before the columns. -/
  outV : env 5 = UInt64.ofNat out
  /-- The bytes of one column. -/
  csV : env 6 = UInt64.ofNat (32 * count)
  /-- The levels the pairing takes. -/
  levelsV : env 14 = UInt64.ofNat (depthFor n)
  /-- The levels climbed after it. -/
  climbsV : env 15 = UInt64.ofNat (depth - depthFor n)
  /-- The zero roots' address. -/
  zerosV : env 16 = UInt64.ofNat zeros

/-- Writing a variable the driver does not keep keeps the kept ones. -/
theorem ColEnv.write {env : Env} {out n count depth ctx zeros : Nat} (h : ColEnv env out n count depth ctx zeros)
    {x : Nat} (v : UInt64) (hx : (7 ≤ x ∧ x ≤ 13) ∨ 17 ≤ x) :
    ColEnv (Asm.assign env x v) out n count depth ctx zeros := by
  have ne : ∀ y, (y < 7 ∨ (14 ≤ y ∧ y < 17)) → Asm.assign env x v y = env y := fun y hy => assign_ne (by omega)
  exact ⟨by rw [ne 0 (by omega), h.colsV], by rw [ne 1 (by omega), h.nV], by rw [ne 2 (by omega), h.countV],
    by rw [ne 3 (by omega), h.depthV], by rw [ne 4 (by omega), h.ctxV], by rw [ne 5 (by omega), h.outV],
    by rw [ne 6 (by omega), h.csV], by rw [ne 14 (by omega), h.levelsV], by rw [ne 15 (by omega), h.climbsV],
    by rw [ne 16 (by omega), h.zerosV]⟩

/-- Variables that agree on the kept ones keep them. -/
theorem ColEnv.of_keep {env e : Env} {out n count depth ctx zeros : Nat} (h : ColEnv env out n count depth ctx zeros)
    (keep : ∀ y, (y < 7 ∨ (14 ≤ y ∧ y < 17)) → e y = env y) : ColEnv e out n count depth ctx zeros :=
  ⟨by rw [keep 0 (by omega), h.colsV], by rw [keep 1 (by omega), h.nV], by rw [keep 2 (by omega), h.countV],
    by rw [keep 3 (by omega), h.depthV], by rw [keep 4 (by omega), h.ctxV], by rw [keep 5 (by omega), h.outV],
    by rw [keep 6 (by omega), h.csV], by rw [keep 14 (by omega), h.levelsV], by rw [keep 15 (by omega), h.climbsV],
    by rw [keep 16 (by omega), h.zerosV]⟩

/-- A context stays filled when memory changes only inside a region apart from its buffers. -/
theorem RootReady.region {w : World} {ctx table zeros pad : Nat} {mask : UInt64} {mem mem' : Memory}
    (r : RootReady w ctx table zeros pad mask mem) {lo span : Nat} (rCtx : Apart (lo, span) (ctx, 32))
    (rTable : Apart (lo, span) (table, Kernel.tableSize)) (rZeros : Apart (lo, span) (zeros, 32 * (zeroHeights + 1)))
    (h : ∀ a, ¬ (lo ≤ a ∧ a < lo + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a) :
    RootReady w ctx table zeros pad mask mem' := by
  have pc := r.padCtx
  have pt := r.padTable
  have pz := r.padZeros
  simp only [Apart] at pc pt pz rCtx rTable rZeros
  exact r.frame fun a held => by
    simp only [RootReady.Held] at held
    exact h a (by omega) (by omega)

/--
A run hashing a column against one zero root meets the hashing conditions.

The column and the digests lie inside a region apart from the context's buffers, and apart from each other.
-/
theorem RootReady.runPreZero {w : World} {ctx table zeros pad : Nat} {mask : UInt64} {mem : Memory}
    (r : RootReady w ctx table zeros pad mask mem) {out left count lo span h : Nat}
    (acc : w.access lo span = true) (regionPad : Apart (lo, span) (pad, 1536))
    (regionCtx : Apart (lo, span) (ctx, 32)) (regionTable : Apart (lo, span) (table, Kernel.tableSize))
    (regionZeros : Apart (lo, span) (zeros, 32 * (zeroHeights + 1)))
    (outIn : lo ≤ out ∧ out + 32 * count ≤ lo + span) (leftIn : lo ≤ left ∧ left + 32 * count ≤ lo + span)
    (apart : out + 32 * count ≤ left ∨ left + 32 * count ≤ out) (hh : h ≤ zeroHeights) :
    RunPre w mem 32 0 out left (zeros + 32 * h) count ctx table pad mask := by
  have rp := regionPad
  have rc := regionCtx
  have rt := regionTable
  have rz := regionZeros
  have pz := r.padZeros
  have ze := access_end r.zerosAccess
  have ae := access_end acc
  have hz : zeroHeights = 64 := rfl
  simp only [Apart] at rp rc rt rz pz
  refine ⟨r.ctxAccess, r.maskAt, r.tableAt, r.padAt,
    ⟨r.tableHeld, access_sub acc outIn.1 (by omega), r.tableAccess,
      fun p hp => ⟨access_sub acc (by omega) (by omega), access_sub r.zerosAccess (by omega) (by omega)⟩,
      ⟨by simp only [addressBound]; omega, by simp only [addressBound]; omega⟩, by simp only [Apart]; omega,
      fun p hp => ⟨by simp only [Apart]; omega, by simp only [Apart]; omega⟩⟩,
    r.padAccess, by simp only [Apart]; omega, r.padTable,
    fun p hp => ⟨by simp only [Apart]; omega, by simp only [Apart]; omega⟩, by simp only [Apart]; omega⟩

/-! ### The start -/

/-- The statements of the column tree driver before its pairing loop. -/
abbrev colStart : List Stmt :=
  [RootColumns.zeros ::= ld (RootColumns.ctx + 16), RootColumns.cs ::= 32 * RootColumns.count,
    RootColumns.out ::= RootColumns.cols - RootColumns.cs,
    callInto RootColumns.levels "ssz_depth_for" [RootColumns.n],
    ifElse (lt RootColumns.levels RootColumns.depth) [RootColumns.climbs ::= RootColumns.depth - RootColumns.levels]
      [RootColumns.climbs ::= 0],
    RootColumns.lvl ::= RootColumns.cols, RootColumns.w ::= RootColumns.n, RootColumns.h ::= 0,
    RootColumns.next ::= RootColumns.cols + RootColumns.n * RootColumns.cs]

/--
The column tree driver's start reads the zero roots' address, places the output right before the columns, and computes
the levels of the pairing and of the climb.

The first level is the columns themselves, at height zero.
-/
theorem colStart_runs {m : Module} {w : World} (hd : m.fns.lookup "ssz_depth_for" = some DepthFor.fn) {sp : Nat}
    (room : w.stackLo + 48 ≤ sp) {mem : Memory} {ctx table zeros pad : Nat} {mask : UInt64}
    (rd : RootReady w ctx table zeros pad mask mem) {out n count depth : Nat} (hn : n < 2 ^ 64)
    (hdepth : depth < 2 ^ 64) :
    ∃ env, Runs m w sp (entryEnv [UInt64.ofNat (out + 32 * count), UInt64.ofNat n, UInt64.ofNat count,
        UInt64.ofNat depth, UInt64.ofNat ctx]) mem (.block colStart) env mem ∧
      ColEnv env out n count depth ctx zeros ∧ env 7 = UInt64.ofNat (out + 32 * count) ∧ env 8 = UInt64.ofNat n ∧
      env 9 = UInt64.ofNat 0 ∧ env 10 = UInt64.ofNat (out + 32 * count + n * (32 * count)) := by
  have dframe : DepthFor.fn.frame = 5 := by decide
  let E0 := entryEnv [UInt64.ofNat (out + 32 * count), UInt64.ofNat n, UInt64.ofNat count, UInt64.ofNat depth,
    UInt64.ofNat ctx]
  have ctxEnd := access_end rd.ctxAccess
  -- The zero roots' address, the column size, and the output.
  have l0 : eval w E0 mem (ld (RootColumns.ctx + 16)) = some (UInt64.ofNat zeros) := by
    rw [← rd.zerosAt]
    exact eval_ld (eval_add (eval_var (show E0 4 = UInt64.ofNat ctx from rfl)) (eval_lit 16))
      (access_sub rd.ctxAccess (by omega) (by omega))
  let E1 := Asm.assign E0 16 (UInt64.ofNat zeros)
  let E2 := Asm.assign E1 6 (UInt64.ofNat (32 * count))
  have l1 : eval w E1 mem (32 * RootColumns.count) = some (UInt64.ofNat (32 * count)) :=
    eval_mul (eval_lit 32) (eval_var (show E1 2 = UInt64.ofNat count from rfl))
  have l2 : eval w E2 mem (RootColumns.cols - RootColumns.cs) = some (UInt64.ofNat out) := by
    have := eval_sub (w := w) (env := E2) (mem := mem) (a := RootColumns.cols) (b := RootColumns.cs)
      (eval_var (show E2 0 = UInt64.ofNat (out + 32 * count) from rfl))
      (eval_var (show E2 6 = UInt64.ofNat (32 * count) from rfl)) (by omega)
    rwa [Nat.add_sub_cancel] at this
  let E3 := Asm.assign E2 5 (UInt64.ofNat out)
  -- The levels of the pairing.
  have dcall := depthFor_calls (w := w) hd (sp := sp) (by rw [dframe]; omega) (UInt64.ofNat n) mem
  rw [ofNat_toNat hn] at dcall
  have s3 := Runs.call (m := m) (sp := sp) (env := E3) (dst := 14) (args := [RootColumns.n])
    (values := [UInt64.ofNat n]) (by simp only [List.mapM_cons, List.mapM_nil]; rfl) dcall
  let E4 := Asm.assign E3 14 (UInt64.ofNat (depthFor n))
  have dsmall : depthFor n ≤ 64 := depthFor_le_of_le_two_pow (Nat.le_of_lt hn)
  -- The levels of the climb, none when the pairing reaches the depth.
  have s4 : Runs m w sp E4 mem (ifElse (lt RootColumns.levels RootColumns.depth)
      [RootColumns.climbs ::= RootColumns.depth - RootColumns.levels] [RootColumns.climbs ::= 0])
      (Asm.assign E4 15 (UInt64.ofNat (depth - depthFor n))) mem := by
    have c := eval_lt (w := w) (env := E4) (mem := mem) (a := RootColumns.levels) (b := RootColumns.depth)
      (eval_var (show E4 14 = UInt64.ofNat (depthFor n) from assign_eq))
      (eval_var (show E4 3 = UInt64.ofNat depth from rfl)) (by omega) hdepth
    by_cases lt : depthFor n < depth
    · rw [ite_eq_left lt] at c
      exact Runs.ifElse_true 1 c (by decide) (Runs.block_cons (Runs.set' (eval_sub
        (eval_var (show E4 3 = UInt64.ofNat depth from rfl))
        (eval_var (show E4 14 = UInt64.ofNat (depthFor n) from assign_eq)) (by omega))) (Runs.block_nil _ _ _ _ _))
    · rw [ite_eq_right lt] at c
      rw [show depth - depthFor n = 0 by omega]
      exact Runs.ifElse_false c (Runs.block_cons (Runs.set' (eval_lit 0)) (Runs.block_nil _ _ _ _ _))
  let E5 := Asm.assign E4 15 (UInt64.ofNat (depth - depthFor n))
  let E6 := Asm.assign E5 7 (UInt64.ofNat (out + 32 * count))
  let E7 := Asm.assign E6 8 (UInt64.ofNat n)
  let E8 := Asm.assign E7 9 (UInt64.ofNat 0)
  have l8 : eval w E8 mem (RootColumns.cols + RootColumns.n * RootColumns.cs) =
      some (UInt64.ofNat (out + 32 * count + n * (32 * count))) :=
    eval_add (eval_var (show E8 0 = _ from rfl)) (eval_mul (eval_var (show E8 1 = _ from rfl))
      (eval_var (show E8 6 = UInt64.ofNat (32 * count) from rfl)))
  refine ⟨Asm.assign E8 10 (UInt64.ofNat (out + 32 * count + n * (32 * count))),
    Runs.block_cons (Runs.set' l0) (Runs.block_cons (Runs.set' l1) (Runs.block_cons (Runs.set' l2)
      (Runs.block_cons s3 (Runs.block_cons s4 (Runs.block_cons (Runs.set' (eval_var (show E5 0 = _ from rfl)))
        (Runs.block_cons (Runs.set' (eval_var (show E6 1 = _ from rfl)))
          (Runs.block_cons (Runs.set' (eval_lit 0)) (Runs.block_cons (Runs.set' l8)
            (Runs.block_nil _ _ _ _ _))))))))), ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl,
    assign_eq⟩

/-! ### Pairs of columns -/

/-- The loop hashing the current level's pairs of columns into the next level. -/
abbrev colPairLoop : Stmt :=
  while_ (lt RootColumns.i RootColumns.half) [
    callInto RootColumns.sink "ssz_hash_columns" [RootColumns.dst + RootColumns.i * RootColumns.cs,
      RootColumns.lvl + 2 * RootColumns.i * RootColumns.cs, RootColumns.lvl + (2 * RootColumns.i + 1) * RootColumns.cs,
      RootColumns.count, RootColumns.ctx],
    RootColumns.i ::= RootColumns.i + 1]

/--
The loop over pairs of columns writes, at the next level's place, the parents of every pair.

Column p of the next level holds, for every record, the root of its subtree one height up at position p.
Memory changes only in the columns written and the padding area.
-/
theorem colPairs_ends {m : Module} {w : World} (hash : HashCalls m w .columns) {sp : Nat}
    (room : w.stackLo + hashStack ≤ sp) {env : Env} {mem : Memory} {out n count depth ctx table zeros pad : Nat}
    {mask : UInt64} (v : ColEnv env out n count depth ctx zeros) {L W D half h span : Nat}
    (lv : env 7 = UInt64.ofNat L) (hv : env 11 = UInt64.ofNat half) (dv : env 13 = UInt64.ofNat D)
    (iv : env 12 = UInt64.ofNat 0) (rd : RootReady w ctx table zeros pad mask mem)
    (acc : w.access out span = true) (rPad : Apart (out, span) (pad, 1536)) (rCtx : Apart (out, span) (ctx, 32))
    (rTable : Apart (out, span) (table, Kernel.tableSize))
    (rZeros : Apart (out, span) (zeros, 32 * (zeroHeights + 1)))
    (lIn : out ≤ L ∧ L + W * (32 * count) ≤ out + span) (dIn : out ≤ D ∧ D + half * (32 * count) ≤ out + span)
    (apart : D + half * (32 * count) ≤ L ∨ L + W * (32 * count) ≤ D) (hW : 2 * half ≤ W) (wSmall : W < 2 ^ 64)
    (leaves : Nat → Array Bytes)
    (roots : ∀ c < W, ∀ i < count, nodeAt mem (L + c * (32 * count) + 32 * i) = subtreeAt (leaves i) h (c * 2 ^ h)) :
    Ends m w sp env mem colPairLoop fun e mm => (∀ y, y ≠ 12 → y ≠ 17 → e y = env y) ∧
      (∀ p < half, ∀ i < count,
        nodeAt mm (D + p * (32 * count) + 32 * i) = subtreeAt (leaves i) (h + 1) (p * 2 ^ (h + 1))) ∧
      (∀ a, ¬ (D ≤ a ∧ a < D + half * (32 * count)) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm a = mem a) := by
  have ae := access_end acc
  have rp := rPad
  simp only [Apart] at rp
  have big : half * (32 * count) ≤ W * (32 * count) := Nat.mul_le_mul_right _ (by omega)
  have halfSmall : half < 2 ^ 64 := by omega
  let inv : Env → Memory → Prop := fun e mm => ∃ k, k ≤ half ∧ e 12 = UInt64.ofNat k ∧
    (∀ y, y ≠ 12 → y ≠ 17 → e y = env y) ∧
    (∀ p < k, ∀ i < count,
      nodeAt mm (D + p * (32 * count) + 32 * i) = subtreeAt (leaves i) (h + 1) (p * 2 ^ (h + 1))) ∧
    (∀ a, ¬ (D ≤ a ∧ a < D + k * (32 * count)) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm a = mem a)
  have ends := Ends.loop (m := m) (w := w) (sp := sp) (env := env) (mem := mem)
    (c := lt RootColumns.i RootColumns.half)
    (body := .block [
      callInto RootColumns.sink "ssz_hash_columns" [RootColumns.dst + RootColumns.i * RootColumns.cs,
        RootColumns.lvl + 2 * RootColumns.i * RootColumns.cs,
        RootColumns.lvl + (2 * RootColumns.i + 1) * RootColumns.cs, RootColumns.count, RootColumns.ctx],
      RootColumns.i ::= RootColumns.i + 1])
    inv (fun e _ => half - (e 12).toNat)
    ⟨0, by omega, iv, fun _ _ _ => rfl, fun p hp => absurd hp (by omega), fun a _ _ => rfl⟩
    (fun e mm ⟨k, hk, ki, keep, _⟩ => ⟨_, eval_lt (eval_var ki) (eval_var (by rw [keep 11 (by decide) (by decide), hv]))
      (by omega) halfSmall⟩)
    (fun e mm c ⟨k, hk, ki, keep, done, frame⟩ hc nz => by
      have hc' := eval_lt (w := w) (env := e) (mem := mm) (a := RootColumns.i) (b := RootColumns.half) (eval_var ki)
        (eval_var (by rw [keep 11 (by decide) (by decide), hv])) (by omega) halfSmall
      rw [hc] at hc'
      have more : k < half := by
        by_cases lt : k < half
        · exact lt
        · rw [ite_eq_right lt] at hc'; cases hc'; exact absurd rfl nz
      -- The products this pass needs, as facts about atoms.
      have e1 : 2 * k * (32 * count) = 2 * (k * (32 * count)) := Nat.mul_assoc _ _ _
      have e2 : (2 * k + 1) * (32 * count) = 2 * (k * (32 * count)) + (32 * count) := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      have f2 : (2 * k + 2) * (32 * count) ≤ W * (32 * count) := Nat.mul_le_mul_right _ (by omega)
      have e3 : (2 * k + 2) * (32 * count) = 2 * (k * (32 * count)) + 2 * (32 * count) := by rw [Nat.add_mul, Nat.mul_assoc]
      have f1 : (k + 1) * (32 * count) ≤ half * (32 * count) := Nat.mul_le_mul_right _ more
      have e4 : (k + 1) * (32 * count) = k * (32 * count) + (32 * count) := by rw [Nat.add_mul, Nat.one_mul]
      have ready : RootReady w ctx table zeros pad mask mm :=
        rd.region rCtx rTable rZeros fun a o p => frame a (by omega) p
      -- The hashing run: the parents of the pair's nodes, one per record.
      have pre : RunPre w mm 32 32 (D + k * (32 * count)) (L + 2 * k * (32 * count)) (L + (2 * k + 1) * (32 * count)) count ctx table pad mask :=
        ready.runPre (lo := out) (span := span) acc rPad rCtx rTable ⟨by omega, by omega⟩
          (fun q hq => ⟨by omega, by omega, by omega, by omega⟩) ⟨by simp only [addressBound]; omega,
            by simp only [addressBound]; omega⟩ (fun q hq => ⟨by simp only [Apart]; omega, by simp only [Apart]; omega⟩)
      obtain ⟨mm1, call, after⟩ := (hash sp mm (D + k * (32 * count)) (L + 2 * k * (32 * count)) (L + (2 * k + 1) * (32 * count)) count ctx table pad
        mask pre ready.kernels room)
      have cs : e 6 = UInt64.ofNat (32 * count) := by rw [keep 6 (by decide) (by decide), v.csV]
      have callRuns := Runs.call (m := m) (sp := sp) (env := e) (mem := mm) (dst := 17)
        (args := [RootColumns.dst + RootColumns.i * RootColumns.cs,
          RootColumns.lvl + 2 * RootColumns.i * RootColumns.cs,
          RootColumns.lvl + (2 * RootColumns.i + 1) * RootColumns.cs, RootColumns.count, RootColumns.ctx])
        (eval_five (eval_add (eval_var (by rw [keep 13 (by decide) (by decide), dv])) (eval_mul (eval_var ki)
            (eval_var cs)))
          (eval_add (eval_var (by rw [keep 7 (by decide) (by decide), lv])) (eval_mul (eval_mul (eval_lit 2)
            (eval_var ki)) (eval_var cs)))
          (eval_add (eval_var (by rw [keep 7 (by decide) (by decide), lv])) (eval_mul (eval_add (eval_mul (eval_lit 2)
            (eval_var ki)) (eval_lit 1)) (eval_var cs)))
          (eval_var (by rw [keep 2 (by decide) (by decide), v.countV]))
          (eval_var (by rw [keep 4 (by decide) (by decide), v.ctxV]))) call
      have inc := Runs.set' (m := m) (w := w) (sp := sp) (mem := mm1) (x := 12) (env := Asm.assign e 17 0)
        (e := RootColumns.i + 1) (eval_add (eval_var (by rw [assign_ne (by decide), ki])) (eval_lit 1))
      refine Ends.step callRuns (Ends.step inc (Ends.nil ⟨⟨k + 1, by omega, assign_eq, fun y a b => ?_,
        fun p hp i hi => ?_, fun a o pd => ?_⟩, ?_⟩))
      · rw [assign_ne a, assign_ne b, keep y a b]
      · by_cases old : p < k
        · -- An earlier column stays as it was.
          have f3 : (p + 1) * (32 * count) ≤ k * (32 * count) := Nat.mul_le_mul_right _ old
          rw [Nat.add_mul, Nat.one_mul] at f3
          rw [nodeAt_congr (m₂ := mm) fun j hj => by rw [after _ (by omega), hashed_outside (by omega)],
            done p old i hi]
        · -- The new column holds the parents of the pair.
          have pk : k = p := by omega
          subst pk
          rw [nodeAt_congr (m₂ := hashed mm (D + k * (32 * count)) (L + 2 * k * (32 * count)) (L + (2 * k + 1) * (32 * count)) count 32 32)
            fun j hj => after _ (by omega), nodeAt_hashed _ _ _ _ _ _ _ _ hi, ← parent_pair,
            nodeAt_congr (m₂ := mem) fun j hj => frame _ (by omega) (by omega),
            nodeAt_congr (m₂ := mem) (a := L + (2 * k + 1) * (32 * count) + 32 * i) fun j hj => frame _ (by omega) (by omega),
            roots _ (by omega) i hi, roots _ (by omega) i hi]
      · rw [after a pd, hashed_outside (by omega), frame a (by omega) pd]
      · show half - (UInt64.ofNat (k + 1)).toNat < half - (e 12).toNat
        rw [ki, ofNat_toNat (by omega), ofNat_toNat (by omega)]
        omega)
  obtain ⟨e, mm, run, ⟨k, hk, ki, keep, done, frame⟩, exit⟩ := ends
  -- The loop stops once every pair is hashed.
  have stop := eval_lt (w := w) (env := e) (mem := mm) (a := RootColumns.i) (b := RootColumns.half) (eval_var ki)
    (eval_var (by rw [keep 11 (by decide) (by decide), hv])) (by omega) halfSmall
  rw [exit] at stop
  have kh : k = half := by
    by_cases lt : k < half
    · rw [ite_eq_left lt] at stop; cases stop
    · omega
  subst kh
  exact ⟨e, mm, run, keep, done, frame⟩

/-! ### One level -/

/-- A depth step: more than one column takes one level more than half of them, rounded up. -/
private theorem colDepth_step {n : Nat} (big : 1 < n) : depthFor n = depthFor (n / 2 + n % 2) + 1 := by
  rw [depthFor, ite_eq_right (by omega), show (n + 1) / 2 = n / 2 + n % 2 by omega]

/--
The column tree driver's state at a level: where the level lies, how many columns it has, and what they hold.

Column c holds, for record i, the root of the record's subtree of the level's height at position c.
The level lies after the columns, with room for the levels still to come, or is the output once nothing is left.
Memory changes only in the output's region and the padding area.
-/
structure ColAt (w : World) (out n count depth ctx table zeros pad span : Nat) (mask : UInt64) (mem0 : Memory)
    (leaves : Nat → Array Bytes) (env : Env) (mem : Memory) (h W L j : Nat) : Prop where
  /-- The kept variables. -/
  vars : ColEnv env out n count depth ctx zeros
  /-- The level's address. -/
  lvlV : env 7 = UInt64.ofNat L
  /-- The level's column count. -/
  widthV : env 8 = UInt64.ofNat W
  /-- The level's height. -/
  heightV : env 9 = UInt64.ofNat h
  /-- Where the next level may go: right after this one. -/
  nextV : env 10 = UInt64.ofNat (L + W * (32 * count))
  /-- At least one column. -/
  wide : 1 ≤ W
  /-- The level lies after the columns with room for the levels to come, or is the output, with nothing to climb. -/
  place : (out + 32 * count ≤ L ∧ L + 3 * (W * (32 * count)) ≤ out + 32 * count + (3 * n + j) * (32 * count)) ∨
    (L = out ∧ W = 1 ∧ depth - depthFor n = 0)
  /-- Its columns hold the subtrees' roots. -/
  roots : ∀ c < W, ∀ i < count, nodeAt mem (L + c * (32 * count) + 32 * i) = subtreeAt (leaves i) h (c * 2 ^ h)
  /-- Its subtrees cover the leaves. -/
  covers : n ≤ W * 2 ^ h
  /-- Its last subtree holds a leaf. -/
  tight : (W - 1) * 2 ^ h < n
  /-- The context stays filled. -/
  ready : RootReady w ctx table zeros pad mask mem
  /-- Memory is as at the start, outside the output's region and the padding area. -/
  frame : ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem a = mem0 a

/-- The body of the column tree driver's pairing loop. -/
abbrev colPass : List Stmt :=
  [RootColumns.half ::= RootColumns.w / 2,
    ifElse (eq (RootColumns.half + RootColumns.w % 2) 1 &&& eq RootColumns.climbs 0)
      [RootColumns.dst ::= RootColumns.out] [RootColumns.dst ::= RootColumns.next],
    RootColumns.i ::= 0,
    colPairLoop,
    when (ne (RootColumns.w % 2) 0)
      [callInto RootColumns.sink "ssz_hash_fixed" [RootColumns.dst + RootColumns.half * RootColumns.cs,
        RootColumns.lvl + (RootColumns.w - 1) * RootColumns.cs, RootColumns.zeros + 32 * RootColumns.h,
        RootColumns.count, RootColumns.ctx]],
    RootColumns.w ::= RootColumns.half + RootColumns.w % 2, RootColumns.lvl ::= RootColumns.dst,
    RootColumns.next ::= RootColumns.dst + RootColumns.w * RootColumns.cs, RootColumns.h ::= RootColumns.h + 1]

set_option maxHeartbeats 2000000 in
/--
One pass of the pairing loop hashes a level of several columns into the next, a height up.

Pairs of columns hash into one column each, and an odd column out against the zero tree of its height.
The next level lands right after this one, or in the output when it is the last and nothing is left to climb.
-/
theorem colPass_ends {m : Module} {w : World} (hash : HashingOk m w) {sp : Nat} (room : w.stackLo + hashStack ≤ sp)
    {out n count depth ctx table zeros pad span : Nat} {mask : UInt64} {mem0 : Memory} {leaves : Nat → Array Bytes}
    (size : ∀ i < count, (leaves i).size = n) (hz : depth ≤ zeroHeights) (nSmall : n < 2 ^ 64)
    (deep : depthFor n ≤ depth) (hspan : 32 * count + (3 * n + (depth - depthFor n)) * (32 * count) ≤ span)
    (acc : w.access out span = true) (rPad : Apart (out, span) (pad, 1536)) (rCtx : Apart (out, span) (ctx, 32))
    (rTable : Apart (out, span) (table, Kernel.tableSize))
    (rZeros : Apart (out, span) (zeros, 32 * (zeroHeights + 1)))
    {env : Env} {mem : Memory} {h W L : Nat}
    (st : ColAt w out n count depth ctx table zeros pad span mask mem0 leaves env mem h W L 0)
    (pairing : h + depthFor W = depthFor n) (big : 2 ≤ W) (wSmall : W ≤ n) :
    Ends m w sp env mem (.block colPass) fun e mm => ∃ L', ColAt w out n count depth ctx table zeros pad span mask mem0
      leaves e mm (h + 1) (W / 2 + W % 2) L' 0 ∧ (h + 1) + depthFor (W / 2 + W % 2) = depthFor n := by
  have ae := access_end acc
  have rp := rPad
  simp only [Apart] at rp
  have v := st.vars
  have place : out + 32 * count ≤ L ∧ L + 3 * (W * (32 * count)) ≤ out + 32 * count + (3 * n) * (32 * count) := by
    rcases st.place with p | p
    · simpa using p
    · omega
  have step := colDepth_step (show 1 < W by omega)
  have hz64 : zeroHeights = 64 := rfl
  have hlow : h < depthFor n := by omega
  -- The products this pass needs, as facts about atoms.
  have climbBound : (3 * n) * (32 * count) + 32 * count ≤ span := by
    have := Nat.mul_le_mul_right (32 * count) (show 3 * n ≤ 3 * n + (depth - depthFor n) by omega)
    omega
  have wc : W * (32 * count) = (W - 1) * (32 * count) + 32 * count := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  have hc : W / 2 * (32 * count) + W % 2 * (32 * count) = (W / 2 + W % 2) * (32 * count) := (Nat.add_mul _ _ _).symm
  have three : 3 * ((W / 2 + W % 2) * (32 * count)) ≤ 2 * (W * (32 * count)) := by
    have := Nat.mul_le_mul_right (32 * count) (show 3 * (W / 2 + W % 2) ≤ 2 * W by omega)
    rwa [Nat.mul_assoc, Nat.mul_assoc] at this
  -- The half.
  have s0 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem) (x := 11) (env := env) (e := RootColumns.w / 2)
    (eval_div (eval_var st.widthV) (eval_lit 2) (by omega) (by decide) (by decide))
  let E1 := Asm.assign env 11 (UInt64.ofNat (W / 2))
  -- Where the next level goes: the output for the last level with nothing to climb, and right after this one otherwise.
  obtain ⟨D, hD⟩ : ∃ D, D = if W / 2 + W % 2 = 1 ∧ depth - depthFor n = 0 then out else L + W * (32 * count) :=
    ⟨_, rfl⟩
  have s1 : Runs m w sp E1 mem (ifElse (eq (RootColumns.half + RootColumns.w % 2) 1 &&& eq RootColumns.climbs 0)
      [RootColumns.dst ::= RootColumns.out] [RootColumns.dst ::= RootColumns.next])
      (Asm.assign E1 13 (UInt64.ofNat D)) mem := by
    have w8 : E1 8 = UInt64.ofNat W := by simp only [E1]; rw [assign_ne (by decide)]; exact st.widthV
    have c := eval_and (eval_eq_nat (w := w) (env := E1) (mem := mem) (a := RootColumns.half + RootColumns.w % 2)
      (b := 1) (eval_add (eval_var assign_eq) (eval_mod (eval_var w8) (eval_lit 2) (by omega) (by decide)
        (by decide))) (eval_lit 1) (by omega) (by decide))
      (eval_eq_nat (w := w) (env := E1) (mem := mem) (a := RootColumns.climbs) (b := 0)
        (eval_var (by simp only [E1]; rw [assign_ne (by decide)]; exact v.climbsV)) (eval_lit 0) (by omega) (by decide))
    by_cases last : W / 2 + W % 2 = 1 ∧ depth - depthFor n = 0
    · rw [ite_eq_left last.1, ite_eq_left last.2] at c
      rw [hD, ite_eq_left last]
      exact Runs.ifElse_true 1 c (by decide) (Runs.block_cons (Runs.set' (eval_var
        (by simp only [E1]; rw [assign_ne (by decide)]; exact v.outV))) (Runs.block_nil _ _ _ _ _))
    · rw [hD, ite_eq_right last]
      have c0 : ((if W / 2 + W % 2 = 1 then (1 : UInt64) else 0) &&& if depth - depthFor n = 0 then 1 else 0) = 0 := by
        by_cases a : W / 2 + W % 2 = 1
        · rw [ite_eq_left a, ite_eq_right fun b => last ⟨a, b⟩]; decide
        · rw [ite_eq_right a]; split <;> decide
      rw [c0] at c
      exact Runs.ifElse_false c (Runs.block_cons (Runs.set' (eval_var
        (by simp only [E1]; rw [assign_ne (by decide)]; exact st.nextV))) (Runs.block_nil _ _ _ _ _))
  let E2 := Asm.assign E1 13 (UInt64.ofNat D)
  have s2 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem) (x := 12) (env := E2) (e := (0 : Expr)) (eval_lit 0)
  let E3 := Asm.assign E2 12 (UInt64.ofNat 0)
  -- The next level's place: inside the region, apart from this level.
  have dPlace : (D = out ∧ W = 2 ∧ depth - depthFor n = 0) ∨ D = L + W * (32 * count) := by
    rw [hD]
    by_cases last : W / 2 + W % 2 = 1 ∧ depth - depthFor n = 0
    · rw [ite_eq_left last]; exact .inl ⟨rfl, by omega, last.2⟩
    · rw [ite_eq_right last]; exact .inr rfl
  have halfLe : W / 2 * (32 * count) ≤ W * (32 * count) := Nat.mul_le_mul_right _ (by omega)
  have twoLe : 2 * (32 * count) ≤ W * (32 * count) := Nat.mul_le_mul_right _ big
  have dIn : out ≤ D ∧ D + W / 2 * (32 * count) ≤ out + span := by
    rcases dPlace with ⟨rfl, w2, _⟩ | rfl
    · subst w2; simp only [show 2 / 2 = 1 from rfl, Nat.one_mul]; omega
    · omega
  have apart : D + W / 2 * (32 * count) ≤ L ∨ L + W * (32 * count) ≤ D := by
    rcases dPlace with ⟨rfl, w2, _⟩ | rfl
    · subst w2; simp only [show 2 / 2 = 1 from rfl, Nat.one_mul]; omega
    · omega
  have keep3 : ∀ y, y ≠ 11 → y ≠ 12 → y ≠ 13 → E3 y = env y := fun y a b c => by
    simp only [E3, E2, E1]; rw [assign_ne b, assign_ne c, assign_ne a]
  obtain ⟨e1, mm1, r1, keep1, pairs, frame1⟩ := colPairs_ends hash.columns room
    (v.of_keep fun y hy => keep3 y (by omega) (by omega) (by omega))
    (L := L) (W := W) (D := D) (half := W / 2) (h := h) (span := span)
    (by rw [keep3 7 (by decide) (by decide) (by decide)]; exact st.lvlV)
    (by simp only [E3, E2]; rw [assign_ne (by decide), assign_ne (by decide)]; exact assign_eq)
    (by simp only [E3]; rw [assign_ne (by decide)]; exact assign_eq) assign_eq st.ready acc rPad rCtx rTable rZeros
    ⟨by omega, by omega⟩ dIn apart (by omega) (by omega) leaves st.roots
  have k1 : ∀ y, y ≠ 11 → y ≠ 12 → y ≠ 13 → y ≠ 17 → e1 y = env y := fun y a b c d => by
    rw [keep1 y b d, keep3 y a b c]
  have e1half : e1 11 = UInt64.ofNat (W / 2) := by
    rw [keep1 11 (by decide) (by decide)]; simp only [E3, E2]; rw [assign_ne (by decide), assign_ne (by decide)]
    exact assign_eq
  have e1dst : e1 13 = UInt64.ofNat D := by
    rw [keep1 13 (by decide) (by decide)]; simp only [E3]; rw [assign_ne (by decide)]; exact assign_eq
  have ready1 : RootReady w ctx table zeros pad mask mm1 :=
    st.ready.region rCtx rTable rZeros fun a o p => frame1 a (by omega) p
  -- An odd column out climbs against the zero tree of the level's height.
  have odd : ∃ e2 mm2, Runs m w sp e1 mm1 (when (ne (RootColumns.w % 2) 0)
      [callInto RootColumns.sink "ssz_hash_fixed" [RootColumns.dst + RootColumns.half * RootColumns.cs,
        RootColumns.lvl + (RootColumns.w - 1) * RootColumns.cs, RootColumns.zeros + 32 * RootColumns.h,
        RootColumns.count, RootColumns.ctx]]) e2 mm2 ∧
      (∀ y, y ≠ 17 → e2 y = e1 y) ∧
      (∀ c < W / 2 + W % 2, ∀ i < count,
        nodeAt mm2 (D + c * (32 * count) + 32 * i) = subtreeAt (leaves i) (h + 1) (c * 2 ^ (h + 1))) ∧
      (∀ a, ¬ (D ≤ a ∧ a < D + (W / 2 + W % 2) * (32 * count)) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm2 a = mem a) := by
    have w8 : e1 8 = UInt64.ofNat W := by rw [k1 8 (by decide) (by decide) (by decide) (by decide)]; exact st.widthV
    have c := eval_ne (w := w) (env := e1) (mem := mm1) (a := RootColumns.w % 2) (b := 0)
      (eval_mod (eval_var w8) (eval_lit 2) (by omega) (by decide) (by decide)) (eval_lit 0)
    have e1cs : e1 6 = UInt64.ofNat (32 * count) := by
      rw [k1 6 (by decide) (by decide) (by decide) (by decide)]; exact v.csV
    have e1lvl : e1 7 = UInt64.ofNat L := by rw [k1 7 (by decide) (by decide) (by decide) (by decide)]; exact st.lvlV
    have e1zeros : e1 16 = UInt64.ofNat zeros := by
      rw [k1 16 (by decide) (by decide) (by decide) (by decide)]; exact v.zerosV
    have e1h : e1 9 = UInt64.ofNat h := by rw [k1 9 (by decide) (by decide) (by decide) (by decide)]; exact st.heightV
    have e1count : e1 2 = UInt64.ofNat count := by
      rw [k1 2 (by decide) (by decide) (by decide) (by decide)]; exact v.countV
    have e1ctx : e1 4 = UInt64.ofNat ctx := by rw [k1 4 (by decide) (by decide) (by decide) (by decide)]; exact v.ctxV
    by_cases isOdd : W % 2 = 1
    · rw [isOdd] at c
      have w3 : D = L + W * (32 * count) := by
        rcases dPlace with ⟨_, w2, _⟩ | e
        · subst w2; simp at isOdd
        · exact e
      subst w3
      have one : W % 2 * (32 * count) = 32 * count := by rw [isOdd, Nat.one_mul]
      have pre : RunPre w mm1 32 0 (L + W * (32 * count) + W / 2 * (32 * count)) (L + (W - 1) * (32 * count))
          (zeros + 32 * h) count ctx table pad mask :=
        ready1.runPreZero acc rPad rCtx rTable rZeros ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega)
      obtain ⟨mm2, call, after⟩ := (hash.fixed sp mm1 _ _ _ count ctx table pad mask pre ready1.kernels room)
      have callRuns := Runs.call (m := m) (sp := sp) (env := e1) (mem := mm1) (dst := 17)
        (args := [RootColumns.dst + RootColumns.half * RootColumns.cs,
          RootColumns.lvl + (RootColumns.w - 1) * RootColumns.cs, RootColumns.zeros + 32 * RootColumns.h,
          RootColumns.count, RootColumns.ctx])
        (eval_five (eval_add (eval_var e1dst) (eval_mul (eval_var e1half) (eval_var e1cs)))
          (eval_add (eval_var e1lvl) (eval_mul (eval_sub (eval_var w8) (eval_lit 1) (by omega)) (eval_var e1cs)))
          (eval_add (eval_var e1zeros) (eval_mul (eval_lit 32) (eval_var e1h)))
          (eval_var e1count)
          (eval_var e1ctx)) call
      refine ⟨_, mm2, Runs.when_true 1 (by rw [c]; rfl) (by decide)
        (Runs.block_cons callRuns (Runs.block_nil _ _ _ _ _)), fun y hy => assign_ne hy, fun c hc i hi => ?_,
        fun a o pd => ?_⟩
      · by_cases old : c < W / 2
        · -- A parent of a pair stays as the pairs left it.
          have f3 : (c + 1) * (32 * count) ≤ W / 2 * (32 * count) := Nat.mul_le_mul_right _ old
          rw [Nat.add_mul, Nat.one_mul] at f3
          rw [nodeAt_congr (m₂ := mm1) fun j hj => by rw [after _ (by omega), hashed_outside (by omega)],
            pairs c old i hi]
        · -- The odd column's parent: the last column against the zero tree.
          have cw : c = W / 2 := by omega
          subst cw
          have zero : nodeAt mm1 (zeros + 32 * h) = zeroSubtree h := nodeAt_zeros ready1.zeroRoots h (by omega)
          have up := parent_last (leaves i) h W isOdd (by rw [size i hi]; exact st.covers)
          have e := nodeAt_hashed mm1 (L + W * (32 * count) + W / 2 * (32 * count)) (L + (W - 1) * (32 * count))
            (zeros + 32 * h) count 32 0 i hi
          simp only [Nat.zero_mul, Nat.add_zero] at e
          rw [nodeAt_congr (m₂ := hashed mm1 (L + W * (32 * count) + W / 2 * (32 * count))
            (L + (W - 1) * (32 * count)) (zeros + 32 * h) count 32 0) fun j hj => after _ (by omega), e, zero, ← up,
            nodeAt_congr (m₂ := mem) fun j hj => frame1 _ (by omega) (by omega), st.roots _ (by omega) i hi]
      · rw [after a pd, hashed_outside (by omega), frame1 a (by omega) pd]
    · have isEven : W % 2 = 0 := by omega
      rw [isEven] at c
      refine ⟨e1, mm1, Runs.when_false (by rw [c]; rfl), fun _ _ => rfl, fun c hc i hi => ?_, fun a o pd => ?_⟩
      · exact pairs c (by omega) i hi
      · exact frame1 a (by rw [isEven, Nat.add_zero] at o; exact o) pd
  obtain ⟨e2, mm2, r2, keep2, roots2, frame2⟩ := odd
  -- The next level's end stays inside the region.
  have dEnd : D + (W / 2 + W % 2) * (32 * count) ≤ out + span := by
    rcases dPlace with ⟨rfl, w2, _⟩ | rfl
    · subst w2; simp only [show 2 / 2 + 2 % 2 = 1 from rfl, Nat.one_mul]; omega
    · omega
  have e2v : ∀ y, y ≠ 11 → y ≠ 12 → y ≠ 13 → y ≠ 17 → e2 y = env y := fun y a b c d => by
    rw [keep2 y d, k1 y a b c d]
  have e2half : e2 11 = UInt64.ofNat (W / 2) := by rw [keep2 11 (by decide)]; exact e1half
  have e2dst : e2 13 = UInt64.ofNat D := by rw [keep2 13 (by decide)]; exact e1dst
  have e2w : e2 8 = UInt64.ofNat W := by rw [e2v 8 (by decide) (by decide) (by decide) (by decide)]; exact st.widthV
  have e2cs : e2 6 = UInt64.ofNat (32 * count) := by
    rw [e2v 6 (by decide) (by decide) (by decide) (by decide)]; exact v.csV
  have e2h : e2 9 = UInt64.ofNat h := by rw [e2v 9 (by decide) (by decide) (by decide) (by decide)]; exact st.heightV
  -- The level moves up: its width, place, next place, and height.
  have s5 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mm2) (x := 8) (env := e2)
    (e := RootColumns.half + RootColumns.w % 2)
    (eval_add (eval_var e2half) (eval_mod (eval_var e2w) (eval_lit 2) (by omega) (by decide) (by decide)))
  let F1 := Asm.assign e2 8 (UInt64.ofNat (W / 2 + W % 2))
  have s6 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mm2) (x := 7) (env := F1) (e := RootColumns.dst)
    (eval_var (show F1 13 = UInt64.ofNat D by simp only [F1]; rw [assign_ne (by decide)]; exact e2dst))
  let F2 := Asm.assign F1 7 (UInt64.ofNat D)
  have s7 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mm2) (x := 10) (env := F2)
    (e := RootColumns.dst + RootColumns.w * RootColumns.cs)
    (eval_add (eval_var (show F2 13 = UInt64.ofNat D by
        simp only [F2, F1]; rw [assign_ne (by decide), assign_ne (by decide)]; exact e2dst))
      (eval_mul (eval_var (show F2 8 = UInt64.ofNat (W / 2 + W % 2) by
          simp only [F2, F1]; rw [assign_ne (by decide)]; exact assign_eq))
        (eval_var (show F2 6 = UInt64.ofNat (32 * count) by
          simp only [F2, F1]; rw [assign_ne (by decide), assign_ne (by decide)]; exact e2cs))))
  let F3 := Asm.assign F2 10 (UInt64.ofNat (D + (W / 2 + W % 2) * (32 * count)))
  have s8 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mm2) (x := 9) (env := F3) (e := RootColumns.h + 1)
    (eval_add (eval_var (show F3 9 = UInt64.ofNat h by
      simp only [F3, F2, F1]; rw [assign_ne (by decide), assign_ne (by decide), assign_ne (by decide)]; exact e2h))
      (eval_lit 1))
  let F4 := Asm.assign F3 9 (UInt64.ofNat (h + 1))
  have up := covers_up n h W st.covers st.tight
  rw [show (W + 1) / 2 = W / 2 + W % 2 by omega] at up
  refine ⟨F4, mm2, Runs.block_cons s0 (Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons r1
    (Runs.block_cons r2 (Runs.block_cons s5 (Runs.block_cons s6 (Runs.block_cons s7 (Runs.block_cons s8
      (Runs.block_nil _ _ _ _ _))))))))), D, ⟨?_, ?_, ?_, assign_eq, ?_, by omega, ?_, roots2, up.1, up.2, ?_,
      fun a o p => ?_⟩, by omega⟩
  · exact v.of_keep fun y hy => by
      simp only [F4, F3, F2, F1]
      rw [assign_ne (by omega), assign_ne (by omega), assign_ne (by omega), assign_ne (by omega)]
      exact e2v y (by omega) (by omega) (by omega) (by omega)
  · simp only [F4, F3]; rw [assign_ne (by decide), assign_ne (by decide)]; exact assign_eq
  · simp only [F4, F3, F2]; rw [assign_ne (by decide), assign_ne (by decide), assign_ne (by decide)]; exact assign_eq
  · simp only [F4]; rw [assign_ne (by decide)]; exact assign_eq
  · -- The last level is the output; any other lies right after this one, with room for the rest.
    rcases dPlace with ⟨rfl, w2, cz⟩ | rfl
    · exact .inr ⟨rfl, by subst w2; rfl, cz⟩
    · exact .inl ⟨by omega, by rw [Nat.add_zero]; omega⟩
  · exact st.ready.region rCtx rTable rZeros fun a o p => frame2 a (by omega) p
  · rw [frame2 a (by omega) p]; exact st.frame a o p

/-- The pairing loop of the column tree driver. -/
abbrev colPairing : Stmt := while_ (lt 1 RootColumns.w) colPass

/--
The pairing loop runs from the columns to one column, at the height the column count's tree needs.

That column holds every record's root over its leaves, and lies after the columns, or in the output.
-/
theorem colPairing_ends {m : Module} {w : World} (hash : HashingOk m w) {sp : Nat} (room : w.stackLo + hashStack ≤ sp)
    {out n count depth ctx table zeros pad span : Nat} {mask : UInt64} {mem0 : Memory} {leaves : Nat → Array Bytes}
    (size : ∀ i < count, (leaves i).size = n) (hz : depth ≤ zeroHeights) (nSmall : n < 2 ^ 64)
    (deep : depthFor n ≤ depth) (hspan : 32 * count + (3 * n + (depth - depthFor n)) * (32 * count) ≤ span)
    (acc : w.access out span = true) (rPad : Apart (out, span) (pad, 1536)) (rCtx : Apart (out, span) (ctx, 32))
    (rTable : Apart (out, span) (table, Kernel.tableSize))
    (rZeros : Apart (out, span) (zeros, 32 * (zeroHeights + 1)))
    {env : Env} {mem : Memory} {h W L : Nat}
    (st : ColAt w out n count depth ctx table zeros pad span mask mem0 leaves env mem h W L 0)
    (pairing : h + depthFor W = depthFor n) (wSmall : W ≤ n) :
    Ends m w sp env mem colPairing fun e mm => ∃ L', ColAt w out n count depth ctx table zeros pad span mask mem0
      leaves e mm (depthFor n) 1 L' 0 := by
  -- The level shrinks every pass until one column is left.
  have ends := Ends.loop (m := m) (w := w) (sp := sp) (env := env) (mem := mem) (c := lt 1 RootColumns.w)
    (body := .block colPass)
    (fun e mm => ∃ h W L, ColAt w out n count depth ctx table zeros pad span mask mem0 leaves e mm h W L 0 ∧
      h + depthFor W = depthFor n ∧ W ≤ n)
    (fun e _ => (e 8).toNat) ⟨h, W, L, st, pairing, wSmall⟩
    (fun e mm ⟨_, W, _, s, _, wn⟩ => ⟨_, eval_lt (eval_lit 1) (eval_var s.widthV) (by decide) (by omega)⟩)
    (fun e mm c ⟨h, W, L, s, p, wn⟩ hc nz => by
      have c' := eval_lt (w := w) (env := e) (mem := mm) (a := (1 : Expr)) (b := RootColumns.w) (eval_lit 1)
        (eval_var s.widthV) (by decide) (by omega)
      rw [hc] at c'
      have big : 2 ≤ W := by
        by_cases b : 1 < W
        · exact b
        · rw [ite_eq_right b] at c'; cases c'; exact absurd rfl nz
      exact (colPass_ends hash room size hz nSmall deep hspan acc rPad rCtx rTable rZeros s p big wn).mono
        fun e' mm' ⟨L', s', p'⟩ => ⟨⟨h + 1, W / 2 + W % 2, L', s', p', by omega⟩, by
          rw [s'.widthV, s.widthV, ofNat_toNat (by omega), ofNat_toNat (by omega)]; omega⟩)
  obtain ⟨e, mm, run, ⟨h, W, L, s, p, _⟩, exit⟩ := ends
  -- The loop stops at one column, at the full height.
  have c' := eval_lt (w := w) (env := e) (mem := mm) (a := (1 : Expr)) (b := RootColumns.w) (eval_lit 1)
    (eval_var s.widthV) (by decide) (by omega)
  rw [exit] at c'
  have one : W = 1 := by
    by_cases b : 1 < W
    · rw [ite_eq_left b] at c'; cases c'
    · have := s.wide; omega
  subst one
  have d1 : depthFor 1 = 0 := by rw [depthFor]; simp
  rw [d1, Nat.add_zero] at p
  subst p
  exact ⟨e, mm, run, L, s⟩

/-! ### The climb -/

/--
The column tree driver's state while climbing: one column, a number of levels above the pairing's height.

The column lies after the columns with room for the climbs to come, or is the output after the last climb.
-/
structure ClimbAt (w : World) (out n count depth ctx table zeros pad span : Nat) (mask : UInt64) (mem0 : Memory)
    (leaves : Nat → Array Bytes) (env : Env) (mem : Memory) (j L : Nat) : Prop where
  /-- The kept variables. -/
  vars : ColEnv env out n count depth ctx zeros
  /-- The column's address. -/
  lvlV : env 7 = UInt64.ofNat L
  /-- The column's height. -/
  heightV : env 9 = UInt64.ofNat (depthFor n + j)
  /-- Where the next column may go: right after this one. -/
  nextV : env 10 = UInt64.ofNat (L + 32 * count)
  /-- The climbs so far. -/
  jV : env 18 = UInt64.ofNat j
  /-- No more climbs than the depth asks for. -/
  le : j ≤ depth - depthFor n
  /-- The column lies after the columns with room for the climbs to come, or is the output after the last one. -/
  place : (out + 32 * count ≤ L ∧ L + 3 * (32 * count) ≤ out + 32 * count + (3 * n + j) * (32 * count)) ∨
    (L = out ∧ j = depth - depthFor n)
  /-- It holds every record's root at its height. -/
  roots : ∀ i < count, nodeAt mem (L + 32 * i) = subtreeAt (leaves i) (depthFor n + j) 0
  /-- One tree of its height covers the leaves. -/
  covers : n ≤ 2 ^ (depthFor n + j)
  /-- The context stays filled. -/
  ready : RootReady w ctx table zeros pad mask mem
  /-- Memory is as at the start, outside the output's region and the padding area. -/
  frame : ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem a = mem0 a

/-- The statements between the pairing loop and the climbing loop. -/
abbrev colMid : List Stmt := [RootColumns.h ::= RootColumns.levels, RootColumns.j ::= 0]

/-- After the pairing, the climb starts at the pairing's height, with no climb done. -/
theorem colMid_runs {m : Module} {w : World} {sp : Nat} {out n count depth ctx table zeros pad span : Nat}
    {mask : UInt64} {mem0 : Memory} {leaves : Nat → Array Bytes} {env : Env} {mem : Memory} {L : Nat}
    (st : ColAt w out n count depth ctx table zeros pad span mask mem0 leaves env mem (depthFor n) 1 L 0) :
    Ends m w sp env mem (.block colMid) fun e mm =>
      ClimbAt w out n count depth ctx table zeros pad span mask mem0 leaves e mm 0 L := by
  have v := st.vars
  refine Ends.step (Runs.set' (eval_var v.levelsV)) (Ends.step (Runs.set' (eval_lit 0)) (Ends.nil ⟨?_, ?_, ?_, ?_,
    assign_eq, by omega, ?_, fun i hi => ?_, by simpa using st.covers, st.ready, st.frame⟩))
  · exact v.of_keep fun y hy => by rw [assign_ne (show y ≠ 18 by omega), assign_ne (show y ≠ 9 by omega)]
  · rw [assign_ne (by decide), assign_ne (by decide)]; exact st.lvlV
  · rw [assign_ne (by decide), assign_eq]; rfl
  · rw [assign_ne (by decide), assign_ne (by decide), st.nextV, Nat.one_mul]
  · rcases st.place with p | p
    · exact .inl ⟨p.1, by rw [Nat.one_mul] at p; exact p.2⟩
    · exact .inr ⟨p.1, p.2.2.symm⟩
  · have := st.roots 0 (by decide) i hi
    simpa using this

/-- The body of the column tree driver's climbing loop. -/
abbrev colClimb : List Stmt :=
  [ifElse (eq (RootColumns.j + 1) RootColumns.climbs) [RootColumns.dst ::= RootColumns.out]
      [RootColumns.dst ::= RootColumns.next],
    callInto RootColumns.sink "ssz_hash_fixed" [RootColumns.dst, RootColumns.lvl, RootColumns.zeros + 32 * RootColumns.h,
      RootColumns.count, RootColumns.ctx],
    RootColumns.lvl ::= RootColumns.dst, RootColumns.next ::= RootColumns.dst + RootColumns.cs,
    RootColumns.h ::= RootColumns.h + 1, RootColumns.j ::= RootColumns.j + 1]

set_option maxHeartbeats 1000000 in
/--
One climb hashes the column against the zero tree of its height, a level up.

The new column lands right after the old one, or in the output for the last climb.
-/
theorem colClimb_ends {m : Module} {w : World} (hash : HashingOk m w) {sp : Nat} (room : w.stackLo + hashStack ≤ sp)
    {out n count depth ctx table zeros pad span : Nat} {mask : UInt64} {mem0 : Memory} {leaves : Nat → Array Bytes}
    (size : ∀ i < count, (leaves i).size = n) (hz : depth ≤ zeroHeights)
    (hspan : 32 * count + (3 * n + (depth - depthFor n)) * (32 * count) ≤ span)
    (acc : w.access out span = true) (rPad : Apart (out, span) (pad, 1536)) (rCtx : Apart (out, span) (ctx, 32))
    (rTable : Apart (out, span) (table, Kernel.tableSize))
    (rZeros : Apart (out, span) (zeros, 32 * (zeroHeights + 1)))
    {env : Env} {mem : Memory} {j L : Nat}
    (st : ClimbAt w out n count depth ctx table zeros pad span mask mem0 leaves env mem j L)
    (more : j < depth - depthFor n) :
    Ends m w sp env mem (.block colClimb) fun e mm =>
      ∃ L', ClimbAt w out n count depth ctx table zeros pad span mask mem0 leaves e mm (j + 1) L' := by
  have ae := access_end acc
  have rp := rPad
  simp only [Apart] at rp
  have hz64 : zeroHeights = 64 := rfl
  have v := st.vars
  have place : out + 32 * count ≤ L ∧ L + 3 * (32 * count) ≤ out + 32 * count + (3 * n + j) * (32 * count) := by
    rcases st.place with p | p
    · exact p
    · omega
  have room3 : (3 * n + j) * (32 * count) + 32 * count ≤ (3 * n + (depth - depthFor n)) * (32 * count) := by
    have := Nat.mul_le_mul_right (32 * count) (show 3 * n + j + 1 ≤ 3 * n + (depth - depthFor n) by omega)
    rwa [Nat.add_mul, Nat.one_mul] at this
  have succ : (3 * n + (j + 1)) * (32 * count) = (3 * n + j) * (32 * count) + 32 * count := by
    rw [← Nat.add_assoc, Nat.add_mul, Nat.one_mul]
  -- Where the new column goes: the output for the last climb, and right after the old one otherwise.
  obtain ⟨D, hD⟩ : ∃ D, D = if j + 1 = depth - depthFor n then out else L + 32 * count := ⟨_, rfl⟩
  have s1 : Runs m w sp env mem (ifElse (eq (RootColumns.j + 1) RootColumns.climbs) [RootColumns.dst ::= RootColumns.out]
      [RootColumns.dst ::= RootColumns.next]) (Asm.assign env 13 (UInt64.ofNat D)) mem := by
    have c := eval_eq_nat (w := w) (env := env) (mem := mem) (a := RootColumns.j + 1) (b := RootColumns.climbs)
      (eval_add (eval_var st.jV) (eval_lit 1)) (eval_var v.climbsV) (by omega) (by omega)
    by_cases last : j + 1 = depth - depthFor n
    · rw [ite_eq_left last] at c
      rw [hD, ite_eq_left last]
      exact Runs.ifElse_true 1 c (by decide) (Runs.block_cons (Runs.set' (eval_var v.outV)) (Runs.block_nil _ _ _ _ _))
    · rw [ite_eq_right last] at c
      rw [hD, ite_eq_right last]
      exact Runs.ifElse_false c (Runs.block_cons (Runs.set' (eval_var st.nextV)) (Runs.block_nil _ _ _ _ _))
  have dIn : out ≤ D ∧ D + 32 * count ≤ out + span ∧ (D + 32 * count ≤ L ∨ L + 32 * count ≤ D) := by
    rw [hD]; split <;> omega
  -- The climb: the column against the zero tree of its height.
  let E1 := Asm.assign env 13 (UInt64.ofNat D)
  have keep1 : ∀ y, y ≠ 13 → E1 y = env y := fun y hy => assign_ne hy
  have pre : RunPre w mem 32 0 D L (zeros + 32 * (depthFor n + j)) count ctx table pad mask :=
    st.ready.runPreZero acc rPad rCtx rTable rZeros ⟨dIn.1, dIn.2.1⟩ ⟨by omega, by omega⟩ dIn.2.2 (by omega)
  obtain ⟨mem1, call, after⟩ := (hash.fixed sp mem _ _ _ count ctx table pad mask pre st.ready.kernels room)
  have callRuns := Runs.call (m := m) (sp := sp) (env := E1) (mem := mem) (dst := 17)
    (args := [RootColumns.dst, RootColumns.lvl, RootColumns.zeros + 32 * RootColumns.h, RootColumns.count,
      RootColumns.ctx])
    (eval_five (eval_var (assign_eq (env := env)))
      (eval_var (by rw [keep1 7 (by decide)]; exact st.lvlV))
      (eval_add (eval_var (by rw [keep1 16 (by decide)]; exact v.zerosV))
        (eval_mul (eval_lit 32) (eval_var (by rw [keep1 9 (by decide)]; exact st.heightV))))
      (eval_var (by rw [keep1 2 (by decide)]; exact v.countV))
      (eval_var (by rw [keep1 4 (by decide)]; exact v.ctxV))) call
  let E2 := Asm.assign E1 17 0
  have e2dst : E2 13 = UInt64.ofNat D := by simp only [E2, E1]; rw [assign_ne (by decide)]; exact assign_eq
  have s3 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem1) (x := 7) (env := E2) (e := RootColumns.dst)
    (eval_var e2dst)
  let E3 := Asm.assign E2 7 (UInt64.ofNat D)
  have s4 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem1) (x := 10) (env := E3)
    (e := RootColumns.dst + RootColumns.cs)
    (eval_add (eval_var (show E3 13 = UInt64.ofNat D by simp only [E3]; rw [assign_ne (by decide)]; exact e2dst))
      (eval_var (show E3 6 = UInt64.ofNat (32 * count) by
        simp only [E3, E2, E1]; rw [assign_ne (by decide), assign_ne (by decide), assign_ne (by decide)]; exact v.csV)))
  let E4 := Asm.assign E3 10 (UInt64.ofNat (D + 32 * count))
  have s5 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem1) (x := 9) (env := E4) (e := RootColumns.h + 1)
    (eval_add (eval_var (show E4 9 = UInt64.ofNat (depthFor n + j) by
      simp only [E4, E3, E2, E1]
      rw [assign_ne (by decide), assign_ne (by decide), assign_ne (by decide), assign_ne (by decide)]
      exact st.heightV)) (eval_lit 1))
  let E5 := Asm.assign E4 9 (UInt64.ofNat (depthFor n + j + 1))
  have s6 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem1) (x := 18) (env := E5) (e := RootColumns.j + 1)
    (eval_add (eval_var (show E5 18 = UInt64.ofNat j by
      simp only [E5, E4, E3, E2, E1]
      rw [assign_ne (by decide), assign_ne (by decide), assign_ne (by decide), assign_ne (by decide),
        assign_ne (by decide)]
      exact st.jV)) (eval_lit 1))
  let E6 := Asm.assign E5 18 (UInt64.ofNat (j + 1))
  have frame1 : ∀ a, ¬ (D ≤ a ∧ a < D + 32 * count) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem1 a = mem a :=
    fun a o p => by rw [after a p, hashed_outside o]
  refine ⟨E6, mem1, Runs.block_cons s1 (Runs.block_cons callRuns (Runs.block_cons s3 (Runs.block_cons s4
    (Runs.block_cons s5 (Runs.block_cons s6 (Runs.block_nil _ _ _ _ _)))))), D, ⟨?_, ?_, ?_, ?_, assign_eq, by omega,
    ?_, fun i hi => ?_, ?_, ?_, fun a o p => ?_⟩⟩
  · exact v.of_keep fun y hy => by
      simp only [E6, E5, E4, E3, E2, E1]
      rw [assign_ne (by omega), assign_ne (by omega), assign_ne (by omega), assign_ne (by omega),
        assign_ne (by omega), assign_ne (by omega)]
  · simp only [E6, E5, E4]; rw [assign_ne (by decide), assign_ne (by decide), assign_ne (by decide)]; exact assign_eq
  · simp only [E6, E5]; rw [assign_ne (by decide), assign_eq]; rfl
  · simp only [E6, E5, E4]; rw [assign_ne (by decide), assign_ne (by decide), assign_eq]
  · -- The last climb lands in the output; any other right after the old column, with room for the rest.
    rw [hD]
    by_cases last : j + 1 = depth - depthFor n
    · rw [ite_eq_left last]; exact .inr ⟨rfl, last⟩
    · rw [ite_eq_right last]; exact .inl ⟨by omega, by rw [succ]; omega⟩
  · -- The new node: the old one against the zero tree.
    have zero : nodeAt mem (zeros + 32 * (depthFor n + j)) = zeroSubtree (depthFor n + j) :=
      nodeAt_zeros st.ready.zeroRoots _ (by omega)
    have up := parent_last (leaves i) (depthFor n + j) 1 rfl (by rw [size i hi, Nat.one_mul]; exact st.covers)
    simp only [Nat.sub_self, Nat.zero_mul, show (1 : Nat) / 2 = 0 from rfl] at up
    have e := nodeAt_hashed mem D L (zeros + 32 * (depthFor n + j)) count 32 0 i hi
    simp only [Nat.zero_mul, Nat.add_zero] at e
    rw [nodeAt_congr (m₂ := hashed mem D L (zeros + 32 * (depthFor n + j)) count 32 0)
      fun k hk => after _ (by omega), e, zero, st.roots i hi, up]
    rfl
  · exact Nat.le_trans st.covers (Nat.pow_le_pow_right (by decide) (by omega))
  · exact st.ready.region rCtx rTable rZeros fun a o p => frame1 a (by omega) p
  · rw [frame1 a (by omega) p]; exact st.frame a o p

/-- Nodes at two places agree when their bytes do. -/
theorem nodeAt_moved {m₁ m₂ : Memory} {a b : Nat} (h : ∀ k < 32, m₁ (a + k) = m₂ (b + k)) :
    nodeAt m₁ a = nodeAt m₂ b := by
  unfold nodeAt
  congr 1
  funext k
  exact h k.val k.isLt

/-- The climbing loop of the column tree driver. -/
abbrev colClimbing : Stmt := while_ (lt RootColumns.j RootColumns.climbs) colClimb

/-- The climbing loop runs until the column reaches the depth asked for. -/
theorem colClimbing_ends {m : Module} {w : World} (hash : HashingOk m w) {sp : Nat}
    (room : w.stackLo + hashStack ≤ sp) {out n count depth ctx table zeros pad span : Nat} {mask : UInt64}
    {mem0 : Memory} {leaves : Nat → Array Bytes} (size : ∀ i < count, (leaves i).size = n) (hz : depth ≤ zeroHeights)
    (hspan : 32 * count + (3 * n + (depth - depthFor n)) * (32 * count) ≤ span)
    (acc : w.access out span = true) (rPad : Apart (out, span) (pad, 1536)) (rCtx : Apart (out, span) (ctx, 32))
    (rTable : Apart (out, span) (table, Kernel.tableSize))
    (rZeros : Apart (out, span) (zeros, 32 * (zeroHeights + 1)))
    {env : Env} {mem : Memory} {L : Nat}
    (st : ClimbAt w out n count depth ctx table zeros pad span mask mem0 leaves env mem 0 L) :
    Ends m w sp env mem colClimbing fun e mm => ∃ L', ClimbAt w out n count depth ctx table zeros pad span mask mem0
      leaves e mm (depth - depthFor n) L' := by
  have hz64 : zeroHeights = 64 := rfl
  -- Each climb brings the count of climbs done one closer to the count asked for.
  have ends := Ends.loop (m := m) (w := w) (sp := sp) (env := env) (mem := mem)
    (c := lt RootColumns.j RootColumns.climbs) (body := .block colClimb)
    (fun e mm => ∃ j L, ClimbAt w out n count depth ctx table zeros pad span mask mem0 leaves e mm j L)
    (fun e _ => depth - depthFor n - (e 18).toNat) ⟨0, L, st⟩
    (fun e mm ⟨j, _, s⟩ => ⟨_, eval_lt (eval_var s.jV) (eval_var s.vars.climbsV) (by have := s.le; omega)
      (by omega)⟩)
    (fun e mm c ⟨j, L, s⟩ hc nz => by
      have c' := eval_lt (w := w) (env := e) (mem := mm) (a := RootColumns.j) (b := RootColumns.climbs)
        (eval_var s.jV) (eval_var s.vars.climbsV) (by have := s.le; omega) (by omega)
      rw [hc] at c'
      have more : j < depth - depthFor n := by
        by_cases b : j < depth - depthFor n
        · exact b
        · rw [ite_eq_right b] at c'; cases c'; exact absurd rfl nz
      exact (colClimb_ends hash room size hz hspan acc rPad rCtx rTable rZeros s more).mono
        fun e' mm' ⟨L', s'⟩ => ⟨⟨j + 1, L', s'⟩, by
          rw [s'.jV, s.jV, ofNat_toNat (by omega), ofNat_toNat (by omega)]; omega⟩)
  obtain ⟨e, mm, run, ⟨j, L, s⟩, exit⟩ := ends
  -- The loop stops once every climb is done.
  have c' := eval_lt (w := w) (env := e) (mem := mm) (a := RootColumns.j) (b := RootColumns.climbs)
    (eval_var s.jV) (eval_var s.vars.climbsV) (by have := s.le; omega) (by omega)
  rw [exit] at c'
  have done : j = depth - depthFor n := by
    by_cases b : j < depth - depthFor n
    · rw [ite_eq_left b] at c'; cases c'
    · have := s.le; omega
  subst done
  exact ⟨e, mm, run, L, s⟩

/-- The column tree driver's last statement: a lone column with nothing to climb is copied into the output. -/
abbrev colEnd : Stmt :=
  when (ne RootColumns.lvl RootColumns.out)
    [callInto RootColumns.sink "ssz_gather" [RootColumns.out, RootColumns.lvl, 1, RootColumns.cs, 0, 0]]

/-- After the climb, the output holds every record's root, copied there when the column lies elsewhere. -/
theorem colEnd_ends {m : Module} {w : World} (gmod : GatherModule m) {sp : Nat} (room : w.stackLo + 8 ≤ sp)
    {out n count depth ctx table zeros pad span : Nat} {mask : UInt64} {mem0 : Memory} {leaves : Nat → Array Bytes}
    (hspan : 32 * count + (3 * n + (depth - depthFor n)) * (32 * count) ≤ span) (deep : depthFor n ≤ depth)
    (acc : w.access out span = true) (rPad : Apart (out, span) (pad, 1536)) (rCtx : Apart (out, span) (ctx, 32))
    (rTable : Apart (out, span) (table, Kernel.tableSize))
    (rZeros : Apart (out, span) (zeros, 32 * (zeroHeights + 1)))
    {env : Env} {mem : Memory} {L : Nat}
    (st : ClimbAt w out n count depth ctx table zeros pad span mask mem0 leaves env mem (depth - depthFor n) L) :
    Ends m w sp env mem colEnd fun _ mm => (∀ i < count, nodeAt mm (out + 32 * i) = subtreeAt (leaves i) depth 0) ∧
      RootReady w ctx table zeros pad mask mm ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm a = mem0 a := by
  have ae := access_end acc
  have v := st.vars
  have hd : depthFor n + (depth - depthFor n) = depth := by omega
  have roots := st.roots
  rw [hd] at roots
  have lSmall : L < 2 ^ 64 := by rcases st.place with p | p <;> omega
  have c := eval_ne (w := w) (env := env) (mem := mem) (a := RootColumns.lvl) (b := RootColumns.out)
    (eval_var st.lvlV) (eval_var v.outV)
  by_cases same : L = out
  · -- The column already is the output.
    subst same
    rw [ite_eq_left rfl] at c
    exact ⟨env, mem, Runs.when_false c, roots, st.ready, st.frame⟩
  · -- The column lies after the columns: copy it into the output.
    rw [ite_eq_right fun h => same ((ofNat_inj lSmall (by omega)).mp h)] at c
    have place : out + 32 * count ≤ L ∧ L + 3 * (32 * count) ≤
        out + 32 * count + (3 * n + (depth - depthFor n)) * (32 * count) := by
      rcases st.place with p | p
      · exact p
      · exact absurd p.1 same
    have pre : GatherPre w out L 1 (32 * count) 0 0 := by
      refine ⟨?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
      · exact access_sub acc (Nat.le_refl _) (by omega)
      · obtain rfl : i = 0 := by omega
        exact access_sub acc (by omega) (by omega)
      · simp only [addressBound]; omega
      · obtain rfl : i = 0 := by omega
        simp only [Apart]; omega
    have call := gather_call (m := m) (w := w) (sp := sp) (mem := mem) (out := UInt64.ofNat out)
      (src := UInt64.ofNat L) (count := 1) (width := UInt64.ofNat (32 * count)) (skip := 0) (pad := 0)
      gmod.general (Kernel.runs_gather w.cpu) (by simp)
      (by rw [ofNat_toNat (by omega), ofNat_toNat lSmall, ofNat_toNat (by omega)]; exact pre) room
    rw [ofNat_toNat (by omega), ofNat_toNat lSmall, ofNat_toNat (by omega)] at call
    have args : ([RootColumns.out, RootColumns.lvl, 1, RootColumns.cs, 0, 0] : List Expr).mapM
        (eval w env mem) = some [UInt64.ofNat out, UInt64.ofNat L, 1, UInt64.ofNat (32 * count), 0, 0] := by
      simp only [List.mapM_cons, List.mapM_nil, eval_var v.outV, eval_var st.lvlV, eval_var v.csV]
      rfl
    have callRuns := Runs.call (dst := 17) args call
    -- The copy changes only the output's first column.
    have frame1 : ∀ a, ¬ (out ≤ a ∧ a < out + 32 * count) →
        gathered mem out L (UInt64.toNat 1) (32 * count) (UInt64.toNat 0) (UInt64.toNat 0) a = mem a := by
      intro a o
      simp only [gathered]
      rw [ite_eq_right (by simp; omega)]
    refine ⟨_, _, Runs.when_true 1 c (by decide) (Runs.block_cons callRuns (Runs.block_nil _ _ _ _ _)),
      fun i hi => ?_, st.ready.region rCtx rTable rZeros fun a o p => frame1 a (by omega), fun a o p => ?_⟩
    · -- Node i of the output is node i of the column.
      rw [← roots i hi]
      refine nodeAt_moved fun k hk => ?_
      have rb := Kernel.recordByte_at mem out L (32 * count) 0 0 0 (32 * i + k) (by omega)
      simp only [Nat.add_zero, Nat.mul_zero] at rb
      simp only [gathered, show UInt64.toNat 1 = 1 from rfl, show UInt64.toNat 0 = 0 from rfl, Nat.add_zero,
        Nat.mul_one]
      rw [ite_eq_left ⟨by omega, by omega⟩, Nat.add_assoc, rb, ite_eq_left (by omega), Nat.add_assoc]
    · rw [frame1 a (by omega)]; exact st.frame a o p

/-! ### The driver -/

/-- The column tree driver's frame holds twenty-five words. -/
theorem colFrame : RootColumns.fn.frame = 25 := by decide

/-- The stack a call to the column tree driver needs: its return address and frame, then a hashing driver's call. -/
abbrev columnsStack : Nat := 208 + hashStack

/-- The column tree driver's body, in its parts. -/
theorem colBody : RootColumns.fn.body = .block (colStart ++ [colPairing] ++ colMid ++ [colClimbing, colEnd]) := rfl

set_option maxHeartbeats 1000000 in
/--
The column tree driver writes, at the output, every record's root over its leaves at the depth asked for.

Leaf c of record i is node i of column c, and the columns lie one after the other right after the output.
The levels go after the columns, inside a region that leaves room for them.
Memory changes only in that region and in the padding area, and the context stays filled.
-/
theorem rootColumns_nodes {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m)
    (hd : m.fns.lookup "ssz_depth_for" = some DepthFor.fn) (hf : m.fns.lookup "ssz_root_columns" = some RootColumns.fn)
    {sp : Nat} (room : w.stackLo + columnsStack ≤ sp) {mem : Memory} {ctx table zeros pad : Nat} {mask : UInt64}
    (rd : RootReady w ctx table zeros pad mask mem) {out n count depth span : Nat} (n1 : 1 ≤ n) (nSmall : n < 2 ^ 64)
    (deep : depthFor n ≤ depth) (hz : depth ≤ zeroHeights)
    (hspan : 32 * count + (3 * n + (depth - depthFor n)) * (32 * count) ≤ span)
    (acc : w.access out span = true) (rPad : Apart (out, span) (pad, 1536)) (rCtx : Apart (out, span) (ctx, 32))
    (rTable : Apart (out, span) (table, Kernel.tableSize))
    (rZeros : Apart (out, span) (zeros, 32 * (zeroHeights + 1))) :
    ∃ mem', Calls m w "ssz_root_columns" sp [UInt64.ofNat (out + 32 * count), UInt64.ofNat n, UInt64.ofNat count,
        UInt64.ofNat depth, UInt64.ofNat ctx] mem 0 mem' ∧
      (∀ i < count, nodeAt mem' (out + 32 * i) =
        subtreeAt (colLeaves mem (out + 32 * count) (32 * count) n i) depth 0) ∧
      RootReady w ctx table zeros pad mask mem' ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a := by
  have frame := colFrame
  have stack : hashStack = 10392 := rfl
  have cstack : columnsStack = 208 + 10392 := rfl
  have hz64 : zeroHeights = 64 := rfl
  let sp' := sp - 8 - 8 * RootColumns.fn.frame
  have inner : w.stackLo + hashStack ≤ sp' := by simp only [sp']; rw [frame]; omega
  let leaves := colLeaves mem (out + 32 * count) (32 * count) n
  have size : ∀ i < count, (leaves i).size = n := fun i _ => colLeaves_size _ _ _ _ _
  -- The start, then the first level: the columns themselves.
  obtain ⟨E0, start, v, e7, e8, e9, e10⟩ := colStart_runs (m := m) hd (sp := sp') (by simp only [sp']; rw [frame]; omega)
    rd (out := out) (count := count) (depth := depth) nSmall (by omega)
  have st0 : ColAt w out n count depth ctx table zeros pad span mask mem leaves E0 mem 0 n (out + 32 * count) 0 := by
    refine ⟨v, e7, e8, e9, e10, n1, .inl ⟨Nat.le_refl _, ?_⟩, fun c hc i hi => ?_, by simp, by simp; omega, rd,
      fun _ _ _ => rfl⟩
    · rw [Nat.add_zero, Nat.mul_assoc]; omega
    · exact (colLeaves_leaf mem _ _ _ i hc).symm
  have pairs := colPairing_ends hash inner size hz nSmall deep hspan acc rPad rCtx rTable rZeros st0 (Nat.zero_add _)
    (Nat.le_refl _)
  obtain ⟨E1, M1, r1, L1, st1⟩ := pairs
  obtain ⟨E2, M2, r2, st2⟩ := colMid_runs (m := m) (sp := sp') st1
  obtain ⟨E3, M3, r3, L3, st3⟩ := colClimbing_ends hash inner size hz hspan acc rPad rCtx rTable rZeros st2
  obtain ⟨E4, M4, r4, roots, ready, keep⟩ := colEnd_ends (sp := sp') gmod (by simp only [sp']; rw [frame]; omega) hspan deep acc
    rPad rCtx rTable rZeros st3
  have body : Runs m w sp' (entryEnv [UInt64.ofNat (out + 32 * count), UInt64.ofNat n, UInt64.ofNat count,
      UInt64.ofNat depth, UInt64.ofNat ctx]) mem RootColumns.fn.body E4 M4 := by
    rw [colBody]
    exact Runs.block_append (Runs.block_append (Runs.block_append start (Runs.block_cons r1
      (Runs.block_nil _ _ _ _ _)))
      r2) (Runs.block_cons r3 (Runs.block_cons r4 (Runs.block_nil _ _ _ _ _)))
  exact ⟨M4, Calls.fn hf (by rw [frame]; omega) rfl body rfl, roots, ready, keep⟩

/--
The column tree driver computes the Lean tree over columns held in memory, one after the other right after the output.

The tree's root column lands at the output.
Memory changes only in the region after the output and in the padding area, and the context stays filled.
-/
theorem rootColumns_calls {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m)
    (hd : m.fns.lookup "ssz_depth_for" = some DepthFor.fn) (hf : m.fns.lookup "ssz_root_columns" = some RootColumns.fn)
    {sp : Nat} (room : w.stackLo + columnsStack ≤ sp) {mem : Memory} {ctx table zeros pad : Nat} {mask : UInt64}
    (rd : RootReady w ctx table zeros pad mask mem) {out count depth span : Nat} (columns : List ByteArray)
    (sized : ∀ c (hc : c < columns.length), columns[c].size = 32 * count)
    (held : ∀ c (hc : c < columns.length), Holds mem (out + 32 * count + c * (32 * count)) columns[c])
    (n1 : 1 ≤ columns.length) (nSmall : columns.length < 2 ^ 64) (deep : depthFor columns.length ≤ depth)
    (hz : depth ≤ zeroHeights) (small : 32 * count < USize.size)
    (hspan : 32 * count + (3 * columns.length + (depth - depthFor columns.length)) * (32 * count) ≤ span)
    (acc : w.access out span = true) (rPad : Apart (out, span) (pad, 1536)) (rCtx : Apart (out, span) (ctx, 32))
    (rTable : Apart (out, span) (table, Kernel.tableSize))
    (rZeros : Apart (out, span) (zeros, 32 * (zeroHeights + 1))) :
    ∃ mem', Calls m w "ssz_root_columns" sp [UInt64.ofNat (out + 32 * count), UInt64.ofNat columns.length,
        UInt64.ofNat count, UInt64.ofNat depth, UInt64.ofNat ctx] mem 0 mem' ∧
      Holds mem' out (columnTreeTo columns count depth) ∧ RootReady w ctx table zeros pad mask mem' ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a := by
  obtain ⟨mem', call, roots, ready, keep⟩ := rootColumns_nodes hash gmod hd hf room rd n1 nSmall deep hz hspan acc
    rPad rCtx rTable rZeros
  -- Leaf c of record i is node i of column c, as memory holds it.
  have tableEntry : ColumnsAt columns count 0 (colLeaves mem (out + 32 * count) (32 * count) columns.length) 0 :=
    ⟨sized, fun c hc i hi => by
      rw [Nat.zero_add, colLeaves_leaf mem _ _ _ i hc, ← nodeAt_of_holds (held c hc) (by rw [sized c hc]; omega)]⟩
  have spec := columnTreeTo_spec columns count depth _ small (fun _ _ => colLeaves_size _ _ _ _ _) n1 tableEntry deep
  exact ⟨mem', call, holds_of_nodes spec.1 fun i hi => by rw [roots i hi, spec.2 i hi], ready, keep⟩

end EthLib.Consensus.Ssz.Native.Driver
