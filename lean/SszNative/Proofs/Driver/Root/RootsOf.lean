import SszNative.Proofs.Driver.Root.Need

/-!
The fixed-size roots driver computes the Lean roots of fixed-size values.

The driver reads the type's plan node and takes one of five paths.
Basic elements, and every type that is not a vector or a container, pack.
A vector or container of one record roots its elements or fields side by side, then their tree.
Several records root one column per element or field, then the tree across the columns.

The driver calls itself on the element or field types, so the proof is an induction on the type.
What one call does is a contract, stated here once and proved for every plain type.
-/

namespace Ssz.Native.Driver

open Ssz.Native.Ir Ssz.Native.Ir.Expr Ssz.Native.Ir.Stmt Ssz.Native.Asm

/-! ### The contract -/

/-- The fixed-size roots driver's frame holds twenty-seven words. -/
theorem rootsFrame : RootsOf.fn.frame = 27 := by decide

/--
The stack a call to the fixed-size roots driver needs.

The deepest call below it takes the column tree's stack, more than the packed or the tree path.
Each level of nesting adds a frame of the driver and one of the chunked driver.
-/
def rootsStack (d : Desc) : Nat := columnsStack + 352 * d.nesting

/--
What a call rooting values of a fixed-size type needs.

The context is filled, and the plan and the values are in memory.
The values lie one stride apart, and the output region holds as many bytes as the scratch bound gives.
The values' strides end below the address bound with room for one more value.
The output region misses the values, the plan, the context's buffers, and the padding area.
-/
structure RootsPre (w : World) (mem : Memory) (d : Desc) (p base start stride count out ctx table zeros pad : Nat)
    (mask : UInt64) (b : ByteArray) : Prop where
  /-- The context is filled. -/
  ready : RootReady w ctx table zeros pad mask mem
  /-- The type's plan is in memory. -/
  plan : WordsAt w mem p (Plan.words d)
  /-- The values' buffer is in memory. -/
  holds : Holds mem base b
  /-- The values' buffer is usable. -/
  bAcc : w.access base b.size = true
  /-- A value fits its stride. -/
  gap : fixedWidth d ≤ stride
  /-- The stride is far below the word size. -/
  strideSmall : stride < 2 ^ 63
  /-- There is at least one value. -/
  pos : 1 ≤ count
  /-- Every value lies inside the buffer. -/
  inside : ∀ i < count, start + stride * i + fixedWidth d ≤ b.size
  /-- The values' strides, and one more value, end below the address bound. -/
  spread : base + start + stride * count + fixedWidth d ≤ addressBound
  /-- The scratch bound is below the cap. -/
  below : rootsNeed d count < scratchCap
  /-- The output region is usable. -/
  acc : w.access out (rootsNeed d count) = true
  /-- The output region ends a node short of the address bound. -/
  slack : out + rootsNeed d count + 32 ≤ addressBound
  /-- The output region misses the values. -/
  oB : Apart (out, rootsNeed d count) (base, b.size)
  /-- It misses the padding area. -/
  oPad : Apart (out, rootsNeed d count) (pad, 1536)
  /-- It misses the context. -/
  oCtx : Apart (out, rootsNeed d count) (ctx, 32)
  /-- It misses the table. -/
  oTable : Apart (out, rootsNeed d count) (table, Kernel.tableSize)
  /-- It misses the zero roots. -/
  oZeros : Apart (out, rootsNeed d count) (zeros, 32 * (zeroHeights + 1))
  /-- It misses the plan. -/
  oPlan : Apart (out, rootsNeed d count) (p, 8 * (Plan.words d).length)
  /-- The values miss the padding area. -/
  bPad : Apart (base, b.size) (pad, 1536)
  /-- The plan misses the padding area. -/
  planPad : Apart (p, 8 * (Plan.words d).length) (pad, 1536)
  /-- A machine word holds a full 64-bit size. -/
  usize : USize.size = 2 ^ 64

/-- The values' strides end below the address bound. -/
theorem RootsPre.reach {w : World} {mem : Memory} {d : Desc} {p base start stride count out ctx table zeros pad : Nat}
    {mask : UInt64} {b : ByteArray} (pre : RootsPre w mem d p base start stride count out ctx table zeros pad mask b) :
    base + start + stride * count ≤ addressBound := by
  have := pre.spread; omega

/--
What a call rooting values leaves: the roots at the output, the context still filled, and memory as it was outside
the output region and the padding area.
-/
def RootsPost (w : World) (mem mem' : Memory) (out span ctx table zeros pad : Nat) (mask : UInt64)
    (roots : ByteArray) : Prop :=
  Holds mem' out roots ∧ RootReady w ctx table zeros pad mask mem' ∧
    ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a

/-- A type the fixed-size roots driver serves: plain, well formed, and of a width far below the word size. -/
def Rootable (d : Desc) : Prop := plain d = true ∧ d.wellFormed = .ok () ∧ narrow d = true

/-- The fixed-size roots driver computes the Lean roots of values of a type, from any state meeting its needs. -/
def RootsOfOk (m : Module) (w : World) (d : Desc) : Prop :=
  ∀ (sp : Nat) (mem : Memory) (p base start stride count out ctx table zeros pad : Nat) (mask : UInt64)
    (b : ByteArray), w.stackLo + rootsStack d ≤ sp →
    RootsPre w mem d p base start stride count out ctx table zeros pad mask b →
    ∃ mem', Calls m w "ssz_roots_of" sp [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat stride,
        UInt64.ofNat count, UInt64.ofNat out, UInt64.ofNat ctx] mem 0 mem' ∧
      RootsPost w mem mem' out (rootsNeed d count) ctx table zeros pad mask (rootsOf d b start stride count)

/-- The variables holding the driver's arguments. -/
structure RootsEnv (env : Env) (p src stride count out ctx : Nat) : Prop where
  /-- The plan node. -/
  p : env 0 = UInt64.ofNat p
  /-- The first value. -/
  src : env 1 = UInt64.ofNat src
  /-- The stride. -/
  stride : env 2 = UInt64.ofNat stride
  /-- The count. -/
  count : env 3 = UInt64.ofNat count
  /-- The output. -/
  out : env 4 = UInt64.ofNat out
  /-- The context. -/
  ctx : env 5 = UInt64.ofNat ctx

/-- Writing a variable past the arguments keeps them. -/
theorem RootsEnv.write {env : Env} {p src stride count out ctx : Nat} (h : RootsEnv env p src stride count out ctx)
    {x : Nat} (v : UInt64) (hx : 6 ≤ x) : RootsEnv (Asm.assign env x v) p src stride count out ctx :=
  ⟨by rw [assign_ne (by omega), h.p], by rw [assign_ne (by omega), h.src], by rw [assign_ne (by omega), h.stride],
    by rw [assign_ne (by omega), h.count], by rw [assign_ne (by omega), h.out], by rw [assign_ne (by omega), h.ctx]⟩

/-- The functions the fixed-size roots driver calls, each under its name. -/
structure RootsFns (m : Module) : Prop where
  /-- The plan readers. -/
  plan : PlanFns m
  /-- The packed roots driver. -/
  packed : m.fns.lookup "ssz_root_packed" = some RootPacked.fn
  /-- The column tree driver. -/
  columns : m.fns.lookup "ssz_root_columns" = some RootColumns.fn
  /-- The chunked roots driver. -/
  chunked : m.fns.lookup "ssz_roots_chunked" = some RootsChunked.fn
  /-- The fixed-size roots driver itself. -/
  roots : m.fns.lookup "ssz_roots_of" = some RootsOf.fn

/-! ### A child's needs -/

/-- An address inside a region apart from another lies outside the other. -/
theorem outside_of_apart {o n x k a : Nat} (h : Apart (o, n) (x, k)) (lo : x ≤ a) (hi : a < x + k) :
    ¬ (o ≤ a ∧ a < o + n) := by
  simp only [Apart] at h; omega

/-- An address inside a region apart from another lies outside the other, the regions named the other way. -/
theorem outside_of_apart' {o n x k a : Nat} (h : Apart (x, k) (o, n)) (lo : x ≤ a) (hi : a < x + k) :
    ¬ (o ≤ a ∧ a < o + n) := by
  simp only [Apart] at h; omega

/-- A region inside one apart from another is apart from it too. -/
theorem apart_sub {o n o₂ n₂ : Nat} {y : Nat × Nat} (h : Apart (o, n) y) (lo : o ≤ o₂) (hi : o₂ + n₂ ≤ o + n) :
    Apart (o₂, n₂) y := by
  simp only [Apart] at h ⊢; omega

/-- A region apart from one is apart from any region inside it. -/
theorem apart_sub' {x : Nat × Nat} {o n o₂ n₂ : Nat} (h : Apart x (o, n)) (lo : o ≤ o₂) (hi : o₂ + n₂ ≤ o + n) :
    Apart x (o₂, n₂) := by
  simp only [Apart] at h ⊢; omega

/-- Being apart goes both ways. -/
theorem apart_comm {x y : Nat × Nat} (h : Apart x y) : Apart y x := by
  simp only [Apart] at h ⊢; omega

/-- A plan stays in memory that agrees with the old memory on its words. -/
theorem planAt_congr {w : World} {m₁ m₂ : Memory} {p : Nat} {ws : List Nat} (h : WordsAt w m₁ p ws)
    (same : ∀ a, p ≤ a → a < p + 8 * ws.length → m₂ a = m₁ a) : WordsAt w m₂ p ws := by
  refine ⟨h.1, fun k hk => ⟨(h.2 k hk).1, ?_⟩⟩
  rw [readLE_congr m₂ m₁ (p + 8 * k) 8 fun i hi => same _ (by omega) (by omega)]
  exact (h.2 k hk).2

/--
A call's needs hold for a child call: a type whose plan lies inside the parent's, values inside the parent's buffer,
and an output region inside the parent's.

Memory may have changed since, but only inside the parent's output region and the padding area.
-/
theorem RootsPre.child {w : World} {mem mem₂ : Memory} {d e : Desc}
    {p base start stride count out ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : RootsPre w mem d p base start stride count out ctx table zeros pad mask b)
    (agree : ∀ a, ¬ (out ≤ a ∧ a < out + rootsNeed d count) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem₂ a = mem a)
    {p₂ start₂ stride₂ count₂ out₂ : Nat} (plan : WordsAt w mem p₂ (Plan.words e))
    (planIn : p ≤ p₂ ∧ p₂ + 8 * (Plan.words e).length ≤ p + 8 * (Plan.words d).length)
    (gap : fixedWidth e ≤ stride₂) (strideSmall : stride₂ < 2 ^ 63) (pos : 1 ≤ count₂)
    (inside : ∀ i < count₂, start₂ + stride₂ * i + fixedWidth e ≤ b.size)
    (spread : base + start₂ + stride₂ * count₂ + fixedWidth e ≤ addressBound) (below : rootsNeed e count₂ < scratchCap)
    (outIn : out ≤ out₂ ∧ out₂ + rootsNeed e count₂ ≤ out + rootsNeed d count) :
    RootsPre w mem₂ e p₂ base start₂ stride₂ count₂ out₂ ctx table zeros pad mask b := by
  have out_ := fun {x k a : Nat} (h : Apart (out, rootsNeed d count) (x, k)) (lo : x ≤ a) (hi : a < x + k) =>
    outside_of_apart h lo hi
  have pad_ := fun {x k a : Nat} (h : Apart (x, k) (pad, 1536)) (lo : x ≤ a) (hi : a < x + k) =>
    outside_of_apart' h lo hi
  have sub := fun {x k : Nat} (h : Apart (out, rootsNeed d count) (x, k)) => apart_sub h outIn.1 outIn.2
  refine ⟨pre.ready.frame fun a held => ?_,
    planAt_congr plan fun a lo hi => agree a (out_ pre.oPlan (by omega) (by omega))
      (pad_ pre.planPad (by omega) (by omega)),
    pre.holds.congr fun i hi => agree _ (out_ pre.oB (by omega) (by omega)) (pad_ pre.bPad (by omega) (by omega)),
    pre.bAcc, gap, strideSmall, pos, inside, spread, below, access_sub pre.acc outIn.1 outIn.2,
    by have := pre.slack; omega, sub pre.oB, sub pre.oPad, sub pre.oCtx, sub pre.oTable, sub pre.oZeros,
    apart_sub' (sub pre.oPlan) planIn.1 planIn.2, pre.bPad,
    apart_sub' (apart_comm pre.planPad) planIn.1 planIn.2 |> apart_comm, pre.usize⟩
  simp only [RootReady.Held] at held
  rcases held with h | h | h
  · exact agree a (out_ pre.oCtx h.1 h.2) (pad_ (apart_comm pre.ready.padCtx) h.1 h.2)
  · exact agree a (out_ pre.oTable h.1 h.2) (pad_ (apart_comm pre.ready.padTable) h.1 h.2)
  · exact agree a (out_ pre.oZeros h.1 h.2) (pad_ (apart_comm pre.ready.padZeros) h.1 h.2)

/-! ### Packing -/

/-- The statements that root packed values: the width, then the packed roots driver. -/
abbrev packedPath (x : Expr) : List Stmt :=
  [callInto RootsOf.w "ssz_plan_fixed_width" [x], callInto RootsOf.sink "ssz_root_packed"
    [RootsOf.w, RootsOf.src, RootsOf.stride, RootsOf.count, RootsOf.out, RootsOf.ctx]]

/--
Values whose roots pack are rooted by the packed roots driver, at the width the plan gives.

The plan read is the type's own node, or the vector's whole node for basic elements.
-/
theorem packedPath_runs {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RootsFns m)
    {sp : Nat} {mem : Memory} {d : Desc} {p base start stride count out ctx table zeros pad : Nat} {mask : UInt64}
    {b : ByteArray} (pre : RootsPre w mem d p base start stride count out ctx table zeros pad mask b)
    (ok : Rootable d) (room : w.stackLo + packedStack ≤ sp) (planRoom : w.stackLo + 112 * d.nesting ≤ sp)
    {env : Env} (ev : RootsEnv env p (base + start) stride count out ctx) {x : Expr}
    (hx : eval w env mem x = some (UInt64.ofNat p))
    (packs : rootsOf d b start stride count = packedRoots (fixedWidth d) (nodesFor (fixedWidth d)) b start stride count)
    (need : rootsNeed d count = packedNeed (satWidth d) count) :
    ∃ env' mem', Runs m w sp env mem (.block (packedPath x)) env' mem' ∧
      RootsPost w mem mem' out (rootsNeed d count) ctx table zeros pad mask (rootsOf d b start stride count) := by
  obtain ⟨pl, wf, thin⟩ := ok
  have wide := width_narrow d pl thin
  have sat := satWidth_plain d pl wide
  -- The bound is exactly the bytes the packed driver uses.
  have span : packedSpan (fixedWidth d) count = rootsNeed d count := by
    rw [need, ← sat]
    exact packedSpan_eq (by rw [← need]; exact pre.below)
  have width := planWidth_calls fns.plan d p sp mem pre.plan wf thin planRoom
  have r1 := Runs.call (m := m) (sp := sp) (env := env) (mem := mem) (dst := RootsOf.w.idx) (args := [x])
    (by simp only [List.mapM_cons, List.mapM_nil, hx]; rfl) width
  have e1 : RootsEnv (Asm.assign env 9 (fixedWidth d).toUInt64) p (base + start) stride count out ctx :=
    ev.write (x := 9) (fixedWidth d).toUInt64 (by decide)
  obtain ⟨mem', call, held, ready, keep⟩ := rootPacked_calls hash gmod fns.plan.depth fns.packed room pre.ready
    pre.holds pre.bAcc pre.gap pre.strideSmall (Nat.le_of_lt wide) pre.inside pre.reach (by rw [span]; exact pre.acc)
    (by rw [span]; exact pre.slack) (by rw [span]; exact pre.oB) (by rw [span]; exact pre.oPad)
    (by rw [span]; exact pre.oCtx) (by rw [span]; exact pre.oTable) (by rw [span]; exact pre.oZeros) pre.bPad pre.usize
  have r2 := Runs.call (m := m) (sp := sp) (env := Asm.assign env 9 (fixedWidth d).toUInt64) (mem := mem) (dst := RootsOf.sink.idx)
    (args := [RootsOf.w, RootsOf.src, RootsOf.stride, RootsOf.count, RootsOf.out, RootsOf.ctx])
    (by
      simp only [List.mapM_cons, List.mapM_nil, eval_var (show Asm.assign env 9 (fixedWidth d).toUInt64 9 = UInt64.ofNat (fixedWidth d) from assign_eq),
        eval_var e1.src, eval_var e1.stride, eval_var e1.count, eval_var e1.out, eval_var e1.ctx]
      rfl) call
  refine ⟨_, mem', Runs.block_cons r1 (Runs.block_cons r2 (Runs.block_nil _ _ _ _ _)), ?_, ready, ?_⟩
  · rw [packs]; exact held
  · intro a o pd
    exact keep a (by rw [span]; exact o) pd

end Ssz.Native.Driver
