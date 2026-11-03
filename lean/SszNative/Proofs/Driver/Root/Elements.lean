import SszNative.Proofs.Driver.Root.Grow
import SszNative.Proofs.Driver.Validate.Spans

/-!
The elements driver writes, node by node, the Lean roots of a sequence's elements.

Fixed-size elements sit one width apart, and the others run from their offset to the next one, the last to the end.
Each element is rooted by the dispatcher on the element type, into its node, with the bytes after the nodes as scratch.
What that call does is a hypothesis, the induction on the type.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Asm

/-! ### A child's needs -/

/--
A call rooting a range meets its needs when its output and scratch lie in a region apart from everything else.

The region is usable, ends a node short of the address bound, and misses the encoding, the plan, and the context's
buffers.
-/
theorem rangePre_of {w : World} {mem : Memory} {d : Desc} {p base start stop out scratch ctx table zeros pad : Nat}
    {mask : UInt64} {b : ByteArray} (ready : RootReady w ctx table zeros pad mask mem)
    (plan : WordsAt w mem p (Plan.words d)) (fits : Fits (Plan.words d)) (holds : Holds mem base b)
    (bAcc : w.access base b.size = true) (ordered : start ≤ stop) (inside : stop ≤ b.size) (small : RootProof.Small b)
    (spread : base + 2 * b.size ≤ addressBound) (sound : d.wellFormed = .ok ()) (thin : narrow d = true)
    (accepted : ∃ v, deserialize d (slice b start stop) = .ok v) (below : varNeed d (stop - start) < scratchCap)
    {lo span : Nat} (rAcc : w.access lo span = true) (rSlack : lo + span + 32 ≤ addressBound)
    (rB : Apart (lo, span) (base, b.size)) (rPad : Apart (lo, span) (pad, 1536)) (rCtx : Apart (lo, span) (ctx, 32))
    (rTable : Apart (lo, span) (table, Kernel.tableSize))
    (rZeros : Apart (lo, span) (zeros, 32 * (zeroHeights + 1)))
    (rPlan : Apart (lo, span) (p, 8 * (Plan.words d).length)) (bPad : Apart (base, b.size) (pad, 1536))
    (planPad : Apart (p, 8 * (Plan.words d).length) (pad, 1536))
    (oIn : lo ≤ out ∧ out + 32 ≤ lo + span) (sIn : lo ≤ scratch ∧ scratch + varNeed d (stop - start) ≤ lo + span)
    (sOut : Apart (scratch, varNeed d (stop - start)) (out, 32)) (usize : USize.size = 2 ^ 64) :
    RangePre w mem d p base start stop out scratch ctx table zeros pad mask b :=
  ⟨ready, plan, fits, holds, bAcc, ordered, inside, small, spread, sound, thin, accepted, below,
    access_sub rAcc sIn.1 sIn.2, by omega, access_sub rAcc oIn.1 oIn.2, apart_sub rB sIn.1 sIn.2, apart_sub rPad sIn.1 sIn.2,
    apart_sub rCtx sIn.1 sIn.2, apart_sub rTable sIn.1 sIn.2, apart_sub rZeros sIn.1 sIn.2,
    apart_sub rPlan sIn.1 sIn.2, sOut, apart_sub rB oIn.1 oIn.2, apart_sub rPad oIn.1 oIn.2,
    apart_sub rCtx oIn.1 oIn.2, apart_sub rTable oIn.1 oIn.2, apart_sub rZeros oIn.1 oIn.2,
    apart_sub rPlan oIn.1 oIn.2, bPad, planPad, usize⟩

/-! ### The element ranges -/

/-- Element i of a sequence: one width along for fixed-size elements, from its offset to the next one otherwise. -/
theorem elementRanges_getD (element : Desc) (b : ByteArray) (start stop count i : Nat) (hi : i < count) :
    (elementRanges element b start stop count).getD i (0, 0) =
      if hasWidth element then (start + i * fixedWidth element, start + (i + 1) * fixedWidth element)
      else (start + offsetAt b (start + i * bytesPerOffset),
        start + if i + 1 < count then offsetAt b (start + (i + 1) * bytesPerOffset) else stop - start) := by
  by_cases hw : hasWidth element = true
  · rw [ite_eq_left hw]
    simp only [elementRanges, fixedSize_eq, hw, ite_true]
    simp [List.getD_eq_getElem?_getD, hi]
  · rw [ite_eq_right hw]
    have hf : hasWidth element = false := by simpa using hw
    simp only [elementRanges, fixedSize_eq, hf, Bool.false_eq_true, ite_false]
    simp only [bodyRanges, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by simp; omega)]
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range, Option.map_some, Option.getD_some]
    congr 2
    by_cases h : i + 1 < count
    · rw [ite_eq_left h, List.getElem_append_left (by simp; omega)]
      simp
    · rw [ite_eq_right h, List.getElem_append_right (by simp; omega)]
      simp

/-- Four bytes a program may use, loaded. -/
theorem eval_ld4_of {w : World} {env : Env} {mem : Memory} {a : Expr} {n : Nat}
    (ha : eval w env mem a = some (UInt64.ofNat n)) (acc : w.access n 4 = true) :
    eval w env mem (ld4 a) = some (readLE mem n 4) := by
  have bn : n < 2 ^ 64 := by have := access_bound acc; omega
  show eval w env mem (.load .b4 a) = _
  simp only [eval, ha, Option.bind_eq_bind, Option.bind, ofNat_toNat bn, Width.bytes, acc]
  rfl

/-- Four bytes of a buffer in memory, read as the offset they hold. -/
theorem readLE_offsetAt {w : World} {mem : Memory} {base : Nat} {b : ByteArray} (holds : Holds mem base b)
    (bAcc : w.access base b.size = true) (i : Nat) (hi : i + 4 ≤ b.size) :
    readLE mem (base + i) 4 = UInt64.ofNat (offsetAt b i) :=
  Validate.DataAt.offset ⟨bAcc, fun j hj => by rw [holds j hj, Kernel.get!_eq _ _ hj]⟩ i hi

/-! ### The driver -/

/-- The elements driver's frame holds twenty-one words. -/
theorem elementsFrame : RootElements.fn.frame = 21 := by decide

/-- The range of element i of a sequence, as the Lean root reads it. -/
abbrev elemRange (element : Desc) (b : ByteArray) (start stop count i : Nat) : Nat × Nat :=
  (elementRanges element b start stop count).getD i (0, 0)

/-- What the elements driver needs: the element's plan, the encoding, the ranges' decoding, and a region apart. -/
structure ElemPre (w : World) (mem : Memory) (element : Desc) (ea base start stop count out span ctx table zeros pad : Nat)
    (mask : UInt64) (b : ByteArray) : Prop where
  /-- The context is filled. -/
  ready : RootReady w ctx table zeros pad mask mem
  /-- The element's plan is in memory. -/
  plan : WordsAt w mem ea (Plan.words element)
  /-- Its words fit machine words. -/
  fits : Fits (Plan.words element)
  /-- The encoding is in memory. -/
  holds : Holds mem base b
  /-- The encoding is usable. -/
  bAcc : w.access base b.size = true
  /-- The sequence's range runs forward. -/
  ordered : start ≤ stop
  /-- It lies inside the encoding. -/
  inside : stop ≤ b.size
  /-- Every buffer the root builds has machine-sized offsets. -/
  small : RootProof.Small b
  /-- Twice the encoding's size past its address stays below the address bound. -/
  spread : base + 2 * b.size ≤ addressBound
  /-- The element type is legal. -/
  sound : element.wellFormed = .ok ()
  /-- Its fixed-size parts are narrow. -/
  thin : narrow element = true
  /-- Each element's range lies inside the sequence's and decodes. -/
  ranges : ∀ i < count, start ≤ (elemRange element b start stop count i).1 ∧
    (elemRange element b start stop count i).1 ≤ (elemRange element b start stop count i).2 ∧
    (elemRange element b start stop count i).2 ≤ stop ∧
    ∃ v, deserialize element (slice b (elemRange element b start stop count i).1
      (elemRange element b start stop count i).2) = .ok v
  /-- The offsets of variable-size elements lie inside the sequence. -/
  offsets : hasWidth element = false → 0 < count → 4 * count ≤ stop - start
  /-- The region holds the roots, then the most an element's scratch needs. -/
  room : 32 * count + varNeed element (stop - start) ≤ span
  /-- That most is below the cap. -/
  below : varNeed element (stop - start) < scratchCap
  /-- The region is usable. -/
  rAcc : w.access out span = true
  /-- The region ends a node short of the address bound. -/
  rSlack : out + span + 32 ≤ addressBound
  /-- The region misses the encoding. -/
  rB : Apart (out, span) (base, b.size)
  /-- It misses the padding area. -/
  rPad : Apart (out, span) (pad, 1536)
  /-- It misses the context. -/
  rCtx : Apart (out, span) (ctx, 32)
  /-- It misses the table. -/
  rTable : Apart (out, span) (table, Kernel.tableSize)
  /-- It misses the zero roots. -/
  rZeros : Apart (out, span) (zeros, 32 * (zeroHeights + 1))
  /-- It misses the element's plan. -/
  rPlan : Apart (out, span) (ea, 8 * (Plan.words element).length)
  /-- The encoding misses the padding area. -/
  bPad : Apart (base, b.size) (pad, 1536)
  /-- The element's plan misses the padding area. -/
  planPad : Apart (ea, 8 * (Plan.words element).length) (pad, 1536)
  /-- A machine word holds a full 64-bit size. -/
  usize : USize.size = 2 ^ 64

/-- The elements driver's variables that stay: the arguments, the element's kind and width, and the scratch. -/
structure ElemEnv (env : Env) (element : Desc) (ea src size count out ctx : Nat) : Prop where
  /-- The element's plan. -/
  eV : env 0 = UInt64.ofNat ea
  /-- The sequence's address. -/
  srcV : env 1 = UInt64.ofNat src
  /-- Its size. -/
  sizeV : env 2 = UInt64.ofNat size
  /-- The count. -/
  countV : env 3 = UInt64.ofNat count
  /-- The output. -/
  outV : env 4 = UInt64.ofNat out
  /-- The context. -/
  ctxV : env 5 = UInt64.ofNat ctx
  /-- Whether the element has a fixed size. -/
  fxV : env 6 = bitOf (hasWidth element)
  /-- Its width. -/
  wV : env 7 = (fixedWidth element).toUInt64
  /-- The scratch after the roots. -/
  scrV : env 8 = UInt64.ofNat (out + 32 * count)

/-- Writing a working variable keeps the variables that stay. -/
theorem ElemEnv.write {env : Env} {element : Desc} {ea src size count out ctx : Nat}
    (h : ElemEnv env element ea src size count out ctx) {x : Nat} (v : UInt64) (hx : 9 ≤ x) :
    ElemEnv (Asm.assign env x v) element ea src size count out ctx :=
  ⟨by rw [assign_ne (by omega), h.eV], by rw [assign_ne (by omega), h.srcV], by rw [assign_ne (by omega), h.sizeV],
    by rw [assign_ne (by omega), h.countV], by rw [assign_ne (by omega), h.outV], by rw [assign_ne (by omega), h.ctxV],
    by rw [assign_ne (by omega), h.fxV], by rw [assign_ne (by omega), h.wV], by rw [assign_ne (by omega), h.scrV]⟩

/-- The elements driver's loop. -/
abbrev elemLoop : Stmt :=
  while_ (lt RootElements.i RootElements.count) [
    ifElse RootElements.fx [RootElements.s ::= RootElements.src + RootElements.w * RootElements.i,
        RootElements.n ::= RootElements.w]
      [RootElements.o ::= ld4 (RootElements.src + 4 * RootElements.i),
        ifElse (lt (RootElements.i + 1) RootElements.count)
          [RootElements.en ::= ld4 (RootElements.src + 4 * RootElements.i + 4)] [RootElements.en ::= RootElements.size],
        RootElements.s ::= RootElements.src + RootElements.o, RootElements.n ::= RootElements.en - RootElements.o],
    callInto RootElements.sink "ssz_root_of" [RootElements.e, RootElements.s, RootElements.n,
      RootElements.out + 32 * RootElements.i, RootElements.scr, RootElements.ctx],
    RootElements.i ::= RootElements.i + 1]

set_option maxHeartbeats 4000000 in
/-- Each pass of the elements loop roots the next element into its node. -/
theorem elemLoop_ends {m : Module} {w : World} {element : Desc} (ih : RootOfOk m w element) {sp : Nat}
    (room : w.stackLo + rootStack element + 256 ≤ sp) {mem0 : Memory}
    {ea base start stop count out span ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : ElemPre w mem0 element ea base start stop count out span ctx table zeros pad mask b)
    {env : Env} (ev : ElemEnv env element ea (base + start) (stop - start) count out ctx) (i0 : env 9 = 0) :
    Ends m w sp env mem0 elemLoop fun _ mm =>
      (∀ i < count, nodeAt mm (out + 32 * i) = (rootOf element b (elemRange element b start stop count i).1
        (elemRange element b start stop count i).2).data) ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm a = mem0 a := by
  have small := pre.small
  unfold RootProof.Small at small
  rw [pre.usize] at small
  have inside := pre.inside
  have ordered := pre.ordered
  have roomR := pre.room
  have rs := pre.rSlack
  have ab := access_bound pre.bAcc
  have ar := access_bound pre.rAcc
  have bound : addressBound = 2 ^ 63 := rfl
  -- The roots so far, and memory as at the start outside the region.
  let inv : Env → Memory → Prop := fun e mm => ∃ i, i ≤ count ∧ ElemEnv e element ea (base + start) (stop - start)
    count out ctx ∧ e 9 = UInt64.ofNat i ∧
    (∀ j < i, nodeAt mm (out + 32 * j) = (rootOf element b (elemRange element b start stop count j).1
      (elemRange element b start stop count j).2).data) ∧
    ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm a = mem0 a
  have cbound : count < 2 ^ 64 := by have := pre.room; omega
  refine (Ends.loop inv (fun e _ => count - (e 9).toNat) ⟨0, Nat.zero_le _, ev, i0, fun j hj => absurd hj
    (Nat.not_lt_zero _), fun _ _ _ => rfl⟩ ?_ ?_).mono ?_
  · rintro e mm ⟨i, hi, ev', hi9, -⟩
    exact ⟨_, eval_lt (eval_var hi9) (eval_var ev'.countV) (by omega) cbound⟩
  · rintro e mm v ⟨i, hi, ev', hi9, roots, frame⟩ hv nz
    have c := eval_lt (w := w) (env := e) (mem := mm) (eval_var hi9) (eval_var ev'.countV) (by omega) cbound
    rw [hv] at c
    have hlt : i < count := by
      by_cases h : i < count
      · exact h
      · rw [ite_eq_right h] at c; cases c; exact absurd rfl nz
    obtain ⟨lo, ord, hiStop, accepted⟩ := pre.ranges i hlt
    -- The element's range, from its width or its offsets.
    obtain ⟨E1, run1, ev1, i1, s1, n1⟩ : ∃ E1, Runs m w sp e mm (ifElse RootElements.fx
        [RootElements.s ::= RootElements.src + RootElements.w * RootElements.i, RootElements.n ::= RootElements.w]
        [RootElements.o ::= ld4 (RootElements.src + 4 * RootElements.i),
          ifElse (lt (RootElements.i + 1) RootElements.count)
            [RootElements.en ::= ld4 (RootElements.src + 4 * RootElements.i + 4)]
            [RootElements.en ::= RootElements.size],
          RootElements.s ::= RootElements.src + RootElements.o, RootElements.n ::= RootElements.en - RootElements.o])
        E1 mm ∧ ElemEnv E1 element ea (base + start) (stop - start) count out ctx ∧ E1 9 = UInt64.ofNat i ∧
        E1 12 = UInt64.ofNat (base + (elemRange element b start stop count i).1) ∧ E1 13 = UInt64.ofNat ((elemRange element b start stop count i).2 - (elemRange element b start stop count i).1) := by
      have code := elementRanges_getD element b start stop count i hlt
      by_cases fx : hasWidth element
      · rw [ite_eq_left fx] at code
        have hr : elemRange element b start stop count i = (start + i * fixedWidth element, start + (i + 1) * fixedWidth element) := code
        rw [hr] at lo ord hiStop
        have r1 := Runs.set' (m := m) (w := w) (sp := sp) (env := e) (mem := mm) (x := 12)
          (eval_add (eval_var ev'.srcV) (eval_mul (eval_var (ev'.wV.trans (toUInt64_ofNat _))) (eval_var hi9)))
        have r2 := Runs.set' (m := m) (w := w) (sp := sp) (env := Asm.assign e 12
          (UInt64.ofNat (base + start + fixedWidth element * i))) (mem := mm) (x := 13)
          (eval_var (show Asm.assign e 12 _ 7 = UInt64.ofNat (fixedWidth element) by
            rw [assign_ne (by decide)]; exact ev'.wV))
        refine ⟨_, Runs.ifElse_true 1 (eval_var (by rw [ev'.fxV, fx]; rfl)) (by decide)
          (Runs.block_cons r1 (Runs.block_cons r2 (Runs.block_nil _ _ _ _ _))),
          (ev'.write _ (by decide)).write _ (by decide), by rw [assign_ne (by decide), assign_ne (by decide), hi9],
          by rw [assign_ne (by decide), assign_eq, hr, Nat.mul_comm i]; congr 1; omega, ?_⟩
        rw [assign_eq, hr, Nat.succ_mul]; congr 1; omega
      · rw [ite_eq_right fx] at code
        have hr : elemRange element b start stop count i = (start + offsetAt b (start + i * bytesPerOffset),
            start + if i + 1 < count then offsetAt b (start + (i + 1) * bytesPerOffset) else stop - start) := code
        rw [hr] at lo ord hiStop
        have tab := pre.offsets (by simpa using fx) (by omega)
        have ld0 : eval w e mm (ld4 (RootElements.src + 4 * RootElements.i)) =
            some (UInt64.ofNat (offsetAt b (start + i * bytesPerOffset))) := by
          have mm0 : ∀ q < 4, mm (base + (start + 4 * i) + q) = mem0 (base + (start + 4 * i) + q) := fun q hq =>
            frame _ (outside_of_apart pre.rB (by omega) (by omega)) (outside_of_apart' pre.bPad (by omega) (by omega))
          rw [eval_ld4_of (eval_add (eval_var ev'.srcV) (eval_mul (eval_lit 4) (eval_var hi9)))
            (access_sub pre.bAcc (by omega) (by omega)), show base + start + 4 * i = base + (start + 4 * i) by omega,
            readLE_congr mm mem0 _ 4 mm0, readLE_offsetAt pre.holds pre.bAcc _ (by omega), Nat.mul_comm i]
        have r1 := Runs.set' (m := m) (w := w) (sp := sp) (x := 10) ld0
        let E := Asm.assign e 10 (UInt64.ofNat (offsetAt b (start + i * bytesPerOffset)))
        have evE := ev'.write (x := 10) (UInt64.ofNat (offsetAt b (start + i * bytesPerOffset))) (by decide)
        have iE : E 9 = UInt64.ofNat i := by simp only [E]; rw [assign_ne (by decide), hi9]
        let nxt := if i + 1 < count then offsetAt b (start + (i + 1) * bytesPerOffset) else stop - start
        have r2 : Runs m w sp E mm (ifElse (lt (RootElements.i + 1) RootElements.count)
            [RootElements.en ::= ld4 (RootElements.src + 4 * RootElements.i + 4)] [RootElements.en ::= RootElements.size])
            (Asm.assign E 11 (UInt64.ofNat nxt)) mm := by
          have cc := eval_lt (w := w) (env := E) (mem := mm) (eval_add (eval_var iE) (eval_lit 1))
            (eval_var evE.countV) (by omega) cbound
          by_cases more : i + 1 < count
          · rw [ite_eq_left more] at cc
            have ld1 : eval w E mm (ld4 (RootElements.src + 4 * RootElements.i + 4)) =
                some (UInt64.ofNat (offsetAt b (start + (i + 1) * bytesPerOffset))) := by
              have mm0 : ∀ q < 4, mm (base + (start + 4 * (i + 1)) + q) = mem0 (base + (start + 4 * (i + 1)) + q) :=
                fun q hq => frame _ (outside_of_apart pre.rB (by omega) (by omega))
                  (outside_of_apart' pre.bPad (by omega) (by omega))
              rw [eval_ld4_of (eval_add (eval_add (eval_var evE.srcV) (eval_mul (eval_lit 4) (eval_var iE)))
                (eval_lit 4)) (access_sub pre.bAcc (by omega) (by omega)),
                show base + start + 4 * i + 4 = base + (start + 4 * (i + 1)) by omega,
                readLE_congr mm mem0 _ 4 mm0, readLE_offsetAt pre.holds pre.bAcc _ (by omega), Nat.mul_comm (i + 1)]
            have : nxt = offsetAt b (start + (i + 1) * bytesPerOffset) := ite_eq_left more
            rw [this]
            exact Runs.ifElse_true 1 cc (by decide) (Runs.block_cons (Runs.set' ld1) (Runs.block_nil _ _ _ _ _))
          · rw [ite_eq_right more] at cc
            have : nxt = stop - start := ite_eq_right more
            rw [this]
            exact Runs.ifElse_false cc (Runs.block_cons (Runs.set' (eval_var evE.sizeV)) (Runs.block_nil _ _ _ _ _))
        let F := Asm.assign E 11 (UInt64.ofNat nxt)
        have evF := evE.write (x := 11) (UInt64.ofNat nxt) (by decide)
        have oF : F 10 = UInt64.ofNat (offsetAt b (start + i * bytesPerOffset)) := by
          simp only [F, E]; rw [assign_ne (by decide), assign_eq]
        have r3 := Runs.set' (m := m) (w := w) (sp := sp) (env := F) (mem := mm) (x := 12)
          (eval_add (eval_var evF.srcV) (eval_var oF))
        have r4 := Runs.set' (m := m) (w := w) (sp := sp)
          (env := Asm.assign F 12 (UInt64.ofNat (base + start + offsetAt b (start + i * bytesPerOffset)))) (mem := mm)
          (x := 13) (eval_sub (eval_var (show Asm.assign F 12 _ 11 = UInt64.ofNat nxt by
              rw [assign_ne (by decide)]; exact assign_eq))
            (eval_var (show Asm.assign F 12 _ 10 = _ by rw [assign_ne (by decide)]; exact oF)) (by omega))
        refine ⟨_, Runs.ifElse_false (eval_var (by rw [ev'.fxV, show hasWidth element = false by simpa using fx]; rfl))
          (Runs.block_cons r1 (Runs.block_cons r2 (Runs.block_cons r3 (Runs.block_cons r4
            (Runs.block_nil _ _ _ _ _))))), (evF.write _ (by decide)).write _ (by decide), ?_, ?_, ?_⟩
        · rw [assign_ne (by decide), assign_ne (by decide)]; simp only [F]; rw [assign_ne (by decide)]; exact iE
        · rw [assign_ne (by decide), assign_eq, hr]; congr 1; omega
        · rw [assign_eq, hr]; congr 1; omega
    -- The element's root, by the dispatcher on the element type.
    have sizeLe : (elemRange element b start stop count i).2 - (elemRange element b start stop count i).1 ≤ stop - start := by omega
    have grow := varNeed_mono element sizeLe
    have childPre : RangePre w mm element ea base (elemRange element b start stop count i).1 (elemRange element b start stop count i).2 (out + 32 * i) (out + 32 * count) ctx table zeros
        pad mask b := by
      have frameP : ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm a = mem0 a := frame
      exact rangePre_of (pre.ready.within (o := out) (n := span) pre.rCtx pre.rTable pre.rZeros frameP)
        (planAt_congr pre.plan fun a lo hi => frameP a (outside_of_apart pre.rPlan lo hi)
          (outside_of_apart' pre.planPad lo hi))
        pre.fits (pre.holds.congr fun j hj => frameP _ (outside_of_apart pre.rB (by omega) (by omega))
          (outside_of_apart' pre.bPad (by omega) (by omega)))
        pre.bAcc ord (by omega) pre.small pre.spread pre.sound pre.thin accepted (Nat.lt_of_le_of_lt grow pre.below)
        pre.rAcc pre.rSlack pre.rB pre.rPad pre.rCtx pre.rTable pre.rZeros pre.rPlan pre.bPad pre.planPad
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by simp only [Apart]; omega) pre.usize
    obtain ⟨mm', call, root, -, keep⟩ := ih sp mm ea base (elemRange element b start stop count i).1 (elemRange element b start stop count i).2 (out + 32 * i) (out + 32 * count) ctx
      table zeros pad mask b room childPre
    have r2 := Runs.call (m := m) (sp := sp) (env := E1) (mem := mm) (dst := 14)
      (args := [RootElements.e, RootElements.s, RootElements.n, RootElements.out + 32 * RootElements.i,
        RootElements.scr, RootElements.ctx])
      (by
        simp only [List.mapM_cons, List.mapM_nil, eval_var ev1.eV, eval_var s1, eval_var n1,
          eval_add (eval_var ev1.outV) (eval_mul (eval_lit 32) (eval_var i1)), eval_var ev1.scrV, eval_var ev1.ctxV]
        rfl) call
    have r3 := Runs.set' (m := m) (w := w) (sp := sp) (env := Asm.assign E1 14 0) (mem := mm') (x := 9)
      (eval_add (eval_var (show Asm.assign E1 14 0 9 = UInt64.ofNat i by rw [assign_ne (by decide)]; exact i1))
        (eval_lit 1))
    have scrIn : out + 32 * count + varNeed element ((elemRange element b start stop count i).2 -
        (elemRange element b start stop count i).1) ≤ out + span := by omega
    refine ⟨_, mm', Runs.block_cons run1 (Runs.block_cons r2 (Runs.block_cons r3 (Runs.block_nil _ _ _ _ _))),
      ⟨i + 1, by omega, (ev1.write _ (by decide)).write _ (by decide), assign_eq, fun j hj => ?_,
        fun a o pd => ?_⟩, ?_⟩
    · by_cases last : j = i
      · subst last; exact root
      · rw [nodeAt_congr (m₂ := mm) fun q hq => keep _ (by omega) (by omega)
          (outside_of_apart' pre.rPad (by omega) (by omega))]
        exact roots j (by omega)
    · rw [keep a (fun h => o ⟨by omega, by omega⟩) (fun h => o ⟨by omega, by omega⟩) pd]
      exact frame a o pd
    · show count - (UInt64.ofNat (i + 1)).toNat < count - (e 9).toNat
      rw [hi9, ofNat_toNat (by omega), ofNat_toNat (by omega)]
      omega
  · rintro e mm ⟨⟨i, hi, ev', hi9, roots, frame⟩, exit⟩
    rw [eval_lt (eval_var hi9) (eval_var ev'.countV) (by omega) cbound] at exit
    have : i = count := by
      by_cases h : i < count
      · rw [ite_eq_left h] at exit; cases exit
      · omega
    subst this
    exact ⟨roots, frame⟩


set_option maxHeartbeats 1000000 in
/--
The elements driver writes, at node i of its output, the Lean root of element i.

What a call of the dispatcher on the element type does is a hypothesis.
Memory changes only in the output region and the padding area.
-/
theorem rootElements_calls {m : Module} {w : World} (fns : RangeFns m) {element : Desc}
    (ih : RootOfOk m w element) {sp : Nat} (room : w.stackLo + 176 + rootStack element + 256 ≤ sp)
    {mem : Memory} {ea base start stop count out span ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : ElemPre w mem element ea base start stop count out span ctx table zeros pad mask b) :
    ∃ mem', Calls m w "ssz_root_elements" sp [UInt64.ofNat ea, UInt64.ofNat (base + start), UInt64.ofNat (stop - start),
        UInt64.ofNat count, UInt64.ofNat out, UInt64.ofNat ctx] mem 0 mem' ∧
      (∀ i < count, nodeAt mem' (out + 32 * i) = (rootOf element b (elemRange element b start stop count i).1
        (elemRange element b start stop count i).2).data) ∧
      RootReady w ctx table zeros pad mask mem' ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a := by
  have stack : 112 * element.nesting ≤ rootStack element := by simp only [rootStack]; omega
  let sp' := sp - 8 - 8 * RootElements.fn.frame
  have room' : w.stackLo + rootStack element + 256 ≤ sp' := by simp only [sp', elementsFrame]; omega
  let E0 := entryEnv [UInt64.ofNat ea, UInt64.ofNat (base + start), UInt64.ofNat (stop - start), UInt64.ofNat count,
    UInt64.ofNat out, UInt64.ofNat ctx]
  have fixed := planFixed_calls fns.roots.plan element ea sp' mem pre.plan pre.sound (by omega)
  have width := planWidth_calls fns.roots.plan element ea sp' mem pre.plan pre.sound pre.thin (by omega)
  have r1 := Runs.call (m := m) (sp := sp') (env := E0) (mem := mem) (dst := 6) (args := [RootElements.e])
    (by simp only [List.mapM_cons, List.mapM_nil]; rfl) fixed
  have r2 := Runs.call (m := m) (sp := sp') (env := Asm.assign E0 6 (bitOf (hasWidth element))) (mem := mem) (dst := 7)
    (args := [RootElements.e]) (by simp only [List.mapM_cons, List.mapM_nil]; rfl) width
  let E2 := Asm.assign (Asm.assign E0 6 (bitOf (hasWidth element))) 7 (fixedWidth element).toUInt64
  have r3 := Runs.set' (m := m) (w := w) (sp := sp') (env := E2) (mem := mem) (x := 8)
    (eval_add (eval_var (show E2 4 = UInt64.ofNat out from rfl))
      (eval_mul (eval_lit 32) (eval_var (show E2 3 = UInt64.ofNat count from rfl))))
  have r4 := Runs.set' (m := m) (w := w) (sp := sp') (env := Asm.assign E2 8 (UInt64.ofNat (out + 32 * count)))
    (mem := mem) (x := 9) (eval_lit 0)
  have ev : ElemEnv (Asm.assign (Asm.assign E2 8 (UInt64.ofNat (out + 32 * count))) 9 (UInt64.ofNat 0)) element ea
      (base + start) (stop - start) count out ctx :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨E5, mem', run5, roots, frame⟩ := elemLoop_ends ih room' pre ev rfl
  refine ⟨mem', Calls.fn fns.elements (by rw [elementsFrame]; omega) rfl (Runs.block_cons r1 (Runs.block_cons r2
    (Runs.block_cons r3 (Runs.block_cons r4 (Runs.block_cons run5 (Runs.block_nil _ _ _ _ _)))))) rfl, roots,
    pre.ready.within (o := out) (n := span) pre.rCtx pre.rTable pre.rZeros frame, frame⟩

end EthLib.Consensus.Ssz.Native.Driver
