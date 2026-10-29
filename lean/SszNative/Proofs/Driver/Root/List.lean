import SszNative.Proofs.Driver.Root.ListFacts
import SszNative.Proofs.Driver.Root.ByteList
import SszNative.Proofs.Driver.Root.BitList

/-!
The list driver writes the Lean root of a list, bounded or progressive.

Its nodes are the packed bytes of basic elements, the roots of fixed-size records rooted together, or the roots of
the elements one by one.
The nodes are then rooted at the limit's depth, or on a progressive spine, and the count is mixed in.
-/

namespace Ssz.Native.Driver

open Ssz Ssz.Native.Ir Ssz.Native.Ir.Expr Ssz.Native.Ir.Stmt Ssz.Native.Asm

/-! ### The nodes -/

/-- What the list driver's node step leaves: the nodes at the buffer, their count and capacity, and the count. -/
structure ListNodes (mem0 mem : Memory) (env : Env) (x : ByteArray) (nodes cap count buf span pad : Nat) : Prop where
  /-- Each node at the buffer is the Lean buffer's node. -/
  held : ∀ i < nodes, nodeAt mem (buf + 32 * i) = nodeOf x 0 i
  /-- The Lean buffer holds the nodes. -/
  inside : 32 * nodes ≤ x.size
  /-- The Lean buffer has machine-sized offsets, when there are nodes. -/
  small : nodes = 0 ∨ x.size < USize.size
  /-- The node count. -/
  nodesV : env 10 = UInt64.ofNat nodes
  /-- The tree's capacity. -/
  capV : env 11 = UInt64.ofNat cap
  /-- The element count. -/
  countV : env 12 = UInt64.ofNat count
  /-- Memory is as at the start outside the buffer's region and the padding area. -/
  frame : ∀ a, ¬ (buf ≤ a ∧ a < buf + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem a = mem0 a

/-- The nodes read from memory are the Lean buffer's nodes. -/
theorem nodesFrom_of_nodeAt {mem : Memory} {a n : Nat} {x : ByteArray}
    (h : ∀ i < n, nodeAt mem (a + 32 * i) = nodeOf x 0 i) :
    nodesFrom (bytesAt mem a (32 * n)) 0 n = nodesFrom x 0 n := by
  apply Array.ext
  · simp
  · intro i hi _
    have hi' : i < n := by simpa using hi
    simp only [nodesFrom, Array.getElem_ofFn]
    rw [nodeOf_bytesAt mem a n i hi', h i hi']

/-- A basic element's width divides a node. -/
theorem basic_width {e : Desc} (basic : e.isBasic = true) (sound : e.wellFormed = .ok ()) :
    fixedWidth e = 1 ∨ fixedWidth e = 2 ∨ fixedWidth e = 4 ∨ fixedWidth e = 8 ∨ fixedWidth e = 16 ∨
      fixedWidth e = 32 := by
  cases e with
  | bool => simp [fixedWidth]
  | uint width =>
    simp only [Desc.wellFormed] at sound
    split at sound
    · rename_i h; simp at h; simp only [fixedWidth]; omega
    · cases sound
  | _ => simp [Desc.isBasic] at basic

/-- A basic element's item length is its width. -/
theorem basic_itemLength {e : Desc} (basic : e.isBasic = true) : e.itemLength = fixedWidth e := by
  cases e <;> simp_all [Desc.isBasic, Desc.itemLength, fixedWidth]

set_option maxHeartbeats 2000000 in
/-- Basic elements are gathered into nodes, and counted and bounded by their width. -/
theorem listBasic_runs {m : Module} {w : World} (gmod : GatherModule m) {sp : Nat} (room : w.stackLo + 8 ≤ sp)
    {mem : Memory} {base start stop out scratch ctx pad : Nat} {p L : Nat} {b : ByteArray} (holds : Holds mem base b)
    (bAcc : w.access base b.size = true) (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (small : 64 * b.size + 128 < 2 ^ 64) (usize : USize.size = 2 ^ 64) {width : Nat}
    (hw : width = 1 ∨ width = 2 ∨ width = 4 ∨ width = 8 ∨ width = 16 ∨ width = 32) (hL : L < 2 ^ 64)
    (bufAcc : w.access (scratch + 64) (32 * nodesFor (stop - start) + 32) = true)
    (bufApart : Apart (scratch + 64, 32 * nodesFor (stop - start) + 32) (base, b.size))
    {env : Env} (ev : RangeEnv env p (base + start) (stop - start) out scratch ctx)
    (h7 : env 7 = UInt64.ofNat L) (h9 : env 9 = UInt64.ofNat width) (h15 : env 15 = UInt64.ofNat (scratch + 64)) :
    ∃ env' mem', Runs m w sp env mem (.block [RootList.nodes ::= ceilDiv RootList.size 32,
        callInto RootList.sink "ssz_gather" [RootList.buf, RootList.src, 1, RootList.size, 0,
          32 * RootList.nodes + 32 - RootList.size],
        RootList.cap ::= RootList.limit / (32 / RootList.w) + ne (RootList.limit % (32 / RootList.w)) 0,
        RootList.count ::= RootList.size / RootList.w]) env' mem' ∧
      RangeEnv env' p (base + start) (stop - start) out scratch ctx ∧ env' 7 = UInt64.ofNat L ∧
      env' 15 = UInt64.ofNat (scratch + 64) ∧ env' 6 = env 6 ∧
      ListNodes mem mem' env' (packRange b start stop) (nodesFor (stop - start)) (nodesFor (L * width))
        ((stop - start) / width) (scratch + 64) (32 * nodesFor (stop - start) + 32) pad := by
  have ab := access_bound bAcc
  have abuf := access_bound bufAcc
  generalize hsize : stop - start = size at ev bufAcc bufApart ⊢
  generalize hn : nodesFor size = n at bufAcc bufApart ⊢
  have hn' : n = (size + 31) / 32 := by rw [← hn]; rfl
  have wpos : 0 < width := by omega
  have wle : width ≤ 32 := by omega
  -- The node count.
  have s1 := Runs.set' (m := m) (w := w) (sp := sp) (env := env) (mem := mem) (x := 10)
    (show eval w env mem (ceilDiv RootList.size 32) = some (UInt64.ofNat n) by
      rw [eval_ceilDiv (eval_var ev.size) 32 (by omega), ofNat_toNat (by omega), hn']; rfl)
  have ev1 := ev.write (x := 10) (UInt64.ofNat n) (by decide)
  have n1 : Asm.assign env 10 (UInt64.ofNat n) 10 = UInt64.ofNat n := assign_eq
  have l1 : Asm.assign env 10 (UInt64.ofNat n) 7 = UInt64.ofNat L := by rw [assign_ne (by decide)]; exact h7
  have w1 : Asm.assign env 10 (UInt64.ofNat n) 9 = UInt64.ofNat width := by rw [assign_ne (by decide)]; exact h9
  have b1 : Asm.assign env 10 (UInt64.ofNat n) 15 = UInt64.ofNat (scratch + 64) := by
    rw [assign_ne (by decide)]; exact h15
  have z1 : Asm.assign env 10 (UInt64.ofNat n) 6 = env 6 := assign_ne (by decide)
  generalize Asm.assign env 10 (UInt64.ofNat n) = E1 at s1 ev1 n1 l1 w1 b1 z1
  -- The gather.
  obtain ⟨mem1, g1, held1, keep1⟩ := packGather_runs (m := m) (w := w) gmod (sp := sp) room (env := E1) (mem := mem)
    (dst := 17) (args := [RootList.buf, RootList.src, 1, RootList.size, 0, 32 * RootList.nodes + 32 - RootList.size])
    (buf := scratch + 64) holds bAcc ordered inside (by rw [usize]; omega) usize (by rw [hsize, hn]; exact bufAcc)
    (by rw [hsize, hn]; exact bufApart)
    (by
      rw [hsize, hn]
      simp only [List.mapM_cons, List.mapM_nil, eval_var b1, eval_var ev1.src, eval_var ev1.size,
        eval_sub (eval_add (eval_mul (eval_lit 32) (eval_var n1)) (eval_lit 32)) (eval_var ev1.size)
          (show size ≤ 32 * n + 32 by omega)]
      rfl)
  rw [hsize, hn] at keep1
  have ev2 := ev1.write (x := 17) 0 (by decide)
  have n2 : Asm.assign E1 17 0 10 = UInt64.ofNat n := by rw [assign_ne (by decide)]; exact n1
  have l2 : Asm.assign E1 17 0 7 = UInt64.ofNat L := by rw [assign_ne (by decide)]; exact l1
  have w2 : Asm.assign E1 17 0 9 = UInt64.ofNat width := by rw [assign_ne (by decide)]; exact w1
  have b2 : Asm.assign E1 17 0 15 = UInt64.ofNat (scratch + 64) := by rw [assign_ne (by decide)]; exact b1
  have z2 : Asm.assign E1 17 0 6 = env 6 := by rw [assign_ne (by decide)]; exact z1
  generalize Asm.assign E1 17 0 = E2 at g1 ev2 n2 l2 w2 b2 z2
  -- The capacity in nodes, a node holding a whole number of elements.
  have kEval : eval w E2 mem1 ((32 : Expr) / RootList.w) = some (UInt64.ofNat (32 / width)) :=
    eval_div (eval_lit 32) (eval_var w2) (by decide) (by omega) (by omega)
  have kpos : 0 < 32 / width := by rcases hw with h | h | h | h | h | h <;> subst h <;> decide
  have kle : 32 / width ≤ 32 := Nat.div_le_self _ _
  have capEq : L / (32 / width) + (if L % (32 / width) = 0 then 0 else 1) = nodesFor (L * width) := by
    simp only [nodesFor]
    rcases hw with h | h | h | h | h | h <;> subst h <;> split <;> omega
  have capEval : eval w E2 mem1 (RootList.limit / (32 / RootList.w) + ne (RootList.limit % (32 / RootList.w)) 0) =
      some (UInt64.ofNat (nodesFor (L * width))) := by
    rw [← capEq]
    have dv := eval_div (eval_var l2) kEval hL (by omega) (by omega)
    have md := eval_mod (eval_var l2) kEval hL (by omega) (by omega)
    have ne' := eval_ne md (eval_lit 0)
    by_cases z : L % (32 / width) = 0
    · rw [if_pos z]
      rw [if_pos (by rw [z])] at ne'
      have := eval_add dv ne'
      simpa using this
    · rw [if_neg z]
      rw [if_neg (fun e => z ((ofNat_inj (by have := Nat.mod_lt L kpos; omega) (by decide)).mp e))] at ne'
      exact eval_add dv ne'
  have s3 := Runs.set' (m := m) (w := w) (sp := sp) (env := E2) (mem := mem1) (x := 11) capEval
  have s4 := Runs.set' (m := m) (w := w) (sp := sp) (env := Asm.assign E2 11 (UInt64.ofNat (nodesFor (L * width))))
    (mem := mem1) (x := 12) (eval_div (eval_var (show Asm.assign E2 11 _ 2 = UInt64.ofNat size by
      rw [assign_ne (by decide)]; exact ev2.size)) (eval_var (show Asm.assign E2 11 _ 9 = UInt64.ofNat width by
      rw [assign_ne (by decide)]; exact w2)) (by omega) (by omega) (by omega))
  have packedSize := (RootProof.packRange_nodes b start stop ordered inside (by rw [usize]; omega)).2
  rw [hsize, hn] at packedSize
  refine ⟨_, mem1, Runs.block_cons s1 (Runs.block_cons g1 (Runs.block_cons s3 (Runs.block_cons s4
    (Runs.block_nil _ _ _ _ _)))), (ev2.write _ (by decide)).write _ (by decide),
    by rw [assign_ne (by decide), assign_ne (by decide)]; exact l2,
    by rw [assign_ne (by decide), assign_ne (by decide)]; exact b2,
    by rw [assign_ne (by decide), assign_ne (by decide)]; exact z2,
    ⟨fun i hi => nodeAt_of_holds held1 (by rw [packedSize]; omega), by rw [packedSize]; omega,
      .inr (by rw [packedSize, usize]; omega), by rw [assign_ne (by decide), assign_ne (by decide)]; exact n2,
      by rw [assign_ne (by decide), assign_eq], assign_eq, fun a o _ => keep1 a o⟩⟩


/-- Node i of joined nodes is buffer i. -/
theorem nodeOf_joinNodes {rs : List ByteArray} (sized : ∀ r ∈ rs, r.size = 32) {i : Nat} (hi : i < rs.length) :
    nodeOf (joinNodes rs) 0 i = rs[i].data := by
  have e := congrArg (fun a : Array Bytes => a[i]!) (RootProof.joinNodes_nodes rs sized).1
  rw [getElem!_pos _ _ (by simp [RootProof.nodesFrom]; exact hi),
    getElem!_pos _ _ (by simp; exact hi)] at e
  simpa [RootProof.nodesFrom, nodeOf] using e

/-- A narrow type of a fixed size is far below the word size. -/
theorem width_lt_of_narrow {d : Desc} (thin : narrow d = true) (fx : hasWidth d = true) : fixedWidth d < 2 ^ 62 := by
  have size : d.fixedSize = some (fixedWidth d) := by rw [fixedSize_eq, if_pos fx]
  cases d with
  | bitVector n => simp only [narrow, decide_eq_true_eq] at thin; simp only [fixedWidth]; omega
  | bool => simp [fixedWidth]
  | vector e l | container _ _ | progressiveContainer _ _ _ | uint _ | byteVector _ =>
    simp only [narrow, size, Bool.and_eq_true, Option.all_some, decide_eq_true_eq] at thin
    first | exact thin.1 | exact thin
  | _ => simp [hasWidth] at fx

/-- The list driver's statements for elements that are not basic. -/
abbrev listComposite : List Stmt :=
  [callInto RootList.fx "ssz_plan_fixed" [RootList.e],
    ifElse RootList.fx [ifElse (eq RootList.w 0) [RootList.count ::= 0] [RootList.count ::= RootList.size / RootList.w]]
      [ifElse (eq RootList.size 0) [RootList.count ::= 0] [RootList.count ::= ld4 RootList.src / 4]],
    RootList.nodes ::= RootList.count, RootList.cap ::= RootList.limit,
    callInto RootList.pl "ssz_plan_plain" [RootList.e],
    ifElse RootList.pl [when (lt 0 RootList.count) [callInto RootList.sink "ssz_roots_chunked"
        [RootList.e, RootList.src, RootList.w, RootList.count, RootList.buf, RootList.ctx]]]
      [callInto RootList.sink "ssz_root_elements"
        [RootList.e, RootList.src, RootList.size, RootList.count, RootList.buf, RootList.ctx]]]

/-- What the list driver's composite step needs: the element's plan, the decoded list's facts, and the region. -/
structure CompPre (w : World) (mem : Memory) (element : Desc) (ea base start stop count buf span ctx table zeros pad : Nat)
    (mask : UInt64) (b : ByteArray) : Prop where
  /-- The context is filled. -/
  ready : RootReady w ctx table zeros pad mask mem
  /-- The element's plan is in memory. -/
  plan : WordsAt w mem ea (Plan.words element)
  /-- Its words fit. -/
  fits : Fits (Plan.words element)
  /-- The encoding is in memory. -/
  holds : Holds mem base b
  /-- It is usable. -/
  bAcc : w.access base b.size = true
  /-- The range runs forward. -/
  ordered : start ≤ stop
  /-- It lies inside the encoding. -/
  inside : stop ≤ b.size
  /-- Every buffer has machine-sized offsets. -/
  small : RootProof.Small b
  /-- Twice the encoding past its address stays below the address bound. -/
  spread : base + 2 * b.size ≤ addressBound
  /-- The element type is legal. -/
  sound : element.wellFormed = .ok ()
  /-- Its fixed-size parts are narrow. -/
  thin : narrow element = true
  /-- It is not basic. -/
  notBasic : element.isBasic = false
  /-- The count is the Lean count. -/
  counted : elementCount element b start stop = count
  /-- Each element's range decodes. -/
  ranges : ∀ i < count, start ≤ (elemRange element b start stop count i).1 ∧
    (elemRange element b start stop count i).1 ≤ (elemRange element b start stop count i).2 ∧
    (elemRange element b start stop count i).2 ≤ stop ∧
    ∃ v, deserialize element (slice b (elemRange element b start stop count i).1
      (elemRange element b start stop count i).2) = .ok v
  /-- There is a range per element. -/
  rlen : (elementRanges element b start stop count).length = count
  /-- Fixed-size elements fill the range. -/
  fixedFill : hasWidth element = true → count * fixedWidth element = stop - start ∧
    (fixedWidth element = 0 → count = 0)
  /-- Variable-size elements are counted by the first offset. -/
  varCount : hasWidth element = false → (stop - start = 0 ∧ count = 0) ∨
    (4 ≤ stop - start ∧ count = offsetAt b start / 4 ∧ 4 * count ≤ stop - start)
  /-- The region holds the roots and what rooting fixed-size records needs. -/
  roomPlain : plain element = true →
    32 * count + max (rootsNeed element 1) (rootsNeed element (min count recordsPerChunk)) ≤ span
  /-- The region holds the roots and an element's scratch. -/
  roomVar : plain element = false → 32 * count + varNeed element (stop - start) ≤ span
  /-- The region's bound is below the cap. -/
  below : span < scratchCap
  /-- The region is usable. -/
  rAcc : w.access buf span = true
  /-- It ends a node short of the address bound. -/
  rSlack : buf + span + 32 ≤ addressBound
  /-- It misses the encoding. -/
  rB : Apart (buf, span) (base, b.size)
  /-- It misses the padding area. -/
  rPad : Apart (buf, span) (pad, 1536)
  /-- It misses the context. -/
  rCtx : Apart (buf, span) (ctx, 32)
  /-- It misses the table. -/
  rTable : Apart (buf, span) (table, Kernel.tableSize)
  /-- It misses the zero roots. -/
  rZeros : Apart (buf, span) (zeros, 32 * (zeroHeights + 1))
  /-- It misses the element's plan. -/
  rPlan : Apart (buf, span) (ea, 8 * (Plan.words element).length)
  /-- The encoding misses the padding area. -/
  bPad : Apart (base, b.size) (pad, 1536)
  /-- The element's plan misses the padding area. -/
  planPad : Apart (ea, 8 * (Plan.words element).length) (pad, 1536)
  /-- A machine word holds a full 64-bit size. -/
  usize : USize.size = 2 ^ 64

/-- The nodes of a list of elements that are not basic: fixed-size records rooted together, or roots one by one. -/
def compNodes (element : Desc) (b : ByteArray) (start stop count : Nat) : ByteArray :=
  if plain element then chunkedRoots element b start (fixedWidth element) count
  else joinNodes (variableRoots element b (elementRanges element b start stop count))

set_option maxHeartbeats 8000000 in
/-- Elements that are not basic are counted, then rooted together or one by one into the buffer. -/
theorem listComposite_runs {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m)
    (fns : RangeFns m) {element : Desc} (ih : RootOfOk m w element) {sp : Nat}
    (room : w.stackLo + 176 + 256 + rootStack element ≤ sp) {mem : Memory}
    {ea base start stop count buf span ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray} {p out scratch L : Nat}
    (pre : CompPre w mem element ea base start stop count buf span ctx table zeros pad mask b)
    {env : Env} (ev : RangeEnv env p (base + start) (stop - start) out scratch ctx)
    (h7 : env 7 = UInt64.ofNat L) (h8 : env 8 = UInt64.ofNat ea) (h9 : env 9 = UInt64.ofNat (fixedWidth element))
    (h15 : env 15 = UInt64.ofNat buf) :
    ∃ env' mem', Runs m w sp env mem (.block listComposite) env' mem' ∧
      RangeEnv env' p (base + start) (stop - start) out scratch ctx ∧ env' 7 = UInt64.ofNat L ∧
      env' 15 = UInt64.ofNat buf ∧ env' 6 = env 6 ∧ RootReady w ctx table zeros pad mask mem' ∧
      ListNodes mem mem' env' (compNodes element b start stop count) count L count buf span pad := by
  have small := pre.small
  unfold RootProof.Small at small
  rw [pre.usize] at small
  have ordered := pre.ordered
  have inside := pre.inside
  have ab := access_bound pre.bAcc
  have ar := access_bound pre.rAcc
  have rs := pre.rSlack
  have bound : addressBound = 2 ^ 63 := rfl
  have one := nesting_pos element
  have capv := cap_eq
  have below := pre.below
  have chunk : recordsPerChunk = 1024 := rfl
  have spread := pre.spread
  have stackP : 112 * element.nesting ≤ rootStack element := by simp only [rootStack]; omega
  -- The variables that stay, through each step.
  let Keep : Env → Prop := fun e => RangeEnv e p (base + start) (stop - start) out scratch ctx ∧
    e 7 = UInt64.ofNat L ∧ e 8 = UInt64.ofNat ea ∧ e 9 = UInt64.ofNat (fixedWidth element) ∧
    e 15 = UInt64.ofNat buf ∧ e 6 = env 6
  have keepW : ∀ e (x : Nat) (v : UInt64), Keep e → x ≠ 7 → x ≠ 8 → x ≠ 9 → x ≠ 15 → 7 ≤ x →
      Keep (Asm.assign e x v) := fun e x v k a b c d h =>
    ⟨k.1.write v (by omega), by rw [assign_ne (Ne.symm a)]; exact k.2.1, by rw [assign_ne (Ne.symm b)]; exact k.2.2.1,
      by rw [assign_ne (Ne.symm c)]; exact k.2.2.2.1, by rw [assign_ne (Ne.symm d)]; exact k.2.2.2.2.1,
      by rw [assign_ne (by omega)]; exact k.2.2.2.2.2⟩
  have k0 : Keep env := ⟨ev, h7, h8, h9, h15, rfl⟩
  -- Whether the element has a fixed size.
  have fixedCall := planFixed_calls fns.roots.plan element ea sp mem pre.plan pre.sound (by omega)
  have r1 := Runs.call (m := m) (sp := sp) (env := env) (mem := mem) (dst := 13) (args := [RootList.e])
    (by simp only [List.mapM_cons, List.mapM_nil, eval_var h8]; rfl) fixedCall
  have k1 := keepW env 13 (bitOf (hasWidth element)) k0 (by decide) (by decide) (by decide) (by decide) (by decide)
  have fx1 : Asm.assign env 13 (bitOf (hasWidth element)) 13 = bitOf (hasWidth element) := assign_eq
  generalize Asm.assign env 13 (bitOf (hasWidth element)) = E1 at r1 k1 fx1
  -- The count.
  have r2 : Runs m w sp E1 mem (ifElse RootList.fx
      [ifElse (eq RootList.w 0) [RootList.count ::= 0] [RootList.count ::= RootList.size / RootList.w]]
      [ifElse (eq RootList.size 0) [RootList.count ::= 0] [RootList.count ::= ld4 RootList.src / 4]])
      (Asm.assign E1 12 (UInt64.ofNat count)) mem := by
    by_cases fx : hasWidth element = true
    · obtain ⟨fill, zero⟩ := pre.fixedFill fx
      have wsmall : fixedWidth element < 2 ^ 64 := by
        have := width_lt_of_narrow pre.thin fx; omega
      refine Runs.ifElse_true 1 (eval_var (by rw [fx1, fx]; rfl)) (by decide) (Runs.block_cons ?_
        (Runs.block_nil _ _ _ _ _))
      have c := eval_eq (w := w) (env := E1) (mem := mem) (eval_var k1.2.2.2.1) (eval_lit 0) wsmall (by decide)
      by_cases z : fixedWidth element = 0
      · rw [if_pos z] at c
        rw [show count = 0 from zero z]
        exact Runs.ifElse_true 1 c (by decide) (Runs.block_cons (Runs.set' (eval_lit 0)) (Runs.block_nil _ _ _ _ _))
      · rw [if_neg z] at c
        have q : (stop - start) / fixedWidth element = count := by
          rw [← fill]; exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero z)
        refine Runs.ifElse_false c (Runs.block_cons (Runs.set' ?_) (Runs.block_nil _ _ _ _ _))
        rw [← q]
        exact eval_div (eval_var k1.1.size) (eval_var k1.2.2.2.1) (by omega) wsmall z
    · have fx' : hasWidth element = false := by simpa using fx
      refine Runs.ifElse_false (eval_var (by rw [fx1, fx']; rfl)) (Runs.block_cons ?_ (Runs.block_nil _ _ _ _ _))
      have c := eval_eq (w := w) (env := E1) (mem := mem) (eval_var k1.1.size) (eval_lit 0) (by omega) (by decide)
      rcases pre.varCount fx' with ⟨hz, hc⟩ | ⟨four, hc, tab⟩
      · rw [if_pos hz] at c
        rw [hc]
        exact Runs.ifElse_true 1 c (by decide) (Runs.block_cons (Runs.set' (eval_lit 0)) (Runs.block_nil _ _ _ _ _))
      · rw [if_neg (by omega)] at c
        refine Runs.ifElse_false c (Runs.block_cons (Runs.set' ?_) (Runs.block_nil _ _ _ _ _))
        rw [hc]
        have ld := eval_ld4_of (w := w) (env := E1) (mem := mem) (a := RootList.src) (eval_var k1.1.src)
          (access_sub pre.bAcc (by omega) (by omega))
        rw [readLE_offsetAt pre.holds pre.bAcc start (by omega)] at ld
        exact eval_div ld (eval_lit 4) (by have := Validate.offsetAt_lt b start; omega) (by decide) (by decide)
  have k2 := keepW E1 12 (UInt64.ofNat count) k1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have c2 : Asm.assign E1 12 (UInt64.ofNat count) 12 = UInt64.ofNat count := assign_eq
  generalize Asm.assign E1 12 (UInt64.ofNat count) = E2 at r2 k2 c2
  -- The node count and the capacity.
  have s3 := Runs.set' (m := m) (w := w) (sp := sp) (env := E2) (mem := mem) (x := 10) (eval_var c2)
  have k3 := keepW E2 10 (UInt64.ofNat count) k2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have c3 : Asm.assign E2 10 (UInt64.ofNat count) 12 = UInt64.ofNat count := by rw [assign_ne (by decide)]; exact c2
  have n3 : Asm.assign E2 10 (UInt64.ofNat count) 10 = UInt64.ofNat count := assign_eq
  generalize Asm.assign E2 10 (UInt64.ofNat count) = E3 at s3 k3 c3 n3
  have s4 := Runs.set' (m := m) (w := w) (sp := sp) (env := E3) (mem := mem) (x := 11) (eval_var k3.2.1)
  have k4 := keepW E3 11 (UInt64.ofNat L) k3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have c4 : Asm.assign E3 11 (UInt64.ofNat L) 12 = UInt64.ofNat count := by rw [assign_ne (by decide)]; exact c3
  have n4 : Asm.assign E3 11 (UInt64.ofNat L) 10 = UInt64.ofNat count := by rw [assign_ne (by decide)]; exact n3
  have l4 : Asm.assign E3 11 (UInt64.ofNat L) 11 = UInt64.ofNat L := assign_eq
  generalize Asm.assign E3 11 (UInt64.ofNat L) = E4 at s4 k4 c4 n4 l4
  -- Whether the element is rooted as fixed-size records.
  have plainCall := planPlain_calls fns.roots.plan element ea sp mem pre.plan pre.sound (by omega)
  have r5 := Runs.call (m := m) (sp := sp) (env := E4) (mem := mem) (dst := 14) (args := [RootList.e])
    (by simp only [List.mapM_cons, List.mapM_nil, eval_var k4.2.2.1]; rfl) plainCall
  have k5 := keepW E4 14 (bitOf (plain element)) k4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have c5 : Asm.assign E4 14 (bitOf (plain element)) 12 = UInt64.ofNat count := by
    rw [assign_ne (by decide)]; exact c4
  have n5 : Asm.assign E4 14 (bitOf (plain element)) 10 = UInt64.ofNat count := by
    rw [assign_ne (by decide)]; exact n4
  have l5 : Asm.assign E4 14 (bitOf (plain element)) 11 = UInt64.ofNat L := by rw [assign_ne (by decide)]; exact l4
  have p5 : Asm.assign E4 14 (bitOf (plain element)) 14 = bitOf (plain element) := assign_eq
  generalize Asm.assign E4 14 (bitOf (plain element)) = E5 at r5 k5 c5 n5 l5 p5
  have lead : ∀ {e' : Env} {mm : Memory}, Runs m w sp E5 mem (ifElse RootList.pl
      [when (lt 0 RootList.count) [callInto RootList.sink "ssz_roots_chunked"
        [RootList.e, RootList.src, RootList.w, RootList.count, RootList.buf, RootList.ctx]]]
      [callInto RootList.sink "ssz_root_elements"
        [RootList.e, RootList.src, RootList.size, RootList.count, RootList.buf, RootList.ctx]]) e' mm →
      Runs m w sp env mem (.block listComposite) e' mm := fun r =>
    Runs.block_cons r1 (Runs.block_cons r2 (Runs.block_cons s3 (Runs.block_cons s4 (Runs.block_cons r5
      (Runs.block_cons r (Runs.block_nil _ _ _ _ _))))))
  have frameReady : ∀ mm : Memory, (∀ a, ¬ (buf ≤ a ∧ a < buf + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm a = mem a) →
      RootReady w ctx table zeros pad mask mm := fun mm f =>
    pre.ready.within (o := buf) (n := span) pre.rCtx pre.rTable pre.rZeros f
  by_cases pl : plain element = true
  · -- Fixed-size records, rooted together a chunk at a time.
    have okE : Rootable element := ⟨pl, pre.sound, pre.thin⟩
    have roomP := pre.roomPlain pl
    have fw := (pre.fixedFill (RootProof.hasWidth_of_plain element pl)).1
    have wide := width_narrow element pl pre.thin
    have cpl : compNodes element b start stop count = chunkedRoots element b start (fixedWidth element) count := by
      simp [compNodes, pl]
    rw [cpl]
    by_cases c0 : count = 0
    · -- No records: nothing to root.
      have cc := eval_lt (w := w) (env := E5) (mem := mem) (eval_lit 0) (eval_var c5) (by decide) (by omega)
      rw [if_neg (by omega)] at cc
      exact ⟨E5, mem, lead (Runs.ifElse_true 1 (eval_var (by rw [p5, pl]; rfl)) (by decide)
        (Runs.block_cons (Runs.when_false cc) (Runs.block_nil _ _ _ _ _))), k5.1, k5.2.1, k5.2.2.2.2.1, k5.2.2.2.2.2,
        frameReady mem (fun _ _ _ => rfl),
        ⟨fun i hi => absurd hi (by omega), by omega, .inl c0, n5, l5, c5, fun _ _ _ => rfl⟩⟩
    · have cc := eval_lt (w := w) (env := E5) (mem := mem) (eval_lit 0) (eval_var c5) (by decide) (by omega)
      rw [if_pos (by omega)] at cc
      have cnt1 : 1 ≤ count := by omega
      have sizedE := rootsOf_size element okE pre.usize
      -- A chunk's needs lie inside the region.
      have chunkNeed : ∀ done c, done < count → done % recordsPerChunk = 0 → c = min recordsPerChunk (count - done) →
          rootsNeed element c ≤ rootsNeed element (min count recordsPerChunk) ∧
          32 * done + rootsNeed element c ≤ 32 * count + rootsNeed element (min count recordsPerChunk) := by
        intro done c lt al hc
        by_cases few : count ≤ recordsPerChunk
        · have : done = 0 := by rw [chunk] at al few; omega
          subst this
          have : c = count := by rw [hc, chunk]; rw [chunk] at few; omega
          subst this
          rw [Nat.min_eq_left few]; omega
        · have top := rootsNeed_chunk element (show c ≤ recordsPerChunk by rw [hc]; exact Nat.min_le_left _ _)
          rw [Nat.min_eq_right (by omega)]; omega
      obtain ⟨mem1, call1, held1, keep1⟩ := rootsChunked_calls (m := m) (w := w) fns.roots.chunked (sp := sp)
        (by rw [chunkedFrame]; omega) (mem0 := mem) (p := ea) (src := base + start) (stride := fixedWidth element)
        (count := count) (out := buf) (ctx := ctx) (pad := pad) (span := span)
        (fun done c => rootsOf element b (start + fixedWidth element * done) (fixedWidth element) c)
        (fun done c lt al hc => sizedE b _ _ c (by rw [hc, chunk]; omega)
          (by have := chunkNeed done c lt al hc; have := Nat.le_max_right (rootsNeed element 1)
                (rootsNeed element (min count recordsPerChunk)); omega))
        (by omega) (by omega) pre.rPad (by have := Nat.zero_le (max (rootsNeed element 1)
          (rootsNeed element (min count recordsPerChunk))); omega)
        (fun mem' done c agree lt al hc => by
          obtain ⟨need, inRoom⟩ := chunkNeed done c lt al hc
          have cpos : 1 ≤ c := by rw [hc, chunk]; omega
          have cle : done + c ≤ count := by rw [hc, chunk]; omega
          have mx := Nat.le_max_right (rootsNeed element 1) (rootsNeed element (min count recordsPerChunk))
          have span' : fixedWidth element * (done + c) ≤ fixedWidth element * count := Nat.mul_le_mul_left _ cle
          rw [Nat.mul_add] at span'
          have fwc : fixedWidth element * count = stop - start := by rw [Nat.mul_comm]; exact fw
          have fw1 : fixedWidth element ≤ stop - start := by
            have := Nat.le_mul_of_pos_right (fixedWidth element) (show 0 < count by omega); omega
          have rpre : RootsPre w mem' element ea base (start + fixedWidth element * done) (fixedWidth element) c
              (buf + 32 * done) ctx table zeros pad mask b :=
            { ready := frameReady mem' agree,
              plan := planAt_congr pre.plan fun a lo hi => agree a (outside_of_apart pre.rPlan lo hi)
                (outside_of_apart' pre.planPad lo hi),
              holds := pre.holds.congr fun j hj => agree _ (outside_of_apart pre.rB (by omega) (by omega))
                (outside_of_apart' pre.bPad (by omega) (by omega)),
              bAcc := pre.bAcc, gap := Nat.le_refl _, strideSmall := by omega, pos := cpos,
              inside := fun i hi => by
                have := Nat.mul_le_mul_left (fixedWidth element) (show done + i + 1 ≤ count by omega)
                rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at this
                omega,
              spread := by omega, below := by omega,
              acc := access_sub pre.rAcc (by omega) (by omega), slack := by omega,
              oB := apart_sub pre.rB (by omega) (by omega), oPad := apart_sub pre.rPad (by omega) (by omega),
              oCtx := apart_sub pre.rCtx (by omega) (by omega), oTable := apart_sub pre.rTable (by omega) (by omega),
              oZeros := apart_sub pre.rZeros (by omega) (by omega), oPlan := apart_sub pre.rPlan (by omega) (by omega),
              bPad := pre.bPad, planPad := pre.planPad, usize := pre.usize }
          obtain ⟨mem'', calls, held, _, keep⟩ := rootsOf_ok hash gmod fns.roots element okE
            (sp - 8 - 8 * RootsChunked.fn.frame) mem' ea base (start + fixedWidth element * done) (fixedWidth element)
            c (buf + 32 * done) ctx table zeros pad mask b (by
              rw [chunkedFrame]; simp only [rootsStack, columnsStack, hashStack, rootStack] at room ⊢; omega) rpre
          refine ⟨mem'', ?_, held, fun a o pd => keep a (fun h => o ⟨h.1, by omega⟩) pd⟩
          rw [show base + start + fixedWidth element * done = base + (start + fixedWidth element * done) by omega]
          exact calls)
      have joined : (if count ≤ recordsPerChunk then
          rootsOf element b (start + fixedWidth element * 0) (fixedWidth element) count
          else chunkJoin (fun done c => rootsOf element b (start + fixedWidth element * done) (fixedWidth element) c)
            count ((count + recordsPerChunk - 1) / recordsPerChunk)) =
          chunkedRoots element b start (fixedWidth element) count := by
        split
        · rename_i few
          rw [chunkedRoots, if_pos few]
          simp only [Nat.mul_zero, Nat.add_zero]
        · rename_i many
          rw [chunkedRoots_join _ _ _ _ _ many]
      rw [joined] at held1
      have rootsSize := chunkedRoots_size element sizedE b start (fixedWidth element) count cnt1 (by
        have := Nat.le_max_right (rootsNeed element 1) (rootsNeed element (min count recordsPerChunk)); omega)
      have k6 := keepW E5 17 0 k5 (by decide) (by decide) (by decide) (by decide) (by decide)
      have r6 := Runs.call (m := m) (sp := sp) (env := E5) (mem := mem) (dst := 17)
        (args := [RootList.e, RootList.src, RootList.w, RootList.count, RootList.buf, RootList.ctx])
        (by
          simp only [List.mapM_cons, List.mapM_nil, eval_var k5.2.2.1, eval_var k5.1.src, eval_var k5.2.2.2.1,
            eval_var c5, eval_var k5.2.2.2.2.1, eval_var k5.1.ctx]
          rfl) call1
      exact ⟨_, mem1, lead (Runs.ifElse_true 1 (eval_var (by rw [p5, pl]; rfl)) (by decide)
        (Runs.block_cons (Runs.when_true 1 cc (by decide) (Runs.block_cons r6 (Runs.block_nil _ _ _ _ _)))
          (Runs.block_nil _ _ _ _ _))), k6.1, k6.2.1, k6.2.2.2.2.1, k6.2.2.2.2.2, frameReady mem1 keep1,
        ⟨fun i hi => nodeAt_of_holds held1 (by rw [rootsSize]; omega), by rw [rootsSize]; exact Nat.le_refl _,
          .inr (by rw [rootsSize, pre.usize]; omega), by rw [assign_ne (by decide)]; exact n5,
          by rw [assign_ne (by decide)]; exact l5, by rw [assign_ne (by decide)]; exact c5, keep1⟩⟩
  · -- Elements of any other type, rooted one by one.
    have pl' : plain element = false := by simpa using pl
    have roomV := pre.roomVar pl'
    have cpl : compNodes element b start stop count =
        joinNodes (variableRoots element b (elementRanges element b start stop count)) := by
      simp [compNodes, pl']
    rw [cpl]
    have epre : ElemPre w mem element ea base start stop count buf span ctx table zeros pad mask b :=
      { ready := pre.ready, plan := pre.plan, fits := pre.fits, holds := pre.holds, bAcc := pre.bAcc,
        ordered := ordered, inside := inside, small := pre.small, spread := pre.spread, sound := pre.sound,
        thin := pre.thin, ranges := pre.ranges,
        offsets := fun fx cpos => by
          rcases pre.varCount fx with ⟨_, h⟩ | ⟨_, _, h⟩
          · omega
          · exact h,
        room := roomV, below := by omega, rAcc := pre.rAcc, rSlack := pre.rSlack, rB := pre.rB, rPad := pre.rPad,
        rCtx := pre.rCtx, rTable := pre.rTable, rZeros := pre.rZeros, rPlan := pre.rPlan, bPad := pre.bPad,
        planPad := pre.planPad, usize := pre.usize }
    obtain ⟨mem1, call1, roots, ready1, keep1⟩ := rootElements_calls fns ih (sp := sp) (by omega) epre
    have k6 := keepW E5 17 0 k5 (by decide) (by decide) (by decide) (by decide) (by decide)
    have r6 := Runs.call (m := m) (sp := sp) (env := E5) (mem := mem) (dst := 17)
      (args := [RootList.e, RootList.src, RootList.size, RootList.count, RootList.buf, RootList.ctx])
      (by
        simp only [List.mapM_cons, List.mapM_nil, eval_var k5.2.2.1, eval_var k5.1.src, eval_var k5.1.size,
          eval_var c5, eval_var k5.2.2.2.2.1, eval_var k5.1.ctx]
        rfl) call1
    let rs := variableRoots element b (elementRanges element b start stop count)
    have rlen : rs.length = count := by
      simp only [rs, variableRoots_eq_map, List.length_map]; exact pre.rlen
    have sized : ∀ r ∈ rs, r.size = 32 := by
      intro r mem'
      simp only [rs, variableRoots_eq_map, List.mem_map] at mem'
      obtain ⟨q, qm, rfl⟩ := mem'
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem qm
      have hi' : i < count := by rw [← pre.rlen]; exact hi
      obtain ⟨_, ord, stp, acc⟩ := pre.ranges i hi'
      have at_ : elemRange element b start stop count i = (elementRanges element b start stop count)[i] := by
        simp only [elemRange, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      rw [at_] at ord stp acc
      exact rootOf_size pre.sound ord (by omega) pre.small acc
    have joinSize := (RootProof.joinNodes_nodes rs sized).2
    rw [rlen] at joinSize
    exact ⟨_, mem1, lead (Runs.ifElse_false (eval_var (by rw [p5, pl']; rfl)) (Runs.block_cons r6
      (Runs.block_nil _ _ _ _ _))), k6.1, k6.2.1, k6.2.2.2.2.1, k6.2.2.2.2.2, ready1,
      ⟨fun i hi => by
        rw [roots i hi, nodeOf_joinNodes sized (by omega)]
        simp only [rs]
        rw [elemRoots_getElem], by rw [joinSize]; exact Nat.le_refl _, .inr (by rw [joinSize, pre.usize]; omega),
        by rw [assign_ne (by decide)]; exact n5, by rw [assign_ne (by decide)]; exact l5,
        by rw [assign_ne (by decide)]; exact c5, keep1⟩⟩


/-! ### Trees over the nodes -/

/-- A tree over nodes memory holds, node by node as a buffer's, is the tree over the buffer's nodes. -/
theorem merkleizeDepth_of_nodeAt {mem : Memory} {a n depth : Nat} {x : ByteArray}
    (h : ∀ i < n, nodeAt mem (a + 32 * i) = nodeOf x 0 i) (inside : 32 * n ≤ x.size)
    (small : n = 0 ∨ x.size < USize.size) (fits : n ≤ 2 ^ depth) (usize : USize.size = 2 ^ 64)
    (nsmall : 32 * n < 2 ^ 63) :
    (merkleizeDepth (bytesAt mem a (32 * n)) n depth).data = (merkleizeDepth x n depth).data := by
  rcases small with rfl | small
  · simp [merkleizeDepth, merkleizeAt]
  · have size : (bytesAt mem a (32 * n)).size = 32 * n := by simp [bytesAt, ByteArray.size]
    rw [(merkleizeDepth_spec _ n depth fits (by omega) (by omega)).2, (merkleizeDepth_spec x n depth fits inside small).2,
      nodesFrom_of_nodeAt h]

/-- A progressive tree over nodes memory holds, node by node as a buffer's, is the tree over the buffer's nodes. -/
theorem merkleizeProgressive_of_nodeAt {mem : Memory} {a n : Nat} {x : ByteArray}
    (h : ∀ i < n, nodeAt mem (a + 32 * i) = nodeOf x 0 i) (inside : 32 * n ≤ x.size)
    (small : n = 0 ∨ x.size < USize.size) (usize : USize.size = 2 ^ 64) (nsmall : 32 * n < 2 ^ 63) :
    (merkleizeProgressive (bytesAt mem a (32 * n)) n).data = (merkleizeProgressive x n).data := by
  rcases small with rfl | small
  · simp [merkleizeProgressive, spine]
  · have size : (bytesAt mem a (32 * n)).size = 32 * n := by simp [bytesAt, ByteArray.size]
    rw [(merkleizeProgressive_spec _ n (by omega) (by omega)).2, (merkleizeProgressive_spec x n inside small).2,
      nodesFrom_of_nodeAt h]

/-! ### Saturated widths -/

mutual

/-- A saturated width is at most the width. -/
theorem satWidth_le_width : (d : Desc) → satWidth d ≤ fixedWidth d
  | .bool => Nat.le_refl _
  | .bitVector _ => Nat.le_refl _
  | .uint _ | .byteVector _ => by simp only [satWidth, sat, fixedWidth]; omega
  | .vector e l => by
    simp only [satWidth, fixedWidth, smul, sat]
    have := satWidth_le_width e
    have := Nat.mul_le_mul this (show min l scratchCap ≤ l by omega)
    omega
  | .container _ fs | .progressiveContainer _ _ fs => by
    simp only [satWidth, fixedWidth]
    have := satFieldsWidth_le_width fs 0
    omega
  | .byteList _ | .bitList _ | .progressiveBitList _ | .list _ _ | .progressiveList _ _ | .compatibleUnion _ _ => by
    simp [satWidth, fixedWidth]

/-- A saturated total width is at most the total width, after the same width so far. -/
theorem satFieldsWidth_le_width : (fs : List Desc) → ∀ acc, satFieldsWidth fs acc ≤ acc + fieldsWidth fs
  | [], acc => by simp [satFieldsWidth, fieldsWidth]
  | f :: rest, acc => by
    simp only [satFieldsWidth, fieldsWidth]
    have h1 := satFieldsWidth_le_width rest (sadd acc (satWidth f))
    have h2 := satWidth_le_width f
    have h3 : sadd acc (satWidth f) ≤ acc + satWidth f := Nat.min_le_left _ _
    omega

end

mutual

/-- A saturated width is zero only for a width of zero. -/
theorem width_zero_of_sat : (d : Desc) → satWidth d = 0 → fixedWidth d = 0
  | .bool, h => by simp [satWidth] at h
  | .bitVector _, h => h
  | .uint _, h | .byteVector _, h => by
    simp only [satWidth, sat] at h; simp only [fixedWidth]; have := cap_eq; omega
  | .vector e l, h => by
    simp only [satWidth, smul, sat] at h
    simp only [fixedWidth]
    have capv := cap_eq
    have : satWidth e * min l scratchCap = 0 := by omega
    rcases Nat.mul_eq_zero.mp this with z | z
    · rw [width_zero_of_sat e z, Nat.zero_mul]
    · have : l = 0 := by omega
      rw [this, Nat.mul_zero]
  | .container _ fs, h | .progressiveContainer _ _ fs, h => by
    simp only [satWidth] at h
    simp only [fixedWidth]
    have := fieldsWidth_zero_of_sat fs 0 h
    omega
  | .byteList _, _ | .bitList _, _ | .progressiveBitList _, _ | .list _ _, _ | .progressiveList _ _, _
  | .compatibleUnion _ _, _ => by simp [fixedWidth]

/-- A saturated total width is zero only for a total width of zero, after a width so far. -/
theorem fieldsWidth_zero_of_sat : (fs : List Desc) → ∀ acc, satFieldsWidth fs acc = 0 → acc + fieldsWidth fs = 0
  | [], acc, h => by simpa [satFieldsWidth, fieldsWidth] using h
  | f :: rest, acc, h => by
    simp only [satFieldsWidth] at h
    simp only [fieldsWidth]
    have := fieldsWidth_zero_of_sat rest _ h
    have capv := cap_eq
    simp only [sadd, sat] at this
    have z : satWidth f = 0 := by omega
    rw [width_zero_of_sat f z]
    omega

end


/-! ### The driver -/

/-- The list driver's statements for basic elements. -/
abbrev listBasic : List Stmt :=
  [RootList.nodes ::= ceilDiv RootList.size 32,
    callInto RootList.sink "ssz_gather" [RootList.buf, RootList.src, 1, RootList.size, 0,
      32 * RootList.nodes + 32 - RootList.size],
    RootList.cap ::= RootList.limit / (32 / RootList.w) + ne (RootList.limit % (32 / RootList.w)) 0,
    RootList.count ::= RootList.size / RootList.w]

/-- The list driver's head: the tag, the limit and the element's plan, the buffer, and the element's width. -/
abbrev listHead : Stmt :=
  ifElse (eq RootList.tag 8) [RootList.limit ::= ld (RootList.p + 8), RootList.e ::= RootList.p + 16]
    [RootList.limit ::= 0, RootList.e ::= RootList.p + 24]

/-- The list driver's tree: at the limit's depth, or on a progressive spine. -/
abbrev listTree : Stmt :=
  ifElse (eq RootList.tag 8)
    [callInto RootList.d "ssz_depth_for" [RootList.cap],
      callInto RootList.sink "ssz_merkleize" [RootList.buf, RootList.nodes, RootList.d, RootList.scratch,
        RootList.buf + 32 * RootList.nodes + 32, RootList.ctx]]
    [callInto RootList.sink "ssz_root_progressive" [RootList.buf, RootList.nodes, RootList.scratch,
      RootList.buf + 32 * RootList.nodes + 32, RootList.ctx]]

/-- The list driver's body, in its parts. -/
theorem rootList_body_eq : RootList.fn.body = .block ([RootList.tag ::= ld RootList.p, listHead,
    RootList.buf ::= RootList.scratch + 64, callInto RootList.w "ssz_plan_fixed_width" [RootList.e],
    ifElse (le (ld RootList.e) 1) listBasic listComposite, listTree] ++
    (lengthNodeAt (Expr.var 4 + 32) (Expr.var 12) ++
      [.call "ssz_hash_pairs" [Expr.var 3, Expr.var 4, Expr.var 4 + 32, 1, Expr.var 5] 17])) := rfl

/-- The list driver's frame holds twenty-five words. -/
theorem listFrame : RootList.fn.frame = 25 := by decide

/-- What a list type gives the list driver: its tag, limit and element plan, its decoding, and its root's shape. -/
theorem list_shape {w : World} {mem : Memory} {d element : Desc} {p : Nat} {b : ByteArray} {start stop : Nat}
    (shape : (∃ limit, d = .list element limit) ∨ (∃ lim, d = .progressiveList element lim))
    (plan : WordsAt w mem p (Plan.words d)) (fits : Fits (Plan.words d)) (sound : d.wellFormed = .ok ())
    (thin : narrow d = true) (accepted : ∃ v, deserialize d (slice b start stop) = .ok v) :
    ∃ (L ea : Nat) (lim : Option Nat) (slices : List Bytes) (values : List Value),
      (Plan.tag d = 8 ∨ Plan.tag d = 9) ∧ L < 2 ^ 64 ∧
      (Plan.tag d = 8 → (w.access (p + 8) 8 = true ∧ readLE mem (p + 8) 8 = UInt64.ofNat L) ∧
        ea = p + 16 ∧ ∀ l, lim = some l → l = L) ∧
      (Plan.tag d = 9 → L = 0 ∧ ea = p + 24) ∧ (∀ l, lim = some l → slices.length ≤ l) ∧
      (Plan.tag d = 8 → lim = some L) ∧
      WordsAt w mem ea (Plan.words element) ∧ Fits (Plan.words element) ∧
      p ≤ ea ∧ ea + 8 * (Plan.words element).length ≤ p + 8 * (Plan.words d).length ∧
      element.wellFormed = .ok () ∧ narrow element = true ∧
      listSlices element lim (slice b start stop) = .ok slices ∧ deserializeEach element slices = .ok values ∧
      (∀ s, varNeed d s = varNeed (.list element 0) s) ∧ rootStack d = rootStack element + 1024 ∧
      rootOf d b start stop = (if Plan.tag d = 8 then
          hashPair (merkleizeCapacity (sequenceNodes element b start stop L).1 (sequenceNodes element b start stop L).2.1
            (sequenceNodes element b start stop L).2.2) (lengthNode (elementCount element b start stop))
        else hashPair (merkleizeProgressive (sequenceNodes element b start stop L).1
          (sequenceNodes element b start stop L).2.1) (lengthNode (elementCount element b start stop))) := by
  obtain ⟨v, read⟩ := accepted
  rcases shape with ⟨limit, rfl⟩ | ⟨lim, rfl⟩
  · simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    rename_i slices cut
    split at read
    · cases read
    rename_i values decoded
    have words : Plan.words (.list element limit) = [8, limit] ++ Plan.words element := by rw [Plan.words]
    have planE := (wordsAt_split (by rw [← words]; exact plan)).2
    have fitsS := fits_split (show Fits ([8, limit] ++ Plan.words element) by rw [← words]; exact fits)
    have lsmall : limit < 2 ^ 64 := fitsS.1 limit (by simp)
    have soundE : element.wellFormed = .ok () := by
      simp [Desc.wellFormed] at sound; exact sound
    have caps := (listSlices_facts cut).1
    refine ⟨limit, p + 16, some limit, slices, values, .inl rfl, lsmall, fun _ => ⟨?_, rfl, fun l h => by cases h; rfl⟩,
      fun h => absurd h (by simp [Plan.tag]), caps, fun _ => rfl, by simpa using planE, fitsS.2, by omega,
      by rw [words, List.length_append]; simp; omega, soundE, by simpa [narrow] using thin, cut, decoded,
      fun s => rfl, ?_, ?_⟩
    · obtain ⟨acc, rd⟩ := plan.read 1 (by simp [Plan.words])
      exact ⟨acc, rd⟩
    · have h : (Desc.list element limit).nesting = element.nesting + 1 := by simp [Desc.nesting]
      unfold rootStack; rw [h]; omega
    · rw [rootOf]; simp [Plan.tag]
  · simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    rename_i slices cut
    split at read
    · cases read
    rename_i values decoded
    have words : Plan.words (.progressiveList element lim) = (9 :: Plan.bound lim) ++ Plan.words element := by
      rw [Plan.words]
    have blen : (9 :: Plan.bound lim).length = 3 := by cases lim <;> rfl
    have planE := (wordsAt_split (by rw [← words]; exact plan)).2
    rw [blen] at planE
    have fitsS := fits_split (show Fits ((9 :: Plan.bound lim) ++ Plan.words element) by rw [← words]; exact fits)
    have soundE : element.wellFormed = .ok () := by
      simp [Desc.wellFormed] at sound; exact sound
    have caps := (listSlices_facts cut).1
    refine ⟨0, p + 24, lim, slices, values, .inr rfl, by decide, fun h => absurd h (by simp [Plan.tag]),
      fun _ => ⟨rfl, rfl⟩, caps, fun h => absurd h (by simp [Plan.tag]), by simpa using planE, fitsS.2, by omega,
      by rw [words, List.length_append, blen]; omega, soundE, by simpa [narrow] using thin, cut, decoded,
      fun s => rfl, ?_, ?_⟩
    · have h : (Desc.progressiveList element lim).nesting = element.nesting + 1 := by simp [Desc.nesting]
      unfold rootStack; rw [h]; omega
    · rw [rootOf]; simp [Plan.tag]


set_option maxHeartbeats 16000000 in
/-- The list driver's body writes the Lean root of a list's range, bounded or progressive. -/
theorem rootList_body {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RangeFns m)
    {element : Desc} (ih : RootOfOk m w element) {d : Desc}
    (shape : (∃ limit, d = .list element limit) ∨ (∃ lim, d = .progressiveList element lim))
    {sp : Nat} {mem : Memory} {p base start stop out scratch ctx table zeros pad : Nat} {mask : UInt64}
    {b : ByteArray} (room : w.stackLo + rootStack element + 816 ≤ sp)
    (pre : RangePre w mem d p base start stop out scratch ctx table zeros pad mask b)
    {env : Env} (ev : RangeEnv env p (base + start) (stop - start) out scratch ctx) :
    ∃ env' mem', Runs m w sp env mem RootList.fn.body env' mem' ∧
      RangePost w mem mem' out scratch (varNeed d (stop - start)) ctx table zeros pad mask (rootOf d b start stop) := by
  have usize := pre.usize
  have small := pre.small
  unfold RootProof.Small at small
  rw [usize] at small
  have ordered := pre.ordered
  have inside := pre.inside
  have spread := pre.spread
  have bound : addressBound = 2 ^ 63 := rfl
  have zh : zeroHeights = 64 := rfl
  have capv := cap_eq
  have stackT : treeStack = 10552 := rfl
  have stackR : 12288 ≤ rootStack element := by simp only [rootStack]; omega
  obtain ⟨L, ea, lim, slices, values, tag89, hL, bnd, prg, capped, limEq, planE, fitsE, eaLo, eaHi, soundE, thinE,
    cut, decoded, needEq, -, rootEq⟩ := list_shape shape pre.plan pre.fits pre.sound pre.thin pre.accepted
  obtain ⟨counted, ranges, rlen, capsL, fixedFill, varCount⟩ := list_decoded ordered inside cut decoded
  -- The scratch: the root and the count's node, the nodes and a spare, then the elements' or the tree's room.
  let nB := nodesBound element (stop - start)
  have elemsLe : (if element.isBasic then 0 else if plain element then
      max (rootsNeed element 1) (rootsNeed element (min nB recordsPerChunk)) else varNeed element (stop - start)) ≤
      scratchCap := by
    split
    · omega
    · split
      · exact Nat.max_le.mpr ⟨rootsNeed_le _ _, rootsNeed_le _ _⟩
      · exact varNeed_le _ _
  generalize hE : (if element.isBasic then 0 else if plain element then
      max (rootsNeed element 1) (rootsNeed element (min nB recordsPerChunk)) else varNeed element (stop - start)) = E
    at elemsLe
  have need : varNeed d (stop - start) = 96 + 32 * nB + max E (2560 + 2048 + 32 * nB) := by
    have below := pre.below
    rw [needEq] at below ⊢
    simp only [varNeed] at below ⊢
    rw [hE] at below ⊢
    simp only [treeNeed, RootProgressive.spineBytes, zeroHeights] at below ⊢
    simp only [sadd, smul, sat] at below ⊢
    omega
  have sAcc := pre.sAcc
  have sSlack := pre.sSlack
  have sB := pre.sB
  have sPad := pre.sPad
  have sCtx := pre.sCtx
  have sTable := pre.sTable
  have sZeros := pre.sZeros
  have sOut := pre.sOut
  have sPlan := pre.sPlan
  have below := pre.below
  rw [need] at sAcc sSlack sB sPad sCtx sTable sZeros sOut sPlan below
  have as := access_bound sAcc
  have nBsize : nB ≤ stop - start := by
    simp only [nB, nodesBound, sat]
    split
    · simp only [nodesFor]; omega
    · split
      · split
        · omega
        · exact Nat.le_trans (Nat.min_le_left _ _) (Nat.div_le_self _ _)
      · exact Nat.le_trans (Nat.min_le_left _ _) (Nat.div_le_self _ _)
  -- The tag, the limit and the element's plan.
  have tagE := eval_tag (e := RootList.p) pre.plan (eval_var ev.p)
  have s1 := Runs.set' (m := m) (w := w) (sp := sp) (x := 6) tagE
  have ev1 := ev.write (x := 6) (Plan.tag d).toUInt64 (by decide)
  have t1 : Asm.assign env 6 (Plan.tag d).toUInt64 6 = (Plan.tag d).toUInt64 := assign_eq
  generalize Asm.assign env 6 (Plan.tag d).toUInt64 = E1 at s1 ev1 t1
  have tagSmall : Plan.tag d < 2 ^ 64 := by have := tag_lt d; omega
  have c8 := eval_eq (w := w) (env := E1) (mem := mem) (a := RootList.tag) (b := 8) (eval_var t1) (eval_lit 8)
    tagSmall (by decide)
  obtain ⟨E2, s2, ev2, t2, l2, e2⟩ : ∃ E2, Runs m w sp E1 mem listHead E2 mem ∧
      RangeEnv E2 p (base + start) (stop - start) out scratch ctx ∧ E2 6 = (Plan.tag d).toUInt64 ∧
      E2 7 = UInt64.ofNat L ∧ E2 8 = UInt64.ofNat ea := by
    rcases tag89 with h8 | h9
    · rw [if_pos h8] at c8
      obtain ⟨⟨acc, rd⟩, hea, -⟩ := bnd h8
      have lw : eval w E1 mem (ld (RootList.p + 8)) = some (UInt64.ofNat L) := by
        rw [eval_ld_of (eval_add (eval_var ev1.p) (eval_lit 8)) (by have := access_end acc; omega) acc, rd]
      have r1 := Runs.set' (m := m) (w := w) (sp := sp) (env := E1) (mem := mem) (x := 7) lw
      have r2 := Runs.set' (m := m) (w := w) (sp := sp) (env := Asm.assign E1 7 (UInt64.ofNat L)) (mem := mem) (x := 8)
        (eval_add (eval_var (show Asm.assign E1 7 (UInt64.ofNat L) 0 = UInt64.ofNat p by
          rw [assign_ne (by decide)]; exact ev1.p)) (eval_lit 16))
      refine ⟨_, Runs.ifElse_true 1 c8 (by decide) (Runs.block_cons r1 (Runs.block_cons r2
        (Runs.block_nil _ _ _ _ _))), (ev1.write _ (by decide)).write _ (by decide),
        by rw [assign_ne (by decide), assign_ne (by decide)]; exact t1,
        by rw [assign_ne (by decide), assign_eq], by rw [assign_eq, hea]⟩
    · rw [if_neg (by omega)] at c8
      obtain ⟨hL0, hea⟩ := prg h9
      have r1 := Runs.set' (m := m) (w := w) (sp := sp) (env := E1) (mem := mem) (x := 7) (eval_lit 0)
      have r2 := Runs.set' (m := m) (w := w) (sp := sp) (env := Asm.assign E1 7 (UInt64.ofNat 0)) (mem := mem) (x := 8)
        (eval_add (eval_var (show Asm.assign E1 7 (UInt64.ofNat 0) 0 = UInt64.ofNat p by
          rw [assign_ne (by decide)]; exact ev1.p)) (eval_lit 24))
      refine ⟨_, Runs.ifElse_false c8 (Runs.block_cons r1 (Runs.block_cons r2 (Runs.block_nil _ _ _ _ _))),
        (ev1.write _ (by decide)).write _ (by decide),
        by rw [assign_ne (by decide), assign_ne (by decide)]; exact t1,
        by rw [assign_ne (by decide), assign_eq, hL0], by rw [assign_eq, hea]⟩
  -- The buffer and the element's width.
  have s3 := Runs.set' (m := m) (w := w) (sp := sp) (env := E2) (mem := mem) (x := 15)
    (eval_add (eval_var ev2.scratch) (eval_lit 64))
  have widthCall := planWidth_calls fns.roots.plan element ea sp mem planE soundE thinE (by
    simp only [rootStack] at room; omega)
  have s4 := Runs.call (m := m) (sp := sp) (env := Asm.assign E2 15 (UInt64.ofNat (scratch + 64))) (mem := mem)
    (dst := 9) (args := [RootList.e]) (by
      simp only [List.mapM_cons, List.mapM_nil, eval_var (show Asm.assign E2 15 (UInt64.ofNat (scratch + 64)) 8 =
        UInt64.ofNat ea by rw [assign_ne (by decide)]; exact e2)]; rfl) widthCall
  let E4 := Asm.assign (Asm.assign E2 15 (UInt64.ofNat (scratch + 64))) 9 (fixedWidth element).toUInt64
  have ev4 : RangeEnv E4 p (base + start) (stop - start) out scratch ctx := (ev2.write _ (by decide)).write _ (by decide)
  have t4 : E4 6 = (Plan.tag d).toUInt64 := by simp only [E4]; rw [assign_ne (by decide), assign_ne (by decide)]; exact t2
  have l4 : E4 7 = UInt64.ofNat L := by simp only [E4]; rw [assign_ne (by decide), assign_ne (by decide)]; exact l2
  have e4 : E4 8 = UInt64.ofNat ea := by simp only [E4]; rw [assign_ne (by decide), assign_ne (by decide)]; exact e2
  have w4 : E4 9 = UInt64.ofNat (fixedWidth element) := assign_eq
  have b4 : E4 15 = UInt64.ofNat (scratch + 64) := by simp only [E4]; rw [assign_ne (by decide)]; exact assign_eq
  -- The nodes, packed or rooted, at the buffer.
  have stackS : 112 * element.nesting ≤ rootStack element := by simp only [rootStack]; omega
  have rRegion : scratch + 64 + (32 + 32 * nB + max E (2560 + 2048 + 32 * nB)) =
      scratch + (96 + 32 * nB + max E (2560 + 2048 + 32 * nB)) := by omega
  obtain ⟨E5, mem1, run5, ev5, t5, b5, ready1, nodes, nLe⟩ : ∃ E5 mem1,
      Runs m w sp E4 mem (ifElse (le (ld RootList.e) 1) listBasic listComposite) E5 mem1 ∧
      RangeEnv E5 p (base + start) (stop - start) out scratch ctx ∧ E5 6 = (Plan.tag d).toUInt64 ∧
      E5 15 = UInt64.ofNat (scratch + 64) ∧ RootReady w ctx table zeros pad mask mem1 ∧
      ListNodes mem mem1 E5 (sequenceNodes element b start stop L).1 (sequenceNodes element b start stop L).2.1
        (sequenceNodes element b start stop L).2.2 (elementCount element b start stop) (scratch + 64)
        (32 + 32 * nB + max E (2560 + 2048 + 32 * nB)) pad ∧ (sequenceNodes element b start stop L).2.1 ≤ nB := by
    have cb := eval_le_tag (e := element) (eval_tag (e := RootList.e) planE (eval_var e4))
    by_cases basic : element.isBasic = true
    · rw [if_pos basic] at cb
      have hw := basic_width basic soundE
      have fx : hasWidth element = true := by cases element <;> simp_all [Desc.isBasic, hasWidth]
      have wpos : 0 < fixedWidth element := by omega
      have nBeq : nB = nodesFor (stop - start) := by
        simp only [nB, nodesBound, basic, if_true, sat]; simp only [nodesFor] at nBsize ⊢; omega
      obtain ⟨E5, mem1, run, ev5, -, b5, z5, ln⟩ := listBasic_runs (pad := pad) gmod (sp := sp) (by omega) pre.holds
        pre.bAcc ordered inside small usize hw hL (access_sub sAcc (by omega) (by rw [← nBeq]; omega))
        (apart_sub sB (by omega) (by rw [← nBeq]; omega)) ev4 l4 w4 b4
      have seq : sequenceNodes element b start stop L = (packRange b start stop, nodesFor (stop - start),
          nodesFor (L * fixedWidth element)) := by
        rw [sequenceNodes]; simp [basic, basic_itemLength basic]
      have cnt : elementCount element b start stop = (stop - start) / fixedWidth element := by
        simp only [elementCount, fixedSize_eq, fx, if_true]; simp; omega
      rw [seq, cnt]
      refine ⟨E5, mem1, Runs.ifElse_true 1 cb (by decide) run, ev5, by rw [z5]; exact t4, b5,
        pre.ready.within (o := scratch + 64) (n := 32 * nodesFor (stop - start) + 32)
          (apart_sub sCtx (by omega) (by rw [← nBeq]; omega)) (apart_sub sTable (by omega) (by rw [← nBeq]; omega))
          (apart_sub sZeros (by omega) (by rw [← nBeq]; omega)) ln.frame,
        { ln with frame := fun a o pd => ln.frame a (fun h => o ⟨h.1, by rw [← nBeq] at h; omega⟩) pd },
        by rw [nBeq]; exact Nat.le_refl _⟩
    · rw [if_neg basic] at cb
      have nb : element.isBasic = false := by simpa using basic
      -- The count is at most the node bound.
      have cntLe : slices.length ≤ nB := by
        simp only [nB, nodesBound, nb, Bool.false_eq_true, if_false]
        by_cases fx : hasWidth element = true
        · obtain ⟨fill, zero⟩ := fixedFill fx
          rw [if_pos fx]
          by_cases z : satWidth element = 0
          · rw [if_pos z, zero (width_zero_of_sat element z)]; exact Nat.zero_le _
          · rw [if_neg z]
            have le := satWidth_le_width element
            have : slices.length ≤ (stop - start) / satWidth element := by
              rw [← fill]
              exact Nat.le_trans (Nat.le_of_eq (Nat.mul_div_cancel _ (by omega)).symm)
                (Nat.div_le_div_left le (by omega))
            have : slices.length ≤ stop - start := by rw [← fill]; exact Nat.le_mul_of_pos_right _ (by omega)
            simp only [sat]; omega
        · rw [if_neg fx]
          rcases varCount (by simpa using fx) with ⟨_, h⟩ | ⟨_, _, h⟩
          · omega
          · simp only [sat, bytesPerOffset]; omega
      have cpre : CompPre w mem element ea base start stop slices.length (scratch + 64)
          (32 + 32 * nB + max E (2560 + 2048 + 32 * nB)) ctx table zeros pad mask b :=
        { ready := pre.ready, plan := planE, fits := fitsE, holds := pre.holds, bAcc := pre.bAcc, ordered := ordered,
          inside := inside, small := pre.small, spread := spread, sound := soundE, thin := thinE, notBasic := nb,
          counted := counted, ranges := ranges, rlen := rlen, fixedFill := fixedFill, varCount := varCount,
          roomPlain := fun pl => by
            have em : E = max (rootsNeed element 1) (rootsNeed element (min nB recordsPerChunk)) := by
              rw [← hE]; simp [nb, pl]
            have mono := recordsNeed_mono element cntLe
            omega,
          roomVar := fun pl => by
            have em : E = varNeed element (stop - start) := by rw [← hE]; simp [nb, pl]
            omega,
          below := by omega, rAcc := access_sub sAcc (by omega) (by omega), rSlack := by omega,
          rB := apart_sub sB (by omega) (by omega), rPad := apart_sub sPad (by omega) (by omega),
          rCtx := apart_sub sCtx (by omega) (by omega), rTable := apart_sub sTable (by omega) (by omega),
          rZeros := apart_sub sZeros (by omega) (by omega),
          rPlan := apart_sub' (apart_sub sPlan (by omega) (by omega)) eaLo eaHi, bPad := pre.bPad,
          planPad := apart_comm (apart_sub' (apart_comm pre.planPad) eaLo eaHi), usize := usize }
      obtain ⟨E5, mem1, run, ev5, -, b5, z5, ready1, ln⟩ := listComposite_runs hash gmod fns ih (sp := sp)
        (by omega) cpre ev4 l4 e4 w4 b4
      have seq : sequenceNodes element b start stop L = (compNodes element b start stop slices.length,
          slices.length, L) := by
        rw [sequenceNodes]; simp only [nb, Bool.false_eq_true, if_false, counted, compNodes]
        split <;> rfl
      rw [seq, counted]
      exact ⟨E5, mem1, Runs.ifElse_false cb run, ev5, by rw [z5]; exact t4, b5, ready1, ln, cntLe⟩
  generalize hX : (sequenceNodes element b start stop L).1 = X at nodes rootEq
  generalize hN : (sequenceNodes element b start stop L).2.1 = N at nodes rootEq nLe
  generalize hC : (sequenceNodes element b start stop L).2.2 = C at nodes rootEq
  generalize hcnt : elementCount element b start stop = cnt at nodes rootEq
  have nSmall : 32 * N < 2 ^ 63 := by omega
  -- The tree over the nodes, into the scratch's first node.
  have c8' := eval_eq (w := w) (env := E5) (mem := mem1) (a := RootList.tag) (b := 8) (eval_var t5) (eval_lit 8)
    tagSmall (by decide)
  obtain ⟨E6, mem2, run6, ev6, c6, root6, sz6, keep6⟩ : ∃ E6 mem2, Runs m w sp E5 mem1 listTree E6 mem2 ∧
      RangeEnv E6 p (base + start) (stop - start) out scratch ctx ∧ E6 12 = UInt64.ofNat cnt ∧
      nodeAt mem2 scratch = (if Plan.tag d = 8 then merkleizeCapacity X N C else merkleizeProgressive X N).data ∧
      (if Plan.tag d = 8 then merkleizeCapacity X N C else merkleizeProgressive X N).size = 32 ∧
      ∀ a, ¬ (scratch ≤ a ∧ a < scratch + (96 + 32 * nB + max E (2560 + 2048 + 32 * nB))) →
        ¬ (pad ≤ a ∧ a < pad + 1536) → mem2 a = mem1 a := by
    rcases tag89 with h8 | h9
    · rw [if_pos h8] at c8' ⊢
      have lc := limEq h8
      have cntL : cnt ≤ L := by rw [← hcnt, counted]; exact capsL L lc
      -- The nodes fit the capacity's tree.
      have fitsTree : N ≤ 2 ^ depthFor C := by
        refine Nat.le_trans ?_ (le_two_pow_depthFor C)
        rw [← hN, ← hC, sequenceNodes]
        split
        · rename_i basic
          have fx : hasWidth element = true := by cases element <;> simp_all [Desc.isBasic, hasWidth]
          have fill := (fixedFill fx).1
          simp only [basic_itemLength basic]
          apply nodesFor_mono
          rw [← fill]; exact Nat.mul_le_mul_right _ (capsL L lc)
        · split <;> (simp only; rw [counted]; exact capsL L lc)
      have cSmall : C < 2 ^ 64 := by
        rw [← hC, sequenceNodes]; split
        · rename_i basic
          simp only [basic_itemLength basic, nodesFor]
          have hb := basic_width basic soundE
          have : L * fixedWidth element ≤ L * 32 := Nat.mul_le_mul_left _ (by omega)
          omega
        · split <;> exact hL
      have deep : depthFor C ≤ 64 := depthFor_le_of_le_two_pow (by omega)
      have dframe : DepthFor.fn.frame = 5 := by decide
      have dcall := depthFor_calls (m := m) (w := w) fns.roots.plan.depth (sp := sp) (by rw [dframe]; omega)
        (UInt64.ofNat C) mem1
      rw [ofNat_toNat cSmall] at dcall
      have r1 := Runs.call (m := m) (sp := sp) (env := E5) (mem := mem1) (dst := 16) (args := [RootList.cap])
        (by simp only [List.mapM_cons, List.mapM_nil, eval_var nodes.capV]; rfl) dcall
      have tpre : TreePre w mem1 (scratch + 64) N (depthFor C) scratch (scratch + 64 + 32 * N + 32) ctx table zeros
          pad mask :=
        { ctxAccess := ready1.ctxAccess, maskAt := ready1.maskAt, tableAt := ready1.tableAt,
          zerosAt := ready1.zerosAt, padAt := ready1.padAt, tableBytes := ready1.tableHeld,
          tableAccess := ready1.tableAccess, zeroRoots := ready1.zeroRoots, zerosAccess := ready1.zerosAccess,
          deep := by rw [zh]; omega, fits := fitsTree, nodesAccess := access_sub sAcc (by omega) (by omega),
          outAccess := access_sub sAcc (by omega) (by omega),
          scratchAccess := access_sub sAcc (by omega) (by omega), padAccess := ready1.padAccess,
          scratchNodes := by simp only [Apart]; omega, scratchOut := by simp only [Apart]; omega,
          scratchCtx := apart_sub sCtx (by omega) (by omega), scratchTable := apart_sub sTable (by omega) (by omega),
          scratchZeros := apart_sub sZeros (by omega) (by omega), scratchPad := apart_sub sPad (by omega) (by omega),
          padNodes := apart_comm (apart_sub sPad (by omega) (by omega)), padCtx := ready1.padCtx,
          padTable := ready1.padTable, padZeros := ready1.padZeros, nodesReach := by omega,
          outNodes := by simp only [Apart]; omega, outZeros := apart_sub sZeros (by omega) (by omega) }
      obtain ⟨mem2, call2, root2, keep2⟩ := treeCalls_native hash.merkleize (sp := sp) tpre ready1.kernels (by
        omega) (by rw [usize]; omega)
      have ev' := ev5.write (x := 16) (depthFor C).toUInt64 (by decide)
      have b' : Asm.assign E5 16 (depthFor C).toUInt64 15 = UInt64.ofNat (scratch + 64) := by
        rw [assign_ne (by decide)]; exact b5
      have n' : Asm.assign E5 16 (depthFor C).toUInt64 10 = UInt64.ofNat N := by
        rw [assign_ne (by decide)]; exact nodes.nodesV
      have r2 := Runs.call (m := m) (sp := sp) (env := Asm.assign E5 16 (depthFor C).toUInt64) (mem := mem1)
        (dst := 17) (args := [RootList.buf, RootList.nodes, RootList.d, RootList.scratch,
          RootList.buf + 32 * RootList.nodes + 32, RootList.ctx])
        (by
          simp only [List.mapM_cons, List.mapM_nil, eval_var b', eval_var n',
            eval_var (show Asm.assign E5 16 (depthFor C).toUInt64 16 = UInt64.ofNat (depthFor C) from assign_eq),
            eval_var ev'.scratch, eval_add (eval_add (eval_var b') (eval_mul (eval_lit 32) (eval_var n')))
              (eval_lit 32), eval_var ev'.ctx]
          rfl) call2
      refine ⟨_, mem2, Runs.ifElse_true 1 c8' (by decide) (Runs.block_cons r1 (Runs.block_cons r2
        (Runs.block_nil _ _ _ _ _))), ev'.write 0 (by decide), ?_, ?_, ?_, fun a o pd => ?_⟩
      · rw [assign_ne (by decide), assign_ne (by decide)]; exact nodes.countV
      · rw [root2, merkleizeCapacity, merkleizeDepth_of_nodeAt nodes.held nodes.inside nodes.small fitsTree usize
          nSmall]
      · rcases nodes.small with h0 | hs
        · rw [h0]; simp [merkleizeCapacity, merkleizeDepth, merkleizeAt, zeroRoot_size]
        · exact (merkleizeDepth_spec X N _ fitsTree nodes.inside hs).1
      · exact keep2 a (fun h => o ⟨by omega, by omega⟩) pd (fun h => o ⟨h.1, by omega⟩)
    · rw [if_neg (by omega)] at c8' ⊢
      have pspan : progressiveSpan N = 4608 + 32 * N := rfl
      have ppre : ProgPre w mem1 (scratch + 64) N scratch (scratch + 64 + 32 * N + 32) ctx table zeros pad mask
          (bytesAt mem1 (scratch + 64) (32 * N)) :=
        { ready := ready1, held := holds_bytesAt _ _ _, inside := by simp [bytesAt, ByteArray.size],
          small := by simp only [bytesAt, ByteArray.size, Array.size_ofFn]; rw [usize]; omega,
          few := by omega, nAcc := access_sub sAcc (by omega) (by omega), nReach := by omega,
          oAcc := access_sub sAcc (by omega) (by omega), sAcc := access_sub sAcc (by omega) (by omega),
          sN := by simp only [Apart, bytesAt, ByteArray.size, Array.size_ofFn]; omega,
          sO := by simp only [Apart]; omega,
          sPad := apart_sub sPad (by omega) (by omega), sCtx := apart_sub sCtx (by omega) (by omega),
          sTable := apart_sub sTable (by omega) (by omega), sZeros := apart_sub sZeros (by omega) (by omega),
          oPad := apart_sub sPad (by omega) (by omega), oCtx := apart_sub sCtx (by omega) (by omega),
          oTable := apart_sub sTable (by omega) (by omega), oZeros := apart_sub sZeros (by omega) (by omega),
          nPad := by
            have := apart_sub (o₂ := scratch + 64) (n₂ := 32 * N) sPad (by omega) (by omega)
            simpa [bytesAt, ByteArray.size] using this }
      have pspan : progressiveSpan N = 4608 + 32 * N := rfl
      obtain ⟨mem2, call2, root2, -, keep2⟩ := rootProgressive_calls hash fns.progressive (sp := sp)
        (by omega) ppre
      have r1 := Runs.call (m := m) (sp := sp) (env := E5) (mem := mem1) (dst := 17)
        (args := [RootList.buf, RootList.nodes, RootList.scratch, RootList.buf + 32 * RootList.nodes + 32,
          RootList.ctx])
        (by
          simp only [List.mapM_cons, List.mapM_nil, eval_var b5, eval_var nodes.nodesV, eval_var ev5.scratch,
            eval_add (eval_add (eval_var b5) (eval_mul (eval_lit 32) (eval_var nodes.nodesV))) (eval_lit 32),
            eval_var ev5.ctx]
          rfl) call2
      refine ⟨_, mem2, Runs.ifElse_false c8' (Runs.block_cons r1 (Runs.block_nil _ _ _ _ _)),
        ev5.write 0 (by decide), by rw [assign_ne (by decide)]; exact nodes.countV, ?_, ?_, fun a o pd => ?_⟩
      · rw [root2, merkleizeProgressive_of_nodeAt nodes.held nodes.inside nodes.small usize nSmall]
      · rcases nodes.small with h0 | hs
        · rw [h0]; simp [merkleizeProgressive, spine, zeroNode, ByteArray.size]
        · exact (merkleizeProgressive_spec X N nodes.inside hs).1
      · exact keep2 a (fun h => o ⟨by omega, by omega⟩) (fun h => o ⟨by omega, by omega⟩) pd
  -- The count mixed in.
  have keep12 : ∀ a, ¬ (scratch ≤ a ∧ a < scratch + (96 + 32 * nB + max E (2560 + 2048 + 32 * nB))) →
      ¬ (pad ≤ a ∧ a < pad + 1536) → mem2 a = mem a :=
    fun a o pd => by rw [keep6 a o pd, nodes.frame a (fun h => o ⟨by omega, by omega⟩) pd]
  have ready2 := pre.ready.within (o := scratch) (n := 96 + 32 * nB + max E (2560 + 2048 + 32 * nB)) sCtx sTable
    sZeros keep12
  have cntSmall : cnt < 2 ^ 64 := by
    rw [← hcnt, counted]
    have := RootProof.list_count_le soundE cut
    rw [slice_size b start stop inside] at this
    omega
  obtain ⟨E7, mem3, run7, root7, ready3, keep7⟩ := mixin_ends hash (sp := sp) (by simp only [hashStack]; omega)
    ready2 ev6.scratch ev6.out ev6.ctx (cnt := Expr.var 12) (n := cnt) (fun _ => eval_var c6) cntSmall
    (access_sub sAcc (by omega) (by omega)) (by omega) pre.oAcc (apart_sub sOut (by omega) (by omega))
    (apart_sub sPad (by omega) (by omega)) (apart_sub sCtx (by omega) (by omega))
    (apart_sub sTable (by omega) (by omega)) (apart_sub sZeros (by omega) (by omega)) pre.oPad pre.oCtx pre.oTable
    pre.oZeros 17
  refine ⟨E7, mem3, ?_, ?_, ready3, fun a o s pd => ?_⟩
  · rw [rootList_body_eq]
    exact Runs.block_append (Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons s3 (Runs.block_cons s4
      (Runs.block_cons run5 (Runs.block_cons run6 (Runs.block_nil _ _ _ _ _))))))) run7
  · -- The root: the tree over the nodes, with the count mixed in.
    rw [root7, root6, rootEq]
    split
    · rename_i h8; rw [if_pos h8] at sz6
      rw [RootProof.hashPair_data _ _ sz6 (by simp [lengthNode, ByteArray.size])]
    · rename_i h8; rw [if_neg h8] at sz6
      rw [RootProof.hashPair_data _ _ sz6 (by simp [lengthNode, ByteArray.size])]
  · rw [need] at s
    rw [keep7 a (fun h => s ⟨by omega, by omega⟩) o pd]
    exact keep12 a s pd


/-- The list driver writes the Lean root of a range of a list, bounded or progressive. -/
theorem rootList_ok {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RangeFns m)
    {element : Desc} (ih : RootOfOk m w element) {d : Desc}
    (shape : (∃ limit, d = .list element limit) ∨ (∃ lim, d = .progressiveList element lim)) :
    RangeOk m w "ssz_root_list" d := by
  intro sp mem p base start stop out scratch ctx table zeros pad mask b room pre
  have stack : rootStack d = rootStack element + 1024 := by
    rcases shape with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · have h : (Desc.list element l).nesting = element.nesting + 1 := by simp [Desc.nesting]
      unfold rootStack; rw [h]; omega
    · have h : (Desc.progressiveList element l).nesting = element.nesting + 1 := by simp [Desc.nesting]
      unfold rootStack; rw [h]; omega
  obtain ⟨env', mem', run, post⟩ := rootList_body hash gmod fns ih shape (sp := sp - 8 - 8 * RootList.fn.frame)
    (by rw [listFrame]; omega) pre (rangeEnv_entry _ _ _ _ _ _)
  exact ⟨mem', Calls.fn fns.list (by rw [listFrame]; omega) rfl run rfl, post⟩

end Ssz.Native.Driver
