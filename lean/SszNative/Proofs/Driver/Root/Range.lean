import SszNative.Proofs.Driver.Root.Dispatch
import SszNative.Proofs.Root.Main

/-!
What a call rooting the value a range of an accepted encoding holds needs, and what it leaves.

Every variable-size root driver takes the same six arguments: the plan, the range's address and size, the output, the
scratch, and the context.
The contract is stated once here, and each driver's proof shows its call keeps it.
The value's root is the Lean root of the range, which the root proofs show is the specification's root.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Asm

/-! ### The contract -/

/--
The stack a call rooting a range needs: a tree call at the bottom, and a few frames per level of nesting.

The tree call takes 10552 bytes, and the longest chain of frames per level takes 528.
-/
def rootStack (d : Desc) : Nat := 12288 + 1024 * d.nesting

/--
What a call rooting the value a range of an encoding holds needs.

The context is filled, the plan and the encoding are in memory, and the encoding is one decoding accepts.
The output takes one node, and the scratch as many bytes as the scratch bound gives.
The output and the scratch miss each other, the encoding, the plan, the context's buffers, and the padding area.
-/
structure RangePre (w : World) (mem : Memory) (d : Desc) (p base start stop out scratch ctx table zeros pad : Nat)
    (mask : UInt64) (b : ByteArray) : Prop where
  /-- The context is filled. -/
  ready : RootReady w ctx table zeros pad mask mem
  /-- The type's plan is in memory. -/
  plan : WordsAt w mem p (Plan.words d)
  /-- Every word of the plan fits a machine word. -/
  fits : Fits (Plan.words d)
  /-- The encoding is in memory. -/
  holds : Holds mem base b
  /-- The encoding is usable. -/
  bAcc : w.access base b.size = true
  /-- The range runs forward. -/
  ordered : start ≤ stop
  /-- The range lies inside the encoding. -/
  inside : stop ≤ b.size
  /-- Every buffer the root builds from the encoding has machine-sized offsets. -/
  small : RootProof.Small b
  /-- Twice the encoding's size past its address stays below the address bound. -/
  spread : base + 2 * b.size ≤ addressBound
  /-- The type is legal. -/
  sound : d.wellFormed = .ok ()
  /-- Every fixed-size type inside the type is far below the word size. -/
  thin : narrow d = true
  /-- The range decodes as a value of the type. -/
  accepted : ∃ v, deserialize d (slice b start stop) = .ok v
  /-- The scratch bound is below the cap. -/
  below : varNeed d (stop - start) < scratchCap
  /-- The scratch is usable. -/
  sAcc : w.access scratch (varNeed d (stop - start)) = true
  /-- The scratch ends a node short of the address bound. -/
  sSlack : scratch + varNeed d (stop - start) + 32 ≤ addressBound
  /-- The output is usable. -/
  oAcc : w.access out 32 = true
  /-- The scratch misses the encoding. -/
  sB : Apart (scratch, varNeed d (stop - start)) (base, b.size)
  /-- It misses the padding area. -/
  sPad : Apart (scratch, varNeed d (stop - start)) (pad, 1536)
  /-- It misses the context. -/
  sCtx : Apart (scratch, varNeed d (stop - start)) (ctx, 32)
  /-- It misses the table. -/
  sTable : Apart (scratch, varNeed d (stop - start)) (table, Kernel.tableSize)
  /-- It misses the zero roots. -/
  sZeros : Apart (scratch, varNeed d (stop - start)) (zeros, 32 * (zeroHeights + 1))
  /-- It misses the plan. -/
  sPlan : Apart (scratch, varNeed d (stop - start)) (p, 8 * (Plan.words d).length)
  /-- It misses the output. -/
  sOut : Apart (scratch, varNeed d (stop - start)) (out, 32)
  /-- The output misses the encoding. -/
  oB : Apart (out, 32) (base, b.size)
  /-- It misses the padding area. -/
  oPad : Apart (out, 32) (pad, 1536)
  /-- It misses the context. -/
  oCtx : Apart (out, 32) (ctx, 32)
  /-- It misses the table. -/
  oTable : Apart (out, 32) (table, Kernel.tableSize)
  /-- It misses the zero roots. -/
  oZeros : Apart (out, 32) (zeros, 32 * (zeroHeights + 1))
  /-- It misses the plan. -/
  oPlan : Apart (out, 32) (p, 8 * (Plan.words d).length)
  /-- The encoding misses the padding area. -/
  bPad : Apart (base, b.size) (pad, 1536)
  /-- The plan misses the padding area. -/
  planPad : Apart (p, 8 * (Plan.words d).length) (pad, 1536)
  /-- A machine word holds a full 64-bit size. -/
  usize : USize.size = 2 ^ 64

/--
What a call rooting a range leaves: the root at the output, the context still filled, and memory as it was outside
the output, the scratch, and the padding area.
-/
def RangePost (w : World) (mem mem' : Memory) (out scratch span ctx table zeros pad : Nat) (mask : UInt64)
    (root : ByteArray) : Prop :=
  nodeAt mem' out = root.data ∧ RootReady w ctx table zeros pad mask mem' ∧
    ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (scratch ≤ a ∧ a < scratch + span) → ¬ (pad ≤ a ∧ a < pad + 1536) →
      mem' a = mem a

/-- A driver of a name roots the ranges of a type's encodings, from any state meeting its needs and a stack some bytes
deeper than the type's. -/
def RangeOkAt (m : Module) (w : World) (name : String) (d : Desc) (extra : Nat) : Prop :=
  ∀ (sp : Nat) (mem : Memory) (p base start stop out scratch ctx table zeros pad : Nat) (mask : UInt64)
    (b : ByteArray), w.stackLo + rootStack d + extra ≤ sp →
    RangePre w mem d p base start stop out scratch ctx table zeros pad mask b →
    ∃ mem', Calls m w name sp [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (stop - start),
        UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx] mem 0 mem' ∧
      RangePost w mem mem' out scratch (varNeed d (stop - start)) ctx table zeros pad mask (rootOf d b start stop)

/-- A driver of a name roots the ranges of a type's encodings, from the type's stack. -/
abbrev RangeOk (m : Module) (w : World) (name : String) (d : Desc) : Prop := RangeOkAt m w name d 0

/-- The dispatcher roots the ranges of a type's encodings, from a frame's room more than the type's stack. -/
abbrev RootOfOk (m : Module) (w : World) (d : Desc) : Prop := RangeOkAt m w "ssz_root_of" d 256

/-- The variables holding a range driver's arguments. -/
structure RangeEnv (env : Env) (p src size out scratch ctx : Nat) : Prop where
  /-- The plan node. -/
  p : env 0 = UInt64.ofNat p
  /-- The range's address. -/
  src : env 1 = UInt64.ofNat src
  /-- The range's size. -/
  size : env 2 = UInt64.ofNat size
  /-- The output. -/
  out : env 3 = UInt64.ofNat out
  /-- The scratch. -/
  scratch : env 4 = UInt64.ofNat scratch
  /-- The context. -/
  ctx : env 5 = UInt64.ofNat ctx

/-- Writing a variable past the arguments keeps them. -/
theorem RangeEnv.write {env : Env} {p src size out scratch ctx : Nat} (h : RangeEnv env p src size out scratch ctx)
    {x : Nat} (v : UInt64) (hx : 6 ≤ x) : RangeEnv (Asm.assign env x v) p src size out scratch ctx :=
  ⟨by rw [assign_ne (by omega), h.p], by rw [assign_ne (by omega), h.src], by rw [assign_ne (by omega), h.size],
    by rw [assign_ne (by omega), h.out], by rw [assign_ne (by omega), h.scratch], by rw [assign_ne (by omega), h.ctx]⟩

/-- A range driver's arguments, as its entry variables. -/
theorem rangeEnv_entry (p src size out scratch ctx : Nat) :
    RangeEnv (entryEnv [UInt64.ofNat p, UInt64.ofNat src, UInt64.ofNat size, UInt64.ofNat out,
      UInt64.ofNat scratch, UInt64.ofNat ctx]) p src size out scratch ctx :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The functions the range drivers call, each under its name. -/
structure RangeFns (m : Module) : Prop where
  /-- The fixed-size roots and the plan readers. -/
  roots : RootsFns m
  /-- The progressive tree. -/
  progressive : m.fns.lookup "ssz_root_progressive" = some RootProgressive.fn
  /-- The roots of a sequence's elements. -/
  elements : m.fns.lookup "ssz_root_elements" = some RootElements.fn
  /-- The roots of a struct's fields. -/
  fields : m.fns.lookup "ssz_root_fields" = some RootFields.fn
  /-- Byte lists. -/
  bytes : m.fns.lookup "ssz_root_bytes" = some RootBytes.fn
  /-- Bit lists. -/
  bits : m.fns.lookup "ssz_root_bits" = some RootBits.fn
  /-- Lists. -/
  list : m.fns.lookup "ssz_root_list" = some RootList.fn
  /-- Vectors of composite elements. -/
  vector : m.fns.lookup "ssz_root_vector" = some RootVector.fn
  /-- Containers of composite fields. -/
  container : m.fns.lookup "ssz_root_container" = some RootContainer.fn
  /-- Progressive containers. -/
  progressiveContainer : m.fns.lookup "ssz_root_progressive_container" = some RootProgressiveContainer.fn
  /-- Compatible unions. -/
  union : m.fns.lookup "ssz_root_union" = some RootUnion.fn
  /-- The dispatcher on the type. -/
  rootOf : m.fns.lookup "ssz_root_of" = some RootOf.fn
  /-- The root of a whole encoding. -/
  top : m.fns.lookup "ssz_hash_tree_root" = some HashTreeRoot.fn

/-! ### Facts the contract gives -/

/-- A context stays filled when memory changed only outside its buffers: in a region apart from them, or the pad. -/
theorem RootReady.within {w : World} {ctx table zeros pad : Nat} {mask : UInt64} {mem mem' : Memory}
    (r : RootReady w ctx table zeros pad mask mem) {o n : Nat} (oCtx : Apart (o, n) (ctx, 32))
    (oTable : Apart (o, n) (table, Kernel.tableSize)) (oZeros : Apart (o, n) (zeros, 32 * (zeroHeights + 1)))
    (keep : ∀ a, ¬ (o ≤ a ∧ a < o + n) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a) :
    RootReady w ctx table zeros pad mask mem' := by
  refine r.frame fun a held => ?_
  simp only [RootReady.Held] at held
  rcases held with h | h | h
  · exact keep a (outside_of_apart oCtx h.1 h.2) (outside_of_apart' (apart_comm r.padCtx) h.1 h.2)
  · exact keep a (outside_of_apart oTable h.1 h.2) (outside_of_apart' (apart_comm r.padTable) h.1 h.2)
  · exact keep a (outside_of_apart oZeros h.1 h.2) (outside_of_apart' (apart_comm r.padZeros) h.1 h.2)

/-- The context stays filled after a step that changes memory only in the output, the scratch, and the padding area. -/
theorem RangePre.readyAfter {w : World} {mem mem' : Memory} {d : Desc}
    {p base start stop out scratch ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : RangePre w mem d p base start stop out scratch ctx table zeros pad mask b)
    (keep : ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (scratch ≤ a ∧ a < scratch + varNeed d (stop - start)) →
      ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a) :
    RootReady w ctx table zeros pad mask mem' := by
  refine pre.ready.frame fun a held => ?_
  have ctxPad := pre.ready.padCtx
  have tablePad := pre.ready.padTable
  have zerosPad := pre.ready.padZeros
  have oc := pre.oCtx
  have ot := pre.oTable
  have oz := pre.oZeros
  have sc := pre.sCtx
  have st := pre.sTable
  have sz := pre.sZeros
  simp only [Apart] at ctxPad tablePad zerosPad oc ot oz sc st sz
  simp only [RootReady.Held] at held
  exact keep a (by omega) (by omega) (by omega)

/-- The bytes read from where memory holds a buffer have the buffer's nodes. -/
theorem nodesFrom_of_holds {mem : Memory} {a n : Nat} {x : ByteArray} (h : Holds mem a x) (inside : 32 * n ≤ x.size) :
    nodesFrom (bytesAt mem a (32 * n)) 0 n = nodesFrom x 0 n := by
  apply Array.ext
  · simp
  · intro i hi _
    have hi' : i < n := by simpa using hi
    simp only [nodesFrom, Array.getElem_ofFn]
    rw [nodeOf_bytesAt mem a n i hi', nodeAt_of_holds h (by
      have := Nat.mul_le_mul_left 32 (show i + 1 ≤ n by omega); omega)]

/-- A tree over nodes read from where memory holds a buffer is the tree over the buffer's nodes. -/
theorem merkleizeDepth_of_holds {mem : Memory} {a n depth : Nat} {x : ByteArray} (h : Holds mem a x)
    (inside : 32 * n ≤ x.size) (fits : n ≤ 2 ^ depth) (small : x.size < USize.size) :
    (merkleizeDepth (bytesAt mem a (32 * n)) n depth).data = (merkleizeDepth x n depth).data := by
  have size : (bytesAt mem a (32 * n)).size = 32 * n := by simp [bytesAt, ByteArray.size]
  rw [(merkleizeDepth_spec _ n depth fits (by omega) (by omega)).2, (merkleizeDepth_spec x n depth fits inside small).2,
    nodesFrom_of_holds h inside]

/-! ### The length mixed in -/

/-- The eight bytes of a count below the word size are its low base-256 digits. -/
theorem qwordByte_ofNat (n : Nat) (hn : n < 2 ^ 64) (k : Nat) (hk : k < 8) :
    qwordByte (UInt64.ofNat n) k = UInt8.ofNat (n >>> (8 * k)) := by
  apply UInt8.toNat_inj.mp
  rw [qwordByte_toNat _ _ hk, ofNat_toNat hn]
  simp [Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- The bytes of a count's node past the first eight are zero, for a count below the word size. -/
theorem lengthNode_high (n : Nat) (hn : n < 2 ^ 64) (k : Nat) (hk : 8 ≤ k) : UInt8.ofNat (n >>> (8 * k)) = 0 := by
  have : n >>> (8 * k) = 0 := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt]
    exact Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by decide) (by omega))
  rw [this]; rfl

/-- Memory after a count's eight bytes and three zero words reads, at their place, the count's node. -/
theorem nodeAt_lengthStores (mem : Memory) (a n : Nat) (hn : n < 2 ^ 64) :
    nodeAt (store (store (store (store mem a 8 (qwordByte (UInt64.ofNat n))) (a + 8) 8 (qwordByte 0))
      (a + 16) 8 (qwordByte 0)) (a + 24) 8 (qwordByte 0)) a = (lengthNode n).data := by
  apply Array.ext
  · simp [nodeAt, lengthNode]
  · intro i h1 h2
    have hi : i < 32 := by simpa [nodeAt] using h1
    simp only [nodeAt, Array.getElem_ofFn, lengthNode, Array.getElem_map, Array.getElem_range, Asm.store]
    by_cases q3 : a + 24 ≤ a + i ∧ a + i < a + 24 + 8
    · rw [ite_eq_left q3, qwordByte_of_zero, lengthNode_high n hn i (by omega)]
    rw [ite_eq_right q3]
    by_cases q2 : a + 16 ≤ a + i ∧ a + i < a + 16 + 8
    · rw [ite_eq_left q2, qwordByte_of_zero, lengthNode_high n hn i (by omega)]
    rw [ite_eq_right q2]
    by_cases q1 : a + 8 ≤ a + i ∧ a + i < a + 8 + 8
    · rw [ite_eq_left q1, qwordByte_of_zero, lengthNode_high n hn i (by omega)]
    rw [ite_eq_right q1, ite_eq_left (by omega), qwordByte_ofNat n hn _ (by omega)]
    congr 2
    omega

/--
A count's node written after a root, then the two hashed into the output.

The root sits at the scratch, the count's node goes right after it, and the parent lands at the output.
Memory changes only in the count's node, the output, and the padding area.
-/
theorem mixin_ends {m : Module} {w : World} (hash : HashingOk m w) {sp : Nat} (room : w.stackLo + hashStack ≤ sp)
    {env : Env} {mem : Memory} {out scratch ctx table zeros pad : Nat} {mask : UInt64}
    (ready : RootReady w ctx table zeros pad mask mem) (hs : env 4 = UInt64.ofNat scratch)
    (ho : env 3 = UInt64.ofNat out) (hc : env 5 = UInt64.ofNat ctx) {cnt : Expr} {n : Nat}
    (hn : ∀ mm, eval w env mm cnt = some (UInt64.ofNat n)) (nSmall : n < 2 ^ 64) (sAcc : w.access scratch 64 = true)
    (sReach : scratch + 96 ≤ addressBound)
    (oAcc : w.access out 32 = true) (sOut : Apart (scratch, 64) (out, 32)) (sPad : Apart (scratch, 64) (pad, 1536))
    (sCtx : Apart (scratch, 64) (ctx, 32)) (sTable : Apart (scratch, 64) (table, Kernel.tableSize))
    (sZeros : Apart (scratch, 64) (zeros, 32 * (zeroHeights + 1))) (oPad : Apart (out, 32) (pad, 1536))
    (oCtx : Apart (out, 32) (ctx, 32)) (oTable : Apart (out, 32) (table, Kernel.tableSize))
    (oZeros : Apart (out, 32) (zeros, 32 * (zeroHeights + 1))) (sink : Nat) :
    Ends m w sp env mem (.block (lengthNodeAt (Expr.var 4 + 32) cnt ++
        [.call "ssz_hash_pairs" [Expr.var 3, Expr.var 4, Expr.var 4 + 32, 1, Expr.var 5] sink]))
      fun _ mm => nodeAt mm out = combine (nodeAt mem scratch) (lengthNode n).data ∧
        RootReady w ctx table zeros pad mask mm ∧
        ∀ a, ¬ (scratch + 32 ≤ a ∧ a < scratch + 64) → ¬ (out ≤ a ∧ a < out + 32) → ¬ (pad ≤ a ∧ a < pad + 1536) →
          mm a = mem a := by
  have so := sOut
  have sp' := sPad
  have sc := sCtx
  have st := sTable
  have sz := sZeros
  have op := oPad
  have oc := oCtx
  have ot := oTable
  have oz := oZeros
  have pc := ready.padCtx
  have ptab := ready.padTable
  have pz := ready.padZeros
  simp only [Apart] at so sp' sc st sz op oc ot oz pc ptab pz
  have bs := access_bound sAcc
  have bo := access_bound oAcc
  have es : ∀ mm, eval w env mm (Expr.var 4) = some (UInt64.ofNat scratch) := fun _ => eval_var hs
  have ek : ∀ (mm : Memory) (k : Nat), eval w env mm (Expr.var 4 + ((k : Nat) : Expr)) =
      some (UInt64.ofNat (scratch + k)) := fun mm k => eval_add (es mm) (eval_cast k)
  -- The count's eight bytes, then three zero words.
  let a := scratch + 32
  let m1 := store mem a 8 (qwordByte (UInt64.ofNat n))
  let m2 := store m1 (a + 8) 8 (qwordByte 0)
  let m3 := store m2 (a + 16) 8 (qwordByte 0)
  let m4 := store m3 (a + 24) 8 (qwordByte 0)
  have acc : ∀ k, k + 8 ≤ 32 → w.access (UInt64.ofNat (a + k)).toNat 8 = true := fun k hk => by
    rw [ofNat_toNat (by omega)]; exact access_sub sAcc (by omega) (by omega)
  have r1 : Runs m w sp env mem (Stmt.st (Expr.var 4 + 32) cnt) env m1 := by
    have := Runs.store m w sp env mem .b8 _ _ _ _ (ek mem 32) (hn mem) (acc 0 (by omega))
    rw [ofNat_toNat (show scratch + 32 < 2 ^ 64 by omega)] at this
    exact this
  have r2 : Runs m w sp env m1 (Stmt.st (Expr.var 4 + 32 + 8) 0) env m2 := by
    have := Runs.store m w sp env m1 .b8 _ (0 : Expr) _ 0 (eval_add (ek m1 32) (eval_lit 8)) rfl (acc 8 (by omega))
    rw [ofNat_toNat (show scratch + 32 + 8 < 2 ^ 64 by omega)] at this
    exact this
  have r3 : Runs m w sp env m2 (Stmt.st (Expr.var 4 + 32 + 16) 0) env m3 := by
    have := Runs.store m w sp env m2 .b8 _ (0 : Expr) _ 0 (eval_add (ek m2 32) (eval_lit 16)) rfl (acc 16 (by omega))
    rw [ofNat_toNat (show scratch + 32 + 16 < 2 ^ 64 by omega)] at this
    exact this
  have r4 : Runs m w sp env m3 (Stmt.st (Expr.var 4 + 32 + 24) 0) env m4 := by
    have := Runs.store m w sp env m3 .b8 _ (0 : Expr) _ 0 (eval_add (ek m3 32) (eval_lit 24)) rfl (acc 24 (by omega))
    rw [ofNat_toNat (show scratch + 32 + 24 < 2 ^ 64 by omega)] at this
    exact this
  -- The stores change only the count's node.
  have keep4 : ∀ x, ¬ (a ≤ x ∧ x < a + 32) → m4 x = mem x := by
    intro x hx
    simp only [m4, m3, m2, m1, Asm.store]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  have node4 : nodeAt m4 a = (lengthNode n).data := nodeAt_lengthStores mem a n nSmall
  have ready4 := ready.within (o := a) (n := 32) (by simp only [Apart]; omega) (by simp only [Apart]; omega)
    (by simp only [Apart]; omega) fun x o _ => keep4 x o
  -- The root and the count's node hashed into the output.
  have inputs : ∀ p < 1, w.access (scratch + 64 * p) 32 = true ∧ w.access (scratch + 32 + 64 * p) 32 = true :=
    fun p hp => by
      obtain rfl : p = 0 := by omega
      exact ⟨access_sub sAcc (by omega) (by omega), access_sub sAcc (by omega) (by omega)⟩
  have pairs : HashPre w m4 out scratch (scratch + 32) 1 64 64 table :=
    ⟨ready4.tableHeld, by simpa using oAcc, ready4.tableAccess, inputs, ⟨by omega, by omega⟩,
      by simp only [Apart]; omega, fun p hp => by simp only [Apart]; omega⟩
  have run : RunPre w m4 64 64 out scratch (scratch + 32) 1 ctx table pad mask :=
    ⟨ready4.ctxAccess, ready4.maskAt, ready4.tableAt, ready4.padAt, pairs, ready4.padAccess,
      by simp only [Apart]; omega, ready4.padTable, fun p hp => by simp only [Apart]; omega,
      by simp only [Apart]; omega⟩
  obtain ⟨mm, call, hm⟩ := hash_call (name := "ssz_hash_pairs") (env := env) (mm := m4) (dst := sink)
    (args := [Expr.var 3, Expr.var 4, Expr.var 4 + 32, 1, Expr.var 5]) hash.pairs rfl rfl rfl run ready4.kernels room
    (eval_five (eval_var ho) (es m4) (ek m4 32) (eval_lit 1) (eval_var hc))
  refine ⟨_, mm, Runs.block_cons r1 (Runs.block_cons r2 (Runs.block_cons r3 (Runs.block_cons r4
    (Runs.block_cons call (Runs.block_nil _ _ _ _ _))))), ?_, ?_, ?_⟩
  · have e := nodeAt_hashed m4 out scratch (scratch + 32) 1 64 64 0 (by decide)
    simp only [Nat.mul_zero, Nat.add_zero] at e
    rw [nodeAt_congr (m₂ := hashed m4 out scratch (scratch + 32) 1 64 64) fun i hi => hm _ (by omega), e,
      nodeAt_congr (m₂ := mem) (a := scratch) fun i hi => keep4 _ (by omega), node4]
  · refine ready4.within (o := out) (n := 32) (by simp only [Apart]; omega) (by simp only [Apart]; omega)
      (by simp only [Apart]; omega) fun x o pd => ?_
    rw [hm x pd, hashed_outside (by omega)]
  · intro x hx ho' pd
    rw [hm x pd, hashed_outside (by omega), keep4 x hx]


/-! ### Steps the range drivers share -/

/-- The four word stores of zero write a node of zeros at the address an expression names. -/
theorem zero32_at {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {dst : Expr} {a : Nat}
    (hd : ∀ mm, eval w env mm dst = some (UInt64.ofNat a)) (acc : w.access a 32 = true) :
    Runs m w sp env mem (.block (zero32 dst)) env (zeroed mem a) := by
  have bound : a + 32 < 2 ^ 64 := by have := access_end acc; omega
  have st := fun (mm : Memory) (k : Nat) (hk : k + 8 ≤ 32) =>
    Runs.store m w sp env mm .b8 (dst + ((k : Nat) : Expr)) (0 : Expr) (UInt64.ofNat (a + k)) 0
      (eval_add (hd mm) (eval_cast k)) rfl
      (by rw [ofNat_toNat (by omega)]; exact access_sub acc (by omega) (by simp only [Width.bytes]; omega))
  refine Runs.block_cons (st mem 0 (by decide)) (Runs.block_cons (st _ 8 (by decide)) (Runs.block_cons
    (st _ 16 (by decide)) (Runs.block_cons (st _ 24 (by decide)) ?_)))
  have same : ∀ mm : Memory, mm = zeroed mem a → Runs m w sp env mm (.block []) env (zeroed mem a) :=
    fun mm h => h ▸ Runs.block_nil _ _ _ _ _
  apply same
  funext x
  simp only [zeroed, Asm.store, ofNat_toNat (show a + 0 < 2 ^ 64 by omega), ofNat_toNat (show a + 8 < 2 ^ 64 by omega),
    ofNat_toNat (show a + 16 < 2 ^ 64 by omega), ofNat_toNat (show a + 24 < 2 ^ 64 by omega), Width.bytes,
    qwordByte_of_zero]
  by_cases h0 : a ≤ x ∧ x < a + 32
  · rw [ite_eq_left h0]; repeat' split
    all_goals first | rfl | omega
  · rw [ite_eq_right h0, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- A node of zeros reads as the zero node. -/
theorem nodeAt_zeroed (mem : Memory) (a : Nat) : nodeAt (zeroed mem a) a = zeroNode.data := by
  apply Array.ext
  · simp [nodeAt, zeroNode]
  · intro i _ _
    simp [nodeAt, zeroed, Asm.store, zeroNode]

/-- A node of zeros changes memory only in its own bytes. -/
theorem zeroed_outside {mem : Memory} {a x : Nat} (h : ¬ (a ≤ x ∧ x < a + 32)) : zeroed mem a x = mem x := by
  simp only [zeroed, Asm.store]; rw [ite_eq_right h]

/--
One pair of adjacent nodes hashed into an output apart from them.

The context's buffers miss both, and only the output and the padding area change.
-/
theorem pairInto_runs {m : Module} {w : World} (hash : HashingOk m w) {sp : Nat} (room : w.stackLo + hashStack ≤ sp)
    {env : Env} {mem : Memory} {args : List Expr} {dst : Nat} {out left ctx table zeros pad : Nat} {mask : UInt64}
    (ready : RootReady w ctx table zeros pad mask mem) (lAcc : w.access left 64 = true)
    (lReach : left + 96 ≤ addressBound) (oAcc : w.access out 32 = true) (lOut : Apart (left, 64) (out, 32))
    (lPad : Apart (left, 64) (pad, 1536)) (oPad : Apart (out, 32) (pad, 1536)) (oCtx : Apart (out, 32) (ctx, 32))
    (oTable : Apart (out, 32) (table, Kernel.tableSize))
    (hv : args.mapM (eval w env mem) = some [UInt64.ofNat out, UInt64.ofNat left, UInt64.ofNat (left + 32), 1,
      UInt64.ofNat ctx]) :
    ∃ mm, Runs m w sp env mem (.call "ssz_hash_pairs" args dst) (Asm.assign env dst 0) mm ∧
      nodeAt mm out = combine (nodeAt mem left) (nodeAt mem (left + 32)) ∧
      ∀ x, ¬ (out ≤ x ∧ x < out + 32) → ¬ (pad ≤ x ∧ x < pad + 1536) → mm x = mem x := by
  have lo := lOut
  have lp := lPad
  have op := oPad
  have oc := oCtx
  have ot := oTable
  simp only [Apart] at lo lp op oc ot
  have bl := access_bound lAcc
  have inputs : ∀ p < 1, w.access (left + 64 * p) 32 = true ∧ w.access (left + 32 + 64 * p) 32 = true :=
    fun p hp => by
      obtain rfl : p = 0 := by omega
      exact ⟨access_sub lAcc (by omega) (by omega), access_sub lAcc (by omega) (by omega)⟩
  have pairs : HashPre w mem out left (left + 32) 1 64 64 table :=
    ⟨ready.tableHeld, by simpa using oAcc, ready.tableAccess, inputs, ⟨by omega, by omega⟩,
      by simp only [Apart]; omega, fun p hp => by simp only [Apart]; omega⟩
  have run : RunPre w mem 64 64 out left (left + 32) 1 ctx table pad mask :=
    ⟨ready.ctxAccess, ready.maskAt, ready.tableAt, ready.padAt, pairs, ready.padAccess,
      by simp only [Apart]; omega, ready.padTable, fun p hp => by simp only [Apart]; omega,
      by simp only [Apart]; omega⟩
  obtain ⟨mm, call, hm⟩ := hash_call (name := "ssz_hash_pairs") (env := env) (mm := mem) (dst := dst)
    (args := args) hash.pairs rfl rfl rfl run ready.kernels room hv
  refine ⟨mm, call, ?_, fun x o pd => by rw [hm x pd, hashed_outside (by omega)]⟩
  have e := nodeAt_hashed mem out left (left + 32) 1 64 64 0 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero] at e
  rw [nodeAt_congr (m₂ := hashed mem out left (left + 32) 1 64 64) fun i hi => hm _ (by omega), e]

/-- A tree over nodes read from inside a buffer memory holds is the tree over those nodes of the buffer. -/
theorem merkleizeAt_of_holds {mem : Memory} {a s n depth : Nat} {x : ByteArray} (h : Holds mem a x)
    (inside : 32 * (s + n) ≤ x.size) (fits : n ≤ 2 ^ depth) (small : x.size < USize.size) :
    (merkleizeDepth (bytesAt mem (a + 32 * s) (32 * n)) n depth).data = (merkleizeAt x (32 * s) n depth).data := by
  have size : (bytesAt mem (a + 32 * s) (32 * n)).size = 32 * n := by simp [bytesAt, ByteArray.size]
  rw [(merkleizeDepth_spec _ n depth fits (by omega) (by omega)).2,
    (merkleizeAt_spec x (32 * s) n depth fits (by omega) small).2]
  congr 1
  apply Array.ext
  · simp
  · intro i hi _
    have hi' : i < n := by simpa using hi
    simp only [nodesFrom, Array.getElem_ofFn]
    rw [nodeOf_bytesAt mem _ n i hi', Nat.add_assoc, ← Nat.mul_add, nodeAt_of_holds h (by
      have := Nat.mul_le_mul_left 32 (show s + i + 1 ≤ s + n by omega); omega),
      show 32 * s = 0 + 32 * s by omega, nodeOf_shift]

end EthLib.Consensus.Ssz.Native.Driver
