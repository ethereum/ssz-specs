import SszNative.Proofs.Driver.Root.Bytes

/-!
The packed roots driver computes the Lean packed roots.

It gathers each value's bytes into a zero-padded block of nodes, then hashes the blocks level by level.
Each level lands right after the one before it, and the last one lands in the output.
The proof follows the Lean computation's levels one at a time, as buffers held in memory.
-/

namespace Ssz.Native.Driver

open Ssz.Native.Ir Ssz.Native.Ir.Expr Ssz.Native.Ir.Stmt Ssz.Native.Asm

/-! ### A filled context -/

/--
A filled root context: its words, the table, zero roots and padding area they name, and a mask with a hashing kernel.

Every root driver takes one.
-/
structure RootReady (w : World) (ctx table zeros pad : Nat) (mask : UInt64) (mem : Memory) : Prop where
  /-- The context's words are usable. -/
  ctxAccess : w.access ctx 32 = true
  /-- The first word is the mask. -/
  maskAt : readLE mem ctx 8 = mask
  /-- The second word is the table's address. -/
  tableAt : readLE mem (ctx + 8) 8 = UInt64.ofNat table
  /-- The third word is the zero roots' address. -/
  zerosAt : readLE mem (ctx + 16) 8 = UInt64.ofNat zeros
  /-- The fourth word is the padding area's address. -/
  padAt : readLE mem (ctx + 24) 8 = UInt64.ofNat pad
  /-- The table is in memory. -/
  tableHeld : Kernel.TableAt mem table
  /-- The table is usable. -/
  tableAccess : w.access table Kernel.tableSize = true
  /-- The zero roots are in memory. -/
  zeroRoots : ∀ i < 32 * (zeroHeights + 1), mem (zeros + i) = zeroRootsTable.get! i
  /-- The zero roots are usable. -/
  zerosAccess : w.access zeros (32 * (zeroHeights + 1)) = true
  /-- The padding area is usable. -/
  padAccess : w.access pad 1536 = true
  /-- The padding area misses the table. -/
  padTable : Apart (pad, 1536) (table, Kernel.tableSize)
  /-- The padding area misses the context. -/
  padCtx : Apart (pad, 1536) (ctx, 32)
  /-- The padding area misses the zero roots. -/
  padZeros : Apart (pad, 1536) (zeros, 32 * (zeroHeights + 1))
  /-- The processor runs every hashing kernel the mask chooses. -/
  kernels : KernelsRun w mask
  /-- The processor runs every gathering kernel the mask chooses. -/
  gathers : GatherKernelsRun w mask

/-- Bytes of the context, the table, or the zero roots. -/
def RootReady.Held (ctx table zeros : Nat) (a : Nat) : Prop :=
  (ctx ≤ a ∧ a < ctx + 32) ∨ (table ≤ a ∧ a < table + Kernel.tableSize) ∨
    (zeros ≤ a ∧ a < zeros + 32 * (zeroHeights + 1))

/-- A context stays filled when its words, the table, and the zero roots stay. -/
theorem RootReady.frame {w : World} {ctx table zeros pad : Nat} {mask : UInt64} {mem mem' : Memory}
    (r : RootReady w ctx table zeros pad mask mem) (h : ∀ a, RootReady.Held ctx table zeros a → mem' a = mem a) :
    RootReady w ctx table zeros pad mask mem' := by
  have inCtx : ∀ k < 32, mem' (ctx + k) = mem (ctx + k) := fun k hk => h _ (.inl ⟨by omega, by omega⟩)
  have word : ∀ j, j + 8 ≤ 32 → readLE mem' (ctx + j) 8 = readLE mem (ctx + j) 8 :=
    fun j hj => readLE_congr mem' mem (ctx + j) 8 fun k hk => by rw [Nat.add_assoc]; exact inCtx _ (by omega)
  refine { r with maskAt := ?_, tableAt := ?_, zerosAt := ?_, padAt := ?_, tableHeld := ?_, zeroRoots := ?_ }
  · rw [← r.maskAt]; simpa using word 0 (by decide)
  · rw [word 8 (by decide), r.tableAt]
  · rw [word 16 (by decide), r.zerosAt]
  · rw [word 24 (by decide), r.padAt]
  · intro i hi
    rw [h _ (.inr (.inl ⟨by omega, by omega⟩))]
    exact r.tableHeld i hi
  · intro i hi
    rw [h _ (.inr (.inr ⟨by omega, by omega⟩))]
    exact r.zeroRoots i hi

/-- A run of pairs, its digests and inputs inside a region apart from the context's buffers, meets the hashing
conditions. -/
theorem RootReady.runPre {w : World} {ctx table zeros pad : Nat} {mask : UInt64} {mem : Memory}
    (r : RootReady w ctx table zeros pad mask mem) {ls rs out left right count lo span : Nat}
    (acc : w.access lo span = true) (regionPad : Apart (lo, span) (pad, 1536))
    (regionCtx : Apart (lo, span) (ctx, 32)) (regionTable : Apart (lo, span) (table, Kernel.tableSize))
    (outIn : lo ≤ out ∧ out + 32 * count ≤ lo + span)
    (inputsIn : ∀ p < count, lo ≤ left + ls * p ∧ left + ls * p + 32 ≤ lo + span ∧ lo ≤ right + rs * p ∧
      right + rs * p + 32 ≤ lo + span)
    (reach : left + ls * count ≤ addressBound ∧ right + rs * count ≤ addressBound)
    (inputsApart : ∀ p < count, Apart (out, 32 * count) (left + ls * p, 32) ∧
      Apart (out, 32 * count) (right + rs * p, 32)) :
    RunPre w mem ls rs out left right count ctx table pad mask := by
  have rp := regionPad
  have rc := regionCtx
  have rt := regionTable
  simp only [Apart] at rp rc rt
  refine ⟨access_sub r.ctxAccess (Nat.le_refl _) (by omega), r.maskAt, r.tableAt, r.padAt,
    ⟨r.tableHeld, access_sub acc outIn.1 (by omega), r.tableAccess,
      fun p hp => ⟨access_sub acc (inputsIn p hp).1 (inputsIn p hp).2.1,
        access_sub acc (inputsIn p hp).2.2.1 (inputsIn p hp).2.2.2⟩, reach, by simp only [Apart]; omega,
      inputsApart⟩,
    r.padAccess, by simp only [Apart]; omega, r.padTable,
    fun p hp => by have := inputsIn p hp; simp only [Apart]; omega, by simp only [Apart]; omega⟩

/-- The zero tree's root of each height the table holds is in memory, at its place in the table. -/
theorem RootReady.zeroRoot_holds {w : World} {ctx table zeros pad : Nat} {mask : UInt64} {mem : Memory}
    (r : RootReady w ctx table zeros pad mask mem) {h : Nat} (hh : h ≤ zeroHeights) :
    Holds mem (zeros + 32 * h) (zeroRoot h) := by
  intro i hi
  rw [zeroRoot_size] at hi
  obtain ⟨size, nodes⟩ := zeroRootsTable_spec
  have node := nodes h hh
  rw [← zeroRoot_data] at node
  have inside : 32 * h + i < 32 * (zeroHeights + 1) := by omega
  rw [Nat.add_assoc, r.zeroRoots _ inside, Kernel.get!_eq _ _ (by omega), Kernel.get!_eq _ _ (by simp; omega),
    ByteArray.getElem_eq_getElem_data, ByteArray.getElem_eq_getElem_data]
  simp only [nodeOf, Nat.zero_add] at node
  simp only [← node, ByteArray.data_extract, Array.getElem_extract]

/-! ### Stores into the padding area -/

/-- A store elsewhere leaves eight bytes as they were. -/
theorem readLE_store_apart (mem : Memory) (a b n : Nat) (f : Nat → UInt8) (h : a + 8 ≤ b ∨ b + n ≤ a) :
    readLE (store mem b n f) a 8 = readLE mem a 8 :=
  readLE_congr _ _ a 8 fun k hk => by simp only [Asm.store]; rw [if_neg (by omega)]

/-- A store leaves every byte outside it as it was. -/
theorem store_outside {mem : Memory} {b n : Nat} {f : Nat → UInt8} {a : Nat} (h : ¬ (b ≤ a ∧ a < b + n)) :
    store mem b n f a = mem a := by
  simp only [Asm.store]; rw [if_neg h]

/-! ### The blocks' size -/

/-- The variables the packed roots driver keeps from its start: the arguments, the depth, the block size, and where the
blocks go. -/
structure PackedEnv (env : Env) (width src stride count out ctx depth g : Nat) : Prop where
  /-- The width. -/
  width : env 0 = UInt64.ofNat width
  /-- The first value's address. -/
  src : env 1 = UInt64.ofNat src
  /-- The stride. -/
  stride : env 2 = UInt64.ofNat stride
  /-- The count. -/
  count : env 3 = UInt64.ofNat count
  /-- The output. -/
  out : env 4 = UInt64.ofNat out
  /-- The context. -/
  ctx : env 5 = UInt64.ofNat ctx
  /-- The depth of one value's tree. -/
  levels : env 6 = UInt64.ofNat depth
  /-- The bytes of one value's block. -/
  slot : env 7 = UInt64.ofNat (32 * 2 ^ depth)
  /-- Where the blocks go. -/
  g : env 8 = UInt64.ofNat g

/-- Writing a variable past the kept ones keeps them. -/
theorem PackedEnv.write {env : Env} {width src stride count out ctx depth g : Nat}
    (h : PackedEnv env width src stride count out ctx depth g) {x : Nat} (v : UInt64) (hx : 9 ≤ x) :
    PackedEnv (Asm.assign env x v) width src stride count out ctx depth g := by
  have ne : ∀ y, y < 9 → Asm.assign env x v y = env y := fun y hy => assign_ne (by omega)
  exact ⟨by rw [ne 0 (by decide), h.width], by rw [ne 1 (by decide), h.src], by rw [ne 2 (by decide), h.stride],
    by rw [ne 3 (by decide), h.count], by rw [ne 4 (by decide), h.out], by rw [ne 5 (by decide), h.ctx],
    by rw [ne 6 (by decide), h.levels], by rw [ne 7 (by decide), h.slot], by rw [ne 8 (by decide), h.g]⟩

/-- The doubling loop of the packed roots, from a block size reached so far, ends at the block of the depth. -/
theorem slotDoubling_runs {m : Module} {w : World} {sp : Nat} {mem : Memory} (D : Nat) (hD : D ≤ 57) :
    ∀ k j (env : Env), j + k = D → env 6 = D.toUInt64 → env 7 = (32 * 2 ^ j).toUInt64 → env 15 = j.toUInt64 →
    ∃ env', Runs m w sp env mem (while_ (lt RootPacked.i RootPacked.depth)
        [RootPacked.slot ::= RootPacked.slot + RootPacked.slot, RootPacked.i ::= RootPacked.i + 1]) env' mem ∧
      env' 7 = (32 * 2 ^ D).toUInt64 ∧ ∀ v, v ≠ 7 → v ≠ 15 → env' v = env v := by
  intro k
  induction k with
  | zero =>
    intro j env hj h6 h7 h15
    simp only [Nat.add_zero] at hj
    subst hj
    refine ⟨env, Runs.loop_exit _ _ _ _ _ _ _ ?_, h7, fun _ _ _ => rfl⟩
    simp [eval, Cond.holds, h6, h15]
  | succ k ih =>
    intro j env hj h6 h7 h15
    have pj : 32 * 2 ^ j + 32 * 2 ^ j = 32 * 2 ^ (j + 1) := by rw [Nat.pow_succ]; omega
    obtain ⟨env', run, e7, frame⟩ := ih (j + 1)
      (Asm.assign (Asm.assign env 7 (32 * 2 ^ (j + 1)).toUInt64) 15 (j + 1).toUInt64) (by omega)
      (by simp [Asm.assign, h6]) (by simp [Asm.assign]) (by simp [Asm.assign])
    refine ⟨env', Runs.loop_step 1 ?_ (by decide)
      (Runs.block_cons (Runs.set' (by simp [eval, h7, ← pj]))
        (Runs.set' (by simp [eval, Asm.assign, h15]))) run, e7, fun v a b => ?_⟩
    · have lt : j.toUInt64 < D.toUInt64 := (toUInt64_lt (by omega) (by omega)).mpr (by omega)
      simp [eval, Cond.holds, h6, h15, lt]
    · rw [frame v a b]; simp [Asm.assign, a, b]

/-- The statements of the packed roots driver before its gather. -/
abbrev packedStart : List Stmt :=
  [callInto RootPacked.depth "ssz_depth_for" [ceilDiv RootPacked.width 32],
    RootPacked.slot ::= 32, RootPacked.i ::= 0,
    while_ (lt RootPacked.i RootPacked.depth) [RootPacked.slot ::= RootPacked.slot + RootPacked.slot,
      RootPacked.i ::= RootPacked.i + 1],
    ifElse (eq RootPacked.depth 0) [RootPacked.g ::= RootPacked.out]
      [RootPacked.g ::= RootPacked.out + 32 * RootPacked.count]]

/--
The packed roots driver's start computes the depth of one value's tree and its block size, and places the blocks:
at the output for values of one node, and after the roots otherwise.
-/
theorem packedStart_runs {m : Module} {w : World} (hd : m.fns.lookup "ssz_depth_for" = some DepthFor.fn) {sp : Nat}
    (room : w.stackLo + 48 ≤ sp) (mem : Memory) {width src stride count out ctx : Nat} (hw : width ≤ scratchCap) :
    ∃ env, Runs m w sp (entryEnv [UInt64.ofNat width, UInt64.ofNat src, UInt64.ofNat stride, UInt64.ofNat count,
        UInt64.ofNat out, UInt64.ofNat ctx]) mem (.block packedStart) env mem ∧
      PackedEnv env width src stride count out ctx (depthFor (nodesFor width))
        (if depthFor (nodesFor width) = 0 then out else out + 32 * count) := by
  have capv : scratchCap = 2 ^ 62 := rfl
  have dframe : DepthFor.fn.frame = 5 := by decide
  let E0 := entryEnv [UInt64.ofNat width, UInt64.ofNat src, UInt64.ofNat stride, UInt64.ofNat count,
    UInt64.ofNat out, UInt64.ofNat ctx]
  have nodes : ((UInt64.ofNat width).toNat + 32 - 1) / 32 = nodesFor width := by
    rw [ofNat_toNat (by omega)]; rfl
  have nodesSmall : nodesFor width < 2 ^ 64 := by simp only [nodesFor]; omega
  have depth := depthFor_calls (w := w) hd (sp := sp) (by rw [dframe]; omega) (nodesFor width).toUInt64 mem
  rw [addr_toNat nodesSmall] at depth
  have dsmall := depth_small hw
  generalize depthFor (nodesFor width) = D at depth dsmall ⊢
  -- The depth.
  have s1 := Runs.call (m := m) (sp := sp) (env := E0) (dst := 6)
    (args := [ceilDiv RootPacked.width 32]) (values := [(nodesFor width).toUInt64])
    (by simp only [List.mapM_cons, List.mapM_nil]
        rw [eval_ceilDiv (x := UInt64.ofNat width) (by simp [eval, E0, entryEnv]) 32 (by simp), nodes]; rfl) depth
  -- The block size, doubled once per level.
  let E3 := Asm.assign (Asm.assign (Asm.assign E0 6 D.toUInt64) 7 32) 15 0
  obtain ⟨E4, loop, e7, keep⟩ := slotDoubling_runs (m := m) (w := w) (sp := sp) (mem := mem) D dsmall D 0 E3
    (by omega) (by simp [E3, Asm.assign]) (by simp [E3, Asm.assign]) (by simp [E3, Asm.assign])
  have k : ∀ v, v < 7 → E4 v = Asm.assign E0 6 D.toUInt64 v := fun v hv => by
    rw [keep v (by omega) (by omega)]; simp only [E3, Asm.assign]; rw [if_neg (by omega), if_neg (by omega)]
  have e6 : E4 6 = UInt64.ofNat D := by rw [k 6 (by decide)]; simp [Asm.assign]
  have arg : ∀ v, v < 6 → E4 v = E0 v := fun v hv => by rw [k v (by omega)]; simp only [Asm.assign]; rw [if_neg (by omega)]
  have eo : E4 4 = UInt64.ofNat out := by rw [arg 4 (by decide)]; rfl
  have ec : E4 3 = UInt64.ofNat count := by rw [arg 3 (by decide)]; rfl
  have pre : Runs m w sp E0 mem (.block (packedStart.take 4)) E4 mem :=
    Runs.block_cons s1 (Runs.block_cons (Runs.set' rfl) (Runs.block_cons (Runs.set' rfl) loop))
  have env5 : ∀ G, PackedEnv (Asm.assign E4 8 (UInt64.ofNat G)) width src stride count out ctx D G := fun G =>
    ⟨by rw [assign_ne (by decide), arg 0 (by decide)]; rfl, by rw [assign_ne (by decide), arg 1 (by decide)]; rfl,
      by rw [assign_ne (by decide), arg 2 (by decide)]; rfl, by rw [assign_ne (by decide), ec],
      by rw [assign_ne (by decide), eo], by rw [assign_ne (by decide), arg 5 (by decide)]; rfl,
      by rw [assign_ne (by decide), e6], by rw [assign_ne (by decide), e7], assign_eq⟩
  by_cases zero : D = 0
  · -- Values of one node gather straight into the output.
    subst zero
    have tail : Runs m w sp E4 mem (.block (packedStart.drop 4)) (Asm.assign E4 8 (UInt64.ofNat out)) mem :=
      Runs.block_cons (Runs.ifElse_true 1 (by simp [eval, Cond.holds, e6]) (by decide)
        (Runs.set' (by simp [eval, eo]))) (Runs.block_nil _ _ _ _ _)
    exact ⟨_, Runs.block_append pre tail, by simpa using env5 out⟩
  · -- Blocks of several nodes go after the roots.
    have nz : UInt64.ofNat D ≠ 0 := fun h => zero ((ofNat_inj (by omega) (by decide)).mp h)
    have tail : Runs m w sp E4 mem (.block (packedStart.drop 4))
        (Asm.assign E4 8 (UInt64.ofNat (out + 32 * count))) mem :=
      Runs.block_cons (Runs.ifElse_false (by simp [eval, Cond.holds, e6, nz])
        (Runs.set' (eval_add (eval_var eo) (eval_mul (eval_lit 32) (eval_var ec))))) (Runs.block_nil _ _ _ _ _)
    exact ⟨_, Runs.block_append pre tail, by rw [if_neg zero]; exact env5 _⟩

/-! ### The gather -/

/--
The packed roots driver's gather writes its shape words into the padding area, then gathers each value into its
block, read from memory as the Lean gather of the buffer the values lie in.

Memory changes only in the shape words and the blocks.
-/
theorem packedGather_runs {m : Module} {w : World} (gather : GatherCalls m w) {sp : Nat}
    (room : w.stackLo + gatherStack ≤ sp) {env : Env} {mem : Memory}
    {width src stride count out ctx depth g table zeros pad : Nat} {mask : UInt64}
    (he : PackedEnv env width src stride count out ctx depth g) (rd : RootReady w ctx table zeros pad mask mem)
    {base start : Nat} {b : ByteArray} (holds : Holds mem base b) (hsrc : src = base + start)
    (gap : width ≤ stride) (strideSmall : stride < 2 ^ 63) (fits : width ≤ 32 * 2 ^ depth) (hD : depth ≤ 57)
    (pre : GatherPre w g src count width (stride - width) (32 * 2 ^ depth - width))
    (inside : ∀ i < count, start + stride * i + width ≤ b.size) (bPad : Apart (base, b.size) (pad, 24))
    (usize : USize.size = 2 ^ 64) :
    ∃ env' mem', Runs m w sp env mem (.block RootPacked.gatherCall) env' mem' ∧
      PackedEnv env' width src stride count out ctx depth g ∧
      Holds mem' g (gatherReference b start.toUSize stride.toUSize width.toUSize count.toUSize
        (32 * 2 ^ depth).toUSize) ∧
      ∀ a, ¬ (pad ≤ a ∧ a < pad + 24) → ¬ (g ≤ a ∧ a < g + (32 * 2 ^ depth) * count) → mem' a = mem a := by
  have padEnd := access_end rd.padAccess
  have ctxEnd := access_end rd.ctxAccess
  have bp := bPad
  simp only [Apart] at bp
  -- Every address and size the gather names stays inside the program's memory.
  have slotPos : 32 ≤ 32 * 2 ^ depth := by have := Nat.one_le_two_pow (n := depth); omega
  have slotSmall : 32 * 2 ^ depth ≤ 2 ^ 62 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hD; omega
  have outEnd := access_end pre.outAccess
  have reach := pre.reach
  simp only [addressBound] at reach
  have strideEq : width + (stride - width) = stride := by omega
  rw [strideEq] at reach
  have countSmall : count < 2 ^ 63 := by
    have := Nat.mul_le_mul_right count slotPos
    rw [show width + (32 * 2 ^ depth - width) = 32 * 2 ^ depth by omega] at outEnd; omega
  have padSmall : pad < 2 ^ 64 := by omega
  -- The shape words' address, from the context.
  have l9 : eval w env mem (ld (RootPacked.ctx + 24)) = some (UInt64.ofNat pad) := by
    rw [← rd.padAt]
    exact eval_ld (eval_add (eval_var he.ctx) (eval_lit 24)) (access_sub rd.ctxAccess (by omega) (by omega))
  let E1 := Asm.assign env 9 (UInt64.ofNat pad)
  have e9 : E1 9 = UInt64.ofNat pad := assign_eq
  have he1 := he.write (UInt64.ofNat pad) (Nat.le_refl 9)
  have acc : ∀ k, k + 8 ≤ 24 → w.access (UInt64.ofNat (pad + k)).toNat Width.b8.bytes = true := fun k hk => by
    rw [ofNat_toNat (by omega)]; exact access_sub rd.padAccess (by omega) (by simp [Width.bytes]; omega)
  -- The three shape words: the width, the skip, and the pad.
  let M1 := store mem pad 8 (qwordByte (UInt64.ofNat width))
  let M2 := store M1 (pad + 8) 8 (qwordByte (UInt64.ofNat (stride - width)))
  let M3 := store M2 (pad + 16) 8 (qwordByte (UInt64.ofNat (32 * 2 ^ depth - width)))
  have st1 := Runs.store m w sp E1 mem .b8 RootPacked.shape RootPacked.width (UInt64.ofNat pad) (UInt64.ofNat width) (eval_var e9) (eval_var he1.width)
      (by simpa using acc 0 (by decide))
  have st2 := Runs.store m w sp E1 M1 .b8 (RootPacked.shape + 8) (RootPacked.stride - RootPacked.width) (UInt64.ofNat (pad + 8)) (UInt64.ofNat (stride - width))
      (eval_add (eval_var e9) (eval_lit 8)) (eval_sub (eval_var he1.stride) (eval_var he1.width) gap) (acc 8 (by decide))
  have st3 := Runs.store m w sp E1 M2 .b8 (RootPacked.shape + 16) (RootPacked.slot - RootPacked.width) (UInt64.ofNat (pad + 16)) (UInt64.ofNat (32 * 2 ^ depth - width))
      (eval_add (eval_var e9) (eval_lit 16)) (eval_sub (eval_var he1.slot) (eval_var he1.width) fits)
      (acc 16 (by decide))
  simp only [ofNat_toNat (show pad < 2 ^ 64 by omega), ofNat_toNat (show pad + 8 < 2 ^ 64 by omega),
    ofNat_toNat (show pad + 16 < 2 ^ 64 by omega), Width.bytes] at st1 st2 st3
  -- Memory after the stores differs from before only in the shape words.
  have m3 : ∀ a, ¬ (pad ≤ a ∧ a < pad + 24) → M3 a = mem a := fun a h => by
    simp only [M3, M2, M1]
    rw [store_outside (by omega), store_outside (by omega), store_outside (by omega)]
  have r0 : readLE M3 pad 8 = UInt64.ofNat width := by
    simp only [M3, M2]
    rw [readLE_store_apart _ _ _ _ _ (by omega), readLE_store_apart _ _ _ _ _ (by omega), readLE_store8]
  have r8 : readLE M3 (pad + 8) 8 = UInt64.ofNat (stride - width) := by
    simp only [M3]
    rw [readLE_store_apart _ _ _ _ _ (by omega), readLE_store8]
  have r16 : readLE M3 (pad + 16) 8 = UInt64.ofNat (32 * 2 ^ depth - width) := readLE_store8 _ _ _
  have rmask : readLE M3 ctx 8 = mask := by
    have pc := rd.padCtx
    simp only [Apart] at pc
    rw [← rd.maskAt]
    exact readLE_congr _ _ _ _ fun k hk => m3 _ (by omega)
  -- The gather, with every argument a word below two to the 64.
  have sizes : g < 2 ^ 64 ∧ src < 2 ^ 64 ∧ count < 2 ^ 64 ∧ width < 2 ^ 64 ∧ stride - width < 2 ^ 64 ∧
      32 * 2 ^ depth - width < 2 ^ 64 := ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨r, call⟩ := gather sp M3 (UInt64.ofNat g) (UInt64.ofNat src) (UInt64.ofNat count) (UInt64.ofNat width)
    (UInt64.ofNat (stride - width)) (UInt64.ofNat (32 * 2 ^ depth - width)) pad ctx mask
    (by rw [ofNat_toNat sizes.1, ofNat_toNat sizes.2.1, ofNat_toNat sizes.2.2.1, ofNat_toNat sizes.2.2.2.1,
      ofNat_toNat sizes.2.2.2.2.1, ofNat_toNat sizes.2.2.2.2.2]; exact pre)
    (access_sub rd.padAccess (by omega) (by omega)) r0 r8 r16 (access_sub rd.ctxAccess (by omega) (by omega)) rmask
    rd.gathers room
  rw [ofNat_toNat sizes.1, ofNat_toNat sizes.2.1, ofNat_toNat sizes.2.2.1, ofNat_toNat sizes.2.2.2.1,
    ofNat_toNat sizes.2.2.2.2.1, ofNat_toNat sizes.2.2.2.2.2] at call
  have callRuns := Runs.call (m := m) (sp := sp) (env := E1) (mem := M3) (dst := 10)
    (args := [RootPacked.g, RootPacked.src, RootPacked.count, RootPacked.shape, RootPacked.ctx])
    (eval_five (eval_var he1.g) (eval_var he1.src) (eval_var he1.count) (eval_var e9) (eval_var he1.ctx)) call
  -- The gathered blocks are the Lean gather of the buffer, which the stores left alone.
  have holds3 : Holds M3 base b := holds.congr fun i hi => m3 _ (by omega)
  have slotEq : width + (32 * 2 ^ depth - width) = 32 * 2 ^ depth := by omega
  refine ⟨_, _, Runs.block_cons (Runs.set' l9) (Runs.block_cons st1 (Runs.block_cons st2 (Runs.block_cons st3
    (Runs.block_cons callRuns (Runs.block_nil _ _ _ _ _))))), he1.write r (by decide), ?_, fun a hp hg => ?_⟩
  · rw [hsrc]
    exact holds_gathered holds3 g start stride width count (32 * 2 ^ depth) fits gap inside (by omega) (by omega)
      (by omega) (by omega) (by omega)
  · simp only [gathered]
    rw [slotEq, if_neg hg, m3 a hp]

/-! ### The levels -/

/-- The blocks after hashing a number of levels, as the Lean packed roots computes them. -/
def packedLevel (slots : ByteArray) (h : Nat) : ByteArray :=
  (List.range h).foldl (fun level _ => hashPairs level 0 (level.size / 64).toUSize) slots

/-- No levels hashed leave the blocks. -/
@[simp] theorem packedLevel_zero (slots : ByteArray) : packedLevel slots 0 = slots := rfl

/-- One more level hashes the adjacent pairs of the level before. -/
theorem packedLevel_succ (slots : ByteArray) (h : Nat) :
    packedLevel slots (h + 1) = hashPairs (packedLevel slots h) 0 ((packedLevel slots h).size / 64).toUSize := by
  simp only [packedLevel, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Whether one converted number equals another, as one or zero. -/
theorem eval_eq_nat {w : World} {env : Env} {mem : Memory} {a b : Expr} {p q : Nat}
    (ha : eval w env mem a = some (UInt64.ofNat p)) (hb : eval w env mem b = some (UInt64.ofNat q)) (bp : p < 2 ^ 64)
    (bq : q < 2 ^ 64) : eval w env mem (Expr.eq a b) = some (if p = q then 1 else 0) := by
  show eval w env mem (.cmp .e a b) = _
  simp only [eval, ha, hb, Option.bind_eq_bind, Option.bind, Cond.holds]
  by_cases h : p = q
  · simp [h]
  · simp [h, mt (ofNat_inj bp bq).mp h]

/-- The hashing loop of the packed roots driver. -/
abbrev packedLoop : Stmt :=
  while_ (lt RootPacked.h RootPacked.depth) [
    ifElse (eq (RootPacked.h + 1) RootPacked.depth) [RootPacked.dst ::= RootPacked.out]
      [RootPacked.dst ::= RootPacked.lvl + RootPacked.size],
    callInto RootPacked.sink "ssz_hash_pairs" [RootPacked.dst, RootPacked.lvl, RootPacked.lvl + 32,
      RootPacked.size / 64, RootPacked.ctx],
    RootPacked.lvl ::= RootPacked.dst, RootPacked.size ::= RootPacked.size / 2, RootPacked.h ::= RootPacked.h + 1]

/-- The bytes of the level at a height: a count of blocks, each of two to the remaining levels nodes. -/
abbrev levelSize (count depth h : Nat) : Nat := count * (32 * 2 ^ (depth - h))

/-- Where the level at a height lies: in the output at the top, and after the levels below it otherwise. -/
def levelAt (out g count depth h : Nat) : Nat :=
  if h = depth then out else g + 2 * (levelSize count depth 0 - levelSize count depth h)

/-- Below the top, a level is twice the next, and no larger than the first. -/
theorem levelSize_step {count depth h : Nat} (hh : h < depth) :
    levelSize count depth h = 64 * (count * 2 ^ (depth - (h + 1))) ∧
      levelSize count depth (h + 1) = 32 * (count * 2 ^ (depth - (h + 1))) ∧
      levelSize count depth h ≤ levelSize count depth 0 := by
  have e : 2 ^ (depth - h) = 2 * 2 ^ (depth - (h + 1)) := by
    rw [show depth - h = depth - (h + 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  have le : 2 ^ (depth - h) ≤ 2 ^ (depth - 0) := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨?_, ?_, Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ le)⟩
  · simp only [levelSize]; rw [e, show 32 * (2 * 2 ^ (depth - (h + 1))) = 64 * 2 ^ (depth - (h + 1)) by omega,
      Nat.mul_left_comm]
  · simp only [levelSize]; rw [Nat.mul_left_comm]

/-- The top level is one node per value. -/
theorem levelSize_top (count depth : Nat) : levelSize count depth depth = 32 * count := by
  simp [levelSize, Nat.mul_comm]

section Levels
variable {m : Module} {w : World} {sp : Nat} {width src stride count out ctx depth g table zeros pad : Nat}
  {mask : UInt64} {mem0 : Memory} {slots : ByteArray}

/-- The state of the hashing loop of the packed roots driver at a height. -/
structure PackedAt (w : World) (width src stride count out ctx depth g table zeros pad : Nat) (mask : UInt64)
    (mem0 : Memory) (slots : ByteArray) (env : Env) (mem : Memory) (h : Nat) : Prop where
  /-- The kept variables. -/
  vars : PackedEnv env width src stride count out ctx depth g
  /-- The current level's address. -/
  lvl : env 11 = UInt64.ofNat (levelAt out g count depth h)
  /-- The current level's size. -/
  size : env 12 = UInt64.ofNat (levelSize count depth h)
  /-- The current height. -/
  height : env 13 = UInt64.ofNat h
  /-- No level past the top. -/
  le : h ≤ depth
  /-- The current level is in memory. -/
  holds : Holds mem (levelAt out g count depth h) (packedLevel slots h)
  /-- It has the level's size. -/
  len : (packedLevel slots h).size = levelSize count depth h
  /-- The context stays filled. -/
  ready : RootReady w ctx table zeros pad mask mem
  /-- Memory changes only in the output, the blocks and levels after it, and the padding area. -/
  frame : ∀ a, ¬ (out ≤ a ∧ a < out + (32 * count + 2 * levelSize count depth 0)) → ¬ (pad ≤ a ∧ a < pad + 1536) →
    mem a = mem0 a

/-- One pass of the hashing loop hashes the current level into the next. -/
theorem packedLevel_step (hash : HashCalls m w .pairs) (room : w.stackLo + hashStack ≤ sp) (pos : 0 < depth)
    (hg : g = out + 32 * count) (hD : depth ≤ 57)
    (acc : w.access out (32 * count + 2 * levelSize count depth 0) = true)
    (slack : out + 32 * count + 2 * levelSize count depth 0 + 32 ≤ addressBound)
    (rPad : Apart (out, 32 * count + 2 * levelSize count depth 0) (pad, 1536))
    (rCtx : Apart (out, 32 * count + 2 * levelSize count depth 0) (ctx, 32))
    (rTable : Apart (out, 32 * count + 2 * levelSize count depth 0) (table, Kernel.tableSize))
    (rZeros : Apart (out, 32 * count + 2 * levelSize count depth 0) (zeros, 32 * (zeroHeights + 1)))
    (usize : USize.size = 2 ^ 64) {env : Env} {mem : Memory} {h : Nat} (hh : h < depth)
    (st : PackedAt w width src stride count out ctx depth g table zeros pad mask mem0 slots env mem h) :
    ∃ env' mem', Runs m w sp env mem (.block [
        ifElse (eq (RootPacked.h + 1) RootPacked.depth) [RootPacked.dst ::= RootPacked.out]
          [RootPacked.dst ::= RootPacked.lvl + RootPacked.size],
        callInto RootPacked.sink "ssz_hash_pairs" [RootPacked.dst, RootPacked.lvl, RootPacked.lvl + 32,
          RootPacked.size / 64, RootPacked.ctx],
        RootPacked.lvl ::= RootPacked.dst, RootPacked.size ::= RootPacked.size / 2, RootPacked.h ::= RootPacked.h + 1])
        env' mem' ∧
      PackedAt w width src stride count out ctx depth g table zeros pad mask mem0 slots env' mem' (h + 1) := by
  obtain ⟨s0, s1, sle⟩ := levelSize_step (count := count) hh
  have top := levelSize_top count depth
  have accEnd := access_end acc
  have rp := rPad
  have rc := rCtx
  have rt := rTable
  have rz := rZeros
  simp only [Apart, addressBound] at rp rc rt rz slack
  -- The quantities of this pass, as plain numbers.
  generalize hS0 : levelSize count depth 0 = S0 at *
  generalize count * 2 ^ (depth - (h + 1)) = q at s0 s1
  generalize hSh : levelSize count depth h = Sh at *
  generalize hSn : levelSize count depth (h + 1) = Sn at *
  have lvlEq : levelAt out g count depth h = g + 2 * (S0 - Sh) := by
    simp only [levelAt, hS0, hSh]; rw [if_neg (by omega)]
  obtain ⟨dst, hdst⟩ : ∃ dst, dst = if h + 1 = depth then out else levelAt out g count depth h + Sh := ⟨_, rfl⟩
  have dstAt : levelAt out g count depth (h + 1) = dst := by
    rw [hdst]
    by_cases last : h + 1 = depth
    · rw [if_pos last]; simp only [levelAt]; rw [if_pos last]
    · rw [if_neg last, lvlEq]; simp only [levelAt, hS0, hSn]; rw [if_neg last]; omega
  have dstIn : out ≤ dst ∧ dst + Sn ≤ out + (32 * count + 2 * S0) := by
    rw [hdst]
    by_cases last : h + 1 = depth
    · rw [if_pos last]; rw [last] at hSn; omega
    · rw [if_neg last, lvlEq]; omega
  have v := st.vars
  -- The branch picks the next level's place.
  have branch : Runs m w sp env mem (ifElse (eq (RootPacked.h + 1) RootPacked.depth) [RootPacked.dst ::= RootPacked.out]
      [RootPacked.dst ::= RootPacked.lvl + RootPacked.size]) (Asm.assign env 14 (UInt64.ofNat dst)) mem := by
    have c := eval_eq_nat (w := w) (env := env) (mem := mem) (a := RootPacked.h + 1) (b := RootPacked.depth)
      (eval_add (eval_var st.height) (eval_lit 1)) (eval_var v.levels) (by omega) (by omega)
    by_cases last : h + 1 = depth
    · rw [if_pos last] at c
      rw [hdst, if_pos last]
      exact Runs.ifElse_true 1 c (by decide) (Runs.set' (eval_var v.out))
    · rw [if_neg last] at c
      rw [hdst, if_neg last]
      exact Runs.ifElse_false c (Runs.set' (eval_add (eval_var st.lvl) (eval_var (hSh ▸ st.size))))
  -- The hashing run's conditions: its digests and inputs lie in the output's region, apart from each other.
  have lvl := st.lvl
  rw [lvlEq] at lvl
  have dstCase : (dst = out ∧ Sn = 32 * count) ∨ dst = g + 2 * (S0 - Sh) + Sh := by
    rw [hdst]
    by_cases last : h + 1 = depth
    · rw [if_pos last]; rw [last] at hSn; exact .inl ⟨rfl, by omega⟩
    · rw [if_neg last, lvlEq]; exact .inr rfl
  have pre : RunPre w mem 64 64 dst (g + 2 * (S0 - Sh)) (g + 2 * (S0 - Sh) + 32) q ctx table pad mask :=
    st.ready.runPre (lo := out) (span := 32 * count + 2 * S0) acc rPad rCtx rTable ⟨dstIn.1, by omega⟩
      (fun p hp => ⟨by omega, by omega, by omega, by omega⟩) ⟨by simp only [addressBound]; omega, by simp only [addressBound]; omega⟩
      (fun p hp => by simp only [Apart]; omega)
  obtain ⟨mem', call, after⟩ := (hash sp mem dst (g + 2 * (S0 - Sh)) (g + 2 * (S0 - Sh) + 32) q ctx table pad mask
    pre st.ready.kernels room)
  have nm : Layout.pairs.name = "ssz_hash_pairs" := rfl
  rw [nm] at call
  -- Memory after the run is the hashed memory, off the padding area.
  have after' : ∀ a, ¬ (pad ≤ a ∧ a < pad + 1536) →
      mem' a = hashed mem dst (g + 2 * (S0 - Sh)) (g + 2 * (S0 - Sh) + 32) q 64 64 a := after
  let E1 := Asm.assign env 14 (UInt64.ofNat dst)
  have callRuns := Runs.call (m := m) (sp := sp) (env := E1) (mem := mem) (dst := 10)
    (args := [RootPacked.dst, RootPacked.lvl, RootPacked.lvl + 32, RootPacked.size / 64, RootPacked.ctx])
    (eval_five (eval_var assign_eq) (eval_var (by simp only [E1]; rw [assign_ne (by decide), lvl]))
      (eval_add (eval_var (by simp only [E1]; rw [assign_ne (by decide), lvl])) (eval_lit 32))
      (eval_div (eval_var (by simp only [E1]; rw [assign_ne (by decide), st.size, hSh])) (eval_lit 64) (by omega) (by decide) (by decide))
      (eval_var (by simp only [E1]; rw [assign_ne (by decide), v.ctx]))) (show Calls m w "ssz_hash_pairs" sp
        [UInt64.ofNat dst, UInt64.ofNat (g + 2 * (S0 - Sh)), UInt64.ofNat (g + 2 * (S0 - Sh) + 32),
          UInt64.ofNat (Sh / 64), UInt64.ofNat ctx] mem 0 mem' by rw [show Sh / 64 = q by omega]; exact call)
  let E2 := Asm.assign E1 10 0
  have setLvl := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem') (x := 11) (env := E2) (e := RootPacked.dst)
    (eval_var (v := UInt64.ofNat dst) (by simp [E2, E1, Asm.assign]))
  let E3 := Asm.assign E2 11 (UInt64.ofNat dst)
  have setSize := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem') (x := 12) (env := E3) (e := RootPacked.size / 2)
    (eval_div (eval_var (by simp only [E3, E2, E1]; rw [assign_ne (by decide), assign_ne (by decide),
      assign_ne (by decide), st.size, hSh])) (eval_lit 2) (by omega) (by decide) (by decide))
  let E4 := Asm.assign E3 12 (UInt64.ofNat (Sh / 2))
  have setH := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem') (x := 13) (env := E4) (e := RootPacked.h + 1)
    (eval_add (eval_var (by simp only [E4, E3, E2, E1]; rw [assign_ne (by decide), assign_ne (by decide),
      assign_ne (by decide), assign_ne (by decide), st.height])) (eval_lit 1))
  refine ⟨_, mem', Runs.block_cons branch (Runs.block_cons callRuns (Runs.block_cons setLvl
    (Runs.block_cons setSize setH))), ?_⟩
  -- The digests sit in the output's region, so every byte outside it and the padding area stays.
  have keep : ∀ a, ¬ (dst ≤ a ∧ a < dst + 32 * q) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a :=
    fun a o p => by rw [after' a p, hashed_outside o]
  have next : packedLevel slots (h + 1) =
      hashPairsReference (packedLevel slots h) (0 : Nat).toUSize q.toUSize := by
    rw [packedLevel_succ, st.len, hSh, show Sh / 64 = q by omega]; rfl
  have qSmall : q < USize.size := by rw [usize]; omega
  refine ⟨((((v.write _ (by decide)).write _ (by decide)).write _ (by decide)).write _ (by decide)).write _
      (by decide), by simp [E4, E3, E2, E1, Asm.assign, dstAt], ?_, by simp [Asm.assign], by omega, ?_, ?_, ?_, ?_⟩
  · show Asm.assign E4 13 _ 12 = _
    rw [assign_ne (by decide)]
    simp only [E4]
    rw [assign_eq, hSn, show Sh / 2 = Sn by omega]
  · -- The next level is the Lean hash of the current one's pairs.
    rw [dstAt, next]
    have held := holds_hashed_pairs st.holds dst 0 q (by rw [st.len, hSh]; omega) (by rw [usize]; decide) qSmall
    rw [lvlEq, Nat.add_zero] at held
    refine held.congr fun i hi => after' _ ?_
    rw [hashPairsReference_size, toUSize_toNat _ qSmall] at hi
    have := dstIn
    omega
  · rw [packedLevel_succ, st.len, hSh, show Sh / 64 = q by omega]
    simp only [hashPairs, hashPairsReference_size, toUSize_toNat _ qSmall]
    omega
  · -- The context, the table and the zero roots are outside both.
    have pc := st.ready.padCtx
    have pt := st.ready.padTable
    have pz := st.ready.padZeros
    simp only [Apart] at pc pt pz
    exact st.ready.frame fun a held => by
      simp only [RootReady.Held] at held
      exact keep a (by omega) (by omega)
  · intro a o p
    rw [hS0] at o
    rw [keep a (by omega) p, st.frame a (by rw [hS0]; exact o) p]

/-- The hashing loop of the packed roots driver, from a height, runs to the top level, which lands in the output. -/
theorem packedLevels_runs (hash : HashCalls m w .pairs) (room : w.stackLo + hashStack ≤ sp) (pos : 0 < depth)
    (hg : g = out + 32 * count) (hD : depth ≤ 57)
    (acc : w.access out (32 * count + 2 * levelSize count depth 0) = true)
    (slack : out + 32 * count + 2 * levelSize count depth 0 + 32 ≤ addressBound)
    (rPad : Apart (out, 32 * count + 2 * levelSize count depth 0) (pad, 1536))
    (rCtx : Apart (out, 32 * count + 2 * levelSize count depth 0) (ctx, 32))
    (rTable : Apart (out, 32 * count + 2 * levelSize count depth 0) (table, Kernel.tableSize))
    (rZeros : Apart (out, 32 * count + 2 * levelSize count depth 0) (zeros, 32 * (zeroHeights + 1)))
    (usize : USize.size = 2 ^ 64) :
    ∀ k h (env : Env) (mem : Memory), h + k = depth →
      PackedAt w width src stride count out ctx depth g table zeros pad mask mem0 slots env mem h →
      ∃ env' mem', Runs m w sp env mem packedLoop env' mem' ∧
        PackedAt w width src stride count out ctx depth g table zeros pad mask mem0 slots env' mem' depth := by
  intro k
  induction k with
  | zero =>
    -- At the top, the loop stops.
    intro h env mem hk st
    simp only [Nat.add_zero] at hk
    subst hk
    refine ⟨env, mem, Runs.loop_exit _ _ _ _ _ _ _ ?_, st⟩
    rw [eval_lt (eval_var st.height) (eval_var st.vars.levels) (by omega) (by omega), if_neg (Nat.lt_irrefl _)]
  | succ k ih =>
    -- Below the top, one pass, then the rest.
    intro h env mem hk st
    obtain ⟨env₁, mem₁, pass, st₁⟩ := packedLevel_step hash room pos hg hD acc slack rPad rCtx rTable rZeros usize
      (by omega) st
    obtain ⟨env', mem', rest, fin⟩ := ih (h + 1) env₁ mem₁ (by omega) st₁
    refine ⟨env', mem', Runs.loop_step 1 ?_ (by decide) pass rest, fin⟩
    rw [eval_lt (eval_var st.height) (eval_var st.vars.levels) (by omega) (by omega), if_pos (by omega)]

end Levels

/-! ### The driver -/

/-- The bytes the packed roots driver uses from its output on: the roots, then the blocks and the levels after them. -/
def packedSpan (width count : Nat) : Nat :=
  if depthFor (nodesFor width) = 0 then 32 * count
  else 32 * count + 2 * levelSize count (depthFor (nodesFor width)) 0

/-- Below the cap, the packed bound is exactly the bytes the driver uses. -/
theorem packedSpan_eq {width count : Nat} (below : packedNeed width count < scratchCap) :
    packedSpan width count = packedNeed width count := by
  have capv : scratchCap = 2 ^ 62 := rfl
  simp only [packedNeed, packedSpan] at below ⊢
  generalize depthFor (nodesFor width) = D at below ⊢
  have pos : 0 < 2 ^ D := Nat.pow_pos (by decide)
  by_cases z : D = 0
  · simp only [if_pos z] at below ⊢
    simp only [smul, sat] at below ⊢
    omega
  · simp only [if_neg z] at below ⊢
    simp only [sadd, smul, sat] at below ⊢
    rcases Nat.eq_zero_or_pos count with c0 | cp
    · subst c0
      simp [levelSize]
    -- No step saturates, since the sum stays below the cap and every factor is positive.
    have a : 2 * count < scratchCap := by
      refine Nat.lt_of_not_le fun big => ?_
      rw [Nat.min_eq_right big] at below
      have : scratchCap ≤ scratchCap * min (32 * 2 ^ D) scratchCap :=
        Nat.le_mul_of_pos_right _ (by rw [capv]; omega)
      omega
    rw [Nat.min_eq_left (Nat.le_of_lt a)] at below
    have b : 32 * 2 ^ D < scratchCap := by
      refine Nat.lt_of_not_le fun big => ?_
      rw [Nat.min_eq_right big] at below
      have : scratchCap ≤ 2 * count * scratchCap := Nat.le_mul_of_pos_left _ (by omega)
      omega
    rw [Nat.min_eq_left (Nat.le_of_lt b)] at below
    rw [Nat.min_eq_left (Nat.le_of_lt b), Nat.min_eq_left (Nat.le_of_lt a)]
    have e : 2 * levelSize count D 0 = 2 * count * (32 * 2 ^ D) := by
      simp only [levelSize, Nat.sub_zero, Nat.mul_assoc]
    rw [e]
    omega

/-- The stack a call to the packed roots driver needs: its return address and frame, then a hashing driver's call. -/
abbrev packedStack : Nat := 176 + hashStack

/-- The packed roots driver's frame holds twenty-one words. -/
theorem packedFrame : RootPacked.fn.frame = 21 := by decide

/--
The packed roots driver computes the Lean packed roots of values one stride apart in a buffer in memory.

The roots land at the output, and the blocks and levels after them.
Memory changes only there and in the padding area, and the context stays filled.
-/
theorem rootPacked_calls {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m)
    (hd : m.fns.lookup "ssz_depth_for" = some DepthFor.fn) (hf : m.fns.lookup "ssz_root_packed" = some RootPacked.fn)
    {sp : Nat} (room : w.stackLo + packedStack ≤ sp) {mem : Memory} {ctx table zeros pad : Nat} {mask : UInt64}
    (rd : RootReady w ctx table zeros pad mask mem) {base start : Nat} {b : ByteArray} (holds : Holds mem base b)
    (bAcc : w.access base b.size = true) {width stride count out : Nat} (gap : width ≤ stride)
    (strideSmall : stride < 2 ^ 63) (hw : width ≤ scratchCap)
    (inside : ∀ i < count, start + stride * i + width ≤ b.size) (reach : base + start + stride * count ≤ addressBound)
    (acc : w.access out (packedSpan width count) = true) (slack : out + packedSpan width count + 32 ≤ addressBound)
    (oB : Apart (out, packedSpan width count) (base, b.size)) (oPad : Apart (out, packedSpan width count) (pad, 1536))
    (oCtx : Apart (out, packedSpan width count) (ctx, 32))
    (oTable : Apart (out, packedSpan width count) (table, Kernel.tableSize))
    (oZeros : Apart (out, packedSpan width count) (zeros, 32 * (zeroHeights + 1)))
    (bPad : Apart (base, b.size) (pad, 1536)) (usize : USize.size = 2 ^ 64) :
    ∃ mem', Calls m w "ssz_root_packed" sp [UInt64.ofNat width, UInt64.ofNat (base + start), UInt64.ofNat stride,
        UInt64.ofNat count, UInt64.ofNat out, UInt64.ofNat ctx] mem 0 mem' ∧
      Holds mem' out (packedRoots width (nodesFor width) b start stride count) ∧
      RootReady w ctx table zeros pad mask mem' ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + packedSpan width count) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a := by
  have frame := packedFrame
  have stack : hashStack = 10392 := rfl
  have ps : packedStack = 176 + 10392 := rfl
  have gs : gatherStack = 152 := rfl
  have inner : w.stackLo + hashStack ≤ sp - 8 - 8 * RootPacked.fn.frame := by rw [frame]; omega
  have dsmall := depth_small hw
  -- The start: the depth, the block size, and where the blocks go.
  obtain ⟨E5, start5, v5⟩ := packedStart_runs (w := w) hd (sp := sp - 8 - 8 * RootPacked.fn.frame)
    (by rw [frame]; omega) mem (src := base + start) (stride := stride) (count := count) (out := out) (ctx := ctx) hw
  have fits : width ≤ 32 * 2 ^ depthFor (nodesFor width) :=
    Nat.le_trans (by simp only [nodesFor]; omega) (Nat.mul_le_mul_left 32 (le_two_pow_depthFor _))
  unfold packedSpan at acc slack oB oPad oCtx oTable oZeros ⊢
  generalize hD : depthFor (nodesFor width) = D at *
  have accEnd := access_end acc
  have bEnd := access_end bAcc
  have ob := oB
  have op := oPad
  simp only [Apart, addressBound] at ob op reach slack
  -- The blocks' region lies inside the output's.
  have slotPos : 32 ≤ 32 * 2 ^ D := by have := Nat.one_le_two_pow (n := D); omega
  have S0eq : levelSize count D 0 = 32 * 2 ^ D * count := by simp [levelSize, Nat.mul_comm]
  have blocksIn : (if D = 0 then out else out + 32 * count) + 32 * 2 ^ D * count ≤
      out + (if D = 0 then 32 * count else 32 * count + 2 * levelSize count D 0) := by
    by_cases z : D = 0
    · subst z; rw [if_pos rfl, if_pos rfl]; simp only [Nat.pow_zero]; omega
    · rw [if_neg z, if_neg z, S0eq]; omega
  have outLe : 32 * count ≤ (if D = 0 then 32 * count else 32 * count + 2 * levelSize count D 0) := by
    split <;> omega
  -- The gather's conditions.
  have pre : GatherPre w (if D = 0 then out else out + 32 * count) (base + start) count width (stride - width)
      (32 * 2 ^ D - width) := by
    have strideEq : width + (stride - width) = stride := by omega
    have slotEq : width + (32 * 2 ^ D - width) = 32 * 2 ^ D := by omega
    refine ⟨?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
    · rw [slotEq]; exact access_sub acc (by split <;> omega) blocksIn
    · rw [strideEq]; have := inside i hi; exact access_sub bAcc (by omega) (by omega)
    · rw [strideEq]; simp only [addressBound]; omega
    · rw [slotEq, strideEq]; have := inside i hi; simp only [Apart]
      by_cases z : D = 0 <;> simp only [z, if_true, if_false] at blocksIn ob ⊢ <;> omega
  obtain ⟨E6, memG, gath, v6, heldG, frameG⟩ := packedGather_runs (sp := sp - 8 - 8 * RootPacked.fn.frame)
    (gatherCalls w gmod) (by omega) v5 rd holds rfl
    gap strideSmall fits dsmall pre inside (by simp only [Apart] at bPad ⊢; omega) usize
  -- The levels start at the blocks, at height zero.
  have pr : packedRoots width (nodesFor width) b start stride count =
      packedLevel (gatherReference b start.toUSize stride.toUSize width.toUSize count.toUSize (32 * 2 ^ D).toUSize) D := by
    rw [← hD]; rfl
  rw [pr]
  have slotsLen := gatherReference_size b start.toUSize stride.toUSize width.toUSize count.toUSize
    (32 * 2 ^ D).toUSize
  have pw : 2 ^ D ≤ 2 ^ 57 := Nat.pow_le_pow_right (by decide) dsmall
  rw [toUSize_toNat _ (by rw [usize]; omega), toUSize_toNat _ (by rw [usize]; omega)] at slotsLen
  generalize gatherReference b start.toUSize stride.toUSize width.toUSize count.toUSize (32 * 2 ^ D).toUSize = slots
    at heldG slotsLen ⊢
  have l1 := Runs.set' (m := m) (w := w) (sp := sp - 8 - 8 * RootPacked.fn.frame) (x := 11) (env := E6) (mem := memG)
    (e := RootPacked.g) (eval_var v6.g)
  have l2 := Runs.set' (m := m) (w := w) (sp := sp - 8 - 8 * RootPacked.fn.frame) (x := 12) (mem := memG)
    (env := Asm.assign E6 11 (UInt64.ofNat (if D = 0 then out else out + 32 * count)))
    (e := RootPacked.count * RootPacked.slot)
    (eval_mul (eval_var (by rw [assign_ne (by decide), v6.count])) (eval_var (by rw [assign_ne (by decide), v6.slot])))
  have l3 := Runs.set' (m := m) (w := w) (sp := sp - 8 - 8 * RootPacked.fn.frame) (x := 13) (mem := memG)
    (env := Asm.assign (Asm.assign E6 11 (UInt64.ofNat (if D = 0 then out else out + 32 * count))) 12
      (UInt64.ofNat (count * (32 * 2 ^ D)))) (e := (0 : Expr)) (eval_lit 0)
  have v9 := ((v6.write (x := 11) (UInt64.ofNat (if D = 0 then out else out + 32 * count)) (by decide)).write
    (x := 12) (UInt64.ofNat (count * (32 * 2 ^ D))) (by decide)).write (x := 13) (UInt64.ofNat 0) (by decide)
  have firstRuns := Runs.block_append start5 gath
  -- The blocks and the shape words are the only bytes written so far.
  have readyG : RootReady w ctx table zeros pad mask memG := by
    have pc := rd.padCtx
    have pt := rd.padTable
    have pz := rd.padZeros
    have oc := oCtx
    have ot := oTable
    have oz := oZeros
    simp only [Apart] at pc pt pz oc ot oz
    exact rd.frame fun a held => by
      simp only [RootReady.Held] at held
      exact frameG a (by omega) (by by_cases z : D = 0 <;> simp only [z, if_true, if_false] at blocksIn oc ot oz ⊢ <;> omega)
  by_cases z : D = 0
  · -- Values of one node: the gathered blocks are the roots, and no level is hashed.
    subst z
    have exit : Runs m w (sp - 8 - 8 * RootPacked.fn.frame)
        (Asm.assign (Asm.assign (Asm.assign E6 11 (UInt64.ofNat (if 0 = 0 then out else out + 32 * count))) 12
          (UInt64.ofNat (count * (32 * 2 ^ 0)))) 13 (UInt64.ofNat 0)) memG packedLoop
        (Asm.assign (Asm.assign (Asm.assign E6 11 (UInt64.ofNat (if 0 = 0 then out else out + 32 * count))) 12
          (UInt64.ofNat (count * (32 * 2 ^ 0)))) 13 (UInt64.ofNat 0)) memG :=
      Runs.loop_exit _ _ _ _ _ _ _ (by
        rw [eval_lt (eval_var assign_eq) (eval_var v9.levels) (by decide) (by decide)]; rfl)
    refine ⟨memG, Calls.fn hf (by rw [frame]; omega) rfl (Runs.block_append firstRuns
      (Runs.block_cons l1 (Runs.block_cons l2 (Runs.block_cons l3 exit)))) rfl, ?_, readyG, fun a o p => ?_⟩
    · simpa using heldG
    · exact frameG a (fun h => p ⟨h.1, by omega⟩) (by simp at o ⊢; omega)
  · -- Blocks of several nodes: the levels are hashed down to the roots.
    rw [if_neg z] at acc slack oPad oCtx oTable oZeros heldG frameG l1 l2 l3 v9 ⊢
    let E9 := Asm.assign (Asm.assign (Asm.assign E6 11 (UInt64.ofNat (out + 32 * count))) 12
      (UInt64.ofNat (count * (32 * 2 ^ D)))) 13 (UInt64.ofNat 0)
    have st0 : PackedAt w width (base + start) stride count out ctx D (out + 32 * count) table zeros pad mask mem
        slots E9 memG 0 := by
      have lvl0 : levelAt out (out + 32 * count) count D 0 = out + 32 * count := by
        simp only [levelAt]; rw [if_neg (by omega)]; omega
      refine ⟨v9, by simp [E9, Asm.assign, lvl0], ?_, by simp [E9, Asm.assign], by omega, ?_, ?_, readyG, ?_⟩
      · simp only [E9, Asm.assign]; simp [levelSize]
      · rw [lvl0]; exact heldG
      · rw [packedLevel_zero, slotsLen]; simp [levelSize, Nat.mul_comm]
      · intro a o p
        exact frameG a (fun h => p ⟨h.1, by omega⟩) (by rw [S0eq] at o; omega)
    obtain ⟨env', mem', loopRuns, fin⟩ := packedLevels_runs (m := m) hash.pairs inner (by omega) rfl dsmall acc
      (by simp only [addressBound]; omega) oPad oCtx oTable oZeros usize D 0 E9 memG (by omega) st0
    have top : levelAt out (out + 32 * count) count D D = out := by simp [levelAt]
    have held := fin.holds
    rw [top] at held
    exact ⟨mem', Calls.fn hf (by rw [frame]; omega) rfl (Runs.block_append firstRuns
      (Runs.block_cons l1 (Runs.block_cons l2 (Runs.block_cons l3 loopRuns)))) rfl, held, fin.ready, fin.frame⟩

end Ssz.Native.Driver
