import SszNative.Driver.Tree
import SszNative.Proofs.Driver.Hash
import SszNative.Proofs.Root.Merkle

/-!
The Merkle tree driver computes the root of the perfect tree over its nodes.

Each pass of its loop hashes one level into the scratch buffer, right after the level before.
The proof follows the specification's tree level by level:
node j of the level at height h is the root of the subtree over leaves j 2^h onward.
-/

namespace Ssz.Native.Driver

open Ssz Ssz.Native.Asm Ssz.Native.Ir

/-! ## Nodes in memory -/

/-- The 32 bytes at an address, as a node. -/
def nodeAt (mem : Memory) (a : Nat) : Bytes :=
  Array.ofFn (n := 32) fun i => mem (a + i.val)

/-- A count of bytes from an address, as a buffer. -/
def bytesAt (mem : Memory) (a n : Nat) : ByteArray :=
  ⟨Array.ofFn (n := n) fun i => mem (a + i.val)⟩

/-- A node reads only its own 32 bytes. -/
theorem nodeAt_congr {m₁ m₂ : Memory} {a : Nat} (h : ∀ i < 32, m₁ (a + i) = m₂ (a + i)) :
    nodeAt m₁ a = nodeAt m₂ a := by
  unfold nodeAt
  congr 1
  funext i
  exact h i.val i.isLt

/-- Byte i of a node is the byte i past its address. -/
theorem nodeAt_get (mem : Memory) (a i : Nat) (hi : i < 32) : (nodeAt mem a)[i]'(by simp [nodeAt, hi]) = mem (a + i) := by
  simp [nodeAt]

/-- A pair's message is its two nodes, one after the other. -/
theorem pairMessage_nodes (mem : Memory) (l r : Nat) : pairMessage mem l r = ⟨nodeAt mem l ++ nodeAt mem r⟩ := by
  simp only [pairMessage, nodeAt]
  apply congrArg ByteArray.mk
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_ofFn, Array.getElem_append, Array.size_ofFn]
    split <;> simp

/-- Node p of the digests of a hashed run is the specification's parent of the run's pair p. -/
theorem nodeAt_hashed (mem : Memory) (out left right n ls rs p : Nat) (hp : p < n) :
    nodeAt (hashed mem out left right n ls rs) (out + 32 * p) =
      combine (nodeAt mem (left + ls * p)) (nodeAt mem (right + rs * p)) := by
  simp only [combine, ← pairMessage_nodes]
  apply Array.ext
  · simp [nodeAt]
  · intro i h1 h2
    simp only [nodeAt, Array.getElem_ofFn] at h1 ⊢
    have hi : i < 32 := by simpa using h1
    rw [hashed_inside hp hi, Kernel.get!_eq _ _ (by simp [hi])]
    rfl

/-- Node j of the bytes read from an address is the node 32 j bytes past it. -/
theorem nodeOf_bytesAt (mem : Memory) (a count j : Nat) (hj : j < count) :
    nodeOf (bytesAt mem a (32 * count)) 0 j = nodeAt mem (a + 32 * j) := by
  simp only [nodeOf, bytesAt, nodeAt, ByteArray.data_extract, Nat.zero_add]
  apply Array.ext
  · simp; omega
  · intro i h1 h2
    simp only [Array.getElem_extract, Array.getElem_ofFn]
    rw [Nat.add_assoc]

/-! ## The zero-tree roots -/

/-- The table of zero-tree roots, as the fold its loop runs. -/
private theorem zeroRootsTable_fold : zeroRootsTable = (List.foldl (fun (b : ByteArray × ByteArray) (_ : Nat) =>
    (b.1 ++ Sha256.hash (b.2 ++ b.2), Sha256.hash (b.2 ++ b.2)))
    (⟨Array.replicate 32 0⟩, ⟨Array.replicate 32 0⟩) (List.range zeroHeights)).1 := by
  -- The counted loop is a fold over the heights.
  unfold zeroRootsTable
  unfold_loop
  rfl

/-- After some heights, the loop holds the top root, and the table of roots up to it. -/
private theorem zeroFold_spec (n : Nat) :
    let F := List.foldl (fun (b : ByteArray × ByteArray) (_ : Nat) =>
      (b.1 ++ Sha256.hash (b.2 ++ b.2), Sha256.hash (b.2 ++ b.2)))
      (⟨Array.replicate 32 0⟩, ⟨Array.replicate 32 0⟩) (List.range n)
    F.2.size = 32 ∧ F.2.data = Ssz.zeroRoot combine zeroChunk n ∧ F.1.size = 32 * (n + 1) ∧
      ∀ j ≤ n, nodeOf F.1 0 j = Ssz.zeroRoot combine zeroChunk j := by
  induction n with
  | zero =>
    refine ⟨rfl, rfl, rfl, fun j hj => ?_⟩
    rw [Nat.le_zero.mp hj]
    rfl
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize List.foldl _ _ (List.range n) = F at ih ⊢
    obtain ⟨T, N⟩ := F
    obtain ⟨nodeSize, nodeData, tableSize, nodes⟩ := ih
    -- The next root hashes the top one with itself, and joins the table.
    have next : (Sha256.hash (N ++ N)).data = Ssz.zeroRoot combine zeroChunk (n + 1) := by
      simp only [Ssz.zeroRoot, ← nodeData, combine, ← ByteArray.data_append]
    refine ⟨Sha256.hash_size _, next, by rw [ByteArray.size_append, tableSize, Sha256.hash_size]; omega,
      fun j hj => ?_⟩
    by_cases old : j ≤ n
    · rw [nodeOf_append_left _ _ _ (by rw [tableSize]; omega), nodes j old]
    · rw [show j = n + 1 by omega, nodeOf_append_right _ _ _ (by rw [tableSize]),
        nodeOf_single _ (Sha256.hash_size _), next]

/-- The table the drivers read holds the zero tree of every height it covers, 32 bytes each. -/
theorem zeroRootsTable_spec : zeroRootsTable.size = 32 * (zeroHeights + 1) ∧
    ∀ h ≤ zeroHeights, nodeOf zeroRootsTable 0 h = zeroSubtree h := by
  obtain ⟨_, _, size, nodes⟩ := zeroFold_spec zeroHeights
  rw [zeroRootsTable_fold]
  exact ⟨size, fun h hh => by rw [nodes h hh, zeroSubtree_eq]⟩

/-- Memory holding the table holds the zero tree of each covered height at 32 bytes per height. -/
theorem nodeAt_zeros {mem : Memory} {zeros : Nat}
    (table : ∀ i < 32 * (zeroHeights + 1), mem (zeros + i) = zeroRootsTable.get! i) (h : Nat) (hh : h ≤ zeroHeights) :
    nodeAt mem (zeros + 32 * h) = zeroSubtree h := by
  obtain ⟨size, nodes⟩ := zeroRootsTable_spec
  rw [← nodes h hh, nodeOf]
  apply Array.ext
  · simp [nodeAt, size]; omega
  · intro i h1 h2
    simp only [nodeAt, Array.getElem_ofFn, ByteArray.data_extract, Array.getElem_extract, Nat.zero_add]
    have hi : i < 32 := by simpa [nodeAt] using h1
    rw [Nat.add_assoc, table _ (by omega), Kernel.get!_eq _ _ (by rw [size]; omega)]
    rfl

/-! ## One level up -/

/-- The parent of nodes 2j and 2j + 1 of a level is node j of the level above. -/
theorem parent_pair (leaves : Array Bytes) (h j : Nat) :
    combine (subtreeAt leaves h (2 * j * 2 ^ h)) (subtreeAt leaves h ((2 * j + 1) * 2 ^ h)) =
      subtreeAt leaves (h + 1) (j * 2 ^ (h + 1)) := by
  rw [up_index, subtreeAt_split, Nat.add_mul, Nat.one_mul]

/-- The last node of an odd level, against the zero tree, is the last node of the level above. -/
theorem parent_last (leaves : Array Bytes) (h W : Nat) (odd : W % 2 = 1) (covers : leaves.size ≤ W * 2 ^ h) :
    combine (subtreeAt leaves h ((W - 1) * 2 ^ h)) (zeroSubtree h) = subtreeAt leaves (h + 1) (W / 2 * 2 ^ (h + 1)) := by
  -- The right half lies past the leaves, so it is the zero tree.
  have whole : (W - 1) * 2 ^ h + 2 ^ h = W * 2 ^ h := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  rw [up_index, subtreeAt_split, show 2 * (W / 2) = W - 1 by omega,
    subtreeAt_past leaves h ((W - 1) * 2 ^ h + 2 ^ h) (by rw [whole]; exact covers)]

/-- The level above covers the leaves as tightly as the level below. -/
theorem covers_up (count h W : Nat) (covers : count ≤ W * 2 ^ h) (tight : (W - 1) * 2 ^ h < count) :
    count ≤ (W + 1) / 2 * 2 ^ (h + 1) ∧ ((W + 1) / 2 - 1) * 2 ^ (h + 1) < count := by
  rw [up_index, up_index]
  exact ⟨Nat.le_trans covers (Nat.mul_le_mul_right _ (by omega)),
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right _ (by omega)) tight⟩

/-! ## More expressions -/

section
variable {w : World} {env : Env} {mem : Memory}

/-- Whether one converted number is at most another, as one or zero. -/
theorem eval_le {a b : Expr} {p q : Nat} (ha : eval w env mem a = some (UInt64.ofNat p))
    (hb : eval w env mem b = some (UInt64.ofNat q)) (bp : p < 2 ^ 64) (bq : q < 2 ^ 64) :
    eval w env mem (Expr.le a b) = some (if p ≤ q then 1 else 0) := by
  show eval w env mem (.cmp .be a b) = _
  simp only [eval, ha, hb, Option.bind_eq_bind, Option.bind, Cond.holds]
  by_cases h : p ≤ q
  · rcases Nat.lt_or_eq_of_le h with lt | rfl
    · simp [h, (ofNat_lt bp bq).mpr lt]
    · simp
  · simp [h, mt (ofNat_lt bp bq).mp (by omega), mt (ofNat_inj bp bq).mp (by omega)]

/-- Whether two converted numbers are equal, as one or zero. -/
theorem eval_eq {a b : Expr} {p q : Nat} (ha : eval w env mem a = some (UInt64.ofNat p))
    (hb : eval w env mem b = some (UInt64.ofNat q)) (bp : p < 2 ^ 64) (bq : q < 2 ^ 64) :
    eval w env mem (Expr.eq a b) = some (if p = q then 1 else 0) := by
  show eval w env mem (.cmp .e a b) = _
  simp only [eval, ha, hb, Option.bind_eq_bind, Option.bind, Cond.holds]
  by_cases h : p = q
  · subst h; simp
  · simp [h, mt (ofNat_inj bp bq).mp h]

/-- A remainder of converted numbers below the word size is the conversion of their remainder. -/
theorem eval_mod {a b : Expr} {p q : Nat} (ha : eval w env mem a = some (UInt64.ofNat p))
    (hb : eval w env mem b = some (UInt64.ofNat q)) (bp : p < 2 ^ 64) (bq : q < 2 ^ 64) (nz : q ≠ 0) :
    eval w env mem (a % b) = some (UInt64.ofNat (p % q)) := by
  show eval w env mem (.mod a b) = _
  have : (UInt64.ofNat q == 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro z
    exact nz ((ofNat_inj bq (by decide)).mp z)
  simp only [eval, ha, hb, Option.bind_eq_bind, Option.bind, this]
  rw [if_neg (by decide)]
  show some _ = some _
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_mod, ofNat_toNat bp, ofNat_toNat bq, ofNat_toNat (by have := Nat.mod_le p q; omega)]

/-- The bitwise or of two values. -/
theorem eval_or {a b : Expr} {x y : UInt64} (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (a ||| b) = some (x ||| y) := by
  show eval w env mem (.op .or a b) = _
  simp only [eval, ha, hb, aluResult, Option.bind_eq_bind, Option.bind]
  rfl

end

/-- Copying 32 bytes to an address puts the source's node there. -/
theorem nodeAt_copied (mem : Memory) (dst src : Nat) : nodeAt (copied mem dst src 32) dst = nodeAt mem src := by
  unfold nodeAt
  congr 1
  funext i
  exact copied_in mem dst src 32 i.val i.isLt

/-! ## What the tree driver needs -/

/--
What a tree root needs: its context, its nodes, the zero-tree roots, and buffers apart from all they touch.

The scratch buffer holds 32 bytes per node and per level, and the padding area is the hashing drivers' own.
-/
structure TreePre (w : World) (mem : Memory) (nodes count depth out scratch ctx table zeros pad : Nat)
    (mask : UInt64) : Prop where
  /-- The context's four words lie in memory the program may use. -/
  ctxAccess : w.access ctx 32 = true
  /-- The first word is the feature mask. -/
  maskAt : readLE mem ctx 8 = mask
  /-- The second word is the constant table's address. -/
  tableAt : readLE mem (ctx + 8) 8 = UInt64.ofNat table
  /-- The third word is the zero-tree roots' address. -/
  zerosAt : readLE mem (ctx + 16) 8 = UInt64.ofNat zeros
  /-- The fourth word is the padding area's address. -/
  padAt : readLE mem (ctx + 24) 8 = UInt64.ofNat pad
  /-- The constant table is in memory. -/
  tableBytes : Kernel.TableAt mem table
  /-- It lies in memory the program may use. -/
  tableAccess : w.access table Kernel.tableSize = true
  /-- The zero-tree roots are in memory. -/
  zeroRoots : ∀ i < 32 * (zeroHeights + 1), mem (zeros + i) = zeroRootsTable.get! i
  /-- They lie in memory the program may use. -/
  zerosAccess : w.access zeros (32 * (zeroHeights + 1)) = true
  /-- The depth has a zero tree in the table. -/
  deep : depth ≤ zeroHeights
  /-- The nodes fit the tree. -/
  fits : count ≤ 2 ^ depth
  /-- The nodes lie in memory the program may use. -/
  nodesAccess : w.access nodes (32 * count) = true
  /-- So does the output. -/
  outAccess : w.access out 32 = true
  /-- So does the scratch buffer. -/
  scratchAccess : w.access scratch (32 * (count + depth)) = true
  /-- So does the padding area. -/
  padAccess : w.access pad 1536 = true
  /-- The scratch buffer misses the nodes. -/
  scratchNodes : Apart (scratch, 32 * (count + depth)) (nodes, 32 * count)
  /-- It misses the output. -/
  scratchOut : Apart (scratch, 32 * (count + depth)) (out, 32)
  /-- It misses the context. -/
  scratchCtx : Apart (scratch, 32 * (count + depth)) (ctx, 32)
  /-- It misses the constant table. -/
  scratchTable : Apart (scratch, 32 * (count + depth)) (table, Kernel.tableSize)
  /-- It misses the zero-tree roots. -/
  scratchZeros : Apart (scratch, 32 * (count + depth)) (zeros, 32 * (zeroHeights + 1))
  /-- It misses the padding area. -/
  scratchPad : Apart (scratch, 32 * (count + depth)) (pad, 1536)
  /-- The padding area misses the nodes. -/
  padNodes : Apart (pad, 1536) (nodes, 32 * count)
  /-- It misses the context. -/
  padCtx : Apart (pad, 1536) (ctx, 32)
  /-- It misses the constant table. -/
  padTable : Apart (pad, 1536) (table, Kernel.tableSize)
  /-- It misses the zero-tree roots. -/
  padZeros : Apart (pad, 1536) (zeros, 32 * (zeroHeights + 1))
  /-- The nodes end a node short of the address bound, as the kernels' moved pointers need. -/
  nodesReach : nodes + 32 * (count + 1) ≤ 2 ^ 63
  /-- The output misses the nodes. -/
  outNodes : Apart (out, 32) (nodes, 32 * count)
  /-- It misses the zero-tree roots. -/
  outZeros : Apart (out, 32) (zeros, 32 * (zeroHeights + 1))

/-- A node a hashing call may read: one of the nodes, one before the call's output in the scratch buffer, or a zero root. -/
def Readable (nodes count scratch zeros dst a : Nat) : Prop :=
  (nodes ≤ a ∧ a + 32 ≤ nodes + 32 * count) ∨ (scratch ≤ a ∧ a + 32 ≤ dst) ∨
    (zeros ≤ a ∧ a + 32 ≤ zeros + 32 * (zeroHeights + 1))

/--
A hashing call into the scratch buffer, on readable nodes, meets the hashing driver's conditions.

Memory may differ from the start only in the scratch buffer and the padding area.
-/
theorem TreePre.runPre {w : World} {mem mm : Memory} {nodes count depth out scratch ctx table zeros pad : Nat}
    {mask : UInt64} (pre : TreePre w mem nodes count depth out scratch ctx table zeros pad mask)
    (frame : ∀ a, ¬ (scratch ≤ a ∧ a < scratch + 32 * (count + depth)) → ¬ (pad ≤ a ∧ a < pad + 1536) →
      mm a = mem a)
    {ls rs dst left right n : Nat} (inside : scratch ≤ dst ∧ dst + 32 * n ≤ scratch + 32 * (count + depth))
    (inputs : ∀ p < n, Readable nodes count scratch zeros dst (left + ls * p) ∧
      Readable nodes count scratch zeros dst (right + rs * p))
    (reach : left + ls * n ≤ 2 ^ 63 ∧ right + rs * n ≤ 2 ^ 63) :
    RunPre w mm ls rs dst left right n ctx table pad mask := by
  have sn := pre.scratchNodes
  have sc := pre.scratchCtx
  have st := pre.scratchTable
  have sz := pre.scratchZeros
  have sp := pre.scratchPad
  have pn := pre.padNodes
  have pc := pre.padCtx
  have pt := pre.padTable
  have pz := pre.padZeros
  simp only [Apart] at sn sc st sz sp pn pc pt pz
  have bs := access_bound pre.scratchAccess
  have hz : zeroHeights = 64 := rfl
  -- The context words lie outside both buffers, so they read as at the start.
  have ctxSame : ∀ k, k + 8 ≤ 32 → readLE mm (ctx + k) 8 = readLE mem (ctx + k) 8 := fun k hk =>
    readLE_congr _ _ _ _ fun i hi => frame _ (by omega) (by omega)
  -- Each readable node lies in memory the program may use, apart from the output and the padding area.
  have access : ∀ a, Readable nodes count scratch zeros dst a → w.access a 32 = true := by
    intro a ha
    rcases ha with h | h | h
    · exact access_sub pre.nodesAccess (by omega) (by omega)
    · exact access_sub pre.scratchAccess (by omega) (by omega)
    · exact access_sub pre.zerosAccess (by omega) (by omega)
  have apartOut : ∀ a, Readable nodes count scratch zeros dst a → Apart (dst, 32 * n) (a, 32) := by
    intro a ha
    simp only [Apart]
    rcases ha with h | h | h <;> omega
  have apartPad : ∀ a, Readable nodes count scratch zeros dst a → Apart (pad, 1536) (a, 32) := by
    intro a ha
    simp only [Apart]
    rcases ha with h | h | h <;> omega
  refine ⟨pre.ctxAccess, ?_, ?_, ?_, ⟨fun i hi => ?_, access_sub pre.scratchAccess inside.1 (by omega),
    pre.tableAccess, fun p hp => ⟨access _ (inputs p hp).1, access _ (inputs p hp).2⟩, reach,
    by simp only [Apart]; omega, fun p hp => ⟨apartOut _ (inputs p hp).1, apartOut _ (inputs p hp).2⟩⟩,
    pre.padAccess, by simp only [Apart]; omega, by simp only [Apart]; omega,
    fun p hp => ⟨apartPad _ (inputs p hp).1, apartPad _ (inputs p hp).2⟩, by simp only [Apart]; omega⟩
  · rw [show ctx = ctx + 0 from rfl, ctxSame 0 (by omega)]; exact pre.maskAt
  · rw [ctxSame 8 (by omega)]; exact pre.tableAt
  · rw [ctxSame 24 (by omega)]; exact pre.padAt
  · rw [frame _ (by omega) (by omega)]; exact pre.tableBytes i hi

/-- A call to a hashing driver, as a run of the statement calling it. -/
theorem hash_call {m : Module} {w : World} {sp : Nat} {env : Env} {mm : Memory} {layout : Layout} {name : String}
    (ok : HashCalls m w layout) (hn : layout.name = name) {ls rs : Nat} (hl : layout.info.2.1 = ls)
    (hr : layout.info.2.2 = rs) {args : List Expr} {dst : Nat} {out left right n ctx table pad : Nat} {mask : UInt64}
    (pre : RunPre w mm ls rs out left right n ctx table pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + hashStack ≤ sp)
    (hv : args.mapM (eval w env mm) = some [UInt64.ofNat out, UInt64.ofNat left, UInt64.ofNat right, UInt64.ofNat n,
      UInt64.ofNat ctx]) :
    ∃ mm', Runs m w sp env mm (.call name args dst) (assign env dst 0) mm' ∧
      ∀ a, ¬ (pad ≤ a ∧ a < pad + 1536) → mm' a = hashed mm out left right n ls rs a := by
  subst hn hl hr
  obtain ⟨mm', c, h⟩ := (ok sp mm out left right n ctx table pad mask pre kernels room)
  exact ⟨mm', Runs.call hv c, h⟩

/-! ## The loop over levels -/

/--
The tree loop's state at a height: where the level lies, how wide it is, and what its nodes are.

Node j of the level is the root of the subtree over leaves j 2^h onward.
The level is the nodes themselves, or lies in the scratch buffer right before where the next level goes.
-/
structure Level (mem mm : Memory) (leaves : Array Bytes) (nodes count depth out scratch ctx zeros pad : Nat)
    (env : Env) (h W L S : Nat) : Prop where
  /-- The depth. -/
  depthV : env 2 = UInt64.ofNat depth
  /-- The output address. -/
  outV : env 3 = UInt64.ofNat out
  /-- The context. -/
  ctxV : env 5 = UInt64.ofNat ctx
  /-- The zero-tree roots' address. -/
  zerosV : env 6 = UInt64.ofNat zeros
  /-- The result so far. -/
  status : env 12 = 0
  /-- The level's address. -/
  levelV : env 7 = UInt64.ofNat L
  /-- The level's width. -/
  widthV : env 8 = UInt64.ofNat W
  /-- The level's height. -/
  heightV : env 9 = UInt64.ofNat h
  /-- Where the next level goes: after the scratch bytes used so far. -/
  dstV : env 10 = UInt64.ofNat (scratch + 32 * S)
  /-- No higher than the tree. -/
  height : h ≤ depth
  /-- At least one node. -/
  wide : 1 ≤ W
  /-- The scratch bytes used, with the next level, fit the buffer. -/
  used : S + W ≤ count + h
  /-- The level is the nodes, or lies in the scratch buffer right before the next level. -/
  place : (L = nodes ∧ W = count) ∨ (scratch ≤ L ∧ L + 32 * W = scratch + 32 * S)
  /-- Its nodes are the subtrees' roots. -/
  roots : ∀ j < W, nodeAt mm (L + 32 * j) = subtreeAt leaves h (j * 2 ^ h)
  /-- Its subtrees cover the leaves. -/
  covers : count ≤ W * 2 ^ h
  /-- Its last subtree holds a leaf. -/
  tight : (W - 1) * 2 ^ h < count
  /-- Memory is as at the start, outside the scratch buffer and the padding area. -/
  frame : ∀ a, ¬ (scratch ≤ a ∧ a < scratch + 32 * (count + depth)) → ¬ (pad ≤ a ∧ a < pad + 1536) →
    mm a = mem a

set_option maxHeartbeats 1000000 in
/-- One pass of the tree loop hashes the level into the next one, a height up. -/
theorem level_step {m : Module} {w : World} {sp : Nat} {mem : Memory}
    {nodes count depth out scratch ctx table zeros pad : Nat} {mask : UInt64}
    (okP : HashCalls m w .pairs) (okF : HashCalls m w .fixed)
    (pre : TreePre w mem nodes count depth out scratch ctx table zeros pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + hashStack ≤ sp)
    {leaves : Array Bytes} (size : leaves.size = count) {env : Env} {mm : Memory} {h W L S : Nat}
    (lv : Level mem mm leaves nodes count depth out scratch ctx zeros pad env h W L S) (below : h < depth) :
    Ends m w sp env mm (.block [
      Stmt.ifElse (Expr.le (Expr.var 8) 1)
        [Stmt.callInto ⟨13⟩ "ssz_hash_fixed" [Expr.var 10, Expr.var 7, Expr.var 6 + 32 * Expr.var 9, 1, Expr.var 5],
          Stmt.assign ⟨12⟩ (Expr.var 12 ||| Expr.var 13)]
        [Stmt.assign ⟨11⟩ (Expr.var 8 / 2),
          Stmt.callInto ⟨13⟩ "ssz_hash_pairs" [Expr.var 10, Expr.var 7, Expr.var 7 + 32, Expr.var 11, Expr.var 5],
          Stmt.assign ⟨12⟩ (Expr.var 12 ||| Expr.var 13),
          Stmt.when (Expr.ne (Expr.var 8 % 2) 0)
            [Stmt.callInto ⟨13⟩ "ssz_hash_fixed" [Expr.var 10 + 32 * Expr.var 11, Expr.var 7 + 32 * (Expr.var 8 - 1),
              Expr.var 6 + 32 * Expr.var 9, 1, Expr.var 5],
              Stmt.assign ⟨12⟩ (Expr.var 12 ||| Expr.var 13)],
          Stmt.assign ⟨8⟩ ((Expr.var 8 + 1) / 2)],
      Stmt.assign ⟨7⟩ (Expr.var 10), Stmt.assign ⟨10⟩ (Expr.var 10 + 32 * Expr.var 8),
      Stmt.assign ⟨9⟩ (Expr.var 9 + 1)])
      fun e mm' => Level mem mm' leaves nodes count depth out scratch ctx zeros pad e (h + 1) ((W + 1) / 2)
        (scratch + 32 * S) (S + (W + 1) / 2) := by
  have bs := access_bound pre.scratchAccess
  have bn := access_bound pre.nodesAccess
  have bz := access_bound pre.zerosAccess
  have bp := access_bound pre.padAccess
  have sp' := pre.scratchPad
  have sz := pre.scratchZeros
  have sn := pre.scratchNodes
  have pz := pre.padZeros
  have pn := pre.padNodes
  simp only [Apart] at sp' sz sn pz pn
  have hz : zeroHeights = 64 := rfl
  have deep := pre.deep
  have wide := lv.wide
  have used := lv.used
  have place := lv.place
  -- Every node of the level is readable by a call writing at or after the next level's start.
  have readLevel : ∀ d, scratch + 32 * S ≤ d → ∀ j < W, Readable nodes count scratch zeros d (L + 32 * j) := by
    intro d hd j hj
    rcases place with ⟨rfl, rfl⟩ | ⟨a, b⟩
    · left; omega
    · right; left; omega
  have readZero : ∀ d p, Readable nodes count scratch zeros d (zeros + 32 * h + 0 * p) := fun d p => by
    right; right; omega
  -- The zero tree of the level's height, as memory holds it at every point of the pass.
  have zeroAt : ∀ mm₁ : Memory, (∀ a, ¬ (scratch ≤ a ∧ a < scratch + 32 * (count + depth)) →
      ¬ (pad ≤ a ∧ a < pad + 1536) → mm₁ a = mem a) → nodeAt mm₁ (zeros + 32 * h) = zeroSubtree h :=
    fun mm₁ fr => by
      rw [nodeAt_congr (m₂ := mem) fun i hi => fr _ (by omega) (by omega)]
      exact nodeAt_zeros pre.zeroRoots h (by omega)
  have nr := pre.nodesReach
  have Lread : L + 32 * W + 32 ≤ 2 ^ 63 := by rcases place with ⟨rfl, rfl⟩ | ⟨a, b⟩ <;> omega
  refine Ends.cons (Q := fun e' mm' => (∀ y, y ≠ 8 → y ≠ 11 → y ≠ 12 → y ≠ 13 → e' y = env y) ∧
      e' 12 = 0 ∧
      e' 8 = UInt64.ofNat ((W + 1) / 2) ∧
      (∀ j < (W + 1) / 2, nodeAt mm' (scratch + 32 * S + 32 * j) = subtreeAt leaves (h + 1) (j * 2 ^ (h + 1))) ∧
      (∀ a, ¬ (scratch + 32 * S ≤ a ∧ a < scratch + 32 * S + 32 * ((W + 1) / 2)) →
        ¬ (pad ≤ a ∧ a < pad + 1536) →
        mm' a = mm a))
    (Ends.ite _ (eval_le (eval_var (x := 8) lv.widthV) (eval_lit 1) (by omega) (by decide)) (fun v => ?_) (fun v => ?_)) ?_
  · -- A lone node climbs one height against the zero tree.
    have w1 : W = 1 := by
      by_cases hw : W ≤ 1
      · omega
      · rw [if_neg hw] at v; exact absurd rfl v
    subst w1
    obtain ⟨mm1, r1, h1⟩ := hash_call (name := "ssz_hash_fixed") (ls := 32) (rs := 0) okF rfl rfl rfl
      (pre.runPre lv.frame (by omega) (fun p hp => ⟨by
        obtain rfl : p = 0 := by omega
        exact readLevel _ (Nat.le_refl _) 0 (by omega), readZero _ p⟩)
        (by omega)) kernels room
      (eval_five (eval_var (x := 10) lv.dstV) (eval_var (x := 7) lv.levelV)
        (eval_add (eval_var (x := 6) lv.zerosV) (eval_mul (eval_lit 32) (eval_var (x := 9) lv.heightV)))
        (eval_lit 1) (eval_var (x := 5) lv.ctxV))
    refine Ends.step r1 (Ends.of_runs
      (Runs.set _ _ _ _ _ _ _ _ (eval_or (eval_var (x := 12) lv.status) (eval_var assign_eq)))
      ⟨fun y _ _ c d => by simp only [assign, if_neg c, if_neg d], rfl, lv.widthV, fun j hj => ?_, fun a ha hp => ?_⟩)
    · have j0 : j = 0 := by omega
      subst j0
      have up := parent_last leaves h 1 rfl (by rw [size]; simpa using lv.covers)
      simp only [Nat.sub_self, Nat.zero_mul, show (1 : Nat) / 2 = 0 from rfl] at up
      have e := nodeAt_hashed mm (scratch + 32 * S) L (zeros + 32 * h) 1 32 0 0 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero] at e
      rw [Nat.mul_zero, Nat.add_zero, Nat.zero_mul,
        nodeAt_congr (m₂ := hashed mm (scratch + 32 * S) L (zeros + 32 * h) 1 32 0) fun i hi => h1 _ (by omega),
        e, zeroAt mm lv.frame, ← up, show nodeAt mm L = subtreeAt leaves h 0 by simpa using lv.roots 0 (by decide)]
    · rw [h1 a hp, hashed_outside (by omega)]
  · -- A wider level: its pairs, then an odd last node against the zero tree.
    have w2 : 2 ≤ W := by
      by_cases hw : W ≤ 1
      · rw [if_pos hw] at v; exact absurd v (by decide)
      · omega
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _
      (eval_div (eval_var (x := 8) lv.widthV) (eval_lit 2) (by omega) (by decide) (by decide))) ?_
    obtain ⟨mm1, r1, h1⟩ := hash_call (env := assign env 11 (UInt64.ofNat (W / 2))) (name := "ssz_hash_pairs")
      (ls := 64) (rs := 64) okP rfl rfl rfl
      (pre.runPre lv.frame (by omega)
        (fun p hp => ⟨by
          have := readLevel _ (Nat.le_refl _) (2 * p) (by omega)
          rwa [show L + 32 * (2 * p) = L + 64 * p by omega] at this, by
          have := readLevel _ (Nat.le_refl _) (2 * p + 1) (by omega)
          rwa [show L + 32 * (2 * p + 1) = L + 32 + 64 * p by omega] at this⟩)
        (by omega)) kernels room
      (eval_five (eval_var (x := 10) lv.dstV) (eval_var (x := 7) lv.levelV)
        (eval_add (eval_var (x := 7) lv.levelV) (eval_lit 32))
        (eval_var assign_eq) (eval_var (x := 5) lv.ctxV))
    -- The parents of the level's pairs.
    have pairs : ∀ j < W / 2, nodeAt mm1 (scratch + 32 * S + 32 * j) = subtreeAt leaves (h + 1) (j * 2 ^ (h + 1)) := by
      intro j hj
      rw [nodeAt_congr (m₂ := hashed mm (scratch + 32 * S) L (L + 32) (W / 2) 64 64) fun i hi => h1 _ (by omega),
        nodeAt_hashed _ _ _ _ _ _ _ _ hj, ← parent_pair, show L + 64 * j = L + 32 * (2 * j) by omega,
        show L + 32 + 64 * j = L + 32 * (2 * j + 1) by omega, lv.roots _ (by omega), lv.roots _ (by omega)]
    have frame1 : ∀ a, ¬ (scratch ≤ a ∧ a < scratch + 32 * (count + depth)) → ¬ (pad ≤ a ∧ a < pad + 1536) →
        mm1 a = mem a := fun a ha hp => by
      rw [h1 a hp, hashed_outside (by omega)]; exact lv.frame a ha hp
    refine Ends.step r1 (Ends.step
      (Runs.set _ _ _ _ _ _ _ _ (eval_or (eval_var (x := 12) lv.status) (eval_var assign_eq))) ?_)
    refine Ends.cons (Q := fun e' mm' => (∀ y, y ≠ 11 → y ≠ 12 → y ≠ 13 → e' y = env y) ∧ e' 12 = 0 ∧
        (∀ j < (W + 1) / 2, nodeAt mm' (scratch + 32 * S + 32 * j) = subtreeAt leaves (h + 1) (j * 2 ^ (h + 1))) ∧
        (∀ a, ¬ (scratch + 32 * S ≤ a ∧ a < scratch + 32 * S + 32 * ((W + 1) / 2)) →
          ¬ (pad ≤ a ∧ a < pad + 1536) → mm' a = mm a))
      (Ends.when _ (eval_ne (eval_mod (eval_var (x := 8) lv.widthV) (eval_lit 2) (by omega) (by decide) (by decide))
        (eval_lit 0)) (fun v => ?_) (fun v => ?_)) ?_
    · -- An odd level: its last node against the zero tree.
      have odd : W % 2 = 1 := by
        have ne := ite_ne_zero v
        have hne : W % 2 ≠ 0 := fun h0 =>
          ne ((ofNat_inj (show W % 2 < 2 ^ 64 by omega) (show 0 < 2 ^ 64 by decide)).mpr h0)
        omega
      obtain ⟨mm2, r2, h2⟩ := hash_call (name := "ssz_hash_fixed") (ls := 32) (rs := 0)
        (env := assign (assign (assign env 11 (UInt64.ofNat (W / 2))) 13 0) 12 (0 ||| 0)) okF rfl rfl rfl
        (pre.runPre frame1 (by omega)
          (fun p hp => ⟨by
            have := readLevel (scratch + 32 * S + 32 * (W / 2)) (by omega) (W - 1) (by omega)
            rwa [show L + 32 * (W - 1) + 32 * p = L + 32 * (W - 1) by omega], readZero _ p⟩) (by omega))
        kernels room
        (eval_five (eval_add (eval_var (x := 10) lv.dstV)
            (eval_mul (eval_lit 32) (eval_var (x := 11) (v := UInt64.ofNat (W / 2)) rfl)))
          (eval_add (eval_var (x := 7) lv.levelV)
            (eval_mul (eval_lit 32) (eval_sub (eval_var (x := 8) lv.widthV) (eval_lit 1) (by omega))))
          (eval_add (eval_var (x := 6) lv.zerosV) (eval_mul (eval_lit 32) (eval_var (x := 9) lv.heightV))) (eval_lit 1)
          (eval_var (x := 5) lv.ctxV))
      refine Ends.step r2 (Ends.of_runs (Runs.set _ _ _ _ _ _ _ _ (eval_or (eval_var (x := 12) (v := 0) rfl)
        (eval_var assign_eq))) ⟨fun y a b c => by simp only [assign, if_neg a, if_neg b, if_neg c], rfl,
          fun j hj => ?_, fun a ha hp => ?_⟩)
      · by_cases last : j < W / 2
        · rw [nodeAt_congr (m₂ := mm1) fun i hi => by rw [h2 _ (by omega), hashed_outside (by omega)], pairs j last]
        · have jw : j = W / 2 := by omega
          subst jw
          have up := parent_last leaves h W odd (by rw [size]; exact lv.covers)
          have e := nodeAt_hashed mm1 (scratch + 32 * S + 32 * (W / 2)) (L + 32 * (W - 1)) (zeros + 32 * h) 1 32 0 0
            (by decide)
          simp only [Nat.mul_zero, Nat.add_zero] at e
          rw [nodeAt_congr (m₂ := hashed mm1 (scratch + 32 * S + 32 * (W / 2)) (L + 32 * (W - 1)) (zeros + 32 * h) 1 32 0)
            fun i hi => h2 _ (by omega), e, zeroAt mm1 frame1, ← up,
            nodeAt_congr (m₂ := mm) fun i hi => by rw [h1 _ (by omega), hashed_outside (by omega)],
            lv.roots _ (by omega)]
      · rw [h2 a hp, hashed_outside (by omega), h1 a hp, hashed_outside (by omega)]
    · -- An even level: the pairs are all of it.
      have even : W % 2 = 0 := by
        have := (ofNat_inj (show W % 2 < 2 ^ 64 by omega) (show 0 < 2 ^ 64 by decide)).mp (ite_eq_zero v)
        omega
      exact ⟨fun y a b c => by simp only [assign, if_neg a, if_neg b, if_neg c], rfl,
        fun j hj => pairs j (by omega), fun a ha hp => by rw [h1 a hp, hashed_outside (by omega)]⟩
    · -- The next level's width.
      rintro e' mm' ⟨fr, st, roots, mf⟩
      exact Ends.of_runs (Runs.set _ _ _ _ _ _ _ _ (eval_div (eval_add (eval_var
        ((fr 8 (by decide) (by decide) (by decide)).trans lv.widthV)) (eval_lit 1)) (eval_lit 2) (by omega) (by decide)
        (by decide))) ⟨fun y a b c d => by rw [assign_ne a]; exact fr y b c d, st, assign_eq, roots, mf⟩
  · -- The level moves up: it lies where the next level went, which moves past it.
    rintro e' mm' ⟨fr, st, wv, roots, mf⟩
    have dv := (fr 10 (by decide) (by decide) (by decide) (by decide)).trans lv.dstV
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_var dv)) ?_
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_add (eval_var ((assign_ne (by decide : (10 : Nat) ≠ 7)).trans dv))
      (eval_mul (eval_lit 32) (eval_var ((assign_ne (by decide : (8 : Nat) ≠ 7)).trans wv))))) ?_
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_add (eval_var ((assign_ne (by decide : (9 : Nat) ≠ 10)).trans
      ((assign_ne (by decide : (9 : Nat) ≠ 7)).trans ((fr 9 (by decide) (by decide) (by decide) (by decide)).trans
        lv.heightV)))) (eval_lit 1))) ?_
    have up := covers_up count h W lv.covers lv.tight
    refine Ends.nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, by omega, by omega, Or.inr ⟨by omega, by omega⟩,
      roots, up.1, up.2, fun a ha hp => ?_⟩
    · show e' 2 = _; rw [fr 2 (by decide) (by decide) (by decide) (by decide)]; exact lv.depthV
    · show e' 3 = _; rw [fr 3 (by decide) (by decide) (by decide) (by decide)]; exact lv.outV
    · show e' 5 = _; rw [fr 5 (by decide) (by decide) (by decide) (by decide)]; exact lv.ctxV
    · show e' 6 = _; rw [fr 6 (by decide) (by decide) (by decide) (by decide)]; exact lv.zerosV
    · exact st
    · rfl
    · exact wv
    · exact assign_eq
    · show UInt64.ofNat (scratch + 32 * S + 32 * ((W + 1) / 2)) = _
      congr 1; omega
    · rw [mf a (by omega) hp]; exact lv.frame a ha hp

/-! ## The whole tree -/

set_option maxHeartbeats 1000000 in
/--
The tree driver ends with the root of the tree over its nodes at the output, and a zero result.

Memory changes only in the scratch buffer, the padding area, and the output.
-/
theorem merkleize_ends {m : Module} {w : World} {sp : Nat} {mem : Memory}
    {nodes count depth out scratch ctx table zeros pad : Nat} {mask : UInt64}
    (okP : HashCalls m w .pairs) (okF : HashCalls m w .fixed)
    (pre : TreePre w mem nodes count depth out scratch ctx table zeros pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + hashStack ≤ sp) :
    Ends m w sp (entryEnv [UInt64.ofNat nodes, UInt64.ofNat count, UInt64.ofNat depth, UInt64.ofNat out,
      UInt64.ofNat scratch, UInt64.ofNat ctx]) mem merkleize.body fun env mem' =>
        env 12 = 0 ∧ nodeAt mem' out = subtreeAt (nodesFrom (bytesAt mem nodes (32 * count)) 0 count) depth 0 ∧
        ∀ a, ¬ (scratch ≤ a ∧ a < scratch + 32 * (count + depth)) → ¬ (pad ≤ a ∧ a < pad + 1536) →
          ¬ (out ≤ a ∧ a < out + 32) → mem' a = mem a := by
  have bs := access_bound pre.scratchAccess
  have bn := access_bound pre.nodesAccess
  have bz := access_bound pre.zerosAccess
  have bx := access_bound pre.ctxAccess
  have bo := access_bound pre.outAccess
  have hz : zeroHeights = 64 := rfl
  have deep := pre.deep
  have so := pre.scratchOut
  have on := pre.outNodes
  have oz := pre.outZeros
  simp only [Apart] at so on oz
  -- The leaves are the nodes read from memory at the start.
  have leaf : ∀ j < count, nodeAt mem (nodes + 32 * j) =
      subtreeAt (nodesFrom (bytesAt mem nodes (32 * count)) 0 count) 0 (j * 2 ^ 0) := fun j hj => by
    rw [Nat.pow_zero, Nat.mul_one, subtreeAt_leaf, nodesFrom_get?, if_pos hj, Option.getD_some, nodeOf_bytesAt _ _ _ _ hj]
  have size : (nodesFrom (bytesAt mem nodes (32 * count)) 0 count).size = count := nodesFrom_size _ _ _
  generalize nodesFrom (bytesAt mem nodes (32 * count)) 0 count = leaves at leaf size
  simp only [merkleize]
  -- The zero roots' address, and a zero result so far.
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (by
    exact (eval_ld (eval_add (eval_var rfl) (eval_lit 16)) (access_sub pre.ctxAccess (by omega) (by omega))).trans
      (congrArg some pre.zerosAt))) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 0)) ?_
  refine Ends.cons (Ends.ite _ (eval_eq (by exact eval_var rfl) (eval_lit 0) (by omega)
    (by decide)) (fun v => ?_) (fun v => ?_)) fun _ _ h => Ends.nil h
  · -- No nodes: the root is the zero tree of the depth.
    have c0 : count = 0 := by
      by_cases hc : count = 0
      · exact hc
      · rw [if_neg hc] at v; exact absurd rfl v
    subst c0
    exact Ends.of_runs (copy32_runs (fun _ => eval_var (x := 3) (v := UInt64.ofNat out) rfl)
      (fun _ => eval_add (eval_var (x := 6) (v := UInt64.ofNat zeros) rfl)
        (eval_mul (eval_lit 32) (eval_var (x := 2) (v := UInt64.ofNat depth) rfl)))
      pre.outAccess (access_sub pre.zerosAccess (by omega) (by omega)) (by simp only [Apart]; omega))
      ⟨rfl, by rw [nodeAt_copied, nodeAt_zeros pre.zeroRoots depth deep, subtreeAt_past _ _ _ (by omega)],
        fun a _ _ ho => copied_out ho⟩
  · have c0 : count ≠ 0 := by
      intro hc
      rw [if_pos hc] at v; exact absurd v (by decide)
    refine Ends.append (Q := fun e mm => e 3 = UInt64.ofNat out ∧ e 12 = 0 ∧ ∃ L, e 7 = UInt64.ofNat L ∧
        ((L = nodes) ∨ (scratch ≤ L ∧ L + 32 ≤ scratch + 32 * (count + depth))) ∧
        nodeAt mm L = subtreeAt leaves depth 0 ∧
        ∀ a, ¬ (scratch ≤ a ∧ a < scratch + 32 * (count + depth)) → ¬ (pad ≤ a ∧ a < pad + 1536) →
          mm a = mem a)
      ?_ ?_
    · -- The loop, from the nodes themselves at height zero.
      refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_var (x := 0) (v := UInt64.ofNat nodes) rfl)) ?_
      refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_var (x := 1) (v := UInt64.ofNat count) rfl)) ?_
      refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 0)) ?_
      refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_var (x := 4) (v := UInt64.ofNat scratch) rfl)) ?_
      refine Ends.cons (Ends.loop
        (fun e mm => ∃ h W L S, Level mem mm leaves nodes count depth out scratch ctx zeros pad e h W L S)
        (fun e _ => depth - (e 9).toNat)
        ⟨0, count, nodes, 0, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, by omega, by omega,
          Or.inl ⟨rfl, rfl⟩, leaf, by simp, by simp; omega, fun _ _ _ => rfl⟩ ?_ ?_) ?_
      · rintro e mm ⟨h, W, L, S, lv⟩
        have := lv.height
        exact ⟨_, eval_lt (eval_var lv.heightV) (eval_var lv.depthV) (by omega) (by omega)⟩
      · rintro e mm v ⟨h, W, L, S, lv⟩ hv nz
        have hd := lv.height
        have hv := Option.some.inj (hv.symm.trans
          (eval_lt (eval_var lv.heightV) (eval_var lv.depthV) (by omega) (by omega)))
        have below : h < depth := by
          by_cases hb : h < depth
          · exact hb
          · rw [if_neg hb] at hv; exact absurd hv nz
        refine Ends.mono (level_step okP okF pre kernels room size lv below) fun e' mm' lv' =>
          ⟨⟨_, _, _, _, lv'⟩, ?_⟩
        rw [lv'.heightV, lv.heightV, ofNat_toNat (by omega), ofNat_toNat (by omega)]
        omega
      · rintro e mm ⟨⟨h, W, L, S, lv⟩, done⟩
        have hd := lv.height
        have done := Option.some.inj (done.symm.trans
          (eval_lt (eval_var lv.heightV) (eval_var lv.depthV) (by omega) (by omega)))
        have top : h = depth := by
          by_cases hb : h < depth
          · rw [if_pos hb] at done; exact absurd done (by decide)
          · omega
        subst top
        -- At the top, one node is left: the root.
        have fits := pre.fits
        have tight := lv.tight
        have one : W = 1 := by
          have : (W - 1) * 2 ^ h < 1 * 2 ^ h := by rw [Nat.one_mul]; omega
          have := Nat.lt_of_mul_lt_mul_right this
          have := lv.wide
          omega
        subst one
        have used := lv.used
        refine Ends.nil ⟨lv.outV, lv.status, L, lv.levelV, ?_, by simpa using lv.roots 0 (by decide), lv.frame⟩
        rcases lv.place with ⟨rfl, _⟩ | ⟨a, b⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨a, by omega⟩
    · -- The root, copied to the output.
      rintro e mm ⟨ov, st, L, lv7, place, root, frame⟩
      have acc : w.access L 32 = true := by
        rcases place with rfl | ⟨a, b⟩
        · exact access_sub pre.nodesAccess (by omega) (by omega)
        · exact access_sub pre.scratchAccess (by omega) (by omega)
      have apart : Apart (out, 32) (L, 32) := by
        simp only [Apart]
        rcases place with rfl | ⟨a, b⟩ <;> omega
      exact Ends.of_runs (copy32_runs (fun _ => eval_var ov) (fun _ => eval_var lv7) pre.outAccess acc apart)
        ⟨st, by rw [nodeAt_copied, root], fun a ha hp ho => by rw [copied_out ho]; exact frame a ha hp⟩

/-! ## Calls -/

/-- The tree driver's frame holds nineteen words. -/
theorem merkleize_frame : merkleize.frame = 19 := rfl

/--
The stack a call to the tree driver needs below its stack pointer.

The driver's return address and frame take 160 bytes, and a hashing driver's call what it needs.
-/
abbrev treeStack : Nat := 160 + hashStack

/-- What a call to the tree driver does, for every tree meeting its conditions, on a processor running its kernels. -/
def TreeCalls (m : Module) (w : World) : Prop :=
  ∀ (sp : Nat) (mem : Memory) (nodes count depth out scratch ctx table zeros pad : Nat) (mask : UInt64),
    TreePre w mem nodes count depth out scratch ctx table zeros pad mask → KernelsRun w mask →
    w.stackLo + treeStack ≤ sp →
    ∃ mem', Calls m w "ssz_merkleize" sp [UInt64.ofNat nodes, UInt64.ofNat count, UInt64.ofNat depth,
      UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx] mem 0 mem' ∧
      nodeAt mem' out = subtreeAt (nodesFrom (bytesAt mem nodes (32 * count)) 0 count) depth 0 ∧
      ∀ a, ¬ (scratch ≤ a ∧ a < scratch + 32 * (count + depth)) → ¬ (pad ≤ a ∧ a < pad + 1536) →
        ¬ (out ≤ a ∧ a < out + 32) → mem' a = mem a

/-- The tree driver, in a module whose hashing drivers keep their calls, does what its call promises. -/
theorem treeCalls {m : Module} {w : World} (tree : m.fns.lookup "ssz_merkleize" = some merkleize)
    (okP : HashCalls m w .pairs) (okF : HashCalls m w .fixed) : TreeCalls m w := by
  intro sp mem nodes count depth out scratch ctx table zeros pad mask pre kernels room
  have stack : treeStack = 160 + 10392 := rfl
  have hs : hashStack = 10392 := rfl
  -- The body runs below the driver's frame, where a hashing driver still finds the stack it needs.
  obtain ⟨env', mem', run, status, root, frame⟩ := merkleize_ends (sp := sp - 8 - 8 * merkleize.frame) okP okF pre
    kernels (by rw [merkleize_frame]; omega)
  refine ⟨mem', ?_, root, frame⟩
  rw [← status]
  exact Calls.fn tree (by rw [merkleize_frame]; omega) rfl run (eval_var rfl)

/-- The root the tree driver writes is the native tree's root, on a machine whose words hold the buffer's size. -/
theorem treeCalls_native {m : Module} {w : World} (calls : TreeCalls m w) {sp : Nat} {mem : Memory}
    {nodes count depth out scratch ctx table zeros pad : Nat} {mask : UInt64}
    (pre : TreePre w mem nodes count depth out scratch ctx table zeros pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + treeStack ≤ sp) (small : 32 * count < USize.size) :
    ∃ mem', Calls m w "ssz_merkleize" sp [UInt64.ofNat nodes, UInt64.ofNat count, UInt64.ofNat depth,
      UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx] mem 0 mem' ∧
      nodeAt mem' out = (merkleizeDepth (bytesAt mem nodes (32 * count)) count depth).data ∧
      ∀ a, ¬ (scratch ≤ a ∧ a < scratch + 32 * (count + depth)) → ¬ (pad ≤ a ∧ a < pad + 1536) →
        ¬ (out ≤ a ∧ a < out + 32) → mem' a = mem a := by
  obtain ⟨mem', call, root, frame⟩ := calls sp mem nodes count depth out scratch ctx table zeros pad mask pre kernels
    room
  -- The buffer read from memory holds exactly the nodes.
  have size : (bytesAt mem nodes (32 * count)).size = 32 * count := by simp [bytesAt, ByteArray.size]
  refine ⟨mem', call, ?_, frame⟩
  rw [root, (merkleizeDepth_spec _ count depth pre.fits (by omega) (by omega)).2]

/-! ## Hashing, packaged -/

/--
The hashing drivers and the tree driver of a module keep their calls on a processor.

Proofs of other drivers take this as a hypothesis, and a module's shape discharges it.
-/
structure HashingOk (m : Module) (w : World) : Prop where
  /-- Hashing adjacent pairs of one level. -/
  pairs : HashCalls m w .pairs
  /-- Hashing two columns pairwise. -/
  columns : HashCalls m w .columns
  /-- Hashing a column against one fixed node. -/
  fixed : HashCalls m w .fixed
  /-- The root of a perfect tree over nodes. -/
  merkleize : TreeCalls m w

/-- A module holding the hashing drivers, their kernels, and the tree driver keeps every hashing call. -/
theorem hashingOk {m : Module} (w : World) (mod : HashModule m)
    (tree : m.fns.lookup "ssz_merkleize" = some merkleize) : HashingOk m w :=
  ⟨hashCalls w mod .pairs, hashCalls w mod .columns, hashCalls w mod .fixed,
    treeCalls tree (hashCalls w mod .pairs) (hashCalls w mod .fixed)⟩

/-! ## The hashing part of a module -/

/-- The hashing drivers and the tree driver, under their exported names. -/
def hashFns : List (String × Fn) :=
  [("ssz_hash_pairs", hashRun .pairs), ("ssz_hash_columns", hashRun .columns), ("ssz_hash_fixed", hashRun .fixed),
    ("ssz_merkleize", merkleize)]

/-- The hashing kernels, under their exported names, each with the meaning its theorem gives. -/
noncomputable def hashExterns : List (String × Extern) :=
  [("ssz_sha256_avx512_pairs", hashExtern (Kernel.Avx512.program 64 64) 16 64 64),
    ("ssz_sha256_avx512_columns", hashExtern (Kernel.Avx512.program 32 32) 16 32 32),
    ("ssz_sha256_avx512_fixed", hashExtern (Kernel.Avx512.program 32 0) 16 32 0),
    ("ssz_sha256_shani_pairs", hashExtern (Kernel.ShaNi.program 64 64) 1 64 64),
    ("ssz_sha256_shani_columns", hashExtern (Kernel.ShaNi.program 32 32) 1 32 32),
    ("ssz_sha256_shani_fixed", hashExtern (Kernel.ShaNi.program 32 0) 1 32 0),
    ("ssz_sha256_shani_dual_pairs", hashExtern (Kernel.ShaNiDual.program 64 64) 2 64 64),
    ("ssz_sha256_shani_dual_columns", hashExtern (Kernel.ShaNiDual.program 32 32) 2 32 32),
    ("ssz_sha256_shani_dual_fixed", hashExtern (Kernel.ShaNiDual.program 32 0) 2 32 0),
    ("ssz_sha256_avx512x2_pairs", hashFrameExtern (Kernel.Avx512x2.program 64 64) 32 64 64 Kernel.Avx512x2.frame),
    ("ssz_sha256_avx512x2_columns", hashFrameExtern (Kernel.Avx512x2.program 32 32) 32 32 32 Kernel.Avx512x2.frame),
    ("ssz_sha256_avx512x2_fixed", hashFrameExtern (Kernel.Avx512x2.program 32 0) 32 32 0 Kernel.Avx512x2.frame),
    ("ssz_sha256_avx2_pairs", hashFrameExtern (Kernel.Avx2.program 64 64) 8 64 64 Kernel.Avx2.frame),
    ("ssz_sha256_avx2_columns", hashFrameExtern (Kernel.Avx2.program 32 32) 8 32 32 Kernel.Avx2.frame),
    ("ssz_sha256_avx2_fixed", hashFrameExtern (Kernel.Avx2.program 32 0) 8 32 0 Kernel.Avx2.frame),
    ("ssz_sha256_baseline_pairs", hashFrameExtern (Kernel.Baseline.program 64 64) 4 64 64 Kernel.Baseline.frame),
    ("ssz_sha256_baseline_columns", hashFrameExtern (Kernel.Baseline.program 32 32) 4 32 32 Kernel.Baseline.frame),
    ("ssz_sha256_baseline_fixed", hashFrameExtern (Kernel.Baseline.program 32 0) 4 32 0 Kernel.Baseline.frame)]

/-- Looking a name up in two lists joined is looking it up in the first, then in the second. -/
theorem lookup_append {β : Type} (l₁ l₂ : List (String × β)) (a : String) :
    (l₁ ++ l₂).lookup a = (l₁.lookup a).or (l₂.lookup a) := by
  induction l₁ with
  | nil => rfl
  | cons p rest ih =>
    -- The head either matches, and is found in both, or the search goes on in both.
    simp only [List.cons_append, List.lookup]
    split <;> simp_all

/--
A module whose functions and routines start with the hashing ones keeps every hashing call.

Its other functions must not take a kernel's name, which would hide the kernel.
-/
theorem hashingOk_append (w : World) (fns : List (String × Fn)) (ext : List (String × Extern))
    (fresh : ∀ layout : Layout, ∀ family ∈ ["avx512x2", "avx512", "shani", "shani_dual", "avx2", "baseline"],
      fns.lookup (kernelName family layout.info.1) = none) :
    HashingOk ⟨hashFns ++ fns, hashExterns ++ ext⟩ w := by
  -- Every name the drivers call is found in the hashing lists, before anything else.
  refine hashingOk w
    ⟨fun layout => ?_, fun layout => ⟨?_, ?_⟩, fun layout => ⟨?_, ?_⟩, fun layout => ⟨?_, ?_⟩,
      fun layout => ⟨?_, ?_⟩, fun layout => ⟨?_, ?_⟩, fun layout => ⟨?_, ?_⟩⟩
    (by rw [lookup_append]; rfl)
  · rw [lookup_append]; cases layout <;> rfl
  · rw [lookup_append, fresh layout "avx512x2" (by simp)]; cases layout <;> rfl
  · rw [lookup_append]; cases layout <;> rfl
  · rw [lookup_append, fresh layout "avx512" (by simp)]; cases layout <;> rfl
  · rw [lookup_append]; cases layout <;> rfl
  · rw [lookup_append, fresh layout "shani" (by simp)]; cases layout <;> rfl
  · rw [lookup_append]; cases layout <;> rfl
  · rw [lookup_append, fresh layout "shani_dual" (by simp)]; cases layout <;> rfl
  · rw [lookup_append]; cases layout <;> rfl
  · rw [lookup_append, fresh layout "avx2" (by simp)]; cases layout <;> rfl
  · rw [lookup_append]; cases layout <;> rfl
  · rw [lookup_append, fresh layout "baseline" (by simp)]; cases layout <;> rfl
  · rw [lookup_append]; cases layout <;> rfl

end Ssz.Native.Driver
