import SszNative.Driver.TreeStore
import SszNative.Proofs.Driver.Tree

/-!
What a tree kept in memory holds, and the facts its three drivers share.

Node j of the level at height h, in a tree of height K, is node 2^(K-h) + j of the heap.
It holds the root of the specification's subtree over the leaves j 2^h onward.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir

/-! ## Trees in memory -/

/-- Every node of a tree of height K, laid out in heap order, holds the root of the subtree under it. -/
def TreeAt (mem : Memory) (tree K : Nat) (leaves : Array Bytes) : Prop :=
  ∀ h ≤ K, ∀ j < 2 ^ (K - h), nodeAt mem (tree + 32 * (2 ^ (K - h) + j)) = subtreeAt leaves h (j * 2 ^ h)

/--
A tree of a power-of-two width over leaves sits in memory.

The leaves fit the width, and every node holds the root of the subtree under it.
-/
def TreeOk (mem : Memory) (tree W : Nat) (leaves : Array Bytes) : Prop :=
  ∃ K, W = 2 ^ K ∧ leaves.size ≤ W ∧ TreeAt mem tree K leaves

/-- The top node of a tree is the root of the whole tree. -/
theorem TreeAt.top {mem : Memory} {tree K : Nat} {leaves : Array Bytes} (ok : TreeAt mem tree K leaves) :
    nodeAt mem (tree + 32) = subtreeAt leaves K 0 := by
  have := ok K (Nat.le_refl _) 0 (by simp)
  simpa using this

/-- A tree's nodes read only the tree's own bytes. -/
theorem TreeAt.congr {mem mem' : Memory} {tree K : Nat} {leaves : Array Bytes} (ok : TreeAt mem tree K leaves)
    (same : ∀ a, tree + 32 ≤ a → a < tree + 32 * 2 ^ (K + 1) → mem' a = mem a) : TreeAt mem' tree K leaves := by
  intro h hh j hj
  have up : 2 ^ (K - h) + j + 1 ≤ 2 ^ (K + 1) := by
    have : 2 ^ (K - h) ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ]; omega
  have one : 1 ≤ 2 ^ (K - h) := Nat.one_le_two_pow
  rw [nodeAt_congr (m₂ := mem) fun i hi => same _ (by omega) (by omega)]
  exact ok h hh j hj

/-- One height up from the leftmost subtree: a tree whose leaves all sit under it climbs against a zero tree. -/
theorem climb_step (leaves : Array Bytes) (h : Nat) (narrow : leaves.size ≤ 2 ^ h) :
    combine (subtreeAt leaves h 0) (zeroSubtree h) = subtreeAt leaves (h + 1) 0 := by
  have := parent_last leaves h 1 rfl (by simpa using narrow)
  simpa using this

/-! ## Expressions -/

/-- A right shift by one of a converted number is the conversion of its half. -/
theorem eval_shr1' {w : World} {env : Env} {mem : Memory} {a : Expr} {p : Nat}
    (ha : eval w env mem a = some (UInt64.ofNat p)) (bp : p < 2 ^ 64) :
    eval w env mem (.shr a 1) = some (UInt64.ofNat (p / 2)) := by
  simp only [eval, ha, Option.bind_eq_bind, Option.bind, show (1 : Nat) < 64 from by decide, ite_true]
  show some _ = some _
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, ofNat_toNat bp]
  simp only [Nat.shiftRight_eq_div_pow]
  rw [ofNat_toNat (n := p / 2) (by omega)]
  rfl

/-! ## The context -/

/-- The context words, the tables they point to, and the padding area, as every tree driver needs them. -/
structure StoreCtx (w : World) (mem : Memory) (ctx table zeros pad : Nat) (mask : UInt64) : Prop where
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
  /-- The padding area lies in memory the program may use. -/
  padAccess : w.access pad 1536 = true
  /-- It misses the context. -/
  padCtx : Apart (pad, 1536) (ctx, 32)
  /-- It misses the constant table. -/
  padTable : Apart (pad, 1536) (table, Kernel.tableSize)
  /-- It misses the zero-tree roots. -/
  padZeros : Apart (pad, 1536) (zeros, 32 * (zeroHeights + 1))

/-- The context holds in any memory that keeps its words and both tables. -/
theorem StoreCtx.congr {w : World} {mem mm : Memory} {ctx table zeros pad : Nat} {mask : UInt64}
    (c : StoreCtx w mem ctx table zeros pad mask)
    (same : ∀ a, (ctx ≤ a ∧ a < ctx + 32) ∨ (table ≤ a ∧ a < table + Kernel.tableSize) ∨
      (zeros ≤ a ∧ a < zeros + 32 * (zeroHeights + 1)) → mm a = mem a) :
    StoreCtx w mm ctx table zeros pad mask := by
  have word : ∀ k, k + 8 ≤ 32 → readLE mm (ctx + k) 8 = readLE mem (ctx + k) 8 := fun k hk =>
    readLE_congr _ _ _ _ fun i hi => same _ (Or.inl (by omega))
  refine ⟨c.ctxAccess, ?_, ?_, ?_, ?_, fun i hi => ?_, c.tableAccess, fun i hi => ?_, c.zerosAccess, c.padAccess,
    c.padCtx, c.padTable, c.padZeros⟩
  · rw [show ctx = ctx + 0 from rfl, word 0 (by omega)]; exact c.maskAt
  · rw [word 8 (by omega)]; exact c.tableAt
  · rw [word 16 (by omega)]; exact c.zerosAt
  · rw [word 24 (by omega)]; exact c.padAt
  · rw [same _ (Or.inr (Or.inl (by omega)))]; exact c.tableBytes i hi
  · rw [same _ (Or.inr (Or.inr (by omega)))]; exact c.zeroRoots i hi

/-- A node a hashing call reads: inside one of two regions of memory, or a zero-tree root. -/
def Src (lo len lo' len' zeros a : Nat) : Prop :=
  (lo ≤ a ∧ a + 32 ≤ lo + len) ∨ (lo' ≤ a ∧ a + 32 ≤ lo' + len') ∨
    (zeros ≤ a ∧ a + 32 ≤ zeros + 32 * (zeroHeights + 1))

/--
A run of pairs read from two regions, or from the zero roots, into digests apart from all of them meets a hashing
driver's conditions.
-/
theorem StoreCtx.runPre {w : World} {mem : Memory} {ctx table zeros pad : Nat} {mask : UInt64}
    (c : StoreCtx w mem ctx table zeros pad mask) {lo len lo' len' ls rs out left right n : Nat}
    (region : w.access lo len = true) (region' : w.access lo' len' = true) (outAccess : w.access out (32 * n) = true)
    (src : ∀ p < n, Src lo len lo' len' zeros (left + ls * p) ∧ Src lo len lo' len' zeros (right + rs * p))
    (reach : left + ls * n ≤ 2 ^ 63 ∧ right + rs * n ≤ 2 ^ 63)
    (outIn : Apart (out, 32 * n) (lo, len)) (outIn' : Apart (out, 32 * n) (lo', len'))
    (outZeros : Apart (out, 32 * n) (zeros, 32 * (zeroHeights + 1)))
    (outTable : Apart (out, 32 * n) (table, Kernel.tableSize)) (outCtx : Apart (ctx, 32) (out, 32 * n))
    (padOut : Apart (pad, 1536) (out, 32 * n)) (padIn : Apart (pad, 1536) (lo, len))
    (padIn' : Apart (pad, 1536) (lo', len')) :
    RunPre w mem ls rs out left right n ctx table pad mask := by
  have pz := c.padZeros
  have bz := access_bound c.zerosAccess
  have hz : zeroHeights = 64 := rfl
  simp only [Apart] at outIn outIn' outZeros padIn padIn' pz
  -- Each node read lies in memory the program may use, apart from the digests and the padding area.
  have access : ∀ a, Src lo len lo' len' zeros a → w.access a 32 = true := by
    intro a ha
    rcases ha with h | h | h
    · exact access_sub region (by omega) (by omega)
    · exact access_sub region' (by omega) (by omega)
    · exact access_sub c.zerosAccess (by omega) (by omega)
  have apartOut : ∀ a, Src lo len lo' len' zeros a → Apart (out, 32 * n) (a, 32) := by
    intro a ha
    simp only [Apart]
    rcases ha with h | h | h <;> omega
  have apartPad : ∀ a, Src lo len lo' len' zeros a → Apart (pad, 1536) (a, 32) := by
    intro a ha
    simp only [Apart]
    rcases ha with h | h | h <;> omega
  exact ⟨c.ctxAccess, c.maskAt, c.tableAt, c.padAt, ⟨c.tableBytes, outAccess, c.tableAccess,
    fun p hp => ⟨access _ (src p hp).1, access _ (src p hp).2⟩, reach, outTable,
    fun p hp => ⟨apartOut _ (src p hp).1, apartOut _ (src p hp).2⟩⟩, c.padAccess, padOut, c.padTable,
    fun p hp => ⟨apartPad _ (src p hp).1, apartPad _ (src p hp).2⟩, outCtx⟩

/-- The zero tree of a height, as memory keeping the zero roots holds it. -/
theorem StoreCtx.zeroAt {w : World} {mem : Memory} {ctx table zeros pad : Nat} {mask : UInt64}
    (c : StoreCtx w mem ctx table zeros pad mask) (h : Nat) (hh : h ≤ zeroHeights) :
    nodeAt mem (zeros + 32 * h) = zeroSubtree h :=
  nodeAt_zeros c.zeroRoots h hh

end EthLib.Consensus.Ssz.Native.Driver
