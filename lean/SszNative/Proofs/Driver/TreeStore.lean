import SszNative.Proofs.Driver.TreeStore.Build
import SszNative.Proofs.Driver.TreeStore.Update
import SszNative.Proofs.Driver.TreeStore.Root

/-!
The tree store's three drivers, as calls, against the specification's trees.

Building leaves a whole tree in memory over the leaves.
Updating, after some leaves are rewritten in place, leaves the whole tree over the new leaves.
The root is the specification's root of the leaves at the declared depth, with the word mixed in if one is given.
Each takes the module's hashing drivers as given, through the hashing package of a module.
-/

namespace Ssz.Native.Driver

open Ssz Ssz.Native.Asm Ssz.Native.Ir

/-- The build driver's frame holds twenty-one words. -/
theorem treeBuild_frame : TreeBuild.fn.frame = 21 := rfl

/-- The update driver's frame holds twenty-five words. -/
theorem treeUpdate_frame : TreeUpdate.fn.frame = 25 := rfl

/-- The root driver's frame holds seventeen words. -/
theorem treeRoot_frame : TreeRoot.fn.frame = 17 := rfl

/--
The stack a call to a tree store driver needs below its stack pointer.

The driver's return address and frame take at most 208 bytes, and a hashing driver's call what it needs.
-/
abbrev storeStack : Nat := 208 + hashStack

/-- A tree's leaves read only the leaves under it, as nodes of height zero. -/
theorem subtreeAt_congr_leaves (a b : Array Bytes) (g s : Nat)
    (same : ∀ i < 2 ^ g, subtreeAt a 0 (s + i) = subtreeAt b 0 (s + i)) : subtreeAt a g s = subtreeAt b g s := by
  induction g generalizing s with
  | zero => simpa using same 0 (by decide)
  | succ g ih =>
    -- Each half reads its own half of the leaves.
    rw [subtreeAt_split, subtreeAt_split]
    congr 1
    · exact ih s fun i lt => same i (by rw [Nat.pow_succ]; omega)
    · exact ih _ fun i lt => by
        have := same (2 ^ g + i) (by rw [Nat.pow_succ]; omega)
        rwa [← Nat.add_assoc] at this

/-! ## Build -/

/--
A call to the build driver leaves the whole tree over the leaves in memory, and returns zero.

The tree's width is the count rounded up to a power of two, and memory changes only in the tree and the padding
area.
-/
theorem treeBuild_calls {m : Module} {w : World} (hashing : HashingOk m w)
    (fn : m.fns.lookup "ssz_tree_build" = some TreeBuild.fn) {sp : Nat} {mem : Memory}
    {tree leaves count K ctx table zeros pad : Nat} {mask : UInt64}
    (pre : BuildPre w mem tree leaves count K ctx table zeros pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + storeStack ≤ sp) :
    ∃ mem', Calls m w "ssz_tree_build" sp [UInt64.ofNat tree, UInt64.ofNat leaves, UInt64.ofNat count,
      UInt64.ofNat ctx] mem 0 mem' ∧
      TreeOk mem' tree (2 ^ K) (nodesFrom (bytesAt mem leaves (32 * count)) 0 count) ∧
      BuildFrame mem mem' tree K pad := by
  have hs : storeStack = 10600 := rfl
  have hh : hashStack = 10392 := rfl
  obtain ⟨env', mem', run, status, tree', frame⟩ := build_ends (sp := sp - 8 - 8 * TreeBuild.fn.frame)
    hashing.pairs pre kernels (by rw [treeBuild_frame]; omega)
  refine ⟨mem', ?_, ⟨K, rfl, by rw [nodesFrom_size]; exact pre.covers, tree'⟩, frame⟩
  rw [← status]
  exact Calls.fn fn (by rw [treeBuild_frame]; omega) rfl run (eval_var rfl)

/-! ## Update -/

/--
A call to the update driver, after some leaves are rewritten in place, leaves the whole tree over the new leaves.

Before the call the tree was whole over the old leaves, and only the leaves at the given indices were rewritten.
The indices are sorted, distinct, and below the width; memory changes only in the tree's inner nodes' bytes, the
scratch buffer, and the padding area.
-/
theorem treeUpdate_calls {m : Module} {w : World} (hashing : HashingOk m w)
    (fn : m.fns.lookup "ssz_tree_update" = some TreeUpdate.fn) {sp : Nat} {mem mem0 : Memory}
    {tree K indices c scratch ctx table zeros pad : Nat} {mask : UInt64}
    (pre : UpdatePre w mem tree K indices c scratch ctx table zeros pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + storeStack ≤ sp)
    {old new : Array Bytes} {idx : Nat → Nat} (idxAt : ∀ i < c, slotWord mem indices i = idx i)
    (inside : ∀ x < c, idx x < 2 ^ K) (sorted : ∀ i j, i < j → j < c → idx i < idx j)
    (fits : new.size ≤ 2 ^ K) (was : TreeAt mem0 tree K old)
    (inner : ∀ a, tree + 32 ≤ a → a < tree + 32 * 2 ^ K → mem a = mem0 a)
    (leavesAt : ∀ j < 2 ^ K, nodeAt mem (tree + 32 * (2 ^ K + j)) = subtreeAt new 0 j)
    (kept : ∀ j < 2 ^ K, (∀ x < c, idx x ≠ j) → subtreeAt new 0 j = subtreeAt old 0 j) :
    ∃ mem', Calls m w "ssz_tree_update" sp [UInt64.ofNat tree, UInt64.ofNat (2 ^ K), UInt64.ofNat indices,
      UInt64.ofNat c, UInt64.ofNat scratch, UInt64.ofNat ctx] mem 0 mem' ∧ TreeOk mem' tree (2 ^ K) new ∧
      UpdateFrame mem mem' tree K c scratch pad := by
  have hs : storeStack = 10600 := rfl
  have hh : hashStack = 10392 := rfl
  -- Before the call, the leaves and every clean node are right over the new leaves.
  have start : UpTo mem tree K new idx c 0 := by
    intro g hg j hj cond
    have gb : 2 ^ (K - g) ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) (by omega)
    by_cases g0 : g = 0
    · subst g0
      simpa using leavesAt j (by simpa using hj)
    · have clean : ¬ Dirty idx c g j := by
        rcases cond with le | cl
        · omega
        · exact cl
      have half : 2 ^ (K - g) * 2 ≤ 2 ^ K := by
        rw [← Nat.pow_succ]; exact Nat.pow_le_pow_right (by decide) (by omega)
      rw [nodeAt_congr (m₂ := mem0) fun r hr => inner _ (by omega) (by omega), was g hg j hj]
      refine subtreeAt_congr_leaves _ _ _ _ fun i hi => (kept _ ?_ fun x hx eq => clean ⟨x, hx, ?_⟩).symm
      · have : (j + 1) * 2 ^ g ≤ 2 ^ (K - g) * 2 ^ g := Nat.mul_le_mul_right _ hj
        rw [← Nat.pow_add, Nat.sub_add_cancel hg, Nat.succ_mul] at this
        omega
      · rw [eq, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos g), Nat.div_eq_of_lt hi, Nat.zero_add]
  obtain ⟨env', mem', run, status, tree', frame⟩ := update_ends (sp := sp - 8 - 8 * TreeUpdate.fn.frame)
    hashing.pairs pre kernels (by rw [treeUpdate_frame]; omega) idxAt inside sorted start
  refine ⟨mem', ?_, ⟨K, rfl, fits, tree'⟩, frame⟩
  rw [← status]
  exact Calls.fn fn (by rw [treeUpdate_frame]; omega) rfl run (eval_var rfl)

/-! ## Root -/

/--
A call to the root driver writes the specification's root of the leaves at the depth, with the word mixed in if one
is given, and returns zero.

The word is the 32 bytes at the mixin address, or none for address zero.
Memory changes only in the tree's first 32 bytes, the output, and the padding area.
-/
theorem treeRoot_calls {m : Module} {w : World} (hashing : HashingOk m w)
    (fn : m.fns.lookup "ssz_tree_root" = some TreeRoot.fn) {sp : Nat} {mem : Memory}
    {tree K depth mixin out ctx table zeros pad : Nat} {mask : UInt64}
    (pre : RootPre w mem tree K depth mixin out ctx table zeros pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + storeStack ≤ sp) {leaves : Array Bytes}
    (ok : TreeOk mem tree (2 ^ K) leaves) :
    ∃ mem', Calls m w "ssz_tree_root" sp [UInt64.ofNat tree, UInt64.ofNat (2 ^ K), UInt64.ofNat depth,
      UInt64.ofNat mixin, UInt64.ofNat out, UInt64.ofNat ctx] mem 0 mem' ∧
      nodeAt mem' out = withMixin (subtreeAt leaves depth 0) (if mixin = 0 then none else some (nodeAt mem mixin)) ∧
      RootFrame mem mem' tree out pad := by
  have hs : storeStack = 10600 := rfl
  have hh : hashStack = 10392 := rfl
  obtain ⟨K', hK, fits, tree'⟩ := ok
  have kk : K' = K := by
    rcases Nat.lt_trichotomy K' K with lt | e | gt
    · have := Nat.pow_lt_pow_right (by decide : 1 < 2) lt; omega
    · exact e
    · have := Nat.pow_lt_pow_right (by decide : 1 < 2) gt; omega
  subst kk
  obtain ⟨env', mem', run, status, root, frame⟩ := root_ends (sp := sp - 8 - 8 * TreeRoot.fn.frame)
    hashing.fixed pre kernels (by rw [treeRoot_frame]; omega) tree'.top fits
  refine ⟨mem', ?_, root, frame⟩
  rw [← status]
  exact Calls.fn fn (by rw [treeRoot_frame]; omega) rfl run (eval_var rfl)

/--
The root without a word mixed in is the specification's bounded merkleization of the leaves at that capacity.

With a word, it is that root mixed with the word, as a length, a selector, or an active-fields word is mixed in.
-/
theorem treeRoot_spec (leaves : Array Bytes) (depth : Nat) (fits : leaves.size ≤ 2 ^ depth) (word : Option Bytes) :
    merkleizeBoundedUnchecked leaves (some (2 ^ depth)) = .ok (subtreeAt leaves depth 0) ∧
      withMixin (subtreeAt leaves depth 0) word =
        match word with
        | none => subtreeAt leaves depth 0
        | some wd => mixIn (subtreeAt leaves depth 0) wd := by
  refine ⟨?_, by cases word <;> rfl⟩
  simp only [merkleizeBoundedUnchecked, show ¬ 2 ^ depth < leaves.size by omega, if_false, depthFor_pow]
  rfl

end Ssz.Native.Driver
