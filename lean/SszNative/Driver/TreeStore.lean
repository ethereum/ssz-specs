import SszNative.Driver.Tree
import SszNative.Ir.Wf

/-!
A Merkle tree kept in memory, so changing a few leaves rehashes only their paths.

The tree is one buffer in heap order, 32 bytes per node.
Node i sits 32 i bytes past the start, and its children are nodes 2i and 2i + 1.
The width is the leaf count rounded up to a power of two, at least one.
The leaves are nodes width to twice the width, so node 1 is the top of the stored tree.
The first 32 bytes, where node 0 would be, are the drivers' own scratch.

```text
    width 4:      node 1
                 /      \
            node 2      node 3
            /    \      /    \
          n4     n5   n6     n7     the leaves, then zero nodes past the data
```

Above the stored tree, the root climbs to the declared depth against zero trees, then mixes a word in.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt

namespace TreeBuild
/-- The tree buffer. -/
abbrev tree : Var := ⟨0⟩
/-- The first leaf to copy in. -/
abbrev leaves : Var := ⟨1⟩
/-- How many leaves. -/
abbrev count : Var := ⟨2⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨3⟩
/-- The address of the zero-tree roots. -/
abbrev zeros : Var := ⟨4⟩
/-- The tree's width, then the current level's width. -/
abbrev width : Var := ⟨5⟩
/-- How many nodes of the current level cover a leaf. -/
abbrev live : Var := ⟨6⟩
/-- A loop index. -/
abbrev i : Var := ⟨7⟩
/-- The height of the level being written. -/
abbrev h : Var := ⟨8⟩
/-- The width of the level being written. -/
abbrev half : Var := ⟨9⟩
/-- The status the hashing driver hands back, zero on every x86-64 processor. -/
abbrev status : Var := ⟨10⟩
/-- A hashing call's result. -/
abbrev got : Var := ⟨11⟩
/-- How many nodes of the level being written cover a leaf. -/
abbrev up : Var := ⟨12⟩
/-- Where the next node goes. -/
abbrev dst : Var := ⟨13⟩
/-- Where it comes from. -/
abbrev src : Var := ⟨14⟩

/-- One level up: the pairs over data hashed in one call, the rest of the level filled with the zero tree. -/
def level : List Stmt :=
  [half ::= .shr width 1, up ::= .shr (live + 1) 1,
    when (ne up 0) [callInto got "ssz_hash_pairs"
      [tree + 32 * half, tree + 32 * width, tree + 32 * width + 32, up, ctx], status ::= status ||| got],
    h ::= h + 1, i ::= up,
    while_ (lt i half) ([dst ::= tree + 32 * half + 32 * i, src ::= zeros + 32 * h] ++ copy32 dst src ++
      [i ::= i + 1]),
    width ::= half, live ::= up]

/--
Build a tree over leaves: arguments tree, leaves, count, ctx.

The leaves are copied in, unless they already sit where the tree keeps them.
Nodes past the data hold zero trees, and each level hashes only the pairs over data, in one call.
Returns zero, since every x86-64 processor has a hashing kernel.
-/
def fn : Fn :=
  { params := 4, vars := 15, result := status,
    body := .block [zeros ::= ld (ctx + 16), status ::= 0,
      -- The width: the count rounded up to a power of two.
      width ::= 1, while_ (lt width count) [width ::= width + width],
      i ::= 0,
      when (ne leaves (tree + 32 * width))
        [while_ (lt i count) ([dst ::= tree + 32 * width + 32 * i, src ::= leaves + 32 * i] ++ copy32 dst src ++
          [i ::= i + 1])],
      i ::= count,
      while_ (lt i width) ([dst ::= tree + 32 * width + 32 * i, src ::= zeros] ++ copy32 dst src ++ [i ::= i + 1]),
      live ::= count, h ::= 0,
      while_ (lt 1 width) level] }
end TreeBuild

namespace TreeUpdate
/-- The tree buffer. -/
abbrev tree : Var := ⟨0⟩
/-- The tree's width. -/
abbrev width : Var := ⟨1⟩
/-- The rewritten leaves' indices, sorted and distinct, eight bytes each. -/
abbrev indices : Var := ⟨2⟩
/-- How many indices. -/
abbrev count : Var := ⟨3⟩
/-- The scratch buffer: 104 bytes per index. -/
abbrev scratch : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- The node indices of the current level, eight bytes each. -/
abbrev list : Var := ⟨6⟩
/-- The gathered pairs. -/
abbrev pairs : Var := ⟨7⟩
/-- Their digests. -/
abbrev digests : Var := ⟨8⟩
/-- How many nodes the current level holds. -/
abbrev k : Var := ⟨9⟩
/-- A loop index. -/
abbrev t : Var := ⟨10⟩
/-- How many parents are kept so far. -/
abbrev n : Var := ⟨11⟩
/-- The last parent kept. -/
abbrev prev : Var := ⟨12⟩
/-- A parent. -/
abbrev p : Var := ⟨13⟩
/-- The first parent. -/
abbrev first : Var := ⟨14⟩
/-- The status the hashing driver hands back, zero on every x86-64 processor. -/
abbrev status : Var := ⟨15⟩
/-- A hashing call's result. -/
abbrev got : Var := ⟨16⟩
/-- A node's address. -/
abbrev a : Var := ⟨17⟩
/-- An address in the scratch buffer. -/
abbrev d : Var := ⟨18⟩

/-- The parents of the current level, each kept once, written over it. -/
def parents : List Stmt :=
  [prev ::= .shr (ld list) 1, st list prev, n ::= 1, t ::= 1,
    while_ (lt t k) [p ::= .shr (ld (list + 8 * t)) 1,
      when (ne p prev) [st (list + 8 * n) p, n ::= n + 1, prev ::= p], t ::= t + 1],
    k ::= n]

/-- The parents' pairs gathered into one run, hashed in one call, and their digests put back. -/
def scattered : List Stmt :=
  [t ::= 0,
    -- The left children, then the right ones.
    while_ (lt t k) ([d ::= pairs + 64 * t, a ::= tree + 64 * ld (list + 8 * t)] ++ copy32 d a ++ [t ::= t + 1]),
    t ::= 0,
    while_ (lt t k) ([d ::= pairs + 64 * t + 32, a ::= tree + 64 * ld (list + 8 * t) + 32] ++ copy32 d a ++
      [t ::= t + 1]),
    callInto got "ssz_hash_pairs" [digests, pairs, pairs + 32, k, ctx], status ::= status ||| got,
    t ::= 0,
    while_ (lt t k) ([a ::= tree + 32 * ld (list + 8 * t), d ::= digests + 32 * t] ++ copy32 a d ++
      [t ::= t + 1])]

/-- The parents, when they are adjacent: their pairs hashed in place, in one call. -/
def adjacent : List Stmt :=
  [callInto got "ssz_hash_pairs" [tree + 32 * first, tree + 64 * first, tree + 64 * first + 32, k, ctx],
    status ::= status ||| got]

/-- One level up: the parents kept once, then hashed in place when adjacent, else gathered. -/
def level : List Stmt :=
  parents ++ [first ::= ld list, ifElse (eq (prev - first + 1) k) adjacent scattered]

/--
Rehash the paths above rewritten leaves: arguments tree, width, indices, count, scratch, ctx.

Each level's parents are kept once, then hashed in one call: in place when they are adjacent, else gathered.
Returns zero, since every x86-64 processor has a hashing kernel.
-/
def fn : Fn :=
  { params := 6, vars := 19, result := status,
    body := .block [status ::= 0,
      when (ne count 0) [list ::= scratch, pairs ::= scratch + 8 * count, digests ::= pairs + 64 * count,
        -- The leaves' node indices.
        t ::= 0, while_ (lt t count) [st (list + 8 * t) (width + ld (indices + 8 * t)), t ::= t + 1],
        k ::= count,
        while_ (lt 1 (ld list)) level]] }
end TreeUpdate

namespace TreeRoot
/-- The tree buffer. -/
abbrev tree : Var := ⟨0⟩
/-- The tree's width. -/
abbrev width : Var := ⟨1⟩
/-- The declared depth. -/
abbrev depth : Var := ⟨2⟩
/-- The address of the word to mix in, or zero for none. -/
abbrev mixin : Var := ⟨3⟩
/-- The output address. -/
abbrev out : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- The address of the zero-tree roots. -/
abbrev zeros : Var := ⟨6⟩
/-- The current height. -/
abbrev h : Var := ⟨7⟩
/-- A width halved down to one. -/
abbrev s : Var := ⟨8⟩
/-- The status the hashing driver hands back, zero on every x86-64 processor. -/
abbrev status : Var := ⟨9⟩
/-- A hashing call's result. -/
abbrev got : Var := ⟨10⟩

/--
The root of a tree: arguments tree, width, depth, mixin, out, ctx.

The stored top climbs from the tree's height to the depth against zero trees, then hashes against the word to mix in.
Each step hashes into the tree's first 32 bytes and copies back to the output.
Returns zero, since every x86-64 processor has a hashing kernel.
-/
def fn : Fn :=
  { params := 6, vars := 11, result := status,
    body := .block ([zeros ::= ld (ctx + 16), status ::= 0] ++ copy32 out (tree + 32) ++
      [h ::= 0, s ::= width, while_ (lt 1 s) [s ::= .shr s 1, h ::= h + 1],
        while_ (lt h depth) ([callInto got "ssz_hash_fixed" [tree, out, zeros + 32 * h, 1, ctx],
          status ::= status ||| got] ++ copy32 out tree ++ [h ::= h + 1]),
        when (ne mixin 0) ([callInto got "ssz_hash_fixed" [tree, out, mixin, 1, ctx],
          status ::= status ||| got] ++ copy32 out tree)]) }
end TreeRoot

/-- The tree store's drivers, under their exported names. -/
def treeStoreFns : List (String × Fn) :=
  [("ssz_tree_build", TreeBuild.fn), ("ssz_tree_update", TreeUpdate.fn), ("ssz_tree_root", TreeRoot.fn)]

/-- Every tree store driver fits the compiler's assumptions. -/
theorem treeStoreFns_wf : treeStoreFns.all (fun f => f.2.wf) = true := by
  decide +kernel

end EthLib.Consensus.Ssz.Native.Driver
