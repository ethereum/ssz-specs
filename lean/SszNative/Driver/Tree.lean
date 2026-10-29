import SszNative.Driver.Hash
import Ssz.Hash.Sha256

/-!
The root of a perfect Merkle tree over a buffer of 32-byte nodes, padded with zero subtrees.

Each level is hashed into a fresh region of a scratch buffer, right after the level before it.
An odd level's last node is hashed against the zero tree of its height.
A lone node climbs the remaining heights against zero trees.
-/

namespace Ssz.Native.Driver

open Ssz.Native.Ir Ssz.Native.Ir.Expr Ssz.Native.Ir.Stmt

/-- The heights of zero trees kept in the constant table: enough for any 64-bit capacity. -/
abbrev zeroHeights : Nat := 64

/-- The roots of the all-zero trees of heights 0 to 64, 32 bytes each, as the drivers read them. -/
def zeroRootsTable : ByteArray := Id.run do
  let mut table := ByteArray.mk (Array.replicate 32 0)
  let mut node := ByteArray.mk (Array.replicate 32 0)
  for _ in [0:zeroHeights] do
    node := Ssz.Sha256.hash (node ++ node)
    table := table ++ node
  return table

section
/-- The address of the first node. -/
private def nodes : Var := ⟨0⟩
/-- How many pairs, or nodes, remain. -/
private def count : Var := ⟨1⟩
/-- The tree's depth. -/
private def depth : Var := ⟨2⟩
/-- The output address. -/
private def out : Var := ⟨3⟩
/-- The scratch buffer for the levels. -/
private def scratch : Var := ⟨4⟩
/-- The context the caller filled. -/
private def ctx : Var := ⟨5⟩
/-- The address of the zero-tree roots. -/
private def zeros : Var := ⟨6⟩
/-- The address of the current level. -/
private def level : Var := ⟨7⟩
/-- The current level's node count. -/
private def width : Var := ⟨8⟩
/-- The current level's height. -/
private def h : Var := ⟨9⟩
/-- Where the next level goes. -/
private def dst : Var := ⟨10⟩
/-- The pairs of the current level. -/
private def half : Var := ⟨11⟩
/-- The result: zero unless no kernel ran. -/
private def status : Var := ⟨12⟩
/-- A hashing call's result. -/
private def got : Var := ⟨13⟩

/--
The root of the tree of a depth over count nodes: arguments nodes, count, depth, out, scratch, ctx.

The scratch buffer needs 32 bytes per node plus 32 per level, and must miss the nodes and the output.
Returns zero, or one when the processor has no hashing kernel.
-/
def merkleize : Fn :=
  { params := 6, vars := 14, result := status,
    body := .block [zeros ::= ld (ctx + 16), status ::= 0,
      ifElse (eq count 0) (copy32 out (zeros + 32 * depth))
        ([level ::= nodes, width ::= count, h ::= 0, dst ::= scratch,
          while_ (lt h depth) [
            ifElse (le width 1)
              -- A lone node climbs against the zero tree of its height.
              [callInto got "ssz_hash_fixed" [dst, level, zeros + 32 * h, 1, ctx], status ::= status ||| got]
              [half ::= width / 2,
                callInto got "ssz_hash_pairs" [dst, level, level + 32, half, ctx], status ::= status ||| got,
                -- An odd last node pairs with the zero tree of its height.
                when (ne (width % 2) 0) [callInto got "ssz_hash_fixed"
                  [dst + 32 * half, level + 32 * (width - 1), zeros + 32 * h, 1, ctx], status ::= status ||| got],
                width ::= (width + 1) / 2],
            level ::= dst, dst ::= dst + 32 * width, h ::= h + 1]] ++ copy32 out level)] }
end

end Ssz.Native.Driver
