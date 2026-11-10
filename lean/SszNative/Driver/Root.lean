import SszNative.Driver.Tree
import SszNative.Root
import SszNative.Ir.Wf

/-!
The root of an encoded value, computed from its bytes, as drivers in the small language.

Each function mirrors one definition of the Lean root computation, step for step.
The type arrives as the address of its plan node, and a nested type is the address of the child node.

The encoding must already be accepted by validation, exactly as the Lean computation assumes.
Nothing here checks it again.

Memory is laid out like a stack that grows upward through a scratch buffer.
A function computing a count of roots writes them at its output, and uses the bytes after them as its own scratch.
A parent places each child's output where it wants the roots, in increasing order, so a child's scratch only ever
covers bytes the parent fills later.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt

/-- The quotient rounded up, for a constant divisor, without the overflow of adding to the dividend. -/
def ceilDiv (a : Expr) (k : Nat) : Expr :=
  a / (k : Expr) + ne (a % (k : Expr)) 0

/-- Thirty-two zero bytes, eight at a time. -/
def zero32 (dst : Expr) : List Stmt :=
  (List.range 4).map fun k => st (dst + ((8 * k : Nat) : Expr)) 0

/-- A count as one little-endian node: the count's eight bytes, then zeros. -/
def lengthNodeAt (dst count : Expr) : List Stmt :=
  [st dst count, st (dst + 8) 0, st (dst + 16) 0, st (dst + 24) 0]

namespace PlanWidth
/-- The node's address. -/
abbrev p : Var := ⟨0⟩
/-- The node's tag. -/
abbrev tag : Var := ⟨1⟩
/-- The width so far. -/
abbrev w : Var := ⟨2⟩
/-- How many fields remain to add. -/
abbrev n : Var := ⟨3⟩
/-- The current field's node. -/
abbrev q : Var := ⟨4⟩
/-- A field's width. -/
abbrev x : Var := ⟨5⟩
/-- A loop index. -/
abbrev i : Var := ⟨6⟩

/-- A fixed-size type's width in bytes, and zero for any other type: argument the node's address. -/
def fn : Fn :=
  { params := 1, vars := 7, result := w,
    body := .block [tag ::= ld p, w ::= 0,
      ifElse (eq tag 0) [w ::= 1] [
      ifElse (le tag 2) [w ::= ld (p + 8)] [
      ifElse (eq tag 4) [w ::= ceilDiv (ld (p + 8)) 8] [
      ifElse (eq tag 7) [callInto w "ssz_plan_fixed_width" [p + 16], w ::= w * ld (p + 8)] [
        when (eq tag 10 ||| eq tag 11) [
          ifElse (eq tag 10) [n ::= ld (p + 8), q ::= p + 16]
            [q ::= p + 16 + 8 * ld (p + 8), n ::= ld q, q ::= q + 8],
          -- The fields' widths, added in order.
          i ::= 0, while_ (lt i n) [callInto x "ssz_plan_fixed_width" [q], w ::= w + x,
            callInto q "ssz_plan_next" [q], i ::= i + 1]]]]]]] }
end PlanWidth

namespace PlanFixed
/-- The node's address. -/
abbrev p : Var := ⟨0⟩
/-- The node's tag. -/
abbrev tag : Var := ⟨1⟩
/-- One while every node seen so far has a fixed size. -/
abbrev r : Var := ⟨2⟩
/-- How many fields remain. -/
abbrev n : Var := ⟨3⟩
/-- The current field's node. -/
abbrev q : Var := ⟨4⟩
/-- A field's answer. -/
abbrev x : Var := ⟨5⟩
/-- A loop index. -/
abbrev i : Var := ⟨6⟩

/-- One when a type has a fixed size, and zero otherwise: argument the node's address. -/
def fn : Fn :=
  { params := 1, vars := 7, result := r,
    body := .block [tag ::= ld p, r ::= 0,
      ifElse (le tag 2 ||| eq tag 4) [r ::= 1] [
      ifElse (eq tag 7) [callInto r "ssz_plan_fixed" [p + 16]] [
        when (eq tag 10 ||| eq tag 11) [
          ifElse (eq tag 10) [n ::= ld (p + 8), q ::= p + 16]
            [q ::= p + 16 + 8 * ld (p + 8), n ::= ld q, q ::= q + 8],
          -- Every field must have a fixed size.
          r ::= 1, i ::= 0, while_ (lt i n) [callInto x "ssz_plan_fixed" [q], r ::= r &&& x,
            callInto q "ssz_plan_next" [q], i ::= i + 1]]]]] }
end PlanFixed

namespace PlanPlain
/-- The node's address. -/
abbrev p : Var := ⟨0⟩
/-- The node's tag. -/
abbrev tag : Var := ⟨1⟩
/-- One while every node seen so far is plain. -/
abbrev r : Var := ⟨2⟩
/-- How many fields remain. -/
abbrev n : Var := ⟨3⟩
/-- The current field's node. -/
abbrev q : Var := ⟨4⟩
/-- A field's answer. -/
abbrev x : Var := ⟨5⟩
/-- A loop index. -/
abbrev i : Var := ⟨6⟩

/--
One when a type is built from booleans, integers, byte and bit vectors, vectors, and containers, and zero otherwise:
argument the node's address.
-/
def fn : Fn :=
  { params := 1, vars := 7, result := r,
    body := .block [tag ::= ld p, r ::= 0,
      ifElse (le tag 2 ||| eq tag 4) [r ::= 1] [
      ifElse (eq tag 7) [callInto r "ssz_plan_plain" [p + 16]] [
        when (eq tag 10) [n ::= ld (p + 8), q ::= p + 16,
          -- Every field must be plain.
          r ::= 1, i ::= 0, while_ (lt i n) [callInto x "ssz_plan_plain" [q], r ::= r &&& x,
            callInto q "ssz_plan_next" [q], i ::= i + 1]]]]] }
end PlanPlain

namespace DepthFor
/-- The leaf count, halved at each level. -/
abbrev n : Var := ⟨0⟩
/-- The depth so far. -/
abbrev d : Var := ⟨1⟩

/-- The smallest depth whose perfect tree holds a count of leaves: argument the count. -/
def fn : Fn :=
  { params := 1, vars := 2, result := d,
    -- Halving rounded up, written so a count near the word's top cannot overflow.
    body := .block [d ::= 0, while_ (lt 1 n) [n ::= n / 2 + n % 2, d ::= d + 1]] }
end DepthFor

namespace RootPacked
/-- The width of one value in bytes. -/
abbrev width : Var := ⟨0⟩
/-- The first value's address. -/
abbrev src : Var := ⟨1⟩
/-- The bytes from one value to the next. -/
abbrev stride : Var := ⟨2⟩
/-- How many values. -/
abbrev count : Var := ⟨3⟩
/-- Where the roots go. -/
abbrev out : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- The depth of one value's tree. -/
abbrev depth : Var := ⟨6⟩
/-- The bytes of one value's block of nodes. -/
abbrev slot : Var := ⟨7⟩
/-- Where the blocks are gathered. -/
abbrev g : Var := ⟨8⟩
/-- The address of the gather's shape words. -/
abbrev shape : Var := ⟨9⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨10⟩
/-- The current level's address. -/
abbrev lvl : Var := ⟨11⟩
/-- The current level's size in bytes. -/
abbrev size : Var := ⟨12⟩
/-- The current level's height. -/
abbrev h : Var := ⟨13⟩
/-- Where the next level goes. -/
abbrev dst : Var := ⟨14⟩
/-- A loop index. -/
abbrev i : Var := ⟨15⟩

/--
The gather into the blocks, by the dispatcher that picks the fastest routine for the width.

The shape words go in the context's padding area, which nothing holds before the hashing.
-/
def gatherCall : List Stmt :=
  [shape ::= ld (ctx + 24), st shape width, st (shape + 8) (stride - width), st (shape + 16) (slot - width),
    callInto sink "ssz_gather_field" [g, src, count, shape, ctx]]

/--
The roots of a count of packed values: arguments width, src, stride, count, out, ctx.

Each value's bytes fill a zero-padded block of nodes, and the blocks are hashed level by level down to one node each.
The scratch after the roots holds the blocks and the levels: twice the blocks' size at most.
-/
def fn : Fn :=
  { params := 6, vars := 16, result := 0,
    body := .block ([callInto depth "ssz_depth_for" [ceilDiv width 32],
      slot ::= 32, i ::= 0, while_ (lt i depth) [slot ::= slot + slot, i ::= i + 1],
      -- Values of one node are their own roots, gathered straight into place.
      ifElse (eq depth 0) [g ::= out] [g ::= out + 32 * count]] ++ gatherCall ++ [
      lvl ::= g, size ::= count * slot, h ::= 0,
      while_ (lt h depth) [
        -- Each level follows the one before it, and the last lands in the output.
        ifElse (eq (h + 1) depth) [dst ::= out] [dst ::= lvl + size],
        callInto sink "ssz_hash_pairs" [dst, lvl, lvl + 32, size / 64, ctx],
        lvl ::= dst, size ::= size / 2, h ::= h + 1]]) }
end RootPacked

namespace RootColumns
/-- The first column's address. -/
abbrev cols : Var := ⟨0⟩
/-- How many columns. -/
abbrev n : Var := ⟨1⟩
/-- How many nodes each column holds. -/
abbrev count : Var := ⟨2⟩
/-- The depth of the tree over the columns. -/
abbrev depth : Var := ⟨3⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨4⟩
/-- Where the root column goes: right before the columns. -/
abbrev out : Var := ⟨5⟩
/-- The bytes of one column. -/
abbrev cs : Var := ⟨6⟩
/-- The current level's first column. -/
abbrev lvl : Var := ⟨7⟩
/-- The current level's column count. -/
abbrev w : Var := ⟨8⟩
/-- The current level's height. -/
abbrev h : Var := ⟨9⟩
/-- Where the next level may go. -/
abbrev next : Var := ⟨10⟩
/-- The pairs of the current level. -/
abbrev half : Var := ⟨11⟩
/-- A loop index. -/
abbrev i : Var := ⟨12⟩
/-- Where the next level goes. -/
abbrev dst : Var := ⟨13⟩
/-- The levels the pairing takes. -/
abbrev levels : Var := ⟨14⟩
/-- The levels climbed against zero trees after it. -/
abbrev climbs : Var := ⟨15⟩
/-- The address of the zero-tree roots. -/
abbrev zeros : Var := ⟨16⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨17⟩
/-- A loop index. -/
abbrev j : Var := ⟨18⟩

/--
The tree over columns, padded with zero-tree levels up to a depth: arguments cols, n, count, depth, ctx.

The root column goes right before the columns, and the levels go right after them.
Pairs of columns are hashed into one column per level, and an odd column out against the zero tree of its height.
-/
def fn : Fn :=
  { params := 5, vars := 19, result := 0,
    body := .block [zeros ::= ld (ctx + 16), cs ::= 32 * count, out ::= cols - cs,
      callInto levels "ssz_depth_for" [n],
      ifElse (lt levels depth) [climbs ::= depth - levels] [climbs ::= 0],
      lvl ::= cols, w ::= n, h ::= 0, next ::= cols + n * cs,
      while_ (lt 1 w) [half ::= w / 2,
        -- The last level of all lands in the output.
        ifElse (eq (half + w % 2) 1 &&& eq climbs 0) [dst ::= out] [dst ::= next],
        i ::= 0,
        while_ (lt i half) [
          callInto sink "ssz_hash_columns" [dst + i * cs, lvl + 2 * i * cs, lvl + (2 * i + 1) * cs, count, ctx],
          i ::= i + 1],
        when (ne (w % 2) 0)
          [callInto sink "ssz_hash_fixed" [dst + half * cs, lvl + (w - 1) * cs, zeros + 32 * h, count, ctx]],
        w ::= half + w % 2, lvl ::= dst, next ::= dst + w * cs, h ::= h + 1],
      -- The climb starts at the height the pairing ends at.
      h ::= levels, j ::= 0,
      while_ (lt j climbs) [
        ifElse (eq (j + 1) climbs) [dst ::= out] [dst ::= next],
        callInto sink "ssz_hash_fixed" [dst, lvl, zeros + 32 * h, count, ctx],
        lvl ::= dst, next ::= dst + cs, h ::= h + 1, j ::= j + 1],
      -- A lone column with nothing to climb is copied out.
      when (ne lvl out) [callInto sink "ssz_gather" [out, lvl, 1, cs, 0, 0]]] }
end RootColumns

namespace RootsOf
/-- The type's plan node. -/
abbrev p : Var := ⟨0⟩
/-- The first value's address. -/
abbrev src : Var := ⟨1⟩
/-- The bytes from one value to the next. -/
abbrev stride : Var := ⟨2⟩
/-- How many values. -/
abbrev count : Var := ⟨3⟩
/-- Where the roots go. -/
abbrev out : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- The node's tag. -/
abbrev tag : Var := ⟨6⟩
/-- The element or field count. -/
abbrev len : Var := ⟨7⟩
/-- The current element or field node. -/
abbrev e : Var := ⟨8⟩
/-- A width in bytes. -/
abbrev w : Var := ⟨9⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨10⟩
/-- The buffer of one value's leaves. -/
abbrev r : Var := ⟨11⟩
/-- A tree depth. -/
abbrev d : Var := ⟨12⟩
/-- The first column. -/
abbrev c : Var := ⟨13⟩
/-- A loop index. -/
abbrev i : Var := ⟨14⟩
/-- The current field's offset in a record. -/
abbrev off : Var := ⟨15⟩
/-- The current leaf's address. -/
abbrev slot : Var := ⟨16⟩
/-- A byte index. -/
abbrev k : Var := ⟨17⟩
/-- The current field's tag. -/
abbrev te : Var := ⟨18⟩
/-- Whether the current field is its own leaf. -/
abbrev pk : Var := ⟨19⟩

/-- Whether a field's root is its own bytes, zero-padded to one node. -/
def packsInto : List Stmt :=
  [te ::= ld e, pk ::= le te 1,
    when (eq te 2) [pk ::= le (ld (e + 8)) 32], when (eq te 4) [pk ::= le (ld (e + 8)) 256]]

/-- A field's bytes copied into a zeroed leaf, eight at a time, then byte by byte. -/
def copyLeaf : List Stmt :=
  zero32 slot ++ [k ::= 0,
    while_ (le (k + 8) w) [st (slot + k) (ld (src + off + k)), k ::= k + 8],
    while_ (lt k w) [st1 (slot + k) (ld1 (src + off + k)), k ::= k + 1]]

/--
The roots of a count of values of a fixed-size type, one stride apart: arguments plan, src, stride, count, out, ctx.

The roots go back to back at the output, and the bytes after them are scratch.
One value is rooted alone; several are rooted together, one column per element or field.
-/
def fn : Fn :=
  { params := 6, vars := 20, result := 0,
    body := .block [tag ::= ld p,
      ifElse (eq tag 7) [len ::= ld (p + 8), e ::= p + 16,
        ifElse (le (ld e) 1)
          -- Basic elements pack together.
          [callInto w "ssz_plan_fixed_width" [p], callInto sink "ssz_root_packed" [w, src, stride, count, out, ctx]]
          [callInto w "ssz_plan_fixed_width" [e],
            ifElse (eq count 1)
              -- One value: its elements' roots side by side, then their tree.
              [r ::= out + 32, callInto sink "ssz_roots_chunked" [e, src, w, len, r, ctx],
                callInto d "ssz_depth_for" [len],
                callInto sink "ssz_merkleize" [r, len, d, out, r + 32 * len + 32, ctx]]
              -- One column per element, then the element tree across them.
              [c ::= out + 32 * count, i ::= 0,
                while_ (lt i len) [
                  callInto sink "ssz_roots_of" [e, src + w * i, stride, count, c + 32 * count * i, ctx],
                  i ::= i + 1],
                callInto d "ssz_depth_for" [len], callInto sink "ssz_root_columns" [c, len, count, d, ctx]]]]
      [ifElse (eq tag 10) [len ::= ld (p + 8), e ::= p + 16, off ::= 0, i ::= 0,
        ifElse (eq count 1)
          -- One record: each field's leaf, then their tree.
          [r ::= out + 32,
            while_ (lt i len) ([callInto w "ssz_plan_fixed_width" [e], slot ::= r + 32 * i] ++ packsInto ++
              [ifElse pk copyLeaf [callInto sink "ssz_roots_of" [e, src + off, w, 1, slot, ctx]],
                off ::= off + w, callInto e "ssz_plan_next" [e], i ::= i + 1]),
            callInto d "ssz_depth_for" [len],
            callInto sink "ssz_merkleize" [r, len, d, out, r + 32 * len + 32, ctx]]
          -- One column per field, then the field tree across them.
          [c ::= out + 32 * count,
            while_ (lt i len) [
              callInto sink "ssz_roots_of" [e, src + off, stride, count, c + 32 * count * i, ctx],
              callInto w "ssz_plan_fixed_width" [e], off ::= off + w, callInto e "ssz_plan_next" [e], i ::= i + 1],
            callInto d "ssz_depth_for" [len], callInto sink "ssz_root_columns" [c, len, count, d, ctx]]]
      -- Every other fixed-size type packs.
      [callInto w "ssz_plan_fixed_width" [p], callInto sink "ssz_root_packed" [w, src, stride, count, out, ctx]]]] }
end RootsOf

namespace RootsChunked
/-- The type's plan node. -/
abbrev p : Var := ⟨0⟩
/-- The first value's address. -/
abbrev src : Var := ⟨1⟩
/-- The bytes from one value to the next. -/
abbrev stride : Var := ⟨2⟩
/-- How many values. -/
abbrev count : Var := ⟨3⟩
/-- Where the roots go. -/
abbrev out : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- The values rooted so far. -/
abbrev done : Var := ⟨6⟩
/-- The values of the current chunk. -/
abbrev c : Var := ⟨7⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨8⟩

/--
The roots of a long run of values, a chunk of records at a time: arguments plan, src, stride, count, out, ctx.

A chunk's records and their columns then fit in one core's cache.
-/
def fn : Fn :=
  { params := 6, vars := 9, result := 0,
    body := .block [
      ifElse (le count (recordsPerChunk : Nat)) [callInto sink "ssz_roots_of" [p, src, stride, count, out, ctx]]
        [done ::= 0,
          while_ (lt done count) [c ::= count - done, when (lt (recordsPerChunk : Nat) c) [c ::= (recordsPerChunk : Nat)],
            callInto sink "ssz_roots_of" [p, src + stride * done, stride, c, out + 32 * done, ctx],
            done ::= done + (recordsPerChunk : Nat)]]] }
end RootsChunked

namespace RootProgressive
/-- The first node's address. -/
abbrev nodes : Var := ⟨0⟩
/-- How many nodes. -/
abbrev count : Var := ⟨1⟩
/-- Where the root goes. -/
abbrev out : Var := ⟨2⟩
/-- The scratch buffer. -/
abbrev scratch : Var := ⟨3⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨4⟩
/-- How many subtrees the spine holds. -/
abbrev k : Var := ⟨5⟩
/-- The first node of the current subtree. -/
abbrev start : Var := ⟨6⟩
/-- The current subtree's capacity. -/
abbrev width : Var := ⟨7⟩
/-- The current subtree's depth. -/
abbrev lg : Var := ⟨8⟩
/-- The current subtree's node count. -/
abbrev here : Var := ⟨9⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨10⟩
/-- A loop index. -/
abbrev i : Var := ⟨11⟩

/-- The bytes of the spine's pair area: enough for every subtree a 64-bit count can need. -/
abbrev spineBytes : Nat := 64 * 40

/--
The root of the progressive tree over a count of nodes: arguments nodes, count, out, scratch, ctx.

Subtree i goes into the left half of pair i of an area at the scratch, and the right half of pair i is the spine below
it, so the spine folds from its last pair up.
-/
def fn : Fn :=
  { params := 5, vars := 12, result := 0,
    body := .block [k ::= 0, start ::= 0, width ::= 1, lg ::= 0,
      while_ (lt start count) [here ::= count - start, when (lt width here) [here ::= width],
        callInto sink "ssz_merkleize"
          [nodes + 32 * start, here, lg, scratch + 64 * k, scratch + (spineBytes : Nat), ctx],
        k ::= k + 1, start ::= start + width, width ::= 4 * width, lg ::= lg + 2],
      ifElse (eq k 0) (zero32 out)
        -- The spine closes with a zero node.
        (zero32 (scratch + 64 * k - 32) ++ [i ::= k - 1,
          while_ (lt 0 i) [
            callInto sink "ssz_hash_pairs" [scratch + 64 * i - 32, scratch + 64 * i, scratch + 64 * i + 32, 1, ctx],
            i ::= i - 1],
          callInto sink "ssz_hash_pairs" [out, scratch, scratch + 32, 1, ctx]])] }
end RootProgressive

namespace RootElements
/-- The element's plan node. -/
abbrev e : Var := ⟨0⟩
/-- The sequence's address. -/
abbrev src : Var := ⟨1⟩
/-- The sequence's size in bytes. -/
abbrev size : Var := ⟨2⟩
/-- How many elements. -/
abbrev count : Var := ⟨3⟩
/-- Where the roots go. -/
abbrev out : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- Whether the element has a fixed size. -/
abbrev fx : Var := ⟨6⟩
/-- The element's width, when fixed. -/
abbrev w : Var := ⟨7⟩
/-- The scratch after the roots. -/
abbrev scr : Var := ⟨8⟩
/-- A loop index. -/
abbrev i : Var := ⟨9⟩
/-- The current element's offset. -/
abbrev o : Var := ⟨10⟩
/-- Where the current element ends. -/
abbrev en : Var := ⟨11⟩
/-- The current element's address. -/
abbrev s : Var := ⟨12⟩
/-- The current element's size. -/
abbrev n : Var := ⟨13⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨14⟩

/--
The roots of a sequence's elements, one per element: arguments element plan, src, size, count, out, ctx.

Fixed-size elements sit one width apart; the others are found through the offsets.
The bytes after the roots are scratch.
-/
def fn : Fn :=
  { params := 6, vars := 15, result := 0,
    body := .block [callInto fx "ssz_plan_fixed" [e], callInto w "ssz_plan_fixed_width" [e],
      scr ::= out + 32 * count, i ::= 0,
      while_ (lt i count) [
        ifElse fx [s ::= src + w * i, n ::= w]
          -- A body runs from its offset to the next one, and the last to the end.
          [o ::= ld4 (src + 4 * i),
            ifElse (lt (i + 1) count) [en ::= ld4 (src + 4 * i + 4)] [en ::= size],
            s ::= src + o, n ::= en - o],
        callInto sink "ssz_root_of" [e, s, n, out + 32 * i, scr, ctx], i ::= i + 1]] }
end RootElements

namespace RootFields
/-- The first field's plan node. -/
abbrev f : Var := ⟨0⟩
/-- How many fields. -/
abbrev n : Var := ⟨1⟩
/-- The struct's address. -/
abbrev src : Var := ⟨2⟩
/-- The struct's size in bytes. -/
abbrev size : Var := ⟨3⟩
/-- Where the roots go. -/
abbrev out : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- The table of field ranges: start, end, and whether the field is fixed, for each field. -/
abbrev t : Var := ⟨6⟩
/-- The position in the fixed part. -/
abbrev pos : Var := ⟨7⟩
/-- A loop index. -/
abbrev j : Var := ⟨8⟩
/-- Whether the current field is fixed. -/
abbrev fx : Var := ⟨9⟩
/-- The current field's width. -/
abbrev w : Var := ⟨10⟩
/-- Where the body after the current one starts. -/
abbrev nextStart : Var := ⟨11⟩
/-- The current table entry. -/
abbrev ent : Var := ⟨12⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨13⟩
/-- The current field node. -/
abbrev q : Var := ⟨14⟩

/--
The roots of a struct's fields, each from its own range: arguments fields plan, n, src, size, out, ctx.

The fixed part is read first, into a table after the roots.
Then each body's end is the next body's start, walking back from the end.
Then each field is rooted from its range, with the bytes after the table as scratch.
-/
def fn : Fn :=
  { params := 6, vars := 15, result := 0,
    body := .block [t ::= out + 32 * n, pos ::= 0, j ::= 0, q ::= f,
      while_ (lt j n) [ent ::= t + 24 * j, callInto fx "ssz_plan_fixed" [q], st (ent + 16) fx,
        ifElse fx [callInto w "ssz_plan_fixed_width" [q], st ent (src + pos), st (ent + 8) (src + pos + w), pos ::= pos + w]
          [st ent (src + ld4 (src + pos)), pos ::= pos + 4],
        callInto q "ssz_plan_next" [q], j ::= j + 1],
      -- Bodies end where the next begins, and the last at the end of the struct.
      nextStart ::= src + size,
      while_ (lt 0 j) [j ::= j - 1, ent ::= t + 24 * j,
        when (eq (ld (ent + 16)) 0) [st (ent + 8) nextStart, nextStart ::= ld ent]],
      q ::= f,
      while_ (lt j n) [ent ::= t + 24 * j,
        callInto sink "ssz_root_of" [q, ld ent, ld (ent + 8) - ld ent, out + 32 * j, t + 24 * n, ctx],
        callInto q "ssz_plan_next" [q], j ::= j + 1]] }
end RootFields

namespace RootBytes
/-- The type's plan node. -/
abbrev p : Var := ⟨0⟩
/-- The value's address. -/
abbrev src : Var := ⟨1⟩
/-- The value's size in bytes. -/
abbrev size : Var := ⟨2⟩
/-- Where the root goes. -/
abbrev out : Var := ⟨3⟩
/-- The scratch buffer. -/
abbrev scratch : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- How many nodes the bytes fill. -/
abbrev nodes : Var := ⟨6⟩
/-- Where the nodes go. -/
abbrev buf : Var := ⟨7⟩
/-- The tree's depth. -/
abbrev d : Var := ⟨8⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨9⟩

/--
The root of a byte list: arguments plan, src, size, out, scratch, ctx.

The scratch holds the contents' root and the length node, then the bytes padded to whole nodes.
-/
def fn : Fn :=
  { params := 6, vars := 10, result := 0,
    body := .block ([nodes ::= ceilDiv size 32, buf ::= scratch + 64,
      callInto sink "ssz_gather" [buf, src, 1, size, 0, 32 * nodes + 32 - size],
      callInto d "ssz_depth_for" [ceilDiv (ld (p + 8)) 32],
      callInto sink "ssz_merkleize" [buf, nodes, d, scratch, buf + 32 * nodes + 32, ctx]] ++
      lengthNodeAt (scratch + 32) size ++
      [callInto sink "ssz_hash_pairs" [out, scratch, scratch + 32, 1, ctx]]) }
end RootBytes

namespace RootBits
/-- The type's plan node. -/
abbrev p : Var := ⟨0⟩
/-- The value's address. -/
abbrev src : Var := ⟨1⟩
/-- The value's size in bytes. -/
abbrev size : Var := ⟨2⟩
/-- Where the root goes. -/
abbrev out : Var := ⟨3⟩
/-- The scratch buffer. -/
abbrev scratch : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- The last byte, halved down to one. -/
abbrev v : Var := ⟨6⟩
/-- The position of the last byte's highest set bit. -/
abbrev hb : Var := ⟨7⟩
/-- Two to that position. -/
abbrev pw : Var := ⟨8⟩
/-- How many bits the list holds. -/
abbrev count : Var := ⟨9⟩
/-- How many bytes those bits fill. -/
abbrev bytes : Var := ⟨10⟩
/-- How many nodes those bytes fill. -/
abbrev nodes : Var := ⟨11⟩
/-- Where the nodes go. -/
abbrev buf : Var := ⟨12⟩
/-- The tree's depth. -/
abbrev d : Var := ⟨13⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨14⟩

/--
The root of a bit list, bounded or progressive: arguments plan, src, size, out, scratch, ctx.

The delimiter is the last byte's highest set bit; the bits below it are the contents.
-/
def fn : Fn :=
  { params := 6, vars := 15, result := 0,
    body := .block ([v ::= ld1 (src + size - 1), hb ::= 0, pw ::= 1,
      while_ (lt 1 v) [v ::= v / 2, hb ::= hb + 1, pw ::= pw + pw],
      count ::= 8 * (size - 1) + hb, bytes ::= (count + 7) / 8, nodes ::= ceilDiv bytes 32, buf ::= scratch + 64,
      callInto sink "ssz_gather" [buf, src, 1, bytes, 0, 32 * nodes + 32 - bytes],
      -- The delimiter shares a byte with the last bits only when the count is not a whole number of bytes.
      when (ne (count % 8) 0) [st1 (buf + count / 8) (ld1 (buf + count / 8) &&& (255 ^^^ pw))],
      ifElse (eq (ld p) 5)
        [callInto d "ssz_depth_for" [ceilDiv (ld (p + 8)) 256],
          callInto sink "ssz_merkleize" [buf, nodes, d, scratch, buf + 32 * nodes + 32, ctx]]
        [callInto sink "ssz_root_progressive" [buf, nodes, scratch, buf + 32 * nodes + 32, ctx]]] ++
      lengthNodeAt (scratch + 32) count ++
      [callInto sink "ssz_hash_pairs" [out, scratch, scratch + 32, 1, ctx]]) }
end RootBits

namespace RootList
/-- The type's plan node. -/
abbrev p : Var := ⟨0⟩
/-- The value's address. -/
abbrev src : Var := ⟨1⟩
/-- The value's size in bytes. -/
abbrev size : Var := ⟨2⟩
/-- Where the root goes. -/
abbrev out : Var := ⟨3⟩
/-- The scratch buffer. -/
abbrev scratch : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- The node's tag. -/
abbrev tag : Var := ⟨6⟩
/-- The declared limit, or zero for a progressive list. -/
abbrev limit : Var := ⟨7⟩
/-- The element's plan node. -/
abbrev e : Var := ⟨8⟩
/-- The element's width. -/
abbrev w : Var := ⟨9⟩
/-- How many nodes the tree is over. -/
abbrev nodes : Var := ⟨10⟩
/-- The capacity of the tree. -/
abbrev cap : Var := ⟨11⟩
/-- How many elements the list holds. -/
abbrev count : Var := ⟨12⟩
/-- Whether the element has a fixed size. -/
abbrev fx : Var := ⟨13⟩
/-- Whether the element is plain. -/
abbrev pl : Var := ⟨14⟩
/-- Where the nodes go. -/
abbrev buf : Var := ⟨15⟩
/-- The tree's depth. -/
abbrev d : Var := ⟨16⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨17⟩

/--
The root of a list, bounded or progressive: arguments plan, src, size, out, scratch, ctx.

Basic elements pack into nodes; plain elements are rooted together as columns; the others are rooted one by one.
-/
def fn : Fn :=
  { params := 6, vars := 18, result := 0,
    body := .block ([tag ::= ld p,
      ifElse (eq tag 8) [limit ::= ld (p + 8), e ::= p + 16] [limit ::= 0, e ::= p + 24],
      buf ::= scratch + 64, callInto w "ssz_plan_fixed_width" [e],
      ifElse (le (ld e) 1)
        [nodes ::= ceilDiv size 32,
          callInto sink "ssz_gather" [buf, src, 1, size, 0, 32 * nodes + 32 - size],
          -- A basic element's width divides a node, so the capacity in nodes needs no product.
          cap ::= limit / (32 / w) + ne (limit % (32 / w)) 0, count ::= size / w]
        [callInto fx "ssz_plan_fixed" [e],
          ifElse fx [ifElse (eq w 0) [count ::= 0] [count ::= size / w]]
            [ifElse (eq size 0) [count ::= 0] [count ::= ld4 src / 4]],
          nodes ::= count, cap ::= limit, callInto pl "ssz_plan_plain" [e],
          -- An empty list has no records to root.
          ifElse pl [when (lt 0 count) [callInto sink "ssz_roots_chunked" [e, src, w, count, buf, ctx]]]
            [callInto sink "ssz_root_elements" [e, src, size, count, buf, ctx]]],
      ifElse (eq tag 8)
        [callInto d "ssz_depth_for" [cap],
          callInto sink "ssz_merkleize" [buf, nodes, d, scratch, buf + 32 * nodes + 32, ctx]]
        [callInto sink "ssz_root_progressive" [buf, nodes, scratch, buf + 32 * nodes + 32, ctx]]] ++
      lengthNodeAt (scratch + 32) count ++
      [callInto sink "ssz_hash_pairs" [out, scratch, scratch + 32, 1, ctx]]) }
end RootList

namespace RootVector
/-- The type's plan node. -/
abbrev p : Var := ⟨0⟩
/-- The value's address. -/
abbrev src : Var := ⟨1⟩
/-- The value's size in bytes. -/
abbrev size : Var := ⟨2⟩
/-- Where the root goes. -/
abbrev out : Var := ⟨3⟩
/-- The scratch buffer. -/
abbrev scratch : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- The element count. -/
abbrev len : Var := ⟨6⟩
/-- The tree's depth. -/
abbrev d : Var := ⟨7⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨8⟩

/-- The root of a vector of elements that are not all plain: arguments plan, src, size, out, scratch, ctx. -/
def fn : Fn :=
  { params := 6, vars := 9, result := 0,
    body := .block [len ::= ld (p + 8),
      callInto sink "ssz_root_elements" [p + 16, src, size, len, scratch, ctx],
      callInto d "ssz_depth_for" [len],
      callInto sink "ssz_merkleize" [scratch, len, d, out, scratch + 32 * len + 32, ctx]] }
end RootVector

namespace RootContainer
/-- The type's plan node. -/
abbrev p : Var := ⟨0⟩
/-- The value's address. -/
abbrev src : Var := ⟨1⟩
/-- The value's size in bytes. -/
abbrev size : Var := ⟨2⟩
/-- Where the root goes. -/
abbrev out : Var := ⟨3⟩
/-- The scratch buffer. -/
abbrev scratch : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- The field count. -/
abbrev n : Var := ⟨6⟩
/-- The tree's depth. -/
abbrev d : Var := ⟨7⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨8⟩

/-- The root of a container whose fields are not all plain: arguments plan, src, size, out, scratch, ctx. -/
def fn : Fn :=
  { params := 6, vars := 9, result := 0,
    body := .block [n ::= ld (p + 8),
      callInto sink "ssz_root_fields" [p + 16, n, src, size, scratch, ctx],
      callInto d "ssz_depth_for" [n],
      callInto sink "ssz_merkleize" [scratch, n, d, out, scratch + 32 * n + 32, ctx]] }
end RootContainer

namespace RootProgressiveContainer
/-- The type's plan node. -/
abbrev p : Var := ⟨0⟩
/-- The value's address. -/
abbrev src : Var := ⟨1⟩
/-- The value's size in bytes. -/
abbrev size : Var := ⟨2⟩
/-- Where the root goes. -/
abbrev out : Var := ⟨3⟩
/-- The scratch buffer. -/
abbrev scratch : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- The layout's length. -/
abbrev k : Var := ⟨6⟩
/-- The layout's first word. -/
abbrev bits : Var := ⟨7⟩
/-- The field count. -/
abbrev n : Var := ⟨8⟩
/-- The field roots. -/
abbrev r : Var := ⟨9⟩
/-- The leaves, one per layout position. -/
abbrev l : Var := ⟨10⟩
/-- A layout position. -/
abbrev j : Var := ⟨11⟩
/-- The next field root to place. -/
abbrev idx : Var := ⟨12⟩
/-- The bit of the current position within its byte. -/
abbrev pw : Var := ⟨13⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨14⟩

/--
The root of a progressive container: arguments plan, src, size, out, scratch, ctx.

Field roots are placed at the layout's set positions, with zero leaves at its gaps, and the layout is mixed in.
-/
def fn : Fn :=
  { params := 6, vars := 15, result := 0,
    body := .block ([k ::= ld (p + 8), bits ::= p + 16, n ::= ld (bits + 8 * k), r ::= scratch + 64,
      callInto sink "ssz_root_fields" [bits + 8 * k + 8, n, src, size, r, ctx],
      l ::= r + 32 * n, j ::= 0, idx ::= 0,
      while_ (lt j k) [
        ifElse (ne (ld (bits + 8 * j)) 0 &&& lt idx n) (copy32 (l + 32 * j) (r + 32 * idx) ++ [idx ::= idx + 1])
          (zero32 (l + 32 * j)),
        j ::= j + 1],
      callInto sink "ssz_root_progressive" [l, k, scratch, l + 32 * k, ctx]] ++ zero32 (scratch + 32) ++
      -- One bit per position from the lowest, as one node.
      [j ::= 0, pw ::= 1,
      while_ (lt j k &&& lt j 256) [
        when (ne (ld (bits + 8 * j)) 0) [st1 (scratch + 32 + j / 8) (ld1 (scratch + 32 + j / 8) ||| pw)],
        j ::= j + 1, ifElse (eq (j % 8) 0) [pw ::= 1] [pw ::= pw + pw]],
      callInto sink "ssz_hash_pairs" [out, scratch, scratch + 32, 1, ctx]]) }
end RootProgressiveContainer

namespace RootUnion
/-- The type's plan node. -/
abbrev p : Var := ⟨0⟩
/-- The value's address. -/
abbrev src : Var := ⟨1⟩
/-- The value's size in bytes. -/
abbrev size : Var := ⟨2⟩
/-- Where the root goes. -/
abbrev out : Var := ⟨3⟩
/-- The scratch buffer. -/
abbrev scratch : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- The option count. -/
abbrev n : Var := ⟨6⟩
/-- The selector byte. -/
abbrev sel : Var := ⟨7⟩
/-- The current option's plan node. -/
abbrev q : Var := ⟨8⟩
/-- An option index. -/
abbrev i : Var := ⟨9⟩
/-- Whether the selected option was found. -/
abbrev found : Var := ⟨10⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨11⟩

/-- The root of a compatible union: arguments plan, src, size, out, scratch, ctx. -/
def fn : Fn :=
  { params := 6, vars := 12, result := 0,
    body := .block ([n ::= ld (p + 8), sel ::= ld1 src, q ::= p + 16 + 8 * n, i ::= 0, found ::= 0,
      while_ (lt i n &&& eq found 0) [
        ifElse (eq (ld (p + 16 + 8 * i)) sel)
          [callInto sink "ssz_root_of" [q, src + 1, size - 1, scratch, scratch + 64, ctx], found ::= 1]
          [callInto q "ssz_plan_next" [q], i ::= i + 1]],
      when (eq found 0) (zero32 scratch)] ++ lengthNodeAt (scratch + 32) sel ++
      [callInto sink "ssz_hash_pairs" [out, scratch, scratch + 32, 1, ctx]]) }
end RootUnion

namespace RootOf
/-- The type's plan node. -/
abbrev p : Var := ⟨0⟩
/-- The value's address. -/
abbrev src : Var := ⟨1⟩
/-- The value's size in bytes. -/
abbrev size : Var := ⟨2⟩
/-- Where the root goes. -/
abbrev out : Var := ⟨3⟩
/-- The scratch buffer. -/
abbrev scratch : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- The node's tag. -/
abbrev tag : Var := ⟨6⟩
/-- Whether the type is plain. -/
abbrev pl : Var := ⟨7⟩
/-- The type's width. -/
abbrev w : Var := ⟨8⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨9⟩

/-- The root of one fixed-size value, rooted as a column of one into the scratch, then copied out. -/
def single : List Stmt :=
  [callInto w "ssz_plan_fixed_width" [p], callInto sink "ssz_roots_of" [p, src, w, 1, scratch, ctx]] ++
    copy32 out scratch

/-- A call passing every argument on to a function of the same shape. -/
def pass (name : String) : Stmt :=
  callInto sink name [p, src, size, out, scratch, ctx]

/--
The root of the value a range of an accepted encoding holds: arguments plan, src, size, out, scratch, ctx.

The root goes to the output, and the scratch must miss the encoding, the plan and the output.
-/
def fn : Fn :=
  { params := 6, vars := 10, result := 0,
    body := .block [tag ::= ld p,
      ifElse (eq tag 3) [pass "ssz_root_bytes"] [
      ifElse (eq tag 5 ||| eq tag 6) [pass "ssz_root_bits"] [
      ifElse (eq tag 8 ||| eq tag 9) [pass "ssz_root_list"] [
      ifElse (eq tag 11) [pass "ssz_root_progressive_container"] [
      ifElse (eq tag 12) [pass "ssz_root_union"] [
      ifElse (eq tag 7 ||| eq tag 10)
        [callInto pl "ssz_plan_plain" [p],
          ifElse pl single [ifElse (eq tag 7) [pass "ssz_root_vector"] [pass "ssz_root_container"]]]
        single]]]]]] }
end RootOf

namespace HashTreeRoot
/-- The type's plan. -/
abbrev plan : Var := ⟨0⟩
/-- The encoding's address. -/
abbrev data : Var := ⟨1⟩
/-- The encoding's size in bytes. -/
abbrev len : Var := ⟨2⟩
/-- Where the root goes. -/
abbrev out : Var := ⟨3⟩
/-- The scratch buffer. -/
abbrev scratch : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- The result, always zero. -/
abbrev status : Var := ⟨6⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨7⟩

/--
The root of an encoding: arguments plan, data, len, out, scratch, ctx.

The encoding must be one validation accepted against the plan's type.
The 32-byte root goes to the output, and the scratch needs the bytes the scratch bound gives.
Returns zero: the hashing kernels run on every x86-64 processor.
-/
def fn : Fn :=
  { params := 6, vars := 8, result := status,
    body := .block [callInto sink "ssz_root_of" [plan, data, len, out, scratch, ctx], status ::= 0] }
end HashTreeRoot

/-!
## Scratch

The bounds below give the bytes a driver uses, as a function of the type and of a size.
A parent's need is its own buffers, then the most any one child needs, since children run one after the other and reuse
the same bytes.

Every step saturates at a cap far past any memory, so the bound a 64-bit word computes is exactly the bound defined
here, and a bound at the cap means no buffer is large enough.
-/

/-- The largest bound reported: past any memory a program may use. -/
abbrev scratchCap : Nat := 2 ^ 62

/-- A number, saturated at the cap. -/
def sat (x : Nat) : Nat := min x scratchCap

/-- A saturated sum. -/
def sadd (a b : Nat) : Nat := sat (a + b)

/-- A saturated product. -/
def smul (a b : Nat) : Nat := sat (a * b)

/-- The bytes a tree over a count of nodes needs past its nodes: the levels, or the spine's pairs and one subtree. -/
def treeNeed (nodes : Nat) : Nat :=
  sadd (RootProgressive.spineBytes + 32 * zeroHeights) (smul 32 nodes)

/-- The bytes packed roots of a count of values of a width use from their output on: the roots, blocks and levels. -/
def packedNeed (width count : Nat) : Nat :=
  let depth := depthFor (nodesFor width)
  if depth = 0 then smul 32 count else sadd (smul 32 count) (smul (smul 2 count) (smul 32 (2 ^ depth)))

mutual

/-- A fixed-size type's width, saturated. -/
def satWidth : Desc → Nat
  | .bool => 1
  | .uint width => sat width
  | .byteVector length => sat length
  | .bitVector length => (length + 7) / 8
  | .vector element length => smul (satWidth element) (sat length)
  | .container _ fields | .progressiveContainer _ _ fields => satFieldsWidth fields 0
  | _ => 0

/-- The saturated total width of a list of fixed-size types, after a width so far. -/
def satFieldsWidth : List Desc → Nat → Nat
  | [], acc => acc
  | field :: rest, acc => satFieldsWidth rest (sadd acc (satWidth field))

end

mutual

/-- The bytes the roots of a count of fixed-size values use from their output on. -/
def rootsNeed : Desc → Nat → Nat
  | .vector element length, count =>
    let len := sat length
    if element.isBasic then packedNeed (smul (satWidth element) len) count
    else if count = 1 then
      -- The element roots, chunk by chunk, then the tree over them.
      let chunks := if len ≤ recordsPerChunk then rootsNeed element len
        else sadd (smul 32 len) (rootsNeed element recordsPerChunk)
      sadd 32 (max chunks (sadd (sadd (smul 32 len) 32) (treeNeed len)))
    else
      sadd (sadd (smul 32 count) (smul (smul 32 count) len))
        (max (rootsNeed element count) (smul (smul 64 count) len))
  | .container _ fields, count =>
    let n := sat fields.length
    let most := fieldsRootsNeed fields count 0
    if count = 1 then sadd (sadd 32 (smul 32 n)) (max most (sadd 32 (treeNeed n)))
    else sadd (sadd (smul 32 count) (smul (smul 32 count) n)) (max most (smul (smul 64 count) n))
  | d, count => packedNeed (satWidth d) count

/-- The most any field's roots need, for a count of records, after a most so far. -/
def fieldsRootsNeed : List Desc → Nat → Nat → Nat
  | [], _, most => most
  | field :: rest, count, most => fieldsRootsNeed rest count (max (rootsNeed field count) most)

end

/--
The most nodes a list's tree can be over, from the size of its encoding, saturated.

Basic elements pack into nodes; any other element has a root of its own, and is at least a width or an offset long.
-/
def nodesBound (element : Desc) (size : Nat) : Nat :=
  sat (if element.isBasic then nodesFor size
    else if hasWidth element then (if satWidth element = 0 then 0 else size / satWidth element)
    else size / bytesPerOffset)

mutual

/-- The bytes rooting a value of a type, from a range of a size, uses from its scratch on. -/
def varNeed : Desc → Nat → Nat
  | .byteList _, size | .bitList _, size | .progressiveBitList _, size =>
    sadd (sadd 96 (smul 32 (nodesFor size))) (treeNeed (nodesFor size))
  | .vector element length, size =>
    if plain (.vector element length) then rootsNeed (.vector element length) 1
    else
      let len := sat length
      sadd (smul 32 len) (max (varNeed element size) (sadd 32 (treeNeed len)))
  | .list element _, size | .progressiveList element _, size =>
    let nodes := nodesBound element size
    -- One record roots alone and may need more than several, so its bound is a floor: the bound grows with the size.
    let elements := if element.isBasic then 0
      else if plain element then max (rootsNeed element 1) (rootsNeed element (min nodes recordsPerChunk))
      else varNeed element size
    sadd (sadd 96 (smul 32 nodes)) (max elements (treeNeed nodes))
  | .container names fields, size =>
    if plain (.container names fields) then rootsNeed (.container names fields) 1
    else
      let n := sat fields.length
      max (sadd (smul 56 n) (fieldsVarNeed fields size 0)) (sadd (sadd (smul 32 n) 32) (treeNeed n))
  | .progressiveContainer active _ fields, size =>
    let n := sat fields.length
    let k := sat active.length
    sadd 64 (max (sadd (smul 56 n) (fieldsVarNeed fields size 0))
      (sadd (sadd (smul 32 n) (smul 32 k)) (treeNeed k)))
  | .compatibleUnion _ options, size => sadd 64 (fieldsVarNeed options size 0)
  | d, _ => rootsNeed d 1

/-- The most any of several types needs, from a range of a size, after a most so far. -/
def fieldsVarNeed : List Desc → Nat → Nat → Nat
  | [], _, most => most
  | field :: rest, size, most => fieldsVarNeed rest size (max (varNeed field size) most)

end

/--
The scratch bytes the root of an encoding of a size needs, saturated at the cap.

Every term is linear in the size, so the scratch is a constant number of times the encoding, plus a constant set by
the type.
A list of fixed-size records needs about 64 bytes per record, and a list of bytes about 2 bytes per byte.
-/
def rootScratch (d : Desc) (len : Nat) : Nat :=
  varNeed d len

/-- A value saturated at the cap, in place. -/
def satIn (r : Var) : Stmt :=
  when (lt (scratchCap : Nat) r) [r ::= (scratchCap : Nat)]

/-- A saturated sum of two values at most the cap, which cannot wrap. -/
def saddIn (r : Var) (a b : Expr) : List Stmt :=
  [r ::= a + b, satIn r]

/-- A saturated product of two values at most the cap: the cap when the product would pass it. -/
def smulIn (r : Var) (a b : Expr) : Stmt :=
  ifElse (eq a 0) [r ::= 0] [ifElse (lt ((scratchCap : Nat) / a) b) [r ::= (scratchCap : Nat)] [r ::= a * b]]

/-- The larger of two values. -/
def maxIn (r : Var) (a b : Expr) : Stmt :=
  ifElse (lt a b) [r ::= b] [r ::= a]

/-- The tree need over a count of nodes at most the cap. -/
def treeIn (r : Var) (nodes : Expr) : List Stmt :=
  smulIn r 32 nodes :: saddIn r ((RootProgressive.spineBytes + 32 * zeroHeights : Nat) : Expr) r

namespace ScratchWidth
/-- The node's address. -/
abbrev p : Var := ⟨0⟩
/-- The node's tag. -/
abbrev tag : Var := ⟨1⟩
/-- The width so far. -/
abbrev w : Var := ⟨2⟩
/-- How many fields. -/
abbrev n : Var := ⟨3⟩
/-- The current field's node. -/
abbrev q : Var := ⟨4⟩
/-- A field's or an element's width. -/
abbrev x : Var := ⟨5⟩
/-- A loop index. -/
abbrev i : Var := ⟨6⟩
/-- A length, saturated. -/
abbrev y : Var := ⟨7⟩

/-- A fixed-size type's width, saturated, and zero for any other type: argument the node's address. -/
def fn : Fn :=
  { params := 1, vars := 8, result := w,
    body := .block [tag ::= ld p, w ::= 0,
      ifElse (eq tag 0) [w ::= 1] [
      ifElse (le tag 2) [w ::= ld (p + 8), satIn w] [
      ifElse (eq tag 4) [w ::= ceilDiv (ld (p + 8)) 8] [
      ifElse (eq tag 7) [callInto x "ssz_scratch_width" [p + 16], y ::= ld (p + 8), satIn y, smulIn w x y] [
        when (eq tag 10 ||| eq tag 11) [
          ifElse (eq tag 10) [n ::= ld (p + 8), q ::= p + 16]
            [q ::= p + 16 + 8 * ld (p + 8), n ::= ld q, q ::= q + 8],
          -- The fields' widths, added in order.
          i ::= 0, while_ (lt i n) ([callInto x "ssz_scratch_width" [q]] ++ saddIn w w x ++
            [callInto q "ssz_plan_next" [q], i ::= i + 1])]]]]]] }
end ScratchWidth

namespace ScratchPacked
/-- The width of one value. -/
abbrev width : Var := ⟨0⟩
/-- How many values. -/
abbrev count : Var := ⟨1⟩
/-- The depth of one value's tree. -/
abbrev depth : Var := ⟨2⟩
/-- The bound so far. -/
abbrev r : Var := ⟨3⟩
/-- Two to the depth. -/
abbrev pw : Var := ⟨4⟩
/-- A loop index. -/
abbrev i : Var := ⟨5⟩
/-- A partial product. -/
abbrev t : Var := ⟨6⟩
/-- Another partial product. -/
abbrev u : Var := ⟨7⟩

/-- The bytes packed roots of a count of values of a width use: arguments width and count, both at most the cap. -/
def fn : Fn :=
  { params := 2, vars := 8, result := r,
    body := .block [callInto depth "ssz_depth_for" [ceilDiv width 32], smulIn r 32 count,
      when (ne depth 0) ([pw ::= 1, i ::= 0, while_ (lt i depth) [pw ::= pw + pw, i ::= i + 1],
        smulIn t 32 pw, smulIn u 2 count, smulIn t u t] ++ saddIn r r t)] }
end ScratchPacked

namespace ScratchRoots
/-- The type's plan node. -/
abbrev p : Var := ⟨0⟩
/-- How many values. -/
abbrev count : Var := ⟨1⟩
/-- The node's tag. -/
abbrev tag : Var := ⟨2⟩
/-- The element count, saturated. -/
abbrev len : Var := ⟨3⟩
/-- The element's node. -/
abbrev e : Var := ⟨4⟩
/-- The bound. -/
abbrev r : Var := ⟨5⟩
/-- The children's need. -/
abbrev t : Var := ⟨6⟩
/-- A partial bound. -/
abbrev u : Var := ⟨7⟩
/-- The field count, saturated. -/
abbrev n : Var := ⟨8⟩
/-- The current field's node. -/
abbrev q : Var := ⟨9⟩
/-- A loop index. -/
abbrev i : Var := ⟨10⟩
/-- A partial bound. -/
abbrev x : Var := ⟨11⟩
/-- A width. -/
abbrev w : Var := ⟨12⟩
/-- The field count. -/
abbrev k : Var := ⟨13⟩

/-- The bytes the roots of a count of fixed-size values use: arguments plan and count, the count at most the cap. -/
def fn : Fn :=
  { params := 2, vars := 14, result := r,
    body := .block [tag ::= ld p,
      ifElse (eq tag 7) [len ::= ld (p + 8), satIn len, e ::= p + 16,
        ifElse (le (ld e) 1)
          [callInto w "ssz_scratch_width" [e], smulIn w w len, callInto r "ssz_scratch_packed" [w, count]]
          [ifElse (eq count 1)
            ([ifElse (le len (recordsPerChunk : Nat)) [callInto t "ssz_scratch_roots" [e, len]]
              ([callInto t "ssz_scratch_roots" [e, (recordsPerChunk : Nat)], smulIn u 32 len] ++ saddIn t u t),
              smulIn u 32 len] ++ saddIn u u 32 ++ treeIn x len ++ saddIn u u x ++ [maxIn t t u] ++ saddIn r 32 t)
            ([callInto t "ssz_scratch_roots" [e, count], smulIn u 64 count, smulIn u u len, maxIn t t u,
              smulIn u 32 count, smulIn x u len] ++ saddIn u u x ++ saddIn r u t)]]
      [ifElse (eq tag 10) ([k ::= ld (p + 8), n ::= k, satIn n, q ::= p + 16, t ::= 0, i ::= 0,
          while_ (lt i k) [callInto x "ssz_scratch_roots" [q, count], maxIn t x t,
            callInto q "ssz_plan_next" [q], i ::= i + 1],
          ifElse (eq count 1)
            ([smulIn u 32 n] ++ saddIn u 32 u ++ treeIn x n ++ saddIn x 32 x ++ [maxIn t t x] ++ saddIn r u t)
            ([smulIn u 32 count, smulIn x u n] ++ saddIn u u x ++ [smulIn x 64 count, smulIn x x n, maxIn t t x] ++
              saddIn r u t)])
        [callInto w "ssz_scratch_width" [p], callInto r "ssz_scratch_packed" [w, count]]]] }
end ScratchRoots

namespace RootScratch
/-- The type's plan node. -/
abbrev p : Var := ⟨0⟩
/-- The size of the value's encoding. -/
abbrev size : Var := ⟨1⟩
/-- The node's tag. -/
abbrev tag : Var := ⟨2⟩
/-- The bound. -/
abbrev r : Var := ⟨3⟩
/-- The children's need. -/
abbrev t : Var := ⟨4⟩
/-- A partial bound. -/
abbrev u : Var := ⟨5⟩
/-- A partial bound. -/
abbrev x : Var := ⟨6⟩
/-- A node count. -/
abbrev nodes : Var := ⟨7⟩
/-- The element's node. -/
abbrev e : Var := ⟨8⟩
/-- A count, saturated. -/
abbrev n : Var := ⟨9⟩
/-- A count of child nodes. -/
abbrev k : Var := ⟨10⟩
/-- The current child node. -/
abbrev q : Var := ⟨11⟩
/-- A loop index. -/
abbrev i : Var := ⟨12⟩
/-- Whether a type is plain. -/
abbrev pl : Var := ⟨13⟩
/-- Whether a type has a fixed size. -/
abbrev fx : Var := ⟨14⟩
/-- A width. -/
abbrev w : Var := ⟨15⟩
/-- A layout length, saturated. -/
abbrev ks : Var := ⟨16⟩

/-- The most any of a count of child nodes needs, from the current child on, into the children's need. -/
def childrenNeed : List Stmt :=
  [t ::= 0, i ::= 0,
    while_ (lt i k) [callInto x "ssz_root_scratch" [q, size], maxIn t x t, callInto q "ssz_plan_next" [q],
      i ::= i + 1]]

/--
The scratch bytes rooting an encoding of a size needs: arguments plan and size.

The bound saturates at the cap, so it is exactly the scratch bound of the plan's type.
-/
def fn : Fn :=
  { params := 2, vars := 17, result := r,
    body := .block [tag ::= ld p,
      ifElse (eq tag 3 ||| eq tag 5 ||| eq tag 6)
        ([nodes ::= ceilDiv size 32, smulIn u 32 nodes] ++ saddIn u 96 u ++ treeIn x nodes ++ saddIn r u x) [
      ifElse (eq tag 8 ||| eq tag 9)
        ([ifElse (eq tag 8) [e ::= p + 16] [e ::= p + 24],
          ifElse (le (ld e) 1) [nodes ::= ceilDiv size 32, satIn nodes, t ::= 0]
            [callInto fx "ssz_plan_fixed" [e],
              ifElse fx [callInto w "ssz_scratch_width" [e], ifElse (eq w 0) [nodes ::= 0] [nodes ::= size / w]]
                [nodes ::= size / 4],
              satIn nodes, callInto pl "ssz_plan_plain" [e],
              ifElse pl [k ::= nodes, when (lt (recordsPerChunk : Nat) k) [k ::= (recordsPerChunk : Nat)],
                  callInto t "ssz_scratch_roots" [e, k], callInto x "ssz_scratch_roots" [e, 1], maxIn t x t]
                [callInto t "ssz_root_scratch" [e, size]]],
          smulIn u 32 nodes] ++ saddIn u 96 u ++ treeIn x nodes ++ [maxIn t t x] ++ saddIn r u t) [
      ifElse (eq tag 7 ||| eq tag 10)
        [callInto pl "ssz_plan_plain" [p],
          ifElse pl [callInto r "ssz_scratch_roots" [p, 1]]
            [ifElse (eq tag 7)
              ([n ::= ld (p + 8), satIn n, callInto t "ssz_root_scratch" [p + 16, size]] ++ treeIn x n ++
                saddIn x 32 x ++ [maxIn t t x, smulIn u 32 n] ++ saddIn r u t)
              ([k ::= ld (p + 8), n ::= k, satIn n, q ::= p + 16] ++ childrenNeed ++
                [smulIn u 56 n] ++ saddIn u u t ++ [smulIn x 32 n] ++ saddIn x x 32 ++ treeIn t n ++
                saddIn x x t ++ [maxIn r u x])]] [
      ifElse (eq tag 11)
        ([ks ::= ld (p + 8), q ::= p + 16 + 8 * ks, satIn ks, k ::= ld q, n ::= k, satIn n, q ::= q + 8] ++
          childrenNeed ++ [smulIn u 56 n] ++ saddIn u u t ++ [smulIn x 32 n, smulIn t 32 ks] ++ saddIn x x t ++
          treeIn t ks ++ saddIn x x t ++ [maxIn r u x] ++ saddIn r 64 r) [
      ifElse (eq tag 12)
        ([k ::= ld (p + 8), q ::= p + 16 + 8 * k] ++ childrenNeed ++ saddIn r 64 t)
        [callInto r "ssz_scratch_roots" [p, 1]]]]]]] }
end RootScratch

/-- The root drivers, each under its exported name. -/
def rootFns : List (String × Fn) :=
  [("ssz_plan_fixed_width", PlanWidth.fn), ("ssz_plan_fixed", PlanFixed.fn),
    ("ssz_plan_plain", PlanPlain.fn), ("ssz_depth_for", DepthFor.fn), ("ssz_root_packed", RootPacked.fn),
    ("ssz_root_columns", RootColumns.fn), ("ssz_roots_of", RootsOf.fn), ("ssz_roots_chunked", RootsChunked.fn),
    ("ssz_root_progressive", RootProgressive.fn), ("ssz_root_elements", RootElements.fn),
    ("ssz_root_fields", RootFields.fn), ("ssz_root_bytes", RootBytes.fn), ("ssz_root_bits", RootBits.fn),
    ("ssz_root_list", RootList.fn), ("ssz_root_vector", RootVector.fn), ("ssz_root_container", RootContainer.fn),
    ("ssz_root_progressive_container", RootProgressiveContainer.fn), ("ssz_root_union", RootUnion.fn),
    ("ssz_root_of", RootOf.fn), ("ssz_hash_tree_root", HashTreeRoot.fn),
    ("ssz_scratch_width", ScratchWidth.fn), ("ssz_scratch_packed", ScratchPacked.fn),
    ("ssz_scratch_roots", ScratchRoots.fn), ("ssz_root_scratch", RootScratch.fn)]

/-- Every root driver fits the compiler's assumptions. -/
theorem rootFns_wf : rootFns.all (fun f => f.2.wf) = true := by
  decide +kernel

end EthLib.Consensus.Ssz.Native.Driver
