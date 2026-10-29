import SszNative.Driver.Root
import SszNative.Driver.Branch

/-!
Nodes, branches, and multiproofs read from an encoding, as drivers in the small language.

Each function mirrors one definition of the Lean walk in `SszNative/Branch.lean`, step for step.
A node's subtree is rooted from its own bytes alone, with the root drivers.

The encoding must already be accepted by validation, exactly as the root driver assumes.
Nothing here checks it again, so the refusals below are the ones the Lean functions give for an accepted encoding.

A generalized index is one 64-bit word, so a node deeper than 63 levels cannot be named.
A caller holding a larger index refuses it before calling.

Each public driver answers one word:

```text
    0    the nodes are written
    3    an index of zero, which names no node
    4    the index of the root, which has no branch
    8    a request naming no index
    9    one index named twice
    10   an index below another of the same request
    12   a path descending into a mixed-in word
    13   a path descending into packed data
    14   a path descending into a position that holds no value
    15   a path onto a level past the end of a progressive spine
```

The tree of one value is described by a layout record, written into the scratch:

```text
    lay + 0     what sits under the tree: 0 packed bytes, 1 values one width apart, 2 a struct's fields,
                3 a progressive struct's positions, 4 a union's option, 5 values found through offsets
    lay + 8     how many leaves, gaps included
    lay + 16    one when the tree is bounded
    lay + 24    the bounded tree's capacity in leaves
    lay + 32    one when a word is mixed in
    lay + 40    the mixed-in word, 32 bytes
    lay + 72    the encoding's address
    lay + 80    packed: where the bytes start; values: where the first starts
    lay + 88    packed: where the bytes stop; a union's option or values through offsets: where they stop
    lay + 96    the element's, the first field's, or the option's plan node
    lay + 104   packed: one when the last byte holds a bit list's delimiter; values one width apart: the width
    lay + 112   packed: the delimiter's bit; values one width apart: one when plain; positions: the layout's words
    lay + 120   the first byte of scratch past the record
    lay + 128   where the node goes
    lay + 136   the context the caller filled
    lay + 144   a struct's field ranges, as the codec writes them: their count, then a start and a stop each
```

Positions are byte offsets into the encoding, so a range of the encoding is its address plus a start and a stop.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt

/-- The bytes of a layout record before its field ranges. -/
abbrev layoutBytes : Nat := 144

namespace ProvePow2
/-- The exponent. -/
abbrev k : Var := ⟨0⟩
/-- The power so far. -/
abbrev r : Var := ⟨1⟩
/-- A loop index. -/
abbrev i : Var := ⟨2⟩

/-- Two to a power, wrapping at the word's width: argument the exponent. -/
def fn : Fn :=
  { params := 1, vars := 3, result := r,
    body := .block [r ::= 1, i ::= 0, while_ (lt i k) [r ::= r + r, i ::= i + 1]] }
end ProvePow2

namespace ProveShr
/-- The word shifted. -/
abbrev x : Var := ⟨0⟩
/-- How many places. -/
abbrev k : Var := ⟨1⟩
/-- A loop index. -/
abbrev i : Var := ⟨2⟩

/-- A word shifted right by a number of places: arguments the word and the count. -/
def fn : Fn :=
  { params := 2, vars := 3, result := x,
    body := .block [i ::= 0, while_ (lt i k) [x ::= .shr x 1, i ::= i + 1]] }
end ProveShr

namespace ProveLayout
/-- The type's plan node. -/
abbrev p : Var := ⟨0⟩
/-- The encoding's address. -/
abbrev data : Var := ⟨1⟩
/-- Where the value starts. -/
abbrev start : Var := ⟨2⟩
/-- Where it stops. -/
abbrev stop : Var := ⟨3⟩
/-- Where the record goes. -/
abbrev lay : Var := ⟨4⟩
/-- The value's size in bytes. -/
abbrev size : Var := ⟨5⟩
/-- The node's tag. -/
abbrev tag : Var := ⟨6⟩
/-- The element's plan node. -/
abbrev e : Var := ⟨7⟩
/-- The element's width. -/
abbrev w : Var := ⟨8⟩
/-- A field or option count. -/
abbrev n : Var := ⟨9⟩
/-- One when the tree is bounded. -/
abbrev bnd : Var := ⟨10⟩
/-- How many elements. -/
abbrev cnt : Var := ⟨11⟩
/-- Whether the element has a fixed size. -/
abbrev fx : Var := ⟨12⟩
/-- Whether the element is plain. -/
abbrev pl : Var := ⟨13⟩
/-- The last byte, halved down to one. -/
abbrev v : Var := ⟨14⟩
/-- The position of the last byte's highest set bit. -/
abbrev hb : Var := ⟨15⟩
/-- Two to that position, or to a position of a layout byte. -/
abbrev pw : Var := ⟨16⟩
/-- How many bits a bit list holds, or the address of a layout's words. -/
abbrev bits : Var := ⟨17⟩
/-- A plan node being walked. -/
abbrev q : Var := ⟨18⟩
/-- A loop index. -/
abbrev i : Var := ⟨19⟩
/-- A layout's length. -/
abbrev k : Var := ⟨20⟩
/-- Whether the selected option was found. -/
abbrev found : Var := ⟨21⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨22⟩
/-- A declared length or limit. -/
abbrev lim : Var := ⟨23⟩
/-- The selector byte, or a count of packed bytes. -/
abbrev sel : Var := ⟨24⟩

/-- A count as the mixed-in word. -/
def mixCount (c : Expr) : List Stmt :=
  st (lay + 32) 1 :: lengthNodeAt (lay + 40) c

/-- Packed bytes from the value's start to a stop, with no delimiter to clear. -/
def packed (to : Expr) : List Stmt :=
  [st lay 0, st (lay + 80) start, st (lay + 88) to, st (lay + 104) 0, st (lay + 8) (ceilDiv (to - start) 32)]

/-- A boolean, an integer, or a byte or bit vector: its bytes, packed, the tree just wide enough or declared. -/
def basic : List Stmt :=
  packed stop ++ [
    ifElse (eq tag 3) ([st (lay + 24) (ceilDiv (ld (p + 8)) 32)] ++ mixCount size)
      [ifElse (eq tag 4) [st (lay + 24) (ceilDiv (ld (p + 8)) 256)] [st (lay + 24) (ceilDiv size 32)]]]

/-- A bit list: its bits, packed without the delimiter, which a byte shares with the last bits when any are left. -/
def bitList : List Stmt :=
  [v ::= ld1 (data + stop - 1), hb ::= 0, pw ::= 1,
    while_ (lt 1 v) [v ::= v / 2, hb ::= hb + 1, pw ::= pw + pw],
    bits ::= 8 * (size - 1) + hb, sel ::= (bits + 7) / 8] ++ packed (start + sel) ++
  [st (lay + 104) (ne (bits % 8) 0), st (lay + 112) pw,
    ifElse (eq tag 5) [st (lay + 24) (ceilDiv (ld (p + 8)) 256)] [bnd ::= 0]] ++ mixCount bits

/-- A vector or a list: basic elements packed, fixed-size ones one width apart, the others through the offsets. -/
def sequence : List Stmt :=
  [ifElse (eq tag 9) [e ::= p + 24, lim ::= 0, bnd ::= 0] [e ::= p + 16, lim ::= ld (p + 8)],
    callInto w "ssz_plan_fixed_width" [e], callInto fx "ssz_plan_fixed" [e],
    -- A vector holds its length; a list as many elements as its encoding does.
    ifElse (eq tag 7) [cnt ::= lim]
      [ifElse fx [ifElse (eq w 0) [cnt ::= 0] [cnt ::= size / w]]
        [ifElse (eq size 0) [cnt ::= 0] [cnt ::= ld4 (data + start) / 4]]],
    when (ne tag 7) (mixCount cnt),
    ifElse (le (ld e) 1)
      -- A basic element's width divides a node, so the capacity in nodes needs no product.
      (packed stop ++ [st (lay + 24) (lim / (32 / w) + ne (lim % (32 / w)) 0)])
      [st (lay + 8) cnt, st (lay + 24) lim, st (lay + 96) e,
        ifElse fx [st lay 1, st (lay + 80) start, st (lay + 104) w, callInto pl "ssz_plan_plain" [e],
          st (lay + 112) pl]
          [st lay 5, st (lay + 80) start, st (lay + 88) stop]]]

/-- A struct's fields from a first node: their count, their ranges, and a leaf each. -/
def fields (first count : Expr) : List Stmt :=
  [n ::= count, st (lay + 96) first, st (lay + 144) n,
    callInto sink "ssz_fields_ranges" [first, data, start, stop, n, lay + 144],
    st (lay + 120) (lay + ((layoutBytes + 8 : Nat) : Expr) + 16 * n)]

/-- A progressive struct's layout, one bit per position from the lowest, as the mixed-in word. -/
def activeWord : List Stmt :=
  [st (lay + 32) 1] ++ zero32 (lay + 40) ++ [i ::= 0, pw ::= 1,
    while_ (lt i k &&& lt i 256) [
      when (ne (ld (bits + 8 * i)) 0) [st1 (lay + 40 + i / 8) (ld1 (lay + 40 + i / 8) ||| pw)],
      i ::= i + 1, ifElse (eq (i % 8) 0) [pw ::= 1] [pw ::= pw + pw]]]

/-- A union: the selected option, after the selector, as one leaf, with the selector mixed in. -/
def union : List Stmt :=
  [n ::= ld (p + 8), sel ::= ld1 (data + start), q ::= p + 16 + 8 * n, i ::= 0, found ::= 0,
    while_ (lt i n &&& eq found 0) [
      ifElse (eq (ld (p + 16 + 8 * i)) sel) [found ::= 1] [callInto q "ssz_plan_next" [q], i ::= i + 1]],
    st lay 4, st (lay + 8) 1, st (lay + 24) 1, st (lay + 96) q, st (lay + 80) (start + 1), st (lay + 88) stop] ++
  mixCount sel

/--
The tree a range of an accepted encoding merkleizes into: arguments plan, data, start, stop, lay.

The record is written at lay, as the header lays it out.
-/
def fn : Fn :=
  { params := 5, vars := 25, result := 0,
    body := .block [size ::= stop - start, tag ::= ld p, bnd ::= 1, st (lay + 32) 0, st (lay + 72) data,
      st (lay + 120) (lay + (layoutBytes : Expr)),
      ifElse (le tag 4) basic [
      ifElse (le tag 6) bitList [
      ifElse (le tag 9) sequence [
      ifElse (eq tag 10) ([st lay 2, st (lay + 8) (ld (p + 8)), st (lay + 24) (ld (p + 8))] ++
        fields (p + 16) (ld (p + 8))) [
      ifElse (eq tag 11) ([k ::= ld (p + 8), bits ::= p + 16, bnd ::= 0, st lay 3, st (lay + 8) k,
        st (lay + 112) bits] ++ fields (bits + 8 * k + 8) (ld (bits + 8 * k)) ++ activeWord)
        union]]]],
      st (lay + 16) bnd] }
end ProveLayout

namespace ProveSlot
/-- The layout record. -/
abbrev lay : Var := ⟨0⟩
/-- The position asked for. -/
abbrev i : Var := ⟨1⟩
/-- Where the value's plan node, start, and stop go. -/
abbrev out : Var := ⟨2⟩
/-- What sits under the tree. -/
abbrev kind : Var := ⟨3⟩
/-- One when the position holds a value. -/
abbrev r : Var := ⟨4⟩
/-- Where the value starts. -/
abbrev s : Var := ⟨5⟩
/-- Where it stops. -/
abbrev e : Var := ⟨6⟩
/-- Its plan node. -/
abbrev q : Var := ⟨7⟩
/-- The encoding's address. -/
abbrev data : Var := ⟨8⟩
/-- Where the values start. -/
abbrev start : Var := ⟨9⟩
/-- A width. -/
abbrev w : Var := ⟨10⟩
/-- A layout position. -/
abbrev j : Var := ⟨11⟩
/-- The field a position holds. -/
abbrev idx : Var := ⟨12⟩
/-- The layout's words. -/
abbrev bits : Var := ⟨13⟩
/-- How many positions there are. -/
abbrev cnt : Var := ⟨14⟩

/-- Field idx's plan node and range, from the codec's table. -/
def field (at_ : Expr) : List Stmt :=
  [callInto q "ssz_plan_skip" [ld (lay + 96), at_], s ::= ld (lay + 152 + 16 * at_),
    e ::= ld (lay + 160 + 16 * at_), r ::= 1]

/--
The value at one position under a tree: arguments lay, i, out.

Answers one and writes the plan node, the start, and the stop at out, or answers zero for a gap or a position past
the end.
-/
def fn : Fn :=
  { params := 3, vars := 15, result := r,
    body := .block [r ::= 0, kind ::= ld lay, cnt ::= ld (lay + 8), data ::= ld (lay + 72), start ::= ld (lay + 80),
      when (lt i cnt) [
        ifElse (eq kind 1) [q ::= ld (lay + 96), w ::= ld (lay + 104), s ::= start + w * i, e ::= s + w, r ::= 1] [
        ifElse (eq kind 2) (field i) [
        ifElse (eq kind 3) [bits ::= ld (lay + 112),
          -- A set position holds the field after those of the set positions before it.
          when (ne (ld (bits + 8 * i)) 0) [idx ::= 0, j ::= 0,
            while_ (lt j i) [when (ne (ld (bits + 8 * j)) 0) [idx ::= idx + 1], j ::= j + 1],
            when (lt idx (ld (lay + 144))) (field idx)]] [
        ifElse (eq kind 4) [q ::= ld (lay + 96), s ::= start, e ::= ld (lay + 88), r ::= 1] [
        when (eq kind 5) [q ::= ld (lay + 96), s ::= start + ld4 (data + start + 4 * i),
          -- A body runs to the next offset, and the last to the end.
          ifElse (lt (i + 1) cnt) [e ::= start + ld4 (data + start + 4 * i + 4)] [e ::= ld (lay + 88)],
          r ::= 1]]]]]],
      when r [st out q, st (out + 8) s, st (out + 16) e]] }
end ProveSlot

namespace ProveLeaves
/-- The layout record. -/
abbrev lay : Var := ⟨0⟩
/-- The first leaf. -/
abbrev first : Var := ⟨1⟩
/-- The leaf past the last. -/
abbrev last : Var := ⟨2⟩
/-- Where the nodes go. -/
abbrev buf : Var := ⟨3⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨4⟩
/-- How many leaves. -/
abbrev cnt : Var := ⟨5⟩
/-- What sits under the tree. -/
abbrev kind : Var := ⟨6⟩
/-- The encoding's address. -/
abbrev data : Var := ⟨7⟩
/-- Where the packed bytes start. -/
abbrev a : Var := ⟨8⟩
/-- How many packed bytes there are. -/
abbrev n : Var := ⟨9⟩
/-- The first packed byte copied. -/
abbrev lo : Var := ⟨10⟩
/-- The packed byte past the last copied. -/
abbrev hi : Var := ⟨11⟩
/-- How many packed bytes are copied. -/
abbrev bytes : Var := ⟨12⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨13⟩
/-- A loop index. -/
abbrev i : Var := ⟨14⟩
/-- Where one value's plan node and range go. -/
abbrev sl : Var := ⟨15⟩

/--
The leaves of a tree from one position to another, as nodes: arguments lay, first, last, buf, ctx.

Returns how many leaves there are, after the last is cut to the tree's own count.
The nodes go to buf, with room for one more, and the bytes after them are scratch.
-/
def fn : Fn :=
  { params := 5, vars := 16, result := cnt,
    body := .block [when (lt (ld (lay + 8)) last) [last ::= ld (lay + 8)], cnt ::= 0,
      when (lt first last) [cnt ::= last - first], kind ::= ld lay, data ::= ld (lay + 72),
      ifElse (eq kind 0)
        [a ::= ld (lay + 80), n ::= ld (lay + 88) - a, lo ::= 0, bytes ::= 0,
          when cnt [lo ::= 32 * first, hi ::= 32 * (first + cnt), when (lt n hi) [hi ::= n],
            when (lt lo hi) [bytes ::= hi - lo]],
          callInto sink "ssz_gather" [buf, data + a + lo, 1, bytes, 0, 32 * cnt + 32 - bytes],
          -- A bit list's delimiter is cleared where its byte is copied.
          when (ld (lay + 104) &&& ne bytes 0 &&& eq (lo + bytes) n)
            [st1 (buf + bytes - 1) (ld1 (buf + bytes - 1) &&& (255 ^^^ ld (lay + 112)))]]
        -- Plain values one width apart are rooted together, as columns.
        [ifElse (eq kind 1 &&& ld (lay + 112))
          -- The chunked driver roots at least one value, so an empty span calls nothing.
          [when cnt [callInto sink "ssz_roots_chunked"
            [ld (lay + 96), data + ld (lay + 80) + ld (lay + 104) * first, ld (lay + 104), cnt, buf, ctx]]]
          [sl ::= buf + 32 * cnt + 32, i ::= 0,
            while_ (lt i cnt) [callInto sink "ssz_prove_slot" [lay, first + i, sl],
              ifElse sink
                [callInto sink "ssz_root_of"
                  [ld sl, data + ld (sl + 8), ld (sl + 16) - ld (sl + 8), buf + 32 * i, sl + 32, ctx]]
                (zero32 (buf + 32 * i)),
              i ::= i + 1]]]] }
end ProveLeaves

namespace ProveSpineWalk
/-- How many leaves the spine holds. -/
abbrev count : Var := ⟨0⟩
/-- The index walked. -/
abbrev index : Var := ⟨1⟩
/-- Its turns still to take. -/
abbrev depth : Var := ⟨2⟩
/-- The first leaf of the current level. -/
abbrev start : Var := ⟨3⟩
/-- The leaves the current level holds. -/
abbrev cap : Var := ⟨4⟩
/-- Where the stop goes. -/
abbrev out : Var := ⟨5⟩
/-- The answer: zero, or the refusal. -/
abbrev r : Var := ⟨6⟩
/-- One when the walk turned off the spine. -/
abbrev turned : Var := ⟨7⟩
/-- One while the walk goes on. -/
abbrev going : Var := ⟨8⟩
/-- Two to the current turn's position. -/
abbrev pw : Var := ⟨9⟩

/--
The walk down a progressive spine, one turn per level: arguments count, index, depth, start, cap, out.

Answers zero and writes the turns left, the first leaf and the capacity of the level reached, and one when the walk
turned off the spine, or answers 15 for a level past the end.
-/
def fn : Fn :=
  { params := 6, vars := 10, result := r,
    body := .block [r ::= 0, turned ::= 0, going ::= 1,
      while_ going [
        ifElse (eq depth 0) [going ::= 0]
          [ifElse (le count start) [r ::= 15, going ::= 0]
            [depth ::= depth - 1, callInto pw "ssz_prove_pow2" [depth],
              -- A clear bit turns left, into the level's own subtree.
              ifElse (eq (index &&& pw) 0) [turned ::= 1, going ::= 0]
                [start ::= start + cap, cap ::= cap * 4]]]],
      st out depth, st (out + 8) start, st (out + 16) cap, st (out + 24) turned] }
end ProveSpineWalk

namespace ProveSpine
/-- The first node's address. -/
abbrev nodes : Var := ⟨0⟩
/-- How many nodes. -/
abbrev count : Var := ⟨1⟩
/-- The first subtree's capacity. -/
abbrev width : Var := ⟨2⟩
/-- Where the root goes. -/
abbrev out : Var := ⟨3⟩
/-- The scratch buffer. -/
abbrev scratch : Var := ⟨4⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨5⟩
/-- How many subtrees the spine holds. -/
abbrev k : Var := ⟨6⟩
/-- The first node of the current subtree. -/
abbrev start : Var := ⟨7⟩
/-- The current subtree's depth. -/
abbrev lg : Var := ⟨8⟩
/-- The current subtree's node count. -/
abbrev here : Var := ⟨9⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨10⟩
/-- A loop index. -/
abbrev i : Var := ⟨11⟩

/--
The root of a progressive tree whose first subtree has a given capacity: arguments nodes, count, width, out,
scratch, ctx.

The capacity is a power of four.
Subtree i goes into the left half of pair i of an area at the scratch, and the right half of pair i is the spine below
it, so the spine folds from its last pair up.
-/
def fn : Fn :=
  { params := 6, vars := 12, result := 0,
    body := .block [k ::= 0, start ::= 0, callInto lg "ssz_branch_level" [width],
      while_ (lt start count) [here ::= count - start, when (lt width here) [here ::= width],
        callInto sink "ssz_merkleize"
          [nodes + 32 * start, here, lg, scratch + 64 * k, scratch + (RootProgressive.spineBytes : Nat), ctx],
        k ::= k + 1, start ::= start + width, width ::= 4 * width, lg ::= lg + 2],
      ifElse (eq k 0) (zero32 out)
        -- The spine closes with a zero node.
        (zero32 (scratch + 64 * k - 32) ++ [i ::= k - 1,
          while_ (lt 0 i) [
            callInto sink "ssz_hash_pairs" [scratch + 64 * i - 32, scratch + 64 * i, scratch + 64 * i + 32, 1, ctx],
            i ::= i - 1],
          callInto sink "ssz_hash_pairs" [out, scratch, scratch + 32, 1, ctx]])] }
end ProveSpine

namespace ProveBounded
/-- The layout record. -/
abbrev lay : Var := ⟨0⟩
/-- The index walked. -/
abbrev index : Var := ⟨1⟩
/-- Its turns still to take. -/
abbrev depth : Var := ⟨2⟩
/-- The first leaf of the subtree. -/
abbrev from_ : Var := ⟨3⟩
/-- The subtree's capacity. -/
abbrev cap : Var := ⟨4⟩
/-- Where the node goes. -/
abbrev out : Var := ⟨5⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨6⟩
/-- The scratch past the record. -/
abbrev free : Var := ⟨7⟩
/-- The subtree's depth. -/
abbrev td : Var := ⟨8⟩
/-- The levels of the node's own tree, or the turns left inside one leaf. -/
abbrev k : Var := ⟨9⟩
/-- The turns taken inside the subtree. -/
abbrev below : Var := ⟨10⟩
/-- The leaves the node spans. -/
abbrev span : Var := ⟨11⟩
/-- How many leaves the layout holds. -/
abbrev count : Var := ⟨12⟩
/-- The node's first leaf, from the subtree's first. -/
abbrev off : Var := ⟨13⟩
/-- The node's first leaf. -/
abbrev first : Var := ⟨14⟩
/-- The leaf past the node's last. -/
abbrev last : Var := ⟨15⟩
/-- How many leaves were laid out. -/
abbrev cnt : Var := ⟨16⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨17⟩
/-- The answer. -/
abbrev r : Var := ⟨18⟩
/-- The leaf the walk enters. -/
abbrev leaf : Var := ⟨19⟩
/-- A power of two. -/
abbrev pw : Var := ⟨20⟩
/-- The child's job. -/
abbrev env : Var := ⟨21⟩

/--
The root of a node of a bounded subtree, or of a node inside one of its leaves: arguments lay, index, depth, from,
cap.

Answers zero with the node written where the record says, or the code of the refusal.
-/
def fn : Fn :=
  { params := 5, vars := 22, result := r,
    body := .block [out ::= ld (lay + 128), ctx ::= ld (lay + 136), free ::= ld (lay + 120), count ::= ld (lay + 8),
      r ::= 0, callInto td "ssz_depth_for" [cap],
      ifElse (le depth td)
        [k ::= td - depth, callInto pw "ssz_prove_pow2" [depth], below ::= index &&& (pw - 1),
          -- Each turn halves the run of leaves a node spans; a span of a whole word has no first leaf past zero.
          callInto span "ssz_prove_pow2" [k], off ::= below * span,
          first ::= count, when (lt off count) [first ::= from_ + off],
          last ::= count, when (lt k 64 &&& lt first count) [when (lt span (count - first)) [last ::= first + span]],
          callInto cnt "ssz_prove_leaves" [lay, first, last, free, ctx],
          callInto sink "ssz_merkleize" [free, cnt, k, out, free + 32 * cnt + 32, ctx]]
        -- Past the bottom of the subtree, the remaining turns are read inside one leaf.
        [ifElse (eq (ld lay) 0) [r ::= 13]
          [k ::= depth - td, callInto leaf "ssz_prove_shr" [index, k], callInto pw "ssz_prove_pow2" [td],
            leaf ::= from_ + (leaf &&& (pw - 1)), callInto sink "ssz_prove_slot" [lay, leaf, free],
            ifElse (eq sink 0) [r ::= 14]
              [callInto pw "ssz_prove_pow2" [k], env ::= free + 24, st env out, st (env + 8) (env + 24),
                st (env + 16) ctx,
                callInto r "ssz_prove_node_at"
                  [ld free, ld (lay + 72), ld (free + 8), ld (free + 16), pw + (index &&& (pw - 1)), env]]]]] }
end ProveBounded

namespace ProveProgressive
/-- The layout record. -/
abbrev lay : Var := ⟨0⟩
/-- The index walked. -/
abbrev index : Var := ⟨1⟩
/-- Its turns still to take. -/
abbrev depth : Var := ⟨2⟩
/-- The first leaf of the current level. -/
abbrev start : Var := ⟨3⟩
/-- The leaves the current level holds. -/
abbrev cap : Var := ⟨4⟩
/-- Where the node goes. -/
abbrev out : Var := ⟨5⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨6⟩
/-- The scratch past the record, where the walk's stop goes. -/
abbrev free : Var := ⟨7⟩
/-- The answer. -/
abbrev r : Var := ⟨8⟩
/-- How many leaves the rest of the spine holds. -/
abbrev cnt : Var := ⟨9⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨10⟩
/-- The capacity of the level reached. -/
abbrev c : Var := ⟨11⟩

/--
The root of a node of a progressive tree: arguments lay, index, depth, start, cap.

The walk either turns into a level's own subtree, or stops on the spine, whose node covers every level from there on.
-/
def fn : Fn :=
  { params := 5, vars := 12, result := r,
    body := .block [out ::= ld (lay + 128), ctx ::= ld (lay + 136), free ::= ld (lay + 120),
      callInto r "ssz_prove_spine_walk" [ld (lay + 8), index, depth, start, cap, free],
      when (eq r 0)
        [ifElse (ld (free + 24)) [callInto r "ssz_prove_bounded" [lay, index, ld free, ld (free + 8), ld (free + 16)]]
          [c ::= ld (free + 16), callInto cnt "ssz_prove_leaves" [lay, ld (free + 8), ld (lay + 8), free + 32, ctx],
            callInto sink "ssz_prove_spine" [free + 32, cnt, c, out, free + 32 * cnt + 64, ctx]]]] }
end ProveProgressive

namespace ProveNodeAt
/-- The type's plan node. -/
abbrev p : Var := ⟨0⟩
/-- The encoding's address. -/
abbrev data : Var := ⟨1⟩
/-- Where the value starts. -/
abbrev start : Var := ⟨2⟩
/-- Where it stops. -/
abbrev stop : Var := ⟨3⟩
/-- The generalized index. -/
abbrev index : Var := ⟨4⟩
/-- The job: where the node goes, the scratch, and the context. -/
abbrev env : Var := ⟨5⟩
/-- Where the node goes. -/
abbrev out : Var := ⟨6⟩
/-- The scratch. -/
abbrev scr : Var := ⟨7⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨8⟩
/-- The answer. -/
abbrev r : Var := ⟨9⟩
/-- The index's depth. -/
abbrev full : Var := ⟨10⟩
/-- The turns into the contents. -/
abbrev depth : Var := ⟨11⟩
/-- One when a word is mixed in. -/
abbrev mx : Var := ⟨12⟩
/-- Two to the depth. -/
abbrev pw : Var := ⟨13⟩
/-- The sink for results nobody reads. -/
abbrev sink : Var := ⟨14⟩

/--
The root of the node at a generalized index of the value a range of an accepted encoding holds: arguments plan,
data, start, stop, index, env.

The job at env holds three words: where the 32-byte node goes, the scratch, and the context.
Answers zero with the node written, or the code of the refusal.
-/
def fn : Fn :=
  { params := 6, vars := 15, result := r,
    body := .block [out ::= ld env, scr ::= ld (env + 8), ctx ::= ld (env + 16), r ::= 0,
      ifElse (eq index 0) [r ::= 3] [
      -- The root sits on no branch, but it is still a node.
      ifElse (eq index 1) [callInto sink "ssz_root_of" [p, data + start, stop - start, out, scr, ctx]]
        [callInto sink "ssz_prove_layout" [p, data, start, stop, scr], st (scr + 128) out, st (scr + 136) ctx,
          callInto full "ssz_branch_level" [index], mx ::= ld (scr + 32), depth ::= full - mx,
          callInto pw "ssz_prove_pow2" [depth],
          -- A mixed-in word is the right child, which puts the contents one level down on the left.
          ifElse (mx &&& ne (index &&& pw) 0)
            [ifElse (ne depth 0) [r ::= 12] (copy32 out (scr + 40))]
            [ifElse (ld (scr + 16)) [callInto r "ssz_prove_bounded" [scr, index, depth, 0, ld (scr + 24)]]
              [callInto r "ssz_prove_progressive" [scr, index, depth, 0, 1]]]]]] }
end ProveNodeAt

namespace ProveNode
/-- The job the caller filled. -/
abbrev job : Var := ⟨0⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨1⟩
/-- The answer. -/
abbrev r : Var := ⟨2⟩
/-- The scratch, which starts with the walk's job. -/
abbrev scr : Var := ⟨3⟩

/--
The node at a generalized index of the value an accepted encoding holds: arguments job, ctx.

The job holds six words:

```text
    job + 0    the address of the type's plan
    job + 8    the address of the encoding
    job + 16   its size in bytes
    job + 24   the generalized index
    job + 32   where the 32-byte node goes
    job + 40   the address of a scratch area, apart from everything else
```
-/
def fn : Fn :=
  { params := 2, vars := 4, result := r,
    body := .block [scr ::= ld (job + 40), st scr (ld (job + 32)), st (scr + 8) (scr + 24), st (scr + 16) ctx,
      callInto r "ssz_prove_node_at" [ld job, ld (job + 8), 0, ld (job + 16), ld (job + 24), scr]] }
end ProveNode

namespace ProveBranch
/-- The job the caller filled. -/
abbrev job : Var := ⟨0⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨1⟩
/-- The answer. -/
abbrev r : Var := ⟨2⟩
/-- The scratch, which starts with the walk's job. -/
abbrev scr : Var := ⟨3⟩
/-- The index. -/
abbrev index : Var := ⟨4⟩
/-- Its depth, the branch's length. -/
abbrev depth : Var := ⟨5⟩
/-- The path node whose sibling comes next. -/
abbrev node : Var := ⟨6⟩
/-- The branch node being written. -/
abbrev j : Var := ⟨7⟩

/--
The branch authenticating one generalized index of the value an accepted encoding holds: arguments job, ctx.

The job holds six words:

```text
    job + 0    the address of the type's plan
    job + 8    the address of the encoding
    job + 16   its size in bytes
    job + 24   the generalized index
    job + 32   where the branch goes, 32 bytes per node, from the leaf upward, as many as the index's depth
    job + 40   the address of a scratch area, apart from everything else
```
-/
def fn : Fn :=
  { params := 2, vars := 8, result := r,
    body := .block [r ::= 0, index ::= ld (job + 24), scr ::= ld (job + 40),
      ifElse (eq index 0) [r ::= 3] [
      ifElse (eq index 1) [r ::= 4]
        [callInto depth "ssz_branch_level" [index], node ::= index, j ::= 0,
          -- The siblings of the path's nodes, from the leaf up, each walked from the root.
          while_ (lt j depth &&& eq r 0) [st scr (ld (job + 32) + 32 * j), st (scr + 8) (scr + 24),
            st (scr + 16) ctx,
            callInto r "ssz_prove_node_at" [ld job, ld (job + 8), 0, ld (job + 16), node ^^^ 1, scr],
            node ::= .shr node 1, j ::= j + 1]]]] }
end ProveBranch

namespace ProveMultiproof
/-- The job the caller filled. -/
abbrev job : Var := ⟨0⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨1⟩
/-- The answer. -/
abbrev r : Var := ⟨2⟩
/-- The scratch. -/
abbrev scr : Var := ⟨3⟩
/-- How many indices. -/
abbrev count : Var := ⟨4⟩
/-- Where the helper indices go. -/
abbrev helpers : Var := ⟨5⟩
/-- How many helper indices. -/
abbrev n : Var := ⟨6⟩
/-- The walk's job. -/
abbrev env : Var := ⟨7⟩
/-- The helper node being written. -/
abbrev i : Var := ⟨8⟩

/--
The nodes authenticating several generalized indices of the value an accepted encoding holds: arguments job, ctx.

The job holds eight words:

```text
    job + 0    the address of the type's plan
    job + 8    the address of the encoding
    job + 16   its size in bytes
    job + 24   the address of the generalized indices, 8 bytes each
    job + 32   how many indices
    job + 40   where the nodes go, 32 bytes each, at most 63 per index
    job + 48   the address of a scratch area, apart from everything else
    job + 56   written: how many nodes, once the helper indices are accepted
```

The nodes are those of the helper indices, largest index first.
The scratch takes 8 + 1536 n bytes for n indices before what one node's walk needs.
-/
def fn : Fn :=
  { params := 2, vars := 9, result := r,
    body := .block [count ::= ld (job + 32), scr ::= ld (job + 48), helpers ::= scr + 8 + 1024 * count,
      callInto r "ssz_branch_helpers" [ld (job + 24), count, scr + 8, helpers, scr],
      when (eq r 0) [n ::= ld scr, st (job + 56) n, env ::= helpers + 512 * count, i ::= 0,
        while_ (lt i n &&& eq r 0) [st env (ld (job + 40) + 32 * i), st (env + 8) (env + 24), st (env + 16) ctx,
          callInto r "ssz_prove_node_at" [ld job, ld (job + 8), 0, ld (job + 16), ld (helpers + 8 * i), env],
          i ::= i + 1]]] }
end ProveMultiproof

mutual

/--
The scratch a walk spends on a value one at a time, along any path into a type: its fixed-size root, a node per child,
and the most any child spends.

A chunk of one value needs its own fixed-size root, which may pass what its parent's root needs, so every type on the
path counts.
-/
def deepNeed : Desc → Nat
  | .vector element length => sadd (sadd (rootsNeed (.vector element length) 1) 32) (deepNeed element)
  | .list element limit => sadd (sadd (rootsNeed (.list element limit) 1) 32) (deepNeed element)
  | .progressiveList element limit =>
    sadd (sadd (rootsNeed (.progressiveList element limit) 1) 32) (deepNeed element)
  | .container names fields =>
    sadd (sadd (rootsNeed (.container names fields) 1) (smul 32 (sat fields.length))) (deepMost fields 0)
  | .progressiveContainer active names fields =>
    sadd (sadd (rootsNeed (.progressiveContainer active names fields) 1) (smul 32 (sat fields.length)))
      (deepMost fields 0)
  | .compatibleUnion selectors options =>
    sadd (sadd (rootsNeed (.compatibleUnion selectors options) 1) (smul 32 (sat options.length)))
      (deepMost options 0)
  | d => rootsNeed d 1

/-- The most any of several types spends, after a most so far. -/
def deepMost : List Desc → Nat → Nat
  | [], most => most
  | field :: rest, most => deepMost rest (max (deepNeed field) most)

end

/--
The scratch bytes one node's walk over an encoding of a size needs, saturated at the cap.

Twice the most of the root's scratch and the path's, then a node per byte of the encoding for the leaves, then one
mebibyte for the records and the jobs of up to 64 levels.
-/
def proveScratch (d : Desc) (size : Nat) : Nat :=
  let most := max (rootScratch d size) (deepNeed d)
  sadd (sadd (sadd most most) (smul 32 (sat size))) (2 ^ 20)

namespace ProveDeep
/-- The type's plan node. -/
abbrev p : Var := ⟨0⟩
/-- The node's tag. -/
abbrev tag : Var := ⟨1⟩
/-- The bound. -/
abbrev r : Var := ⟨2⟩
/-- The children's most. -/
abbrev t : Var := ⟨3⟩
/-- A partial bound. -/
abbrev x : Var := ⟨4⟩
/-- How many children, saturated. -/
abbrev n : Var := ⟨5⟩
/-- How many children to visit. -/
abbrev k : Var := ⟨6⟩
/-- The current child node. -/
abbrev q : Var := ⟨7⟩
/-- A loop index. -/
abbrev i : Var := ⟨8⟩
/-- A layout length. -/
abbrev ks : Var := ⟨9⟩

/-- The most any of a count of child nodes spends, from the current child on. -/
def children : List Stmt :=
  [n ::= k, i ::= 0,
    while_ (lt i k) [callInto x "ssz_prove_deep" [q], maxIn t x t, callInto q "ssz_plan_next" [q], i ::= i + 1]]

/-- The children's count and most, by the node's kind. -/
def kinds : Stmt :=
  ifElse (eq tag 7 ||| eq tag 8) [n ::= 1, callInto t "ssz_prove_deep" [p + 16]] [
  ifElse (eq tag 9) [n ::= 1, callInto t "ssz_prove_deep" [p + 24]] [
  ifElse (eq tag 10) ([k ::= ld (p + 8), q ::= p + 16] ++ children) [
  ifElse (eq tag 11) ([ks ::= ld (p + 8), q ::= p + 16 + 8 * ks, k ::= ld q, q ::= q + 8] ++ children) [
  when (eq tag 12) ([k ::= ld (p + 8), q ::= p + 16 + 8 * k] ++ children)]]]]

/-- The node's tag, then the children's count and most. -/
def head : List Stmt :=
  [tag ::= ld p, t ::= 0, n ::= 0, kinds]

/-- The node's own fixed-size root, a node per child, and the children's most. -/
def tail : List Stmt :=
  [callInto r "ssz_scratch_roots" [p, 1], satIn n, smulIn x 32 n] ++ saddIn r r x ++ saddIn r r t

/-- The scratch a walk spends on values along any path into a type, saturated at the cap: argument the plan node. -/
def fn : Fn :=
  { params := 1, vars := 10, result := r, body := .block (head ++ tail) }
end ProveDeep

namespace ProveScratch
/-- The type's plan. -/
abbrev p : Var := ⟨0⟩
/-- The size of the encoding. -/
abbrev size : Var := ⟨1⟩
/-- The bound. -/
abbrev r : Var := ⟨2⟩
/-- A partial bound. -/
abbrev t : Var := ⟨3⟩

/--
The scratch bytes one node's walk over an encoding of a size needs, saturated at the cap: arguments plan and size.

Twice the most of the root's scratch and the path's, then a node per byte of the encoding for the leaves, then one
mebibyte for the records and the jobs of up to 64 levels.
-/
def fn : Fn :=
  { params := 2, vars := 4, result := r,
    body := .block ([callInto r "ssz_root_scratch" [p, size], callInto t "ssz_prove_deep" [p], maxIn r r t] ++
      saddIn r r r ++ [satIn size, smulIn t 32 size] ++ saddIn r r t ++ saddIn r r ((2 ^ 20 : Nat) : Expr)) }
end ProveScratch

/-- The proving drivers, each under its exported name. -/
def proveFns : List (String × Fn) :=
  [("ssz_prove_pow2", ProvePow2.fn), ("ssz_prove_shr", ProveShr.fn), ("ssz_prove_layout", ProveLayout.fn),
    ("ssz_prove_slot", ProveSlot.fn), ("ssz_prove_leaves", ProveLeaves.fn),
    ("ssz_prove_spine_walk", ProveSpineWalk.fn), ("ssz_prove_spine", ProveSpine.fn),
    ("ssz_prove_bounded", ProveBounded.fn), ("ssz_prove_progressive", ProveProgressive.fn),
    ("ssz_prove_node_at", ProveNodeAt.fn), ("ssz_prove_node", ProveNode.fn), ("ssz_prove_branch", ProveBranch.fn),
    ("ssz_prove_multiproof", ProveMultiproof.fn), ("ssz_prove_deep", ProveDeep.fn),
    ("ssz_prove_scratch", ProveScratch.fn)]

/-- Every proving driver fits the compiler's assumptions. -/
theorem proveFns_wf : proveFns.all (fun f => f.2.wf) = true := by
  decide +kernel

end EthLib.Consensus.Ssz.Native.Driver
