import SszNative.Ir.Dsl
import SszNative.Ir.Wf

/-!
Deserialization and serialization one layer at a time, on byte buffers, walking a plan.

A driver receives the address of a plan node, as `SszNative/Plan.lean` writes it, and never builds a value.

    ssz_ranges(plan, data, len, start, stop, out)
        the range [start, stop) of the buffer at data, len bytes long, holds a composite's encoding:
        its parts' ranges are written to out, as deserialization would cut them
    ssz_assemble(plan, parts, count, out, outCap)
        parts holds count pairs of words, the address and the size of each part's encoding:
        the composite's encoding is written to out, as serialization would lay it out

The ranges are written as words:

```text
    out + 0             on entry, how many ranges fit; on success, how many there are
    out + 8 + 16 i      where range i starts
    out + 16 + 16 i     where range i stops
```

The ranges answer zero on success, one for an encoding deserialization refuses, two when the ranges do not fit, and
three for a type with no parts.

Assembly answers the encoding's size on success, or one of the codes of `assembleCode`, all far above any size.
A union's parts are its selector byte, then the option's encoding.
A bit list's are one part, its bits packed lowest first with the padding clear, and count is its bit count.
A byte array's are its bytes, cut anywhere.

Words read from a plan are the plan's numbers; a width no fixed-size type has stands for a variable size.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt
open EthLib.Consensus.Ssz.Native.Asm (Width)

/-- The word standing for a variable size, or for no bound. -/
abbrev none64 : Nat := 2 ^ 64 - 1

/-- The size four-byte offsets cannot name. -/
abbrev offsetLimit : Nat := 2 ^ 32

/-- Four bytes stored at an address. -/
def st4 (a v : Expr) : Stmt := .store .b4 a v

/-- A plan word, a number of words after an address. -/
def word (p : Expr) (k : Nat) : Expr := ld (p + ((8 * k : Nat) : Expr))

namespace Next
/-- The plan node. -/
def p : Var := ⟨0⟩
/-- Its tag. -/
def tag : Var := ⟨1⟩
/-- A count of words or of nodes. -/
def n : Var := ⟨2⟩
/-- The answer. -/
def q : Var := ⟨3⟩
end Next

/-- The address right after a plan node: argument the node. -/
def planNext : Fn :=
  open Next in
  { params := 1, vars := 4, result := q,
    body := .block [tag ::= ld p,
      ifElse (eq tag 0) [q ::= p + 8]
      -- The scalar and byte or bit array tags carry one word.
      [ifElse (lt tag 6) [q ::= p + 16]
      [ifElse (eq tag 6) [q ::= p + 24]
      -- A vector or a list: a word, then the element node.
      [ifElse (lt tag 9) [callInto q "ssz_plan_next" [p + 16]]
      [ifElse (eq tag 9) [callInto q "ssz_plan_next" [p + 24]]
      [ifElse (eq tag 10) [callInto q "ssz_plan_skip" [p + 16, word p 1]]
      -- A progressive container: its layout bits, then its field count and fields.
      [ifElse (eq tag 11) [n ::= word p 1, callInto q "ssz_plan_skip" [p + 24 + 8 * n, ld (p + 16 + 8 * n)]]
      -- A union: its selectors, then its options.
      [n ::= word p 1, callInto q "ssz_plan_skip" [p + 16 + 8 * n, n]]]]]]]]] }

namespace Skip
/-- The first node. -/
def q : Var := ⟨0⟩
/-- How many nodes. -/
def n : Var := ⟨1⟩
/-- Nodes skipped so far. -/
def i : Var := ⟨2⟩
end Skip

/-- The address right after a number of plan nodes: arguments the first node and the count. -/
def planSkip : Fn :=
  open Skip in
  { params := 2, vars := 3, result := q,
    body := .block [i ::= 0, while_ (lt i n) [callInto q "ssz_plan_next" [q], i ::= i + 1]] }

namespace Width_
/-- The plan node. -/
def p : Var := ⟨0⟩
/-- Its tag. -/
def tag : Var := ⟨1⟩
/-- The answer. -/
def w : Var := ⟨2⟩
/-- The element's width. -/
def e : Var := ⟨3⟩
/-- The layout length of a progressive container. -/
def k : Var := ⟨4⟩
end Width_

/-- The width of a fixed-size type, or the word for a variable size: argument the node. -/
def planWidth : Fn :=
  open Width_ in
  { params := 1, vars := 5, result := w,
    body := .block [tag ::= ld p, w ::= (none64 : Expr),
      ifElse (eq tag 0) [w ::= 1]
      [ifElse (le tag 2) [w ::= word p 1]
      [ifElse (eq tag 4) [w ::= (word p 1 + 7) / 8]
      -- A vector of fixed-size elements is as wide as its elements together.
      [ifElse (eq tag 7) [callInto e "ssz_plan_width" [p + 16], when (ne e (none64 : Expr)) [w ::= e * word p 1]]
      [ifElse (eq tag 10) [callInto w "ssz_plan_fields_width" [p + 16, word p 1]]
      [when (eq tag 11) [k ::= word p 1, callInto w "ssz_plan_fields_width" [p + 24 + 8 * k, ld (p + 16 + 8 * k)]]]]]]]] }

namespace Fields
/-- The first field node. -/
def q : Var := ⟨0⟩
/-- How many fields. -/
def n : Var := ⟨1⟩
/-- The fields counted so far. -/
def i : Var := ⟨2⟩
/-- The width so far, or the word for a variable size. -/
def total : Var := ⟨3⟩
/-- One field's width. -/
def w : Var := ⟨4⟩
end Fields

/-- The width of fields that are all fixed-size, or the word for a variable size: arguments the first node, the count. -/
def planFieldsWidth : Fn :=
  open Fields in
  { params := 2, vars := 5, result := total,
    body := .block [i ::= 0, total ::= 0,
      while_ (lt i n &&& ne total (none64 : Expr)) [callInto w "ssz_plan_width" [q],
        -- One variable field leaves the whole struct variable.
        ifElse (eq w (none64 : Expr)) [total ::= (none64 : Expr)]
          [total ::= total + w, callInto q "ssz_plan_next" [q], i ::= i + 1]]] }

/-- The width of a struct's fixed part, an offset standing for each variable field: arguments the first node, count. -/
def planLeading : Fn :=
  open Fields in
  { params := 2, vars := 5, result := total,
    body := .block [i ::= 0, total ::= 0,
      while_ (lt i n) [callInto w "ssz_plan_width" [q],
        ifElse (eq w (none64 : Expr)) [total ::= total + 4] [total ::= total + w],
        callInto q "ssz_plan_next" [q], i ::= i + 1]] }

namespace Stride
/-- Where the first element starts. -/
def start : Var := ⟨0⟩
/-- Each element's width. -/
def w : Var := ⟨1⟩
/-- How many elements. -/
def count : Var := ⟨2⟩
/-- The output. -/
def out : Var := ⟨3⟩
/-- The answer. -/
def r : Var := ⟨4⟩
/-- The element being written. -/
def i : Var := ⟨5⟩
end Stride

/-- The ranges of elements one width apart: arguments the start, the width, the count, the output. -/
def strideRanges : Fn :=
  open Stride in
  { params := 4, vars := 6, result := r,
    body := .block [r ::= 2,
      when (le count (ld out)) [i ::= 0,
        while_ (lt i count) [st (out + 8 + 16 * i) (start + i * w), st (out + 16 + 16 * i) (start + (i + 1) * w),
          i ::= i + 1],
        st out count, r ::= 0]] }

namespace Offsets
/-- The buffer. -/
def data : Var := ⟨0⟩
/-- Where the composite starts. -/
def start : Var := ⟨1⟩
/-- Where it stops. -/
def stop : Var := ⟨2⟩
/-- How many offsets. -/
def count : Var := ⟨3⟩
/-- The output. -/
def out : Var := ⟨4⟩
/-- The answer. -/
def r : Var := ⟨5⟩
/-- The offset being read. -/
def i : Var := ⟨6⟩
/-- Whether the offsets are in order so far. -/
def ok : Var := ⟨7⟩
/-- The offset read. -/
def o : Var := ⟨8⟩
/-- Where its body ends. -/
def next : Var := ⟨9⟩
/-- The composite's size. -/
def size : Var := ⟨10⟩
end Offsets

/--
The bodies an offset table opens: arguments the buffer, the start, the stop, the count, the output.

The table is checked whole before any range is written: each body ends where the next begins, the last at the stop.
-/
def offsetRanges : Fn :=
  open Offsets in
  -- Where body i ends: at the next offset, or at the end for the last one.
  let ending : Stmt := ifElse (lt (i + 1) count) [next ::= ld4 (data + start + 4 * (i + 1))] [next ::= size]
  { params := 5, vars := 11, result := r,
    body := .block [size ::= stop - start, r ::= 1, ok ::= 1, i ::= 0,
      while_ (lt i count &&& ok) [o ::= ld4 (data + start + 4 * i), ending,
        when (lt next o) [ok ::= 0], i ::= i + 1],
      when ok [r ::= 2,
        when (le count (ld out)) [i ::= 0,
          while_ (lt i count) [o ::= ld4 (data + start + 4 * i), ending,
            st (out + 8 + 16 * i) (start + o), st (out + 16 + 16 * i) (start + next), i ::= i + 1],
          st out count, r ::= 0]]] }

namespace SeqV
/-- The element's plan node. -/
def e : Var := ⟨0⟩
/-- The buffer. -/
def data : Var := ⟨1⟩
/-- Where the composite starts. -/
def start : Var := ⟨2⟩
/-- Where it stops. -/
def stop : Var := ⟨3⟩
/-- The vector's length, or the list's limit. -/
def n : Var := ⟨4⟩
/-- The output. -/
def out : Var := ⟨5⟩
/-- The answer. -/
def r : Var := ⟨6⟩
/-- The composite's size. -/
def size : Var := ⟨7⟩
/-- The element's width. -/
def w : Var := ⟨8⟩
/-- The first offset. -/
def first : Var := ⟨9⟩
/-- How many elements. -/
def count : Var := ⟨10⟩
end SeqV

/-- The ranges of a vector's elements: arguments the element node, buffer, start, stop, length, output. -/
def vectorView : Fn :=
  open SeqV in
  { params := 6, vars := 11, result := r,
    body := .block [size ::= stop - start, r ::= 1,
      when (lt size (offsetLimit : Expr)) [callInto w "ssz_plan_width" [e],
        ifElse (ne w (none64 : Expr))
          [when (eq size (w * n)) [callInto r "ssz_stride_ranges" [start, w, n, out]]]
          -- Variable elements: a table of one offset each, the first one its own width.
          [when (le (n * 4) size)
            [ifElse (eq n 0) [callInto r "ssz_stride_ranges" [start, 0, 0, out]]
              [when (eq (ld4 (data + start)) (n * 4)) [callInto r "ssz_offset_ranges" [data, start, stop, n, out]]]]]]] }

/-- The ranges of a list's elements: arguments the element node, buffer, start, stop, limit, output. -/
def listView : Fn :=
  open SeqV in
  { params := 6, vars := 11, result := r,
    body := .block [size ::= stop - start, r ::= 1,
      when (lt size (offsetLimit : Expr))
        [ifElse (eq size 0) [callInto r "ssz_stride_ranges" [start, 0, 0, out]]
          [callInto w "ssz_plan_width" [e],
            ifElse (ne w (none64 : Expr))
              -- Fixed-size elements: as many as fit, which must be a whole number within the limit.
              [when (ne w 0) [when (eq (size % w) 0) [count ::= size / w,
                when (le count n) [callInto r "ssz_stride_ranges" [start, w, count, out]]]]]
              -- Variable elements: the first offset is the table's width, so it gives the count.
              [when (le 4 size) [first ::= ld4 (data + start),
                when (le 4 first &&& eq (first % 4) 0 &&& le first size) [count ::= first / 4,
                  when (le count n) [callInto r "ssz_offset_ranges" [data, start, stop, count, out]]]]]]]] }

namespace Struct
/-- The first field node. -/
def q : Var := ⟨0⟩
/-- The buffer. -/
def data : Var := ⟨1⟩
/-- Where the struct starts. -/
def start : Var := ⟨2⟩
/-- Where it stops. -/
def stop : Var := ⟨3⟩
/-- How many fields. -/
def n : Var := ⟨4⟩
/-- The output. -/
def out : Var := ⟨5⟩
/-- The answer. -/
def r : Var := ⟨6⟩
/-- The struct's size. -/
def size : Var := ⟨7⟩
/-- The fixed part's width. -/
def leading : Var := ⟨8⟩
/-- Whether the struct is accepted so far. -/
def ok : Var := ⟨9⟩
/-- The field being read. -/
def i : Var := ⟨10⟩
/-- Its plan node. -/
def f : Var := ⟨11⟩
/-- Its width. -/
def w : Var := ⟨12⟩
/-- Where it sits in the fixed part. -/
def pos : Var := ⟨13⟩
/-- The offset of a variable field. -/
def o : Var := ⟨14⟩
/-- The previous offset, or the word for none yet. -/
def prev : Var := ⟨15⟩
/-- The width of the whole struct, or the word for a variable size. -/
def fixed : Var := ⟨16⟩
end Struct

/--
The ranges of a struct's fields: arguments the first field node, buffer, start, stop, field count, output.

The budget comes first, then the offsets as a whole, and only then is any range written.
-/
def fieldsView : Fn :=
  open Struct in
  { params := 6, vars := 17, result := r,
    body := .block [size ::= stop - start, r ::= 1,
      when (lt size (offsetLimit : Expr)) [callInto fixed "ssz_plan_fields_width" [q, n],
        ifElse (ne fixed (none64 : Expr)) [leading ::= fixed, ok ::= eq size fixed]
          [callInto leading "ssz_plan_leading" [q, n], ok ::= le leading size],
        -- The offsets: the first at the end of the fixed part, each at least the one before.
        i ::= 0, f ::= q, pos ::= 0, prev ::= (none64 : Expr),
        while_ (lt i n &&& ok) [callInto w "ssz_plan_width" [f],
          ifElse (ne w (none64 : Expr)) [pos ::= pos + w]
            [o ::= ld4 (data + start + pos),
              ifElse (eq prev (none64 : Expr)) [ok ::= eq o leading] [ok ::= le prev o],
              prev ::= o, pos ::= pos + 4],
          callInto f "ssz_plan_next" [f], i ::= i + 1],
        -- The last body ends at the end, so the last offset is no further.
        when (ok &&& ne prev (none64 : Expr)) [ok ::= le prev size],
        when ok [r ::= 2,
          when (le n (ld out)) [i ::= 0, f ::= q, pos ::= 0, prev ::= (none64 : Expr),
            while_ (lt i n) [callInto w "ssz_plan_width" [f],
              ifElse (ne w (none64 : Expr))
                [st (out + 8 + 16 * i) (start + pos), st (out + 16 + 16 * i) (start + pos + w), pos ::= pos + w]
                -- A body runs from its offset to the next one, so it closes the body before it.
                [o ::= ld4 (data + start + pos), st (out + 8 + 16 * i) (start + o),
                  when (ne prev (none64 : Expr)) [st (out + 16 + 16 * prev) (start + o)],
                  prev ::= i, pos ::= pos + 4],
              callInto f "ssz_plan_next" [f], i ::= i + 1],
            when (ne prev (none64 : Expr)) [st (out + 16 + 16 * prev) stop],
            st out n, r ::= 0]]]] }

namespace View
/-- The plan node. -/
def plan : Var := ⟨0⟩
/-- The buffer. -/
def data : Var := ⟨1⟩
/-- Its size. -/
def len : Var := ⟨2⟩
/-- Where the composite starts. -/
def start : Var := ⟨3⟩
/-- Where it stops. -/
def stop : Var := ⟨4⟩
/-- The output. -/
def out : Var := ⟨5⟩
/-- The answer. -/
def r : Var := ⟨6⟩
/-- The tag. -/
def tag : Var := ⟨7⟩
/-- A bound, or a layout length. -/
def k : Var := ⟨8⟩
end View

/--
The ranges of a composite's parts: arguments the plan node, buffer, size, start, stop, output.

Zero on success, one for a refused encoding, two when the ranges do not fit, three for a type with no parts.
-/
def view : Fn :=
  open View in
  { params := 6, vars := 9, result := r,
    body := .block [r ::= 1,
      when (le start stop &&& le stop len) [tag ::= ld plan, r ::= 3,
        ifElse (eq tag 7) [callInto r "ssz_vector_ranges" [plan + 16, data, start, stop, word plan 1, out]]
        [ifElse (eq tag 8) [callInto r "ssz_list_ranges" [plan + 16, data, start, stop, word plan 1, out]]
        [ifElse (eq tag 9)
          [ifElse (eq (word plan 1) 0) [k ::= (none64 : Expr)] [k ::= word plan 2],
            callInto r "ssz_list_ranges" [plan + 24, data, start, stop, k, out]]
        [ifElse (eq tag 10) [callInto r "ssz_fields_ranges" [plan + 16, data, start, stop, word plan 1, out]]
        [ifElse (eq tag 11) [k ::= word plan 1,
            callInto r "ssz_fields_ranges" [plan + 24 + 8 * k, data, start, stop, ld (plan + 16 + 8 * k), out]]
        -- A union: the selector byte, then the rest.
        [when (eq tag 12) [r ::= 1,
          when (lt start stop) [r ::= 2,
            when (le 2 (ld out)) [st (out + 8) start, st (out + 16) (start + 1), st (out + 24) (start + 1),
              st (out + 32) stop, st out 2, r ::= 0]]]]]]]]]] }

/-- The code for parts whose encoding would need an offset four bytes cannot hold. -/
abbrev codeOverflow : Nat := 2 ^ 64 - 1
/-- The code for a count of parts, bytes, or bits the type does not allow. -/
abbrev codeCount : Nat := 2 ^ 64 - 2
/-- The code for a part of the wrong size for its fixed-size type. -/
abbrev codePart : Nat := 2 ^ 64 - 3
/-- The code for a selector the union does not allow. -/
abbrev codeSelector : Nat := 2 ^ 64 - 4
/-- The code for an output too small for the encoding. -/
abbrev codeCapacity : Nat := 2 ^ 64 - 5
/-- The code for a type assembly does not cover. -/
abbrev codeType : Nat := 2 ^ 64 - 6
/-- The code for packed bits with a padding bit set. -/
abbrev codePadding : Nat := 2 ^ 64 - 7

namespace Copy
/-- Where to. -/
def dst : Var := ⟨0⟩
/-- Where from. -/
def src : Var := ⟨1⟩
/-- How many bytes. -/
def n : Var := ⟨2⟩
/-- How many bytes are copied so far. -/
def i : Var := ⟨3⟩
/-- How many bytes the whole words cover. -/
def whole : Var := ⟨4⟩
end Copy

/--
Bytes copied: arguments where to, where from, how many.

Whole eight-byte words go first, then the few bytes left one at a time.
-/
def copyBytes : Fn :=
  open Copy in
  { params := 3, vars := 5, result := 0,
    body := .block [i ::= 0, whole ::= n - n % 8,
      while_ (lt i whole) [st (dst + i) (ld (src + i)), i ::= i + 8],
      while_ (lt i n) [st1 (dst + i) (ld1 (src + i)), i ::= i + 1]] }

namespace Bytes_
/-- The parts. -/
def parts : Var := ⟨0⟩
/-- How many. -/
def count : Var := ⟨1⟩
/-- The length, or the limit. -/
def n : Var := ⟨2⟩
/-- Whether the length is exact. -/
def exact : Var := ⟨3⟩
/-- The output. -/
def out : Var := ⟨4⟩
/-- Its capacity. -/
def cap : Var := ⟨5⟩
/-- The answer. -/
def r : Var := ⟨6⟩
/-- The part being read. -/
def i : Var := ⟨7⟩
/-- The size so far. -/
def total : Var := ⟨8⟩
/-- Whether the size passed what a word holds. -/
def wrap : Var := ⟨9⟩
/-- The size after one more part. -/
def sum : Var := ⟨10⟩
/-- A sink for copies. -/
def sink : Var := ⟨11⟩
end Bytes_

/--
The bytes of a byte array, joined from parts: arguments the parts, count, length or limit, whether exact, output, capacity.
-/
def joinBytes : Fn :=
  open Bytes_ in
  { params := 6, vars := 12, result := r,
    body := .block [total ::= 0, wrap ::= 0, i ::= 0,
      while_ (lt i count) [sum ::= total + ld (parts + 16 * i + 8), when (lt sum total) [wrap ::= 1],
        total ::= sum, i ::= i + 1],
      r ::= (codeCount : Expr),
      when (eq wrap 0)
        [ifElse exact [when (eq total n) [r ::= 0]] [when (le total n) [r ::= 0]],
          when (eq r 0) [r ::= (codeOverflow : Expr),
            when (lt total (offsetLimit : Expr)) [r ::= (codeCapacity : Expr),
              when (le total cap) [total ::= 0, i ::= 0,
                while_ (lt i count) [callInto sink "ssz_copy" [out + total, ld (parts + 16 * i), ld (parts + 16 * i + 8)],
                  total ::= total + ld (parts + 16 * i + 8), i ::= i + 1],
                r ::= total]]]]] }

namespace Lay
/-- The plan node of the first field, or of the element. -/
def q : Var := ⟨0⟩
/-- Whether every part has the one element type. -/
def same : Var := ⟨1⟩
/-- The parts. -/
def parts : Var := ⟨2⟩
/-- How many. -/
def count : Var := ⟨3⟩
/-- The output. -/
def out : Var := ⟨4⟩
/-- Its capacity. -/
def cap : Var := ⟨5⟩
/-- The answer. -/
def r : Var := ⟨6⟩
/-- The part being read. -/
def i : Var := ⟨7⟩
/-- Its type's plan node. -/
def f : Var := ⟨8⟩
/-- Its type's width. -/
def w : Var := ⟨9⟩
/-- Its size. -/
def len : Var := ⟨10⟩
/-- The fixed part's width. -/
def head : Var := ⟨11⟩
/-- The encoding's size so far. -/
def total : Var := ⟨12⟩
/-- Whether the size passed what a word holds. -/
def wrap : Var := ⟨13⟩
/-- The size after one more step. -/
def sum : Var := ⟨14⟩
/-- Where the next body goes. -/
def body : Var := ⟨15⟩
/-- A sink for copies. -/
def sink : Var := ⟨16⟩
end Lay

/--
Parts laid out as a struct or a sequence: arguments the type node, whether all parts share it, parts, count, output,
capacity.

The parts are checked whole, then the size, and only then is anything written.
-/
def layParts : Fn :=
  open Lay in
  -- The next part's type: the same one, or the next field.
  let advance : Stmt := when (eq same 0) [callInto f "ssz_plan_next" [f]]
  -- Grow the size by a step, noting when it passes what a word holds.
  let grow (step : Expr) : List Stmt := [sum ::= total + step, when (lt sum total) [wrap ::= 1], total ::= sum]
  { params := 6, vars := 17, result := r,
    body := .block [r ::= 0, i ::= 0, f ::= q, head ::= 0, total ::= 0, wrap ::= 0,
      while_ (lt i count &&& eq r 0) ([callInto w "ssz_plan_width" [f], len ::= ld (parts + 16 * i + 8),
        ifElse (ne w (none64 : Expr))
          [ifElse (ne len w) [r ::= (codePart : Expr)] ([head ::= head + w] ++ grow len)]
          ([head ::= head + 4] ++ grow 4 ++ grow len),
        advance, i ::= i + 1]),
      when (eq r 0) [r ::= (codeOverflow : Expr),
        when (eq wrap 0 &&& lt total (offsetLimit : Expr)) [r ::= (codeCapacity : Expr),
          when (le total cap) [i ::= 0, f ::= q, total ::= 0, body ::= head,
            while_ (lt i count) [callInto w "ssz_plan_width" [f], len ::= ld (parts + 16 * i + 8),
              ifElse (ne w (none64 : Expr))
                [callInto sink "ssz_copy" [out + total, ld (parts + 16 * i), len], total ::= total + len]
                -- A variable part leaves its body's offset in place, and its body after the others.
                [st4 (out + total) body, callInto sink "ssz_copy" [out + body, ld (parts + 16 * i), len],
                  body ::= body + len, total ::= total + 4],
              advance, i ::= i + 1],
            r ::= body]]]] }

namespace UnionV
/-- The union's plan node. -/
def plan : Var := ⟨0⟩
/-- The parts. -/
def parts : Var := ⟨1⟩
/-- How many. -/
def count : Var := ⟨2⟩
/-- The output. -/
def out : Var := ⟨3⟩
/-- Its capacity. -/
def cap : Var := ⟨4⟩
/-- The answer. -/
def r : Var := ⟨5⟩
/-- The selector. -/
def s : Var := ⟨6⟩
/-- How many options. -/
def n : Var := ⟨7⟩
/-- The option being looked at. -/
def i : Var := ⟨8⟩
/-- The option the selector names, or the word for none. -/
def found : Var := ⟨9⟩
/-- That option's plan node. -/
def option : Var := ⟨10⟩
/-- Its width. -/
def w : Var := ⟨11⟩
/-- The body's size. -/
def len : Var := ⟨12⟩
/-- A sink for copies. -/
def sink : Var := ⟨13⟩
end UnionV

/-- A union from its selector byte and its option's encoding: arguments the plan node, parts, count, output, capacity. -/
def unionParts : Fn :=
  open UnionV in
  { params := 5, vars := 14, result := r,
    body := .block [r ::= (codeCount : Expr),
      when (eq count 2) [r ::= (codePart : Expr),
        when (eq (ld (parts + 8)) 1) [s ::= ld1 (ld parts), n ::= word plan 1, i ::= 0, found ::= (none64 : Expr),
          -- The first selector equal to the selector names the option.
          while_ (lt i n &&& eq found (none64 : Expr))
            [when (eq (ld (plan + 16 + 8 * i)) s) [found ::= i], i ::= i + 1],
          r ::= (codeSelector : Expr),
          when (ne found (none64 : Expr) &&& le 1 s &&& le s 127) [
            callInto option "ssz_plan_skip" [plan + 16 + 8 * n, found],
            callInto w "ssz_plan_width" [option], len ::= ld (parts + 24), r ::= (codePart : Expr),
            when (eq w (none64 : Expr) ||| eq len w) [r ::= (codeCapacity : Expr),
              when (lt len cap) [st1 out s, callInto sink "ssz_copy" [out + 1, ld (parts + 16), len],
                r ::= len + 1]]]]]] }

namespace Bits
/-- The parts: one, the packed bits. -/
def parts : Var := ⟨0⟩
/-- The bit count. -/
def count : Var := ⟨1⟩
/-- The limit, or the word for none. -/
def limit : Var := ⟨2⟩
/-- The output. -/
def out : Var := ⟨3⟩
/-- Its capacity. -/
def cap : Var := ⟨4⟩
/-- The answer. -/
def r : Var := ⟨5⟩
/-- The packed bytes. -/
def src : Var := ⟨6⟩
/-- How many. -/
def len : Var := ⟨7⟩
/-- The bits used in the last byte. -/
def used : Var := ⟨8⟩
/-- The closing bit, in the last byte. -/
def bit : Var := ⟨9⟩
/-- A loop index. -/
def j : Var := ⟨10⟩
/-- The last byte. -/
def last : Var := ⟨11⟩
/-- A sink for copies. -/
def sink : Var := ⟨12⟩
end Bits

/-- A bit list from its packed bits and bit count: arguments the parts, count, limit, output, capacity. -/
def bitsParts : Fn :=
  open Bits in
  { params := 5, vars := 13, result := r,
    body := .block [r ::= (codeCount : Expr),
      when (le count limit) [src ::= ld parts, len ::= ld (parts + 8), used ::= count % 8, r ::= (codePart : Expr),
        when (eq len (count / 8 + ne used 0))
          [ifElse (eq used 0)
            -- A whole number of bytes: the closing bit takes a byte of its own.
            [r ::= (codeCapacity : Expr),
              when (lt len cap) [callInto sink "ssz_copy" [out, src, len], st1 (out + len) 1, r ::= len + 1]]
            -- Otherwise it goes above the last bit, in the last byte, whose padding must be clear.
            [bit ::= 1, j ::= 0, while_ (lt j used) [bit ::= bit + bit, j ::= j + 1],
              last ::= ld1 (src + len - 1), r ::= (codePadding : Expr),
              when (eq (last / bit) 0) [r ::= (codeCapacity : Expr),
                when (le len cap) [callInto sink "ssz_copy" [out, src, len], st1 (out + len - 1) (last ||| bit),
                  r ::= len]]]]]] }

namespace Assemble
/-- The plan node. -/
def plan : Var := ⟨0⟩
/-- The parts. -/
def parts : Var := ⟨1⟩
/-- How many, or a bit list's bit count. -/
def count : Var := ⟨2⟩
/-- The output. -/
def out : Var := ⟨3⟩
/-- Its capacity. -/
def cap : Var := ⟨4⟩
/-- The answer. -/
def r : Var := ⟨5⟩
/-- The tag. -/
def tag : Var := ⟨6⟩
/-- A bound, or a layout length. -/
def k : Var := ⟨7⟩
end Assemble

/--
A composite's encoding from its parts' encodings: arguments the plan node, parts, count, output, capacity.

Returns the encoding's size, or a code far above any size.
-/
def assembleParts : Fn :=
  open Assemble in
  -- An optional bound, from its two words: none as the word for none.
  let bound : List Stmt := [ifElse (eq (word plan 1) 0) [k ::= (none64 : Expr)] [k ::= word plan 2]]
  { params := 5, vars := 8, result := r,
    body := .block [tag ::= ld plan, r ::= (codeType : Expr),
      ifElse (eq tag 2) [callInto r "ssz_assemble_bytes" [parts, count, word plan 1, 1, out, cap]]
      [ifElse (eq tag 3) [callInto r "ssz_assemble_bytes" [parts, count, word plan 1, 0, out, cap]]
      [ifElse (eq tag 5) [callInto r "ssz_assemble_bits" [parts, count, word plan 1, out, cap]]
      [ifElse (eq tag 6) (bound ++ [callInto r "ssz_assemble_bits" [parts, count, k, out, cap]])
      [ifElse (eq tag 7)
        [ifElse (ne count (word plan 1)) [r ::= (codeCount : Expr)]
          [callInto r "ssz_lay_out" [plan + 16, 1, parts, count, out, cap]]]
      [ifElse (eq tag 8)
        [ifElse (lt (word plan 1) count) [r ::= (codeCount : Expr)]
          [callInto r "ssz_lay_out" [plan + 16, 1, parts, count, out, cap]]]
      [ifElse (eq tag 9)
        (bound ++ [ifElse (lt k count) [r ::= (codeCount : Expr)]
          [callInto r "ssz_lay_out" [plan + 24, 1, parts, count, out, cap]]])
      [ifElse (eq tag 10)
        [ifElse (ne count (word plan 1)) [r ::= (codeCount : Expr)]
          [callInto r "ssz_lay_out" [plan + 16, 0, parts, count, out, cap]]]
      [ifElse (eq tag 11)
        [k ::= word plan 1,
          ifElse (ne count (ld (plan + 16 + 8 * k))) [r ::= (codeCount : Expr)]
            [callInto r "ssz_lay_out" [plan + 24 + 8 * k, 0, parts, count, out, cap]]]
      [when (eq tag 12) [callInto r "ssz_assemble_union" [plan, parts, count, out, cap]]]]]]]]]]]] }

/-- The codec drivers, each under its exported name. -/
def codecFns : List (String × Fn) :=
  [("ssz_plan_next", planNext), ("ssz_plan_skip", planSkip), ("ssz_plan_width", planWidth),
    ("ssz_plan_fields_width", planFieldsWidth), ("ssz_plan_leading", planLeading),
    ("ssz_stride_ranges", strideRanges), ("ssz_offset_ranges", offsetRanges),
    ("ssz_vector_ranges", vectorView), ("ssz_list_ranges", listView), ("ssz_fields_ranges", fieldsView),
    ("ssz_ranges", view), ("ssz_copy", copyBytes), ("ssz_assemble_bytes", joinBytes),
    ("ssz_lay_out", layParts), ("ssz_assemble_union", unionParts), ("ssz_assemble_bits", bitsParts),
    ("ssz_assemble", assembleParts)]

/-- Every codec driver fits the compiler's assumptions. -/
theorem codecFns_wf : codecFns.all (fun f => f.2.wf) = true := by decide +kernel

end EthLib.Consensus.Ssz.Native.Driver
