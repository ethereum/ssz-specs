import SszNative.Ir.Dsl
import SszNative.Ir.Wf
import SszNative.Validate
import SszNative.Plan
import Ssz.Type.Valid

/-!
The decoding check, as functions of the small language walking a plan.

A type arrives as its plan: 64-bit words in prefix order, as the plan format lays them out.
A node is named by the address of its tag word.
The encoding arrives as a range of absolute addresses, so a part of it is named by where it starts and stops.

Each function mirrors one step of the check written in Lean, in the same order:

    ssz_validate_range        one range against one type
    ssz_validate_probe        the probes of a fixed-size type
    ssz_validate_records      the same probes over records one width apart
    ssz_validate_delimited    a delimited bit encoding
    ssz_validate_spans        a table of offsets, checked as a whole
    ssz_validate_each         each body a table of offsets opens
    ssz_validate_vector       a fixed count of variable-size elements
    ssz_validate_list         a counted sequence
    ssz_validate_struct       a struct: budget, fixed fields, table, bodies
    ssz_validate_option       the option a union selector names

A refusal is written once, where it is found, as four words: the refusal's code, then its numbers.
Every caller then stops and passes the refusal up.

Before any byte is read, the plan itself is checked: it must read back as one type, declared legally, small enough
that every width the check computes fits a word.
-/

namespace Ssz

/-- The numbers a refusal carries, in order. -/
def Err.payload : Err → List Nat
  | .overLimit a b | .scope a b | .scopeTooSmall a b | .scopeUndivided a b | .firstOffset a b | .count a b
  | .branchLength a b | .leafCount a b | .proofLength a b | .merkleizeLimit a b | .layoutTooWide a b
  | .layoutFieldCount a b | .unionIncompatible a b | .hexLength a b | .uintRange a b | .documentOverLimit a b => [a, b]
  | .notABit a | .unknownSelector a | .notAGindex a | .nestedIndex a | .noSuchField a | .noSuchOption a
  | .noSuchPosition a | .zeroTreeWidth a | .unionSelectorRepeated a | .uintWidth a | .offsetOverflow a
  | .undeclaredSelector a => [a]
  | .unionSelectorRange a b c => [a, b, c]
  | _ => []

/--
A refusal as the four words the native check writes.

The first word names the refusal by its position among the refusals, and the numbers it carries follow.
Words past the numbers are zero.
-/
def Err.toWords (e : Err) : List Nat :=
  (e.ctorIdx :: e.payload ++ [0, 0, 0]).take 4

end Ssz

namespace Ssz.Native

open Ssz

mutual

/--
Whether every width and count the native check computes for a type fits below 2^32, and every word below 2^64.

A plan the native check accepts always fits; a type that does not is refused as a plan.
-/
def fitsNative : Desc → Bool
  | .bool => true
  | .uint width => width < 2 ^ 32
  | .byteVector length | .bitVector length => length < 2 ^ 32
  | .byteList limit | .bitList limit => limit < 2 ^ 64
  | .progressiveBitList limit => limit.all (· < 2 ^ 64)
  | .vector element length =>
    fitsNative element && length < 2 ^ 32 && (!hasWidth element || fixedWidth element * length < 2 ^ 32)
  | .list element limit => fitsNative element && limit < 2 ^ 64
  | .progressiveList element limit => fitsNative element && limit.all (· < 2 ^ 64)
  | .container _ fields => allFitNative fields && fields.length < 2 ^ 32 && Desc.leadingWidth fields < 2 ^ 32
  | .progressiveContainer _ _ fields =>
    allFitNative fields && fields.length < 2 ^ 32 && Desc.leadingWidth fields < 2 ^ 32
  | .compatibleUnion selectors options =>
    allFitNative options && options.length < 2 ^ 32 && selectors.length == options.length &&
      selectors.all (· < 2 ^ 64)

/-- Whether every type of a list fits the native check. -/
def allFitNative : List Desc → Bool
  | [] => true
  | d :: rest => fitsNative d && allFitNative rest

end

end Ssz.Native

namespace Ssz.Native.Driver.Validate

open Ssz.Native.Ir Ssz.Native.Ir.Expr Ssz.Native.Ir.Stmt

/-- The word standing for no width, and for a refused plan: no address or width reaches it. -/
def none_ : Expr := .lit 18446744073709551615

/-- The first size a four-byte offset cannot name. -/
def bound32 : Expr := .lit 4294967296

/-- A refusal's code, as a constant. -/
def code (e : Ssz.Err) : Expr := (e.ctorIdx : Nat)

/-- A word of a node: the k-th word after its tag. -/
def word (p : Expr) (k : Nat) : Expr := ld (p + ((8 * k : Nat) : Expr))

/-- Write a refusal through the routine that stores it, keeping its result. -/
def fail (r : Var) (err : Expr) (e : Ssz.Err) (args : List Expr) : Stmt :=
  callInto r "ssz_validate_fail" ([err, code e] ++ (args ++ [0, 0, 0]).take 3)

/-- Both conditions, for conditions that are zero or one. -/
def both (a b : Expr) : Expr := a &&& b

/-- Either condition, for conditions that are zero or one. -/
def either (a b : Expr) : Expr := a ||| b

/-- Write a refusal's four words and return one: arguments err, code, and three numbers. -/
def failFn : Fn :=
  let err : Var := ⟨0⟩
  let c : Var := ⟨1⟩
  let a : Var := ⟨2⟩
  let b : Var := ⟨3⟩
  let d : Var := ⟨4⟩
  { params := 5, vars := 5, result := 1,
    body := .block [st err c, st (err + 8) a, st (err + 16) b, st (err + 24) d] }

/-- The address past one node: argument the node. -/
def skipFn : Fn :=
  let p : Var := ⟨0⟩
  let t : Var := ⟨1⟩
  let r : Var := ⟨2⟩
  let n : Var := ⟨3⟩
  { params := 1, vars := 4, result := r,
    body := .block [t ::= ld p,
      ifElse (eq t 0) [r ::= p + 8]
      [ifElse (le t 5) [r ::= p + 16]
      [ifElse (eq t 6) [r ::= p + 24]
      [ifElse (le t 8) [callInto r "ssz_validate_skip" [p + 16]]
      [ifElse (eq t 9) [callInto r "ssz_validate_skip" [p + 24]]
      [ifElse (eq t 10) [callInto r "ssz_validate_skip_all" [p + 16, word p 1]]
      [ifElse (eq t 11) [n ::= word p 1, callInto r "ssz_validate_skip_all" [p + 24 + 8 * n, ld (p + 16 + 8 * n)]]
      -- A union: its selectors, then its options.
      [n ::= word p 1, callInto r "ssz_validate_skip_all" [p + 16 + 8 * n, n]]]]]]]]] }

/-- The address past a count of nodes: arguments the first node, the count. -/
def skipAllFn : Fn :=
  let q : Var := ⟨0⟩
  let n : Var := ⟨1⟩
  { params := 2, vars := 2, result := q,
    body := while_ (ne n 0) [callInto q "ssz_validate_skip" [q], n ::= n - 1] }

/-- A type's fixed width, or the word standing for none: argument the node. -/
def widthFn : Fn :=
  let p : Var := ⟨0⟩
  let t : Var := ⟨1⟩
  let r : Var := ⟨2⟩
  let n : Var := ⟨3⟩
  let w : Var := ⟨4⟩
  { params := 1, vars := 5, result := r,
    body := .block [t ::= ld p,
      ifElse (eq t 0) [r ::= 1]
      [ifElse (le t 2) [r ::= word p 1]
      [ifElse (eq t 4) [r ::= (word p 1 + 7) / 8]
      [ifElse (eq t 7) [callInto w "ssz_validate_width" [p + 16],
        ifElse (eq w none_) [r ::= none_] [r ::= w * word p 1]]
      [ifElse (eq t 10) [callInto r "ssz_validate_fields_width" [p + 16, word p 1]]
      [ifElse (eq t 11) [n ::= word p 1, callInto r "ssz_validate_fields_width" [p + 24 + 8 * n, ld (p + 16 + 8 * n)]]
      [r ::= none_]]]]]]] }

/-- The total width of a count of fields, or the word standing for none: arguments the first field, the count. -/
def fieldsWidthFn : Fn :=
  let q : Var := ⟨0⟩
  let n : Var := ⟨1⟩
  let r : Var := ⟨2⟩
  let w : Var := ⟨3⟩
  { params := 2, vars := 4, result := r,
    body := .block [r ::= 0,
      while_ (ne n 0) [callInto w "ssz_validate_width" [q],
        -- One variable field leaves the whole struct variable.
        ifElse (eq w none_) [r ::= none_, n ::= 0]
          [r ::= r + w, callInto q "ssz_validate_skip" [q], n ::= n - 1]]] }

/-- The width of a struct's fixed part, an offset standing for each variable field: arguments the first field, the count. -/
def leadingFn : Fn :=
  let q : Var := ⟨0⟩
  let n : Var := ⟨1⟩
  let r : Var := ⟨2⟩
  let w : Var := ⟨3⟩
  { params := 2, vars := 4, result := r,
    body := .block [r ::= 0,
      while_ (ne n 0) [callInto w "ssz_validate_width" [q],
        ifElse (eq w none_) [r ::= r + 4] [r ::= r + w],
        callInto q "ssz_validate_skip" [q], n ::= n - 1]] }

/-- One when a type leaves probes, and zero otherwise: argument the node. -/
def hasProbesFn : Fn :=
  let p : Var := ⟨0⟩
  let t : Var := ⟨1⟩
  let r : Var := ⟨2⟩
  let n : Var := ⟨3⟩
  { params := 1, vars := 4, result := r,
    body := .block [t ::= ld p,
      ifElse (eq t 0) [r ::= 1]
      [ifElse (eq t 4) [r ::= ne (word p 1 % 8) 0]
      -- A vector of no elements leaves no probes, whatever its element leaves.
      [ifElse (eq t 7) [ifElse (eq (word p 1) 0) [r ::= 0] [callInto r "ssz_validate_has_probes" [p + 16]]]
      [ifElse (eq t 10) [callInto r "ssz_validate_any_probes" [p + 16, word p 1]]
      [ifElse (eq t 11) [n ::= word p 1, callInto r "ssz_validate_any_probes" [p + 24 + 8 * n, ld (p + 16 + 8 * n)]]
      [r ::= 0]]]]]] }

/-- One when any of a count of fields leaves probes: arguments the first field, the count. -/
def anyProbesFn : Fn :=
  let q : Var := ⟨0⟩
  let n : Var := ⟨1⟩
  let r : Var := ⟨2⟩
  { params := 2, vars := 3, result := r,
    body := .block [r ::= 0,
      while_ (ne n 0) [callInto r "ssz_validate_has_probes" [q],
        ifElse (ne r 0) [n ::= 0] [callInto q "ssz_validate_skip" [q], n ::= n - 1]]] }

/-- Run a fixed-size type's probes on a value: arguments the node, the value's start, err. -/
def probeFn : Fn :=
  let p : Var := ⟨0⟩
  let start : Var := ⟨1⟩
  let err : Var := ⟨2⟩
  let t : Var := ⟨3⟩
  let r : Var := ⟨4⟩
  let n : Var := ⟨5⟩
  let m : Var := ⟨6⟩
  let b : Var := ⟨7⟩
  let w : Var := ⟨8⟩
  { params := 3, vars := 9, result := r,
    body := .block [t ::= ld p, r ::= 0,
      ifElse (eq t 0) [b ::= ld1 start, when (lt 1 b) [fail r err (.notABit 0) [b]]]
      [ifElse (eq t 4) [n ::= word p 1, m ::= n % 8,
        -- The last byte's bits from the length up are padding.
        when (ne m 0) [b ::= ld1 (start + (n + 7) / 8 - 1),
          while_ (ne m 0) [b ::= .shr b 1, m ::= m - 1],
          when (ne b 0) [fail r err .paddingBits []]]]
      [ifElse (eq t 7) [callInto b "ssz_validate_has_probes" [p + 16],
        when (ne b 0) [callInto w "ssz_validate_width" [p + 16],
          callInto r "ssz_validate_records" [p + 16, w, start, word p 1, err]]]
      [ifElse (eq t 10) [callInto r "ssz_validate_fields_probe" [p + 16, word p 1, start, err]]
      [ifElse (eq t 11) [n ::= word p 1,
        callInto r "ssz_validate_fields_probe" [p + 24 + 8 * n, ld (p + 16 + 8 * n), start, err]]
      []]]]]] }

/-- Run the same probes over records one width apart, stopping at the first refusal: arguments node, width, start, count, err. -/
def recordsFn : Fn :=
  let p : Var := ⟨0⟩
  let w : Var := ⟨1⟩
  let start : Var := ⟨2⟩
  let count : Var := ⟨3⟩
  let err : Var := ⟨4⟩
  let r : Var := ⟨5⟩
  { params := 5, vars := 6, result := r,
    body := .block [r ::= 0,
      while_ (both (ne count 0) (eq r 0)) [callInto r "ssz_validate_probe" [p, start, err],
        start ::= start + w, count ::= count - 1]] }

/-- Run each fixed field's probes at its offset: arguments the first field, the count, start, err. -/
def fieldsProbeFn : Fn :=
  let q : Var := ⟨0⟩
  let n : Var := ⟨1⟩
  let start : Var := ⟨2⟩
  let err : Var := ⟨3⟩
  let r : Var := ⟨4⟩
  let w : Var := ⟨5⟩
  { params := 4, vars := 6, result := r,
    body := .block [r ::= 0,
      while_ (both (ne n 0) (eq r 0)) [callInto r "ssz_validate_probe" [q, start, err],
        callInto w "ssz_validate_width" [q], start ::= start + w,
        callInto q "ssz_validate_skip" [q], n ::= n - 1]] }

/-- Check a delimited bit encoding: arguments start, stop, whether there is a limit, the limit, err. -/
def delimitedFn : Fn :=
  let start : Var := ⟨0⟩
  let stop : Var := ⟨1⟩
  let has : Var := ⟨2⟩
  let limit : Var := ⟨3⟩
  let err : Var := ⟨4⟩
  let r : Var := ⟨5⟩
  let size : Var := ⟨6⟩
  let final : Var := ⟨7⟩
  let i : Var := ⟨8⟩
  let z : Var := ⟨9⟩
  let h : Var := ⟨10⟩
  let count : Var := ⟨11⟩
  { params := 5, vars := 12, result := r,
    body := .block [r ::= 0, size ::= stop - start,
      ifElse (eq size 0) [fail r err .emptyEncoding []]
      [final ::= ld1 (stop - 1),
        ifElse (eq final 0)
          -- Trailing zero bytes: refused as such, unless every byte is zero.
          [i ::= 0, z ::= 1,
            while_ (both (lt i size) z) [when (ne (ld1 (start + i)) 0) [z ::= 0], i ::= i + 1],
            ifElse (ne z 0) [fail r err .noDelimiter []] [fail r err .trailingZeros []]]
          ([h ::= 0] ++ (List.range 7).map (fun k => when (ne (.shr final (k + 1)) 0) [h ::= ((k + 1 : Nat) : Expr)]) ++
            [count ::= 8 * (size - 1) + h,
              when (both (ne has 0) (lt limit count)) [fail r err (.overLimit 0 0) [limit, count]]])]] }

/-- Check a table of offsets as a whole: arguments the table, the count, the size it closes over, err. -/
def spansFn : Fn :=
  let tbl : Var := ⟨0⟩
  let count : Var := ⟨1⟩
  let size : Var := ⟨2⟩
  let err : Var := ⟨3⟩
  let r : Var := ⟨4⟩
  let i : Var := ⟨5⟩
  let a : Var := ⟨6⟩
  { params := 4, vars := 7, result := r,
    body := .block [r ::= 0, i ::= 1,
      while_ (both (lt i count) (eq r 0)) [a ::= ld4 (tbl + 4 * (i - 1)),
        when (lt (ld4 (tbl + 4 * i)) a) [fail r err .offsetUnordered []], i ::= i + 1],
      -- The last body is closed by the size.
      when (both (eq r 0) (ne count 0)) [when (lt size (ld4 (tbl + 4 * (count - 1)))) [fail r err .offsetPastScope []]]] }

/-- Check each body a checked table opens: arguments the element, the table, the count, the size, err. -/
def eachFn : Fn :=
  let p : Var := ⟨0⟩
  let tbl : Var := ⟨1⟩
  let count : Var := ⟨2⟩
  let size : Var := ⟨3⟩
  let err : Var := ⟨4⟩
  let r : Var := ⟨5⟩
  let i : Var := ⟨6⟩
  let e : Var := ⟨7⟩
  { params := 5, vars := 8, result := r,
    body := .block [r ::= 0, i ::= 0,
      while_ (both (lt i count) (eq r 0)) [
        ifElse (lt (i + 1) count) [e ::= ld4 (tbl + 4 * i + 4)] [e ::= size],
        callInto r "ssz_validate_range" [p, tbl + ld4 (tbl + 4 * i), tbl + e, err], i ::= i + 1]] }

/-- Check a fixed count of variable-size elements: arguments the vector's node, start, stop, err. -/
def vectorFn : Fn :=
  let p : Var := ⟨0⟩
  let start : Var := ⟨1⟩
  let stop : Var := ⟨2⟩
  let err : Var := ⟨3⟩
  let r : Var := ⟨4⟩
  let size : Var := ⟨5⟩
  let n : Var := ⟨6⟩
  let first : Var := ⟨7⟩
  { params := 4, vars := 8, result := r,
    body := .block [r ::= 0, size ::= stop - start,
      ifElse (le bound32 size) [fail r err (.offsetOverflow 0) [size]]
      [n ::= word p 1, first ::= n * 4,
        ifElse (lt size first) [fail r err (.scopeTooSmall 0 0) [first, size]]
        [when (ne n 0) [
          ifElse (ne (ld4 start) first) [fail r err (.firstOffset 0 0) [first, ld4 start]]
          [callInto r "ssz_validate_spans" [start, n, size, err],
            when (eq r 0) [callInto r "ssz_validate_each" [p + 16, start, n, size, err]]]]]]] }

/-- Check a counted sequence: arguments the element's node, start, stop, whether there is a limit, the limit, err. -/
def listFn : Fn :=
  let e : Var := ⟨0⟩
  let start : Var := ⟨1⟩
  let stop : Var := ⟨2⟩
  let has : Var := ⟨3⟩
  let limit : Var := ⟨4⟩
  let err : Var := ⟨5⟩
  let r : Var := ⟨6⟩
  let size : Var := ⟨7⟩
  let w : Var := ⟨8⟩
  let count : Var := ⟨9⟩
  let first : Var := ⟨10⟩
  let b : Var := ⟨11⟩
  { params := 6, vars := 12, result := r,
    body := .block [r ::= 0, size ::= stop - start,
      ifElse (le bound32 size) [fail r err (.offsetOverflow 0) [size]]
      [when (ne size 0) [callInto w "ssz_validate_width" [e],
        ifElse (ne w none_)
          [ifElse (eq w 0) [fail r err .scopeWidthless []]
          [ifElse (ne (size % w) 0) [fail r err (.scopeUndivided 0 0) [size, w]]
          [count ::= size / w,
            ifElse (both (ne has 0) (lt limit count)) [fail r err (.overLimit 0 0) [limit, count]]
            [callInto b "ssz_validate_has_probes" [e],
              when (ne b 0) [callInto r "ssz_validate_records" [e, w, start, count, err]]]]]]
          [ifElse (lt size 4) [fail r err (.scopeTooSmall 0 0) [4, size]]
          [first ::= ld4 start,
            ifElse (lt first 4) [fail r err .offsetBelowTable []]
            [ifElse (ne (first % 4) 0) [fail r err .offsetUnaligned []]
            [ifElse (lt size first) [fail r err .offsetPastScope []]
            [count ::= first / 4,
              ifElse (both (ne has 0) (lt limit count)) [fail r err (.overLimit 0 0) [limit, count]]
              [callInto r "ssz_validate_spans" [start, count, size, err],
                when (eq r 0) [callInto r "ssz_validate_each" [e, start, count, size, err]]]]]]]]]]] }

/-- Check each fixed field in place: arguments the first field, the count, start, err. -/
def inlineFn : Fn :=
  let q : Var := ⟨0⟩
  let n : Var := ⟨1⟩
  let start : Var := ⟨2⟩
  let err : Var := ⟨3⟩
  let r : Var := ⟨4⟩
  let w : Var := ⟨5⟩
  let pos : Var := ⟨6⟩
  { params := 4, vars := 7, result := r,
    body := .block [r ::= 0, pos ::= 0,
      while_ (both (ne n 0) (eq r 0)) [callInto w "ssz_validate_width" [q],
        ifElse (ne w none_)
          [callInto r "ssz_validate_range" [q, start + pos, start + pos + w, err], pos ::= pos + w]
          [pos ::= pos + 4],
        callInto q "ssz_validate_skip" [q], n ::= n - 1]] }

/--
Check a struct's table of offsets as a whole: arguments the first field, the count, start, size, the fixed part's width,
err.
-/
def structSpansFn : Fn :=
  let q : Var := ⟨0⟩
  let n : Var := ⟨1⟩
  let start : Var := ⟨2⟩
  let size : Var := ⟨3⟩
  let lead : Var := ⟨4⟩
  let err : Var := ⟨5⟩
  let r : Var := ⟨6⟩
  let w : Var := ⟨7⟩
  let pos : Var := ⟨8⟩
  let seen : Var := ⟨9⟩
  let prev : Var := ⟨10⟩
  let o : Var := ⟨11⟩
  { params := 6, vars := 12, result := r,
    body := .block [r ::= 0, pos ::= 0, seen ::= 0, prev ::= 0,
      while_ (both (ne n 0) (eq r 0)) [callInto w "ssz_validate_width" [q],
        ifElse (ne w none_) [pos ::= pos + w]
          [o ::= ld4 (start + pos),
            -- The first body starts where the fixed part ends, and each later one no earlier than the one before.
            ifElse (eq seen 0) [when (ne o lead) [fail r err (.firstOffset 0 0) [lead, o]]]
              [when (lt o prev) [fail r err .offsetUnordered []]],
            seen ::= 1, prev ::= o, pos ::= pos + 4],
        callInto q "ssz_validate_skip" [q], n ::= n - 1],
      when (eq r 0) [when (lt size prev) [fail r err .offsetPastScope []]]] }

/-- Where the next body begins, or the size when none follows: arguments the next field, the count left, its slot, size. -/
def nextBodyFn : Fn :=
  let q : Var := ⟨0⟩
  let n : Var := ⟨1⟩
  let at_ : Var := ⟨2⟩
  let size : Var := ⟨3⟩
  let r : Var := ⟨4⟩
  let w : Var := ⟨5⟩
  { params := 4, vars := 6, result := r,
    body := .block [r ::= size,
      while_ (ne n 0) [callInto w "ssz_validate_width" [q],
        ifElse (ne w none_) [at_ ::= at_ + w, callInto q "ssz_validate_skip" [q], n ::= n - 1]
          [r ::= ld4 at_, n ::= 0]]] }

/-- Check each field against its range, in declaration order: arguments the first field, the count, start, size, err. -/
def fieldsFn : Fn :=
  let q : Var := ⟨0⟩
  let n : Var := ⟨1⟩
  let start : Var := ⟨2⟩
  let size : Var := ⟨3⟩
  let err : Var := ⟨4⟩
  let r : Var := ⟨5⟩
  let w : Var := ⟨6⟩
  let pos : Var := ⟨7⟩
  let next : Var := ⟨8⟩
  let e : Var := ⟨9⟩
  { params := 5, vars := 10, result := r,
    body := .block [r ::= 0, pos ::= 0,
      while_ (both (ne n 0) (eq r 0)) [callInto w "ssz_validate_width" [q], callInto next "ssz_validate_skip" [q],
        ifElse (ne w none_)
          [callInto r "ssz_validate_range" [q, start + pos, start + pos + w, err], pos ::= pos + w]
          -- A body runs from its offset to the next body's offset, or to the size.
          [callInto e "ssz_validate_next_body" [next, n - 1, start + pos + 4, size],
            callInto r "ssz_validate_range" [q, start + ld4 (start + pos), start + e, err], pos ::= pos + 4],
        q ::= next, n ::= n - 1]] }

/-- Check a struct: arguments the first field, the count, start, stop, err. -/
def structFn : Fn :=
  let q : Var := ⟨0⟩
  let n : Var := ⟨1⟩
  let start : Var := ⟨2⟩
  let stop : Var := ⟨3⟩
  let err : Var := ⟨4⟩
  let r : Var := ⟨5⟩
  let size : Var := ⟨6⟩
  let fw : Var := ⟨7⟩
  let lead : Var := ⟨8⟩
  { params := 5, vars := 9, result := r,
    body := .block [r ::= 0, size ::= stop - start,
      ifElse (le bound32 size) [fail r err (.offsetOverflow 0) [size]]
      [callInto fw "ssz_validate_fields_width" [q, n],
        ifElse (ne fw none_)
          -- Every field fixed: the struct is its width exactly, and each field sits in place.
          [ifElse (ne size fw) [fail r err (.scope 0 0) [fw, size]]
            [callInto r "ssz_validate_fields" [q, n, start, size, err]]]
          [callInto lead "ssz_validate_leading" [q, n],
            ifElse (lt size lead) [fail r err (.scopeTooSmall 0 0) [lead, size]]
            -- Fixed fields first, then the table as a whole, then every field in order.
            [callInto r "ssz_validate_inline" [q, n, start, err],
              when (eq r 0) [callInto r "ssz_validate_struct_spans" [q, n, start, size, lead, err],
                when (eq r 0) [callInto r "ssz_validate_fields" [q, n, start, size, err]]]]]]] }

/-- Check the option a selector names: arguments the selectors, the count, the selector, start, stop, err. -/
def optionFn : Fn :=
  let q : Var := ⟨0⟩
  let n : Var := ⟨1⟩
  let sel : Var := ⟨2⟩
  let start : Var := ⟨3⟩
  let stop : Var := ⟨4⟩
  let err : Var := ⟨5⟩
  let r : Var := ⟨6⟩
  let o : Var := ⟨7⟩
  let i : Var := ⟨8⟩
  let found : Var := ⟨9⟩
  { params := 6, vars := 10, result := r,
    body := .block [r ::= 0, o ::= q + 8 * n, i ::= 0, found ::= 0,
      while_ (both (lt i n) (eq found 0))
        [ifElse (eq (ld (q + 8 * i)) sel) [found ::= 1] [callInto o "ssz_validate_skip" [o], i ::= i + 1]],
      ifElse (eq found 0) [fail r err (.unknownSelector 0) [sel]]
        [ifElse (either (lt sel 1) (lt 127 sel)) [fail r err (.unionSelectorRange 0 0 0) [sel, 1, 127]]
          [callInto r "ssz_validate_range" [o, start, stop, err]]]] }

/-- Check a range against a type: arguments the node, start, stop, err. -/
def rangeFn : Fn :=
  let p : Var := ⟨0⟩
  let start : Var := ⟨1⟩
  let stop : Var := ⟨2⟩
  let err : Var := ⟨3⟩
  let r : Var := ⟨4⟩
  let size : Var := ⟨5⟩
  let w : Var := ⟨6⟩
  let t : Var := ⟨7⟩
  let n : Var := ⟨8⟩
  { params := 4, vars := 9, result := r,
    body := .block [r ::= 0, size ::= stop - start, callInto w "ssz_validate_width" [p], t ::= ld p,
      ifElse (ne w none_)
        -- A fixed-size type: the size checks, then the probes.
        [ifElse (both (either (either (eq t 2) (eq t 7)) (either (eq t 10) (eq t 11))) (le bound32 size))
          [fail r err (.offsetOverflow 0) [size]]
          [ifElse (ne size w) [fail r err (.scope 0 0) [w, size]] [callInto r "ssz_validate_probe" [p, start, err]]]]
      [ifElse (eq t 3)
        [ifElse (le bound32 size) [fail r err (.offsetOverflow 0) [size]]
          [when (lt (word p 1) size) [fail r err (.overLimit 0 0) [word p 1, size]]]]
      [ifElse (eq t 5) [callInto r "ssz_validate_delimited" [start, stop, 1, word p 1, err]]
      [ifElse (eq t 6) [callInto r "ssz_validate_delimited" [start, stop, word p 1, word p 2, err]]
      [ifElse (eq t 7) [callInto r "ssz_validate_vector" [p, start, stop, err]]
      [ifElse (eq t 8) [callInto r "ssz_validate_list" [p + 16, start, stop, 1, word p 1, err]]
      [ifElse (eq t 9) [callInto r "ssz_validate_list" [p + 24, start, stop, word p 1, word p 2, err]]
      [ifElse (eq t 10) [callInto r "ssz_validate_struct" [p + 16, word p 1, start, stop, err]]
      [ifElse (eq t 11) [n ::= word p 1,
        callInto r "ssz_validate_struct" [p + 24 + 8 * n, ld (p + 16 + 8 * n), start, stop, err]]
      -- A union: its selector byte, then the option it names.
      [ifElse (eq size 0) [fail r err .noSelector []]
        [callInto r "ssz_validate_option" [p + 16, word p 1, ld1 start, start + 1, stop, err]]]]]]]]]]]] }

/-! The plan's own check: it reads back as one type, legally declared, within the native check's sizes. -/

/--
One when two types are equal: arguments the two nodes.

A plan names fields by position, so two types are equal exactly when their words are.
-/
def eqFn : Fn :=
  let a : Var := ⟨0⟩
  let b : Var := ⟨1⟩
  let r : Var := ⟨2⟩
  let ea : Var := ⟨3⟩
  let eb : Var := ⟨4⟩
  let n : Var := ⟨5⟩
  let i : Var := ⟨6⟩
  { params := 2, vars := 7, result := r,
    body := .block [callInto ea "ssz_validate_skip" [a], callInto eb "ssz_validate_skip" [b], r ::= 0,
      when (eq (ea - a) (eb - b)) [r ::= 1, i ::= 0, n ::= (ea - a) / 8,
        while_ (both (lt i n) (ne r 0)) [when (ne (ld (a + 8 * i)) (ld (b + 8 * i))) [r ::= 0], i ::= i + 1]]] }

/-- How a type spells a byte array: zero for none, one for a fixed count, two for a bounded count. -/
def bytesFn : Fn :=
  let p : Var := ⟨0⟩
  let t : Var := ⟨1⟩
  let r : Var := ⟨2⟩
  { params := 1, vars := 3, result := r,
    body := .block [t ::= ld p, r ::= 0,
      ifElse (eq t 2) [r ::= 1]
      [ifElse (eq t 3) [r ::= 2]
      -- A vector or list of one-byte integers; the width is read only below an integer's tag, where it sits.
      [when (either (eq t 7) (eq t 8)) [when (eq (word p 2) 1) [when (eq (word p 3) 1) [r ::= t - 6]]]]]] }

/-- One when two types use compatible Merkle layouts: arguments the two nodes. -/
def compatFn : Fn :=
  let a : Var := ⟨0⟩
  let b : Var := ⟨1⟩
  let r : Var := ⟨2⟩
  let ka : Var := ⟨3⟩
  let kb : Var := ⟨4⟩
  let t : Var := ⟨5⟩
  { params := 2, vars := 6, result := r,
    body := .block [callInto r "ssz_validate_eq" [a, b],
      when (eq r 0) [callInto ka "ssz_validate_bytes" [a], callInto kb "ssz_validate_bytes" [b],
        ifElse (either (ne ka 0) (ne kb 0))
          -- A byte array and a sequence of single bytes are one shape; its size is read only when both spell one.
          [when (eq ka kb) [r ::= eq (word a 1) (word b 1)]]
          [t ::= ld a,
            when (eq t (ld b))
            [ifElse (eq t 0) [r ::= 1]
            [ifElse (le t 5) [r ::= both (ne t 2) (both (ne t 3) (eq (word a 1) (word b 1)))]
            [ifElse (eq t 6) [r ::= 1]
            [ifElse (le t 8) [when (eq (word a 1) (word b 1)) [callInto r "ssz_validate_compat" [a + 16, b + 16]]]
            [ifElse (eq t 9) [callInto r "ssz_validate_compat" [a + 24, b + 24]]
            [ifElse (eq t 10)
              [when (eq (word a 1) (word b 1)) [callInto r "ssz_validate_compat_all" [a + 16, b + 16, word a 1]]]
            [ifElse (eq t 11) [callInto r "ssz_validate_layouts" [a, b]]
            [callInto r "ssz_validate_options_agree" [a + 16 + 8 * word a 1, word a 1, b + 16 + 8 * word b 1, word b 1]]]]]]]]]]]] }

/-- One when two counts of types are pairwise compatible: arguments the two first nodes, the count. -/
def compatAllFn : Fn :=
  let a : Var := ⟨0⟩
  let b : Var := ⟨1⟩
  let n : Var := ⟨2⟩
  let r : Var := ⟨3⟩
  { params := 3, vars := 4, result := r,
    body := .block [r ::= 1,
      while_ (both (ne n 0) (ne r 0)) [callInto r "ssz_validate_compat" [a, b],
        callInto a "ssz_validate_skip" [a], callInto b "ssz_validate_skip" [b], n ::= n - 1]] }

/-- One when every option of one union fits every option of another: arguments the first options and counts. -/
def optionsAgreeFn : Fn :=
  let a : Var := ⟨0⟩
  let na : Var := ⟨1⟩
  let b : Var := ⟨2⟩
  let nb : Var := ⟨3⟩
  let r : Var := ⟨4⟩
  let q : Var := ⟨5⟩
  let j : Var := ⟨6⟩
  { params := 4, vars := 7, result := r,
    body := .block [r ::= 1,
      while_ (both (ne na 0) (ne r 0)) [q ::= b, j ::= nb,
        while_ (both (ne j 0) (ne r 0)) [callInto r "ssz_validate_compat" [a, q],
          callInto q "ssz_validate_skip" [q], j ::= j - 1],
        callInto a "ssz_validate_skip" [a], na ::= na - 1]] }

/--
One when two progressive containers place the fields they share alike: arguments the two nodes.

A field's name is its layout position, so only a position both layouts set needs a check: compatible fields there.
-/
def layoutsFn : Fn :=
  let a : Var := ⟨0⟩
  let b : Var := ⟨1⟩
  let r : Var := ⟨2⟩
  let i : Var := ⟨3⟩
  let oi : Var := ⟨4⟩
  let oj : Var := ⟨5⟩
  let fa : Var := ⟨6⟩
  let fb : Var := ⟨7⟩
  { params := 2, vars := 8, result := r,
    body := .block [r ::= 1, i ::= 0, oi ::= 0, oj ::= 0,
      while_ (both (both (lt i (word a 1)) (lt i (word b 1))) (ne r 0)) [
        when (both (ne (ld (a + 16 + 8 * i)) 0) (ne (ld (b + 16 + 8 * i)) 0)) [
          callInto fa "ssz_validate_skip_all" [a + 24 + 8 * word a 1, oi],
          callInto fb "ssz_validate_skip_all" [b + 24 + 8 * word b 1, oj],
          callInto r "ssz_validate_compat" [fa, fb]],
        -- Each layout's ordinal counts the fields placed before the next position.
        when (ne (ld (a + 16 + 8 * i)) 0) [oi ::= oi + 1],
        when (ne (ld (b + 16 + 8 * i)) 0) [oj ::= oj + 1],
        i ::= i + 1]] }

/-- One when two words spell a bound as a plan writes one: two zeros for none, a one then the value for some. -/
def canonicalBound (p : Expr) : Expr := either (both (eq (word p 1) 0) (eq (word p 2) 0)) (eq (word p 1) 1)

/-- The address past one node whose declaration checks out, or the word standing for none: arguments the node, the plan's end. -/
def planFn : Fn :=
  let p : Var := ⟨0⟩
  let stop : Var := ⟨1⟩
  let t : Var := ⟨2⟩
  let r : Var := ⟨3⟩
  let n : Var := ⟨4⟩
  let q : Var := ⟨5⟩
  let w : Var := ⟨6⟩
  let i : Var := ⟨7⟩
  let c : Var := ⟨8⟩
  let s : Var := ⟨9⟩
  let j : Var := ⟨10⟩
  { params := 2, vars := 11, result := r,
    body := .block [r ::= none_,
      when (le (p + 8) stop) [t ::= ld p,
      ifElse (eq t 0) [r ::= p + 8]
      [ifElse (le t 5) [when (le (p + 16) stop) [n ::= word p 1,
        -- Six integer widths; fixed counts of at least one and below 2^32; any limit.
        ifElse (eq t 1) [when (either (either (either (eq n 1) (eq n 2)) (either (eq n 4) (eq n 8)))
            (either (eq n 16) (eq n 32))) [r ::= p + 16]]
          [ifElse (either (eq t 2) (eq t 4)) [when (both (ne n 0) (lt n bound32)) [r ::= p + 16]]
            [r ::= p + 16]]]]
      [ifElse (eq t 6) [when (le (p + 24) stop) [when (canonicalBound p) [r ::= p + 24]]]
      [ifElse (eq t 7) [when (le (p + 16) stop) [n ::= word p 1,
        when (both (ne n 0) (lt n bound32)) [callInto q "ssz_validate_plan" [p + 16, stop],
          when (ne q none_) [callInto w "ssz_validate_width" [p + 16],
            when (either (eq w none_) (lt (w * n) bound32)) [r ::= q]]]]]
      [ifElse (eq t 8) [when (le (p + 16) stop) [callInto r "ssz_validate_plan" [p + 16, stop]]]
      [ifElse (eq t 9) [when (le (p + 24) stop) [when (canonicalBound p) [callInto r "ssz_validate_plan" [p + 24, stop]]]]
      [ifElse (eq t 10) [when (le (p + 16) stop) [n ::= word p 1,
        when (both (ne n 0) (lt n bound32)) [callInto q "ssz_validate_plan_all" [p + 16, n, stop],
          when (ne q none_) [callInto w "ssz_validate_leading" [p + 16, n], when (lt w bound32) [r ::= q]]]]]
      [ifElse (eq t 11) [when (le (p + 16) stop) [n ::= word p 1,
        -- A layout of one to 256 positions, each bit zero or one, ending on a field, setting one position per field.
        when (both (both (ne n 0) (le n 256)) (le (p + 24 + 8 * n) stop)) [
          c ::= 0, i ::= 0, s ::= 1,
          while_ (lt i n) [when (ne (ld (p + 16 + 8 * i)) 0) [c ::= c + 1],
            when (lt 1 (ld (p + 16 + 8 * i))) [s ::= 0], i ::= i + 1],
          when (both (ne s 0) (both (ne (ld (p + 8 + 8 * n)) 0) (eq (ld (p + 16 + 8 * n)) c))) [
            callInto q "ssz_validate_plan_all" [p + 24 + 8 * n, c, stop],
            when (ne q none_) [callInto w "ssz_validate_leading" [p + 24 + 8 * n, c],
              when (lt w bound32) [r ::= q]]]]]]
      [when (eq t 12) [when (le (p + 16) stop) [n ::= word p 1,
        -- At least one option, each under its own selector from 1 to 127, every two options compatible.
        when (both (both (ne n 0) (lt n bound32)) (le (p + 16 + 8 * n) stop)) [
          c ::= 1, i ::= 0,
          while_ (lt i n) [s ::= ld (p + 16 + 8 * i),
            when (either (lt s 1) (lt 127 s)) [c ::= 0],
            j ::= 0, while_ (lt j i) [when (eq (ld (p + 16 + 8 * j)) s) [c ::= 0], j ::= j + 1],
            i ::= i + 1],
          when (ne c 0) [callInto q "ssz_validate_plan_all" [p + 16 + 8 * n, n, stop],
            when (ne q none_) [callInto c "ssz_validate_pairs" [p + 16 + 8 * n, n],
              when (ne c 0) [r ::= q]]]]]]]]]]]]]]]] }

/-- The address past a count of checked nodes, or the word standing for none: arguments the first node, the count, the end. -/
def planAllFn : Fn :=
  let q : Var := ⟨0⟩
  let n : Var := ⟨1⟩
  let stop : Var := ⟨2⟩
  { params := 3, vars := 3, result := q,
    body := while_ (both (ne n 0) (ne q none_)) [callInto q "ssz_validate_plan" [q, stop], n ::= n - 1] }

/-- One when every option is compatible with every later one: arguments the first option, the count. -/
def pairsFn : Fn :=
  let a : Var := ⟨0⟩
  let n : Var := ⟨1⟩
  let r : Var := ⟨2⟩
  let b : Var := ⟨3⟩
  let j : Var := ⟨4⟩
  let next : Var := ⟨5⟩
  { params := 2, vars := 6, result := r,
    body := .block [r ::= 1,
      while_ (both (ne n 0) (ne r 0)) [callInto next "ssz_validate_skip" [a], b ::= next, j ::= n - 1,
        while_ (both (ne j 0) (ne r 0)) [callInto r "ssz_validate_compat" [a, b],
          callInto b "ssz_validate_skip" [b], j ::= j - 1],
        a ::= next, n ::= n - 1]] }

/-- The word standing for a plan nested too deeply: no address reaches it either. -/
def deep_ : Expr := .lit 18446744073709551614

/-- The deepest nesting a plan may have, which bounds the stack every walk of it uses. -/
abbrev maxNesting : Nat := 64

/--
The address past one node, when the node and all below it fit before the plan's end and nest at most a budget deep:
arguments the node, the plan's end, the budget.

Otherwise the word standing for none, or the word standing for too deep when the budget runs out first.
Only the counts that place the nodes are read, so the walk is safe on any words.
-/
def depthFn : Fn :=
  let p : Var := ⟨0⟩
  let stop : Var := ⟨1⟩
  let budget : Var := ⟨2⟩
  let t : Var := ⟨3⟩
  let n : Var := ⟨4⟩
  let q : Var := ⟨5⟩
  { params := 3, vars := 6, result := q,
    body := .block [q ::= none_,
      when (le (p + 8) stop) [t ::= ld p,
      ifElse (eq budget 0) [q ::= deep_]
      [ifElse (eq t 0) [q ::= p + 8]
      [ifElse (le t 5) [when (le (p + 16) stop) [q ::= p + 16]]
      [ifElse (eq t 6) [when (le (p + 24) stop) [q ::= p + 24]]
      [ifElse (le t 8) [when (le (p + 16) stop) [callInto q "ssz_validate_depth" [p + 16, stop, budget - 1]]]
      [ifElse (eq t 9) [when (le (p + 24) stop) [callInto q "ssz_validate_depth" [p + 24, stop, budget - 1]]]
      [ifElse (eq t 10) [when (le (p + 16) stop)
          [callInto q "ssz_validate_depth_all" [p + 16, word p 1, stop, budget - 1]]]
      -- A progressive container: its layout bits and its field count must fit, then its fields.
      [ifElse (eq t 11) [when (le (p + 16) stop) [n ::= word p 1,
          when (both (lt n bound32) (le (p + 24 + 8 * n) stop))
            [callInto q "ssz_validate_depth_all" [p + 24 + 8 * n, ld (p + 16 + 8 * n), stop, budget - 1]]]]
      -- A union: its selectors must fit, then its options.
      [when (eq t 12) [when (le (p + 16) stop) [n ::= word p 1,
          when (both (lt n bound32) (le (p + 16 + 8 * n) stop))
            [callInto q "ssz_validate_depth_all" [p + 16 + 8 * n, n, stop, budget - 1]]]]]]]]]]]]]] }

/--
The address past a count of nodes walked as one node is, or the word standing for none or for too deep: arguments the
first node, the count, the plan's end, the budget.

Each node takes at least a word, so the walk stops by the plan's end however large the count.
-/
def depthAllFn : Fn :=
  let q : Var := ⟨0⟩
  let n : Var := ⟨1⟩
  let stop : Var := ⟨2⟩
  let budget : Var := ⟨3⟩
  { params := 4, vars := 4, result := q,
    body := while_ (both (ne n 0) (le q stop)) [callInto q "ssz_validate_depth" [q, stop, budget], n ::= n - 1] }

/--
The plan's check alone: arguments the plan and its length in bytes.

Returns zero when the plan reads back as one type, nested at most the deepest a plan may be, legally declared, and
within the native check's sizes.
Returns three when the plan nests deeper than that, and two when it is refused otherwise.
Every walk of an accepted plan then needs a stack bounded by a constant.
-/
def checkPlanFn : Fn :=
  let plan : Var := ⟨0⟩
  let planLen : Var := ⟨1⟩
  let r : Var := ⟨2⟩
  let q : Var := ⟨3⟩
  { params := 2, vars := 4, result := r,
    body := .block [r ::= 2,
      when (eq (planLen % 8) 0) [callInto q "ssz_validate_depth" [plan, plan + planLen, (maxNesting : Expr)],
        ifElse (eq q deep_) [r ::= 3]
          [when (eq q (plan + planLen)) [callInto q "ssz_validate_plan" [plan, plan + planLen],
            when (eq q (plan + planLen)) [r ::= 0]]]]] }

/--
The decoding check: arguments the plan, its length in bytes, the encoding, its length, err.

Returns zero when the encoding is accepted, one when it is refused with the refusal written at err, two when the
plan is refused, and three when the plan nests too deeply.
-/
def validateFn : Fn :=
  let plan : Var := ⟨0⟩
  let planLen : Var := ⟨1⟩
  let data : Var := ⟨2⟩
  let len : Var := ⟨3⟩
  let err : Var := ⟨4⟩
  let r : Var := ⟨5⟩
  { params := 5, vars := 6, result := r,
    body := .block [callInto r "ssz_check_plan" [plan, planLen],
      when (eq r 0) [callInto r "ssz_validate_range" [plan, data, data + len, err]]] }

/-- The functions of the check, under their exported names. -/
def fns : List (String × Fn) :=
  [("ssz_validate", validateFn),
    ("ssz_validate_fail", failFn),
    ("ssz_validate_skip", skipFn),
    ("ssz_validate_skip_all", skipAllFn),
    ("ssz_validate_width", widthFn),
    ("ssz_validate_fields_width", fieldsWidthFn),
    ("ssz_validate_leading", leadingFn),
    ("ssz_validate_has_probes", hasProbesFn),
    ("ssz_validate_any_probes", anyProbesFn),
    ("ssz_validate_probe", probeFn),
    ("ssz_validate_records", recordsFn),
    ("ssz_validate_fields_probe", fieldsProbeFn),
    ("ssz_validate_delimited", delimitedFn),
    ("ssz_validate_spans", spansFn),
    ("ssz_validate_each", eachFn),
    ("ssz_validate_vector", vectorFn),
    ("ssz_validate_list", listFn),
    ("ssz_validate_inline", inlineFn),
    ("ssz_validate_struct_spans", structSpansFn),
    ("ssz_validate_next_body", nextBodyFn),
    ("ssz_validate_fields", fieldsFn),
    ("ssz_validate_struct", structFn),
    ("ssz_validate_option", optionFn),
    ("ssz_validate_range", rangeFn),
    ("ssz_validate_eq", eqFn),
    ("ssz_validate_bytes", bytesFn),
    ("ssz_validate_compat", compatFn),
    ("ssz_validate_compat_all", compatAllFn),
    ("ssz_validate_options_agree", optionsAgreeFn),
    ("ssz_validate_layouts", layoutsFn),
    ("ssz_validate_plan", planFn),
    ("ssz_validate_plan_all", planAllFn),
    ("ssz_validate_pairs", pairsFn),
    ("ssz_validate_depth", depthFn),
    ("ssz_validate_depth_all", depthAllFn),
    ("ssz_check_plan", checkPlanFn)]

/-- Every function fits the compiler's assumptions. -/
theorem fns_wf : fns.all (fun p => p.2.wf) = true := by decide +kernel

end Ssz.Native.Driver.Validate
