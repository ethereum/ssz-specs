import EthLib.Consensus.Ssz.Type.Desc

/-!
A type, written as bytes that any language can produce and the native code can walk.

A plan is a sequence of 64-bit little-endian words, one type node after another in prefix order:

```text
    node := tag, then by tag:
      0  boolean
      1  unsigned integer              width in bytes
      2  byte vector                   length
      3  byte list                     limit
      4  bit vector                    length
      5  bit list                      limit
      6  progressive bit list          has-limit, limit
      7  vector                        length, element node
      8  list                          limit, element node
      9  progressive list              has-limit, limit, element node
     10  container                     field count, field nodes
     11  progressive container         layout length, layout bits, field count, field nodes
     12  compatible union              option count, selectors, option nodes
```

A plan is written one way only: a layout bit is zero or one, and an absent bound is two zero words.
Reading refuses any other spelling, so a plan read back is exactly the plan of the type it reads.

Field names never reach bytes or roots, so a plan carries none.
Reading a plan back names each field by its position: a struct's by its ordinal, a progressive container's by the
layout position it sits at.
Those names are distinct, and two progressive containers name a shared position alike, so every legal type stays
legal.
-/

namespace EthLib.Consensus.Ssz.Native.Plan

open EthLib.Consensus.Ssz

/-- The tag word of a type node. -/
def tag : Desc → Nat
  | .bool => 0 | .uint _ => 1 | .byteVector _ => 2 | .byteList _ => 3 | .bitVector _ => 4 | .bitList _ => 5
  | .progressiveBitList _ => 6 | .vector _ _ => 7 | .list _ _ => 8 | .progressiveList _ _ => 9
  | .container _ _ => 10 | .progressiveContainer _ _ _ => 11 | .compatibleUnion _ _ => 12

/-- An optional bound as two words: whether there is one, and its value. -/
def bound : Option Nat → List Nat
  | none => [0, 0]
  | some b => [1, b]

mutual

/-- A type's words, in prefix order. -/
def words : Desc → List Nat
  | .bool => [0]
  | .uint width => [1, width]
  | .byteVector length => [2, length]
  | .byteList limit => [3, limit]
  | .bitVector length => [4, length]
  | .bitList limit => [5, limit]
  | .progressiveBitList limit => 6 :: bound limit
  | .vector element length => [7, length] ++ words element
  | .list element limit => [8, limit] ++ words element
  | .progressiveList element limit => 9 :: bound limit ++ words element
  | .container _ fields => [10, fields.length] ++ wordsAll fields
  | .progressiveContainer active _ fields =>
    [11, active.length] ++ active.map (fun b => if b then 1 else 0) ++ [fields.length] ++ wordsAll fields
  | .compatibleUnion selectors options => [12, options.length] ++ selectors ++ wordsAll options

/-- Several types' words, one after the other. -/
def wordsAll : List Desc → List Nat
  | [] => []
  | d :: rest => words d ++ wordsAll rest

end

/-- A word's eight little-endian bytes. -/
def wordBytes (w : Nat) : List UInt8 :=
  (List.range 8).map fun k => UInt8.ofNat (w >>> (8 * k))

/-- A type's plan, as the bytes the native code reads. -/
def encode (d : Desc) : ByteArray :=
  ⟨((words d).flatMap wordBytes).toArray⟩

/-- Field names by position, for a count of fields. -/
def positionNames (n : Nat) : List String :=
  (List.range n).map toString

/-- The positions a layout sets, in order. -/
def layoutPositions (active : List Bool) : List Nat :=
  active.zipIdx.filterMap fun (present, position) => if present then some position else none

/-- Field names by layout position, one for each position a layout sets. -/
def layoutNames (active : List Bool) : List String :=
  (layoutPositions active).map toString

mutual

/-- A type with every field named as reading its plan back names it. -/
def rename : Desc → Desc
  | .vector element length => .vector (rename element) length
  | .list element limit => .list (rename element) limit
  | .progressiveList element limit => .progressiveList (rename element) limit
  | .container _ fields => .container (positionNames fields.length) (renameAll fields)
  | .progressiveContainer active _ fields =>
    .progressiveContainer active (layoutNames active) (renameAll fields)
  | .compatibleUnion selectors options => .compatibleUnion selectors (renameAll options)
  | d => d

/-- Several types, each renamed. -/
def renameAll : List Desc → List Desc
  | [] => []
  | d :: rest => rename d :: renameAll rest

end

mutual

/-- Whether every union in a type pairs one selector with each option, which its plan needs to be read back. -/
def paired : Desc → Bool
  | .vector element _ | .list element _ | .progressiveList element _ => paired element
  | .container _ fields | .progressiveContainer _ _ fields => pairedAll fields
  | .compatibleUnion selectors options => selectors.length == options.length && pairedAll options
  | _ => true

/-- Whether every union in several types pairs its selectors with its options. -/
def pairedAll : List Desc → Bool
  | [] => true
  | d :: rest => paired d && pairedAll rest

end

/-- A bound read back from its two words. -/
def readBound (has value : Nat) : Option Nat :=
  if has == 0 then none else some value

/-- Whether two words spell a bound as a plan writes one: two zeros for none, a one then the value for some. -/
def canonicalBound (has value : Nat) : Bool :=
  (has == 0 && value == 0) || has == 1

mutual

/-- One type read from words, with the words after it; fuel bounds the nesting. -/
def readNode : (fuel : Nat) → List Nat → Option (Desc × List Nat)
  | 0, _ => none
  | fuel + 1, t :: rest =>
    match t, rest with
    | 0, rest => some (.bool, rest)
    | 1, w :: rest => some (.uint w, rest)
    | 2, n :: rest => some (.byteVector n, rest)
    | 3, n :: rest => some (.byteList n, rest)
    | 4, n :: rest => some (.bitVector n, rest)
    | 5, n :: rest => some (.bitList n, rest)
    | 6, h :: n :: rest => if canonicalBound h n then some (.progressiveBitList (readBound h n), rest) else none
    | 7, n :: rest => (readNode fuel rest).map fun (e, rest) => (.vector e n, rest)
    | 8, n :: rest => (readNode fuel rest).map fun (e, rest) => (.list e n, rest)
    | 9, h :: n :: rest =>
      if canonicalBound h n then (readNode fuel rest).map fun (e, rest) => (.progressiveList e (readBound h n), rest)
      else none
    | 10, n :: rest => (readNodes fuel n rest).map fun (fs, rest) => (.container (positionNames n) fs, rest)
    | 11, k :: rest =>
      let active := (rest.take k).map (· != 0)
      if (rest.take k).all (· ≤ 1) then
        match rest.drop k with
        | n :: rest => (readNodes fuel n rest).map fun (fs, rest) =>
            (.progressiveContainer active (layoutNames active) fs, rest)
        | [] => none
      else none
    | 12, n :: rest =>
      let selectors := rest.take n
      (readNodes fuel n (rest.drop n)).map fun (os, rest) => (.compatibleUnion selectors os, rest)
    | _, _ => none
  | _, [] => none

/-- A count of types read from words, one after the other. -/
def readNodes : (fuel : Nat) → Nat → List Nat → Option (List Desc × List Nat)
  | _, 0, rest => some ([], rest)
  | 0, _ + 1, _ => none
  | fuel + 1, n + 1, rest => do
    let (d, rest) ← readNode fuel rest
    let (ds, rest) ← readNodes fuel n rest
    return (d :: ds, rest)

end

/-- The words of a plan's bytes, eight bytes each, little-endian. -/
def toWords (b : ByteArray) : List Nat :=
  (List.range (b.size / 8)).map fun i =>
    (List.range 8).foldl (fun acc k => acc + (b.get! (8 * i + k)).toNat * 256 ^ k) 0

/-- The type a plan writes, when its bytes are exactly one type's words. -/
def decode (b : ByteArray) : Option Desc :=
  if b.size % 8 != 0 then none
  else
    let ws := toWords b
    match readNode ws.length ws with
    | some (d, []) => some d
    | _ => none

end EthLib.Consensus.Ssz.Native.Plan
