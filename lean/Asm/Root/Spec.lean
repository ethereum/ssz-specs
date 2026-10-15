import Ssz.Proofs.Codec.RootLaws
import Ssz.Proofs.Codec.RootDomain

/-!
The root of a fixed-size value, computed from its encoding alone.

A fixed-size type's encoding is its fields' encodings back to back, with no offsets.
Each field's bytes are therefore a fixed slice, and its root can be taken from that slice.
-/

namespace Ssz.Asm.Root

open Ssz

mutual

/-- Types built from booleans, integers, byte and bit vectors, vectors, and containers. -/
def plain : Desc → Bool
  | .bool => true
  | .uint _ => true
  | .byteVector _ => true
  | .bitVector _ => true
  | .vector element _ => plain element
  | .container _ fields => plainAll fields
  | _ => false

/-- Every type in a list is plain. -/
def plainAll : List Desc → Bool
  | [] => true
  | field :: fields => plain field && plainAll fields

end

mutual

/-- Encoded width in bytes of a plain type. -/
def width : Desc → Nat
  | .bool => 1
  | .uint w => w
  | .byteVector n => n
  | .bitVector n => (n + 7) / 8
  | .vector element n => width element * n
  | .container _ fields => (widths fields).sum
  | _ => 0

/-- Encoded widths of a list of types. -/
def widths : List Desc → List Nat
  | [] => []
  | field :: fields => width field :: widths fields

end

/-- Bytes concatenated in order. -/
def joined : List Bytes → Bytes
  | [] => #[]
  | part :: parts => part ++ joined parts

/-- Consecutive slices of the given widths. -/
def slices : List Nat → Bytes → List Bytes
  | [], _ => []
  | w :: ws, bytes => bytes.extract 0 w :: slices ws (bytes.extract w bytes.size)

/-- The root of packed bytes: split into chunks, and the tree just wide enough to hold them. -/
def packedRoot (bytes : Bytes) : Bytes :=
  subtreeAt (packBytes bytes) (depthFor (packBytes bytes).size) 0

mutual

/-- The root of a plain type, from its encoding. -/
def rootOf : Desc → Bytes → Bytes
  | .vector element n, bytes =>
    -- Basic elements share chunks, and anything else brings a root of its own.
    if element.isBasic then packedRoot bytes
    else subtreeAt ((slices (List.replicate n (width element)) bytes).map (rootOf element)).toArray
      (depthFor n) 0
  | .container _ fields, bytes =>
    subtreeAt (rootsOf fields (slices (widths fields) bytes)).toArray (depthFor fields.length) 0
  | _, bytes => packedRoot bytes

/-- The roots of a list of types, each from its own slice. -/
def rootsOf : List Desc → List Bytes → List Bytes
  | field :: fields, part :: parts => rootOf field part :: rootsOf fields parts
  | _, _ => []

end

end Ssz.Asm.Root
