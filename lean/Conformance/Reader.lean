import Ssz
import Lean.Data.Json

/-! Reading the declaration, the value, and the path one conformance vector carries. -/

namespace Conformance

open Ssz Lean

/-- A refusal, printed. -/
def describe (fault : Err) : String := toString (repr fault)

/-- Turn a refusal into a message, so both sides report failures the same way. -/
def orFail {α : Type} (name : String) : Except Err α → Except String α
  | .ok value => .ok value
  | .error fault => .error s!"{name} refused: {describe fault}"

/-- The field under a name, if the vector has one. -/
def field? (json : Json) (name : String) : Option Json :=
  (json.getObjVal? name).toOption

/-- The field under a name, required. -/
def field (json : Json) (name : String) : Except String Json :=
  match field? json name with
  | some value => .ok value
  | none => .error s!"no {name} in the vector"

/-- The text a field holds. -/
def text (json : Json) : Except String String :=
  match json with
  | .str value => .ok value
  | _ => .error "expected a string"

/-- The bytes a hex field holds, which is how a vector writes every byte string. -/
def bytes (json : Json) : Except String Bytes := do
  match ofHex (← text json) with
  | .ok data => .ok data
  | .error fault => .error s!"unreadable hex: {describe fault}"

/-- The number a decimal-string field holds, which is how a vector writes every index. -/
def number (json : Json) : Except String Nat := do
  match (← text json).toNat? with
  | some value => .ok value
  | none => .error "expected decimal digits in a string"

/-- The number a bare-number field holds, used for the counts and the path positions. -/
def plain (json : Json) : Except String Nat :=
  match json with
  | .num value =>
    if value.exponent == 0 && value.mantissa ≥ 0 then .ok value.mantissa.toNat
    else .error "expected a whole number"
  | _ => .error "expected a number"

/-- The entries an array field holds. -/
def entries (json : Json) : Except String (List Json) :=
  match json with
  | .arr values => .ok values.toList
  | _ => .error "expected an array"

/-- The bytes a named hex field holds. -/
def hexField (vector : Json) (name : String) : Except String Bytes := do
  bytes (← field vector name)

/-- The number a named decimal-string field holds. -/
def numberField (vector : Json) (name : String) : Except String Nat := do
  number (← field vector name)

/-- The number a named bare-number field holds. -/
def plainField (vector : Json) (name : String) : Except String Nat := do
  plain (← field vector name)

/-- The bytes each entry of a named array field holds. -/
def hexList (vector : Json) (name : String) : Except String (List Bytes) := do
  (← entries (← field vector name)).mapM bytes

/-- The number each entry of a named array field holds. -/
def numberList (vector : Json) (name : String) : Except String (List Nat) := do
  (← entries (← field vector name)).mapM number

/--
Whether a kind names an unsigned integer of some width.

A vector can name a width SSZ does not define.

Refusing that is the declaration check's job, not this reader's.

Reading only the six defined widths would report the wrong reason.
-/
private def isUintKind (kind : String) : Bool :=
  kind.startsWith "Uint" && kind.length > 4 && (kind.toList.drop 4).all Char.isDigit

/-- The declaration keys each kind is entitled to, beyond the kind itself. -/
private def entitledKeys : String → Except Err (List String)
  | "Boolean" => .ok []
  | "ProgressiveBitList" => .ok ["limit"]
  | "Byte" => .ok ["bits"]
  | "BitVector" | "ByteVector" => .ok ["length"]
  | "BitList" | "ByteList" => .ok ["limit"]
  | "Vector" => .ok ["length", "elementType"]
  | "List" => .ok ["limit", "elementType"]
  | "ProgressiveList" => .ok ["limit", "elementType"]
  | "Container" => .ok ["fields"]
  | "ProgressiveContainer" => .ok ["activeFields", "fields"]
  | "CompatibleUnion" => .ok ["options"]
  | kind => if isUintKind kind then .ok ["bits"] else .error .badDeclaration

/-- The keys a kind may leave out, a progressive shape stating a bound only where it has one. -/
private def optionalKeys : String → List String
  | "ProgressiveBitList" | "ProgressiveList" => ["limit"]
  | _ => []

/-- The name a declaration gives a field. -/
private def name (json : Json) : Except Err String :=
  match json with
  | .str value => .ok value
  | _ => .error .badDeclaration

/-- A count a declaration states, refused where it is written as a negative number. -/
private def count (json : Json) : Except Err Nat :=
  match json with
  | .num value =>
    if value.mantissa < 0 then .error .capacityNegative
    else if value.exponent != 0 then .error .badDeclaration
    else .ok value.mantissa.toNat
  | _ => .error .badDeclaration

/-- One layout position, which is a gap or a field. -/
private def layoutBit (json : Json) : Except Err Bool :=
  match json with
  | .num value =>
    if value.mantissa == 0 then .ok false
    else if value.mantissa == 1 then .ok true
    else .error .layoutNotBits
  | .bool bit => .ok bit
  | _ => .error .layoutNotBits

/-- The declaration a vector carries, together with where it spells the byte alias. -/
partial def readDescriptor (json : Json) : Except Err (Desc × Spelling) := do
  let .obj carried := json | throw .badDeclaration
  let names := carried.toList.map fun (name, _) => name
  let .some kindField := field? json "kind" | throw .undeclared
  let .str kind := kindField | throw .badDeclaration
  let allowed ← entitledKeys kind
  for name in names do
    if name != "kind" && !allowed.contains name then throw .notEntitled
  let optional := optionalKeys kind
  for name in allowed do
    if !names.contains name && !optional.contains name then throw .undeclared
  let stated (name : String) : Except Err Nat := do
    let .some value := field? json name | throw .undeclared
    count value
  let bound : Except Err (Option Nat) := do
    let .some value := field? json "limit" | return none
    return some (← count value)
  let element : Except Err (Desc × Spelling) := do
    let .some value := field? json "elementType" | throw .undeclared
    readDescriptor value
  let held (key marker : String) : Except Err (List (Json × Desc × Spelling)) := do
    let .some value := field? json key | throw .undeclared
    let .arr parts := value | throw .badDeclaration
    let mut out := []
    for part in parts do
      let .some label := field? part marker | throw .undeclared
      let .some declared := field? part "type" | throw .undeclared
      let (shape, spelling) ← readDescriptor declared
      out := out ++ [(label, shape, spelling)]
    return out
  match kind with
  | "Boolean" => return (.bool, .opaque)
  | "Byte" => return (.uint 1, .byte)
  | "BitVector" => return (.bitVector (← stated "length"), .opaque)
  | "BitList" => return (.bitList (← stated "limit"), .opaque)
  | "ProgressiveBitList" => return (.progressiveBitList (← bound), .opaque)
  | "ByteVector" => return (.byteVector (← stated "length"), .opaque)
  | "ByteList" => return (.byteList (← stated "limit"), .opaque)
  | "Vector" =>
    let (shape, spelling) ← element
    return (.vector shape (← stated "length"), .plain [spelling])
  | "List" =>
    let (shape, spelling) ← element
    return (.list shape (← stated "limit"), .plain [spelling])
  | "ProgressiveList" =>
    let (shape, spelling) ← element
    return (.progressiveList shape (← bound), .plain [spelling])
  | "Container" =>
    let parts ← held "fields" "name"
    return (.container (← parts.mapM fun (label, _) => name label)
      (parts.map fun (_, shape, _) => shape), .plain (parts.map fun (_, _, s) => s))
  | "ProgressiveContainer" =>
    let .some layout := field? json "activeFields" | throw .undeclared
    let .arr positions := layout | throw .layoutNotBits
    let active ← positions.toList.mapM layoutBit
    let parts ← held "fields" "name"
    return (.progressiveContainer active (← parts.mapM fun (label, _) => name label)
      (parts.map fun (_, shape, _) => shape), .plain (parts.map fun (_, _, s) => s))
  | "CompatibleUnion" =>
    let parts ← held "options" "selector"
    return (.compatibleUnion (← parts.mapM fun (label, _) => count label)
      (parts.map fun (_, shape, _) => shape), .plain (parts.map fun (_, _, s) => s))
  | kind =>
    if !isUintKind kind then throw .badDeclaration
    let bits ← stated "bits"
    -- A width that is no whole number of bytes is refused as a width, not as an odd kind.
    if bits == 0 || bits % 8 != 0 then throw (.uintWidth bits)
    return (.uint (bits / 8), .opaque)


/--
One step of a path, in the spelling a vector writes it.

A name is a struct field, and a position is an element or a union selector.

A word is one of the three a root is hashed against.
-/
inductive Step where
  /-- A struct field, named rather than counted, since names are not part of SSZ. -/
  | named (name : String)
  /-- An element position or a union selector, which cannot be negative. -/
  | at (position : Int)
  /-- A word a root is hashed against, which ends the path. -/
  | word (name : String)

/-- The step a generalized-index vector writes, where the JSON type gives the kind. -/
def readIndexStep (json : Json) : Except String Step :=
  match json with
  | .str name => .ok (.named name)
  | .num value => if value.exponent == 0 then .ok (.at value.mantissa)
      else .error "a position is a whole number"
  | .obj _ => do return .word (← text (← field json "mixin"))
  | _ => .error "a path step is a name, a position, or a mixed-in word"

/-- The step a proof vector writes, where a one-key object gives the kind. -/
def readProofStep (json : Json) : Except String Step := do
  if let some name := field? json "field" then return .named (← text name)
  -- A position is a bare number here, where a generalized index is decimal digits in a string.
  if let some position := field? json "position" then return .at (← plain position)
  if let some word := field? json "mixin" then return .word (← text word)
  .error "a path step names a field, a position, or a mixed-in word"

/-- The word a vector names, in either of the two spellings the formats use. -/
private def readWord : String → Except Err PathStep
  | "elementCount" | "__len__" => .ok .length
  | "fieldLayout" | "__active_fields__" => .ok .activeFields
  | "typeSelector" | "__selector__" => .ok .selector
  | _ => .error .noMixin

/-- The declared field names of a struct, if the shape has any. -/
private def fieldNames : Desc → Option (List String)
  | .container names _ => some names
  | .progressiveContainer _ names _ => some names
  | _ => none

/--
The steps a path takes, resolved against the declaration as the walk descends.

A vector names a struct field, and a declaration counts it.

Converting between the two needs the shape the step was taken against.

Once a step reaches no further shape, a name can no longer be converted.

The remaining steps are passed on as positions for the resolver to refuse.
-/
def readPath (shape : Desc) (steps : List Step) : Except Err (List PathStep) := do
  let mut reached : Option Desc := some shape
  let mut out : List PathStep := []
  for step in steps do
    let resolved : PathStep ← match step with
      | .word name => readWord name
      | .at position =>
        if position < 0 then throw (.noSuchPosition 0) else pure (.position position.toNat)
      | .named name => match reached.bind fieldNames with
        | none => if reached.isSome then throw .notAPosition else pure (.position 0)
        | some names => match names.idxOf? name with
          | some ordinal => pure (.position ordinal)
          | none => throw (.noSuchField 0)
    out := out ++ [resolved]
    reached := reached.bind fun current =>
      match current.resolveStep resolved with
      | .ok (_, child) => child
      | .error _ => none
  return out

end Conformance
