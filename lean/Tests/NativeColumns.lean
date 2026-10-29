import SszNative
import Ssz.Type.Valid

/-! Composite vector columns preserve element and record order, including wide vectors. -/

namespace Tests.NativeColumns

open Ssz

private def check (width : Nat) : IO Unit := do
  let shape := Desc.list (.vector (.byteVector 1) width) 2
  -- Distinct positions prevent a reversed or duplicated column list from agreeing by accident.
  let bytes : ByteArray := ⟨(Array.range (2 * width)).map fun i =>
    UInt8.ofNat (i * 131 + i / 251)⟩
  unless shape.wellFormed.isOk do throw (IO.userError "invalid composite vector regression schema")
  let reference := do
    let value ← deserialize shape bytes.data
    hashTreeRoot shape value
  match reference, Native.hashTreeRoot shape bytes with
  | .ok expected, .ok actual =>
    unless actual.data == expected do
      throw (IO.userError s!"composite vector columns disagree at width {width}")
  | _, _ => throw (IO.userError s!"valid composite vector refused at width {width}")

def run : IO Unit := do
  -- Both odd padding and the formerly quadratic wide-column path must be exercised.
  for width in [1, 2, 3, 17, 128, 16000] do check width

end Tests.NativeColumns
