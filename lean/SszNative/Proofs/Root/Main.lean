import SszNative.Proofs.Root.Variable.Agree
import SszNative.Proofs.Root.Variable.Bridge

/-! The native root of an encoding is the specification's root of the value it decodes to, or the same refusal. -/

namespace Ssz.Native

open Ssz

/--
Given what the trees and the fixed-size roots compute, the native root agrees with the specification.

The type is well formed, and the encoding small enough that every buffer the root builds has machine-sized offsets.
-/
theorem hashTreeRoot_eq_of (facts : RootProof.Facts) (d : Desc) (sound : d.wellFormed = .ok ()) (b : ByteArray)
    (small : RootProof.Small b) :
    (hashTreeRoot d b).map ByteArray.data = (do let v ← deserialize d b.data; Ssz.hashTreeRoot d v) := by
  -- The check refuses exactly what decoding refuses, with the same reason.
  have whole : slice b 0 b.size = b.data := by simp [slice, ← ByteArray.size_data]
  simp only [hashTreeRoot, validate_eq, Bind.bind, Except.bind, Except.map, pure, Except.pure]
  cases decoded : deserialize d b.data with
  | error e => rfl
  | ok v =>
    -- An accepted encoding is rooted in place, to the root of the value it holds.
    have rooted := RootProof.agrees facts d sound b 0 b.size v (Nat.zero_le _) (Nat.le_refl _) small
      (by rw [whole]; exact decoded)
    simp only [rooted]

/--
The native root of an encoding is the specification's root of the value it decodes to, or the same refusal.

The type is well formed, and the encoding small enough that every buffer the root builds has machine-sized offsets.
The caller supplies the exact bound below; the theorem does not prove allocation success.
-/
theorem hashTreeRoot_eq (d : Desc) (sound : d.wellFormed = .ok ()) (b : ByteArray)
    (small : 64 * b.size + 128 < USize.size) :
    (hashTreeRoot d b).map ByteArray.data = (do let v ← deserialize d b.data; Ssz.hashTreeRoot d v) :=
  hashTreeRoot_eq_of RootProof.facts_hold d sound b small

end Ssz.Native
