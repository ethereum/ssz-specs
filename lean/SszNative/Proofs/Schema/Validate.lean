import SszNative.Schema
import SszNative.Proofs.Validate.Fixed
import SszNative.Proofs.Root.Record

/-! A compiled declaration refuses exactly what its declaration refuses. -/

namespace Ssz.Native

open Ssz

/-- The check of a fixed-size value over a whole encoding: the two size checks, then the probes. -/
theorem validateFixed_whole (d : Desc) (width : Nat) (b : ByteArray) :
    validateFixed d width b 0 b.size =
      if composite d && b.size ≥ 4294967296 then .error (.offsetOverflow b.size)
      else if b.size != width then .error (.scope width b.size)
      else checkRuns b 0 (runs d) := by
  -- The range is the whole buffer, and the bound is 2^32.
  simp only [validateFixed, Nat.sub_zero, bytesPerOffset]
  by_cases big : (composite d && decide (b.size ≥ 4294967296)) = true
  · simp [big, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
  · by_cases wrong : (b.size != width) = true
    · simp [big, wrong, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    · simp [big, wrong]

/-- A compiled declaration refuses exactly what its declaration refuses, with the same reason. -/
theorem Schema.validate_compile (d : Desc) (b : ByteArray) :
    (Schema.compile d).validate b = Native.validate d b := by
  unfold Schema.compile fixedOf
  split
  · rename_i names fields
    split
    · -- A struct of fixed-size fields: its sizes, then its probes.
      rename_i p
      simp only [Schema.validate, Native.validate]
      rw [validateRange, if_pos (plain_hasWidth _ p), validateFixed_whole]
    · -- Any other struct takes the general check.
      rfl
  · -- Any other declaration takes the general check.
    rfl

/-- Every schema is its declaration compiled, since its cache cannot be supplied separately. -/
theorem Schema.eq_compile (s : Schema) : s = Schema.compile s.desc := by
  obtain ⟨d, f, compiled⟩ := s
  subst compiled
  rfl

/-- Every schema refuses exactly what its declaration refuses, with the same reason. -/
theorem Schema.validate_eq (s : Schema) (b : ByteArray) : s.validate b = Native.validate s.desc b := by
  rw [s.eq_compile]
  exact Schema.validate_compile s.desc b

end Ssz.Native
