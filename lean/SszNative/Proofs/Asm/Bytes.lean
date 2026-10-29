import SszNative.Asm.Semantics

/-! Little-endian loads and stores of up to eight bytes, as numbers. -/

namespace Ssz.Native.Asm

/-- Bytes from an address as a little-endian natural number. -/
def bytesNat (mem : Nat → UInt8) (a : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (mem a).toNat + 256 * bytesNat mem (a + 1) n

/-- A count of bytes reads as a number below 256 to that count. -/
theorem bytesNat_lt (mem : Nat → UInt8) (a n : Nat) : bytesNat mem a n < 256 ^ n := by
  induction n generalizing a with
  | zero => simp [bytesNat]
  | succ n ih =>
    have := ih (a + 1); have := (mem a).toNat_lt
    simp only [bytesNat, Nat.pow_succ]
    omega

/-- A little-endian load of at most eight bytes is the number its bytes spell. -/
theorem readLE_toNat (mem : Nat → UInt8) (a n : Nat) (hn : n ≤ 8) :
    (readLE mem a n).toNat = bytesNat mem a n := by
  induction n generalizing a with
  | zero => simp [readLE, bytesNat]
  | succ n ih =>
    simp only [readLE, bytesNat]
    have rest := ih (a + 1) (by omega)
    have bound := bytesNat_lt mem (a + 1) n
    have small : 256 ^ n ≤ 2 ^ 56 := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact Nat.pow_le_pow_right (by decide) (by omega)
    rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, rest]
    simp only [UInt8.toNat_toUInt64, show ((8 : UInt64).toNat % 64) = 8 from rfl]
    rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega), Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (mem a).toNat_lt,
      Nat.shiftLeft_eq]
    omega

/-- Byte k of a word is its k-th base-256 digit. -/
theorem qwordByte_toNat (v : UInt64) (k : Nat) (hk : k < 8) : (qwordByte v k).toNat = v.toNat / 256 ^ k % 256 := by
  simp only [qwordByte, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight]
  rw [show (8 * k).toUInt64.toNat % 64 = 8 * k by simp; omega, Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-- Bytes that are the digits of a number, from some digit on, read back as the number's digits from there. -/
theorem bytesNat_digits (f : Nat → UInt8) (a v j n : Nat)
    (digits : ∀ k < n, (f (a + k)).toNat = v / 256 ^ (j + k) % 256) :
    bytesNat f a n = v / 256 ^ j % 256 ^ n := by
  induction n generalizing a j with
  | zero => simp [bytesNat, Nat.mod_one]
  | succ n ih =>
    simp only [bytesNat]
    have h0 := digits 0 (by omega)
    have rest := ih (a + 1) (j + 1) (fun k hk => by
      have := digits (k + 1) (by omega); simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this)
    simp only [Nat.add_zero] at h0
    rw [h0, rest, Nat.pow_succ, ← Nat.div_div_eq_div_mul, Nat.pow_succ 256 n, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]

/-- A word stored and read back at the same width is the word cut to that width. -/
theorem readLE_store (mem : Nat → UInt8) (a w : Nat) (hw : w ≤ 8) (v : UInt64) :
    (readLE (store mem a w (qwordByte v)) a w).toNat = v.toNat % 256 ^ w := by
  rw [readLE_toNat _ _ _ hw, bytesNat_digits _ a v.toNat 0 w (fun k hk => by
    simp only [store, show a ≤ a + k by omega, show a + k < a + w by omega, and_self, if_true,
      Nat.add_sub_cancel_left, Nat.zero_add]
    exact qwordByte_toNat v k (by omega))]
  simp

/-- A word stored as eight bytes reads back as itself. -/
theorem readLE_store8 (mem : Nat → UInt8) (a : Nat) (v : UInt64) : readLE (store mem a 8 (qwordByte v)) a 8 = v := by
  apply UInt64.toNat_inj.mp
  rw [readLE_store _ _ _ (by decide)]
  exact Nat.mod_eq_of_lt v.toNat_lt

end Ssz.Native.Asm
