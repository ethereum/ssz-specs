import Asm.Memory

/-! The register arithmetic the loops do on small counts and offsets. -/

namespace Ssz.Asm.Merkle

theorem ofNat_add_one {n : Nat} :
    BitVec.ofNat 64 n + (BitVec.ofNat 12 1).signExtend 64 = BitVec.ofNat 64 (n + 1) := by
  rw [signExtend_ofNat12 (by omega), ← BitVec.ofNat_add]

theorem ofNat_add_imm {a : BitVec 64} {c : Nat} (small : c < 2048) :
    a + (BitVec.ofNat 12 c).signExtend 64 = a + BitVec.ofNat 64 c := by
  rw [signExtend_ofNat12 small]

theorem ofNat_half {n : Nat} (small : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> (1 % 64) = BitVec.ofNat 64 (n / 2) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt small]
  omega

theorem ofNat_shift {i s : Nat} (small : 2 ^ s * i < 2 ^ 64) (short : s < 64) :
    BitVec.ofNat 64 i <<< (s % 64) = BitVec.ofNat 64 (2 ^ s * i) := by
  apply BitVec.eq_of_toNat_eq
  rw [Nat.mod_eq_of_lt short, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show i < 2 ^ 64 by
      have : 1 ≤ 2 ^ s := Nat.one_le_two_pow
      calc i ≤ 2 ^ s * i := Nat.le_mul_of_pos_left i this
        _ < 2 ^ 64 := small)]
  rw [Nat.mul_comm]

theorem ofNat_lt_iff {a b : Nat} (smallA : a < 2 ^ 64) (smallB : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).toNat < (BitVec.ofNat 64 b).toNat ↔ a < b := by
  simp [Nat.mod_eq_of_lt smallA, Nat.mod_eq_of_lt smallB]

theorem ofNat_eq_iff {a b : Nat} (smallA : a < 2 ^ 64) (smallB : b < 2 ^ 64) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro same
    have := congrArg BitVec.toNat same
    simpa [Nat.mod_eq_of_lt smallA, Nat.mod_eq_of_lt smallB] using this
  · rintro rfl
    rfl

end Ssz.Asm.Merkle
