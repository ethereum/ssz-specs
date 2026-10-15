import Asm.Block
import Asm.Word

/-! Address ranges, and what loads see after stores to the same or to other ranges. -/

namespace Ssz.Asm

/-- Whether an address lies among the n bytes from a base, counting modulo 2^64. -/
def Within (x base : BitVec 64) (n : Nat) : Prop :=
  (x - base).toNat < n

/-- Two byte ranges that share no address. -/
def Disjoint (a : BitVec 64) (n : Nat) (b : BitVec 64) (k : Nat) : Prop :=
  ∀ x, Within x a n → ¬Within x b k

theorem Disjoint.symm {a b : BitVec 64} {n k : Nat} (d : Disjoint a n b k) : Disjoint b k a n :=
  fun x inB inA => d x inA inB

/-- A byte at a small offset from a base lies within any range from that base reaching past it. -/
theorem within_offset {a : BitVec 64} {i n : Nat} (small : i < 2 ^ 64) :
    Within (a + BitVec.ofNat 64 i) a n ↔ i < n := by
  -- The offset from the base is i itself.
  simp only [Within, BitVec.add_comm a, BitVec.add_sub_cancel, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt small]

/-- A sub-range of a range lies within it. -/
theorem within_sub {x a : BitVec 64} {c n len : Nat} (inside : Within x (a + BitVec.ofNat 64 c) len)
    (fits : c + len ≤ n) (small : n < 2 ^ 64) : Within x a n := by
  simp only [Within] at inside ⊢
  have : x - a = (x - (a + BitVec.ofNat 64 c)) + BitVec.ofNat 64 c := by bv_omega
  rw [this, BitVec.toNat_add, BitVec.toNat_ofNat]
  have : c < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Two ranges at offsets of one base that do not overlap share no address. -/
theorem disjoint_offsets {a : BitVec 64} {c n c' n' : Nat} (apart : c + n ≤ c' ∨ c' + n' ≤ c)
    (small : c + n < 2 ^ 64 ∧ c' + n' < 2 ^ 64) :
    Disjoint (a + BitVec.ofNat 64 c) n (a + BitVec.ofNat 64 c') n' := by
  intro x first second
  simp only [Within] at first second
  -- Both offsets are measured from the shared base.
  have split : ∀ d, x - (a + BitVec.ofNat 64 d) = (x - a) - BitVec.ofNat 64 d := by
    intro d
    bv_omega
  rw [split] at first second
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat] at first second
  have := (x - a).isLt
  rcases Nat.lt_or_ge (x - a).toNat c with low | high <;>
    rcases Nat.lt_or_ge (x - a).toNat c' with low' | high' <;>
    · simp only [Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show c' < 2 ^ 64 by omega)] at first second
      omega

namespace Machine

theorem mem_store_of_not_within {m : Machine} {a x : BitVec 64} {n : Nat} {v : BitVec 64}
    (outside : ¬Within x a n) : (m.store a n v).mem x = m.mem x :=
  mem_store_outside (Nat.not_lt.mp outside)

/-- A load from bytes a store does not touch reads what was there before. -/
theorem load_store_of_disjoint {m : Machine} {a b : BitVec 64} {n k : Nat} {v : BitVec 64}
    (apart : Disjoint b k a n) (small : k < 2 ^ 64) : (m.store a n v).load b k = m.load b k := by
  apply load_congr
  intro i within
  exact mem_store_of_not_within (apart _ ((within_offset (by omega)).mpr within))

/-- Eight bytes stored and loaded back at one address give the stored value. -/
theorem load_store_self8 {m : Machine} {a v : BitVec 64} : (m.store a 8 v).load a 8 = v := by
  simp only [load, mem_store_inside (by decide : (0 : Nat) < 8) (by decide),
    mem_store_inside (by decide : (1 : Nat) < 8) (by decide),
    mem_store_inside (by decide : (2 : Nat) < 8) (by decide),
    mem_store_inside (by decide : (3 : Nat) < 8) (by decide),
    mem_store_inside (by decide : (4 : Nat) < 8) (by decide),
    mem_store_inside (by decide : (5 : Nat) < 8) (by decide),
    mem_store_inside (by decide : (6 : Nat) < 8) (by decide),
    mem_store_inside (by decide : (7 : Nat) < 8) (by decide)]
  bitwise

/-- Four bytes stored and loaded back at one address give the low word of the stored value. -/
theorem load_store_self4 {m : Machine} {a v : BitVec 64} :
    (m.store a 4 v).load a 4 = (v.setWidth 32).setWidth 64 := by
  simp only [load, mem_store_inside (by decide : (0 : Nat) < 4) (by decide),
    mem_store_inside (by decide : (1 : Nat) < 4) (by decide),
    mem_store_inside (by decide : (2 : Nat) < 4) (by decide),
    mem_store_inside (by decide : (3 : Nat) < 4) (by decide)]
  bitwise

end Machine

/-- A small non-negative immediate, sign-extended, is the number itself. -/
theorem signExtend_ofNat12 {c : Nat} (small : c < 2048) :
    (BitVec.ofNat 12 c).signExtend 64 = BitVec.ofNat 64 c := by
  -- Below 2^11 the sign bit is clear, so sign extension is zero extension.
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · simp only [BitVec.msb_eq_decide, BitVec.toNat_ofNat, decide_eq_false_iff_not]
    omega

end Ssz.Asm
