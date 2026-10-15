import Asm.Machine
import Ssz.Proofs.Hash.Sha256Spec

/-!
The 32-bit word identities behind the SHA-256 kernel.

Each one is checked a bit at a time, so no decision procedure beyond the kernel is trusted.
-/

namespace Ssz.Asm

instance : Std.Commutative (α := Bool) (· != ·) := ⟨by decide⟩

set_option hygiene false in
/--
Close a bitvector equation by checking every bit position separately.

Each position reduces to an equation between exclusive ors of input bits.
Associativity and commutativity then close it.
-/
macro "bitwise" : tactic => `(tactic| (
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  -- One goal per bit position, each with a literal index.
  simp only [Nat.lt_succ_iff_lt_or_eq] at hi
  repeat' rcases hi with hi | rfl
  all_goals try (exfalso; omega)
  -- Literal indices let every shift and rotation resolve to a single input bit.
  all_goals simp [BitVec.getLsbD_rotateRight, BitVec.getLsbD_signExtend, BitVec.msb_eq_getLsbD_last]
  all_goals (try simp [BitVec.getElem_signExtend, BitVec.getElem_setWidth, BitVec.getElem_shiftLeft,
    BitVec.msb_eq_getLsbD_last, BitVec.getMsbD_eq_getLsbD])
  all_goals ac_rfl))

@[simp] theorem setWidth_signExtend32 (w : BitVec 32) : (w.signExtend 64).setWidth 32 = w := by
  -- Sign extension leaves the low 32 bits in place.
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getElem_signExtend, hi, show i < 64 by omega]

@[simp] theorem setWidth_sext32 (v : BitVec 64) : (sext32 v).setWidth 32 = v.setWidth 32 := by
  -- A word result is sign-extended from its own low 32 bits.
  simp [sext32]

theorem setWidth_add32 (x y : BitVec 64) : (x + y).setWidth 32 = x.setWidth 32 + y.setWidth 32 :=
  -- Addition modulo 2^64 agrees with addition modulo 2^32 on the low 32 bits.
  BitVec.setWidth_add x y (by decide)

/--
The shift chain behind three rotations of the low word of a register.

The source sits in the high half, so each right shift by r leaves:

```text
    bits 32..63:  x >>> r          (the bits that move down)
    bits  0..31:  x <<< (32 - r)   (the bits that wrap around)
```

Shifts distribute over exclusive or, so three shifts by first, second, and third reach all three distances.
-/
def chain3 (x : BitVec 64) (first second third : Nat) : BitVec 64 :=
  let doubled := x <<< 32
  ((((doubled >>> first) ^^^ doubled) >>> second) ^^^ doubled) >>> third

/-- Three rotations, with the moved-down bits folded onto the wrapped-around bits. -/
def rotations3 (x : BitVec 64) (first second third : Nat) : BitVec 64 :=
  (chain3 x first second third >>> 32) ^^^ chain3 x first second third

/-- The shift chain behind two rotations of the low word of a register. -/
def chain2 (x : BitVec 64) (first second : Nat) : BitVec 64 :=
  let doubled := x <<< 32
  ((doubled >>> first) ^^^ doubled) >>> second

/-- Two rotations and a logical shift, the shape of the schedule mixing functions. -/
def rotations2 (x : BitVec 64) (first second shift : Nat) : BitVec 64 :=
  -- The logical shift of the low word has no wrapped-around part, so it joins separately.
  ((chain2 x first second >>> 32) ^^^ chain2 x first second) ^^^
    ((x.setWidth 32 >>> shift).signExtend 64)

theorem large1_rotations (x : BitVec 64) :
    (rotations3 x 14 5 6).setWidth 32 = Sha256.Spec.large1 (x.setWidth 32) := by
  simp only [rotations3, chain3, Sha256.Spec.large1]
  bitwise

theorem large0_rotations (x : BitVec 64) :
    (rotations3 x 9 11 2).setWidth 32 = Sha256.Spec.large0 (x.setWidth 32) := by
  simp only [rotations3, chain3, Sha256.Spec.large0]
  bitwise

theorem small0_rotations (x : BitVec 64) :
    (rotations2 x 11 7 3).setWidth 32 = Sha256.Spec.small0 (x.setWidth 32) := by
  simp only [rotations2, chain2, Sha256.Spec.small0]
  bitwise

theorem small1_rotations (x : BitVec 64) :
    (rotations2 x 2 17 10).setWidth 32 = Sha256.Spec.small1 (x.setWidth 32) := by
  simp only [rotations2, chain2, Sha256.Spec.small1]
  bitwise

/-- Choice in three instructions: where e is set take f, elsewhere take g. -/
theorem choose_three (e f g : BitVec 64) :
    (((f ^^^ g) &&& e) ^^^ g).setWidth 32 =
      (e.setWidth 32 &&& f.setWidth 32) ^^^ ((~~~e.setWidth 32) &&& g.setWidth 32) := by
  -- Each bit is a three-input truth table.
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi,
    decide_true, Bool.true_and]
  cases e.getLsbD i <;> cases f.getLsbD i <;> cases g.getLsbD i <;> rfl

/--
Majority in two instructions, given the exclusive or of b and c from the round before.

Where a and b agree the majority is b, and elsewhere c breaks the tie.
-/
theorem majority_two (a b c : BitVec 64) :
    (((b ^^^ c) &&& (a ^^^ b)) ^^^ b).setWidth 32 =
      (a.setWidth 32 &&& b.setWidth 32) ^^^ (a.setWidth 32 &&& c.setWidth 32) ^^^
        (b.setWidth 32 &&& c.setWidth 32) := by
  -- Each bit is a three-input truth table.
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_xor, BitVec.getLsbD_and, hi, decide_true,
    Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

end Ssz.Asm
