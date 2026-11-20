import SszNative.Kernel.Detect
import SszNative.Kernel.ShaNi
import SszNative.Kernel.ShaNiDual
import SszNative.Kernel.Avx512
import SszNative.Proofs.Kernel.Avx512x2.Pair
import SszNative.Proofs.Kernel.Avx2.Main
import SszNative.Proofs.Kernel.Baseline.Main
import SszNative.Kernel.Gather
import SszNative.Proofs.Asm.Run
import SszNative.Proofs.Asm.Spec
import SszNative.Proofs.Asm.Machine
import SszNative.Proofs.Ir.Leaf

/-!
The feature detection routine, run on the machine model: it returns the processor's kernel mask.

```text
    leaves 0, 1      highest leaf, leaf 1's ecx
    leaf 7           its ebx, skipped below leaf 7
    xgetbv           the saved state, skipped when unreadable
    combine          ands of single bits: SHA in rax, AVX in rdx, AVX2 then AVX-512 in rcx
```

The run has four paths, by the two skips.
Each reaches the combining block with the same three words, so one proof of that block serves all four.
Every bit the block cuts out is then the bit the feature checks read, which gives the mask.

Each bit of the mask also lets a family of kernels run, for every stride and field width.
-/

namespace EthLib.Consensus.Ssz.Native.Kernel.Detect

open EthLib.Consensus.Ssz.Native.Asm

/-- A word's bit at a position, as one or zero. -/
def bitAt (v : UInt64) (k : Nat) : UInt64 :=
  (v >>> (k % 64).toUInt64) &&& 1

/-- Bits of registers anded into an accumulator, one register and position at a time. -/
def andBits (g : Gpr → UInt64) : List (Gpr × Nat) → UInt64 → UInt64
  | [], a => a
  | p :: ps, a => andBits g ps (a &&& bitAt (g p.1) p.2)

/-- The bits of several registers anded into one accumulator. -/
def flags (acc : Gpr) (ps : List (Gpr × Nat)) : List Instr :=
  ps.flatMap fun p => flag acc p.1 p.2

/-- The anded bits read only the registers they name. -/
theorem andBits_congr (g h : Gpr → UInt64) (ps : List (Gpr × Nat)) (same : ∀ p ∈ ps, g p.1 = h p.1) (a : UInt64) :
    andBits g ps a = andBits h ps a := by
  induction ps generalizing a with
  | nil => rfl
  | cons p ps ih =>
    simp only [andBits]
    rw [same p (by simp), ih (fun q hq => same q (by simp [hq]))]

/-- One bit, anded into an accumulator, changes only the accumulator and the temporary. -/
theorem exec_flag (acc w : Gpr) (k : Nat) (t : State) (accTmp : acc ≠ tmp)
    (shift : k % 64 ≠ 0) (one1 : t.gpr one = 1) :
    (exec (flag acc w k) t).gpr acc = t.gpr acc &&& bitAt (t.gpr w) k ∧
    (∀ g, g ≠ acc → g ≠ tmp → (exec (flag acc w k) t).gpr g = t.gpr g) ∧
    (exec (flag acc w k) t).mem = t.mem ∧ (exec (flag acc w k) t).cpu = t.cpu := by
  refine ⟨?_, fun g ga gt => ?_, ?_, ?_⟩
  · simp [flag, exec, exec1, assign, aluResult, shift, accTmp, one1, bitAt]
  · simp [flag, exec, exec1, assign, aluResult, shift, ga, gt]
  · simp [flag, exec, exec1, aluResult, shift]
  · simp [flag, exec, exec1, aluResult, shift]

/-- Bits anded one after another into an accumulator, from registers the accumulation leaves alone. -/
theorem exec_flags (acc : Gpr) (ps : List (Gpr × Nat)) (t : State) (accTmp : acc ≠ tmp) (accOne : acc ≠ one)
    (one1 : t.gpr one = 1) (srcs : ∀ p ∈ ps, p.1 ≠ acc ∧ p.1 ≠ tmp ∧ p.2 % 64 ≠ 0) :
    (exec (flags acc ps) t).gpr acc = andBits t.gpr ps (t.gpr acc) ∧
    (∀ g, g ≠ acc → g ≠ tmp → (exec (flags acc ps) t).gpr g = t.gpr g) ∧
    (exec (flags acc ps) t).mem = t.mem ∧ (exec (flags acc ps) t).cpu = t.cpu := by
  induction ps generalizing t with
  | nil => exact ⟨rfl, fun _ _ _ => rfl, rfl, rfl⟩
  | cons p ps ih =>
    obtain ⟨-, -, pShift⟩ := srcs p (by simp)
    obtain ⟨fAcc, fKeep, fMem, fCpu⟩ := exec_flag acc p.1 p.2 t accTmp pShift one1
    -- The first bit, then the rest from the machine it leaves.
    have rest := ih (exec (flag acc p.1 p.2) t) (by rw [fKeep _ (Ne.symm accOne) (by decide), one1])
      (fun q hq => srcs q (by simp [hq]))
    simp only [flags, List.flatMap_cons, exec_append] at rest ⊢
    obtain ⟨rAcc, rKeep, rMem, rCpu⟩ := rest
    refine ⟨?_, fun g ga gt => by rw [rKeep g ga gt, fKeep g ga gt], by rw [rMem, fMem], by rw [rCpu, fCpu]⟩
    -- The later bits read registers the first one left alone.
    rw [rAcc, fAcc,
      andBits_congr _ t.gpr ps (fun q hq => fKeep _ (srcs q (by simp [hq])).1 (srcs q (by simp [hq])).2.1)]
    rfl

/-- The SHA bits: SSSE3, SSE4.1, and SHA. -/
def shaBits : List (Gpr × Nat) := [(ecx1, 9), (ecx1, 19), (ebx7, 29)]

/-- The AVX bits: AVX, a readable control register, and the saved SSE and AVX state. -/
def avxBits : List (Gpr × Nat) := [(ecx1, 28), (ecx1, 27), (xcr, 1), (xcr, 2)]

/-- The AVX2 bit beyond AVX. -/
def deepBits : List (Gpr × Nat) := [(ebx7, 5)]

/-- The AVX-512 bits beyond AVX: three parts, and the saved opmask and upper zmm state. -/
def wideBits : List (Gpr × Nat) := [(ebx7, 16), (ebx7, 30), (ebx7, 31), (xcr, 5), (xcr, 6), (xcr, 7)]

/-- The combining block is four accumulations, then the mask put together and rbx restored. -/
theorem combine_eq : combine = [.movReg .rax one] ++ flags .rax shaBits ++ [.movReg .rdx one] ++ flags .rdx avxBits ++
    [.movReg .rcx .rdx] ++ flags .rcx deepBits ++ [.shlImm .rcx 3, .alu .or .rax .rcx] ++
    [.movReg .rcx .rdx] ++ flags .rcx wideBits ++
    [.shlImm .rcx 1, .shlImm .rdx 2, .alu .or .rax .rcx, .alu .or .rax .rdx, .movReg .rbx saved] := rfl

/-- The mask the combining block computes from leaf 1's ecx, the control register's word, and leaf 7's ebx. -/
def maskOf (c x b : UInt64) : UInt64 :=
  let g := fun r => if r = ecx1 then c else if r = xcr then x else b
  let avx := andBits g avxBits 1
  andBits g shaBits 1 ||| andBits g deepBits avx <<< 3 ||| andBits g wideBits avx <<< 1 ||| avx <<< 2

/-- The combining block leaves the mask in rax and the saved word in rbx, and touches no memory. -/
theorem exec_combine (t : State) (one1 : t.gpr one = 1) :
    (exec combine t).gpr .rax = maskOf (t.gpr ecx1) (t.gpr xcr) (t.gpr ebx7) ∧
    (exec combine t).gpr .rbx = t.gpr saved ∧
    (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ tmp → g ≠ .rbx → (exec combine t).gpr g = t.gpr g) ∧
    (exec combine t).mem = t.mem ∧ (exec combine t).cpu = t.cpu := by
  rw [combine_eq]
  simp only [exec_append]
  -- The SHA bits into rax.
  generalize h1 : exec [.movReg .rax one] t = t1
  have g1 : t1.gpr = assign t.gpr .rax 1 := by subst h1; simp [exec, exec1, one1]
  have m1 : t1.mem = t.mem ∧ t1.cpu = t.cpu := by subst h1; simp [exec, exec1]
  obtain ⟨a2, k2, m2, c2⟩ := exec_flags .rax shaBits t1 (by decide) (by decide) (by simp [g1, assign, one1])
    (by decide)
  generalize exec (flags .rax shaBits) t1 = t2 at a2 k2 m2 c2
  -- The AVX bits into rdx.
  generalize h3 : exec [.movReg .rdx one] t2 = t3
  have g3 : t3.gpr = assign t2.gpr .rdx 1 := by
    subst h3; simp [exec, exec1, k2 one (by decide) (by decide), g1, assign, one1]
  have m3 : t3.mem = t2.mem ∧ t3.cpu = t2.cpu := by subst h3; simp [exec, exec1]
  obtain ⟨a4, k4, m4, c4⟩ := exec_flags .rdx avxBits t3 (by decide) (by decide)
    (by simp [g3, assign, k2 one (by decide) (by decide), g1, one1]) (by decide)
  generalize exec (flags .rdx avxBits) t3 = t4 at a4 k4 m4 c4
  -- The AVX2 bit into rcx, starting from the AVX ones, then moved into rax.
  generalize hA : exec [.movReg .rcx .rdx] t4 = tA
  have gA : tA.gpr = assign t4.gpr .rcx (t4.gpr .rdx) := by subst hA; simp [exec, exec1]
  have mA : tA.mem = t4.mem ∧ tA.cpu = t4.cpu := by subst hA; simp [exec, exec1]
  obtain ⟨aB, kB, mB, cB⟩ := exec_flags .rcx deepBits tA (by decide) (by decide)
    (by simp [gA, assign, k4 one (by decide) (by decide), g3, k2 one (by decide) (by decide), g1, one1]) (by decide)
  generalize exec (flags .rcx deepBits) tA = tB at aB kB mB cB
  generalize hC : exec [.shlImm .rcx 3, .alu .or .rax .rcx] tB = tC
  have gC : tC.gpr = assign (assign tB.gpr .rcx (tB.gpr .rcx <<< 3)) .rax (tB.gpr .rax ||| tB.gpr .rcx <<< 3) := by
    subst hC; simp [exec, exec1, assign, aluResult]
  have mC : tC.mem = tB.mem ∧ tC.cpu = tB.cpu := by subst hC; simp [exec, exec1, aluResult]
  -- The AVX-512 bits into rcx, starting from the AVX ones again.
  generalize h5 : exec [.movReg .rcx .rdx] tC = t5
  have g5 : t5.gpr = assign tC.gpr .rcx (tC.gpr .rdx) := by subst h5; simp [exec, exec1]
  have m5 : t5.mem = tC.mem ∧ t5.cpu = tC.cpu := by subst h5; simp [exec, exec1]
  obtain ⟨a6, k6, m6, c6⟩ := exec_flags .rcx wideBits t5 (by decide) (by decide)
    (by simp [g5, gC, assign, kB one (by decide) (by decide), gA, k4 one (by decide) (by decide), g3,
      k2 one (by decide) (by decide), g1, one1]) (by decide)
  generalize exec (flags .rcx wideBits) t5 = t6 at a6 k6 m6 c6
  -- Every register but the three accumulators and the temporary is as on entry.
  have keep1 : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ tmp → t1.gpr g = t.gpr g := fun g ga _ _ _ => by
    rw [g1, assign, ite_eq_right ga]
  have keep3 : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ tmp → t3.gpr g = t.gpr g := fun g ga gc gd gt => by
    rw [g3, assign, ite_eq_right gd, k2 g ga gt, keep1 g ga gc gd gt]
  have keepA : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ tmp → tA.gpr g = t.gpr g := fun g ga gc gd gt => by
    rw [gA, assign, ite_eq_right gc, k4 g gd gt, keep3 g ga gc gd gt]
  have keep5 : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ tmp → t5.gpr g = t.gpr g := fun g ga gc gd gt => by
    rw [g5, assign, ite_eq_right gc, gC, assign, ite_eq_right ga, assign, ite_eq_right gc, kB g gc gt, keepA g ga gc gd gt]
  have keep : ∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ tmp → t6.gpr g = t.gpr g := fun g ga gc gd gt => by
    rw [k6 g gc gt, keep5 g ga gc gd gt]
  -- Each accumulation reads only the three words, which no accumulation changes.
  have words : ∀ ps : List (Gpr × Nat), (∀ p ∈ ps, p.1 = ecx1 ∨ p.1 = xcr ∨ p.1 = ebx7) → ∀ (u : State),
      (∀ g, g ≠ .rax → g ≠ .rcx → g ≠ .rdx → g ≠ tmp → u.gpr g = t.gpr g) → ∀ a,
      andBits u.gpr ps a =
        andBits (fun r => if r = ecx1 then t.gpr ecx1 else if r = xcr then t.gpr xcr else t.gpr ebx7) ps a :=
    fun ps hps u hu a => andBits_congr _ _ ps (fun p hp => by
      rcases hps p hp with h | h | h <;> rw [h, hu _ (by decide) (by decide) (by decide) (by decide)] <;> simp) a
  have inWords : ∀ ps : List (Gpr × Nat), ps.all (fun p => p.1 = ecx1 ∨ p.1 = xcr ∨ p.1 = ebx7) = true →
      ∀ p ∈ ps, p.1 = ecx1 ∨ p.1 = xcr ∨ p.1 = ebx7 := fun ps h p hp => by
    simpa using List.all_eq_true.mp h p hp
  -- The AVX accumulator, followed back to where it was seeded.
  have avx4 : t4.gpr .rdx = andBits t3.gpr avxBits 1 := by
    rw [a4, g3]
    rfl
  have deepB : tB.gpr .rcx = andBits tA.gpr deepBits (andBits t3.gpr avxBits 1) := by
    rw [aB, gA, assign, ite_eq_left rfl, avx4]
  have shaB : tB.gpr .rax = andBits t1.gpr shaBits 1 := by
    rw [kB _ (by decide) (by decide), gA, assign, ite_eq_right (by decide), k4 _ (by decide) (by decide), g3, assign,
      ite_eq_right (by decide), a2, g1]
    rfl
  have rdxB : tB.gpr .rdx = andBits t3.gpr avxBits 1 := by
    rw [kB _ (by decide) (by decide), gA, assign, ite_eq_right (by decide), avx4]
  -- The four accumulators at the end.
  have sha : t6.gpr .rax = andBits t1.gpr shaBits 1 ||| andBits tA.gpr deepBits (andBits t3.gpr avxBits 1) <<< 3 := by
    rw [k6 _ (by decide) (by decide), g5, gC]
    simp [assign, shaB, deepB]
  have avx : t6.gpr .rdx = andBits t3.gpr avxBits 1 := by
    rw [k6 _ (by decide) (by decide), g5, gC]
    simp [assign, rdxB]
  have wide : t6.gpr .rcx = andBits t5.gpr wideBits (andBits t3.gpr avxBits 1) := by
    rw [a6]
    congr 1
    rw [g5, gC]
    simp [assign, rdxB]
  simp [exec, exec1, assign, aluResult]
  refine ⟨?_, ?_, fun g ga gc gd gt gb => ?_, by rw [m6, m5.1, mC.1, mB, mA.1, m4, m3.1, m2, m1.1],
    by rw [c6, m5.2, mC.2, cB, mA.2, c4, m3.2, c2, m1.2]⟩
  · rw [sha, avx, wide, words _ (inWords _ (by decide)) t1 keep1, words _ (inWords _ (by decide)) t3 keep3,
      words _ (inWords _ (by decide)) tA keepA, words _ (inWords _ (by decide)) t5 keep5]
    rfl
  · exact keep _ (by decide) (by decide) (by decide) (by decide)
  · simp [ga, gc, gd, gb]
    exact keep g ga gc gd gt

/-- One or zero, by a truth value. -/
def ofBool (p : Bool) : UInt64 :=
  if p then 1 else 0

/-- Whether a number's binary digit at a position is one. -/
def digitOf (n k : Nat) : Bool :=
  decide (n / 2 ^ k % 2 = 1)

/-- A register's bit, cut out by a shift and an and, is one exactly when its digit is. -/
theorem bitAt_eq (v : UInt64) (k : Nat) (hk : k < 64) : bitAt v k = ofBool (digitOf v.toNat k) := by
  apply UInt64.toNat_inj.mp
  have count : (k % 64).toUInt64.toNat % 64 = k := by simp; omega
  simp only [bitAt, UInt64.toNat_and, UInt64.toNat_shiftRight, count, Nat.shiftRight_eq_div_pow, ofBool, digitOf]
  have := Nat.mod_two_eq_zero_or_one (v.toNat / 2 ^ k)
  by_cases h : v.toNat / 2 ^ k % 2 = 1 <;> simp [h] <;> omega

/-- A cpuid word's bit, as the feature checks read it, is its digit. -/
theorem bit_eq (w : UInt32) (k : Nat) (hk : k < 32) : bit w k = digitOf w.toNat k := by
  have value : ((w >>> k.toUInt32) &&& 1).toNat = w.toNat / 2 ^ k % 2 := by
    simp [UInt32.toNat_and, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hk]
  rw [bit, digitOf, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt32.toNat_inj, value]
  rfl

/-- Whether the control register is readable is bit 27 of leaf 1's ecx. -/
theorem osxsave_eq (cpu : Cpu) : cpu.osxsave = digitOf (cpu.cpuid 1 0).2.2.1.toNat 27 :=
  bit_eq _ 27 (by decide)

/-- A mask test below bit 8 reads only the low eight bits. -/
theorem and_low (n m : Nat) (small : m < 256) : n &&& m = n % 256 &&& m := by
  rw [← Nat.mod_eq_of_lt (show n &&& m < 256 from Nat.lt_of_le_of_lt Nat.and_le_right small),
    show (256 : Nat) = 2 ^ 8 from rfl, Nat.and_mod_two_pow, Nat.mod_eq_of_lt (show m < 2 ^ 8 from small)]

/-- Bits 1 and 2 both set, as a mask test. -/
theorem and6 (v : UInt64) : (v &&& 6 == 6) = (digitOf v.toNat 1 && digitOf v.toNat 2) := by
  have table : ∀ r < 256, (r &&& 6 = 6 ↔ r / 2 % 2 = 1 ∧ r / 4 % 2 = 1) := by decide +kernel
  rw [Bool.eq_iff_iff, beq_iff_eq, Bool.and_eq_true, digitOf, digitOf, decide_eq_true_iff, decide_eq_true_iff,
    ← UInt64.toNat_inj, UInt64.toNat_and, and_low _ _ (by decide), show (6 : UInt64).toNat = 6 from rfl,
    table _ (Nat.mod_lt _ (by decide)), Nat.pow_one, show (2 : Nat) ^ 2 = 4 from rfl]
  omega

/-- Bits 5, 6, and 7 all set, as a mask test. -/
theorem andE0 (v : UInt64) : (v &&& 0xE0 == 0xE0) = (digitOf v.toNat 5 && digitOf v.toNat 6 && digitOf v.toNat 7) := by
  have table : ∀ r < 256, (r &&& 0xE0 = 0xE0 ↔ (r / 32 % 2 = 1 ∧ r / 64 % 2 = 1) ∧ r / 128 % 2 = 1) := by decide +kernel
  rw [Bool.eq_iff_iff, beq_iff_eq, Bool.and_eq_true, Bool.and_eq_true, digitOf, digitOf, digitOf, decide_eq_true_iff,
    decide_eq_true_iff, decide_eq_true_iff, ← UInt64.toNat_inj, UInt64.toNat_and, and_low _ _ (by decide),
    show (0xE0 : UInt64).toNat = 0xE0 from rfl, table _ (Nat.mod_lt _ (by decide)),
    show (2 : Nat) ^ 5 = 32 from rfl, show (2 : Nat) ^ 6 = 64 from rfl, show (2 : Nat) ^ 7 = 128 from rfl]
  omega

/-- The control register's word the routine holds: its low half when readable, and zero otherwise. -/
def xcrWord (cpu : Cpu) : UInt64 :=
  if cpu.osxsave then cpu.xcr0 &&& 0xFFFFFFFF else 0

/-- The held word's low digits are the control register's, when it is readable. -/
theorem digitOf_xcrWord (cpu : Cpu) (k : Nat) (hk : k < 32) :
    digitOf (xcrWord cpu).toNat k = (cpu.osxsave && digitOf cpu.xcr0.toNat k) := by
  unfold xcrWord
  cases cpu.osxsave
  · simp [digitOf]
  · simp only [ite_true, Bool.true_and, digitOf, UInt64.toNat_and,
      show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    -- Cutting at bit 32 keeps every digit below it.
    rw [← Nat.testBit_eq_decide_div_mod_eq, ← Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_mod_two_pow]
    simp [hk]

/-- Two bits anded are the and of their truth values. -/
theorem ofBool_and (p q : Bool) : ofBool p &&& ofBool q = ofBool (p && q) := by
  cases p <;> cases q <;> rfl

/-- One anded with a bit is the bit. -/
theorem one_and_ofBool (q : Bool) : (1 : UInt64) &&& ofBool q = ofBool q := by
  cases q <;> rfl

/-- The mask the combining block computes is the processor's kernel mask. -/
theorem maskOf_eq (cpu : Cpu) :
    maskOf (cpu.cpuid 1 0).2.2.1.toUInt64 (xcrWord cpu) cpu.leaf7.toUInt64 = cpu.featureMask := by
  simp only [maskOf, andBits, shaBits, avxBits, deepBits, wideBits]
  simp [bitAt_eq, ofBool_and, one_and_ofBool, digitOf_xcrWord]
  simp only [Cpu.featureMask, Cpu.has, Cpu.ymmState, Cpu.zmmState, bit_eq _ _ (show 5 < 32 by decide), bit_eq _ _ (show 9 < 32 by decide),
    bit_eq _ _ (show 19 < 32 by decide), bit_eq _ _ (show 28 < 32 by decide), bit_eq _ _ (show 29 < 32 by decide),
    bit_eq _ _ (show 16 < 32 by decide), bit_eq _ _ (show 30 < 32 by decide), bit_eq _ _ (show 31 < 32 by decide),
    and6, andE0, osxsave_eq]
  -- What is left holds for every value of the fourteen bits.
  generalize digitOf (cpu.cpuid 1 0).2.2.1.toNat 9 = c9
  generalize digitOf (cpu.cpuid 1 0).2.2.1.toNat 19 = c19
  generalize digitOf (cpu.cpuid 1 0).2.2.1.toNat 27 = c27
  generalize digitOf (cpu.cpuid 1 0).2.2.1.toNat 28 = c28
  generalize digitOf cpu.leaf7.toNat 5 = b5
  generalize digitOf cpu.leaf7.toNat 16 = b16
  generalize digitOf cpu.leaf7.toNat 29 = b29
  generalize digitOf cpu.leaf7.toNat 30 = b30
  generalize digitOf cpu.leaf7.toNat 31 = b31
  generalize digitOf cpu.xcr0.toNat 1 = x1
  generalize digitOf cpu.xcr0.toNat 2 = x2
  generalize digitOf cpu.xcr0.toNat 5 = x5
  generalize digitOf cpu.xcr0.toNat 6 = x6
  generalize digitOf cpu.xcr0.toNat 7 = x7
  revert c9 c19 c27 c28 b5 b16 b29 b30 b31 x1 x2 x5 x6 x7
  decide +kernel

/-- The routine is its leaves, the leaf 7 branch, the control register read behind its branch, and the mask. -/
theorem layout : Kernel.detect.toList = leaves ++ [.jcc .b 16] ++ leaf7 ++ readable ++
    [.jz 25, .zeroReg .rcx, .xgetbv, .movReg xcr .rax] ++ combine ++ [.ret] := rfl

/-- A register the caller keeps is none the routine writes, rbx aside. -/
theorem kept_ne (g : Gpr) (hg : g ∈ calleeSaved) : g ≠ .rax ∧ g ≠ .rcx ∧ g ≠ .rdx ∧ g ≠ .rsi ∧ g ≠ .rdi ∧
    g ≠ .r8 ∧ g ≠ .r9 ∧ g ≠ .r10 ∧ g ≠ .r11 := by
  revert g; decide

/-- A highest leaf compares below 7 as a 64-bit register exactly when it is below 7. -/
theorem toUInt64_lt7 (m : UInt32) : (m.toUInt64 < 7) = (m < 7) := by
  simp [UInt64.lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt]

/-- One step of a run is a step. -/
theorem run_one (program : Array Instr) (t : State) : run program 1 t = step program t := rfl

section

variable (s : State)

/-- The machine at the join after leaf 7: the saved rbx, leaf 1's ecx, and leaf 7's ebx in place. -/
def At16 (t : State) : Prop :=
  t.pc = 16 ∧ t.status = .running ∧ t.cpu = s.cpu ∧ t.mem = s.mem ∧ t.gpr saved = s.gpr .rbx ∧
  t.gpr ecx1 = (s.cpu.cpuid 1 0).2.2.1.toUInt64 ∧ t.gpr ebx7 = s.cpu.leaf7.toUInt64 ∧
  ∀ g ∈ calleeSaved, g ≠ .rbx → t.gpr g = s.gpr g

/-- The machine at the join after the control register read: the three words and the constant one in place. -/
def At25 (t : State) : Prop :=
  t.pc = 25 ∧ t.status = .running ∧ t.cpu = s.cpu ∧ t.mem = s.mem ∧ t.gpr saved = s.gpr .rbx ∧
  t.gpr ecx1 = (s.cpu.cpuid 1 0).2.2.1.toUInt64 ∧ t.gpr ebx7 = s.cpu.leaf7.toUInt64 ∧
  t.gpr xcr = xcrWord s.cpu ∧ t.gpr one = 1 ∧
  ∀ g ∈ calleeSaved, g ≠ .rbx → t.gpr g = s.gpr g

/-- From the entry, the routine reaches the join after leaf 7. -/
theorem to16 (start : s.pc = 0) (running : s.status = .running) : ∃ n, At16 s (run Kernel.detect n s) := by
  have block := run_block Kernel.detect [] leaves _ (by rw [layout]; rfl) (by decide) s start running
  have fetch : Kernel.detect[11]? = some (.jcc .b 16) := rfl
  by_cases low : (s.cpu.cpuid 0 0).1 < 7
  · -- No leaf 7: the branch skips it, and its word stays zero.
    refine ⟨11 + 1, ?_⟩
    rw [run_add, show 11 = leaves.length from rfl, block]
    simp only [run]
    simp [step, fetch, leaves, exec, exec1, assign, signExtend32, toUInt64_lt7, low, running, At16, Cpu.leaf7,
      Cpu.maxLeaf, Cond.holds]
    intro g hg hb
    simp [kept_ne g hg, hb]
  · -- Leaf 7 exists: the branch falls through to it.
    have next : step Kernel.detect { exec leaves s with pc := ([] : List Instr).length + leaves.length } =
        { exec leaves s with pc := 12 } := by
      simp [step, fetch, leaves, exec, exec1, assign, signExtend32, toUInt64_lt7, low, running, Cond.holds]
    have block7 := run_block Kernel.detect (leaves ++ [.jcc .b 16]) leaf7
      (readable ++ [.jz 25, .zeroReg .rcx, .xgetbv, .movReg xcr .rax] ++ combine ++ [.ret]) (by rw [layout]; simp)
      (by decide) { exec leaves s with pc := 12 } rfl (by simp [running])
    refine ⟨11 + 1 + 4, ?_⟩
    rw [run_add, run_add, show 11 = leaves.length from rfl, block, run_one, next, show 4 = leaf7.length from rfl,
      block7]
    simp [leaves, leaf7, exec, exec1, assign, running, At16, Cpu.leaf7, Cpu.maxLeaf, low]
    intro g hg hb
    simp [kept_ne g hg, hb]

/-- The readable bit, cut out by a shift and an and, is zero exactly when the control register is unreadable. -/
theorem readable_zero (cpu : Cpu) :
    ((cpu.cpuid 1 0).2.2.1.toUInt64 >>> 27 &&& 1 == 0) = !cpu.osxsave := by
  have := bitAt_eq (cpu.cpuid 1 0).2.2.1.toUInt64 27 (by decide)
  simp only [bitAt] at this
  rw [show ((27 % 64 : Nat).toUInt64) = 27 from rfl] at this
  rw [this, osxsave_eq, UInt32.toNat_toUInt64]
  cases digitOf (cpu.cpuid 1 0).2.2.1.toNat 27 <;> rfl

/-- From the join after leaf 7, the routine reaches the join after the control register read. -/
theorem to25 (t : State) (at16 : At16 s t) : ∃ n, At25 s (run Kernel.detect n t) := by
  obtain ⟨pc, running, cpu, mem, rbx, ecx, ebx, kept⟩ := at16
  have block := run_block Kernel.detect (leaves ++ [.jcc .b 16] ++ leaf7) readable
    ([.jz 25, .zeroReg .rcx, .xgetbv, .movReg xcr .rax] ++ combine ++ [.ret]) (by rw [layout]; simp) (by decide)
    t (by rw [pc]; rfl) running
  have fetch : Kernel.detect[21]? = some (.jz 25) := rfl
  -- The readable bit decides the branch, and the block sets the constant and clears the word.
  have zf : (exec readable t).zf = !s.cpu.osxsave := by
    simp [readable, exec, exec1, assign, aluResult, ecx, readable_zero]
  have rOne : (exec readable t).gpr one = 1 := by simp [readable, exec, exec1, assign]
  have rXcr : (exec readable t).gpr xcr = 0 := by simp [readable, exec, exec1, assign]
  have rKeep : ∀ g, g ≠ .rax → g ≠ one → g ≠ xcr → (exec readable t).gpr g = t.gpr g := fun g ga go gx => by
    simp [readable, exec, exec1, assign, ga, go, gx]
  have rMem : (exec readable t).mem = t.mem ∧ (exec readable t).cpu = t.cpu := by simp [readable, exec, exec1]
  rw [show (leaves ++ [Instr.jcc .b 16] ++ leaf7).length + readable.length = 21 from rfl] at block
  have rRun : (exec readable t).status = .running := by rw [exec_status]; exact running
  rw [← show 5 = readable.length from rfl] at block
  generalize exec readable t = r at zf rOne rXcr rKeep rMem block rRun
  by_cases ox : s.cpu.osxsave
  · -- Readable: the branch falls through to the read, which keeps the register's low half.
    have f22 : Kernel.detect[22]? = some (.zeroReg .rcx) := rfl
    have f23 : Kernel.detect[23]? = some .xgetbv := rfl
    have f24 : Kernel.detect[24]? = some (.movReg xcr .rax) := rfl
    refine ⟨5 + 4, ?_⟩
    rw [run_add, block]
    simp only [run]
    simp [step, fetch, f22, f23, f24, zf, ox, rRun, exec1, assign, At25, rMem.1, rMem.2, cpu, mem, rOne]
    refine ⟨by rw [rKeep _ (by decide) (by decide) (by decide), rbx],
      by rw [rKeep _ (by decide) (by decide) (by decide), ecx],
      by rw [rKeep _ (by decide) (by decide) (by decide), ebx], by simp [xcrWord, ox], fun g hg hb => ?_⟩
    have ne := kept_ne g hg
    simp [ne]
    rw [rKeep g ne.1 ne.2.2.2.1 ne.2.2.2.2.2.2.2.1, kept g hg hb]
  · -- Unreadable: the branch skips the read, and the word stays zero.
    refine ⟨5 + 1, ?_⟩
    rw [run_add, block, run_one]
    simp [step, fetch, zf, ox, rRun, At25, rMem.1, rMem.2, cpu, mem, rOne, rXcr, xcrWord]
    refine ⟨by rw [rKeep _ (by decide) (by decide) (by decide), rbx],
      by rw [rKeep _ (by decide) (by decide) (by decide), ecx],
      by rw [rKeep _ (by decide) (by decide) (by decide), ebx], fun g hg hb => ?_⟩
    have ne := kept_ne g hg
    rw [rKeep g ne.1 ne.2.2.2.1 ne.2.2.2.2.2.2.2.1, kept g hg hb]

/-- From the join after the read, the routine combines the words into the mask and returns. -/
theorem finish (t : State) (at25 : At25 s t) :
    let f := run Kernel.detect (combine.length + 1) t
    f.status = .returned ∧ f.gpr .rax = s.cpu.featureMask ∧ (∀ g ∈ calleeSaved, f.gpr g = s.gpr g) ∧
      f.mem = s.mem ∧ f.cpu = s.cpu := by
  obtain ⟨pc, running, cpu, mem, rbx, ecx, ebx, word, one1, kept⟩ := at25
  have block := run_block Kernel.detect
    (leaves ++ [.jcc .b 16] ++ leaf7 ++ readable ++ [.jz 25, .zeroReg .rcx, .xgetbv, .movReg xcr .rax]) combine [.ret]
    (by rw [layout]) (by decide) t (by rw [pc]; rfl) running
  obtain ⟨cRax, cRbx, cKeep, cMem, cCpu⟩ := exec_combine t one1
  have fetch : Kernel.detect[92]? = some .ret := rfl
  rw [show (leaves ++ [Instr.jcc .b 16] ++ leaf7 ++ readable ++
    [Instr.jz 25, .zeroReg .rcx, .xgetbv, .movReg xcr .rax]).length + combine.length = 92 from rfl] at block
  rw [run_add, block, run_one]
  simp [step, running, fetch]
  refine ⟨by rw [cRax, ecx, word, ebx, maskOf_eq], fun g hg => ?_, by rw [cMem, mem], by rw [cCpu, cpu]⟩
  by_cases hb : g = .rbx
  · rw [hb, cRbx, rbx]
  · have ne := kept_ne g hg
    rw [cKeep g ne.1 ne.2.1 ne.2.2.1 ne.2.2.2.2.1 hb, kept g hg hb]

end

end EthLib.Consensus.Ssz.Native.Kernel.Detect

namespace EthLib.Consensus.Ssz.Native.Kernel

open EthLib.Consensus.Ssz.Native.Asm Kernel.Detect

/--
The routine returns the processor's kernel mask in rax.

It hands back every register the caller keeps, the stack pointer among them, and changes no memory.
-/
theorem detect_correct (s : State) (start : s.pc = 0) (running : s.status = .running) :
    ∃ steps, let f := run detect steps s
      f.status = .returned ∧ f.gpr .rax = s.cpu.featureMask ∧ (∀ g ∈ calleeSaved, f.gpr g = s.gpr g) ∧
      f.mem = s.mem ∧ f.cpu = s.cpu := by
  -- Leaves 0 and 1 and maybe 7, then the control register maybe, then the mask.
  obtain ⟨n1, at16⟩ := to16 s start running
  obtain ⟨n2, at25⟩ := to25 s _ at16
  have done := finish s _ at25
  generalize combine.length + 1 = n3 at done
  refine ⟨n1 + n2 + n3, ?_⟩
  rw [run_add, run_add]
  exact done

/-- A processor runs a routine whose every instruction needs only features from a list it has. -/
theorem runs_of_features (cpu : Cpu) (program : Array Instr) (allowed : List Feature)
    (needs : program.toList.all (fun i => i.features.all (· ∈ allowed)) = true) (has : ∀ f ∈ allowed, cpu.has f) :
    cpu.runs program := by
  simp only [Cpu.runs, List.all_eq_true]
  intro i hi f hf
  have := List.all_eq_true.mp (List.all_eq_true.mp needs i hi) f hf
  exact has f (by simpa using this)

/-- Every processor runs the routine: it needs only the 64-bit baseline. -/
theorem detect_runs (cpu : Cpu) : cpu.runs detect :=
  runs_of_features cpu detect [] (by decide +kernel) (by simp)

/-- The routine calls no other routine. -/
theorem detect_leaf : Leaf detect := by
  intro i hi name h
  subst h
  have none : detect.toList.all (fun i => match i with | .call _ => false | _ => true) = true := by decide +kernel
  simpa using List.all_eq_true.mp none _ hi

/-- What the routine means to a caller: no arguments, the processor's kernel mask, and memory untouched. -/
def detectExtern : Ir.Extern :=
  ⟨fun w _ args mem => if args = [] then some (w.cpu.featureMask, mem) else none⟩

/-- The routine keeps the call contract of its meaning, on every processor. -/
theorem detect_leafOk (w : Ir.World) : Ir.LeafOk w detect detectExtern := by
  intro s sp args ir ir' res start running cpu _ _ _ _ _ _ heap spec
  -- The meaning answers only a call without arguments, with the mask and memory as it was.
  have answer : res = w.cpu.featureMask ∧ ir' = ir := by
    simp only [detectExtern] at spec
    split at spec
    · cases spec; exact ⟨rfl, rfl⟩
    · cases spec
  obtain ⟨n, ret, rax, kept, mem, cpuN⟩ := detect_correct s start running
  refine ⟨detect_runs w.cpu, n, ret, by rw [rax, cpu, answer.1], kept .rsp (by decide),
    fun g hg => kept g ?_, fun a ha => by rw [mem, heap a ha, answer.2], fun a _ _ => by rw [mem], cpuN⟩
  revert g; decide

/-- The features the SHA kernels need. -/
def narrowFeatures : List Feature := [.sha, .ssse3, .sse41]

/-- The features the AVX-512 kernels need. -/
def wideFeatures : List Feature := [.avx512f, .avx512bw, .avx512vl, .avx]

/-- Whether every instruction of a routine needs only features from a list. -/
def needsOnly (allowed : List Feature) (program : Array Instr) : Bool :=
  program.toList.all fun i => i.features.all (· ∈ allowed)

/-- The mask's bits, each as the condition it stands for. -/
theorem featureMask_bits (cpu : Cpu) :
    (cpu.featureMask &&& 1 ≠ 0 → (cpu.has .sha && cpu.has .ssse3 && cpu.has .sse41) = true) ∧
    (cpu.featureMask &&& 2 ≠ 0 → (cpu.has .avx512f && cpu.has .avx512bw && cpu.has .avx512vl && cpu.has .avx) = true) ∧
    (cpu.featureMask &&& 4 ≠ 0 → cpu.has .avx = true) ∧
    (cpu.featureMask &&& 8 ≠ 0 → (cpu.has .avx2 && cpu.has .avx) = true) := by
  -- Four truth values decide the mask.
  unfold Cpu.featureMask
  generalize (cpu.has .avx512f && cpu.has .avx512bw && cpu.has .avx512vl && cpu.has .avx) = q
  generalize (cpu.has .avx2 && cpu.has .avx) = v
  generalize cpu.has .avx = r
  generalize (cpu.has .sha && cpu.has .ssse3 && cpu.has .sse41) = p
  cases p <;> cases q <;> cases r <;> cases v <;> decide

set_option maxRecDepth 100000 in
/-- The SHA kernel for every pair of strides needs only the SHA features. -/
theorem shaNi_needs (ls rs : Nat) : needsOnly narrowFeatures (ShaNi.program ls rs) = true := rfl

set_option maxRecDepth 100000 in
/-- The interleaved SHA kernel for every pair of strides needs only the SHA features. -/
theorem shaNiDual_needs (ls rs : Nat) : needsOnly narrowFeatures (ShaNiDual.program ls rs) = true := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The AVX-512 kernel for every pair of strides needs only the AVX-512 features. -/
theorem avx512_needs (ls rs : Nat) : needsOnly wideFeatures (Avx512.program ls rs) = true := rfl

/-- A routine's instructions, as a list, need only features from a list. -/
def listNeeds (allowed : List Feature) (code : List Instr) : Bool :=
  code.all fun i => i.features.all (· ∈ allowed)

/-- Two lists of instructions joined need what each needs. -/
theorem listNeeds_append (allowed : List Feature) (a b : List Instr) :
    listNeeds allowed (a ++ b) = (listNeeds allowed a && listNeeds allowed b) := by
  simp [listNeeds, List.all_append]

set_option maxRecDepth 100000 in
/-- The thirty-two-lane kernel for every pair of strides needs only the AVX-512 features. -/
theorem avx512x2_needs (ls rs : Nat) : needsOnly wideFeatures (Avx512x2.program ls rs) = true := by
  -- The pieces without strides, checked by evaluation.
  have closed : listNeeds wideFeatures (Avx512x2.firstBlock true) && listNeeds wideFeatures (Avx512x2.firstBlock false) &&
      listNeeds wideFeatures Avx512x2.middleCode && listNeeds wideFeatures Avx512x2.paddingBlock &&
      listNeeds wideFeatures Avx512x2.outputCode && listNeeds wideFeatures Avx512x2.closingCode = true := by
    decide +kernel
  -- The loads read the strides only in their addresses, which no feature depends on.
  have setup : listNeeds wideFeatures (Avx512x2.setupCode ls rs) = true := rfl
  simp only [Bool.and_eq_true] at closed
  -- The rest are integer instructions and branches, which need nothing.
  show listNeeds wideFeatures (Avx512x2.program ls rs).toList = true
  simp only [Avx512x2.program_toList, Avx512x2.body_eq, Avx512x2.opening, Avx512x2.tailCode, listNeeds_append,
    setup, closed, Bool.and_true]
  rfl

set_option maxRecDepth 100000 in
/-- The eight-lane kernel for every pair of strides needs only AVX2 and AVX. -/
theorem avx2_needs (ls rs : Nat) : needsOnly [.avx2, .avx] (Avx2.program ls rs) = true := by
  -- The pieces without strides, checked by evaluation.
  have closed : listNeeds [.avx2, .avx] (Avx2.firstBlock true) && listNeeds [.avx2, .avx] (Avx2.firstBlock false) &&
      listNeeds [.avx2, .avx] Avx2.middleCode && listNeeds [.avx2, .avx] Avx2.paddingBlock &&
      listNeeds [.avx2, .avx] Avx2.outputCode = true := by
    decide +kernel
  -- The loads read the strides only in their addresses, which no feature depends on.
  have setup : listNeeds [.avx2, .avx] (Avx2.setupCode ls rs) = true := rfl
  simp only [Bool.and_eq_true] at closed
  -- The rest are integer instructions and branches, which need nothing.
  show listNeeds [.avx2, .avx] (Avx2.program ls rs).toList = true
  simp only [Avx2.program_toList, Avx2.tailCode, listNeeds_append, setup, closed, Bool.and_true]
  rfl

set_option maxRecDepth 100000 in
/-- The SSE2 kernel for every pair of strides needs only the 64-bit baseline. -/
theorem baseline_needs (ls rs : Nat) : needsOnly [] (Baseline.program ls rs) = true := by
  -- The pieces without strides, checked by evaluation.
  have closed : listNeeds [] (Baseline.firstBlock true) && listNeeds [] (Baseline.firstBlock false) &&
      listNeeds [] Baseline.middleCode && listNeeds [] Baseline.paddingBlock &&
      listNeeds [] Baseline.outputCode = true := by
    decide +kernel
  -- The loads read the strides only in their addresses, which no feature depends on.
  have setup : listNeeds [] (Baseline.setupCode ls rs) = true := rfl
  simp only [Bool.and_eq_true] at closed
  -- The rest are integer instructions and branches, which need nothing.
  show listNeeds [] (Baseline.program ls rs).toList = true
  simp only [Baseline.program_toList, Baseline.tailCode, listNeeds_append, setup, closed, Bool.and_true]
  rfl

/-- Every processor runs the SSE2 kernel, for every pair of strides. -/
theorem runs_baseline (cpu : Cpu) (ls rs : Nat) : cpu.runs (Baseline.program ls rs) :=
  runs_of_features cpu _ [] (baseline_needs ls rs) (by simp)

/-- The gather for every field width needs only AVX. -/
theorem gatherNode_needs (width : Nat) : needsOnly [.avx] (gatherNode width) = true := by
  unfold gatherNode loadField
  split <;> rfl

/-- When the mask's first bit is set, the processor runs the SHA kernels, for every pair of strides. -/
theorem runs_of_mask_shani (cpu : Cpu) (ls rs : Nat) (bit : cpu.featureMask &&& 1 ≠ 0) :
    cpu.runs (ShaNi.program ls rs) ∧ cpu.runs (ShaNiDual.program ls rs) := by
  have has : ∀ f ∈ narrowFeatures, cpu.has f := by
    have := (featureMask_bits cpu).1 bit
    simp only [Bool.and_eq_true] at this
    simp [narrowFeatures, this]
  exact ⟨runs_of_features _ _ _ (shaNi_needs ls rs) has, runs_of_features _ _ _ (shaNiDual_needs ls rs) has⟩

/-- When the mask's second bit is set, the processor runs both AVX-512 kernels, for every pair of strides. -/
theorem runs_of_mask_avx512 (cpu : Cpu) (ls rs : Nat) (bit : cpu.featureMask &&& 2 ≠ 0) :
    cpu.runs (Avx512.program ls rs) ∧ cpu.runs (Avx512x2.program ls rs) := by
  have has : ∀ f ∈ wideFeatures, cpu.has f := by
    have := (featureMask_bits cpu).2.1 bit
    simp only [Bool.and_eq_true] at this
    simp [wideFeatures, this]
  exact ⟨runs_of_features _ _ _ (avx512_needs ls rs) has, runs_of_features _ _ _ (avx512x2_needs ls rs) has⟩

/-- When the mask's fourth bit is set, the processor runs the AVX2 kernel, for every pair of strides. -/
theorem runs_of_mask_avx2 (cpu : Cpu) (ls rs : Nat) (bit : cpu.featureMask &&& 8 ≠ 0) :
    cpu.runs (Avx2.program ls rs) := by
  have has : ∀ f ∈ [Feature.avx2, .avx], cpu.has f := by
    have := (featureMask_bits cpu).2.2.2 bit
    simp only [Bool.and_eq_true] at this
    simp [this]
  exact runs_of_features _ _ _ (avx2_needs ls rs) has

/-- When the mask's third bit is set, the processor runs the AVX gathers, for every field width. -/
theorem runs_of_mask_avx (cpu : Cpu) (width : Nat) (bit : cpu.featureMask &&& 4 ≠ 0) :
    cpu.runs (gatherNode width) ∧ cpu.runs gatherKey := by
  have has : ∀ f ∈ [Feature.avx], cpu.has f := by simp [(featureMask_bits cpu).2.2.1 bit]
  exact ⟨runs_of_features _ _ _ (gatherNode_needs width) has, runs_of_features _ _ _ (by decide +kernel) has⟩

/-- Every processor runs the general gather: it needs only the 64-bit baseline. -/
theorem runs_gather (cpu : Cpu) : cpu.runs gather :=
  runs_of_features cpu gather [] (by decide +kernel) (by simp)

end EthLib.Consensus.Ssz.Native.Kernel
