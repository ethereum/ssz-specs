import Asm.Block
import Asm.Word
import Asm.Sha256.Code

/-! What one round and one schedule step of the kernel compute, read against FIPS 180-4. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Sha256

open Ssz.Sha256 (Spec.State Spec.step Spec.large0 Spec.large1 Spec.small0 Spec.small1)

/-- Registers that are pairwise distinct and never the zero register. -/
def Distinct (regs : List Reg) : Prop :=
  (0 :: regs).Pairwise (· ≠ ·)

/-- Close a register disequality from the hypotheses, in either orientation, or by evaluation. -/
macro "reg_ne" : tactic =>
  `(tactic| first | assumption | (apply Ne.symm; assumption))

/-- Split distinctness into one hypothesis per pair of registers. -/
macro "split_distinct " h:ident : tactic =>
  `(tactic| (
    simp only [Distinct, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, and_assoc] at $h:ident
    repeat' obtain ⟨_, $h:ident⟩ := $h:ident))

theorem execBlock_rotations3 {m : Machine} {dst tmp src : Reg} {first second third : Nat}
    (zd : 0 ≠ dst) (zt : 0 ≠ tmp) (dt : dst ≠ tmp) :
    execBlock (rotations3Code dst tmp src first second third) m =
      (m.write tmp (chain3 (m.read src) (first % 64) (second % 64) (third % 64))).write dst
        (rotations3 (m.read src) (first % 64) (second % 64) (third % 64)) := by
  -- Every intermediate value reads back from the register it was just written to.
  simp [rotations3Code, Instr.run, rotations3, chain3, Ne.symm zd, Ne.symm zt, dt, Ne.symm dt]

theorem execBlock_rotations2 {m : Machine} {dst tmp src : Reg} {first second shift : Nat}
    (zd : 0 ≠ dst) (zt : 0 ≠ tmp) (dt : dst ≠ tmp) (ds : dst ≠ src) (ts : tmp ≠ src) :
    execBlock (rotations2Code dst tmp src first second shift) m =
      (m.write tmp (((m.read src).setWidth 32 >>> (shift % 32)).signExtend 64)).write dst
        (rotations2 (m.read src) (first % 64) (second % 64) (shift % 32)) := by
  -- The logical shift reads the source, which neither temporary has touched.
  simp [rotations2Code, Instr.run, rotations2, chain2, Ne.symm zd, Ne.symm zt, Ne.symm ds,
    Ne.symm ts, dt, Ne.symm dt]

end Ssz.Asm.Sha256

namespace Ssz.Asm.Sha256

open Ssz.Sha256 (Spec.State Spec.step Spec.large0 Spec.large1 Spec.small0 Spec.small1)

/-- A register holding a 32-bit word in the sign-extended form every word instruction writes. -/
abbrev Holds (m : Machine) (r : Reg) (word : BitVec 32) : Prop :=
  m.read r = word.signExtend 64

/-- The two immediates of a round constant rebuild it exactly. -/
def Rebuilds (k : BitVec 32) : Prop :=
  (((upper k ++ (0 : BitVec 12)).signExtend 64) + (lower k).signExtend 64).setWidth 32 = k

/-- The sign-extended form of a 32-bit value is fixed by its low 32 bits. -/
theorem sext32_eq {v : BitVec 64} {word : BitVec 32} (low : v.setWidth 32 = word) :
    sext32 v = word.signExtend 64 := by
  simp [sext32, low]

theorem round_spec {m : Machine} {a b d e f g h w q p : Reg} {k word : BitVec 32}
    {s : Spec.State} (distinct : Distinct [a, b, d, e, f, g, h, w, q, p, t0, t1])
    (rebuilds : Rebuilds k)
    (ha : Holds m a s.a) (hb : Holds m b s.b) (hd : Holds m d s.d) (he : Holds m e s.e)
    (hf : Holds m f s.f) (hg : Holds m g s.g) (hh : Holds m h s.h) (hw : Holds m w word)
    (hq : Holds m q (s.b ^^^ s.c)) :
    let m' := execBlock (roundCodeWith a b d e f g h w q p k) m
    Holds m' h (Spec.step s k word).a ∧ Holds m' d (Spec.step s k word).e ∧
      Holds m' p (s.a ^^^ s.b) ∧ m'.mem = m.mem ∧
      ∀ x, x ≠ h → x ≠ d → x ≠ p → x ≠ q → x ≠ t0 → x ≠ t1 → m'.read x = m.read x := by
  intro m'
  split_distinct distinct
  simp only [m', roundCodeWith, execBlock_append]
  rw [execBlock_rotations3 (dst := t0) (tmp := t1) (by reg_ne) (by reg_ne) (by reg_ne)]
  simp (disch := reg_ne) only [execBlock_cons, execBlock_nil, List.cons_append, List.nil_append,
    Instr.run, Machine.read_write_self', Machine.read_write_ne', Machine.read_write_ne]
  rw [execBlock_rotations3 (dst := t0) (tmp := t1) (by reg_ne) (by reg_ne) (by reg_ne)]
  simp (disch := reg_ne) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self',
    Machine.read_write_ne', Machine.read_write_ne]
  refine ⟨?_, ?_, ?_, by simp, fun x xh xd xp xq x0 x1 => ?_⟩
  -- Reading back each output skips every later write to another register.
  all_goals simp (disch := reg_ne) only [Holds, Machine.read_write_self', Machine.read_write_ne',
    Machine.read_write_ne]
  -- The two immediates rebuild the round constant.
  all_goals try simp only [sext32_eq rebuilds]
  -- Every input is a sign-extended word, and b xor c splits into its two words.
  all_goals simp only [Holds] at ha hb hd he hf hg hh hw hq
  all_goals simp only [ha, hb, hd, he, hf, hg, hh, hw, hq, BitVec.signExtend_xor]
  -- Only the low 32 bits of each sum matter, and the mixing functions are the specified ones.
  all_goals first
    | apply sext32_eq
    | skip
  all_goals simp only [Nat.reduceMod, setWidth_add32, setWidth_sext32, large1_rotations, large0_rotations, choose_three,
    majority_two, setWidth_signExtend32, Spec.step, BitVec.add_assoc]
  done

theorem schedule_spec {m : Machine} {w w2 w15 w7 : Reg} {x16 x2 x15 x7 : BitVec 32}
    (distinct : Distinct [w, w2, w15, w7, t0, t1])
    (h16 : Holds m w x16) (h2 : Holds m w2 x2) (h15 : Holds m w15 x15) (h7 : Holds m w7 x7) :
    let m' := execBlock (scheduleCodeWith w w2 w15 w7) m
    Holds m' w (x16 + Spec.small0 x15 + x7 + Spec.small1 x2) ∧ m'.mem = m.mem ∧
      ∀ x, x ≠ w → x ≠ t0 → x ≠ t1 → m'.read x = m.read x := by
  intro m'
  split_distinct distinct
  simp only [m', scheduleCodeWith, execBlock_append]
  rw [execBlock_rotations2 (dst := t0) (tmp := t1) (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne)
    (by reg_ne)]
  simp (disch := reg_ne) only [execBlock_cons, execBlock_nil, List.cons_append, List.nil_append,
    Instr.run, Machine.read_write_self', Machine.read_write_ne', Machine.read_write_ne]
  rw [execBlock_rotations2 (dst := t0) (tmp := t1) (by reg_ne) (by reg_ne) (by reg_ne) (by reg_ne)
    (by reg_ne)]
  simp (disch := reg_ne) only [execBlock_cons, execBlock_nil, Instr.run, Machine.read_write_self',
    Machine.read_write_ne', Machine.read_write_ne]
  refine ⟨?_, by simp, fun x xw x0 x1 => ?_⟩
  -- Reading back the new word skips the temporaries written after it.
  all_goals simp (disch := reg_ne) only [Holds, Machine.read_write_self', Machine.read_write_ne',
    Machine.read_write_ne]
  simp only [Holds] at h16 h2 h15 h7
  simp only [h16, h2, h15, h7]
  -- Only the low 32 bits of the sum matter, and the mixing functions are the specified ones.
  apply sext32_eq
  simp only [Nat.reduceMod, setWidth_add32, setWidth_sext32, small0_rotations, small1_rotations,
    setWidth_signExtend32]
  ac_rfl

end Ssz.Asm.Sha256
