import Asm.Sha256.PairSpec

/-! The padding block's rounds, whose schedule words are folded into their constants. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Sha256

open Ssz.Sha256 (Spec.State Spec.step Spec.rounds Spec.messageWord)

theorem round_fused_spec {m : Machine} {a b d e f g h q p : Reg} {k word kw : BitVec 32}
    {s : Spec.State} (distinct : Distinct [a, b, d, e, f, g, h, q, p, t0, t1])
    (rebuilds : Rebuilds kw) (fold : kw = k + word)
    (ha : Holds m a s.a) (hb : Holds m b s.b) (hd : Holds m d s.d) (he : Holds m e s.e)
    (hf : Holds m f s.f) (hg : Holds m g s.g) (hh : Holds m h s.h)
    (hq : Holds m q (s.b ^^^ s.c)) :
    let m' := execBlock (roundFusedCodeWith a b d e f g h q p kw) m
    Holds m' h (Spec.step s k word).a ∧ Holds m' d (Spec.step s k word).e ∧
      Holds m' p (s.a ^^^ s.b) ∧ m'.mem = m.mem ∧
      ∀ x, x ≠ h → x ≠ d → x ≠ p → x ≠ q → x ≠ t0 → x ≠ t1 → m'.read x = m.read x := by
  intro m'
  split_distinct distinct
  simp only [m', roundFusedCodeWith, execBlock_append]
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
  -- The two immediates rebuild the constant with the schedule word already in it.
  all_goals try simp only [sext32_eq rebuilds]
  all_goals simp only [Holds] at ha hb hd he hf hg hh hq
  all_goals simp only [ha, hb, hd, he, hf, hg, hh, hq, BitVec.signExtend_xor]
  all_goals first
    | apply sext32_eq
    | skip
  all_goals simp only [Nat.reduceMod, setWidth_add32, setWidth_sext32, large1_rotations,
    large0_rotations, choose_three, majority_two, setWidth_signExtend32, Spec.step, fold,
    BitVec.add_assoc]

theorem fused_rebuilds : ∀ i, i < 64 → Rebuilds (fusedConstant i) := by
  -- Sixty-four folded constants, each checked by evaluation.
  unfold Rebuilds
  decide

theorem fusedConstant_eq {i : Nat} (bound : i < 64) :
    fusedConstant i = (Ssz.Sha256.roundConstants[i]'bound).toBitVec + Spec.messageWord padWords i := by
  rw [padSchedule_spec i bound]
  simp [fusedConstant, Nat.mod_eq_of_lt bound]

/-- The registers between two padding-block rounds, read against the specification. -/
structure FusedInv (init : Spec.State) (m0 : Machine) (i : Nat) (bound : i ≤ 64) (m : Machine) :
    Prop where
  /-- The first working word. -/
  a : Holds m (wordHome i 0) (Spec.rounds padWords init i bound).a
  /-- The second working word. -/
  b : Holds m (wordHome i 1) (Spec.rounds padWords init i bound).b
  /-- The third working word. -/
  c : Holds m (wordHome i 2) (Spec.rounds padWords init i bound).c
  /-- The fourth working word. -/
  d : Holds m (wordHome i 3) (Spec.rounds padWords init i bound).d
  /-- The fifth working word. -/
  e : Holds m (wordHome i 4) (Spec.rounds padWords init i bound).e
  /-- The sixth working word. -/
  f : Holds m (wordHome i 5) (Spec.rounds padWords init i bound).f
  /-- The seventh working word. -/
  g : Holds m (wordHome i 6) (Spec.rounds padWords init i bound).g
  /-- The eighth working word. -/
  h : Holds m (wordHome i 7) (Spec.rounds padWords init i bound).h
  /-- The majority carry. -/
  carry : Holds m (carry i)
    ((Spec.rounds padWords init i bound).b ^^^ (Spec.rounds padWords init i bound).c)
  /-- Memory, which no round touches. -/
  mem : m.mem = m0.mem
  /-- Every register but the homes, the carries, and the temporaries. -/
  frame : ∀ x, x ∉ stateRegs.toList → x ∉ carryRegs.toList → x ≠ t0 → x ≠ t1 → m.read x = m0.read x

theorem fused_distinct (i : Nat) :
    Distinct [wordHome i 0, wordHome i 1, wordHome i 3, wordHome i 4, wordHome i 5, wordHome i 6,
      wordHome i 7, carry i, carry (i + 1), t0, t1] := by
  -- A sublist of the distinct registers of an ordinary round.
  have full := round_distinct i
  unfold Distinct at full ⊢
  exact List.Pairwise.sublist (by simp) full

theorem fused_step {init : Spec.State} {m0 m : Machine} {i : Nat} (bound : i < 64)
    (inv : FusedInv init m0 i (by omega) m) :
    FusedInv init m0 (i + 1) bound (execBlock (roundFusedCode i) m) := by
  have round := round_fused_spec (m := m) (fused_distinct i) (fused_rebuilds i bound)
    (fusedConstant_eq bound) inv.a inv.b inv.d inv.e inv.f inv.g inv.h inv.carry
  simp only [roundFusedCode]
  obtain ⟨newA, newE, newCarry, mem, frame⟩ := round
  have next : Spec.rounds padWords init (i + 1) bound =
      Spec.step (Spec.rounds padWords init i (by omega))
        (Ssz.Sha256.roundConstants[i]'bound).toBitVec (Spec.messageWord padWords i) := rfl
  have kept (j : Nat) (small : j < 8) (notH : j ≠ 7) (notD : j ≠ 3) (word : BitVec 32)
      (held : Holds m (wordHome i j) word) :
      Holds (execBlock (roundFusedCodeWith (wordHome i 0) (wordHome i 1) (wordHome i 3)
        (wordHome i 4) (wordHome i 5) (wordHome i 6) (wordHome i 7) (carry i) (carry (i + 1))
        (fusedConstant i)) m) (wordHome i j) word := by
    obtain ⟨h7, h3, p, q, z0, z1⟩ := home_kept (i := i) small notH notD
    rw [Holds, frame _ h7 h3 p q z0 z1]
    exact held
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x notState notCarry x0 x1 => ?_⟩
  · rw [wordHome_succ_zero, next]
    exact newA
  · rw [wordHome_succ i 0 (by omega), next]
    exact kept 0 (by omega) (by omega) (by omega) _ inv.a
  · rw [wordHome_succ i 1 (by omega), next]
    exact kept 1 (by omega) (by omega) (by omega) _ inv.b
  · rw [wordHome_succ i 2 (by omega), next]
    exact kept 2 (by omega) (by omega) (by omega) _ inv.c
  · rw [wordHome_succ i 3 (by omega), next]
    exact newE
  · rw [wordHome_succ i 4 (by omega), next]
    exact kept 4 (by omega) (by omega) (by omega) _ inv.e
  · rw [wordHome_succ i 5 (by omega), next]
    exact kept 5 (by omega) (by omega) (by omega) _ inv.f
  · rw [wordHome_succ i 6 (by omega), next]
    exact kept 6 (by omega) (by omega) (by omega) _ inv.g
  · rw [next]
    exact newCarry
  · rw [mem, inv.mem]
  · -- A register that is no home and no carry is not among the round's outputs.
    have notHome (j : Nat) : x ≠ wordHome i j := by
      rintro rfl
      exact notState (by simp [wordHome, Vector.getElem_mem])
    have notCarryReg (c : Nat) : x ≠ carry c := by
      rintro rfl
      exact notCarry (by simp [carry, Vector.getElem_mem])
    rw [frame x (notHome 7) (notHome 3) (notCarryReg _) (notCarryReg _) x0 x1, inv.frame x notState notCarry x0 x1]

theorem fused_all {init : Spec.State} {m0 m : Machine} (start : FusedInv init m0 0 (by omega) m) :
    ∀ n (bound : n ≤ 64), FusedInv init m0 n bound (execBlock (fusedRoundsCode n) m)
  | 0, _ => start
  | n + 1, bound => by
    rw [fusedRoundsCode, execBlock_append]
    exact fused_step bound (fused_all start n (by omega))

end Ssz.Asm.Sha256
