import Asm.Frame
import Asm.Sha256.Phases

/-! The feed-forward that writes the new chaining state back over the old one. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm

theorem Machine.word32_store_self {m : Machine} {a v : BitVec 64} :
    (m.store a 4 v).word32 a = v.setWidth 32 := by
  -- The low four bytes come back, and nothing above them.
  simp only [word32, load_store_self4]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

@[simp] theorem Machine.word32_write {m : Machine} {r : Reg} {v a : BitVec 64} :
    (m.write r v).word32 a = m.word32 a := by
  simp [word32]

theorem Machine.word32_store_other {m : Machine} {a b v : BitVec 64} (apart : Disjoint b 4 a 4) :
    (m.store a 4 v).word32 b = m.word32 b := by
  simp only [word32, load_store_of_disjoint apart (by decide)]

/-- A smaller range from the same base lies inside a larger one. -/
theorem within_mono {x a : BitVec 64} {n k : Nat} (inside : Within x a n) (le : n ≤ k) :
    Within x a k := by
  simp only [Within] at *
  omega

/-- Word j of a chaining state, by index. -/
def stateWord (s : Ssz.Sha256.Spec.State) (j : Nat) : BitVec 32 :=
  (s.words[j % 8]'(Nat.mod_lt _ (by decide)))

end Ssz.Asm

namespace Ssz.Asm.Sha256

theorem wordHome_zero (j : Nat) (small : j < 8) :
    wordHome 0 j = stateRegs[j % 8]'(Nat.mod_lt _ (by decide)) := by
  simp [wordHome, Nat.mod_eq_of_lt small]

/-- The first n words of the new state written back, and the rest still waiting in registers. -/
theorem feedForward_upto {m : Machine} {st : BitVec 64} {init work : Ssz.Sha256.Spec.State}
    (base : m.read t1 = st)
    (working : ∀ j, j < 8 → Holds m (wordHome 0 j) (stateWord work j))
    (incoming : ∀ j, j < 8 → m.word32 (st + BitVec.ofNat 64 (4 * j)) = stateWord init j) :
    ∀ n, n ≤ 8 →
      let m' := execBlock ((List.range n).flatMap feedWordCode) m
      m'.read t1 = st ∧
        (∀ j, n ≤ j → j < 8 → Holds m' (wordHome 0 j) (stateWord work j)) ∧
        (∀ j, j < n → m'.word32 (st + BitVec.ofNat 64 (4 * j)) = stateWord init j + stateWord work j) ∧
        (∀ y, ¬Within y st (4 * n) → m'.mem y = m.mem y) ∧
        ∀ x, x ∉ stateRegs.toList → x ≠ t0 → m'.read x = m.read x
  | 0, _ => ⟨base, fun j _ small => working j small, fun _ below => absurd below (Nat.not_lt_zero _),
    fun _ _ => rfl, fun _ _ _ => rfl⟩
  | n + 1, bound => by
    intro m'
    obtain ⟨baseN, waiting, written, memN, frameN⟩ := feedForward_upto base working incoming n (by omega)
    simp only [m', List.range_succ, List.flatMap_append, List.flatMap_singleton, execBlock_append]
    generalize execBlock ((List.range n).flatMap feedWordCode) m = mn at baseN waiting written memN frameN
    -- This word's home, which no other register shares.
    have home := wordHome_zero n (by omega)
    have zs : (0 : Reg) ≠ wordHome 0 n := (nonzero 0 n 0 0).1
    have st0 : wordHome 0 n ≠ t0 := (wordHome_ne 0 n 0 0).2.2.1
    have st1 : wordHome 0 n ≠ t1 := (wordHome_ne 0 n 0 0).2.2.2
    have z0 : (0 : Reg) ≠ t0 := by decide
    have t01 : t0 ≠ t1 := by decide
    simp (disch := reg_ne) only [feedWordCode, ← home, execBlock_cons, execBlock_nil, Instr.run,
      Machine.read_write_self', Machine.read_write_ne', Machine.read_write_ne, Machine.read_store,
      Machine.load_write, Machine.mem_write, baseN, signExtend_ofNat12 (show 4 * n < 2048 by omega)]
    -- The word read back is still the incoming one, since no earlier store reached it.
    have fresh : mn.load (st + BitVec.ofNat 64 (4 * n)) 4 = m.load (st + BitVec.ofNat 64 (4 * n)) 4 := by
      apply Machine.load_congr
      intro i within
      apply memN
      rw [show st + BitVec.ofNat 64 (4 * n) + BitVec.ofNat 64 i = st + BitVec.ofNat 64 (4 * n + i) by
        rw [BitVec.add_assoc, BitVec.ofNat_add]]
      rw [within_offset (by omega)]
      omega
    have incomingN := incoming n (by omega)
    have workN := waiting n (by omega) (by omega)
    simp only [Machine.word32] at incomingN
    simp only [Holds] at workN
    refine ⟨trivial, fun j above below => ?_, fun j below => ?_, fun y outside => ?_,
      fun x outside xt => ?_⟩
    · -- A later home is neither this word's home nor the temporary.
      rw [Holds, Machine.read_store,
        Machine.read_write_ne (wordHome_ne_wordHome (by omega) (by omega) (by omega)),
        Machine.read_write_ne (wordHome_ne 0 j 0 0).2.2.1]
      exact waiting j (by omega) below
    · by_cases now : j = n
      · subst now
        rw [Machine.word32_store_self, setWidth_sext32, setWidth_add32, setWidth_sext32, fresh,
          incomingN, workN, setWidth_signExtend32, BitVec.add_comm]
      · -- An earlier word sits four or more bytes away from this store.
        rw [Machine.word32_store_other (disjoint_offsets (by omega) (by omega)), Machine.word32_write,
          Machine.word32_write]
        exact written j (by omega)
    · rw [Machine.mem_store_of_not_within fun inside =>
          outside (within_sub inside (by omega) (by omega)),
        Machine.mem_write, Machine.mem_write]
      exact memN y fun inside => outside (within_mono inside (by omega))
    · have xs : x ≠ wordHome 0 n := by
        rintro rfl
        exact outside (by simp [home, Vector.getElem_mem])
      rw [Machine.read_write_ne xs, Machine.read_write_ne xt]
      exact frameN x outside xt

end Ssz.Asm.Sha256
