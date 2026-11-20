import SszNative.Driver.Prove
import SszNative.Proofs.Driver.Branch.Common

/-! Powers of two and right shifts by a counted number of places, as calls. -/

namespace EthLib.Consensus.Ssz.Native.Driver.ProveProof

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Driver.BranchProof

/-- Doubling a word a counted number of times gives two to that count, wrapped. -/
theorem pow2_body (m : Module) (w : World) (sp : Nat) (k : UInt64) (mem : Memory) :
    ∃ env', Runs m w sp (entryEnv [k]) mem ProvePow2.fn.body env' mem ∧ env' 1 = UInt64.ofNat (2 ^ k.toNat) := by
  -- The power starts at one, and the count at zero.
  have s1 := Runs.set m w sp (entryEnv [k]) mem 1 (.lit 1) 1 rfl
  have s2 := Runs.set m w sp (assign (entryEnv [k]) 1 1) mem 2 (.lit 0) 0 rfl
  -- Each pass doubles the power and counts one, keeping the power two to the count.
  obtain ⟨env', mem', loop, ⟨same, hk, le, pow⟩, done⟩ := Runs.loop_inv (m := m) (w := w) (sp := sp)
    (c := Ir.Expr.lt (Ir.Var.mk 2) (Ir.Var.mk 0))
    (body := .block [Ir.Stmt.assign ⟨1⟩ (Ir.Var.mk 1 + Ir.Var.mk 1), Ir.Stmt.assign ⟨2⟩ (Ir.Var.mk 2 + 1)])
    (fun env mem' => mem' = mem ∧ env 0 = k ∧ (env 2).toNat ≤ k.toNat ∧ env 1 = UInt64.ofNat (2 ^ (env 2).toNat))
    (fun env _ => k.toNat - (env 2).toNat)
    (fun env mem' _ => ⟨_, rfl⟩)
    (fun env mem' v ⟨same, hk, le, pow⟩ hv nz => by
      have below := lt_of_eval rfl rfl hv nz
      dsimp only at below
      rw [hk] at below
      refine ⟨_, _, Runs.block_cons (Runs.set m w sp env mem' 1 _ _ rfl)
        (Runs.block_cons (Runs.set m w sp _ mem' 2 _ _ rfl) (Runs.block_nil m w sp _ mem')), ⟨same, ?_, ?_, ?_⟩, ?_⟩
      all_goals simp only [assign, show (1 : Nat) ≠ 2 by decide, show (2 : Nat) ≠ 1 by decide,
        show (0 : Nat) ≠ 2 by decide, show (0 : Nat) ≠ 1 by decide, ite_false, ite_true, aluResult]
      · exact hk
      · rw [toNat_add_of_lt _ _ (by simp; have := k.toNat_lt; omega)]
        simp only [UInt64.reduceToNat]
        omega
      · rw [toNat_add_of_lt _ _ (by simp; have := k.toNat_lt; omega), pow]
        simp only [UInt64.reduceToNat, Nat.pow_succ]
        apply UInt64.toNat_inj.mp
        simp [UInt64.toNat_add, Nat.add_mod, Nat.mul_two]
      · rw [toNat_add_of_lt _ _ (by simp; have := k.toNat_lt; omega)]
        simp only [UInt64.reduceToNat]
        omega)
    (assign (assign (entryEnv [k]) 1 1) 2 0) mem ⟨rfl, by simp [assign, entryEnv], by simp [assign], by simp [assign]⟩
  subst same
  refine ⟨env', Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons loop (Runs.block_nil m w sp _ _))), ?_⟩
  -- On exit the count has reached the exponent.
  have reached := not_lt_of_eval rfl rfl done
  dsimp only at reached
  rw [hk] at reached
  rw [pow, show (env' 2).toNat = k.toNat by omega]

/-- A call of the power function returns two to its argument, wrapped, and writes nothing. -/
theorem pow2_calls {m : Module} {w : World} (hf : m.fns.lookup "ssz_prove_pow2" = some ProvePow2.fn) {sp : Nat}
    (room : w.stackLo + 8 + 8 * ProvePow2.fn.frame ≤ sp) (k : UInt64) (mem : Memory) :
    Calls m w "ssz_prove_pow2" sp [k] mem (UInt64.ofNat (2 ^ k.toNat)) mem := by
  obtain ⟨env', run, pow⟩ := pow2_body m w (sp - 8 - 8 * ProvePow2.fn.frame) k mem
  exact Calls.fn hf room rfl run (by simp [ProvePow2.fn, eval, pow])

/-- Halving a word a counted number of times divides it by two to that count. -/
theorem shr_body (m : Module) (w : World) (sp : Nat) (x k : UInt64) (mem : Memory) :
    ∃ env', Runs m w sp (entryEnv [x, k]) mem ProveShr.fn.body env' mem ∧
      (env' 0).toNat = x.toNat / 2 ^ k.toNat := by
  -- The count starts at zero.
  have s1 := Runs.set m w sp (entryEnv [x, k]) mem 2 (.lit 0) 0 rfl
  -- Each pass halves the word and counts one, keeping the word the argument over two to the count.
  obtain ⟨env', mem', loop, ⟨same, hk, le, quot⟩, done⟩ := Runs.loop_inv (m := m) (w := w) (sp := sp)
    (c := Ir.Expr.lt (Ir.Var.mk 2) (Ir.Var.mk 1))
    (body := .block [Ir.Stmt.assign ⟨0⟩ (.shr (Ir.Var.mk 0) 1), Ir.Stmt.assign ⟨2⟩ (Ir.Var.mk 2 + 1)])
    (fun env mem' => mem' = mem ∧ env 1 = k ∧ (env 2).toNat ≤ k.toNat ∧
      (env 0).toNat = x.toNat / 2 ^ (env 2).toNat)
    (fun env _ => k.toNat - (env 2).toNat)
    (fun env mem' _ => ⟨_, rfl⟩)
    (fun env mem' v ⟨same, hk, le, quot⟩ hv nz => by
      have below := lt_of_eval rfl rfl hv nz
      dsimp only at below
      rw [hk] at below
      refine ⟨_, _, Runs.block_cons (Runs.set m w sp env mem' 0 _ _ rfl)
        (Runs.block_cons (Runs.set m w sp _ mem' 2 _ _ rfl) (Runs.block_nil m w sp _ mem')), ⟨same, ?_, ?_, ?_⟩, ?_⟩
      all_goals simp only [assign, show (0 : Nat) ≠ 2 by decide, show (2 : Nat) ≠ 0 by decide,
        show (1 : Nat) ≠ 2 by decide, show (1 : Nat) ≠ 0 by decide, ite_false, ite_true, aluResult]
      · exact hk
      · rw [toNat_add_of_lt _ _ (by simp; have := k.toNat_lt; omega)]
        simp only [UInt64.reduceToNat]
        omega
      · rw [toNat_add_of_lt _ _ (by simp; have := k.toNat_lt; omega), toNat_shr_one, quot]
        simp only [UInt64.reduceToNat, Nat.pow_succ, Nat.div_div_eq_div_mul]
      · rw [toNat_add_of_lt _ _ (by simp; have := k.toNat_lt; omega)]
        simp only [UInt64.reduceToNat]
        omega)
    (assign (entryEnv [x, k]) 2 0) mem ⟨rfl, by simp [assign, entryEnv], by simp [assign], by simp [assign, entryEnv]⟩
  subst same
  refine ⟨env', Runs.block_cons s1 (Runs.block_cons loop (Runs.block_nil m w sp _ _)), ?_⟩
  -- On exit the count has reached the shift.
  have reached := not_lt_of_eval rfl rfl done
  dsimp only at reached
  rw [hk] at reached
  rw [quot, show (env' 2).toNat = k.toNat by omega]

/-- A call of the shift function returns its word divided by two to its count, and writes nothing. -/
theorem shr_calls {m : Module} {w : World} (hf : m.fns.lookup "ssz_prove_shr" = some ProveShr.fn) {sp : Nat}
    (room : w.stackLo + 8 + 8 * ProveShr.fn.frame ≤ sp) (x k : UInt64) (mem : Memory) :
    ∃ r, r.toNat = x.toNat / 2 ^ k.toNat ∧ Calls m w "ssz_prove_shr" sp [x, k] mem r mem := by
  obtain ⟨env', run, quot⟩ := shr_body m w (sp - 8 - 8 * ProveShr.fn.frame) x k mem
  exact ⟨env' 0, quot, Calls.fn hf room rfl run (by simp [ProveShr.fn, eval])⟩

end EthLib.Consensus.Ssz.Native.Driver.ProveProof
