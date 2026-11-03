import SszNative.Proofs.Driver.Branch.Common

/-! The level of an index, the search for a word, and the comparison of two nodes, as calls. -/

namespace EthLib.Consensus.Ssz.Native.Driver.BranchProof

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm

/-- Halving a word down to one counts its level. -/
theorem level_body (m : Module) (w : World) (sp : Nat) (x : UInt64) (mem : Memory) :
    ∃ env', Runs m w sp (entryEnv [x]) mem Level.fn.body env' mem ∧ env' 1 = (Nat.log2 x.toNat).toUInt64 := by
  -- The count starts at zero.
  have start := Runs.set m w sp (entryEnv [x]) mem 1 (.lit 0) 0 rfl
  -- Each pass halves the word and counts one level, keeping their sum the level of the argument.
  obtain ⟨env', mem', loop, ⟨same, sum⟩, done⟩ := Runs.loop_inv (m := m) (w := w) (sp := sp)
    (c := Ir.Expr.lt 1 (Ir.Var.mk 0)) (body := .block [Ir.Stmt.assign ⟨0⟩ (.shr (Ir.Var.mk 0) 1),
      Ir.Stmt.assign ⟨1⟩ (Ir.Var.mk 1 + 1)])
    (fun env mem' => mem' = mem ∧ (env 1).toNat + Nat.log2 (env 0).toNat = Nat.log2 x.toNat)
    (fun env _ => (env 0).toNat)
    (fun env mem' _ => ⟨_, rfl⟩)
    (fun env mem' v ⟨same, sum⟩ hv nz => by
      have big' := lt_of_eval rfl rfl hv nz
      simp only [UInt64.reduceToNat] at big'
      refine ⟨_, _, Runs.block_cons (Runs.set m w sp env mem' 0 _ _ rfl)
        (Runs.block_cons (Runs.set m w sp _ mem' 1 _ _ rfl) (Runs.block_nil m w sp _ mem')), ⟨same, ?_⟩, ?_⟩
      · have half := log2_half (env 0).toNat (by omega)
        have bound := log2_lt_64 x
        simp only [assign, toNat_shr_one, show (0 : Nat) ≠ 1 by decide, show (1 : Nat) ≠ 0 by decide, ite_false,
          ite_true, aluResult]
        rw [toNat_add_of_lt _ _ (by simp; omega)]
        simp only [UInt64.reduceToNat]
        omega
      · simp only [assign, show (0 : Nat) ≠ 1 by decide, ite_false, ite_true, toNat_shr_one]
        omega)
    (assign (entryEnv [x]) 1 0) mem ⟨rfl, by simp [assign, entryEnv, Nat.log2]⟩
  subst same
  refine ⟨env', Runs.block_cons start (Runs.block_cons loop (Runs.block_nil m w sp _ _)), ?_⟩
  -- On exit the word is at most one, so the count alone is the level.
  have small' := not_lt_of_eval rfl rfl done
  simp only [UInt64.reduceToNat] at small'
  rw [log2_small _ (by omega)] at sum
  apply UInt64.toNat_inj.mp
  rw [toNat_ofNat_of_lt _ (by have := log2_lt_64 x; omega)]
  omega

/-- A call of the level function returns the level of its argument and writes nothing. -/
theorem level_calls {m : Module} {w : World} (hf : m.fns.lookup "ssz_branch_level" = some Level.fn) {sp : Nat}
    (room : w.stackLo + 32 ≤ sp) (x : UInt64) (mem : Memory) :
    Calls m w "ssz_branch_level" sp [x] mem (Nat.log2 x.toNat).toUInt64 mem := by
  obtain ⟨env', run, level⟩ := level_body m w (sp - 8 - 8 * Level.fn.frame) x mem
  have frame : Level.fn.frame = 3 := by decide
  exact Calls.fn hf (by omega) rfl run (by simp [Level.fn, eval, level])

/-- The first position below a count whose word equals a key, or the count when none does. -/
def firstAt (f : Nat → UInt64) (key : UInt64) : Nat → Nat
  | 0 => 0
  | n + 1 => if firstAt f key n < n then firstAt f key n else if f n = key then n else n + 1

/-- The first position is the one before which nothing matches, and which matches or is the count. -/
theorem firstAt_eq (f : Nat → UInt64) (key : UInt64) :
    ∀ (count i : Nat), (∀ j < i, f j ≠ key) → (i = count ∨ (i < count ∧ f i = key)) → firstAt f key count = i
  | 0, i, _, h => by
    simp only [firstAt]
    omega
  | n + 1, i, before, h => by
    simp only [firstAt]
    by_cases early : i < n
    · -- The match lies below the last position, where the shorter search already finds it.
      have hit : i < n ∧ f i = key := by
        rcases h with h | ⟨_, h⟩
        · omega
        · exact ⟨early, h⟩
      have := firstAt_eq f key n i before (.inr hit)
      rw [this, ite_eq_left early]
    · -- Nothing matches below the last position, so the shorter search runs to its end.
      have := firstAt_eq f key n n (fun j hj => before j (by omega)) (.inl rfl)
      rw [this, ite_eq_right (by omega)]
      by_cases last : i = n
      · subst last
        have hit : f i = key := by
          rcases h with h | ⟨_, h⟩
          · omega
          · exact h
        simp [hit]
      · have miss : f n ≠ key := before n (by omega)
        simp only [miss, ite_false]
        omega

/-- The first position is at most the count. -/
theorem firstAt_le (f : Nat → UInt64) (key : UInt64) : ∀ count, firstAt f key count ≤ count
  | 0 => by simp [firstAt]
  | n + 1 => by
    have := firstAt_le f key n
    simp only [firstAt]
    split
    · omega
    · split <;> omega

/-- The first position has no match before it, and is either the count or a match. -/
theorem firstAt_spec (f : Nat → UInt64) (key : UInt64) :
    ∀ n, (∀ j < firstAt f key n, f j ≠ key) ∧ (firstAt f key n = n ∨ (firstAt f key n < n ∧ f (firstAt f key n) = key))
  | 0 => by simp [firstAt]
  | n + 1 => by
    obtain ⟨before, stop⟩ := firstAt_spec f key n
    simp only [firstAt]
    by_cases early : firstAt f key n < n
    · rw [ite_eq_left early]
      rcases stop with e | ⟨_, hit⟩
      · omega
      · exact ⟨before, .inr ⟨by omega, hit⟩⟩
    · rw [ite_eq_right early]
      have atEnd : firstAt f key n = n := by have := firstAt_le f key n; omega
      rw [atEnd] at before
      by_cases hit : f n = key
      · rw [ite_eq_left hit]; exact ⟨before, .inr ⟨by omega, hit⟩⟩
      · rw [ite_eq_right hit]
        refine ⟨fun j hj => ?_, .inl rfl⟩
        by_cases last : j = n
        · rw [last]; exact hit
        · exact before j (by omega)

/-- The first position falls short of the count exactly when some position below it matches. -/
theorem firstAt_lt_iff (f : Nat → UInt64) (key : UInt64) (n : Nat) :
    firstAt f key n < n ↔ ∃ j < n, f j = key := by
  obtain ⟨before, stop⟩ := firstAt_spec f key n
  constructor
  · intro lt
    rcases stop with e | ⟨_, hit⟩
    · omega
    · exact ⟨_, lt, hit⟩
  · intro ⟨j, hj, hit⟩
    have le := firstAt_le f key n
    by_cases e : firstAt f key n = n
    · exact absurd hit (before j (by omega))
    · omega

/-- Words a stride apart from a base, by position. -/
def big32 (mem : Memory) (base stride : Nat) (j : Nat) : UInt64 :=
  readLE mem (base + stride * j) 8

/-- The search keeps its arguments, a stop at least its position, and no match before its position. -/
private def FindInv (mem : Memory) (base stride count key : UInt64) (env : Env) (mem' : Memory) : Prop :=
  mem' = mem ∧ env 0 = base ∧ env 1 = stride ∧ env 2 = count ∧ env 3 = key ∧ (env 4).toNat ≤ (env 5).toNat ∧
    (∀ j < (env 4).toNat, big32 mem base.toNat stride.toNat j ≠ key) ∧
    (env 5 = count ∨ (env 5 = env 4 ∧ (env 4).toNat < count.toNat ∧
      big32 mem base.toNat stride.toNat (env 4).toNat = key))

/-- A call of the search returns the first position holding the key, or the count, and writes nothing. -/
theorem find_calls {m : Module} {w : World} (hf : m.fns.lookup "ssz_branch_find" = some Find.fn) {sp : Nat}
    (room : w.stackLo + 80 ≤ sp) (base stride count key : UInt64) (mem : Memory)
    (acc : ∀ j < count.toNat, w.access (base.toNat + stride.toNat * j) 8 = true) :
    Calls m w "ssz_branch_find" sp [base, stride, count, key] mem
      (firstAt (big32 mem base.toNat stride.toNat) key count.toNat).toUInt64 mem := by
  obtain ⟨r, mem', call, hr, hm⟩ := Calls.of_wp (Q := fun r mem' =>
      r = (firstAt (big32 mem base.toNat stride.toNat) key count.toNat).toUInt64 ∧ mem' = mem)
    (w := w) (sp := sp) (args := [base, stride, count, key]) (mem := mem) hf
    (by have frame : Find.fn.frame = 9 := by decide
        omega) rfl (by
    simp only [Find.fn]
    refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons ?_))))
    refine Wp.loop (FindInv mem base stride count key) (fun env _ => (env 5).toNat - (env 4).toNat)
      ⟨rfl, rfl, rfl, rfl, rfl, by simp [assign], by simp [assign], by simp [assign, entryEnv]⟩ ?_
    intro env mem' ⟨same, h0, h1, h2, h3, le, before, stop⟩
    subst same
    refine ⟨_, eval_cmp .b rfl rfl, fun nz => ?_, fun z => ?_⟩
    · -- A pass reads the word at the position, and stops there on a match or moves on.
      have lt : (env 4).toNat < (env 5).toNat := by
        simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using nz
      have inRange : (env 4).toNat < count.toNat := by
        rcases stop with s | ⟨s, _, _⟩ <;> rw [s] at lt <;> omega
      have a := acc _ inRange
      have addr : (env 0 + env 1 * env 4).toNat = base.toNat + stride.toNat * (env 4).toNat := by
        have := access_bound a
        rw [h0, h1, toNat_addr _ _ _ (by omega)]
      have word : eval w env mem' (Ir.Expr.ld (Ir.Expr.var 0 + Ir.Expr.var 1 * Ir.Expr.var 4)) =
          some (big32 mem' base.toNat stride.toNat (env 4).toNat) := by
        rw [eval_ld (eval_add rfl (eval_mul rfl rfl)) (by rw [addr]; exact a), big32, addr]
      refine Wp.ite (eval_eq word rfl) (fun hit => ?_) (fun miss => ?_)
      · -- A match stops the search where it stands.
        have hit : big32 mem' base.toNat stride.toNat (env 4).toNat = key := by
          rw [← h3]
          by_cases e : big32 mem' base.toNat stride.toNat (env 4).toNat = env 3
          · exact e
          · simp [e] at hit
        refine Wp.cons (Wp.set rfl (Wp.nil ⟨⟨rfl, ?_⟩, ?_⟩)) <;> simp only [assign, ↓reduceIte,
          Nat.reduceEqDiff]
        · exact ⟨h0, h1, h2, h3, Nat.le_refl _, before, .inr ⟨trivial, inRange, hit⟩⟩
        · omega
      · -- A miss moves the position on by one.
        have miss : big32 mem' base.toNat stride.toNat (env 4).toNat ≠ key := by
          rw [← h3]; intro eq; simp [eq] at miss
        have next : (env 4 + 1).toNat = (env 4).toNat + 1 := by
          have := count.toNat_lt
          rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
        refine Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨⟨rfl, ?_⟩, ?_⟩)) <;>
          simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]
        · refine ⟨h0, h1, h2, h3, by omega, fun j hj => ?_, ?_⟩
          · by_cases at_ : j = (env 4).toNat
            · rw [at_]; exact miss
            · exact before j (by omega)
          · rcases stop with s | ⟨s, _, _⟩
            · exact .inl s
            · rw [s] at lt; omega
        · omega
    · -- On exit the position has reached the stop, which is the count or the first match.
      have ge : ¬ (env 4).toNat < (env 5).toNat := by
        simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using z
      refine Wp.nil ⟨env 4, rfl, ?_, rfl⟩
      apply UInt64.toNat_inj.mp
      have bound := firstAt_le (big32 mem' base.toNat stride.toNat) key count.toNat
      have := count.toNat_lt
      rw [toNat_ofNat_of_lt _ (by omega)]
      symm
      apply firstAt_eq _ _ _ _ before
      rcases stop with s | ⟨s, r, hit⟩
      · rw [s] at le ge; exact .inl (by omega)
      · exact .inr ⟨r, hit⟩)
  rw [hr, hm] at call
  exact call

/-- One byte read as a word is that byte. -/
theorem readLE_one (mem : Memory) (a : Nat) : readLE mem a 1 = (mem a).toUInt64 := by
  simp [readLE]

/-- Two nodes read from memory are equal exactly when their bytes agree. -/
theorem readNode_eq_iff (mem : Memory) (a b : Nat) :
    readNode mem a = readNode mem b ↔ ∀ k < 32, mem (a + k) = mem (b + k) := by
  constructor
  · intro h k hk
    -- Equal nodes agree at every position.
    have := congrArg (fun n : ByteArray => n.data[k]?) h
    simpa [readNode, hk] using this
  · intro h
    simp only [readNode]
    congr 2
    funext i
    exact h i.val i.isLt

/-- The comparison keeps its arguments, and its flag says whether every byte so far agrees. -/
private def SameInv (mem : Memory) (a b : UInt64) (env : Env) (mem' : Memory) : Prop :=
  mem' = mem ∧ env 0 = a ∧ env 1 = b ∧ (env 2).toNat ≤ 32 ∧
    env 3 = if ∀ k < (env 2).toNat, mem (a.toNat + k) = mem (b.toNat + k) then 1 else 0

/-- A call of the comparison returns one when two nodes are equal, zero otherwise, and writes nothing. -/
theorem same_calls {m : Module} {w : World} (hf : m.fns.lookup "ssz_branch_same" = some Same.fn) {sp : Nat}
    (room : w.stackLo + 64 ≤ sp) (a b : UInt64) (mem : Memory)
    (ha : w.access a.toNat 32 = true) (hb : w.access b.toNat 32 = true) :
    Calls m w "ssz_branch_same" sp [a, b] mem (if readNode mem a.toNat = readNode mem b.toNat then 1 else 0) mem := by
  obtain ⟨r, mem', call, hr, hm⟩ := Calls.of_wp (Q := fun r mem' =>
      r = (if readNode mem a.toNat = readNode mem b.toNat then 1 else 0) ∧ mem' = mem)
    (w := w) (sp := sp) (args := [a, b]) (mem := mem) hf
    (by have frame : Same.fn.frame = 7 := by decide
        omega) rfl (by
    simp only [Same.fn]
    refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons ?_))))
    refine Wp.loop (SameInv mem a b) (fun env _ => 32 - (env 2).toNat)
      ⟨rfl, rfl, rfl, by simp [assign], by simp [assign]⟩ ?_
    intro env mem' ⟨same, h0, h1, le, flag⟩
    subst same
    refine ⟨_, eval_cmp .b rfl rfl, fun nz => ?_, fun z => ?_⟩
    · -- A pass compares one byte, and clears the flag on a difference.
      have lt : (env 2).toNat < 32 := by
        simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using nz
      have ba := access_bound ha
      have bb := access_bound hb
      have pa : (env 0 + env 2).toNat = a.toNat + (env 2).toNat := by
        rw [h0, toNat_add_of_lt _ _ (by omega)]
      have pb : (env 1 + env 2).toNat = b.toNat + (env 2).toNat := by
        rw [h1, toNat_add_of_lt _ _ (by omega)]
      have la := eval_ld1 (w := w) (mem := mem') (eval_add (a := Ir.Expr.var 0) (b := Ir.Expr.var 2) rfl rfl)
        (by rw [pa]; exact access_sub ha (by omega))
      have lb := eval_ld1 (w := w) (mem := mem') (eval_add (a := Ir.Expr.var 1) (b := Ir.Expr.var 2) rfl rfl)
        (by rw [pb]; exact access_sub hb (by omega))
      rw [pa, readLE_one] at la
      rw [pb, readLE_one] at lb
      have next : (env 2 + 1).toNat = (env 2).toNat + 1 := by
        rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
      -- The flag after the pass covers one more byte.
      have extend : (∀ k < (env 2).toNat + 1, mem' (a.toNat + k) = mem' (b.toNat + k)) ↔
          ((∀ k < (env 2).toNat, mem' (a.toNat + k) = mem' (b.toNat + k)) ∧
            mem' (a.toNat + (env 2).toNat) = mem' (b.toNat + (env 2).toNat)) := by
        constructor
        · intro h; exact ⟨fun k hk => h k (by omega), h _ (by omega)⟩
        · intro ⟨h, last⟩ k hk
          by_cases at_ : k = (env 2).toNat
          · rw [at_]; exact last
          · exact h k (by omega)
      refine Wp.cons (Wp.ite (eval_ne la lb) (fun differ => ?_) (fun agree => ?_))
      · have differ : mem' (a.toNat + (env 2).toNat) ≠ mem' (b.toNat + (env 2).toNat) := by
          intro e; simp [e] at differ
        refine Wp.set rfl (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨⟨rfl, ?_⟩, ?_⟩))) <;>
          simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]
        · refine ⟨h0, h1, by omega, ?_⟩
          rw [ite_eq_right]
          intro h; exact differ ((extend.mp h).2)
        · omega
      · have agree : mem' (a.toNat + (env 2).toNat) = mem' (b.toNat + (env 2).toNat) := by
          by_cases e : mem' (a.toNat + (env 2).toNat) = mem' (b.toNat + (env 2).toNat)
          · exact e
          · simp only [ite_eq_right (fun h => e (UInt8.toUInt64_inj.mp h))] at agree; exact absurd agree (by decide)
        refine Wp.skip (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨⟨rfl, ?_⟩, ?_⟩))) <;>
          simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]
        · refine ⟨h0, h1, by omega, ?_⟩
          rw [flag]
          by_cases all : ∀ k < (env 2).toNat, mem' (a.toNat + k) = mem' (b.toNat + k)
          · rw [ite_eq_left all, ite_eq_left (extend.mpr ⟨all, agree⟩)]
          · rw [ite_eq_right all, ite_eq_right (fun h => all (extend.mp h).1)]
        · omega
    · -- On exit all 32 bytes were compared.
      have ge : ¬ (env 2).toNat < 32 := by
        simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using z
      refine Wp.nil ⟨env 3, rfl, ?_, rfl⟩
      rw [flag, show (env 2).toNat = 32 by omega]
      by_cases all : ∀ k < 32, mem' (a.toNat + k) = mem' (b.toNat + k)
      · rw [ite_eq_left all, ite_eq_left ((readNode_eq_iff _ _ _).mpr all)]
      · rw [ite_eq_right all, ite_eq_right (fun h => all ((readNode_eq_iff _ _ _).mp h))])
  rw [hr, hm] at call
  exact call

end EthLib.Consensus.Ssz.Native.Driver.BranchProof
