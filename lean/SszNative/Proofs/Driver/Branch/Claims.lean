import SszNative.Proofs.Driver.Branch.Paths

/-!
The compiled claim check refuses exactly what the specification's index checks refuse, with the same first refusal.

The check runs in three loops: one for repeats, one over the claims, and one inside it over a claim's ancestors.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.BranchProof

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm

/-- The word a check answers: zero when it passes, or the code of its refusal. -/
def unitCode : Except Err Unit → UInt64
  | .ok _ => 0
  | .error e => answerCode (.error e)

/-- A key is found among some words exactly when its value is one of them. -/
theorem firstAt_words_lt_iff (mem : Memory) (a n : Nat) (key : UInt64) :
    firstAt (big32 mem a 8) key n < n ↔ key.toNat ∈ wordsAt mem a n := by
  rw [firstAt_lt_iff]
  simp only [big32, wordsAt, List.mem_map, List.mem_range]
  constructor
  · intro ⟨j, hj, e⟩; exact ⟨j, hj, by rw [e]⟩
  · intro ⟨j, hj, e⟩; exact ⟨j, hj, UInt64.toNat_inj.mp e⟩

/-- The first words have no repeat, one more exactly when the next is not among them. -/
theorem nodup_wordsAt_succ (mem : Memory) (a n : Nat) :
    (wordsAt mem a (n + 1)).Nodup ↔
      (wordsAt mem a n).Nodup ∧ (readLE mem (a + 8 * n) 8).toNat ∉ wordsAt mem a n := by
  rw [wordsAt_succ, List.nodup_append]
  simp only [List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil, and_self, true_and,
    List.mem_singleton]
  constructor
  · intro ⟨h, out⟩; exact ⟨h, fun m => out _ m _ rfl rfl⟩
  · intro ⟨h, out⟩; exact ⟨h, fun x hx y hy e => by subst hy; subst e; exact out hx⟩

/-- A word read from a list of words in usable memory has an address that does not wrap. -/
theorem word_addr {w : World} {a : UInt64} {n : Nat} (acc : w.access a.toNat (8 * n) = true) (i : UInt64)
    (hi : i.toNat < n) : (a + 8 * i).toNat = a.toNat + 8 * i.toNat ∧ w.access (a.toNat + 8 * i.toNat) 8 = true := by
  have := access_bound acc
  refine ⟨by rw [toNat_addr _ _ _ (by simp; omega)]; simp, access_sub acc (by omega)⟩

/-- A search through usable words, run as a call, returns whether and where the key is. -/
theorem find_words {m : Module} {w : World} (hf : m.fns.lookup "ssz_branch_find" = some Find.fn) {sp : Nat}
    (room : w.stackLo + 80 ≤ sp) {a : UInt64} {n : Nat} (acc : w.access a.toNat (8 * n) = true) (count : UInt64)
    (le : count.toNat ≤ n) (key : UInt64) (mem : Memory) :
    Calls m w "ssz_branch_find" sp [a, 8, count, key] mem (firstAt (big32 mem a.toNat 8) key count.toNat).toUInt64 mem :=
  find_calls hf room a 8 count key mem fun j hj => access_sub acc (by simp at *; omega)

/-- The first match among some words, as a word, is the count exactly when the key is not among them. -/
theorem firstAt_words_eq_count (mem : Memory) (a : Nat) (count key : UInt64) :
    (firstAt (big32 mem a 8) key count.toNat).toUInt64 = count ↔ key.toNat ∉ wordsAt mem a count.toNat := by
  rw [← firstAt_words_lt_iff]
  have le := firstAt_le (big32 mem a 8) key count.toNat
  have := count.toNat_lt
  constructor
  · intro h
    have := congrArg UInt64.toNat h
    rw [toNat_ofNat_of_lt _ (by omega)] at this
    omega
  · intro h
    apply UInt64.toNat_inj.mp
    rw [toNat_ofNat_of_lt _ (by omega)]; omega

/-- The ancestor loop: it ends having found a claimed ancestor on the walked path, or found none on it. -/
theorem ancestors_loop {m : Module} {w : World} (hf : m.fns.lookup "ssz_branch_find" = some Find.fn) {sp : Nat}
    (room : w.stackLo + 80 ≤ sp) {mem : Memory} {indices count : UInt64}
    (acc : w.access indices.toNat (8 * count.toNat) = true) (env : Env) (e0 : env 0 = indices) (e1 : env 1 = count)
    (e5 : env 5 = 0) {Q : Env → Memory → Prop}
    (post : ∀ env', env' 0 = indices → env' 1 = count → env' 2 = env 2 → env' 3 = env 3 →
      ((env' 5 = 0 ∧ ((pathOf (env 6).toNat).any fun x => (wordsAt mem indices.toNat count.toNat).contains x) = false) ∨
        (env' 5 = 10 ∧ ((pathOf (env 6).toNat).any fun x => (wordsAt mem indices.toNat count.toNat).contains x) = true)) →
      Q env' mem) :
    Wp m w sp (Stmt.while_ (Ir.Expr.lt 1 CheckClaims.above)
      [Stmt.callInto CheckClaims.found "ssz_branch_find" [CheckClaims.indices, 8, CheckClaims.count, CheckClaims.above],
        Stmt.ifElse (Ir.Expr.ne CheckClaims.found CheckClaims.count) [CheckClaims.answer ::= 10, CheckClaims.above ::= 0]
          [CheckClaims.above ::= .shr CheckClaims.above 1]]) env mem Q := by
  let L := wordsAt mem indices.toNat count.toNat
  let hit (x : Nat) : Bool := (pathOf x).any fun y => L.contains y
  refine Wp.loop (fun env' mem' => mem' = mem ∧ env' 0 = indices ∧ env' 1 = count ∧ env' 2 = env 2 ∧
      env' 3 = env 3 ∧ ((env' 5 = 0 ∧ hit (env 6).toNat = hit (env' 6).toNat) ∨
        (env' 5 = 10 ∧ hit (env 6).toNat = true ∧ env' 6 = 0)))
    (fun env' _ => (env' 6).toNat) ⟨rfl, e0, e1, rfl, rfl, .inl ⟨e5, rfl⟩⟩ ?_
  intro env' mem' ⟨same, f0, f1, f2, f3, state⟩
  subst same
  refine ⟨_, eval_cmp .b rfl rfl, fun nz => ?_, fun z => ?_⟩
  · -- Above the root, look the ancestor up among the claims.
    have big : 1 < (env' 6).toNat := by simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using nz
    have running : env' 5 = 0 ∧ hit (env 6).toNat = hit (env' 6).toNat := by
      rcases state with s | ⟨_, _, z⟩
      · exact s
      · rw [z] at big; simp at big
    have call := find_words hf room acc count (Nat.le_refl _) (env' 6) mem'
    rw [← f0, ← f1] at call
    refine Wp.cons (Wp.call (values := [env' 0, 8, env' 1, env' 6]) rfl ⟨_, mem', call, ?_⟩)
    have cons := pathOf_cons (env' 6).toNat (by omega)
    refine Wp.cons (Wp.ite (eval_ne rfl rfl) (fun found => ?_) (fun missing => ?_))
    · -- A claimed ancestor refuses the claim, and stops the walk.
      have member : (env' 6).toNat ∈ L := by
        have : ¬ (firstAt (big32 mem' indices.toNat 8) (env' 6) count.toNat).toUInt64 = count := by
          intro h
          simp only [assign, ↓reduceIte, Nat.reduceEqDiff, f0, f1] at found
          rw [ite_eq_left h] at found
          exact found rfl
        rw [firstAt_words_eq_count] at this
        exact Classical.not_not.mp this
      refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.nil (Wp.nil ⟨⟨rfl, ?_⟩, ?_⟩))))) <;>
        simp only [assign, ↓reduceIte, Nat.reduceEqDiff]
      · refine ⟨f0, f1, f2, f3, .inr ⟨trivial, ?_, trivial⟩⟩
        rw [running.2]; simp [hit, cons, member]
      · simp; omega
    · -- An unclaimed ancestor passes, and the walk goes on from its parent.
      have outside : (env' 6).toNat ∉ L := by
        have : (firstAt (big32 mem' indices.toNat 8) (env' 6) count.toNat).toUInt64 = count := by
          by_cases h : (firstAt (big32 mem' indices.toNat 8) (env' 6) count.toNat).toUInt64 = count
          · exact h
          · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, f0, f1] at missing
            rw [ite_eq_right h] at missing
            exact absurd missing (by decide)
        exact (firstAt_words_eq_count _ _ _ _).mp this
      refine Wp.cons (Wp.set (eval_shr1 rfl) (Wp.nil (Wp.nil ⟨⟨rfl, ?_⟩, ?_⟩))) <;>
        simp only [assign, ↓reduceIte, Nat.reduceEqDiff, toNat_shr_one]
      · refine ⟨f0, f1, f2, f3, .inl ⟨running.1, ?_⟩⟩
        rw [running.2]; simp [hit, cons, outside]
      · omega
  · -- At the root, the walk has covered the whole path.
    have small : ¬ 1 < (env' 6).toNat := by simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using z
    refine post env' f0 f1 f2 f3 ?_
    rcases state with ⟨s, h⟩ | ⟨s, h, _⟩
    · refine .inl ⟨s, ?_⟩
      have : hit (env' 6).toNat = false := by simp [hit, pathOf_small (env' 6).toNat (by omega)]
      rw [← this, ← h]
    · exact .inr ⟨s, h⟩

/-- The claims from a position on are the claim there, then those after it. -/
theorem wordsAt_drop (mem : Memory) (a n i : Nat) (h : i < n) :
    (wordsAt mem a n).drop i = (readLE mem (a + 8 * i) 8).toNat :: (wordsAt mem a n).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [wordsAt_length]; exact h), wordsAt_getElem]

/-- The claims checked so far, then the rest, are all the claims checked. -/
theorem rejectClaimPaths_split (L : List Nat) (i : Nat) :
    rejectClaimPaths L L = (rejectClaimPaths L (L.take i)).bind fun _ => rejectClaimPaths L (L.drop i) := by
  rw [← rejectClaimPaths_append, List.take_append_drop]

/-- The repeat loop: it ends with no repeat among all claims, or with the code for a repeat. -/
private def RepeatInv (mem : Memory) (indices count : UInt64) (env : Env) (mem' : Memory) : Prop :=
  mem' = mem ∧ env 0 = indices ∧ env 1 = count ∧ (env 2).toNat ≤ count.toNat ∧
    ((env 5 = 0 ∧ (wordsAt mem indices.toNat (env 2).toNat).Nodup) ∨
      (env 5 = 9 ∧ ¬ (wordsAt mem indices.toNat count.toNat).Nodup ∧ (env 2).toNat = count.toNat))

/-- The claim loop: claims so far pass, or the code of the first refusal is kept. -/
private def ClaimInv (mem : Memory) (indices count : UInt64) (env : Env) (mem' : Memory) : Prop :=
  mem' = mem ∧ env 0 = indices ∧ env 1 = count ∧ (env 2).toNat ≤ count.toNat ∧
    ((env 5 = 0 ∧ rejectClaimPaths (wordsAt mem indices.toNat count.toNat)
        (wordsAt mem indices.toNat (env 2).toNat) = .ok ()) ∨
      (env 5 ≠ 0 ∧ (env 2).toNat = count.toNat ∧ env 5 = unitCode (rejectClaimPaths
        (wordsAt mem indices.toNat count.toNat) (wordsAt mem indices.toNat count.toNat))))

/-- A call of the claim check answers the code of the specification's index checks on the claims, and writes nothing. -/
theorem check_claims_calls {m : Module} {w : World} (hc : m.fns.lookup "ssz_branch_check_claims" = some CheckClaims.fn)
    (hf : m.fns.lookup "ssz_branch_find" = some Find.fn) {sp : Nat} (room : w.stackLo + 192 ≤ sp) (indices count : UInt64)
    (mem : Memory) (acc : w.access indices.toNat (8 * count.toNat) = true) :
    Calls m w "ssz_branch_check_claims" sp [indices, count] mem
      (unitCode (rejectRelated (wordsAt mem indices.toNat count.toNat))) mem := by
  have frameSize : CheckClaims.fn.frame = 13 := by decide
  let L := wordsAt mem indices.toNat count.toNat
  suffices body : Wp m w (sp - 112) CheckClaims.fn.body (entryEnv [indices, count]) mem
      fun env mem' => ∃ r, eval w env mem' (Ir.Expr.var 5) = some r ∧ (r = unitCode (rejectRelated L) ∧ mem' = mem) by
    obtain ⟨r, mem', call, hr, hm⟩ := Calls.of_wp (Q := fun r mem' => r = unitCode (rejectRelated L) ∧ mem' = mem)
      (w := w) (sp := sp) (args := [indices, count]) (mem := mem) hc (by omega) rfl (by rw [frameSize]; exact body)
    rw [hr, hm] at call
    exact call
  have deep : w.stackLo + 80 ≤ sp - 112 := by omega
  simp only [CheckClaims.fn]
  refine Wp.cons (Wp.set rfl (Wp.cons (Wp.ite (eval_eq rfl rfl) (fun zero => ?_) (fun nonzero => ?_))))
  · -- No claim at all.
    have : count = 0 := by
      by_cases h : count = 0
      · exact h
      · simp [assign, entryEnv, h] at zero
    refine Wp.cons (Wp.set rfl (Wp.nil (Wp.nil ⟨_, rfl, ?_, rfl⟩)))
    simp [assign, L, this, wordsAt, rejectRelated_eq, unitCode, answerCode]
  have c0 : count.toNat ≠ 0 := by
    intro h
    have : count = 0 := UInt64.toNat_inj.mp (by rw [h]; rfl)
    simp [assign, entryEnv, this] at nonzero
  have nonempty : L ≠ [] := by
    intro h; have := congrArg List.length h; simp [L, wordsAt_length] at this; omega
  -- The repeat loop, then the claim loop when no claim repeats.
  refine Wp.cons (Wp.set rfl (Wp.cons ?_))
  refine Wp.loop (RepeatInv mem indices count) (fun env _ => count.toNat - (env 2).toNat)
    ⟨rfl, by simp [assign, entryEnv], by simp [assign, entryEnv], by simp [assign],
      .inl ⟨by simp [assign], by simp [assign, wordsAt]⟩⟩ ?_
  intro env mem' ⟨same, e0, e1, le, state⟩
  subst same
  refine ⟨_, eval_cmp .b rfl rfl, fun nz => ?_, fun z => ?_⟩
  · have lt : (env 2).toNat < (env 1).toNat := by simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using nz
    rw [e1] at lt
    have running : env 5 = 0 ∧ (wordsAt mem' indices.toNat (env 2).toNat).Nodup := by
      rcases state with s | ⟨_, _, e⟩
      · exact s
      · omega
    obtain ⟨addr, wacc⟩ := word_addr acc (env 2) lt
    have key := eval_ld (w := w) (env := env) (mem := mem') (eval_add (a := Ir.Expr.var 0)
      (b := 8 * Ir.Expr.var 2) rfl (eval_mul rfl rfl)) (by rw [e0, addr]; exact wacc)
    rw [e0, addr] at key
    let k := readLE mem' (indices.toNat + 8 * (env 2).toNat) 8
    have call := find_words hf deep acc (env 2) (by omega) k mem'
    rw [← e0] at call
    refine Wp.cons (Wp.call (values := [env 0, 8, env 2, k])
      (by simp only [List.mapM_cons, List.mapM_nil, key]; rfl) ⟨_, mem', call, ?_⟩)
    rw [e0]
    refine Wp.cons (Wp.ite (eval_ne rfl rfl) (fun found => ?_) (fun missing => ?_))
    · -- An earlier copy of this claim: a repeat.
      have repeat_ : k.toNat ∈ wordsAt mem' indices.toNat (env 2).toNat := by
        have hne : ¬ (firstAt (big32 mem' indices.toNat 8) k (env 2).toNat).toUInt64 = env 2 := by
          intro h
          simp only [assign, ↓reduceIte, Nat.reduceEqDiff] at found
          rw [ite_eq_left h] at found
          exact found rfl
        exact Classical.not_not.mp (mt (firstAt_words_eq_count _ _ _ _).mpr hne)
      have dup : ¬ (wordsAt mem' indices.toNat count.toNat).Nodup := by
        intro nd
        have prefix_ := nd.sublist (List.take_sublist ((env 2).toNat + 1) _)
        rw [wordsAt_take _ _ _ _ (by omega), nodup_wordsAt_succ] at prefix_
        exact prefix_.2 repeat_
      refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.nil (Wp.nil ⟨⟨rfl, ?_⟩, ?_⟩))))) <;>
        simp only [assign, ↓reduceIte, Nat.reduceEqDiff]
      · exact ⟨e0, e1, by rw [e1]; exact Nat.le_refl _, .inr ⟨trivial, dup, by rw [e1]⟩⟩
      · rw [e1]; omega
    · -- No earlier copy: the claims so far stay distinct.
      have fresh : k.toNat ∉ wordsAt mem' indices.toNat (env 2).toNat := by
        have : (firstAt (big32 mem' indices.toNat 8) k (env 2).toNat).toUInt64 = env 2 := by
          by_cases h : (firstAt (big32 mem' indices.toNat 8) k (env 2).toNat).toUInt64 = env 2
          · exact h
          · simp only [assign, ↓reduceIte, Nat.reduceEqDiff] at missing
            rw [ite_eq_right h] at missing
            exact absurd missing (by decide)
        exact (firstAt_words_eq_count _ _ _ _).mp this
      have next : (env 2 + 1).toNat = (env 2).toNat + 1 := by
        have := count.toNat_lt
        rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
      refine Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil (Wp.nil ⟨⟨rfl, ?_⟩, ?_⟩))) <;>
        simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]
      · exact ⟨e0, e1, by omega, .inl ⟨running.1, (nodup_wordsAt_succ _ _ _).mpr ⟨running.2, fresh⟩⟩⟩
      · omega
  -- After the repeat loop: the claim loop runs only when no claim repeats.
  have ge : ¬ (env 2).toNat < (env 1).toNat := by simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using z
  rw [e1] at ge
  refine Wp.cons (Wp.set rfl (Wp.cons (Wp.ite (eval_eq rfl rfl) (fun clean => ?_) (fun repeated => ?_))))
  · have quiet : env 5 = 0 := by
      by_cases h : env 5 = 0
      · exact h
      · simp [assign, h] at clean
    have nodup : L.Nodup := by
      rcases state with ⟨_, nd⟩ | ⟨s, _, _⟩
      · rwa [show (env 2).toNat = count.toNat by omega] at nd
      · rw [s] at quiet; exact absurd quiet (by decide)
    have related : rejectRelated L = rejectClaimPaths L L := by
      rw [rejectRelated_eq, ite_eq_right nonempty, ite_eq_right (not_not_intro nodup)]
    refine Wp.cons ?_
    refine Wp.loop (ClaimInv mem' indices count) (fun env _ => count.toNat - (env 2).toNat)
      ⟨rfl, by simp [assign, e0], by simp [assign, e1], by simp [assign],
        .inl ⟨by simp [assign, quiet], by simp [assign, wordsAt, rejectClaimPaths]⟩⟩ ?_
    intro env2 mem2 ⟨same2, f0, f1, le2, st2⟩
    subst same2
    refine ⟨_, eval_cmp .b rfl rfl, fun nz => ?_, fun z => ?_⟩
    · have lt : (env2 2).toNat < count.toNat := by
        rw [← f1]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using nz
      have running : env2 5 = 0 ∧ rejectClaimPaths L (wordsAt mem2 indices.toNat (env2 2).toNat) = .ok () := by
        rcases st2 with s | ⟨_, e, _⟩
        · exact s
        · omega
      obtain ⟨addr, wacc⟩ := word_addr acc (env2 2) lt
      have key := eval_ld (w := w) (env := env2) (mem := mem2) (eval_add (a := Ir.Expr.var 0)
        (b := 8 * Ir.Expr.var 2) rfl (eval_mul rfl rfl)) (by rw [f0, addr]; exact wacc)
      rw [f0, addr] at key
      have total0 := rejectClaimPaths_split L (env2 2).toNat
      rw [wordsAt_take _ _ _ _ (by omega), running.2, wordsAt_drop _ _ _ _ lt] at total0
      generalize hc : readLE mem2 (indices.toNat + 8 * (env2 2).toNat) 8 = c at key total0
      -- All the claims are checked as those before this one, then this one, then the rest.
      have total : rejectClaimPaths L L = rejectClaimPaths L (c.toNat :: L.drop ((env2 2).toNat + 1)) := by
        rw [total0]
        rfl
      have next : (env2 2 + 1).toNat = (env2 2).toNat + 1 := by
        have := count.toNat_lt
        rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
      refine Wp.cons (Wp.set key (Wp.cons (Wp.ite (eval_eq rfl rfl) (fun zero => ?_) (fun nonzero' => ?_))))
      · -- A claim of zero names no node.
        have cz : c = 0 := by
          by_cases h : c = 0
          · exact h
          · simp only [assign, ↓reduceIte, ite_eq_right h] at zero
            exact absurd rfl zero
        refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.nil (Wp.nil ⟨⟨rfl, ?_⟩, ?_⟩))))) <;>
          simp only [assign, ↓reduceIte, Nat.reduceEqDiff]
        · refine ⟨f0, f1, by rw [f1]; exact Nat.le_refl _, .inr ⟨by decide, by rw [f1], ?_⟩⟩
          rw [total, rejectClaimPaths_cons, cz]; rfl
        · rw [f1]; omega
      have c0' : c.toNat ≠ 0 := by
        intro h
        have : c = 0 := UInt64.toNat_inj.mp (by rw [h]; rfl)
        simp only [assign, ↓reduceIte, this] at nonzero'
        exact absurd nonzero' (by decide)
      refine Wp.ite (eval_eq rfl rfl) (fun one => ?_) (fun notOne => ?_)
      · -- The root's index has no branch.
        have c1 : c = 1 := by
          by_cases h : c = 1
          · exact h
          · simp only [assign, ↓reduceIte, ite_eq_right h] at one
            exact absurd rfl one
        refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.nil (Wp.nil ⟨⟨rfl, ?_⟩, ?_⟩))))) <;>
          simp only [assign, ↓reduceIte, Nat.reduceEqDiff]
        · refine ⟨f0, f1, by rw [f1]; exact Nat.le_refl _, .inr ⟨by decide, by rw [f1], ?_⟩⟩
          rw [total, rejectClaimPaths_cons, c1]; rfl
        · rw [f1]; omega
      have c1' : c.toNat ≠ 1 := by
        intro h
        have : c = 1 := UInt64.toNat_inj.mp (by rw [h]; rfl)
        simp only [assign, ↓reduceIte, this] at notOne
        exact absurd notOne (by decide)
      -- The strict ancestors, walked from the parent.
      refine Wp.cons (Wp.set (eval_shr1 rfl) (Wp.cons (ancestors_loop hf deep acc _
        (by simp [assign, f0]) (by simp [assign, f1]) (by simp [assign, running.1])
        (fun env' g0 g1 g2 g3 outcome => ?_))))
      simp only [assign, ↓reduceIte, Nat.reduceEqDiff, toNat_shr_one] at g2 g3 outcome
      refine Wp.cons (Wp.ite (eval_ne rfl rfl) (fun bad => ?_) (fun good => ?_))
      · -- A claimed ancestor refuses this claim.
        have loud : env' 5 = 10 ∧ ((pathOf (c.toNat / 2)).any fun x => L.contains x) = true := by
          rcases outcome with ⟨s, _⟩ | s
          · simp [s] at bad
          · exact s
        refine Wp.cons (Wp.set rfl (Wp.nil (Wp.nil (Wp.nil ⟨⟨rfl, ?_⟩, ?_⟩)))) <;>
          simp only [assign, ↓reduceIte, Nat.reduceEqDiff]
        · refine ⟨g0, g1, by rw [g1]; exact Nat.le_refl _, .inr ⟨by rw [loud.1]; decide, by rw [g1], ?_⟩⟩
          rw [loud.1, total, rejectClaimPaths_cons, ite_eq_right c0', ite_eq_right c1', ite_eq_left loud.2]; rfl
        · rw [g1]; omega
      · -- No claimed ancestor: this claim passes, and the next one is checked.
        have quiet' : env' 5 = 0 ∧ ((pathOf (c.toNat / 2)).any fun x => L.contains x) = false := by
          rcases outcome with s | ⟨s, _⟩
          · exact s
          · simp [s] at good
        refine Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil (Wp.nil (Wp.nil ⟨⟨rfl, ?_⟩, ?_⟩)))) <;>
          simp only [assign, ↓reduceIte, Nat.reduceEqDiff, g2, next]
        · refine ⟨g0, g1, by omega, .inl ⟨quiet'.1, ?_⟩⟩
          rw [wordsAt_succ, rejectClaimPaths_append, running.2]
          rw [hc]
          show rejectClaimPaths L [c.toNat] = _
          rw [rejectClaimPaths_cons, ite_eq_right c0', ite_eq_right c1', quiet'.2]; rfl
        · omega
    · -- Every claim was checked: the answer is the first refusal, or zero.
      have done : ¬ (env2 2).toNat < count.toNat := by
        rw [← f1]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using z
      refine Wp.nil (Wp.nil (Wp.nil ⟨_, rfl, ?_, rfl⟩))
      rw [related]
      rcases st2 with ⟨s, h⟩ | ⟨_, _, h⟩
      · rw [show (env2 2).toNat = count.toNat by omega] at h
        rw [s, h]; rfl
      · exact h
  · -- A repeat was found: the answer is its code.
    have loud : env 5 = 9 := by
      rcases state with ⟨s, _⟩ | ⟨s, _, _⟩
      · simp [assign, s] at repeated
      · exact s
    have dup : ¬ L.Nodup := by
      rcases state with ⟨s, _⟩ | ⟨_, d, _⟩
      · simp [assign, s] at repeated
      · exact d
    refine Wp.skip (Wp.nil (Wp.nil ⟨_, rfl, ?_, rfl⟩))
    simp [assign, loud, rejectRelated_eq, nonempty, dup, unitCode, answerCode, L]

end EthLib.Consensus.Ssz.Native.Driver.BranchProof
