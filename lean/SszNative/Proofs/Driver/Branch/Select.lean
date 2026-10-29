import SszNative.Proofs.Driver.Branch.Helpers

/-!
The compiled selection writes the distinct candidates, largest first.

Each pass scans every candidate for the largest one below the last written, and writes it.
A pass that finds none ends the selection, every candidate having been written.
-/

namespace Ssz.Native.Driver.BranchProof

open Ssz.Native.Ir Ssz.Native.Asm

/-- The scan of one pass: the largest qualifying candidate so far, if any qualified. -/
theorem scan_loop {m : Module} {w : World} {sp : Nat} {mem : Memory} {cands count : UInt64}
    (acc : w.access cands.toNat (8 * count.toNat) = true) (env : Env) (e0 : env 0 = cands) (e1 : env 1 = count)
    (e5 : env 5 = 0) (e7 : env 7 = 0) {Q : Env → Memory → Prop}
    (post : ∀ env', env' 0 = cands → env' 1 = count → env' 2 = env 2 → env' 3 = env 3 → env' 4 = env 4 →
      env' 9 = env 9 → env' 10 = env 10 →
      ((env' 5 = 0 ∧ ∀ x ∈ wordsAt mem cands.toNat count.toNat, ¬ (env 3 = 0 ∨ x < (env 4).toNat)) ∨
        (env' 5 = 1 ∧ (env 3 = 0 ∨ (env' 6).toNat < (env 4).toNat) ∧
          (env' 6).toNat ∈ wordsAt mem cands.toNat count.toNat ∧
          ∀ x ∈ wordsAt mem cands.toNat count.toNat, (env 3 = 0 ∨ x < (env 4).toNat) → x ≤ (env' 6).toNat)) →
      Q env' mem) :
    Wp m w sp (Stmt.while_ (Ir.Expr.lt SelectDesc.i SelectDesc.count)
      [SelectDesc.c ::= Ir.Expr.ld (SelectDesc.cands + 8 * SelectDesc.i),
        Stmt.when ((Ir.Expr.eq SelectDesc.started 0) ||| (Ir.Expr.lt SelectDesc.c SelectDesc.last))
          [Stmt.when ((Ir.Expr.eq SelectDesc.found 0) ||| (Ir.Expr.lt SelectDesc.best SelectDesc.c))
            [SelectDesc.best ::= SelectDesc.c, SelectDesc.found ::= 1]],
        SelectDesc.i ::= SelectDesc.i + 1]) env mem Q := by
  let C := wordsAt mem cands.toNat count.toNat
  let qual (x : Nat) : Prop := env 3 = 0 ∨ x < (env 4).toNat
  refine Wp.loop (fun env' mem' => mem' = mem ∧ env' 0 = cands ∧ env' 1 = count ∧ env' 2 = env 2 ∧ env' 3 = env 3 ∧
      env' 4 = env 4 ∧ env' 9 = env 9 ∧ env' 10 = env 10 ∧ (env' 7).toNat ≤ count.toNat ∧
      ((env' 5 = 0 ∧ ∀ j < (env' 7).toNat, ¬ qual (readLE mem (cands.toNat + 8 * j) 8).toNat) ∨
        (env' 5 = 1 ∧ qual (env' 6).toNat ∧ (env' 6).toNat ∈ C ∧
          ∀ j < (env' 7).toNat, qual (readLE mem (cands.toNat + 8 * j) 8).toNat →
            (readLE mem (cands.toNat + 8 * j) 8).toNat ≤ (env' 6).toNat)))
    (fun env' _ => count.toNat - (env' 7).toNat)
    ⟨rfl, e0, e1, rfl, rfl, rfl, rfl, rfl, by simp [e7], .inl ⟨e5, by simp [e7]⟩⟩ ?_
  intro env' mem' ⟨same, f0, f1, f2, f3, f4, f9, f10, le, state⟩
  subst same
  refine ⟨_, eval_cmp .b rfl rfl, fun nz => ?_, fun z => ?_⟩
  · have lt : (env' 7).toNat < count.toNat := by rw [← f1]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using nz
    obtain ⟨addr, wacc⟩ := word_addr acc (env' 7) lt
    have key := eval_ld (w := w) (env := env') (mem := mem') (eval_add (a := Ir.Expr.var 0)
      (b := 8 * Ir.Expr.var 7) rfl (eval_mul rfl rfl)) (by rw [f0, addr]; exact wacc)
    rw [f0, addr] at key
    have inC : (readLE mem' (cands.toNat + 8 * (env' 7).toNat) 8).toNat ∈ C := by
      simp only [C, wordsAt, List.mem_map, List.mem_range]; exact ⟨_, lt, rfl⟩
    generalize hc : readLE mem' (cands.toNat + 8 * (env' 7).toNat) 8 = c at key inC
    have next : (env' 7 + 1).toNat = (env' 7).toNat + 1 := by
      have := count.toNat_lt
      rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
    -- After the pass over this candidate, the facts hold of one more position.
    have extend : ∀ j < (env' 7).toNat + 1, (readLE mem' (cands.toNat + 8 * j) 8).toNat =
        if j < (env' 7).toNat then (readLE mem' (cands.toNat + 8 * j) 8).toNat else c.toNat := by
      intro j hj
      by_cases early : j < (env' 7).toNat
      · rw [if_pos early]
      · rw [if_neg early, show j = (env' 7).toNat by omega, hc]
    have flag1 := eval_or (eval_eq (a := Ir.Expr.var 3) (b := (0 : Ir.Expr)) (env := assign env' 8 c) (w := w)
      (mem := mem') rfl rfl) (eval_lt (a := Ir.Expr.var 8) (b := Ir.Expr.var 4) rfl rfl)
    rw [or_flags] at flag1
    refine Wp.cons (Wp.set key (Wp.cons (Wp.ite flag1 (fun q => ?_) (fun nq => ?_))))
    · -- A qualifying candidate replaces the best when it is the first or larger.
      have q : qual c.toNat := by
        have : (assign env' 8 c 3 = 0 ∨ (assign env' 8 c 8).toNat < (assign env' 8 c 4).toNat) := by
          by_cases h : (assign env' 8 c 3 = 0 ∨ (assign env' 8 c 8).toNat < (assign env' 8 c 4).toNat)
          · exact h
          · rw [if_neg h] at q; exact absurd rfl q
        simp only [assign, ↓reduceIte, Nat.reduceEqDiff] at this
        rw [f3, f4] at this; exact this
      have flag2 := eval_or (eval_eq (a := Ir.Expr.var 5) (b := (0 : Ir.Expr)) (env := assign env' 8 c) (w := w)
        (mem := mem') rfl rfl) (eval_lt (a := Ir.Expr.var 6) (b := Ir.Expr.var 8) rfl rfl)
      rw [or_flags] at flag2
      refine Wp.cons (Wp.ite flag2 (fun better => ?_) (fun worse => ?_))
      · have better : env' 5 = 0 ∨ (env' 6).toNat < c.toNat := by
          by_cases h : (assign env' 8 c 5 = 0 ∨ (assign env' 8 c 6).toNat < (assign env' 8 c 8).toNat)
          · simpa [assign] using h
          · rw [if_neg h] at better; exact absurd rfl better
        refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.nil (Wp.nil (Wp.cons (Wp.set (eval_add rfl rfl)
          (Wp.nil ⟨⟨rfl, ?_⟩, ?_⟩)))))))) <;>
          simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]
        · refine ⟨f0, f1, f2, f3, f4, f9, f10, by omega, .inr ⟨trivial, q, inC, fun j hj qj => ?_⟩⟩
          rw [extend j hj] at qj ⊢
          split
          · rename_i early
            rw [if_pos early] at qj
            rcases state with ⟨_, none⟩ | ⟨s1, _, _, below⟩
            · exact absurd qj (none j early)
            · have := below j early qj
              rcases better with b | b
              · rw [s1] at b; exact absurd b (by decide)
              · omega
          · omega
        · omega
      · have worse : ¬ (env' 5 = 0 ∨ (env' 6).toNat < c.toNat) := by
          intro h
          rw [if_pos (by simpa [assign] using h)] at worse
          exact absurd worse (by decide)
        refine Wp.skip (Wp.nil (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨⟨rfl, ?_⟩, ?_⟩)))) <;>
          simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]
        · rcases state with ⟨s, _⟩ | ⟨s, qb, mb, below⟩
          · exact absurd (.inl s) worse
          · refine ⟨f0, f1, f2, f3, f4, f9, f10, by omega, .inr ⟨s, qb, mb, fun j hj qj => ?_⟩⟩
            rw [extend j hj] at qj ⊢
            split
            · rename_i early
              rw [if_pos early] at qj
              exact below j early qj
            · rw [if_neg (by assumption)] at qj
              omega
        · omega
    · -- A candidate that does not qualify changes nothing.
      have nq : ¬ qual c.toNat := by
        intro h
        rw [if_pos (by simp only [assign, ↓reduceIte, Nat.reduceEqDiff]; rw [f3, f4]; exact h)] at nq
        exact absurd nq (by decide)
      refine Wp.skip (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨⟨rfl, ?_⟩, ?_⟩))) <;>
        simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]
      · refine ⟨f0, f1, f2, f3, f4, f9, f10, by omega, ?_⟩
        rcases state with ⟨s, none⟩ | ⟨s, qb, mb, below⟩
        · refine .inl ⟨s, fun j hj => ?_⟩
          rw [extend j hj]
          split
          · rename_i early; exact none j early
          · exact nq
        · refine .inr ⟨s, qb, mb, fun j hj qj => ?_⟩
          rw [extend j hj] at qj ⊢
          split
          · rename_i early; rw [if_pos early] at qj; exact below j early qj
          · rename_i late; rw [if_neg late] at qj; exact absurd qj nq
      · omega
  · -- Every candidate was scanned.
    have done : ¬ (env' 7).toNat < count.toNat := by rw [← f1]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using z
    have all : (env' 7).toNat = count.toNat := by omega
    -- A candidate is the word at some position.
    have pos : ∀ x ∈ C, ∃ j < count.toNat, (readLE mem' (cands.toNat + 8 * j) 8).toNat = x := by
      intro x hx
      simp only [C, wordsAt, List.mem_map, List.mem_range] at hx
      exact hx
    refine post env' f0 f1 f2 f3 f4 f9 f10 ?_
    rcases state with ⟨s, none⟩ | ⟨s, qb, mb, below⟩
    · refine .inl ⟨s, fun x hx => ?_⟩
      obtain ⟨j, hj, rfl⟩ := pos x hx
      exact none j (by omega)
    · refine .inr ⟨s, qb, mb, fun x hx qx => ?_⟩
      obtain ⟨j, hj, rfl⟩ := pos x hx
      exact below j (by omega) qx

/-- The selection: the values written fall strictly, are candidates, and are every candidate from the last one up. -/
private def SelInv (mem : Memory) (C : List Nat) (cands count out : UInt64) (env : Env) (mem' : Memory) : Prop :=
  env 0 = cands ∧ env 1 = count ∧ env 2 = out ∧ (env 3 = 0 ∨ env 3 = 1) ∧
    (∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 8 * (env 9).toNat) → mem' a = mem a) ∧
    (wordsAt mem' out.toNat (env 9).toNat).Pairwise (· > ·) ∧ (∀ x ∈ wordsAt mem' out.toNat (env 9).toNat, x ∈ C) ∧
    (env 3 = 0 → (env 9).toNat = 0) ∧
    (env 3 ≠ 0 → (∀ x ∈ wordsAt mem' out.toNat (env 9).toNat, (env 4).toNat ≤ x) ∧
      ∀ x ∈ C, (env 4).toNat ≤ x → x ∈ wordsAt mem' out.toNat (env 9).toNat) ∧
    (env 10 = 1 ∨ (env 10 = 0 ∧ ∀ x ∈ C, x ∈ wordsAt mem' out.toNat (env 9).toNat))

/-- Distinct values drawn from a list are no more than it holds. -/
theorem length_le_of_pairwise {S C : List Nat} (desc : S.Pairwise (· > ·)) (sub : ∀ x ∈ S, x ∈ C) :
    S.length ≤ C.length :=
  List.Nodup.length_le_of_subset (desc.imp fun h => Nat.ne_of_gt h) sub

/--
A call of the selection writes the distinct candidates, largest first, and returns how many there are.

What it writes is a strictly falling list holding exactly the candidates.
-/
theorem select_calls {m : Module} {w : World} (hs : m.fns.lookup "ssz_branch_select" = some SelectDesc.fn)
    {sp : Nat} (room : w.stackLo + 112 ≤ sp) (cands count out : UInt64) (mem : Memory)
    (ac : w.access cands.toNat (8 * count.toNat) = true) (ao : w.access out.toNat (8 * count.toNat) = true)
    (apart : Apart (out.toNat, 8 * count.toNat) (cands.toNat, 8 * count.toNat)) :
    ∃ S mem', Calls m w "ssz_branch_select" sp [cands, count, out] mem S.length.toUInt64 mem' ∧
      wordsAt mem' out.toNat S.length = S ∧ S.Pairwise (· > ·) ∧
      (∀ x, x ∈ S ↔ x ∈ wordsAt mem cands.toNat count.toNat) ∧
      ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 8 * count.toNat) → mem' a = mem a := by
  have frameSize : SelectDesc.fn.frame = 13 := by decide
  generalize hC : wordsAt mem cands.toNat count.toNat = C
  have lenC : C.length = count.toNat := by rw [← hC, wordsAt_length]
  have bc := access_bound ac
  have bo := access_bound ao
  suffices body : Wp m w (sp - 112) SelectDesc.fn.body (entryEnv [cands, count, out]) mem
      fun env mem' => ∃ r, eval w env mem' (Ir.Expr.var 9) = some r ∧ (∃ S, r = S.length.toUInt64 ∧
        wordsAt mem' out.toNat S.length = S ∧ S.Pairwise (· > ·) ∧ (∀ x, x ∈ S ↔ x ∈ C) ∧
        ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 8 * count.toNat) → mem' a = mem a) by
    obtain ⟨r, mem', call, S, hr, words, desc, members, frame⟩ := Calls.of_wp (Q := fun r mem' =>
        ∃ S, r = S.length.toUInt64 ∧ wordsAt mem' out.toNat S.length = S ∧ S.Pairwise (· > ·) ∧
          (∀ x, x ∈ S ↔ x ∈ C) ∧ ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 8 * count.toNat) → mem' a = mem a)
      (w := w) (sp := sp) (args := [cands, count, out]) (mem := mem) hs (by omega) rfl
      (by rw [frameSize]; exact body)
    rw [hr] at call
    exact ⟨S, mem', call, words, desc, members, frame⟩
  simp only [SelectDesc.fn]
  refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons ?_))))))))
  refine Wp.loop (SelInv mem C cands count out)
    (fun env _ => if env 10 = 0 then 0 else count.toNat + 1 - (env 9).toNat)
    ⟨by simp [assign, entryEnv], by simp [assign, entryEnv], by simp [assign, entryEnv], by simp [assign],
      fun _ _ => rfl, by simp [assign, wordsAt], by simp [assign, wordsAt], by simp [assign],
      by simp [assign], by simp [assign]⟩ ?_
  intro env mem' ⟨e0, e1, e2, e3, frame, desc, sub, fresh, lastOk, more⟩
  have lenS := length_le_of_pairwise desc sub
  rw [lenC, wordsAt_length] at lenS
  -- The candidates are read where nothing is written.
  have candsNow : wordsAt mem' cands.toNat count.toNat = C := by
    rw [← hC]
    exact wordsAt_congr fun k hk => frame _ (by simp only [Apart] at apart; omega)
  refine ⟨_, rfl, fun nz => ?_, fun z => ?_⟩
  · have going : env 10 = 1 := by
      rcases more with h | ⟨h, _⟩
      · exact h
      · exact absurd h nz
    refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons
      (scan_loop (mem := mem') ac _ (by simp [assign, e0]) (by simp [assign, e1]) (by simp [assign])
        (by simp [assign]) (fun env' g0 g1 g2 g3 g4 g9 g10 outcome => ?_))))))))
    simp only [assign, ↓reduceIte, Nat.reduceEqDiff] at g2 g3 g4 g9 g10
    rw [candsNow] at outcome
    refine Wp.cons (Wp.ite rfl (fun found => ?_) (fun none => ?_))
    · -- The best qualifying candidate is written next, and becomes the last one.
      obtain ⟨_, qb, mb, below⟩ : env' 5 = 1 ∧ (env 3 = 0 ∨ (env' 6).toNat < (env 4).toNat) ∧
          (env' 6).toNat ∈ C ∧ ∀ x ∈ C, (env 3 = 0 ∨ x < (env 4).toNat) → x ≤ (env' 6).toNat := by
        rcases outcome with ⟨s, _⟩ | s
        · exact absurd s found
        · exact s
      let S := wordsAt mem' out.toNat (env 9).toNat
      have newDesc : (S ++ [(env' 6).toNat]).Pairwise (· > ·) := by
        refine List.pairwise_append.mpr ⟨desc, by simp, fun x hx y hy => ?_⟩
        simp only [List.mem_singleton] at hy
        subst hy
        rcases e3 with s | s
        · have hx' : x ∈ wordsAt mem' out.toNat (env 9).toNat := hx
          rw [fresh s] at hx'; simp [wordsAt] at hx'
        · have := (lastOk (by rw [s]; decide)).1 x hx
          rcases qb with q | q
          · rw [s] at q; exact absurd q (by decide)
          · omega
      have newSub : ∀ x ∈ S ++ [(env' 6).toNat], x ∈ C := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact sub x h
        · simp only [List.mem_singleton] at h; rw [h]; exact mb
      have lenNew := length_le_of_pairwise newDesc newSub
      rw [lenC, List.length_append, wordsAt_length] at lenNew
      simp only [List.length_singleton] at lenNew
      have addrN : (env' 2 + 8 * env' 9).toNat = out.toNat + 8 * (env 9).toNat := by
        rw [g2, g9, e2, toNat_addr _ _ _ (by simp; omega)]; simp
      have nextN : (env' 9 + 1).toNat = (env 9).toNat + 1 := by
        have := count.toNat_lt
        rw [g9, toNat_add_of_lt _ _ (by simp; omega)]; simp
      refine Wp.cons (Wp.store (eval_add rfl (eval_mul rfl rfl)) rfl
        (by rw [addrN]; exact access_sub ao (by simp [Width.bytes]; omega))
        (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl
          (Wp.nil (Wp.nil ⟨?_, ?_⟩)))))))))
      · simp only [SelInv, assign, ↓reduceIte, Nat.reduceEqDiff, addrN, nextN, Width.bytes]
        have written : wordsAt (store mem' (out.toNat + 8 * (env 9).toNat) 8 (qwordByte (env' 6))) out.toNat
            ((env 9).toNat + 1) = S ++ [(env' 6).toNat] := wordsAt_store_end _ _ _ _
        rw [written]
        refine ⟨g0, g1, g2.trans e2, .inr trivial, fun a ha => ?_, newDesc, newSub, by simp, fun _ => ⟨?_, ?_⟩, .inl (by rw [g10]; exact going)⟩
        · rw [store_outside _ _ _ _ _ (by omega)]; exact frame a (by omega)
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · have := List.pairwise_append.mp newDesc
            have := this.2.2 x h (env' 6).toNat (by simp)
            omega
          · simp only [List.mem_singleton] at h; omega
        · intro x hx hle
          by_cases same : x = (env' 6).toNat
          · simp [same]
          rcases e3 with s | s
          · -- Nothing was written before: every candidate qualified, so none exceeds the best.
            have := below x hx (.inl s)
            omega
          · by_cases high : (env 4).toNat ≤ x
            · exact List.mem_append_left _ ((lastOk (by rw [s]; decide)).2 x hx high)
            · have := below x hx (.inr (by omega))
              omega
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, g10, going, nextN]
        simp; omega
    · -- No candidate qualifies: every candidate has been written.
      have none' : ∀ x ∈ C, ¬ (env 3 = 0 ∨ x < (env 4).toNat) := by
        rcases outcome with ⟨_, s⟩ | ⟨s, _⟩
        · exact s
        · rw [s] at none; exact absurd none (by decide)
      refine Wp.cons (Wp.set rfl (Wp.nil (Wp.nil ⟨?_, ?_⟩)))
      · simp only [SelInv, assign, ↓reduceIte, Nat.reduceEqDiff]
        rw [g0, g1, g2, g3, g4, g9]
        refine ⟨rfl, rfl, e2, e3, frame, desc, sub, fresh, lastOk, .inr ⟨trivial, fun x hx => ?_⟩⟩
        have := none' x hx
        have started : env 3 ≠ 0 := fun h => this (.inl h)
        exact (lastOk started).2 x hx (by omega)
      · simp only [assign, ↓reduceIte, going]
        simp; omega
  · -- The selection is over: every candidate is written, distinct and falling.
    have stopped : env 10 = 0 := z
    have complete : ∀ x ∈ C, x ∈ wordsAt mem' out.toNat (env 9).toNat := by
      rcases more with h | ⟨_, h⟩
      · rw [h] at stopped; exact absurd stopped (by decide)
      · exact h
    refine Wp.nil ⟨env 9, rfl, wordsAt mem' out.toNat (env 9).toNat, ?_, by rw [wordsAt_length], desc,
      fun x => ⟨sub x, complete x⟩, fun a ha => frame a (by omega)⟩
    rw [wordsAt_length]
    apply UInt64.toNat_inj.mp
    rw [toNat_ofNat_of_lt _ (by have := count.toNat_lt; omega)]

end Ssz.Native.Driver.BranchProof
