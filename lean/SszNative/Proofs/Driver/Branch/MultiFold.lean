import SszNative.Proofs.Driver.Branch.MultiSpec

/-!
The fold loop of the compiled multiproof verifier: one level per pass, between two node-set areas used in turn.

Each pass writes the level's parents, then the entries off the level, into the other area, and swaps the two.
-/

namespace Ssz.Native.Driver.BranchProof

open Ssz.Native.Ir Ssz.Native.Asm

/-- Four evaluated arguments evaluate together. -/
theorem mapM_four {w : World} {env : Env} {mem : Memory} {a b c d : Ir.Expr} {x y z u : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) (hc : eval w env mem c = some z)
    (hd : eval w env mem d = some u) : [a, b, c, d].mapM (eval w env mem) = some [x, y, z, u] := by
  simp [List.mapM_cons, ha, hb, hc, hd]

/-- The fold loop: the two areas, a node set whose fold is the target, or the refusal that ended it. -/
def FoldInv (ready : Memory → Prop) (free : Nat → Prop) (mem : Memory) (job ctx scratch X Y : UInt64)
    (M : Nat) (F : Except Err ByteArray) (env : Env) (mem' : Memory) : Prop :=
  env 0 = job ∧ env 1 = ctx ∧ env 8 = scratch ∧
    ((env 11 = X ∧ env 12 = Y) ∨ (env 11 = Y ∧ env 12 = X)) ∧ (env 13).toNat ≤ M ∧ ready mem' ∧
    (∀ a, free a → ¬ (X.toNat ≤ a ∧ a < X.toNat + 80 * M) → ¬ (Y.toNat ≤ a ∧ a < Y.toNat + 80 * M) →
      ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + 8) → mem' a = mem a) ∧
    ((env 9 = 0 ∧ foldToRoot (env 15).toNat (entriesAt mem' (env 11).toNat (env 13).toNat) = F) ∨
      (env 9 = 11 ∧ env 15 = 0 ∧ ∃ e, F = .error e))

/-- The fold loop ends at depth zero, with the fold's target still that of its node set, or refused. -/
theorem fold_loop {m : Module} {w : World} {ctx : UInt64} {ready : Memory → Prop} {free : Nat → Prop}
    {room : Nat} (hash : PairHashing m w ctx ready free room)
    (hp : m.fns.lookup "ssz_branch_fold_parents" = some FoldParents.fn)
    (hk : m.fns.lookup "ssz_branch_fold_kept" = some FoldKept.fn)
    (hl : m.fns.lookup "ssz_branch_level" = some Level.fn) (hf : m.fns.lookup "ssz_branch_find" = some Find.fn)
    {sp : Nat} (deep : w.stackLo + 240 + room ≤ sp) {mem : Memory} {job scratch X Y : UInt64} {M : Nat}
    (ax : w.access X.toNat (80 * M) = true) (ay : w.access Y.toNat (80 * M) = true)
    (as : w.access scratch.toNat 8 = true)
    (fx : ∀ k < 80 * M, free (X.toNat + k)) (fy : ∀ k < 80 * M, free (Y.toNat + k))
    (fs : ∀ k < 8, free (scratch.toNat + k))
    (xy : Apart (X.toNat, 80 * M) (Y.toNat, 80 * M)) (sx : Apart (scratch.toNat, 8) (X.toNat, 80 * M))
    (sy : Apart (scratch.toNat, 8) (Y.toNat, 80 * M)) (F : Except Err ByteArray) (env : Env) (mem' : Memory)
    (start : FoldInv ready free mem job ctx scratch X Y M F env mem') {Q : Env → Memory → Prop}
    (post : ∀ env' mem'', FoldInv ready free mem job ctx scratch X Y M F env' mem'' → env' 15 = 0 → Q env' mem'') :
    Wp m w sp (Stmt.while_ (Ir.Expr.lt 0 VerifyMultiproof.depth)
      [Stmt.callInto VerifyMultiproof.answer "ssz_branch_fold_parents" [VerifyMultiproof.cur, VerifyMultiproof.size,
          VerifyMultiproof.nxt, VerifyMultiproof.depth, VerifyMultiproof.ctx, VerifyMultiproof.scratch],
        Stmt.ifElse (Ir.Expr.ne VerifyMultiproof.answer 0) [VerifyMultiproof.depth ::= 0]
          [Stmt.callInto VerifyMultiproof.t "ssz_branch_fold_kept" [VerifyMultiproof.cur, VerifyMultiproof.size,
              VerifyMultiproof.nxt + 40 * Ir.Expr.ld VerifyMultiproof.scratch, VerifyMultiproof.depth],
            VerifyMultiproof.size ::= Ir.Expr.ld VerifyMultiproof.scratch + VerifyMultiproof.t,
            VerifyMultiproof.tmp ::= VerifyMultiproof.cur, VerifyMultiproof.cur ::= VerifyMultiproof.nxt,
            VerifyMultiproof.nxt ::= VerifyMultiproof.tmp, VerifyMultiproof.depth ::= VerifyMultiproof.depth - 1]])
      env mem' Q := by
  have bx := access_bound ax
  have bY := access_bound ay
  have bs := access_bound as
  simp only [Apart] at xy sx sy
  refine Wp.loop (FoldInv ready free mem job ctx scratch X Y M F) (fun env _ => (env 15).toNat) start ?_
  intro env mem' ⟨e0, e1, e8, areas, sizeLe, rd, frame, state⟩
  refine ⟨_, eval_cmp .b rfl rfl, fun nz => ?_, fun z => ?_⟩
  · have pos : 0 < (env 15).toNat := by
      have : ¬ (env 15).toNat = 0 := by simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using nz
      omega
    have running : env 9 = 0 ∧ foldToRoot (env 15).toNat (entriesAt mem' (env 11).toNat (env 13).toNat) = F := by
      rcases state with s | ⟨_, z, _⟩
      · exact s
      · rw [z] at pos; simp at pos
    -- The two areas, as the current and the next one.
    obtain ⟨c, n, ec, en, cOk, nOk, cFree, nFree, cn, sc, sn⟩ : ∃ c n : UInt64, env 11 = c ∧ env 12 = n ∧
        w.access c.toNat (80 * M) = true ∧ w.access n.toNat (80 * M) = true ∧
        (∀ k < 80 * M, free (c.toNat + k)) ∧ (∀ k < 80 * M, free (n.toNat + k)) ∧
        (Apart (c.toNat, 80 * M) (n.toNat, 80 * M) ∧ Apart (scratch.toNat, 8) (c.toNat, 80 * M) ∧
          Apart (scratch.toNat, 8) (n.toNat, 80 * M)) := by
      rcases areas with ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨X, Y, a, b, ax, ay, fx, fy, by simp only [Apart]; omega, by simp only [Apart]; omega,
          by simp only [Apart]; omega⟩
      · exact ⟨Y, X, a, b, ay, ax, fy, fx, by simp only [Apart]; omega, by simp only [Apart]; omega,
          by simp only [Apart]; omega⟩
    simp only [Apart] at cn sc sn
    have bc := access_bound cOk
    have bn := access_bound nOk
    obtain ⟨d, hd⟩ : ∃ d, (env 15).toNat = d + 1 := ⟨(env 15).toNat - 1, by omega⟩
    -- The first pass, from the current area into the next one.
    obtain ⟨r, mem2, callP, rd2, postP, frame2⟩ := fold_parents_calls hp hl hf hash deep c (env 13) n (env 15)
      scratch mem' rd (access_prefix cOk (by omega)) (access_prefix nOk (by omega)) as
      (fun k hk => cFree k (by omega)) (fun k hk => nFree k (by omega)) fs
      (by simp only [Apart]; omega) (by simp only [Apart]; omega)
    rw [← ec, ← en, ← e8, ← e1] at callP
    rw [ec] at running
    have cNow : entriesAt mem2 c.toNat (env 13).toNat = entriesAt mem' c.toNat (env 13).toNat :=
      entriesAt_congr fun k hk => frame2 _ (cFree k (by omega)) (by omega) (by omega)
    refine Wp.cons (Wp.call (values := [env 11, env 13, env 12, env 15, env 1, env 8]) rfl ⟨_, mem2, callP, ?_⟩)
    have swap : (c = X ∧ n = Y) ∨ (c = Y ∧ n = X) := by rw [← ec, ← en]; exact areas
    have frameUp : ∀ a, free a → ¬ (X.toNat ≤ a ∧ a < X.toNat + 80 * M) → ¬ (Y.toNat ≤ a ∧ a < Y.toNat + 80 * M) →
        ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + 8) → mem2 a = mem a := by
      intro a fa ox oy os
      rw [frame2 a fa (by rcases swap with ⟨_, h2⟩ | ⟨_, h2⟩ <;> subst h2 <;> omega)
        (by omega), frame a fa ox oy os]
    cases hL : levelParents (env 15).toNat (entriesAt mem' c.toNat (env 13).toNat)
        (entriesAt mem' c.toNat (env 13).toNat) with
    | error e =>
      -- A refusal ends the fold.
      rw [hL] at postP
      have r11 : r = 11 := postP
      refine Wp.cons (Wp.ite (eval_ne rfl rfl) (fun _ => ?_) (fun z => ?_))
      · refine Wp.cons (Wp.set rfl (Wp.nil (Wp.nil ⟨?_, ?_⟩)))
        · simp only [FoldInv, assign, ↓reduceIte, Nat.reduceEqDiff]
          refine ⟨e0, e1, e8, areas, sizeLe, rd2, frameUp, .inr ⟨r11, trivial, e, ?_⟩⟩
          rw [← running.2, hd, foldToRoot_succ_error d _ (by rw [← hd]; exact hL)]
        · simp only [assign, ↓reduceIte]; simp; omega
      · simp only [assign, ↓reduceIte, r11] at z; exact absurd z (by decide)
    | ok ps =>
      rw [hL] at postP
      obtain ⟨r0, word, written⟩ := postP
      have lenPK := levelParents_length _ _ _ _ hL
      rw [entriesAt_length] at lenPK
      have psTo : ps.length.toUInt64.toNat = ps.length := toNat_ofNat_of_lt _ (by omega)
      refine Wp.cons (Wp.ite (eval_ne rfl rfl) (fun bad => ?_) (fun _ => ?_))
      · simp only [assign, ↓reduceIte, r0] at bad; exact absurd rfl bad
      -- The second pass, into the next area right after the parents.
      have dAddr : (n + 40 * ps.length.toUInt64).toNat = n.toNat + 40 * ps.length := by
        rw [toNat_addr _ _ _ (by rw [psTo]; simp; omega), psTo]; simp
      obtain ⟨mem3, callK, wordsK, frame3⟩ := fold_kept_calls (w := w) hk hl (sp := sp) (by omega) c (env 13)
        (n + 40 * ps.length.toUInt64) (env 15) mem2 (access_prefix cOk (by omega))
        (by rw [dAddr]; exact access_sub nOk (by omega)) (by rw [dAddr]; simp only [Apart]; omega)
      rw [cNow] at callK wordsK
      rw [dAddr] at wordsK frame3
      have sNow : readLE mem2 scratch.toNat 8 = ps.length.toUInt64 := word
      have argNext : eval w (assign env 9 r) mem2 (Ir.Expr.var 12 + 40 * Ir.Expr.ld (Ir.Expr.var 8)) =
          some (n + 40 * ps.length.toUInt64) := by
        rw [eval_add rfl (eval_mul rfl (eval_ld (x := scratch) (by simp [assign, e8, eval]) (by simpa using as))),
          sNow]
        simp [assign, en]
      rw [← ec] at callK
      refine Wp.cons (Wp.call (values := [env 11, env 13, n + 40 * ps.length.toUInt64, env 15])
        (mapM_four rfl rfl argNext rfl) ⟨_, mem3, callK, ?_⟩)
      rw [ec]
      generalize hK : levelKept (env 15).toNat (entriesAt mem' c.toNat (env 13).toNat) = K at callK wordsK lenPK ⊢
      have kTo : K.length.toUInt64.toNat = K.length := toNat_ofNat_of_lt _ (by omega)
      have sAfter : readLE mem3 scratch.toNat 8 = ps.length.toUInt64 := by
        rw [readLE_congr mem3 mem2 _ 8 (fun k hk => frame3 _ (by omega)), sNow]
      have sumTo : (ps.length.toUInt64 + K.length.toUInt64).toNat = ps.length + K.length := by
        rw [toNat_add_of_lt _ _ (by rw [psTo, kTo]; omega), psTo, kTo]
      have dTo : (env 15 - 1).toNat = d := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
      refine Wp.cons (Wp.set (eval_add (eval_ld (x := scratch) (by simp [assign, e8, eval]) (by simpa using as)) rfl)
        (Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons (Wp.set (eval_sub rfl rfl)
          (Wp.nil (Wp.nil ⟨?_, ?_⟩)))))))))))
      · simp only [FoldInv, assign, ↓reduceIte, Nat.reduceEqDiff, sAfter]
        refine ⟨e0, e1, e8, ?_, by rw [sumTo]; omega, hash.ready_frame _ _ rd2 fun a nf => frame3 a fun inside =>
          nf (by rw [show a = n.toNat + (a - n.toNat) by omega]; exact nFree _ (by omega)), fun a fa ox oy os => ?_,
          .inl ⟨by simp [r0], ?_⟩⟩
        · rw [en, ec]; rcases swap with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact .inr ⟨h2, h1⟩
          · exact .inl ⟨h2, h1⟩
        · rw [frame3 a (by rcases swap with ⟨_, h2⟩ | ⟨_, h2⟩ <;> subst h2 <;> omega), frameUp a fa ox oy os]
        · rw [en, dTo, sumTo, entriesAt_append, wordsK,
            entriesAt_congr (fun k hk => frame3 _ (by omega)), written, ← hK, hd,
            ← foldToRoot_succ_ok d _ _ (by rw [← hd]; exact hL), ← hd]
          exact running.2
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, dTo]; omega
  · have zero : (env 15).toNat = 0 := by simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using z
    exact post env mem' ⟨e0, e1, e8, areas, sizeLe, rd, frame, state⟩
      (UInt64.toNat_inj.mp (by rw [zero]; rfl))

end Ssz.Native.Driver.BranchProof
