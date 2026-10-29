import SszNative.Proofs.Driver.Branch.MultiFold

/-!
The node set the compiled multiproof verifier folds: the leaves at their indices, then the proof nodes at the helper
indices, written as entries.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.BranchProof

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm

/-- One entry written from an index word and a node elsewhere: a store, a copy, then the next position. -/
theorem entry_write {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {Q : Env → Memory → Prop}
    {dst word node : Ir.Expr} {d x s : UInt64} (step : Stmt)
    (hd : ∀ mem, eval w env mem dst = some d) (hx : eval w env mem (Ir.Expr.ld word) = some x)
    (hs : ∀ mem, eval w env mem node = some s)
    (ad : w.access d.toNat 40 = true) (as : w.access s.toNat 32 = true) (apart : Apart (d.toNat, 40) (s.toNat, 32))
    (h : ∀ mem', readLE mem' d.toNat 8 = x → readNode mem' (d.toNat + 8) = readNode mem s.toNat →
      (∀ a, ¬ (d.toNat ≤ a ∧ a < d.toNat + 40) → mem' a = mem a) → Wp m w sp (.block [step]) env mem' Q) :
    Wp m w sp (.block ([Stmt.st dst (Ir.Expr.ld word)] ++ copy32 (dst + 8) node ++ [step])) env mem Q := by
  have bd := access_bound ad
  have bs := access_bound as
  simp only [Apart] at apart
  have d8 : (d + 8).toNat = d.toNat + 8 := by rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
  have a8 : w.access d.toNat (Width.bytes .b8) = true := access_prefix ad (by simp [Width.bytes])
  refine Wp.append (Wp.append (Wp.cons (Wp.store (wd := .b8) (hd mem) hx a8 (Wp.nil ?_))))
  refine copy32_wp (d := d + 8) (s := s) (fun m => eval_add (hd m) rfl) hs
    (by rw [d8]; exact access_sub ad (by omega)) as (by rw [d8]; simp only [Apart]; omega) fun mem2 copied outside => ?_
  rw [d8] at copied outside
  simp only [Width.bytes] at copied outside
  refine h mem2 ?_ ?_ ?_
  · rw [readLE_congr mem2 (store mem d.toNat 8 (qwordByte x)) _ 8 (fun k hk => outside _ (by omega)), readLE_store8]
  · apply readNode_ext
    intro k hk
    rw [copied k hk, store_outside _ _ _ _ _ (by omega)]
  · intro a ha
    rw [outside a (by omega), store_outside _ _ _ _ _ (by omega)]

/--
A loop writing entries from position o on: at each step an index word from one list and a node from another.

It ends with the entries so far followed by the words zipped with the nodes, and writes nothing else.
-/
theorem build_loop {m : Module} {w : World} {sp : Nat} {mem : Memory} {Q : Env → Memory → Prop}
    {dstE wordE nodeE : Ir.Expr} (bv : Nat) (hbv : bv ≠ 14) (env0 : Env) (cnt : UInt64) (hcnt : env0 bv = cnt)
    (A W Nd o : Nat)
    (hdst : ∀ env, (∀ k, k ≠ 14 → env k = env0 k) → (env 14).toNat < cnt.toNat →
      ∃ x, (∀ mem', eval w env mem' dstE = some x) ∧ x.toNat = A + 40 * (o + (env 14).toNat))
    (hword : ∀ env mem, (∀ k, k ≠ 14 → env k = env0 k) → (env 14).toNat < cnt.toNat →
      ∃ y, eval w env mem wordE = some y ∧ y.toNat = W + 8 * (env 14).toNat)
    (hnode : ∀ env, (∀ k, k ≠ 14 → env k = env0 k) → (env 14).toNat < cnt.toNat →
      ∃ z, (∀ mem', eval w env mem' nodeE = some z) ∧ z.toNat = Nd + 32 * (env 14).toNat)
    (aA : w.access (A + 40 * o) (40 * cnt.toNat) = true) (aW : w.access W (8 * cnt.toNat) = true)
    (aN : w.access Nd (32 * cnt.toNat) = true)
    (pW : Apart (A + 40 * o, 40 * cnt.toNat) (W, 8 * cnt.toNat))
    (pN : Apart (A + 40 * o, 40 * cnt.toNat) (Nd, 32 * cnt.toNat))
    (start : env0 14 = 0)
    (post : ∀ env' mem', (∀ k, k ≠ 14 → env' k = env0 k) →
      entriesAt mem' A (o + cnt.toNat) = entriesAt mem A o ++
        (wordsAt mem W cnt.toNat).zip (nodesAt mem Nd cnt.toNat) →
      (∀ a, ¬ (A + 40 * o ≤ a ∧ a < A + 40 * o + 40 * cnt.toNat) → mem' a = mem a) → Q env' mem') :
    Wp m w sp (Stmt.while_ (Ir.Expr.lt (Ir.Expr.var 14) (Ir.Expr.var bv))
      ([Stmt.st dstE (Ir.Expr.ld wordE)] ++ copy32 (dstE + 8) nodeE ++ [Ir.Stmt.assign ⟨14⟩ (Ir.Expr.var 14 + 1)]))
      env0 mem Q := by
  have bA := access_bound aA
  have bW := access_bound aW
  have bN := access_bound aN
  simp only [Apart] at pW pN
  refine Wp.loop (fun env mem' => (∀ k, k ≠ 14 → env k = env0 k) ∧ (env 14).toNat ≤ cnt.toNat ∧
      (∀ a, ¬ (A + 40 * o ≤ a ∧ a < A + 40 * o + 40 * (env 14).toNat) → mem' a = mem a) ∧
      entriesAt mem' A (o + (env 14).toNat) = entriesAt mem A o ++
        (wordsAt mem W (env 14).toNat).zip (nodesAt mem Nd (env 14).toNat))
    (fun env _ => cnt.toNat - (env 14).toNat)
    ⟨fun _ _ => rfl, by simp [start], fun _ _ => rfl, by simp [start, wordsAt, nodesAt]⟩ ?_
  intro env mem' ⟨same, le, frame, entries⟩
  refine ⟨_, eval_cmp .b rfl rfl, fun nz => ?_, fun z => ?_⟩
  · have lt : (env 14).toNat < cnt.toNat := by
      rw [← hcnt, ← same bv hbv]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using nz
    obtain ⟨x, hx, xv⟩ := hdst env same lt
    obtain ⟨y, hy, yv⟩ := hword env mem' same lt
    obtain ⟨z, hz, zv⟩ := hnode env same lt
    -- The word and the node read as they were, since only the entries are written.
    have wordNow : readLE mem' y.toNat 8 = readLE mem y.toNat 8 :=
      readLE_congr _ _ _ _ fun k hk => frame _ (by omega)
    have nodeNow : readNode mem' z.toNat = readNode mem z.toNat :=
      readNode_congr fun k hk => frame _ (by omega)
    have ld := eval_ld (w := w) (env := env) (mem := mem') hy (by rw [yv]; exact access_sub aW (by omega))
    rw [wordNow] at ld
    have next : (env 14 + 1).toNat = (env 14).toNat + 1 := by
      have := cnt.toNat_lt
      rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
    have xv' : x.toNat = A + 40 * o + 40 * (env 14).toNat := by omega
    refine entry_write _ hx ld hz (by rw [xv']; exact access_sub aA (by omega))
      (by rw [zv]; exact access_sub aN (by omega)) (by rw [xv, zv]; simp only [Apart]; omega)
      fun mem2 word node outside => Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨?_, ?_⟩))
    · simp only [assign, ↓reduceIte, next]
      refine ⟨fun k hk => by rw [ite_eq_right hk]; exact same k hk, by omega, fun a ha => ?_, ?_⟩
      · rw [outside a (by rw [xv]; omega), frame a (by omega)]
      · rw [show o + ((env 14).toNat + 1) = o + (env 14).toNat + 1 by omega, entriesAt_succ,
          entriesAt_congr (mem := mem') (mem' := mem2) (fun k hk => outside _ (by omega)), entries,
          show A + 40 * (o + (env 14).toNat) = x.toNat by omega, word, node, nodeNow,
          wordsAt_succ, nodesAt_succ, zip_succ _ _ _ _ (by simp [wordsAt_length, nodesAt_length]),
          List.append_assoc, ← yv, ← zv]
    · simp only [assign, ↓reduceIte, next]; omega
  · have ge : ¬ (env 14).toNat < cnt.toNat := by
      rw [← hcnt, ← same bv hbv]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using z
    have all : (env 14).toNat = cnt.toNat := by omega
    rw [all] at entries frame
    exact post env mem' same entries frame

/-- The deepest level among some entries, one more: the deeper of the two. -/
theorem deepestOf_succ (mem : Memory) (a n : Nat) :
    deepestOf (entriesAt mem a (n + 1)) = max (deepestOf (entriesAt mem a n)) (Nat.log2 (readLE mem (a + 40 * n) 8).toNat) := by
  rw [entriesAt_succ, deepestOf_append]; rfl

/-- The loop finding the deepest level: it ends with the deepest level of the node set, and writes nothing. -/
theorem deepest_loop {m : Module} {w : World} (hl : m.fns.lookup "ssz_branch_level" = some Level.fn) {sp : Nat}
    (room : w.stackLo + 32 ≤ sp) {mem : Memory} (env0 : Env) (cur size : UInt64) (e11 : env0 11 = cur)
    (e13 : env0 13 = size) (e14 : env0 14 = 0) (e15 : env0 15 = 0)
    (ac : w.access cur.toNat (40 * size.toNat) = true) {Q : Env → Memory → Prop}
    (post : ∀ env', (∀ k, k ≠ 14 → k ≠ 15 → k ≠ 16 → env' k = env0 k) →
      (env' 15).toNat = deepestOf (entriesAt mem cur.toNat size.toNat) → Q env' mem) :
    Wp m w sp (Stmt.while_ (Ir.Expr.lt VerifyMultiproof.i VerifyMultiproof.size)
      [Stmt.callInto VerifyMultiproof.t "ssz_branch_level" [Ir.Expr.ld (VerifyMultiproof.cur + 40 * VerifyMultiproof.i)],
        Stmt.when (Ir.Expr.lt VerifyMultiproof.depth VerifyMultiproof.t) [VerifyMultiproof.depth ::= VerifyMultiproof.t],
        VerifyMultiproof.i ::= VerifyMultiproof.i + 1]) env0 mem Q := by
  refine Wp.loop (fun env mem' => mem' = mem ∧ (∀ k, k ≠ 14 → k ≠ 15 → k ≠ 16 → env k = env0 k) ∧
      (env 14).toNat ≤ size.toNat ∧ (env 15).toNat = deepestOf (entriesAt mem cur.toNat (env 14).toNat))
    (fun env _ => size.toNat - (env 14).toNat)
    ⟨rfl, fun _ _ _ _ => rfl, by simp [e14], by simp [e14, e15, entriesAt, deepestOf]⟩ ?_
  intro env mem' ⟨same, keep, le, deep⟩
  subst same
  have f11 : env 11 = cur := by rw [keep 11 (by decide) (by decide) (by decide), e11]
  have f13 : env 13 = size := by rw [keep 13 (by decide) (by decide) (by decide), e13]
  refine ⟨_, eval_cmp .b rfl rfl, fun nz => ?_, fun z => ?_⟩
  · have lt : (env 14).toNat < size.toNat := by rw [← f13]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using nz
    obtain ⟨addr, eacc⟩ := entry_addr ac (env 14) lt
    have word := eval_ld (w := w) (env := env) (mem := mem') (eval_add (a := Ir.Expr.var 11)
      (b := 40 * Ir.Expr.var 14) rfl (eval_mul rfl rfl)) (by rw [f11, addr]; exact access_prefix eacc (by omega))
    rw [f11, addr] at word
    generalize hx : readLE mem' (cur.toNat + 40 * (env 14).toNat) 8 = x at word
    have lv := level_calls (w := w) hl (sp := sp) room x mem'
    have small := log2_lt_64 x
    have next : (env 14 + 1).toNat = (env 14).toNat + 1 := by
      have := size.toNat_lt
      rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
    have grow := deepestOf_succ mem' cur.toNat (env 14).toNat
    rw [hx] at grow
    have lvTo : (Nat.log2 x.toNat).toUInt64.toNat = Nat.log2 x.toNat := toNat_ofNat_of_lt _ (by omega)
    refine Wp.cons (Wp.call (values := [x]) (by simp only [List.mapM_cons, List.mapM_nil, word]; rfl)
      ⟨_, mem', lv, ?_⟩)
    refine Wp.cons (Wp.ite (eval_lt rfl rfl) (fun deeper => ?_) (fun shallower => ?_))
    · have d' : (env 15).toNat < Nat.log2 x.toNat := by
        simp only [assign, ↓reduceIte, Nat.reduceEqDiff, lvTo] at deeper
        by_cases h : (env 15).toNat < x.toNat.log2
        · exact h
        · rw [ite_eq_right h] at deeper; exact absurd rfl deeper
      refine Wp.cons (Wp.set rfl (Wp.nil (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨⟨rfl, ?_, ?_, ?_⟩, ?_⟩)))))
      · intro k h14 h15 h16
        simp only [assign, ite_eq_right h14, ite_eq_right h15, ite_eq_right h16]
        exact keep k h14 h15 h16
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]; omega
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next, lvTo, grow, ← deep]; omega
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]; omega
    · have d' : ¬ (env 15).toNat < Nat.log2 x.toNat := by
        simp only [assign, ↓reduceIte, Nat.reduceEqDiff, lvTo] at shallower
        intro h; rw [ite_eq_left h] at shallower; exact absurd shallower (by decide)
      refine Wp.skip (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨⟨rfl, ?_, ?_, ?_⟩, ?_⟩)))
      · intro k h14 h15 h16
        simp only [assign, ite_eq_right h14, ite_eq_right h16]
        exact keep k h14 h15 h16
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]; omega
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next, grow, ← deep]; omega
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]; omega
  · have ge : ¬ (env 14).toNat < size.toNat := by rw [← f13]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using z
    rw [show (env 14).toNat = size.toNat by omega] at deep
    exact post env keep deep

end EthLib.Consensus.Ssz.Native.Driver.BranchProof
