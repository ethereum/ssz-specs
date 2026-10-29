import SszNative.Proofs.Driver.Branch.Claims

/-!
The compiled helper indices are the specification's.

The claims' paths are written one after the other, then the siblings that are no path node, then those candidates
again, distinct and largest first.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.BranchProof

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm

/-- A path is as long as its index's level. -/
theorem pathOf_length (c : Nat) : (pathOf c).length = Nat.log2 c := by
  simp [pathOf]

/-- The path of a 64-bit index holds at most 63 nodes. -/
theorem pathOf_length_le (c : UInt64) : (pathOf c.toNat).length ≤ 63 := by
  rw [pathOf_length]; have := log2_lt_64 c; omega

/-- The paths of words read from memory hold at most 63 nodes per word. -/
theorem flatMap_pathOf_length (mem : Memory) (a : Nat) :
    ∀ i, ((wordsAt mem a i).flatMap pathOf).length ≤ 63 * i
  | 0 => by simp [wordsAt]
  | i + 1 => by
    rw [wordsAt_succ, List.flatMap_append, List.length_append]
    have := flatMap_pathOf_length mem a i
    have := pathOf_length_le (readLE mem (a + 8 * i) 8)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    omega

/-- The path walk: the paths of the claims so far, then part of the current claim's path, written in order. -/
private def PathInv (mem : Memory) (indices count paths : UInt64) (env : Env) (mem' : Memory) : Prop :=
  env 0 = indices ∧ env 1 = count ∧ env 2 = paths ∧ (env 3).toNat ≤ count.toNat ∧
    (∀ a, ¬ (paths.toNat ≤ a ∧ a < paths.toNat + 8 * (env 5).toNat) → mem' a = mem a) ∧
    wordsAt mem' paths.toNat (env 5).toNat = (wordsAt mem indices.toNat (env 3).toNat).flatMap pathOf

/-- A call of the path walk writes the claims' paths one after the other and returns their node count. -/
theorem collect_paths_calls {m : Module} {w : World} (hc : m.fns.lookup "ssz_branch_paths" = some CollectPaths.fn)
    {sp : Nat} (room : w.stackLo + 80 ≤ sp) (indices count paths : UInt64) (mem : Memory)
    (ai : w.access indices.toNat (8 * count.toNat) = true) (ap : w.access paths.toNat (512 * count.toNat) = true)
    (apart : Apart (paths.toNat, 512 * count.toNat) (indices.toNat, 8 * count.toNat)) :
    ∃ mem', Calls m w "ssz_branch_paths" sp [indices, count, paths] mem
        ((wordsAt mem indices.toNat count.toNat).flatMap pathOf).length.toUInt64 mem' ∧
      wordsAt mem' paths.toNat ((wordsAt mem indices.toNat count.toNat).flatMap pathOf).length =
        (wordsAt mem indices.toNat count.toNat).flatMap pathOf ∧
      ∀ a, ¬ (paths.toNat ≤ a ∧ a < paths.toNat + 512 * count.toNat) → mem' a = mem a := by
  have frameSize : CollectPaths.fn.frame = 9 := by decide
  let P := (wordsAt mem indices.toNat count.toNat).flatMap pathOf
  have bi := access_bound ai
  have bp := access_bound ap
  suffices body : Wp m w (sp - 80) CollectPaths.fn.body (entryEnv [indices, count, paths]) mem
      fun env mem' => ∃ r, eval w env mem' (Ir.Expr.var 5) = some r ∧ (r = P.length.toUInt64 ∧
        wordsAt mem' paths.toNat P.length = P ∧
        ∀ a, ¬ (paths.toNat ≤ a ∧ a < paths.toNat + 512 * count.toNat) → mem' a = mem a) by
    obtain ⟨r, mem', call, hr, words, frame⟩ := Calls.of_wp (Q := fun r mem' => r = P.length.toUInt64 ∧
        wordsAt mem' paths.toNat P.length = P ∧
        ∀ a, ¬ (paths.toNat ≤ a ∧ a < paths.toNat + 512 * count.toNat) → mem' a = mem a)
      (w := w) (sp := sp) (args := [indices, count, paths]) (mem := mem) hc (by omega) rfl
      (by rw [frameSize]; exact body)
    rw [hr] at call
    exact ⟨mem', call, words, frame⟩
  simp only [CollectPaths.fn]
  refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons ?_))))
  refine Wp.loop (PathInv mem indices count paths) (fun env _ => count.toNat - (env 3).toNat)
    ⟨by simp [assign, entryEnv], by simp [assign, entryEnv], by simp [assign, entryEnv], by simp [assign],
      fun _ _ => rfl, by simp [assign, wordsAt]⟩ ?_
  intro env mem' ⟨e0, e1, e2, le, frame, words⟩
  refine ⟨_, eval_cmp .b rfl rfl, fun nz => ?_, fun z => ?_⟩
  · have lt : (env 3).toNat < count.toNat := by rw [← e1]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using nz
    obtain ⟨addr, wacc⟩ := word_addr ai (env 3) lt
    have count_n : (env 5).toNat = ((wordsAt mem indices.toNat (env 3).toNat).flatMap pathOf).length := by
      rw [← words, wordsAt_length]
    have bound_n := flatMap_pathOf_length mem indices.toNat (env 3).toNat
    -- The claim is read where the paths do not reach.
    have unchanged : readLE mem' (indices.toNat + 8 * (env 3).toNat) 8 =
        readLE mem (indices.toNat + 8 * (env 3).toNat) 8 :=
      readLE_congr _ _ _ _ fun k hk => frame _ (by simp only [Apart] at apart; omega)
    have key := eval_ld (w := w) (env := env) (mem := mem') (eval_add (a := Ir.Expr.var 0)
      (b := 8 * Ir.Expr.var 3) rfl (eval_mul rfl rfl)) (by rw [e0, addr]; exact wacc)
    rw [e0, addr, unchanged] at key
    generalize hc : readLE mem (indices.toNat + 8 * (env 3).toNat) 8 = c at key
    have pathLen := pathOf_length_le c
    refine Wp.cons (Wp.set key (Wp.cons ?_))
    -- The inner walk: the nodes written so far, followed by the path still ahead, make the claim's path.
    refine Wp.loop (fun env' mem'' => env' 0 = indices ∧ env' 1 = count ∧ env' 2 = paths ∧ env' 3 = env 3 ∧
        (∀ a, ¬ (paths.toNat ≤ a ∧ a < paths.toNat + 8 * (env' 5).toNat) → mem'' a = mem a) ∧
        ∃ written, wordsAt mem'' paths.toNat (env' 5).toNat =
          (wordsAt mem indices.toNat (env 3).toNat).flatMap pathOf ++ written ∧
          written ++ pathOf (env' 4).toNat = pathOf c.toNat)
      (fun env' _ => (env' 4).toNat)
      ⟨by simp [assign, e0], by simp [assign, e1], by simp [assign, e2], by simp [assign], fun a ha => frame a (by simpa [assign] using ha),
        [], by simp [assign, words], by simp [assign]⟩ ?_
    intro env' mem'' ⟨f0, f1, f2, f3, frame', written, wr, split⟩
    refine ⟨_, eval_cmp .b rfl rfl, fun nz => ?_, fun z => ?_⟩
    · -- One more node of the path is written, and the walk moves to its parent.
      have big : 1 < (env' 4).toNat := by simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using nz
      have cons := pathOf_cons _ big
      have lenW : (env' 5).toNat = ((wordsAt mem indices.toNat (env 3).toNat).flatMap pathOf).length +
          written.length := by rw [← List.length_append, ← wr, wordsAt_length]
      have lenSplit := congrArg List.length split
      rw [List.length_append, cons, List.length_cons] at lenSplit
      have small : (env' 5).toNat + 1 ≤ 63 * count.toNat := by omega
      have addrN : (env' 2 + 8 * env' 5).toNat = paths.toNat + 8 * (env' 5).toNat := by
        rw [f2, toNat_addr _ _ _ (by simp; omega)]; simp
      have next : (env' 5 + 1).toNat = (env' 5).toNat + 1 := by
        rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
      refine Wp.cons (Wp.store (eval_add rfl (eval_mul rfl rfl)) rfl
        (by rw [addrN]; exact access_sub ap (by simp [Width.bytes]; omega))
        (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.cons (Wp.set (eval_shr1 rfl) (Wp.nil ⟨?_, ?_⟩))))))
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, toNat_shr_one, next, addrN, Width.bytes]
        refine ⟨f0, f1, f2, f3, fun a ha => ?_, written ++ [(env' 4).toNat], ?_, ?_⟩
        · rw [store_outside _ _ _ _ _ (by omega)]; exact frame' a (by omega)
        · rw [wordsAt_store_end, wr, List.append_assoc]
        · rw [List.append_assoc, List.singleton_append, ← cons, split]
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, toNat_shr_one]; omega
    · -- At the root the claim's whole path is written, and the next claim follows.
      have small : ¬ 1 < (env' 4).toNat := by simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using z
      rw [pathOf_small _ (by omega), List.append_nil] at split
      have next : (env' 3 + 1).toNat = (env' 3).toNat + 1 := by
        have := count.toNat_lt
        rw [f3, toNat_add_of_lt _ _ (by simp; omega)]; simp
      refine Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)) <;>
        simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]
      · exact f0
      · exact f1
      · exact f2
      · rw [f3]; omega
      · exact frame'
      · rw [wr, split, f3, wordsAt_succ, List.flatMap_append, hc]; simp
      · rw [f3]; omega
  · -- Every claim's path is written.
    have done : ¬ (env 3).toNat < count.toNat := by rw [← e1]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using z
    have all : (env 3).toNat = count.toNat := by omega
    rw [all] at words
    have len : (env 5).toNat = P.length := by
      show _ = ((wordsAt mem indices.toNat count.toNat).flatMap pathOf).length
      rw [← words, wordsAt_length]
    have bound := flatMap_pathOf_length mem indices.toNat count.toNat
    have hP : P.length = ((wordsAt mem indices.toNat count.toNat).flatMap pathOf).length := rfl
    refine Wp.nil ⟨env 5, rfl, ?_, by rw [← len, words], fun a ha => frame a (by omega)⟩
    apply UInt64.toNat_inj.mp
    rw [len, toNat_ofNat_of_lt _ (by have := count.toNat_lt; omega)]

/-- The candidate walk: the candidates among the path nodes so far, written in order. -/
private def CandInv (mem : Memory) (P : List Nat) (paths count out : UInt64) (env : Env) (mem' : Memory) : Prop :=
  env 0 = paths ∧ env 1 = count ∧ env 2 = out ∧ (env 3).toNat ≤ count.toNat ∧
    (∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 8 * (env 6).toNat) → mem' a = mem a) ∧
    wordsAt mem' out.toNat (env 6).toNat = ((wordsAt mem paths.toNat (env 3).toNat).map fun p => p ^^^ 1).filter
      fun s => s ∉ P

/-- A call of the candidate walk writes the candidates for helper indices in path order and returns their count. -/
theorem candidates_calls {m : Module} {w : World} (hc : m.fns.lookup "ssz_branch_candidates" = some Candidates.fn)
    (hf : m.fns.lookup "ssz_branch_find" = some Find.fn) {sp : Nat} (room : w.stackLo + 176 ≤ sp)
    (paths count out : UInt64) (mem : Memory)
    (ap : w.access paths.toNat (8 * count.toNat) = true) (ao : w.access out.toNat (8 * count.toNat) = true)
    (apart : Apart (out.toNat, 8 * count.toNat) (paths.toNat, 8 * count.toNat)) :
    ∃ mem', Calls m w "ssz_branch_candidates" sp [paths, count, out] mem
        (candidatesOf (wordsAt mem paths.toNat count.toNat)).length.toUInt64 mem' ∧
      wordsAt mem' out.toNat (candidatesOf (wordsAt mem paths.toNat count.toNat)).length =
        candidatesOf (wordsAt mem paths.toNat count.toNat) ∧
      ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 8 * count.toNat) → mem' a = mem a := by
  have frameSize : Candidates.fn.frame = 11 := by decide
  generalize hP : wordsAt mem paths.toNat count.toNat = P
  have bp := access_bound ap
  have bo := access_bound ao
  suffices body : Wp m w (sp - 96) Candidates.fn.body (entryEnv [paths, count, out]) mem
      fun env mem' => ∃ r, eval w env mem' (Ir.Expr.var 6) = some r ∧ (r = (candidatesOf P).length.toUInt64 ∧
        wordsAt mem' out.toNat (candidatesOf P).length = candidatesOf P ∧
        ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 8 * count.toNat) → mem' a = mem a) by
    obtain ⟨r, mem', call, hr, words, frame⟩ := Calls.of_wp (Q := fun r mem' =>
        r = (candidatesOf P).length.toUInt64 ∧ wordsAt mem' out.toNat (candidatesOf P).length = candidatesOf P ∧
        ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 8 * count.toNat) → mem' a = mem a)
      (w := w) (sp := sp) (args := [paths, count, out]) (mem := mem) hc (by omega) rfl
      (by rw [frameSize]; exact body)
    rw [hr] at call
    exact ⟨mem', call, words, frame⟩
  have deep : w.stackLo + 80 ≤ sp - 96 := by omega
  simp only [Candidates.fn]
  refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons ?_))))
  refine Wp.loop (CandInv mem P paths count out) (fun env _ => count.toNat - (env 3).toNat)
    ⟨by simp [assign, entryEnv], by simp [assign, entryEnv], by simp [assign, entryEnv], by simp [assign],
      fun _ _ => rfl, by simp [assign, wordsAt]⟩ ?_
  intro env mem' ⟨e0, e1, e2, le, frame, words⟩
  refine ⟨_, eval_cmp .b rfl rfl, fun nz => ?_, fun z => ?_⟩
  · have lt : (env 3).toNat < count.toNat := by rw [← e1]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using nz
    obtain ⟨addr, wacc⟩ := word_addr ap (env 3) lt
    have count_n : (env 6).toNat = (((wordsAt mem paths.toNat (env 3).toNat).map fun p => p ^^^ 1).filter
        fun s => s ∉ P).length := by rw [← words, wordsAt_length]
    have n_le : (env 6).toNat ≤ (env 3).toNat := by
      rw [count_n]
      exact Nat.le_trans (List.length_filter_le _ _) (by simp [wordsAt_length])
    -- The path nodes are read where the candidates do not reach.
    have same : ∀ k < 8 * count.toNat, mem' (paths.toNat + k) = mem (paths.toNat + k) :=
      fun k hk => frame _ (by simp only [Apart] at apart; omega)
    have pathsNow : wordsAt mem' paths.toNat count.toNat = P := by rw [← hP]; exact wordsAt_congr same
    have node := eval_ld (w := w) (env := env) (mem := mem') (eval_add (a := Ir.Expr.var 0)
      (b := 8 * Ir.Expr.var 3) rfl (eval_mul rfl rfl)) (by rw [e0, addr]; exact wacc)
    rw [e0, addr, readLE_congr mem' mem _ 8 (fun k hk => by rw [Nat.add_assoc]; exact same _ (by omega))] at node
    generalize hp : readLE mem (paths.toNat + 8 * (env 3).toNat) 8 = p at node
    have call := find_words hf deep ap count (Nat.le_refl _) (p ^^^ 1) mem'
    rw [← e0, ← e1] at call
    refine Wp.cons (Wp.set (eval_xor node rfl) (Wp.cons (Wp.call (values := [env 0, 8, env 1, p ^^^ 1]) rfl
      ⟨_, mem', call, ?_⟩)))
    have next : (env 3 + 1).toNat = (env 3).toNat + 1 := by
      have := count.toNat_lt
      rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
    have sib : (p ^^^ 1).toNat = p.toNat ^^^ 1 := by simp
    -- The prefix of path nodes grows by this one.
    have grow : ((wordsAt mem paths.toNat ((env 3).toNat + 1)).map fun p => p ^^^ 1).filter (fun s => s ∉ P) =
        (((wordsAt mem paths.toNat (env 3).toNat).map fun p => p ^^^ 1).filter fun s => s ∉ P) ++
          ([p.toNat ^^^ 1].filter fun s => s ∉ P) := by
      rw [wordsAt_succ, hp, List.map_append, List.filter_append]; rfl
    refine Wp.cons (Wp.ite (eval_eq rfl rfl) (fun fresh => ?_) (fun seen => ?_))
    · -- A sibling off every path is a candidate, written next.
      have off : (p ^^^ 1).toNat ∉ P := by
        have : (firstAt (big32 mem' (env 0).toNat 8) (p ^^^ 1) (env 1).toNat).toUInt64 = env 1 := by
          by_cases h : (firstAt (big32 mem' (env 0).toNat 8) (p ^^^ 1) (env 1).toNat).toUInt64 = env 1
          · exact h
          · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, ite_eq_right h] at fresh; exact absurd rfl fresh
        rw [e0, e1, firstAt_words_eq_count, pathsNow] at this
        exact this
      have addrN : (env 2 + 8 * env 6).toNat = out.toNat + 8 * (env 6).toNat := by
        rw [e2, toNat_addr _ _ _ (by simp; omega)]; simp
      have nextN : (env 6 + 1).toNat = (env 6).toNat + 1 := by
        have := count.toNat_lt
        rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
      refine Wp.cons (Wp.store (eval_add rfl (eval_mul rfl rfl)) rfl ?_ (Wp.cons (Wp.set (eval_add rfl rfl)
        (Wp.nil (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨?_, ?_⟩)))))))
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff]
        rw [addrN]; exact access_sub ao (by simp [Width.bytes]; omega)
      · simp only [CandInv, assign, ↓reduceIte, Nat.reduceEqDiff, next, nextN, addrN, Width.bytes]
        refine ⟨e0, e1, e2, by omega, fun a ha => ?_, ?_⟩
        · rw [store_outside _ _ _ _ _ (by omega)]; exact frame a (by omega)
        · rw [wordsAt_store_end, words, grow, sib]
          simp only [List.filter_cons, List.filter_nil]
          rw [sib] at off
          simp [off]
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]; omega
    · -- A sibling on some path is no candidate.
      have on : (p ^^^ 1).toNat ∈ P := by
        have : ¬ (firstAt (big32 mem' (env 0).toNat 8) (p ^^^ 1) (env 1).toNat).toUInt64 = env 1 := by
          intro h
          simp only [assign, ↓reduceIte, Nat.reduceEqDiff, ite_eq_left h] at seen
          exact absurd seen (by decide)
        rw [e0, e1, firstAt_words_eq_count, pathsNow] at this
        exact Classical.not_not.mp this
      refine Wp.skip (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨?_, ?_⟩)))
      · simp only [CandInv, assign, ↓reduceIte, Nat.reduceEqDiff, next]
        refine ⟨e0, e1, e2, by omega, frame, ?_⟩
        rw [words, grow]
        rw [sib] at on
        simp [on]
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]; omega
  · -- Every path node was read.
    have done : ¬ (env 3).toNat < count.toNat := by rw [← e1]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using z
    rw [show (env 3).toNat = count.toNat by omega, hP] at words
    have len : (env 6).toNat = (candidatesOf P).length := by
      show _ = (((P.map fun p => p ^^^ 1).filter fun s => s ∉ P)).length
      rw [← words, wordsAt_length]
    have bound : (candidatesOf P).length ≤ count.toNat :=
      Nat.le_trans (List.length_filter_le _ _) (by rw [← hP]; simp [wordsAt_length])
    refine Wp.nil ⟨env 6, rfl, ?_, by rw [← len]; exact words, fun a ha => frame a (by omega)⟩
    apply UInt64.toNat_inj.mp
    rw [len, toNat_ofNat_of_lt _ (by have := count.toNat_lt; omega)]

end EthLib.Consensus.Ssz.Native.Driver.BranchProof
