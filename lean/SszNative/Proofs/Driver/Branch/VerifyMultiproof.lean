import SszNative.Proofs.Driver.Branch.MultiBuild
import SszNative.Proofs.Driver.Branch.Bridge

/-!
The compiled multiproof verifier answers what the Lean verifier answers.

It checks the counts, computes the helper indices, writes the node set, finds the deepest level, folds level by level,
and compares the node at the root's index with the expected root.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.BranchProof

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm

/-- Memories agreeing on some nodes' bytes read the same nodes. -/
theorem nodesAt_congr {mem mem' : Memory} {a n : Nat} (h : ∀ k < 32 * n, mem' (a + k) = mem (a + k)) :
    nodesAt mem' a n = nodesAt mem a n := by
  simp only [nodesAt]
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  exact readNode_congr fun k hk => by rw [Nat.add_assoc]; exact h _ (by omega)

/-- A level's first pass refuses only for a missing side of a pair. -/
theorem levelParents_error (d : Nat) (N : List (Nat × ByteArray)) :
    ∀ L {e}, levelParents d N L = .error e → e = .proofIncomplete
  | [], _, h => by cases h
  | (index, node) :: rest, e, h => by
    simp only [levelParents] at h
    split at h
    · exact levelParents_error d N rest h
    split at h
    · split at h
      · cases r : levelParents d N rest with
        | error e' => rw [r] at h; cases h; exact levelParents_error d N rest r
        | ok _ => rw [r] at h; cases h
      · cases h; rfl
    split at h
    · cases h; rfl
    · exact levelParents_error d N rest h

/-- A fold refuses only for a missing side of a pair, or a missing root. -/
theorem foldToRoot_error : ∀ (d : Nat) (N : List (Nat × ByteArray)) {e}, foldToRoot d N = .error e →
    e = .proofIncomplete
  | 0, N, e, h => by
    simp only [foldToRoot] at h
    split at h
    · cases h
    · cases h; rfl
  | d + 1, N, e, h => by
    cases r : levelParents (d + 1) N N with
    | error e' => rw [foldToRoot_succ_error d N r] at h; cases h; exact levelParents_error _ _ _ r
    | ok ps => rw [foldToRoot_succ_ok d N ps r] at h; exact foldToRoot_error d _ h

/-- The scratch bytes a multiproof job of n indices and p proof nodes needs. -/
def multiScratch (n p : Nat) : Nat := 8 + 1536 * n + 160 * (n + p)

/-- A multiproof job in memory: its eight words, the regions they name usable, the scratch area free and apart. -/
structure MultiJob (w : World) (free : Nat → Prop) (mem : Memory)
    (job leaves leafCount proof proofCount indices count root scratch : UInt64) : Prop where
  /-- The job's words are usable. -/
  words : w.access job.toNat 64 = true
  /-- The leaves' address. -/
  w0 : readLE mem job.toNat 8 = leaves
  /-- The number of leaves. -/
  w1 : readLE mem (job.toNat + 8) 8 = leafCount
  /-- The proof nodes' address. -/
  w2 : readLE mem (job.toNat + 16) 8 = proof
  /-- The number of proof nodes. -/
  w3 : readLE mem (job.toNat + 24) 8 = proofCount
  /-- The indices' address. -/
  w4 : readLE mem (job.toNat + 32) 8 = indices
  /-- The number of indices. -/
  w5 : readLE mem (job.toNat + 40) 8 = count
  /-- The root's address. -/
  w6 : readLE mem (job.toNat + 48) 8 = root
  /-- The scratch area's address. -/
  w7 : readLE mem (job.toNat + 56) 8 = scratch
  /-- The leaves are usable. -/
  leavesOk : w.access leaves.toNat (32 * leafCount.toNat) = true
  /-- The proof nodes are usable. -/
  proofOk : w.access proof.toNat (32 * proofCount.toNat) = true
  /-- The indices are usable. -/
  indicesOk : w.access indices.toNat (8 * count.toNat) = true
  /-- The root is usable. -/
  rootOk : w.access root.toNat 32 = true
  /-- The scratch area is usable. -/
  scratchOk : w.access scratch.toNat (multiScratch count.toNat proofCount.toNat) = true
  /-- The scratch area is free memory. -/
  scratchFree : ∀ k < multiScratch count.toNat proofCount.toNat, free (scratch.toNat + k)
  /-- The root is free memory. -/
  rootFree : ∀ k < 32, free (root.toNat + k)
  /-- The job is free memory. -/
  jobFree : ∀ k < 64, free (job.toNat + k)
  /-- The scratch area misses the leaves. -/
  leavesApart : Apart (scratch.toNat, multiScratch count.toNat proofCount.toNat) (leaves.toNat, 32 * leafCount.toNat)
  /-- The scratch area misses the proof nodes. -/
  proofApart : Apart (scratch.toNat, multiScratch count.toNat proofCount.toNat) (proof.toNat, 32 * proofCount.toNat)
  /-- The scratch area misses the indices. -/
  indicesApart : Apart (scratch.toNat, multiScratch count.toNat proofCount.toNat) (indices.toNat, 8 * count.toNat)
  /-- The scratch area misses the root. -/
  rootApart : Apart (scratch.toNat, multiScratch count.toNat proofCount.toNat) (root.toNat, 32)
  /-- The scratch area misses the job. -/
  jobApart : Apart (scratch.toNat, multiScratch count.toNat proofCount.toNat) (job.toNat, 64)

/-- The functions of the multiproof verifier, each under its exported name. -/
structure MultiFns (m : Module) : Prop where
  /-- The helper indices and their parts. -/
  helpers : HelperFns m
  /-- The level of an index. -/
  level : m.fns.lookup "ssz_branch_level" = some Level.fn
  /-- The node comparison. -/
  same : m.fns.lookup "ssz_branch_same" = some Same.fn
  /-- The first fold pass. -/
  parents : m.fns.lookup "ssz_branch_fold_parents" = some FoldParents.fn
  /-- The second fold pass. -/
  kept : m.fns.lookup "ssz_branch_fold_kept" = some FoldKept.fn
  /-- The verifier. -/
  verify : m.fns.lookup "ssz_verify_multiproof" = some VerifyMultiproof.fn

set_option maxHeartbeats 4000000 in
/--
The compiled multiproof verifier answers what the Lean verifier answers on the leaves, proof nodes, indices and root
its job names.

It changes no free memory outside its scratch area, and keeps the hashing context.
-/
theorem verify_multiproof_calls {m : Module} {w : World} {ctx : UInt64} {ready : Memory → Prop}
    {free : Nat → Prop} {room : Nat} (fns : MultiFns m) (hash : PairHashing m w ctx ready free room) {sp : Nat}
    (deep : w.stackLo + 512 + room ≤ sp) {mem : Memory} (rd : ready mem)
    {job leaves leafCount proof proofCount indices count root scratch : UInt64}
    (j : MultiJob w free mem job leaves leafCount proof proofCount indices count root scratch) :
    ∃ mem', Calls m w "ssz_verify_multiproof" sp [job, ctx] mem
        (answerCode (verifyMerkleMultiproof (nodesAt mem leaves.toNat leafCount.toNat)
          (nodesAt mem proof.toNat proofCount.toNat) (wordsAt mem indices.toNat count.toNat)
          (readNode mem root.toNat))) mem' ∧
      ready mem' ∧
      ∀ a, free a → ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + multiScratch count.toNat proofCount.toNat) →
        mem' a = mem a := by
  have frameSize : VerifyMultiproof.fn.frame = 25 := by decide
  let verdict := answerCode (verifyMerkleMultiproof (nodesAt mem leaves.toNat leafCount.toNat)
    (nodesAt mem proof.toNat proofCount.toNat) (wordsAt mem indices.toNat count.toNat) (readNode mem root.toNat))
  let S := multiScratch count.toNat proofCount.toNat
  suffices body : Wp m w (sp - 208) VerifyMultiproof.fn.body (entryEnv [job, ctx]) mem
      fun env mem' => ∃ r, eval w env mem' (Ir.Expr.var 9) = some r ∧ (r = verdict ∧ ready mem' ∧
        ∀ a, free a → ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + S) → mem' a = mem a) by
    obtain ⟨r, mem', call, hr, rd', fr⟩ := Calls.of_wp (Q := fun r mem' => r = verdict ∧ ready mem' ∧
        ∀ a, free a → ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + S) → mem' a = mem a)
      (w := w) (sp := sp) (args := [job, ctx]) (mem := mem) fns.verify (by omega) rfl
      (by rw [frameSize]; exact body)
    rw [hr] at call
    exact ⟨mem', call, rd', fr⟩
  simp only [VerifyMultiproof.fn]
  have bj := access_bound j.words
  have bS := access_bound j.scratchOk
  have sizes : ∀ n ∈ nodesAt mem leaves.toNat leafCount.toNat ++ nodesAt mem proof.toNat proofCount.toNat,
      n.size = 32 := by
    intro n hn
    simp only [List.mem_append, nodesAt, List.mem_map] at hn
    rcases hn with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact readNode_size _ _
  -- The job's words.
  refine Wp.cons (Wp.set (eval_ld (x := job) rfl (by simpa using access_sub (k := 0) (j := 8) j.words (by omega)))
    (Wp.cons (Wp.set (eval_ld_off (x := job) (n := 8) rfl (access_sub j.words (by simp)))
    (Wp.cons (Wp.set (eval_ld_off (x := job) (n := 16) rfl (access_sub j.words (by simp)))
    (Wp.cons (Wp.set (eval_ld_off (x := job) (n := 24) rfl (access_sub j.words (by simp)))
    (Wp.cons (Wp.set (eval_ld_off (x := job) (n := 32) rfl (access_sub j.words (by simp)))
    (Wp.cons (Wp.set (eval_ld_off (x := job) (n := 40) rfl (access_sub j.words (by simp)))
    (Wp.cons (Wp.set (eval_ld_off (x := job) (n := 56) rfl (access_sub j.words (by simp))) ?_)))))))))))))
  refine Wp.of_env (fun env => env 0 = job ∧ env 1 = ctx ∧ env 2 = leaves ∧ env 3 = leafCount ∧ env 4 = proof ∧
      env 5 = proofCount ∧ env 6 = indices ∧ env 7 = count ∧ env 8 = scratch)
    (by simp only [assign, ↓reduceIte, Nat.reduceEqDiff, entryEnv, UInt64.reduceToNat]
        exact ⟨rfl, rfl, j.w0, j.w1, j.w2, j.w3, j.w4, j.w5, j.w7⟩) ?_
  intro env ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8⟩
  refine Wp.cons (Wp.ite (eval_ne rfl rfl) (fun differ => ?_) (fun same => ?_))
  · -- Leaves that do not pair one to one with the indices.
    have ne : leafCount ≠ count := by
      intro h; simp only [e3, e7, h] at differ; exact differ (by simp)
    refine Wp.cons (Wp.set rfl (Wp.nil (Wp.nil ⟨_, rfl, ?_, rd, fun _ _ _ => rfl⟩)))
    simp only [verdict, verifyMerkleMultiproof_eq _ _ _ _ sizes, nodesAt_length, wordsAt_length]
    rw [ite_eq_left (fun h => ne (UInt64.toNat_inj.mp h))]
    simp [assign, answerCode]
  have eqc : leafCount = count := by
    by_cases h : leafCount = count
    · exact h
    · simp only [e3, e7, ite_eq_right h] at same; exact absurd same (by decide)
  -- The helper indices, into the scratch area.
  let L := wordsAt mem indices.toNat count.toNat
  have bI := access_bound j.indicesOk
  have pI := j.indicesApart
  have pL := j.leavesApart
  have pP := j.proofApart
  have pR := j.rootApart
  have pJ := j.jobApart
  simp only [Apart, multiScratch] at pI pL pP pR pJ bS
  have p8 : (scratch + 8).toNat = scratch.toNat + 8 := by rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
  have m1 : (1024 * count).toNat = 1024 * count.toNat := by
    rw [toNat_mul_of_lt _ _ (by simp; omega)]; simp
  have hAddr : (scratch + 8 + 1024 * count).toNat = scratch.toNat + 8 + 1024 * count.toNat := by
    rw [toNat_add_of_lt _ _ (by rw [p8, m1]; omega), p8, m1]
  have sub : ∀ k len, k + len ≤ S → w.access (scratch.toNat + k) len = true :=
    fun k len h => access_sub j.scratchOk h
  have sS : S = 8 + 1536 * count.toNat + 160 * (count.toNat + proofCount.toNat) := rfl
  have scratchFree' : ∀ a, scratch.toNat ≤ a → a < scratch.toNat + S → free a := fun a h1 h2 => by
    have := j.scratchFree (a - scratch.toNat) (by show a - scratch.toNat < S; omega)
    rwa [show scratch.toNat + (a - scratch.toNat) = a by omega] at this
  obtain ⟨mem1, callH, okH, frameH⟩ := helper_indices_calls (w := w) fns.helpers (sp := sp - 208) (by omega)
    indices count (scratch + 8) (scratch + 8 + 1024 * count) scratch mem j.indicesOk
    (by rw [p8]; exact sub 8 _ (by omega))
    (by rw [hAddr, Nat.add_assoc]; exact sub _ _ (by omega))
    (by simpa using sub 0 8 (by omega))
    (by rw [p8]; simp only [Apart]; omega) (by rw [hAddr, p8]; simp only [Apart]; omega)
    (by rw [hAddr]; simp only [Apart]; omega)
  rw [p8, hAddr] at frameH
  have frame1 : ∀ a, ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + S) → mem1 a = mem a := fun a ha =>
    frameH a (by omega) (by omega) (by omega)
  have rd1 : ready mem1 := hash.ready_frame _ _ rd fun a nf => frame1 a fun inside =>
    nf (by rw [show a = scratch.toNat + (a - scratch.toNat) by omega]; exact j.scratchFree _ (by omega))
  refine Wp.cons (Wp.set (eval_add (eval_add rfl rfl) (eval_mul rfl rfl)) (Wp.cons (Wp.call
    (values := [indices, count, scratch + 8, scratch + 8 + 1024 * count, scratch])
    (by rw [show indices = env 6 from e6.symm, show count = env 7 from e7.symm,
      show scratch = env 8 from e8.symm]; rfl) ⟨_, mem1, callH, ?_⟩)))
  have lenL : L.length = count.toNat := wordsAt_length _ _ _
  cases hG : getHelperIndices L with
  | error e =>
    -- Refused indices are answered as they are.
    refine Wp.ite (eval_eq rfl rfl) (fun z => ?_) (fun _ => Wp.skip (Wp.nil ⟨_, rfl, ?_, rd1,
      fun a _ ha => frame1 a ha⟩))
    · simp only [assign, ↓reduceIte, helperCode, ite_eq_right (answerCode_error_ne_zero e)] at z
      exact absurd rfl z
    · simp only [assign, ↓reduceIte, verdict]
      rw [verifyMerkleMultiproof_eq _ _ _ _ sizes, nodesAt_length, wordsAt_length, eqc, ite_eq_right (by simp),
        show getHelperIndices (wordsAt mem indices.toNat count.toNat) = .error e from hG]
      rfl
  | ok hs =>
    obtain ⟨lenWord, hWords⟩ := okH hs hG
    refine Wp.ite (eval_eq rfl rfl) (fun _ => ?_) (fun z => by
      simp only [assign, ↓reduceIte, helperCode] at z; exact absurd z (by decide))
    have word := eval_ld (w := w) (env := assign (assign env 10 (env 8 + 8 + 1024 * env 7)) 9 0) (mem := mem1)
      (a := Ir.Expr.var 8) (x := scratch) (by simp [assign, e8, eval]) (by simpa using sub 0 8 (by omega))
    rw [lenWord] at word
    -- At most one helper per path node, and at most 63 path nodes per claim.
    have hsLen : hs.length ≤ 63 * count.toNat := by
      have sub' := List.Nodup.length_le_of_subset (getHelperIndices_nodup hG)
        (fun x hx => ((getHelperIndices_frontier hG).2.2 x).mp hx |>.1)
      rw [List.length_map, claimPaths_eq, show L = wordsAt mem indices.toNat count.toNat from rfl] at sub'
      have := flatMap_pathOf_length mem indices.toNat count.toNat
      omega
    have hsTo : hs.length.toUInt64.toNat = hs.length := toNat_ofNat_of_lt _ (by omega)
    refine Wp.ite (eval_ne word rfl) (fun differ => ?_) (fun same' => ?_)
    · -- A proof of the wrong length.
      have ne : hs.length ≠ proofCount.toNat := by
        intro h
        simp only [assign, ↓reduceIte, Nat.reduceEqDiff, e5] at differ
        rw [ite_eq_left (UInt64.toNat_inj.mp (by rw [hsTo, h]))] at differ
        exact differ rfl
      refine Wp.cons (Wp.set rfl (Wp.nil (Wp.nil ⟨_, rfl, ?_, rd1, fun a _ ha => frame1 a ha⟩)))
      simp only [assign, ↓reduceIte, verdict]
      rw [verifyMerkleMultiproof_eq _ _ _ _ sizes, nodesAt_length, wordsAt_length, eqc, ite_eq_right (by simp),
        show getHelperIndices (wordsAt mem indices.toNat count.toNat) = .ok hs from hG]
      simp only [nodesAt_length]
      rw [ite_eq_left (Ne.symm ne)]
      rfl
    have pc : hs.length = proofCount.toNat := by
      by_cases h : hs.length.toUInt64 = proofCount
      · rw [← hsTo, h]
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, e5, ite_eq_right h] at same'
        exact absurd same' (by decide)
    -- The two node-set areas, after the helper indices.
    have m15 : (1536 * count).toNat = 1536 * count.toNat := by rw [toNat_mul_of_lt _ _ (by simp; omega)]; simp
    have aAddr : (scratch + 8 + 1536 * count).toNat = scratch.toNat + 8 + 1536 * count.toNat := by
      rw [toNat_add_of_lt _ _ (by rw [p8, m15]; omega), p8, m15]
    have mTo : (count + proofCount).toNat = count.toNat + proofCount.toNat := by
      rw [toNat_add_of_lt _ _ (by omega)]
    have m80 : (80 * (count + proofCount)).toNat = 80 * (count.toNat + proofCount.toNat) := by
      rw [toNat_mul_of_lt _ _ (by rw [mTo]; simp; omega), mTo]; simp
    have bAddr : (scratch + 8 + 1536 * count + 80 * (count + proofCount)).toNat =
        scratch.toNat + 8 + 1536 * count.toNat + 80 * (count.toNat + proofCount.toNat) := by
      rw [toNat_add_of_lt _ _ (by rw [aAddr, m80]; omega), aAddr, m80]
    have helpersNow : wordsAt mem1 (scratch.toNat + 8 + 1024 * count.toNat) proofCount.toNat = hs := by
      rw [← pc, ← hAddr]; exact hWords
    refine Wp.cons (Wp.set (eval_add (eval_add rfl rfl) (eval_mul rfl rfl)) (Wp.cons (Wp.set (eval_add rfl rfl)
      (Wp.cons (Wp.set (eval_add rfl (eval_mul rfl rfl)) (Wp.cons (Wp.set rfl (Wp.cons ?_))))))))
    refine Wp.of_env (fun env => env 0 = job ∧ env 1 = ctx ∧ env 2 = leaves ∧ env 4 = proof ∧
        env 5 = proofCount ∧ env 6 = indices ∧ env 7 = count ∧ env 8 = scratch ∧ env 9 = 0 ∧
        env 10 = scratch + 8 + 1024 * count ∧ env 11 = scratch + 8 + 1536 * count ∧
        env 12 = scratch + 8 + 1536 * count + 80 * (count + proofCount) ∧ env 13 = count + proofCount ∧ env 14 = 0)
      (by simp [assign, e0, e1, e2, e4, e5, e6, e7, e8, helperCode]) ?_
    intro envA ⟨a0, a1, a2, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩
    have bL := access_bound j.leavesOk
    have bP := access_bound j.proofOk
    rw [eqc] at bL pL
    -- The leaves at their indices.
    refine build_loop 7 (by decide) envA count a7 (scratch.toNat + 8 + 1536 * count.toNat) indices.toNat
      leaves.toNat 0
      (fun env' same' lt => ⟨env' 11 + 40 * env' 14, fun _ => eval_add rfl (eval_mul rfl rfl), by
        rw [same' 11 (by decide), a11, toNat_add_of_lt _ _ (by rw [aAddr, toNat_mul_of_lt _ _ (by simp; omega)]; simp; omega),
          aAddr, toNat_mul_of_lt _ _ (by simp; omega)]; simp⟩)
      (fun env' _ same' lt => ⟨env' 6 + 8 * env' 14, eval_add rfl (eval_mul rfl rfl), by
        rw [same' 6 (by decide), a6, toNat_addr _ _ _ (by simp; omega)]; simp⟩)
      (fun env' same' lt => ⟨env' 2 + 32 * env' 14, fun _ => eval_add rfl (eval_mul rfl rfl), by
        rw [same' 2 (by decide), a2, toNat_addr _ _ _ (by simp; omega)]; simp⟩)
      (by simpa [Nat.add_assoc] using sub (8 + 1536 * count.toNat) (40 * count.toNat) (by omega)) j.indicesOk
      (by rw [← eqc]; exact j.leavesOk) (by simp only [Apart]; omega) (by simp only [Apart]; omega) a14
      (fun env2 mem2 same2 entries2 frame2 => ?_)
    -- The proof nodes at the helper indices, after the leaves.
    have aA2 : w.access (scratch.toNat + 8 + 1536 * count.toNat + 40 * count.toNat) (40 * proofCount.toNat) = true := by
      have := sub (8 + 1536 * count.toNat + 40 * count.toNat) (40 * proofCount.toNat) (by omega)
      rwa [show scratch.toNat + (8 + 1536 * count.toNat + 40 * count.toNat) =
        scratch.toNat + 8 + 1536 * count.toNat + 40 * count.toNat by omega] at this
    have aH2 : w.access (scratch.toNat + 8 + 1024 * count.toNat) (8 * proofCount.toNat) = true := by
      have := sub (8 + 1024 * count.toNat) (8 * proofCount.toNat) (by omega)
      rwa [show scratch.toNat + (8 + 1024 * count.toNat) = scratch.toNat + 8 + 1024 * count.toNat by omega] at this
    have b5 : (assign env2 14 0) 5 = proofCount := by simp [assign, same2 5 (by decide), a5]
    have keep2 : ∀ k, k ≠ 14 → assign env2 14 0 k = envA k := fun k hk => by
      simp only [assign, ite_eq_right hk]; exact same2 k hk
    refine Wp.cons (Wp.set rfl (Wp.cons (build_loop 5 (by decide) (assign env2 14 0) proofCount b5
      (scratch.toNat + 8 + 1536 * count.toNat) (scratch.toNat + 8 + 1024 * count.toNat) proof.toNat count.toNat
      (fun env' same' lt => ⟨env' 11 + 40 * (env' 7 + env' 14), fun _ => eval_add rfl (eval_mul rfl (eval_add rfl rfl)),
        by
          have h11 : env' 11 = scratch + 8 + 1536 * count := by rw [same' 11 (by decide), keep2 11 (by decide), a11]
          have h7 : env' 7 = count := by rw [same' 7 (by decide), keep2 7 (by decide), a7]
          have s7 : (env' 7 + env' 14).toNat = count.toNat + (env' 14).toNat := by
            rw [h7, toNat_add_of_lt _ _ (by omega)]
          rw [h11, toNat_add_of_lt _ _ (by rw [aAddr, toNat_mul_of_lt _ _ (by rw [s7]; simp; omega), s7]; simp; omega),
            aAddr, toNat_mul_of_lt _ _ (by rw [s7]; simp; omega), s7]; simp⟩)
      (fun env' _ same' lt => ⟨env' 10 + 8 * env' 14, eval_add rfl (eval_mul rfl rfl), by
        rw [same' 10 (by decide), keep2 10 (by decide), a10, toNat_addr _ _ _ (by rw [hAddr]; simp; omega), hAddr]
        simp⟩)
      (fun env' same' lt => ⟨env' 4 + 32 * env' 14, fun _ => eval_add rfl (eval_mul rfl rfl), by
        rw [same' 4 (by decide), keep2 4 (by decide), a4, toNat_addr _ _ _ (by simp; omega)]; simp⟩)
      aA2 aH2 j.proofOk (by simp only [Apart]; omega) (by simp only [Apart]; omega) (by simp [assign])
      (fun env3 mem3 same3 entries3 frame3 => ?_))))
    simp only [Nat.mul_zero, Nat.add_zero] at frame2
    -- The node set written is the Lean verifier's.
    let NODES := (wordsAt mem indices.toNat count.toNat).zip (nodesAt mem leaves.toNat count.toNat) ++
      hs.zip (nodesAt mem proof.toNat proofCount.toNat)
    have nodesEq : entriesAt mem3 (scratch.toNat + 8 + 1536 * count.toNat) (count.toNat + proofCount.toNat) =
        NODES := by
      simp only [Nat.zero_add] at entries2
      rw [entries3, entries2]
      have w1 : wordsAt mem1 indices.toNat count.toNat = wordsAt mem indices.toNat count.toNat :=
        wordsAt_congr fun k (hk : k < 8 * count.toNat) => frame1 _ (by omega)
      have l1 : nodesAt mem1 leaves.toNat count.toNat = nodesAt mem leaves.toNat count.toNat :=
        nodesAt_congr fun k (hk : k < 32 * count.toNat) => frame1 _ (by omega)
      have h2 : wordsAt mem2 (scratch.toNat + 8 + 1024 * count.toNat) proofCount.toNat = hs := by
        rw [← helpersNow]; exact wordsAt_congr fun k (hk : k < 8 * proofCount.toNat) => frame2 _ (by omega)
      have p2a : nodesAt mem2 proof.toNat proofCount.toNat = nodesAt mem1 proof.toNat proofCount.toNat := by
        apply nodesAt_congr
        intro k hk
        apply frame2
        clear pI pL pR pJ
        omega
      have p2b : nodesAt mem1 proof.toNat proofCount.toNat = nodesAt mem proof.toNat proofCount.toNat :=
        nodesAt_congr fun k (hk : k < 32 * proofCount.toNat) => frame1 (proof.toNat + k) (by clear pI pL pR pJ; omega)
      have p2 := p2a.trans p2b
      rw [w1, l1, h2, p2]
      simp only [entriesAt, List.range_zero, List.map_nil, List.nil_append]
      rfl
    have frame3' : ∀ a, ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + S) → mem3 a = mem a := by
      intro a ha
      clear pI pL pP pR pJ
      have o3 : ¬ (scratch.toNat + 8 + 1536 * count.toNat + 40 * count.toNat ≤ a ∧
          a < scratch.toNat + 8 + 1536 * count.toNat + 40 * count.toNat + 40 * proofCount.toNat) := by
        intro h; apply ha; constructor <;> omega
      have o2 : ¬ (scratch.toNat + 8 + 1536 * count.toNat ≤ a ∧
          a < scratch.toNat + 8 + 1536 * count.toNat + 40 * count.toNat) := by
        intro h; apply ha; constructor <;> omega
      rw [frame3 a o3, frame2 a o2, frame1 a ha]
    have rd3 : ready mem3 := hash.ready_frame _ _ rd fun a nf => frame3' a fun inside =>
      nf (scratchFree' a inside.1 inside.2)
    have keep3 : ∀ k, k ≠ 14 → env3 k = envA k := fun k hk => by rw [same3 k hk, keep2 k hk]
    -- The deepest level, then the fold.
    have ac : w.access (scratch + 8 + 1536 * count).toNat (40 * (count + proofCount).toNat) = true := by
      rw [aAddr, mTo]
      have := sub (8 + 1536 * count.toNat) (40 * (count.toNat + proofCount.toNat)) (by omega)
      rwa [show scratch.toNat + (8 + 1536 * count.toNat) = scratch.toNat + 8 + 1536 * count.toNat by omega] at this
    refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons (deepest_loop fns.level (sp := sp - 208) (by omega)
      _ (scratch + 8 + 1536 * count) (count + proofCount)
      (by simp [assign, keep3 11 (by decide), a11]) (by simp [assign, keep3 13 (by decide), a13])
      (by simp [assign]) (by simp [assign]) ac (fun env5 keep5 deep5 => ?_))))))
    rw [aAddr, mTo, nodesEq] at deep5
    have k5 : ∀ k, k ≠ 14 → k ≠ 15 → k ≠ 16 → env5 k = envA k := fun k h14 h15 h16 => by
      rw [keep5 k h14 h15 h16]; simp only [assign, ite_eq_right h14, ite_eq_right h15]; exact keep3 k h14
    -- The fold, between the two areas.
    let F := foldToRoot (deepestOf NODES) NODES
    have xOk : w.access (scratch + 8 + 1536 * count).toNat (80 * (count.toNat + proofCount.toNat)) = true := by
      rw [aAddr]
      have := sub (8 + 1536 * count.toNat) (80 * (count.toNat + proofCount.toNat)) (by omega)
      rwa [show scratch.toNat + (8 + 1536 * count.toNat) = scratch.toNat + 8 + 1536 * count.toNat by omega] at this
    have yOk : w.access (scratch + 8 + 1536 * count + 80 * (count + proofCount)).toNat
        (80 * (count.toNat + proofCount.toNat)) = true := by
      rw [bAddr]
      have := sub (8 + 1536 * count.toNat + 80 * (count.toNat + proofCount.toNat))
        (80 * (count.toNat + proofCount.toNat)) (by omega)
      rwa [show scratch.toNat + (8 + 1536 * count.toNat + 80 * (count.toNat + proofCount.toNat)) =
        scratch.toNat + 8 + 1536 * count.toNat + 80 * (count.toNat + proofCount.toNat) by omega] at this
    have fX : ∀ k < 80 * (count.toNat + proofCount.toNat), free ((scratch + 8 + 1536 * count).toNat + k) :=
      fun k hk => scratchFree' _ (by rw [aAddr]; omega) (by rw [aAddr]; omega)
    have fY : ∀ k < 80 * (count.toNat + proofCount.toNat),
        free ((scratch + 8 + 1536 * count + 80 * (count + proofCount)).toNat + k) :=
      fun k hk => scratchFree' _ (by rw [bAddr]; omega) (by rw [bAddr]; omega)
    have fW : ∀ k < 8, free (scratch.toNat + k) := fun k hk => scratchFree' _ (by omega) (by omega)
    have sW : w.access scratch.toNat 8 = true := by simpa using sub 0 8 (by omega)
    refine Wp.cons (fold_loop hash fns.parents fns.kept fns.level fns.helpers.find (sp := sp - 208) (by omega)
      (mem := mem3) (job := job) xOk yOk sW fX fY fW (by rw [aAddr, bAddr]; simp only [Apart]; omega)
      (by rw [aAddr]; simp only [Apart]; omega) (by rw [bAddr]; simp only [Apart]; omega) F env5 mem3 ?_
      (fun env6 mem6 inv6 z6 => ?_))
    · refine ⟨by rw [k5 0 (by decide) (by decide) (by decide), a0], by rw [k5 1 (by decide) (by decide) (by decide), a1],
        by rw [k5 8 (by decide) (by decide) (by decide), a8],
        .inl ⟨by rw [k5 11 (by decide) (by decide) (by decide), a11],
          by rw [k5 12 (by decide) (by decide) (by decide), a12]⟩,
        by rw [k5 13 (by decide) (by decide) (by decide), a13, mTo]; exact Nat.le_refl _, rd3, fun _ _ _ _ _ => rfl,
        .inl ⟨by rw [k5 9 (by decide) (by decide) (by decide), a9], ?_⟩⟩
      rw [k5 11 (by decide) (by decide) (by decide), a11, k5 13 (by decide) (by decide) (by decide), a13, aAddr, mTo,
        nodesEq, deep5]
    obtain ⟨f0, f1, f8, areas6, size6, rd6, frame6, state6⟩ := inv6
    have frame6' : ∀ a, free a → ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + S) → mem6 a = mem a := by
      intro a fa ha
      have oX : ¬ ((scratch + 8 + 1536 * count).toNat ≤ a ∧
          a < (scratch + 8 + 1536 * count).toNat + 80 * (count.toNat + proofCount.toNat)) := by
        rw [aAddr]; intro h; apply ha; constructor <;> omega
      have oY : ¬ ((scratch + 8 + 1536 * count + 80 * (count + proofCount)).toNat ≤ a ∧
          a < (scratch + 8 + 1536 * count + 80 * (count + proofCount)).toNat +
            80 * (count.toNat + proofCount.toNat)) := by
        rw [bAddr]; intro h; apply ha; constructor <;> omega
      have oW : ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + 8) := by
        intro h; apply ha; constructor <;> omega
      rw [frame6 a fa oX oY oW, frame3' a ha]
    -- The verdict, in terms of the fold.
    have verdictF : verdict = answerCode (F.map fun rebuilt => decide (rebuilt = readNode mem root.toNat)) := by
      simp only [verdict]
      rw [verifyMerkleMultiproof_eq _ _ _ _ sizes, nodesAt_length, wordsAt_length, eqc, ite_eq_right (by simp),
        show getHelperIndices (wordsAt mem indices.toNat count.toNat) = .ok hs from hG]
      simp only [nodesAt_length]
      rw [ite_eq_right (by omega)]
    rcases state6 with ⟨s9, fold6⟩ | ⟨s9, _, e, Fe⟩
    · -- The fold reached the root's level: the root's entry is looked up and compared.
      rw [show (env6 15).toNat = 0 by rw [z6]; rfl] at fold6
      -- The current area is one of the two, with room for the node set.
      have cur6 : w.access (env6 11).toNat (40 * (env6 13).toNat) = true := by
        rcases areas6 with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
        · exact access_prefix xOk (by omega)
        · exact access_prefix yOk (by omega)
      have bc := access_bound cur6
      have bz := (env6 13).toNat_lt
      have call := find_calls (w := w) fns.helpers.find (sp := sp - 208) (by omega) (env6 11) 40 (env6 13) 1 mem6
        fun j hj => by simpa using access_sub (k := 40 * j) (j := 8) cur6 (by omega)
      simp only [UInt64.reduceToNat] at call
      have look := nodeAt_entriesAt mem6 (env6 11).toNat 1 (env6 13).toNat
      simp only [UInt64.reduceToNat] at look
      generalize hJ : firstAt (big32 mem6 (env6 11).toNat 40) 1 (env6 13).toNat = J at call look
      have jle : J ≤ (env6 13).toNat := by rw [← hJ]; exact firstAt_le _ _ _
      simp only [foldToRoot, look] at fold6
      refine Wp.ite (eval_eq rfl rfl) (fun _ => ?_) (fun z => ?_)
      rotate_left
      · simp [s9] at z
      refine Wp.cons (Wp.call (values := [env6 11, 40, env6 13, 1]) rfl ⟨_, mem6, call, ?_⟩)
      have jTo : J.toUInt64.toNat = J := toNat_ofNat_of_lt _ (by omega)
      refine Wp.ite (eval_eq rfl rfl) (fun missing => ?_) (fun found => ?_)
      · -- No entry at the root's index.
        have none_ : ¬ J < (env6 13).toNat := by
          intro h
          simp only [assign, ↓reduceIte, Nat.reduceEqDiff] at missing
          rw [ite_eq_right (fun e => by rw [← e, jTo] at h; omega)] at missing
          exact missing rfl
        rw [ite_eq_right none_] at fold6
        refine Wp.cons (Wp.set rfl (Wp.nil (Wp.nil ⟨_, rfl, ?_, rd6, frame6'⟩)))
        simp only [assign, ↓reduceIte]
        rw [verdictF, ← fold6]; rfl
      · -- The root's entry, compared with the expected root.
        have some_ : J < (env6 13).toNat := by
          rcases Nat.lt_or_eq_of_le jle with h | h
          · exact h
          · simp only [assign, ↓reduceIte, Nat.reduceEqDiff] at found
            rw [ite_eq_left (by rw [h]; exact UInt64.ofNat_toNat)] at found
            exact absurd found (by decide)
        rw [ite_eq_left some_] at fold6
        -- The expected root's address, read from the job, which nothing wrote.
        have bj' := access_bound j.words
        have rootWord : eval w (assign env6 14 J.toUInt64) mem6 (Ir.Expr.ld (Ir.Expr.var 0 + 48)) = some root := by
          have h := eval_ld_off (w := w) (env := assign env6 14 J.toUInt64) (mem := mem6) (a := Ir.Expr.var 0)
            (x := job) (n := 48) (show eval w (assign env6 14 J.toUInt64) mem6 (Ir.Expr.var 0) = some job by
              simp [eval, assign, f0]) (access_sub j.words (by simp))
          simp only [UInt64.reduceToNat] at h
          rw [readLE_congr mem6 mem _ 8 (fun k hk => by
            rw [Nat.add_assoc]; exact frame6' _ (j.jobFree _ (by omega)) (by omega)), j.w6] at h
          exact h
        have rootNow : readNode mem6 root.toNat = readNode mem root.toNat :=
          readNode_congr fun k hk => frame6' _ (j.rootFree k hk) (by omega)
        have nodeAddr : (env6 11 + 40 * J.toUInt64 + 8).toNat = (env6 11).toNat + 40 * J + 8 := by
          rw [toNat_add_of_lt _ _ (by rw [toNat_addr _ _ _ (by rw [jTo]; simp; omega), jTo]; simp; omega),
            toNat_addr _ _ _ (by rw [jTo]; simp; omega), jTo]; simp
        have sc := same_calls (w := w) fns.same (sp := sp - 208) (by omega) (env6 11 + 40 * J.toUInt64 + 8) root mem6
          (by rw [nodeAddr, Nat.add_assoc]; exact access_sub cur6 (by omega)) j.rootOk
        have args : [Ir.Expr.var 11 + 40 * Ir.Expr.var 14 + 8, Ir.Expr.ld (Ir.Expr.var 0 + 48)].mapM
            (eval w (assign env6 14 J.toUInt64) mem6) = some [env6 11 + 40 * J.toUInt64 + 8, root] := by
          have first : eval w (assign env6 14 J.toUInt64) mem6 (Ir.Expr.var 11 + 40 * Ir.Expr.var 14 + 8) =
              some (env6 11 + 40 * J.toUInt64 + 8) := eval_add (eval_add rfl (eval_mul rfl rfl)) rfl
          simp [List.mapM_cons, first, rootWord]
        refine Wp.cons (Wp.call args ⟨_, mem6, sc, Wp.nil (Wp.nil ⟨_, rfl, ?_, rd6, frame6'⟩)⟩)
        simp only [assign, ↓reduceIte]
        rw [verdictF, ← fold6, nodeAddr, rootNow]
        simp only [Except.map, answerCode_decide]
    · -- The fold refused: a pair or the root was missing.
      refine Wp.ite (eval_eq rfl rfl) (fun z => ?_) (fun _ => Wp.skip (Wp.nil
        ⟨env6 9, rfl, ?_, rd6, frame6'⟩))
      · simp only [s9] at z; exact absurd z (by decide)
      · rw [s9, verdictF, Fe, foldToRoot_error _ _ Fe]; rfl

/--
With the proved hashing drivers and a filled context, the compiled multiproof verifier answers what the Lean
verifier answers on the leaves, proof nodes, indices and root its job names.
-/
theorem verify_multiproof_hashing {m : Module} {w : World} (hash : HashingOk m w) (fns : MultiFns m)
    {ctx : UInt64} {table pad : Nat} {mask : UInt64} {sp : Nat} (deep : w.stackLo + 512 + hashStack ≤ sp)
    {mem : Memory} (rd : CtxReady w ctx.toNat table pad mask mem)
    {job leaves leafCount proof proofCount indices count root scratch : UInt64}
    (j : MultiJob w (CtxFree ctx.toNat table pad) mem job leaves leafCount proof proofCount indices count root
      scratch) :
    ∃ mem', Calls m w "ssz_verify_multiproof" sp [job, ctx] mem
        (answerCode (verifyMerkleMultiproof (nodesAt mem leaves.toNat leafCount.toNat)
          (nodesAt mem proof.toNat proofCount.toNat) (wordsAt mem indices.toNat count.toNat)
          (readNode mem root.toNat))) mem' ∧
      CtxReady w ctx.toNat table pad mask mem' ∧
      ∀ a, CtxFree ctx.toNat table pad a →
        ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + multiScratch count.toNat proofCount.toNat) → mem' a = mem a :=
  verify_multiproof_calls fns (pairHashing_of hash ctx table pad mask) deep rd j

end EthLib.Consensus.Ssz.Native.Driver.BranchProof
