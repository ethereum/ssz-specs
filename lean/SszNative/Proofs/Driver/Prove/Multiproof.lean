import SszNative.Proofs.Driver.Prove.Branch
import SszNative.Proofs.Driver.Branch.VerifyMultiproof

/-!
The compiled multiproof builder walks to each helper node, as the Lean multiproof does.

The helper indices come from the compiled helper-index computation, and each node from the contract of the walk.
-/

namespace Ssz.Native.Driver.ProveProof

open Ssz Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Driver.BranchProof

/-- A refusal of a request's indices, which comes before any walk. -/
def ClaimErr (e : Err) : Prop :=
  (∃ i, e = .notAGindex i) ∨ e = .rootHasNoBranch ∨ (∃ i, e = .nestedIndex i) ∨ e = .emptyRequest ∨
    e = .repeatedIndex

/-- A refusal of the indices has the same code in every driver. -/
theorem ClaimErr.code {e : Err} (h : ClaimErr e) : errCode e = answerCode (.error e) := by
  rcases h with ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩ | rfl | rfl <;> rfl

/-- An ancestor check refuses only a nested index. -/
theorem rejectAncestors_error {l : List Nat} {c : Nat} : ∀ {rest : List Nat} {e : Err},
    rejectAncestors l c rest = .error e → ClaimErr e
  | [], e, h => by simp [rejectAncestors] at h
  | a :: rest, e, h => by
    by_cases hc : a ∈ l
    · simp [rejectAncestors, hc, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      exact .inr (.inr (.inl ⟨c, h.symm⟩))
    · simp [rejectAncestors, hc] at h
      exact rejectAncestors_error h

/-- A step after a path refuses as the path does, or as the step does on the path. -/
theorem getPathIndices_error {i : Nat} {e : Err} {α : Type} (k : List Nat → Except Err α)
    (h : (getPathIndices i >>= k) = .error e) : ClaimErr e ∨ ∃ p, getPathIndices i = .ok p ∧ k p = .error e := by
  cases hp : getPathIndices i with
  | ok p => exact .inr ⟨p, rfl, by rw [hp] at h; exact h⟩
  | error e' =>
    rw [hp] at h
    cases h
    left
    simp only [getPathIndices, gindexLength, gindexDepth, bind, Except.bind] at hp
    by_cases z : i < 1
    · simp [z] at hp; exact .inl ⟨i, hp.symm⟩
    · by_cases o : Nat.log2 i = 0
      · simp [z, o] at hp; exact .inr (.inl hp.symm)
      · simp [z, o, pure, Except.pure] at hp

/-- The path checks refuse only as the indices are refused. -/
theorem rejectClaimPaths_error {l : List Nat} : ∀ {cs : List Nat} {e : Err},
    rejectClaimPaths l cs = .error e → ClaimErr e
  | [], e, h => by simp [rejectClaimPaths] at h
  | c :: rest, e, h => by
    simp only [rejectClaimPaths] at h
    rcases getPathIndices_error _ h with ce | ⟨p, _, hk⟩
    · exact ce
    · cases ha : rejectAncestors l c (p.drop 1) with
      | error e' =>
        rw [ha] at hk; cases hk; exact rejectAncestors_error ha
      | ok u =>
        rw [ha] at hk
        exact rejectClaimPaths_error hk

/-- The claim checks refuse only as the indices are refused. -/
theorem rejectRelated_error {l : List Nat} {e : Err} (h : rejectRelated l = .error e) : ClaimErr e := by
  rw [rejectRelated_eq] at h
  split at h
  · cases h; exact .inr (.inr (.inr (.inl rfl)))
  split at h
  · cases h; exact .inr (.inr (.inr (.inr rfl)))
  exact rejectClaimPaths_error h

/-- The helper indices refuse only as the indices are refused. -/
theorem helperIndices_claimErr {l : List Nat} {e : Err} (h : getHelperIndices l = .error e) : ClaimErr e := by
  cases hr : rejectRelated l with
  | error e' =>
    rw [getHelperIndices_error hr] at h; cases h; exact rejectRelated_error hr
  | ok u =>
    cases u
    simp [getHelperIndices, hr, collectPathIndices_eq hr, bind, Except.bind, pure, Except.pure] at h

/-- Every node on a path lies below the root. -/
theorem mem_pathOf_two (c : Nat) (x : Nat) (hx : x ∈ pathOf c) : 2 ≤ x := by
  by_cases small : c ≤ 1
  · rw [pathOf_small c small] at hx; cases hx
  · rw [pathOf_cons c (by omega)] at hx
    rcases List.mem_cons.mp hx with rfl | h
    · omega
    · exact mem_pathOf_two (c / 2) x h
termination_by c
decreasing_by omega

/-- The sibling of a node below the root is an index, never zero. -/
theorem xor_one_pos {x : Nat} (two : 2 ≤ x) : 1 ≤ x ^^^ 1 := by
  apply Nat.pos_of_ne_zero
  intro zero
  have back : x = (x ^^^ 1) ^^^ 1 := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [zero, Nat.zero_xor] at back
  omega

/-- Every helper index is an index, never zero. -/
theorem helper_pos {l hs : List Nat} (h : getHelperIndices l = .ok hs) : ∀ x ∈ hs, 1 ≤ x := by
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (((getHelperIndices_frontier h).2.2 x).mp hx).1
  rw [claimPaths_eq] at hp
  obtain ⟨c, _, hc⟩ := List.mem_flatMap.mp hp
  exact xor_one_pos (mem_pathOf_two c p hc)

/-- At most one helper per path node, and at most 63 path nodes per index. -/
theorem helpers_length {mem : Memory} {a count : Nat} {hs : List Nat}
    (hG : getHelperIndices (wordsAt mem a count) = .ok hs) : hs.length ≤ 63 * count := by
  have sub' := List.Nodup.length_le_of_subset (getHelperIndices_nodup hG)
    (fun x hx => ((getHelperIndices_frontier hG).2.2 x).mp hx |>.1)
  rw [List.length_map, claimPaths_eq] at sub'
  have := flatMap_pathOf_length mem a count
  omega

/-- An accepted encoding's multiproof is the walk to each of its helper indices. -/
theorem buildMultiproof_eq {d : Desc} {b : ByteArray} (valid : validate d b = .ok ()) (l : List Nat) :
    buildMultiproof d b l = (getHelperIndices l >>= fun hs => hs.mapM (walkNode d b)) := by
  simp [buildMultiproof, valid, bind, Except.bind]
  rfl

/-- One more node walked after the first ones of a list. -/
theorem mapM_take_succ {α : Type} (f : Nat → Except Err α) (hs : List Nat) (i : Nat) (h : i < hs.length) :
    (hs.take (i + 1)).mapM f = (do
      let nodes ← (hs.take i).mapM f
      let node ← f hs[i]
      pure (nodes ++ [node])) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.mapM_append, List.mapM_cons,
    List.mapM_nil]
  cases (hs.take i).mapM f <;> cases f hs[i] <;> rfl

/-- A refusal among the first nodes of a list is the refusal of the whole list. -/
theorem mapM_take_error {α : Type} {f : Nat → Except Err α} {hs : List Nat} {i : Nat} {e : Err}
    (h : (hs.take i).mapM f = .error e) : hs.mapM f = .error e := by
  rw [← List.take_append_drop i hs, List.mapM_append, h]
  rfl

/--
A multiproof-building job in memory: its words, the indices, the nodes' place and the scratch usable, free, and
apart.

The word after the job's seven is where the node count is written, so it is free memory too.
-/
structure MultiJob (w : World) (free : Nat → Prop) (mem : Memory)
    (job plan data size indices count out scr : UInt64) (need : Nat) : Prop where
  /-- The job's words are usable. -/
  words : w.access job.toNat 64 = true
  /-- The job's first seven words are not free, so nothing the walk writes reaches them. -/
  kept : ∀ k < 56, ¬ free (job.toNat + k)
  /-- The plan's address. -/
  w0 : readLE mem job.toNat 8 = plan
  /-- The encoding's address. -/
  w1 : readLE mem (job.toNat + 8) 8 = data
  /-- The encoding's size. -/
  w2 : readLE mem (job.toNat + 16) 8 = size
  /-- The indices' address. -/
  w3 : readLE mem (job.toNat + 24) 8 = indices
  /-- How many indices. -/
  w4 : readLE mem (job.toNat + 32) 8 = count
  /-- Where the nodes go. -/
  w5 : readLE mem (job.toNat + 40) 8 = out
  /-- The scratch area's address. -/
  w6 : readLE mem (job.toNat + 48) 8 = scr
  /-- The node count's word is free memory. -/
  countFree : ∀ k < 8, free (job.toNat + 56 + k)
  /-- The indices are usable. -/
  indicesOk : w.access indices.toNat (8 * count.toNat) = true
  /-- The indices miss the scratch area. -/
  indicesApart : Apart (indices.toNat, 8 * count.toNat) (scr.toNat, 32 + 1536 * count.toNat + need)
  /-- The nodes' place is usable, 63 nodes per index. -/
  outOk : w.access out.toNat (2016 * count.toNat) = true
  /-- The scratch area is usable. -/
  scrOk : w.access scr.toNat (32 + 1536 * count.toNat + need) = true
  /-- The nodes' place is free memory. -/
  outFree : ∀ k < 2016 * count.toNat, free (out.toNat + k)
  /-- The scratch area is free memory. -/
  scrFree : ∀ k < 32 + 1536 * count.toNat + need, free (scr.toNat + k)
  /-- The nodes' place misses the scratch area. -/
  apart : Apart (out.toNat, 2016 * count.toNat) (scr.toNat, 32 + 1536 * count.toNat + need)
  /-- The node count's word misses the nodes' place. -/
  countOut : Apart (job.toNat + 56, 8) (out.toNat, 2016 * count.toNat)
  /-- The node count's word misses the scratch area. -/
  countScr : Apart (job.toNat + 56, 8) (scr.toNat, 32 + 1536 * count.toNat + need)

/-- The places a multiproof job may write: the nodes, the scratch, the node count's word, and the padding area. -/
def MultiOutside (job out scr count need pad a : Nat) : Prop :=
  ¬ (out ≤ a ∧ a < out + 2016 * count) ∧ ¬ (scr ≤ a ∧ a < scr + 32 + 1536 * count + need) ∧
    ¬ (job + 56 ≤ a ∧ a < job + 64) ∧ ¬ (pad ≤ a ∧ a < pad + 1536)

/--
The multiproof loop: fixed arguments, the helper reached, the frame, the count and helper words, and the nodes walked.
-/
private def MultiInv (d : Desc) (b : ByteArray) (mem : Memory) (job ctx count out scr : UInt64) (need pad : Nat)
    (hs : List Nat) (env : Env) (mem' : Memory) : Prop :=
  env 0 = job ∧ env 1 = ctx ∧ env 3 = scr ∧ env 4 = count ∧ env 5 = scr + 8 + 1024 * count ∧
    (env 6).toNat = hs.length ∧ env 7 = scr + 8 + 1024 * count + 512 * count ∧ (env 8).toNat ≤ hs.length ∧
    (∀ a, MultiOutside job.toNat out.toNat scr.toNat count.toNat need pad a → mem' a = mem a) ∧
    readLE mem' (job.toNat + 56) 8 = hs.length.toUInt64 ∧
    wordsAt mem' (scr.toNat + 8 + 1024 * count.toNat) hs.length = hs ∧
    ((env 2 = 0 ∧ ∃ nodes, (hs.take (env 8).toNat).mapM (walkNode d b) = .ok nodes ∧
        nodesAt mem' out.toNat (env 8).toNat = nodes) ∨
      ∃ e, env 2 = errCode e ∧ (hs.take (env 8).toNat).mapM (walkNode d b) = .error e)

/--
A call of the multiproof builder answers what the Lean multiproof answers, and writes its nodes and their count when
there are some.

The walk to each node is the contract of the branch builder, and the encoding is one validation accepts.
Only the nodes' place, the scratch area, the node count's word, and the padding area change.
-/
theorem prove_multiproof_calls {m : Module} {w : World} {d : Desc} {b : ByteArray} {plan data ctx : UInt64}
    {pad : Nat} {ready : Memory → Prop} {free : Nat → Prop} {need room : Nat}
    (hf : m.fns.lookup "ssz_prove_multiproof" = some ProveMultiproof.fn) (fns : HelperFns m)
    (walk : NodeAtOk m w d b plan data ctx pad ready free need room) (valid : validate d b = .ok ()) {sp : Nat}
    (deep : w.stackLo + 8 + 8 * ProveMultiproof.fn.frame + room + 304 ≤ sp)
    (job indices count out scr : UInt64) (mem : Memory) (r0 : ready mem)
    (j : MultiJob w free mem job plan data b.size.toUInt64 indices count out scr need)
    (jobPad : ∀ k < 56, ¬ (pad ≤ job.toNat + k ∧ job.toNat + k < pad + 1536)) :
    ∃ r mem', Calls m w "ssz_prove_multiproof" sp [job, ctx] mem r mem' ∧
      r = proveCode (buildMultiproof d b (wordsAt mem indices.toNat count.toNat)) ∧
      (∀ nodes,
        buildMultiproof d b (wordsAt mem indices.toNat count.toNat) = .ok nodes →
          readLE mem' (job.toNat + 56) 8 = nodes.length.toUInt64 ∧ nodesAt mem' out.toNat nodes.length = nodes) ∧
      ∀ a, MultiOutside job.toNat out.toNat scr.toNat count.toNat need pad a → mem' a = mem a := by
  generalize hL : wordsAt mem indices.toNat count.toNat = L
  have bo := BranchProof.access_bound j.outOk
  have bs := BranchProof.access_bound j.scrOk
  have bj := BranchProof.access_bound j.words
  have bi := BranchProof.access_bound j.indicesOk
  -- An address that is not free is outside every place the job may write.
  have outside : ∀ a, ¬ free a → ¬ (pad ≤ a ∧ a < pad + 1536) →
      MultiOutside job.toNat out.toNat scr.toNat count.toNat need pad a := fun a nf np =>
    ⟨fun h => nf (by have := j.outFree (a - out.toNat) (by omega); rwa [Nat.add_sub_cancel' h.1] at this),
      fun h => nf (by have := j.scrFree (a - scr.toNat) (by omega); rwa [Nat.add_sub_cancel' h.1] at this),
      fun h => nf (by
        have := j.countFree (a - (job.toNat + 56)) (by omega); rwa [Nat.add_sub_cancel' h.1] at this), np⟩
  -- The padding area is never free, so the places the job writes miss it.
  have notPad : ∀ a, free a → ¬ (pad ≤ a ∧ a < pad + 1536) := fun a f h => walk.padKept a h.1 h.2 f
  let Post := fun (r : UInt64) (mem' : Memory) =>
    r = proveCode (buildMultiproof d b L) ∧
      (∀ nodes, buildMultiproof d b L = .ok nodes →
        readLE mem' (job.toNat + 56) 8 = nodes.length.toUInt64 ∧ nodesAt mem' out.toNat nodes.length = nodes) ∧
      ∀ a, MultiOutside job.toNat out.toNat scr.toNat count.toNat need pad a → mem' a = mem a
  suffices body : Wp m w (sp - 8 - 8 * ProveMultiproof.fn.frame) ProveMultiproof.fn.body (entryEnv [job, ctx]) mem
      fun env mem' => ∃ r, eval w env mem' ProveMultiproof.fn.result = some r ∧ Post r mem' by
    exact Calls.of_wp hf (by omega) rfl body
  have spRoom : w.stackLo + room + 304 ≤ sp - 8 - 8 * ProveMultiproof.fn.frame := by omega
  generalize sp - 8 - 8 * ProveMultiproof.fn.frame = sp' at spRoom ⊢
  simp only [ProveMultiproof.fn]
  have rd : ∀ k, k + 8 ≤ 64 → w.access (job.toNat + k) 8 = true := fun k hk => BranchProof.access_sub j.words hk
  -- The count and the scratch are read from the job, and the helpers placed past the helper computation's scratch.
  refine Wp.cons (Wp.set (eval_word (x := job) rfl 32 (rd 32 (by omega)) j.w4) ?_)
  refine Wp.cons (Wp.set (eval_word (x := job) rfl 48 (rd 48 (by omega)) j.w6) ?_)
  refine Wp.cons (Wp.set (v := scr + 8 + 1024 * count) (BranchProof.eval_add (BranchProof.eval_add rfl rfl) (BranchProof.eval_mul rfl rfl)) ?_)
  have s8 : (scr + 8).toNat = scr.toNat + 8 := by
    rw [BranchProof.toNat_add_of_lt _ _ (by simp; omega)]; simp
  have hN : (scr + 8 + 1024 * count).toNat = scr.toNat + 8 + 1024 * count.toNat := by
    rw [BranchProof.toNat_add_of_lt _ _ (by rw [s8, BranchProof.toNat_mul_of_lt _ _ (by simp; omega)]; simp; omega), s8,
      BranchProof.toNat_mul_of_lt _ _ (by simp; omega)]; simp
  have eN : (scr + 8 + 1024 * count + 512 * count).toNat = scr.toNat + 8 + 1536 * count.toNat := by
    rw [BranchProof.toNat_add_of_lt _ _ (by rw [hN, BranchProof.toNat_mul_of_lt _ _ (by simp; omega)]; simp; omega), hN,
      BranchProof.toNat_mul_of_lt _ _ (by simp; omega)]; simp; omega
  -- The helper indices, computed in the scratch.
  obtain ⟨mem1, call1, okH, frame1⟩ := helper_indices_calls fns (sp := sp') (by omega) indices count (scr + 8)
    (scr + 8 + 1024 * count) scr mem j.indicesOk (by rw [s8]; exact BranchProof.access_sub (k := 8) j.scrOk (by omega))
    (by rw [hN, Nat.add_assoc]; exact BranchProof.access_sub (k := 8 + 1024 * count.toNat) j.scrOk (by omega))
    (BranchProof.access_prefix j.scrOk (by omega))
    (by rw [s8]; have := j.indicesApart; simp only [Apart] at this ⊢; omega)
    (by rw [s8, hN]; simp only [Apart]; omega) (by rw [hN]; simp only [Apart]; omega)
  simp only [hL, s8, hN] at call1 okH frame1
  have hI := eval_word (w := w) (env := assign (assign (assign (assign (entryEnv [job, ctx]) 2 2) 4 count) 3 scr) 5
    (scr + 8 + 1024 * count)) (mem := mem) (a := Ir.Expr.var 0) (x := job) rfl 24 (rd 24 (by omega)) j.w3
  refine Wp.cons (Wp.call (values := [indices, count, scr + 8, scr + 8 + 1024 * count, scr])
    (by simp only [List.mapM_cons, List.mapM_nil]; erw [hI]; rfl)
    ⟨_, mem1, call1, ?_⟩)
  have frame1' : ∀ a, MultiOutside job.toNat out.toNat scr.toNat count.toNat need pad a → mem1 a = mem a :=
    fun a ⟨_, hs, _, _⟩ => frame1 a (by omega) (by omega) (by omega)
  refine Wp.ite (BranchProof.eval_eq rfl rfl) (fun z => ?_) (fun nz => ?_)
  rotate_left
  · -- A refused request is answered as it is.
    cases hG : getHelperIndices L with
    | ok hs => simp [assign, hG, helperCode] at nz
    | error e =>
      refine Wp.skip ⟨_, rfl, ?_, fun nodes h => ?_, frame1'⟩
      · simp only [assign, ↓reduceIte, buildMultiproof_eq valid, hG, helperCode]
        exact ((helperIndices_claimErr hG).code).symm
      · rw [buildMultiproof_eq valid, hG] at h; cases h
  obtain ⟨hs, hG⟩ : ∃ hs, getHelperIndices L = .ok hs := by
    cases hG : getHelperIndices L with
    | ok hs => exact ⟨hs, rfl⟩
    | error e =>
      simp only [assign, ↓reduceIte, hG, helperCode] at z
      exact absurd (flag_ne z) (answerCode_error_ne_zero e)
  obtain ⟨lenWord, helperWords⟩ := okH hs hG
  have hsLen : hs.length ≤ 63 * count.toNat := by rw [← hL] at hG; exact helpers_length hG
  have hsTo : hs.length.toUInt64.toNat = hs.length := BranchProof.toNat_ofNat_of_lt _ (by omega)
  have cAt : (job + 56).toNat = job.toNat + 56 := by rw [BranchProof.toNat_add_of_lt _ _ (by simp; omega)]; simp
  refine Wp.cons (Wp.set (BranchProof.eval_ld (x := scr) rfl (BranchProof.access_prefix j.scrOk (by omega))) ?_)
  rw [lenWord]
  refine Wp.cons (Wp.store (x := job + 56) (y := hs.length.toUInt64) (BranchProof.eval_add rfl rfl) rfl
    (by rw [cAt]; exact rd 56 (by omega)) ?_)
  refine Wp.cons (Wp.set (v := scr + 8 + 1024 * count + 512 * count) (BranchProof.eval_add rfl (BranchProof.eval_mul rfl rfl)) ?_)
  refine Wp.cons (Wp.set rfl ?_)
  simp only [Width.bytes]
  rw [cAt]
  generalize hM2 : store mem1 (job.toNat + 56) 8 (qwordByte hs.length.toUInt64) = mem2
  have count2 : readLE mem2 (job.toNat + 56) 8 = hs.length.toUInt64 := by rw [← hM2, readLE_store8]
  have words2 : wordsAt mem2 (scr.toNat + 8 + 1024 * count.toNat) hs.length = hs := by
    rw [← hM2, wordsAt_congr fun k hk => store_outside _ _ _ _ _ (by have := j.countScr; simp only [Apart] at this; omega)]
    exact helperWords
  have frame2 : ∀ a, MultiOutside job.toNat out.toNat scr.toNat count.toNat need pad a → mem2 a = mem a :=
    fun a h => by rw [← hM2, store_outside _ _ _ _ _ h.2.2.1]; exact frame1' a h
  refine Wp.loop (MultiInv d b mem job ctx count out scr need pad hs)
    (fun env _ => hs.length - (env 8).toNat)
    ⟨by simp [assign, entryEnv], by simp [assign, entryEnv], by simp [assign], by simp [assign], by simp [assign],
      by simp only [assign, ↓reduceIte, Nat.reduceEqDiff]; exact hsTo, by simp [assign], by simp [assign],
      frame2, count2, words2,
      .inl ⟨by simp [assign, hG, helperCode], [], by simp [assign]; rfl, by simp [assign, nodesAt]⟩⟩ ?_
  have bm : buildMultiproof d b L = hs.mapM (walkNode d b) := by rw [buildMultiproof_eq valid, hG]; rfl
  -- Any usable range inside the job, the nodes' place, or the scratch.
  have accIn : ∀ {a n : Nat}, w.access a n = true → ∀ x len, a ≤ x → x + len ≤ a + n → w.access x len = true :=
    fun {a n} h x len h1 h2 => by
      have := BranchProof.access_sub (k := x - a) (j := len) h (by omega)
      rwa [Nat.add_sub_cancel' h1] at this
  intro env mm ⟨e0, e1, e3, e4, e5, e6, e7, ile, frame, cW, hW, st⟩
  refine ⟨_, BranchProof.eval_and (BranchProof.eval_lt rfl rfl) (BranchProof.eval_eq rfl rfl), fun go => ?_,
    fun stop => ?_⟩
  rotate_left
  · -- The loop ends with the last helper walked or the first refusal.
    rw [and_flags] at stop
    have done := flag_eq stop
    rw [e6] at done
    repeat refine Wp.nil ?_
    refine ⟨env 2, rfl, ?_, fun nodes h => ?_, frame⟩
    · rw [bm]
      rcases st with ⟨r0', ns, pre, _⟩ | ⟨e, re, pre⟩
      · have last : (env 8).toNat = hs.length := by
          have : ¬ ((env 8).toNat < hs.length) := fun h => done ⟨h, r0'⟩
          omega
        rw [last, List.take_length] at pre
        rw [pre, r0']; rfl
      · rw [re, mapM_take_error pre]; rfl
    · rw [bm] at h
      rcases st with ⟨r0', ns, pre, written⟩ | ⟨e, re, pre⟩
      · have last : (env 8).toNat = hs.length := by
          have : ¬ ((env 8).toNat < hs.length) := fun h => done ⟨h, r0'⟩
          omega
        rw [last, List.take_length, h] at pre
        injection pre with e
        subst e
        have len : nodes.length = hs.length := by rw [← written, nodesAt_length, last]
        rw [len, ← last]
        exact ⟨by rw [last]; exact cW, written⟩
      · rw [mapM_take_error pre] at h; cases h
  · -- One more helper: its record is written, then the walk to it.
    rw [and_flags] at go
    obtain ⟨more, r0'⟩ := flag_ne go
    rw [e6] at more
    rcases st with ⟨_, ns, pre, written⟩ | ⟨e, re, _⟩
    rotate_left
    · exact absurd (re.symm.trans r0') (errCode_ne_zero e)
    have hE : (env 7).toNat = scr.toNat + 8 + 1536 * count.toNat := by rw [e7, eN]
    have hO : (out + 32 * env 8).toNat = out.toNat + 32 * (env 8).toNat := by
      rw [BranchProof.toNat_addr _ _ _ (by simp; omega)]; simp
    have h8 : (env 7 + 8).toNat = (env 7).toNat + 8 := by
      rw [BranchProof.toNat_add_of_lt _ _ (by rw [hE]; simp; omega)]; simp
    have h16 : (env 7 + 16).toNat = (env 7).toNat + 16 := by
      rw [BranchProof.toNat_add_of_lt _ _ (by rw [hE]; simp; omega)]; simp
    have hH : (env 5 + 8 * env 8).toNat = scr.toNat + 8 + 1024 * count.toNat + 8 * (env 8).toNat := by
      rw [BranchProof.toNat_addr _ _ _ (by rw [e5, hN]; simp; omega), e5, hN]; simp
    have keptMM : ∀ k < 56, mm (job.toNat + k) = mem (job.toNat + k) := fun k hk =>
      frame _ (outside _ (j.kept k hk) (jobPad k hk))
    refine Wp.cons (Wp.store (x := env 7) (y := out + 32 * env 8) rfl
      (BranchProof.eval_add (eval_word (x := env 0) rfl 40 (by rw [e0]; exact rd 40 (by omega))
        (by rw [e0, show (40 : UInt64).toNat = 40 from rfl,
          readLE_congr mm mem _ 8 (fun i hi => by rw [Nat.add_assoc]; exact keptMM _ (by omega))]; exact j.w5))
        (BranchProof.eval_mul rfl rfl))
      (by rw [hE]; exact accIn j.scrOk _ _ (by omega) (by simp only [Width.bytes]; omega)) ?_)
    refine Wp.cons (Wp.store (x := env 7 + 8) (y := env 7 + 24) (BranchProof.eval_add rfl rfl)
      (BranchProof.eval_add rfl rfl) (by rw [h8, hE]; exact accIn j.scrOk _ _ (by omega) (by simp only [Width.bytes]; omega)) ?_)
    refine Wp.cons (Wp.store (x := env 7 + 16) (y := env 1) (BranchProof.eval_add rfl rfl) rfl
      (by rw [h16, hE]; exact accIn j.scrOk _ _ (by omega) (by simp only [Width.bytes]; omega)) ?_)
    simp only [Width.bytes]
    obtain ⟨rec0, rec8, rec16, recOut⟩ := record_words mm (env 7).toNat (env 7 + 8).toNat (env 7 + 16).toNat
      (out + 32 * env 8) (env 7 + 24) (env 1) h8 h16 _ rfl
    generalize store (store (store mm (env 7).toNat 8 (qwordByte (out + 32 * env 8))) (env 7 + 8).toNat 8
      (qwordByte (env 7 + 24))) (env 7 + 16).toNat 8 (qwordByte (env 1)) = mem3 at rec0 rec8 rec16 recOut ⊢
    rw [hE] at rec0 rec8 rec16 recOut
    -- The record lies in the scratch, past the helpers, so everything else is as it was.
    have jr : ∀ k, k + 8 ≤ 56 → readLE mem3 (job.toNat + k) 8 = readLE mem (job.toNat + k) 8 := fun k hk =>
      readLE_congr mem3 mem _ 8 fun i hi => by
        rw [Nat.add_assoc, recOut _ (by have := (outside _ (j.kept (k + i) (by omega)) (jobPad (k + i) (by omega))).2.1; omega),
          keptMM _ (by omega)]
    have ready3 : ready mem3 := walk.ready_frame mem mem3 r0 fun a nf np => by
      rw [recOut a (by have := (outside a nf np).2.1; omega), frame a (outside a nf np)]
    have hv : (readLE mem3 (env 5 + 8 * env 8).toNat 8).toNat = hs[(env 8).toNat] := by
      rw [hH, readLE_congr mem3 mm _ 8 fun i hi => recOut _ (by omega)]
      have := wordsAt_getElem mm (scr.toNat + 8 + 1024 * count.toNat) hs.length (env 8).toNat
        (by rw [wordsAt_length]; exact more)
      rw [← this]
      exact List.getElem_of_eq hW _
    obtain ⟨r, mem4, call, rc, rnode, rframe⟩ := walk.node sp' mem3 (readLE mem3 (env 5 + 8 * env 8).toNat 8)
      (out + 32 * env 8) (env 7) ready3 (by omega)
      (by rw [hO]; exact accIn j.outOk _ _ (by omega) (by omega)) (by rw [hE]; exact accIn j.scrOk _ _ (by omega) (by omega))
      (fun k hk => by rw [hO, Nat.add_assoc]; exact j.outFree _ (by omega))
      (fun k hk => by
        rw [hE]; have := j.scrFree (8 + 1536 * count.toNat + k) (by omega)
        rwa [show scr.toNat + (8 + 1536 * count.toNat + k) = scr.toNat + 8 + 1536 * count.toNat + k by omega] at this)
      (by rw [hO, hE]; have := j.apart; simp only [Apart] at this ⊢; omega)
      (by rw [hE]; exact rec0) (by rw [hE]; exact rec8) (by rw [hE, rec16, e1])
    refine Wp.cons (Wp.call (values := [plan, data, 0, b.size.toUInt64, readLE mem3 (env 5 + 8 * env 8).toNat 8, env 7])
      (mapM_six
        (by
          rw [BranchProof.eval_ld (x := env 0) rfl (by rw [e0]; simpa using rd 0 (by omega)), e0]
          have := jr 0 (by omega)
          simp only [Nat.add_zero] at this
          rw [this, j.w0])
        (eval_word (x := env 0) rfl 8 (by rw [e0]; exact rd 8 (by omega))
          (by rw [e0]; exact (jr 8 (by omega)).trans j.w1))
        rfl
        (eval_word (x := env 0) rfl 16 (by rw [e0]; exact rd 16 (by omega))
          (by rw [e0]; exact (jr 16 (by omega)).trans j.w2))
        (BranchProof.eval_ld (BranchProof.eval_add rfl (BranchProof.eval_mul rfl rfl))
          (by rw [hH]; exact accIn j.scrOk _ _ (by omega) (by omega)))
        rfl) ⟨r, mem4, call, ?_⟩)
    refine Wp.cons (Wp.set (BranchProof.eval_add rfl rfl) ?_)
    have hI1 : (env 8 + 1).toNat = (env 8).toNat + 1 := BranchProof.toNat_add_of_lt _ _ (by simp; omega)
    rw [hv] at rc rnode
    -- Outside the node just written and the scratch past the record, the walk changed nothing.
    have back : ∀ a, ¬ (out.toNat + 32 * (env 8).toNat ≤ a ∧ a < out.toNat + 32 * (env 8).toNat + 32) →
        ¬ (scr.toNat + 8 + 1536 * count.toNat ≤ a ∧ a < scr.toNat + 8 + 1536 * count.toNat + 24 + need) →
        ¬ (pad ≤ a ∧ a < pad + 1536) → mem4 a = mm a := fun a h1 h2 h3 => by
      rw [rframe a (by rw [hO]; exact h1) (by rw [hE]; omega) h3, recOut a (by omega)]
    have ap := j.apart
    have co := j.countOut
    have cs := j.countScr
    simp only [Apart] at ap co cs
    refine Wp.nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
      try simp only [assign, ↓reduceIte, Nat.reduceEqDiff]
    · exact e0
    · exact e1
    · exact e3
    · exact e4
    · exact e5
    · exact e6
    · exact e7
    · rw [hI1]; omega
    · exact fun a h => by
        rw [back a (by have := h.1; omega) (by have := h.2.1; omega) h.2.2.2]; exact frame a h
    · rw [readLE_congr mem4 mm _ 8 fun i hi => back _ (by omega) (by omega)
        (notPad _ (j.countFree i hi))]; exact cW
    · rw [wordsAt_congr fun k hk => back _ (by omega) (by omega)
        (notPad _ (by
          have := j.scrFree (8 + 1024 * count.toNat + k) (by omega)
          rwa [show scr.toNat + (8 + 1024 * count.toNat + k) = scr.toNat + 8 + 1024 * count.toNat + k by omega]
            at this))]
      exact hW
    · rw [hI1]
      cases hw : walkNode d b hs[(env 8).toNat] with
      | ok node =>
        refine .inl ⟨by rw [rc, hw]; rfl, ns ++ [node], by rw [mapM_take_succ _ _ _ more, pre, hw]; rfl, ?_⟩
        rw [nodesAt_succ, ← written, ← rnode node hw, hO,
          nodesAt_congr (mem := mm) fun k hk => back _ (by omega) (by omega) (notPad _ (j.outFree k (by omega)))]
      | error e => exact .inr ⟨e, by rw [rc, hw]; rfl, by rw [mapM_take_succ _ _ _ more, pre, hw]; rfl⟩
    · rw [hI1]; omega

end Ssz.Native.Driver.ProveProof
