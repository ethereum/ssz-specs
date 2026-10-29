import SszNative.Proofs.Driver.Prove.SpineWalk
import SszNative.Proofs.Driver.Branch.HelperIndices
import SszNative.Branch

/-!
The compiled branch builder walks to each sibling on the path, as the Lean branch does.

The walk to one node is taken as a contract here, and discharged for every type by the walk's own proof.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.ProveProof

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Driver.BranchProof

/-- The code a proving driver answers for a refusal. -/
def errCode : Err → UInt64
  | .pathIntoMixin => 12
  | .pathIntoPacked => 13
  | .pathIntoGap => 14
  | .pathPastSpine => 15
  | e => answerCode (.error e)

/-- The word a proving driver answers: zero when the nodes are written, or the code of the refusal. -/
def proveCode {α : Type} : Except Err α → UInt64
  | .ok _ => 0
  | .error e => errCode e

/-- A refusal is never answered as zero. -/
theorem errCode_ne_zero (e : Err) : errCode e ≠ 0 := by
  cases e <;> simp [errCode, answerCode]

/-- The Lean walk to the node at an index of the value an encoding holds, with the budget the branch gives it. -/
def walkNode (d : Desc) (b : ByteArray) (index : Nat) : Except Err ByteArray :=
  nodeRootAt (d.nesting + index) d b 0 b.size index

/--
The contract of the walk to one node, which the root drivers' contracts discharge.

Memory holds the type's plan, the encoding, and a filled context while a predicate on it holds, and that predicate
only reads addresses outside a free set.
The walk is called with a 24-byte record at the start of its scratch: where the node goes, the scratch past the
record, and the context.
It answers what the Lean walk answers, writes the node when there is one, and changes nothing but the node, the
scratch past the record, and the context's padding area, which is never free.
-/
structure NodeAtOk (m : Module) (w : World) (d : Desc) (b : ByteArray) (plan data ctx : UInt64) (pad : Nat)
    (ready : Memory → Prop) (free : Nat → Prop) (need room : Nat) : Prop where
  /-- One walk from the root to a node, with its record, its node and its scratch usable, free, and apart. -/
  node : ∀ (sp : Nat) (mem : Memory) (index out scr : UInt64), ready mem → w.stackLo + room ≤ sp →
    w.access out.toNat 32 = true → w.access scr.toNat (24 + need) = true →
    (∀ k < 32, free (out.toNat + k)) → (∀ k < 24 + need, free (scr.toNat + k)) →
    Apart (out.toNat, 32) (scr.toNat, 24 + need) →
    readLE mem scr.toNat 8 = out → readLE mem (scr.toNat + 8) 8 = scr + 24 → readLE mem (scr.toNat + 16) 8 = ctx →
    ∃ r mem', Calls m w "ssz_prove_node_at" sp [plan, data, 0, b.size.toUInt64, index, scr] mem r mem' ∧
      r = proveCode (walkNode d b index.toNat) ∧
      (∀ node, walkNode d b index.toNat = .ok node → readNode mem' out.toNat = node) ∧
      ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 32) → ¬ (scr.toNat + 24 ≤ a ∧ a < scr.toNat + 24 + need) →
        ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a
  /-- Writing only free addresses and the padding area keeps the plan, the encoding, and the context. -/
  ready_frame : ∀ mem mem', ready mem → (∀ a, ¬ free a → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a) →
    ready mem'
  /-- The padding area is never free. -/
  padKept : ∀ a, pad ≤ a → a < pad + 1536 → ¬ free a

/-- An accepted encoding's branch is the walk to each node its branch indices name. -/
theorem buildProof_eq {d : Desc} {b : ByteArray} (valid : validate d b = .ok ()) (index : Nat) :
    buildProof d b index = (getBranchIndices index >>= fun l => l.mapM (walkNode d b)) := by
  simp [buildProof, valid, bind, Except.bind]
  rfl

/-- The walks to the first siblings of a path, from the leaf up. -/
def branchPrefix (d : Desc) (b : ByteArray) (index k : Nat) : Except Err (List ByteArray) :=
  (List.range k).mapM fun level => walkNode d b ((index >>> level) ^^^ 1)

/-- One more sibling walked onto a prefix. -/
theorem branchPrefix_succ (d : Desc) (b : ByteArray) (index k : Nat) :
    branchPrefix d b index (k + 1) = (do
      let nodes ← branchPrefix d b index k
      let node ← walkNode d b ((index >>> k) ^^^ 1)
      pure (nodes ++ [node])) := by
  simp [branchPrefix, List.range_succ, List.mapM_append]

/-- A refused prefix refuses every longer one the same way. -/
theorem branchPrefix_error {d : Desc} {b : ByteArray} {index k : Nat} {e : Err}
    (h : branchPrefix d b index k = .error e) : ∀ n, k ≤ n → branchPrefix d b index n = .error e
  | n, le => by
    rcases Nat.eq_or_lt_of_le le with same | below
    · rw [← same]; exact h
    · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [branchPrefix_succ, branchPrefix_error h n' (by omega)]
      rfl

/-- The branch of an index of two or more is the walk to every sibling on its path. -/
theorem buildProof_of_two {d : Desc} {b : ByteArray} (valid : validate d b = .ok ()) {index : Nat}
    (two : 2 ≤ index) : buildProof d b index = branchPrefix d b index (Nat.log2 index) := by
  rw [buildProof_eq valid]
  simp [getBranchIndices, getPathIndices, gindexLength_of_two two, gindexSibling, bind, Except.bind, pure,
    Except.pure, branchPrefix, List.mapM_map, Function.comp_def]

/-- The branch of index zero is refused as naming no node. -/
theorem buildProof_zero {d : Desc} {b : ByteArray} (valid : validate d b = .ok ()) :
    buildProof d b 0 = .error (.notAGindex 0) := by
  rw [buildProof_eq valid]
  simp [getBranchIndices, getPathIndices, gindexLength, gindexDepth, bind, Except.bind]

/-- The root's branch is refused, since the root sits on none. -/
theorem buildProof_one {d : Desc} {b : ByteArray} (valid : validate d b = .ok ()) :
    buildProof d b 1 = .error .rootHasNoBranch := by
  rw [buildProof_eq valid]
  have one : Nat.log2 1 = 0 := log2_small 1 (by omega)
  simp [getBranchIndices, getPathIndices, gindexLength, gindexDepth, bind, Except.bind, one]

/-- A sibling on the path below the root is an index, never zero. -/
theorem sibling_pos {index k : Nat} (below : k < Nat.log2 index) : 1 ≤ (index >>> k) ^^^ 1 := by
  have nz : index ≠ 0 := by intro h; subst h; simp [log2_small 0 (by omega)] at below
  have big : 2 ^ (k + 1) ≤ index := (Nat.le_log2 nz).mp below
  have two : 2 ≤ index >>> k := by
    rw [Nat.shiftRight_eq_div_pow, Nat.le_div_iff_mul_le (Nat.two_pow_pos k)]
    rw [Nat.pow_succ, Nat.mul_comm] at big
    exact big
  -- Flipping the low bit back recovers the node, so the sibling is zero only for the node one.
  apply Nat.pos_of_ne_zero
  intro zero
  have back : (index >>> k) = ((index >>> k) ^^^ 1) ^^^ 1 := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [zero, Nat.zero_xor] at back
  omega

/-- Two flags joined by a bitwise and are the flag of both holding. -/
theorem and_flags (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : UInt64) &&& (if q then 1 else 0)) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] <;> decide

/-- Six evaluated arguments evaluate together. -/
theorem mapM_six {w : World} {env : Env} {mem : Memory} {a b c d e f : Ir.Expr} {x y z u v t : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) (hc : eval w env mem c = some z)
    (hd : eval w env mem d = some u) (he : eval w env mem e = some v) (hf : eval w env mem f = some t) :
    [a, b, c, d, e, f].mapM (eval w env mem) = some [x, y, z, u, v, t] := by
  simp [List.mapM_cons, ha, hb, hc, hd, he, hf]

/-- A load of a word at a constant offset from an address, known to hold a value, evaluates to it. -/
theorem eval_word {w : World} {env : Env} {mem : Memory} {a : Ir.Expr} {x : UInt64} (ha : eval w env mem a = some x)
    (n : UInt64) {v : UInt64} (acc : w.access (x.toNat + n.toNat) 8 = true) (h : readLE mem (x.toNat + n.toNat) 8 = v) :
    eval w env mem (Ir.Expr.ld (a + .lit n)) = some v := by
  rw [eval_ld_off ha acc, h]

/-- Memories agreeing on a run of nodes read the same nodes. -/
theorem nodesAt_congr {mem mem' : Memory} {a n : Nat} (h : ∀ k < 32 * n, mem' (a + k) = mem (a + k)) :
    nodesAt mem' a n = nodesAt mem a n := by
  simp only [nodesAt]
  apply List.map_congr_left
  intro j hj
  have := List.mem_range.mp hj
  exact readNode_congr fun i hi => by rw [Nat.add_assoc]; exact h _ (by omega)

/-- One more node read after a run of them. -/
theorem nodesAt_succ (mem : Memory) (a n : Nat) :
    nodesAt mem a (n + 1) = nodesAt mem a n ++ [readNode mem (a + 32 * n)] := by
  simp [nodesAt, List.range_succ]

/-- Three words written one after another: each reads back, and nothing outside them changes. -/
theorem record_words (mem : Memory) (s a8 a16 : Nat) (v0 v1 v2 : UInt64) (h8 : a8 = s + 8) (h16 : a16 = s + 16) :
    ∀ M, M = store (store (store mem s 8 (qwordByte v0)) a8 8 (qwordByte v1)) a16 8 (qwordByte v2) →
      readLE M s 8 = v0 ∧ readLE M (s + 8) 8 = v1 ∧ readLE M (s + 16) 8 = v2 ∧
        ∀ a, ¬ (s ≤ a ∧ a < s + 24) → M a = mem a := by
  intro M hM
  subst h8 h16 hM
  refine ⟨?_, ?_, readLE_store8 _ _ _, fun a h => ?_⟩
  · rw [readLE_under _ s (s + 16) 8 _ (by omega), readLE_under _ s (s + 8) 8 _ (by omega), readLE_store8]
  · rw [readLE_under _ (s + 8) (s + 16) 8 _ (by omega), readLE_store8]
  · rw [store_outside _ _ _ _ _ (by omega), store_outside _ _ _ _ _ (by omega), store_outside _ _ _ _ _ (by omega)]

/-- A branch-building job in memory: its six words, the branch and scratch usable and free, and apart. -/
structure ProveJob (w : World) (free : Nat → Prop) (mem : Memory) (job plan data size index out scr : UInt64)
    (count need : Nat) : Prop where
  /-- The job's words are usable. -/
  words : w.access job.toNat 48 = true
  /-- The job's words are not free, so nothing the walk writes reaches them. -/
  kept : ∀ k < 48, ¬ free (job.toNat + k)
  /-- The plan's address. -/
  w0 : readLE mem job.toNat 8 = plan
  /-- The encoding's address. -/
  w1 : readLE mem (job.toNat + 8) 8 = data
  /-- The encoding's size. -/
  w2 : readLE mem (job.toNat + 16) 8 = size
  /-- The generalized index. -/
  w3 : readLE mem (job.toNat + 24) 8 = index
  /-- Where the nodes go. -/
  w4 : readLE mem (job.toNat + 32) 8 = out
  /-- The scratch area's address. -/
  w5 : readLE mem (job.toNat + 40) 8 = scr
  /-- The nodes' place is usable. -/
  outOk : w.access out.toNat (32 * count) = true
  /-- The scratch area is usable. -/
  scrOk : w.access scr.toNat (24 + need) = true
  /-- The nodes' place is free memory. -/
  outFree : ∀ k < 32 * count, free (out.toNat + k)
  /-- The scratch area is free memory. -/
  scrFree : ∀ k < 24 + need, free (scr.toNat + k)
  /-- The nodes' place misses the scratch area. -/
  apart : Apart (out.toNat, 32 * count) (scr.toNat, 24 + need)

/-- The branch loop: fixed arguments, the path node and level reached, the frame, and the nodes walked so far. -/
private def BranchInv (d : Desc) (b : ByteArray) (mem : Memory) (job ctx index out scr : UInt64) (need pad : Nat)
    (env : Env) (mem' : Memory) : Prop :=
  env 0 = job ∧ env 1 = ctx ∧ env 3 = scr ∧ env 4 = index ∧ (env 5).toNat = Nat.log2 index.toNat ∧
    (env 7).toNat ≤ Nat.log2 index.toNat ∧ (env 6).toNat = index.toNat >>> (env 7).toNat ∧
    (∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 32 * Nat.log2 index.toNat) →
      ¬ (scr.toNat ≤ a ∧ a < scr.toNat + 24 + need) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a) ∧
    ((env 2 = 0 ∧ ∃ nodes, branchPrefix d b index.toNat (env 7).toNat = .ok nodes ∧
        nodesAt mem' out.toNat (env 7).toNat = nodes) ∨
      ∃ e, env 2 = errCode e ∧ branchPrefix d b index.toNat (env 7).toNat = .error e)

/--
A call of the branch builder answers what the Lean branch answers, and writes the branch when there is one.

The walk to each node is the contract above, and the encoding is one validation accepts.
Only the branch's place, the scratch area, and the padding area change.
-/
theorem prove_branch_calls {m : Module} {w : World} {d : Desc} {b : ByteArray} {plan data ctx : UInt64}
    {pad : Nat} {ready : Memory → Prop} {free : Nat → Prop} {need room : Nat}
    (hf : m.fns.lookup "ssz_prove_branch" = some ProveBranch.fn)
    (hl : m.fns.lookup "ssz_branch_level" = some Level.fn)
    (walk : NodeAtOk m w d b plan data ctx pad ready free need room) (valid : validate d b = .ok ()) {sp : Nat}
    (deep : w.stackLo + 8 + 8 * ProveBranch.fn.frame + room + 32 ≤ sp)
    (job index out scr : UInt64) (mem : Memory) (r0 : ready mem)
    (j : ProveJob w free mem job plan data b.size.toUInt64 index out scr (Nat.log2 index.toNat) need)
    (jobPad : ∀ k < 48, ¬ (pad ≤ job.toNat + k ∧ job.toNat + k < pad + 1536)) :
    ∃ r mem', Calls m w "ssz_prove_branch" sp [job, ctx] mem r mem' ∧
      r = proveCode (buildProof d b index.toNat) ∧
      (∀ nodes, buildProof d b index.toNat = .ok nodes →
        nodesAt mem' out.toNat (Nat.log2 index.toNat) = nodes) ∧
      ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 32 * Nat.log2 index.toNat) →
        ¬ (scr.toNat ≤ a ∧ a < scr.toNat + 24 + need) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a := by
  have nLt : Nat.log2 index.toNat < 64 := log2_lt_64 index
  have bo := access_bound j.outOk
  have bs := access_bound j.scrOk
  have bj := access_bound j.words
  -- An address that is not free lies outside the branch and the scratch.
  have outside : ∀ a, ¬ free a → ¬ (out.toNat ≤ a ∧ a < out.toNat + 32 * Nat.log2 index.toNat) ∧
      ¬ (scr.toNat ≤ a ∧ a < scr.toNat + 24 + need) := fun a nf =>
    ⟨fun h => nf (by have := j.outFree (a - out.toNat) (by omega); rwa [Nat.add_sub_cancel' h.1] at this),
      fun h => nf (by have := j.scrFree (a - scr.toNat) (by omega); rwa [Nat.add_sub_cancel' h.1] at this)⟩
  let Post := fun (r : UInt64) (mem' : Memory) =>
    r = proveCode (buildProof d b index.toNat) ∧
      (∀ nodes, buildProof d b index.toNat = .ok nodes →
        nodesAt mem' out.toNat (Nat.log2 index.toNat) = nodes) ∧
      ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 32 * Nat.log2 index.toNat) →
        ¬ (scr.toNat ≤ a ∧ a < scr.toNat + 24 + need) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a
  suffices body : Wp m w (sp - 8 - 8 * ProveBranch.fn.frame) ProveBranch.fn.body (entryEnv [job, ctx]) mem
      fun env mem' => ∃ r, eval w env mem' ProveBranch.fn.result = some r ∧ Post r mem' by
    exact Calls.of_wp hf (by omega) rfl body
  have spRoom : w.stackLo + room + 32 ≤ sp - 8 - 8 * ProveBranch.fn.frame := by omega
  generalize sp - 8 - 8 * ProveBranch.fn.frame = sp' at spRoom ⊢
  simp only [ProveBranch.fn]
  have rd : ∀ k, k + 8 ≤ 48 → w.access (job.toNat + k) 8 = true := fun k hk => access_sub j.words hk
  -- The index and the scratch are read from the job.
  refine Wp.cons (Wp.set rfl ?_)
  refine Wp.cons (Wp.set (eval_word (x := job) rfl 24 (rd 24 (by omega)) j.w3) ?_)
  refine Wp.cons (Wp.set (eval_word (x := job) rfl 40 (rd 40 (by omega)) j.w5) ?_)
  refine Wp.ite (eval_eq rfl rfl) (fun z => ?_) (fun nz => ?_)
  · -- Index zero names no node.
    have z' : index = 0 := by simpa [assign] using z
    refine Wp.cons (Wp.set rfl ?_)
    repeat refine Wp.nil ?_
    refine ⟨_, rfl, ?_, fun nodes h => ?_, fun _ _ _ _ => rfl⟩
    · simp [assign, z', buildProof_zero valid, proveCode, errCode, answerCode]
    · simp [z', buildProof_zero valid] at h
  have nz' : index ≠ 0 := by simpa [assign] using nz
  refine Wp.ite (eval_eq rfl rfl) (fun o => ?_) (fun no => ?_)
  · -- The root has no branch.
    have o' : index = 1 := by simpa [assign] using o
    refine Wp.cons (Wp.set rfl ?_)
    repeat refine Wp.nil ?_
    refine ⟨_, rfl, ?_, fun nodes h => ?_, fun _ _ _ _ => rfl⟩
    · simp [assign, o', buildProof_one valid, proveCode, errCode, answerCode]
    · simp [o', buildProof_one valid] at h
  have no' : index ≠ 1 := by simpa [assign] using no
  have two : 2 ≤ index.toNat := by
    have a : index.toNat ≠ 0 := fun h => nz' (UInt64.toNat_inj.mp (by simpa using h))
    have c : index.toNat ≠ 1 := fun h => no' (UInt64.toNat_inj.mp (by simpa using h))
    omega
  -- The branch's length is the index's level, and the walk starts at the index itself.
  refine Wp.cons (Wp.call (values := [index]) rfl ⟨_, mem, level_calls hl (by omega) index mem, ?_⟩)
  refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons ?_))))
  refine Wp.loop (BranchInv d b mem job ctx index out scr need pad)
    (fun env _ => Nat.log2 index.toNat - (env 7).toNat)
    ⟨by simp [assign, entryEnv], by simp [assign, entryEnv], by simp [assign], by simp [assign],
      by simp only [assign, ↓reduceIte, Nat.reduceEqDiff]; exact toNat_ofNat_of_lt _ (by omega), by simp [assign],
      by simp [assign],
      fun _ _ _ _ => rfl, .inl ⟨by simp [assign], [], by simp [assign, branchPrefix]; rfl,
        by simp [assign, nodesAt]⟩⟩ ?_
  intro env mm ⟨e0, e1, e3, e4, e5, jle, e6, frame, st⟩
  refine ⟨_, eval_and (eval_lt rfl rfl) (eval_eq rfl rfl), fun go => ?_, fun stop => ?_⟩
  rotate_left
  · -- The loop ends with the last sibling walked or the first refusal.
    rw [and_flags] at stop
    have done := flag_eq stop
    rw [e5] at done
    repeat refine Wp.nil ?_
    refine ⟨env 2, rfl, ?_, fun nodes h => ?_, frame⟩
    · rw [buildProof_of_two valid two]
      rcases st with ⟨r0', ns, pre, _⟩ | ⟨e, re, pre⟩
      · have last : Nat.log2 index.toNat = (env 7).toNat := by
          have : ¬ ((env 7).toNat < Nat.log2 index.toNat) := fun h => done ⟨h, r0'⟩
          omega
        rw [last, pre, r0']; rfl
      · rw [re, branchPrefix_error pre _ jle]; rfl
    · rw [buildProof_of_two valid two] at h
      rcases st with ⟨r0', ns, pre, written⟩ | ⟨e, re, pre⟩
      · have last : Nat.log2 index.toNat = (env 7).toNat := by
          have : ¬ ((env 7).toNat < Nat.log2 index.toNat) := fun h => done ⟨h, r0'⟩
          omega
        rw [last, pre] at h
        cases h
        rw [last]; exact written
      · rw [branchPrefix_error pre _ jle] at h; cases h
  · -- One more sibling: its record is written, then the walk to it.
    rw [and_flags] at go
    obtain ⟨more, r0'⟩ := flag_ne go
    rw [e5] at more
    rcases st with ⟨_, ns, pre, written⟩ | ⟨e, re, _⟩
    rotate_left
    · exact absurd (re.symm.trans r0') (errCode_ne_zero e)
    have hO : (out + 32 * env 7).toNat = out.toNat + 32 * (env 7).toNat := by
      rw [toNat_addr _ _ _ (by simp; omega)]; simp
    have h8 : (env 3 + 8).toNat = scr.toNat + 8 := by
      rw [toNat_add_of_lt _ _ (by rw [e3]; simp; omega), e3]; simp
    have h16 : (env 3 + 16).toNat = scr.toNat + 16 := by
      rw [toNat_add_of_lt _ _ (by rw [e3]; simp; omega), e3]; simp
    have keptMM : ∀ k < 48, mm (job.toNat + k) = mem (job.toNat + k) := fun k hk =>
      frame _ (outside _ (j.kept k hk)).1 (outside _ (j.kept k hk)).2 (jobPad k hk)
    refine Wp.cons (Wp.store (x := env 3) (y := out + 32 * env 7) rfl
      (eval_add (eval_word (x := env 0) rfl 32 (by rw [e0]; exact rd 32 (by omega))
        (by rw [e0, show (32 : UInt64).toNat = 32 from rfl,
          readLE_congr mm mem _ 8 (fun i hi => by rw [Nat.add_assoc]; exact keptMM _ (by omega))]; exact j.w4))
        (eval_mul rfl rfl))
      (by rw [e3]; exact access_prefix j.scrOk (by simp only [Width.bytes]; omega)) ?_)
    refine Wp.cons (Wp.store (x := env 3 + 8) (y := env 3 + 24) (eval_add rfl rfl) (eval_add rfl rfl)
      (by rw [h8]; exact access_sub j.scrOk (by simp only [Width.bytes]; omega)) ?_)
    refine Wp.cons (Wp.store (x := env 3 + 16) (y := env 1) (eval_add rfl rfl) rfl
      (by rw [h16]; exact access_sub j.scrOk (by simp only [Width.bytes]; omega)) ?_)
    simp only [Width.bytes]
    obtain ⟨rec0, rec8, rec16, recOut⟩ := record_words mm (env 3).toNat (env 3 + 8).toNat (env 3 + 16).toNat (out + 32 * env 7) (env 3 + 24) (env 1)
      (by rw [h8, e3]) (by rw [h16, e3]) _ rfl
    generalize store (store (store mm (env 3).toNat 8 (qwordByte (out + 32 * env 7))) (env 3 + 8).toNat 8
      (qwordByte (env 3 + 24))) (env 3 + 16).toNat 8 (qwordByte (env 1)) = mem3 at rec0 rec8 rec16 recOut ⊢
    rw [e3] at rec0 rec8 rec16 recOut
    -- The record lies in the scratch, so the job's words and everything not free are as they were.
    have jr : ∀ k, k + 8 ≤ 48 → readLE mem3 (job.toNat + k) 8 = readLE mem (job.toNat + k) 8 := fun k hk =>
      readLE_congr mem3 mem _ 8 fun i hi => by
        rw [Nat.add_assoc, recOut _ (fun h => j.kept (k + i) (by omega) (by
          have := j.scrFree (job.toNat + (k + i) - scr.toNat) (by omega)
          rwa [Nat.add_sub_cancel' h.1] at this)), keptMM _ (by omega)]
    have ready3 : ready mem3 := walk.ready_frame mem mem3 r0 fun a nf np => by
      rw [recOut a (by have := (outside a nf).2; omega), frame a (outside a nf).1 (outside a nf).2 np]
    obtain ⟨r, mem4, call, rc, rnode, rframe⟩ := walk.node sp' mem3 (env 6 ^^^ 1) (out + 32 * env 7) (env 3)
      ready3 (by omega) (by rw [hO]; exact access_sub j.outOk (by omega)) (by rw [e3]; exact j.scrOk)
      (fun k hk => by rw [hO, Nat.add_assoc]; exact j.outFree _ (by omega))
      (fun k hk => by rw [e3]; exact j.scrFree k hk)
      (by rw [hO, e3]; have := j.apart; simp only [Apart] at this ⊢; omega)
      (by rw [e3]; exact rec0) (by rw [e3]; exact rec8) (by rw [e3, rec16, e1])
    refine Wp.cons (Wp.call (values := [plan, data, 0, b.size.toUInt64, env 6 ^^^ 1, env 3])
      (mapM_six
        (by
          rw [eval_ld (x := env 0) rfl (by rw [e0]; simpa using rd 0 (by omega)), e0]
          have := jr 0 (by omega)
          simp only [Nat.add_zero] at this
          rw [this, j.w0])
        (eval_word (x := env 0) rfl 8 (by rw [e0]; exact rd 8 (by omega))
          (by rw [e0]; exact (jr 8 (by omega)).trans j.w1))
        rfl
        (eval_word (x := env 0) rfl 16 (by rw [e0]; exact rd 16 (by omega))
          (by rw [e0]; exact (jr 16 (by omega)).trans j.w2))
        (eval_xor rfl rfl) rfl) ⟨r, mem4, call, ?_⟩)
    refine Wp.cons (Wp.set (eval_shr1 rfl) (Wp.cons (Wp.set (eval_add rfl rfl) ?_)))
    have hJ : (env 7 + 1).toNat = (env 7).toNat + 1 := toNat_add_of_lt _ _ (by simp; omega)
    have hN : (env 6 >>> (1 : Nat).toUInt64).toNat = index.toNat >>> ((env 7).toNat + 1) := by
      rw [toNat_shr_one, e6, Nat.shiftRight_succ]
    have hS : (env 6 ^^^ 1).toNat = (index.toNat >>> (env 7).toNat) ^^^ 1 := by
      rw [UInt64.toNat_xor, e6]; rfl
    rw [hS] at rc rnode
    -- Outside the node just written and the scratch, the walk changed nothing.
    have back : ∀ a, ¬ (out.toNat + 32 * (env 7).toNat ≤ a ∧ a < out.toNat + 32 * (env 7).toNat + 32) →
        ¬ (scr.toNat ≤ a ∧ a < scr.toNat + 24 + need) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem4 a = mm a :=
      fun a h1 h2 h3 => by rw [rframe a (by rw [hO]; exact h1) (by rw [e3]; omega) h3, recOut a (by omega)]
    refine Wp.nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;> try simp only [assign, ↓reduceIte, Nat.reduceEqDiff]
    · exact e0
    · exact e1
    · exact e3
    · exact e4
    · exact e5
    · rw [hJ]; omega
    · rw [hN, hJ]
    · exact fun a h1 h2 h3 => by rw [back a (by omega) h2 h3]; exact frame a h1 h2 h3
    · rw [hJ]
      cases hw : walkNode d b ((index.toNat >>> (env 7).toNat) ^^^ 1) with
      | ok node =>
        refine .inl ⟨by rw [rc, hw]; rfl, ns ++ [node], by rw [branchPrefix_succ, pre, hw]; rfl, ?_⟩
        rw [nodesAt_succ, ← written, ← rnode node hw, hO,
          nodesAt_congr (mem := mm) fun k hk => back _ (by omega) (by have := j.apart; simp only [Apart] at this; omega)
            (fun hp => walk.padKept _ hp.1 hp.2 (j.outFree k (by omega)))]
      | error e => exact .inr ⟨e, by rw [rc, hw]; rfl, by rw [branchPrefix_succ, pre, hw]; rfl⟩
    · rw [hJ]; omega

