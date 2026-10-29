import SszNative.Proofs.Driver.Branch.Hashing

/-!
The compiled branch verifier answers what the Lean verifier answers.

The verifier reads its job, refuses an index of zero or one, compares the branch length with the index's depth, then
climbs one level per branch node.
The climbing node alternates between the two halves of the scratch area, so a parent never overwrites its children.
-/

namespace Ssz.Native.Driver.BranchProof

open Ssz.Native.Ir Ssz.Native.Asm

/-- Arrays compare equal exactly when they are. -/
theorem beq_eq_decide (a b : ByteArray) : (a == b) = decide (a = b) := by
  rw [beq_data]
  by_cases h : a = b
  · subst h; simp
  · have : a.data ≠ b.data := fun e => h (ByteArray.ext e)
    simp [h, this]

/-- A node read from memory passes the width check. -/
theorem checkNode_readNode (mem : Memory) (a : Nat) : checkNode (readNode mem a) = .ok () := by
  simp [checkNode, readNode_size, bytesPerChunk]

/-- A list of nodes passes the width check when each one does. -/
theorem checkNodes_of (nodes : List ByteArray) (h : ∀ n ∈ nodes, n.size = 32) : checkNodes nodes = .ok () := by
  induction nodes with
  | nil => rfl
  | cons n rest ih =>
    simp only [checkNodes, checkNode, h n (by simp), bytesPerChunk, bind, Except.bind]
    exact ih (fun x hx => h x (by simp [hx]))

/-- Nodes read from memory pass the width check. -/
theorem checkNodes_nodesAt (mem : Memory) (a n : Nat) : checkNodes (nodesAt mem a n) = .ok () :=
  checkNodes_of _ (by simp [nodesAt, readNode_size])

/-- Nodes read from memory, as many as asked. -/
theorem nodesAt_length (mem : Memory) (a n : Nat) : (nodesAt mem a n).length = n := by
  simp [nodesAt]

/-- The verdict once the index has a depth equal to the branch length: the climbed node against the root. -/
theorem verifyMerkleProof_ok (leaf root : ByteArray) (proof : List ByteArray) (index : Nat)
    (depth : gindexLength index = .ok proof.length) (leafSize : leaf.size = 32)
    (sizes : ∀ n ∈ proof, n.size = 32) :
    verifyMerkleProof leaf proof index root = .ok (decide (climbBranch index 0 leaf proof = root)) := by
  simp [verifyMerkleProof, depth, checkNode, leafSize, bytesPerChunk, checkNodes_of proof sizes, beq_eq_decide,
    bind, Except.bind, pure, Except.pure]

/-- A climb past every branch node ends on the node it carries. -/
theorem climbBranch_nil (index level : Nat) (node : ByteArray) : climbBranch index level node [] = node := rfl

/-- A climb takes the next branch node into the parent, one level up. -/
theorem climbBranch_cons (index level : Nat) (node sibling : ByteArray) (rest : List ByteArray) :
    climbBranch index level node (sibling :: rest) =
      climbBranch index (level + 1)
        (if gindexBit index level then combine sibling node else combine node sibling) rest := rfl

/-- A branch job in memory: its six words, the regions they name usable and free, the scratch apart from all. -/
structure BranchJob (w : World) (free : Nat → Prop) (mem : Memory) (job leaf proof count index root scratch : UInt64) :
    Prop where
  /-- The job's words are usable. -/
  words : w.access job.toNat 48 = true
  /-- The leaf's address. -/
  w0 : readLE mem job.toNat 8 = leaf
  /-- The branch's address. -/
  w1 : readLE mem (job.toNat + 8) 8 = proof
  /-- The branch's node count. -/
  w2 : readLE mem (job.toNat + 16) 8 = count
  /-- The leaf's generalized index. -/
  w3 : readLE mem (job.toNat + 24) 8 = index
  /-- The root's address. -/
  w4 : readLE mem (job.toNat + 32) 8 = root
  /-- The scratch area's address. -/
  w5 : readLE mem (job.toNat + 40) 8 = scratch
  /-- The leaf is usable. -/
  leafOk : w.access leaf.toNat 32 = true
  /-- The branch is usable. -/
  proofOk : w.access proof.toNat (32 * count.toNat) = true
  /-- The root is usable. -/
  rootOk : w.access root.toNat 32 = true
  /-- The scratch area is usable. -/
  scratchOk : w.access scratch.toNat 64 = true
  /-- The leaf is free memory, which hashing leaves alone. -/
  leafFree : ∀ k < 32, free (leaf.toNat + k)
  /-- The branch is free memory. -/
  proofFree : ∀ k < 32 * count.toNat, free (proof.toNat + k)
  /-- The root is free memory. -/
  rootFree : ∀ k < 32, free (root.toNat + k)
  /-- The scratch area is free memory. -/
  scratchFree : ∀ k < 64, free (scratch.toNat + k)
  /-- The scratch area misses the leaf. -/
  leafApart : Apart (scratch.toNat, 64) (leaf.toNat, 32)
  /-- The scratch area misses the branch. -/
  proofApart : Apart (scratch.toNat, 64) (proof.toNat, 32 * count.toNat)
  /-- The scratch area misses the root. -/
  rootApart : Apart (scratch.toNat, 64) (root.toNat, 32)

/-- An index of zero is refused before anything else. -/
theorem verifyMerkleProof_zero (leaf root : ByteArray) (proof : List ByteArray) :
    verifyMerkleProof leaf proof 0 root = .error (.notAGindex 0) := by
  simp [verifyMerkleProof, gindexLength, gindexDepth, bind, Except.bind]

/-- The root's index is refused before anything else. -/
theorem verifyMerkleProof_one (leaf root : ByteArray) (proof : List ByteArray) :
    verifyMerkleProof leaf proof 1 root = .error .rootHasNoBranch := by
  have one : Nat.log2 1 = 0 := log2_small 1 (by omega)
  simp [verifyMerkleProof, gindexLength, gindexDepth, bind, Except.bind, one]

/-- A branch of the wrong length is refused. -/
theorem verifyMerkleProof_length (leaf root : ByteArray) (proof : List ByteArray) {index : Nat} (two : 2 ≤ index)
    (ne : Nat.log2 index ≠ proof.length) :
    verifyMerkleProof leaf proof index root = .error (.branchLength (Nat.log2 index) proof.length) := by
  simp [verifyMerkleProof, gindexLength_of_two two, Ne.symm ne, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

/-- The climb: fixed arguments, the turns left, the climbing node's place, and the climb still owed. -/
private def ClimbInv (ready : Memory → Prop) (free : Nat → Prop) (mem : Memory)
    (job ctx leaf proof count index root scratch : UInt64) (env : Env) (mem' : Memory) : Prop :=
  env 0 = job ∧ env 1 = ctx ∧ env 2 = leaf ∧ env 3 = proof ∧ env 4 = count ∧ env 5 = index ∧ env 6 = root ∧
    env 7 = scratch ∧ (env 12).toNat ≤ count.toNat ∧ (env 9).toNat = index.toNat / 2 ^ (env 12).toNat ∧
    (env 10).toNat = (if (env 12).toNat = 0 then leaf.toNat else scratch.toNat + 32 * (((env 12).toNat + 1) % 2)) ∧
    env 14 = 0 ∧ ready mem' ∧
    (∀ a, free a → ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + 64) → mem' a = mem a) ∧
    climbBranch index.toNat 0 (readNode mem leaf.toNat) (nodesAt mem proof.toNat count.toNat) =
      climbBranch index.toNat (env 12).toNat (readNode mem' (env 10).toNat)
        ((nodesAt mem proof.toNat count.toNat).drop (env 12).toNat)

/-- The nodes from a position on are the node there, then those after it. -/
theorem nodesAt_drop (mem : Memory) (a n l : Nat) (h : l < n) :
    (nodesAt mem a n).drop l = readNode mem (a + 32 * l) :: (nodesAt mem a n).drop (l + 1) := by
  rw [List.drop_eq_getElem_cons (by simp [nodesAt]; omega)]
  simp [nodesAt]

/-- Whether the index turns right at a level, read from the turns left after that many halvings. -/
theorem gindexBit_eq (index level : Nat) : gindexBit index level = decide (index / 2 ^ level % 2 = 1) := by
  simp [gindexBit, Nat.testBit_eq_decide_div_mod_eq]

/-- Two ranges apart stay apart for any ranges inside them. -/
theorem Apart.sub {a n b k c j : Nat} (h : Apart (a, n) (b, k)) (hc : a ≤ c ∧ c + j ≤ a + n) :
    Apart (c, j) (b, k) := by
  simp only [Apart] at h ⊢; omega

/-- Apartness either way round. -/
theorem Apart.symm {x y : Nat × Nat} (h : Apart x y) : Apart y x := by
  simp only [Apart] at h ⊢; omega

/-- One pass of the climb: a parent hashed into the other scratch half, one level up. -/
theorem climb_pass {m : Module} {w : World} {ctx : UInt64} {ready : Memory → Prop} {free : Nat → Prop}
    {room : Nat} (hash : PairHashing m w ctx ready free room) {sp : Nat} (deep : w.stackLo + room ≤ sp)
    {mem : Memory} {job leaf proof count index root scratch : UInt64}
    (j : BranchJob w free mem job leaf proof count index root scratch) (env : Env) (mem' : Memory)
    (inv : ClimbInv ready free mem job ctx leaf proof count index root scratch env mem')
    (more : (env 12).toNat < count.toNat) :
    Wp m w sp (.block [Ir.Stmt.assign VerifyBranch.out (Ir.Expr.var 7 + 32 * (Ir.Expr.var 12 &&& 1)),
      Ir.Stmt.ifElse (Ir.Expr.ne (Ir.Expr.var 9 &&& 1) 0)
        [Ir.Stmt.callInto VerifyBranch.got "ssz_hash_columns"
          [Ir.Expr.var 11, Ir.Expr.var 3 + 32 * Ir.Expr.var 12, Ir.Expr.var 10, 1, Ir.Expr.var 1]]
        [Ir.Stmt.callInto VerifyBranch.got "ssz_hash_columns"
          [Ir.Expr.var 11, Ir.Expr.var 10, Ir.Expr.var 3 + 32 * Ir.Expr.var 12, 1, Ir.Expr.var 1]],
      Ir.Stmt.assign VerifyBranch.status (Ir.Expr.var 14 ||| Ir.Expr.var 13),
      Ir.Stmt.assign VerifyBranch.cur (Ir.Expr.var 11),
      Ir.Stmt.assign VerifyBranch.turns (.shr (Ir.Expr.var 9) 1),
      Ir.Stmt.assign VerifyBranch.level (Ir.Expr.var 12 + 1)]) env mem'
      (fun env' mem'' => ClimbInv ready free mem job ctx leaf proof count index root scratch env' mem'' ∧
        count.toNat - (env' 12).toNat < count.toNat - (env 12).toNat) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, le, turns, cur, status, rd, frame, climb⟩ := inv
  -- The places the pass reads and writes, as numbers.
  have bs := access_bound j.scratchOk
  have bp := access_bound j.proofOk
  have bl := access_bound j.leafOk
  have outVal : (env 7 + 32 * (env 12 &&& 1)).toNat = scratch.toNat + 32 * ((env 12).toNat % 2) := by
    have low : (env 12 &&& 1).toNat = (env 12).toNat % 2 := toNat_and_one _
    have : (32 * (env 12 &&& 1)).toNat = 32 * ((env 12).toNat % 2) := by
      rw [toNat_mul_of_lt _ _ (by rw [low]; simp; omega), low]; simp
    rw [toNat_add_of_lt _ _ (by rw [this, e7]; omega), this, e7]
  have sibVal : (env 3 + 32 * env 12).toNat = proof.toNat + 32 * (env 12).toNat := by
    rw [e3, toNat_addr _ _ _ (by simp; omega)]; simp
  -- The output, the branch node, and the climbing node are usable, and the output misses both.
  have outOk : w.access (env 7 + 32 * (env 12 &&& 1)).toNat 32 = true := by
    rw [outVal]; exact access_sub j.scratchOk (by omega)
  have outFree : ∀ k < 32, free ((env 7 + 32 * (env 12 &&& 1)).toNat + k) := by
    intro k hk; rw [outVal, Nat.add_assoc]; exact j.scratchFree _ (by omega)
  have sibOk : w.access (env 3 + 32 * env 12).toNat 32 = true := by
    rw [sibVal]; exact access_sub j.proofOk (by omega)
  have curOk : w.access (env 10).toNat 32 = true := by
    rw [cur]; split
    · exact j.leafOk
    · exact access_sub j.scratchOk (by omega)
  have sibFree : ∀ k < 32, free ((env 3 + 32 * env 12).toNat + k) := by
    intro k hk; rw [sibVal, Nat.add_assoc]; exact j.proofFree _ (by omega)
  have curFree : ∀ k < 32, free ((env 10).toNat + k) := by
    intro k hk; rw [cur]; split
    · exact j.leafFree k hk
    · rw [Nat.add_assoc]; exact j.scratchFree _ (by omega)
  have sibApart : Apart ((env 7 + 32 * (env 12 &&& 1)).toNat, 32) ((env 3 + 32 * env 12).toNat, 32) := by
    have := j.proofApart
    rw [outVal, sibVal]; simp only [Apart] at this ⊢; omega
  have curApart : Apart ((env 7 + 32 * (env 12 &&& 1)).toNat, 32) ((env 10).toNat, 32) := by
    have := j.leafApart
    rw [outVal, cur]; split
    · simp only [Apart] at this ⊢; omega
    · simp only [Apart]; omega
  -- The branch node read now is the one the job named, since only the scratch area was written.
  have sibNode : readNode mem' (env 3 + 32 * env 12).toNat = readNode mem (proof.toNat + 32 * (env 12).toNat) := by
    rw [sibVal]
    apply readNode_congr
    intro k hk
    have := j.proofApart
    exact frame _ (by rw [Nat.add_assoc]; exact j.proofFree _ (by omega)) (by simp only [Apart] at this; omega)
  -- The bit the pass tests is the index's turn at this level.
  have bitVal : (env 9 &&& 1).toNat = index.toNat / 2 ^ (env 12).toNat % 2 := by
    rw [toNat_and_one, turns]
  -- Both sides of the branch hash a pair, then run the same updates.
  have rest : ∀ (mem'' : Memory), ready mem'' →
      (∀ a, free a → ¬ ((env 7 + 32 * (env 12 &&& 1)).toNat ≤ a ∧ a < (env 7 + 32 * (env 12 &&& 1)).toNat + 32) →
        mem'' a = mem' a) →
      readNode mem'' (env 7 + 32 * (env 12 &&& 1)).toNat =
        (if gindexBit index.toNat (env 12).toNat then combine (readNode mem (proof.toNat + 32 * (env 12).toNat))
          (readNode mem' (env 10).toNat)
        else combine (readNode mem' (env 10).toNat) (readNode mem (proof.toNat + 32 * (env 12).toNat))) →
      Wp m w sp (.block [Ir.Stmt.assign VerifyBranch.status (Ir.Expr.var 14 ||| Ir.Expr.var 13),
        Ir.Stmt.assign VerifyBranch.cur (Ir.Expr.var 11),
        Ir.Stmt.assign VerifyBranch.turns (.shr (Ir.Expr.var 9) 1),
        Ir.Stmt.assign VerifyBranch.level (Ir.Expr.var 12 + 1)])
        (assign (assign env 11 (env 7 + 32 * (env 12 &&& 1))) 13 0) mem''
        (fun env' mem'' => ClimbInv ready free mem job ctx leaf proof count index root scratch env' mem'' ∧
          count.toNat - (env' 12).toNat < count.toNat - (env 12).toNat) := by
    intro mem'' rd'' frame'' parent
    have next : (env 12 + 1).toNat = (env 12).toNat + 1 := by
      have := count.toNat_lt
      rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
    refine Wp.cons (Wp.set (eval_or rfl rfl) (Wp.cons (Wp.set rfl (Wp.cons (Wp.set (eval_shr1 rfl)
      (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨?_, ?_⟩)))))))) <;>
      simp only [ClimbInv, assign, ↓reduceIte, Nat.reduceEqDiff, next]
    · refine ⟨e0, e1, e2, e3, e4, e5, e6, e7, by omega, ?_, ?_, by rw [status]; rfl, rd'', ?_, ?_⟩
      · rw [toNat_shr_one, turns, Nat.div_div_eq_div_mul, Nat.pow_succ]
      · rw [outVal]; omega
      · intro a fa outside
        rw [frame'' a fa (by rw [outVal]; omega), frame a fa outside]
      · rw [climb, nodesAt_drop _ _ _ _ more, climbBranch_cons, ← parent]
    · omega
  -- The output address goes into its variable, then the bit picks which side the climbing node joins.
  refine Wp.cons (Wp.set (eval_add rfl (eval_mul rfl (eval_and rfl rfl))) (Wp.cons ?_))
  refine Wp.ite (eval_ne (eval_and rfl rfl) rfl) (fun hset => ?_) (fun hclr => ?_)
  · -- A set bit: the branch node on the left.
    have bit : gindexBit index.toNat (env 12).toNat = true := by
      rw [gindexBit_eq, ← bitVal]
      have nz : env 9 &&& 1 ≠ 0 := by
        intro z
        simp only [assign, ↓reduceIte, Nat.reduceEqDiff] at hset
        rw [if_pos z] at hset
        exact hset rfl
      have : (env 9 &&& 1).toNat ≠ 0 := fun h => nz (UInt64.toNat_inj.mp (by rw [h]; rfl))
      have small := Nat.mod_lt (env 9).toNat (show 0 < 2 by decide)
      rw [toNat_and_one] at this
      simp only [decide_eq_true_eq]
      omega
    obtain ⟨mem'', call, rd'', node, frame''⟩ := hash.pair_node rd deep outOk sibOk curOk outFree sibFree curFree sibApart curApart
    rw [← e1] at call
    refine Wp.call (values := [_, _, _, 1, _]) rfl ⟨0, mem'', call, rest mem'' rd'' frame'' ?_⟩
    rw [node, bit, if_pos rfl, sibNode]
  · -- A clear bit: the branch node on the right.
    have bit : gindexBit index.toNat (env 12).toNat = false := by
      rw [gindexBit_eq, ← bitVal]
      have : env 9 &&& 1 = 0 := by
        by_cases z : env 9 &&& 1 = 0
        · exact z
        · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, if_neg z] at hclr
          exact absurd hclr (by decide)
      rw [this]; simp
    obtain ⟨mem'', call, rd'', node, frame''⟩ :=
      hash.pair_node rd deep outOk curOk sibOk outFree curFree sibFree curApart sibApart
    rw [← e1] at call
    refine Wp.call (values := [_, _, _, 1, _]) rfl ⟨0, mem'', call, rest mem'' rd'' frame'' ?_⟩
    rw [node, bit, if_neg (by decide), sibNode]

/-- The verdict on a climbed branch, as the word the verifier answers. -/
theorem answerCode_decide (p : Prop) [Decidable p] :
    answerCode (.ok (decide p)) = if p then 1 else 0 := by
  by_cases h : p <;> simp [h, answerCode]

/--
The compiled branch verifier answers what the Lean verifier answers on the leaf, branch, index and root its job
names.

It changes no free memory outside its scratch area, and keeps the hashing context.
-/
theorem verify_branch_calls {m : Module} {w : World} {ctx : UInt64} {ready : Memory → Prop} {free : Nat → Prop}
    {room : Nat} (hv : m.fns.lookup "ssz_verify_branch" = some VerifyBranch.fn)
    (hl : m.fns.lookup "ssz_branch_level" = some Level.fn) (hs : m.fns.lookup "ssz_branch_same" = some Same.fn)
    (hash : PairHashing m w ctx ready free room) {sp : Nat} (deep : w.stackLo + 256 + room ≤ sp)
    {mem : Memory} (rd : ready mem) {job leaf proof count index root scratch : UInt64}
    (j : BranchJob w free mem job leaf proof count index root scratch) :
    ∃ mem', Calls m w "ssz_verify_branch" sp [job, ctx] mem
        (answerCode (verifyMerkleProof (readNode mem leaf.toNat) (nodesAt mem proof.toNat count.toNat) index.toNat
          (readNode mem root.toNat))) mem' ∧
      ready mem' ∧ ∀ a, free a → ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + 64) → mem' a = mem a := by
  have frameSize : VerifyBranch.fn.frame = 21 := by decide
  let verdict := answerCode (verifyMerkleProof (readNode mem leaf.toNat) (nodesAt mem proof.toNat count.toNat)
    index.toNat (readNode mem root.toNat))
  suffices body : Wp m w (sp - 176) VerifyBranch.fn.body (entryEnv [job, ctx]) mem
      fun env mem' => ∃ r, eval w env mem' (Ir.Expr.var 15) = some r ∧ (r = verdict ∧ ready mem' ∧
        ∀ a, free a → ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + 64) → mem' a = mem a) by
    obtain ⟨r, mem', call, hr, rd', fr⟩ := Calls.of_wp (Q := fun r mem' => r = verdict ∧ ready mem' ∧
        ∀ a, free a → ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + 64) → mem' a = mem a)
      (w := w) (sp := sp) (args := [job, ctx]) (mem := mem) hv (by omega) rfl (by rw [frameSize]; exact body)
    rw [hr] at call
    exact ⟨mem', call, rd', fr⟩
  simp only [VerifyBranch.fn]
  have bj := access_bound j.words
  -- The six words of the job.
  refine Wp.cons (Wp.set (eval_ld (x := job) rfl (by simpa using access_sub (k := 0) (j := 8) j.words (by omega)))
    (Wp.cons (Wp.set (eval_ld_off (x := job) (n := 8) rfl (access_sub j.words (by simp)))
    (Wp.cons (Wp.set (eval_ld_off (x := job) (n := 16) rfl (access_sub j.words (by simp)))
    (Wp.cons (Wp.set (eval_ld_off (x := job) (n := 24) rfl (access_sub j.words (by simp)))
    (Wp.cons (Wp.set (eval_ld_off (x := job) (n := 32) rfl (access_sub j.words (by simp)))
    (Wp.cons (Wp.set (eval_ld_off (x := job) (n := 40) rfl (access_sub j.words (by simp))) ?_)))))))))))
  refine Wp.of_env (fun env => env 0 = job ∧ env 1 = ctx ∧ env 2 = leaf ∧ env 3 = proof ∧ env 4 = count ∧
      env 5 = index ∧ env 6 = root ∧ env 7 = scratch)
    (by simp only [assign, ↓reduceIte, Nat.reduceEqDiff, entryEnv, UInt64.reduceToNat]
        exact ⟨rfl, rfl, j.w0, j.w1, j.w2, j.w3, j.w4, j.w5⟩) ?_
  intro env ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩
  -- Every early answer leaves memory as it was.
  have done : ∀ (env' : Env) (v : UInt64), env' 15 = v → v = verdict →
      Wp m w (sp - 176) (.block []) env' mem fun env mem' =>
        ∃ r, eval w env mem' (Ir.Expr.var 15) = some r ∧ (r = verdict ∧ ready mem' ∧
          ∀ a, free a → ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + 64) → mem' a = mem a) :=
    fun env' v hv eq => Wp.nil ⟨v, by rw [← hv]; rfl, eq, rd, fun _ _ _ => rfl⟩
  refine Wp.cons (Wp.ite (eval_eq rfl rfl) (fun zero => ?_) (fun nonzero => ?_))
  · -- An index of zero names no node.
    have : index = 0 := by
      rw [← e5]; by_cases h : env 5 = 0
      · exact h
      · simp [h] at zero
    refine Wp.cons (Wp.set rfl (Wp.nil (done _ 3 rfl ?_)))
    simp only [verdict, this, UInt64.toNat_zero, verifyMerkleProof_zero, answerCode]
  have i0 : index.toNat ≠ 0 := by
    intro h
    have : env 5 = 0 := by rw [e5]; exact UInt64.toNat_inj.mp (by rw [h]; rfl)
    simp [this] at nonzero
  refine Wp.cons (Wp.ite (eval_eq rfl rfl) (fun one => ?_) (fun notOne => ?_))
  · -- The root's index has no branch.
    have : index = 1 := by
      rw [← e5]; by_cases h : env 5 = 1
      · exact h
      · simp [h] at one
    refine Wp.cons (Wp.set rfl (Wp.nil (Wp.nil (done _ 4 rfl ?_))))
    simp only [verdict, this, UInt64.toNat_one, verifyMerkleProof_one, answerCode]
  have i1 : index.toNat ≠ 1 := by
    intro h
    have : env 5 = 1 := by rw [e5]; exact UInt64.toNat_inj.mp (by rw [h]; rfl)
    simp [this] at notOne
  have two : 2 ≤ index.toNat := by omega
  -- The depth of the index, against the branch length.
  have lv := level_calls (w := w) hl (sp := sp - 176) (by omega) (env 5) mem
  refine Wp.cons (Wp.call (values := [env 5]) rfl ⟨_, mem, lv, ?_⟩)
  have small := log2_lt_64 index
  refine Wp.cons (Wp.ite (eval_ne rfl rfl) (fun differ => ?_) (fun same => ?_))
  · -- A branch of the wrong length is refused.
    have ne : Nat.log2 index.toNat ≠ (nodesAt mem proof.toNat count.toNat).length := by
      rw [nodesAt_length]
      intro h
      simp only [assign, ↓reduceIte, Nat.reduceEqDiff, e4, e5] at differ
      rw [if_pos (UInt64.toNat_inj.mp (by rw [toNat_ofNat_of_lt _ (by omega), h]))] at differ
      exact differ rfl
    refine Wp.cons (Wp.set rfl (Wp.nil (Wp.nil (Wp.nil (done _ 5 rfl ?_)))))
    simp only [verdict, verifyMerkleProof_length _ _ _ two ne, answerCode]
  have depth : Nat.log2 index.toNat = count.toNat := by
    simp only [assign, ↓reduceIte, Nat.reduceEqDiff, e4, e5] at same
    by_cases h : (Nat.log2 index.toNat).toUInt64 = count
    · rw [← h, toNat_ofNat_of_lt _ (by omega)]
    · simp [h] at same
  -- The climb starts on the leaf, with every turn of the index still ahead.
  refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons ?_))))))))
  refine Wp.loop (ClimbInv ready free mem job ctx leaf proof count index root scratch)
    (fun env _ => count.toNat - (env 12).toNat) ?_ ?_
  · simp only [ClimbInv, assign, ↓reduceIte, Nat.reduceEqDiff]
    refine ⟨e0, e1, e2, e3, e4, e5, e6, e7, by simp, by simp [e5], by simp [e2], trivial, rd, fun _ _ _ => trivial, ?_⟩
    simp [e2]
  intro env' mem' inv
  refine ⟨_, eval_cmp .b rfl rfl, fun nz => ?_, fun z => ?_⟩
  · -- Each pass climbs one level.
    have more : (env' 12).toNat < count.toNat := by
      rw [← inv.2.2.2.2.1]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using nz
    exact climb_pass hash (by omega) j env' mem' inv more
  -- The climb has used the whole branch, so the climbing node is the rebuilt root.
  obtain ⟨_, e1', _, _, e4', _, e6', e7', le, _, cur, status, rd', frame', climb⟩ := inv
  have top : (env' 12).toNat = count.toNat := by
    have : ¬ (env' 12).toNat < (env' 4).toNat := by simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using z
    rw [e4'] at this; omega
  have bs := access_bound j.scratchOk
  have curOk : w.access (env' 10).toNat 32 = true := by
    rw [cur]; split
    · exact j.leafOk
    · exact access_sub j.scratchOk (by omega)
  have rootOk : w.access (env' 6).toNat 32 = true := by rw [e6']; exact j.rootOk
  have rootNode : readNode mem' root.toNat = readNode mem root.toNat := by
    apply readNode_congr
    intro k hk
    have := j.rootApart
    exact frame' _ (j.rootFree k hk) (by simp only [Apart] at this; omega)
  refine Wp.cons (Wp.ite (eval_ne rfl rfl) (fun bad => ?_) (fun _ => ?_))
  · simp [status] at bad
  have sc := same_calls (w := w) hs (sp := sp - 176) (by omega) (env' 10) (env' 6) mem' curOk rootOk
  refine Wp.cons (Wp.call (values := [env' 10, env' 6]) rfl ⟨_, mem', sc, ?_⟩)
  refine Wp.nil (Wp.nil (Wp.nil (Wp.nil (Wp.nil ⟨_, rfl, ?_, rd', frame'⟩))))
  -- The verdict: the index's depth is the branch length, every node is whole, and the climbed node is compared.
  have len : gindexLength index.toNat = .ok (nodesAt mem proof.toNat count.toNat).length := by
    rw [gindexLength_of_two two, nodesAt_length, depth]
  simp only [verdict, verifyMerkleProof_ok _ _ _ _ len (readNode_size _ _)
    (by simp [nodesAt, readNode_size]), answerCode_decide, climb, top, e6', rootNode]
  rw [List.drop_of_length_le (by rw [nodesAt_length]; exact Nat.le_refl _), climbBranch_nil]
  simp only [assign, ↓reduceIte]

end Ssz.Native.Driver.BranchProof
