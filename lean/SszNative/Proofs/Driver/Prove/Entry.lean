import SszNative.Proofs.Driver.Prove.NodeAt

/-!
The exported proving drivers answer what the Lean node, branch, and multiproof answer, with no contract left.

Each takes the walk to one node from its proof for every type, on an encoding validation accepts.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.ProveProof

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Driver.BranchProof

/-- An accepted encoding's node is the walk to it. -/
theorem nodeRoot_eq {d : Desc} {b : ByteArray} (valid : validate d b = .ok ()) (index : Nat) :
    nodeRoot d b index = walkNode d b index := by
  simp [nodeRoot, valid, walkNode, bind, Except.bind]

/--
A call of the node builder answers what the Lean node answers, and writes the node when there is one.

The walk to the node is the contract of the branch builder, and the encoding is one validation accepts.
Only the node's place, the scratch area, and the padding area change.
-/
theorem prove_node_calls {m : Module} {w : World} {d : Desc} {b : ByteArray} {plan data ctx : UInt64}
    {pad : Nat} {ready : Memory → Prop} {free : Nat → Prop} {need room : Nat}
    (hf : m.fns.lookup "ssz_prove_node" = some ProveNode.fn)
    (walk : NodeAtOk m w d b plan data ctx pad ready free need room) (valid : validate d b = .ok ()) {sp : Nat}
    (deep : w.stackLo + 8 + 8 * ProveNode.fn.frame + room ≤ sp)
    (job index out scr : UInt64) (mem : Memory) (r0 : ready mem)
    (j : ProveJob w free mem job plan data b.size.toUInt64 index out scr 1 need) :
    ∃ r mem', Calls m w "ssz_prove_node" sp [job, ctx] mem r mem' ∧
      r = proveCode (nodeRoot d b index.toNat) ∧
      (∀ node, nodeRoot d b index.toNat = .ok node → readNode mem' out.toNat = node) ∧
      ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 32) → ¬ (scr.toNat ≤ a ∧ a < scr.toNat + 24 + need) →
        ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a := by
  have bo := BranchProof.access_bound j.outOk
  have bs := BranchProof.access_bound j.scrOk
  have bj := BranchProof.access_bound j.words
  rw [nodeRoot_eq valid]
  let Post := fun (r : UInt64) (mem' : Memory) =>
    r = proveCode (walkNode d b index.toNat) ∧
      (∀ node, walkNode d b index.toNat = .ok node → readNode mem' out.toNat = node) ∧
      ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 32) → ¬ (scr.toNat ≤ a ∧ a < scr.toNat + 24 + need) →
        ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a
  suffices body : BranchProof.Wp m w (sp - 8 - 8 * ProveNode.fn.frame) ProveNode.fn.body (entryEnv [job, ctx]) mem
      fun env mem' => ∃ r, eval w env mem' ProveNode.fn.result = some r ∧ Post r mem' by
    exact Calls.of_wp hf (by omega) rfl body
  have spRoom : w.stackLo + room ≤ sp - 8 - 8 * ProveNode.fn.frame := by omega
  generalize sp - 8 - 8 * ProveNode.fn.frame = sp' at spRoom ⊢
  simp only [ProveNode.fn]
  have rd : ∀ k, k + 8 ≤ 48 → w.access (job.toNat + k) 8 = true := fun k hk => BranchProof.access_sub j.words hk
  -- The scratch is read from the job, and the walk's record is written at its start.
  refine Wp.cons (Wp.set (eval_word (x := job) rfl 40 (rd 40 (by omega)) j.w5) ?_)
  have h8 : (scr + 8).toNat = scr.toNat + 8 := by rw [BranchProof.toNat_add_of_lt _ _ (by simp; omega)]; simp
  have h16 : (scr + 16).toNat = scr.toNat + 16 := by rw [BranchProof.toNat_add_of_lt _ _ (by simp; omega)]; simp
  refine Wp.cons (Wp.store (x := scr) (y := out) rfl
    (eval_word (x := job) rfl 32 (rd 32 (by omega)) j.w4)
    (BranchProof.access_prefix j.scrOk (by simp only [Width.bytes]; omega)) ?_)
  refine Wp.cons (Wp.store (x := scr + 8) (y := scr + 24) (BranchProof.eval_add rfl rfl) (BranchProof.eval_add rfl rfl)
    (by rw [h8]; exact BranchProof.access_sub j.scrOk (by simp only [Width.bytes]; omega)) ?_)
  refine Wp.cons (Wp.store (x := scr + 16) (y := ctx) (BranchProof.eval_add rfl rfl) rfl
    (by rw [h16]; exact BranchProof.access_sub j.scrOk (by simp only [Width.bytes]; omega)) ?_)
  simp only [Width.bytes]
  obtain ⟨rec0, rec8, rec16, recOut⟩ := record_words mem scr.toNat (scr + 8).toNat (scr + 16).toNat out
    (scr + 24) ctx h8 h16 _ rfl
  generalize store (store (store mem scr.toNat 8 (qwordByte out)) (scr + 8).toNat 8 (qwordByte (scr + 24)))
    (scr + 16).toNat 8 (qwordByte ctx) = mem3 at rec0 rec8 rec16 recOut ⊢
  -- The record lies in the scratch, so the job's words and everything not free are as they were.
  have notScr : ∀ a, ¬ free a → ¬ (scr.toNat ≤ a ∧ a < scr.toNat + 24) := fun a nf h => nf (by
    have := j.scrFree (a - scr.toNat) (by omega); rwa [Nat.add_sub_cancel' h.1] at this)
  have jr : ∀ k, k + 8 ≤ 48 → readLE mem3 (job.toNat + k) 8 = readLE mem (job.toNat + k) 8 := fun k hk =>
    readLE_congr mem3 mem _ 8 fun i hi => by
      rw [Nat.add_assoc, recOut _ (notScr _ (j.kept (k + i) (by omega)))]
  have ready3 : ready mem3 := walk.ready_frame mem mem3 r0 fun a nf _ => recOut a (notScr a nf)
  obtain ⟨r, mem4, call, rc, rnode, rframe⟩ := walk.node sp' mem3 index out scr ready3 (by omega)
    (BranchProof.access_prefix j.outOk (by omega)) j.scrOk (fun k hk => j.outFree k (by omega)) j.scrFree
    (by have := j.apart; simp only [Apart] at this ⊢; omega) rec0 rec8 rec16
  refine Wp.cons (Wp.call (values := [plan, data, 0, b.size.toUInt64, index, scr])
    (mapM_six
      (by
        rw [BranchProof.eval_ld (x := job) rfl (by simpa using rd 0 (by omega))]
        have := jr 0 (by omega)
        simp only [Nat.add_zero] at this
        rw [this, j.w0])
      (eval_word (x := job) rfl 8 (rd 8 (by omega)) ((jr 8 (by omega)).trans j.w1))
      rfl
      (eval_word (x := job) rfl 16 (rd 16 (by omega)) ((jr 16 (by omega)).trans j.w2))
      (eval_word (x := job) rfl 24 (rd 24 (by omega)) ((jr 24 (by omega)).trans j.w3))
      rfl) ⟨r, mem4, call, ?_⟩)
  refine Wp.nil ⟨r, by simp [assign], rc, rnode, fun a h1 h2 h3 => ?_⟩
  rw [rframe a h1 (by omega) h3, recOut a (by omega)]

/-! ### With the walk proved -/

/--
A call of the node builder answers what the Lean node answers, and writes the node when there is one.

The encoding is one validation accepts, the type nests at most 64 deep, and the scratch holds the prover's scratch
bound.
Only the node's place, the scratch area, and the padding area change.
-/
theorem prove_node_ok {m : Module} {w : World} (fns : ProveFns m) (hash : HashingOk m w)
    (hf : m.fns.lookup "ssz_prove_node" = some ProveNode.fn) {d : Desc} {b : ByteArray}
    {plan data ctx table zeros pad : Nat} {mask : UInt64} (st : ProveStatic w d b plan data ctx table zeros pad)
    {sp : Nat} (deep : w.stackLo + 8 + 8 * ProveNode.fn.frame + nodeStack d ≤ sp) (job index out scr : UInt64)
    (mem : Memory) (r0 : ProveReady w d b plan data ctx table zeros pad mask mem)
    (j : ProveJob w (ProveFree ctx table zeros pad plan (8 * (Plan.words d).length) data b.size) mem job
      (UInt64.ofNat plan) (UInt64.ofNat data) b.size.toUInt64 index out scr 1 (proveScratch d b.size - 24)) :
    ∃ r mem', Calls m w "ssz_prove_node" sp [job, UInt64.ofNat ctx] mem r mem' ∧
      r = proveCode (nodeRoot d b index.toNat) ∧
      (∀ node, nodeRoot d b index.toNat = .ok node → readNode mem' out.toNat = node) ∧
      ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 32) →
        ¬ (scr.toNat ≤ a ∧ a < scr.toNat + 24 + (proveScratch d b.size - 24)) → ¬ (pad ≤ a ∧ a < pad + 1536) →
        mem' a = mem a :=
  prove_node_calls hf (nodeAtOk_of fns hash st) st.valid deep job index out scr mem r0 j

/--
A call of the branch builder answers what the Lean branch answers, and writes the branch when there is one.

The encoding is one validation accepts, the type nests at most 64 deep, and the scratch holds the prover's scratch
bound.
Only the branch's place, the scratch area, and the padding area change.
-/
theorem prove_branch_ok {m : Module} {w : World} (fns : ProveFns m) (hash : HashingOk m w)
    (hf : m.fns.lookup "ssz_prove_branch" = some ProveBranch.fn) {d : Desc} {b : ByteArray}
    {plan data ctx table zeros pad : Nat} {mask : UInt64} (st : ProveStatic w d b plan data ctx table zeros pad)
    {sp : Nat} (deep : w.stackLo + 8 + 8 * ProveBranch.fn.frame + nodeStack d + 32 ≤ sp) (job index out scr : UInt64)
    (mem : Memory) (r0 : ProveReady w d b plan data ctx table zeros pad mask mem)
    (j : ProveJob w (ProveFree ctx table zeros pad plan (8 * (Plan.words d).length) data b.size) mem job
      (UInt64.ofNat plan) (UInt64.ofNat data) b.size.toUInt64 index out scr (Nat.log2 index.toNat)
      (proveScratch d b.size - 24))
    (jobPad : ∀ k < 48, ¬ (pad ≤ job.toNat + k ∧ job.toNat + k < pad + 1536)) :
    ∃ r mem', Calls m w "ssz_prove_branch" sp [job, UInt64.ofNat ctx] mem r mem' ∧
      r = proveCode (buildProof d b index.toNat) ∧
      (∀ nodes, buildProof d b index.toNat = .ok nodes →
        nodesAt mem' out.toNat (Nat.log2 index.toNat) = nodes) ∧
      ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 32 * Nat.log2 index.toNat) →
        ¬ (scr.toNat ≤ a ∧ a < scr.toNat + 24 + (proveScratch d b.size - 24)) → ¬ (pad ≤ a ∧ a < pad + 1536) →
        mem' a = mem a :=
  prove_branch_calls hf fns.level (nodeAtOk_of fns hash st) st.valid deep job index out scr mem r0 j jobPad

/--
A call of the multiproof builder answers what the Lean multiproof answers, and writes its nodes and their count when
there are some.

The encoding is one validation accepts, the type nests at most 64 deep, and the scratch holds the prover's scratch
bound past the helper indices.
Only the nodes' place, the scratch area, the node count's word, and the padding area change.
-/
theorem prove_multiproof_ok {m : Module} {w : World} (fns : ProveFns m) (hash : HashingOk m w)
    (hf : m.fns.lookup "ssz_prove_multiproof" = some ProveMultiproof.fn) (helpers : HelperFns m) {d : Desc}
    {b : ByteArray} {plan data ctx table zeros pad : Nat} {mask : UInt64}
    (st : ProveStatic w d b plan data ctx table zeros pad) {sp : Nat}
    (deep : w.stackLo + 8 + 8 * ProveMultiproof.fn.frame + nodeStack d + 304 ≤ sp)
    (job indices count out scr : UInt64) (mem : Memory) (r0 : ProveReady w d b plan data ctx table zeros pad mask mem)
    (j : MultiJob w (ProveFree ctx table zeros pad plan (8 * (Plan.words d).length) data b.size) mem job
      (UInt64.ofNat plan) (UInt64.ofNat data) b.size.toUInt64 indices count out scr (proveScratch d b.size - 24))
    (jobPad : ∀ k < 56, ¬ (pad ≤ job.toNat + k ∧ job.toNat + k < pad + 1536)) :
    ∃ r mem', Calls m w "ssz_prove_multiproof" sp [job, UInt64.ofNat ctx] mem r mem' ∧
      r = proveCode (buildMultiproof d b (BranchProof.wordsAt mem indices.toNat count.toNat)) ∧
      (∀ nodes,
        buildMultiproof d b (BranchProof.wordsAt mem indices.toNat count.toNat) = .ok nodes →
          readLE mem' (job.toNat + 56) 8 = nodes.length.toUInt64 ∧ nodesAt mem' out.toNat nodes.length = nodes) ∧
      ∀ a, MultiOutside job.toNat out.toNat scr.toNat count.toNat (proveScratch d b.size - 24) pad a →
        mem' a = mem a :=
  prove_multiproof_calls hf helpers (nodeAtOk_of fns hash st) st.valid deep job indices count out scr mem r0 j jobPad

end EthLib.Consensus.Ssz.Native.Driver.ProveProof
