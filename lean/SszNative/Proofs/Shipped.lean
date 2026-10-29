import SszNative.Kernel.Assembly
import SszNative.Proofs.Ir.Link
import SszNative.Proofs.Kernel.Detect
import SszNative.Proofs.Driver.Root.Top
import SszNative.Proofs.Driver.Validate.Main
import SszNative.Proofs.Driver.Validate.PlanSound
import SszNative.Proofs.Plan.Rename
import SszNative.Proofs.Driver.TreeStore
import SszNative.Proofs.Driver.Branch
import SszNative.Proofs.Driver.Prove

/-!
The image the native library ships, checked as a link, and the drivers' theorems run on its whole machine.

The image is the drivers compiled and linked, then the kernels.
Its module pairs the drivers with the meanings the kernels' theorems prove.
Every fact the drivers' theorems take of a module holds of this one, so each of them becomes a statement about the
machine running the shipped image, from a call instruction to the instruction after it.
-/

namespace Ssz.Native

open Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Driver

/-- The shipped image passes the link check. -/
theorem shipped_linkCheck : linkCheck shippedFns shippedExterns = true := by
  decide +kernel

/-! ## The shipped module -/

/-- The meanings of the kernels and of the feature detection, each under its exported name. -/
noncomputable def shippedContracts : List (String × Extern) :=
  hashExterns ++ gatherExterns ++ [("ssz_cpu_features", Kernel.detectExtern)]

/-- The drivers, and the meanings of the routines written by hand. -/
noncomputable def shippedModule : Module :=
  ⟨shippedFns, shippedContracts⟩

/-- The image the native library ships. -/
abbrev shippedImage : Image :=
  Module.link shippedFns shippedExterns

/-- The drivers after the hashing and gathering ones. -/
def otherFns : List (String × Fn) :=
  codecFns ++ rootFns ++ branchFns ++ proveFns ++ Validate.fns ++ treeStoreFns

/-- The module, with the hashing and gathering parts first. -/
theorem shippedModule_eq : shippedModule =
    ⟨hashFns ++ gatherFns ++ otherFns, hashExterns ++ gatherExterns ++ [("ssz_cpu_features", Kernel.detectExtern)]⟩ :=
  rfl

/-- No two drivers share a name. -/
theorem shippedFns_nodup : (shippedFns.map (·.1)).Nodup := by
  decide +kernel

/-- In a list whose names are distinct, an entry's name finds that entry. -/
theorem lookup_of_mem {α : Type} : ∀ (l : List (String × α)), (l.map (·.1)).Nodup → ∀ p ∈ l, l.lookup p.1 = some p.2
  | [], _, _, h => by simp at h
  | (k, b) :: rest, nodup, p, h => by
    simp only [List.map_cons, List.nodup_cons] at nodup
    rcases List.mem_cons.mp h with rfl | h'
    · simp [List.lookup]
    · -- An entry further on carries a name the head does not.
      have later : p.1 ∈ rest.map (·.1) := List.mem_map_of_mem h'
      have ne : (p.1 == k) = false := by
        simp only [beq_eq_false_iff_ne]
        intro e
        exact nodup.1 (e ▸ later)
      simp only [List.lookup, ne]
      exact lookup_of_mem rest nodup.2 p h'

/-- Each driver's name finds that driver. -/
theorem shipped_lookup {p : String × Fn} (h : p ∈ shippedFns) : shippedModule.fns.lookup p.1 = some p.2 :=
  lookup_of_mem shippedFns shippedFns_nodup p h

/-! ## The facts the drivers' theorems take -/

/-- The module holds the codec drivers. -/
theorem shipped_codec : HasCodec shippedModule := fun _ h =>
  shipped_lookup (by simp [shippedFns, h])

/-- The module holds the decoding check's functions. -/
theorem shipped_loaded : Validate.Loaded shippedModule := fun _ h =>
  shipped_lookup (by simp [shippedFns, h])

/-- The module keeps every hashing call, on every processor. -/
theorem shipped_hashing (w : World) : HashingOk shippedModule w := by
  rw [shippedModule_eq, List.append_assoc hashFns, List.append_assoc hashExterns]
  refine hashingOk_append w _ _ fun layout family known => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at known
  cases layout <;> rcases known with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The module holds the gather dispatcher and its kernels. -/
theorem shipped_gather : GatherModule shippedModule := by
  rw [shippedModule_eq]
  refine gatherModule_append _ _ fun name known => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at known
  rcases known with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The module holds the plan readers. -/
theorem shipped_plan : PlanFns shippedModule :=
  ⟨shipped_codec, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The module holds the fixed-size roots driver and the drivers it calls. -/
theorem shipped_roots : RootsFns shippedModule :=
  ⟨shipped_plan, rfl, rfl, rfl, rfl⟩

/-- The module holds the range drivers. -/
theorem shipped_range : RangeFns shippedModule :=
  ⟨shipped_roots, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The module holds the multiproof verifier and the functions it calls. -/
theorem shipped_multi : BranchProof.MultiFns shippedModule :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩

/-- The module holds the proving drivers and the functions they call. -/
theorem shipped_prove : ProveProof.ProveFns shippedModule :=
  ⟨shipped_range, shipped_gather, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The module holds the helper-index computation. -/
theorem shipped_helpers : BranchProof.HelperFns shippedModule :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The kernels keep their contracts in the image -/

/-- A kernel of the image that calls nothing and keeps its contract alone keeps it in the image. -/
theorem shipped_extern (w : World) (j : Nat) (hj : j < shippedExterns.size) {name : String} {code : Array Instr}
    {e : Extern} (at_j : shippedExterns[j] = (name, code)) (leaf : Leaf code) (ok : LeafOk w code e) :
    ExternOk shippedImage w name e := by
  obtain ⟨find, code_eq, _, _⟩ := extern_found shippedFns shippedExterns shipped_linkCheck j hj
  rw [at_j] at find code_eq
  exact extern_of_leaf _ w name _ e find (by rw [code_eq]; exact leaf) (by rw [code_eq]; exact ok)

/-- Every kernel, and the feature detection, keeps in the image the contract of its meaning. -/
theorem shipped_contracts (w : World) : ∀ p ∈ shippedContracts, ExternOk shippedImage w p.1 p.2 := by
  simp only [shippedContracts, hashExterns, gatherExterns, List.cons_append, List.nil_append,
    List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  refine ⟨shipped_extern w 0 (by decide) rfl (avx512_leaf 64 64) (avx512_leafOk w 64 64),
    shipped_extern w 1 (by decide) rfl (avx512_leaf 32 32) (avx512_leafOk w 32 32),
    shipped_extern w 2 (by decide) rfl (avx512_leaf 32 0) (avx512_leafOk w 32 0),
    shipped_extern w 12 (by decide) rfl (shani_leaf 64 64) (shani_leafOk w 64 64),
    shipped_extern w 13 (by decide) rfl (shani_leaf 32 32) (shani_leafOk w 32 32),
    shipped_extern w 14 (by decide) rfl (shani_leaf 32 0) (shani_leafOk w 32 0),
    shipped_extern w 15 (by decide) rfl (shaniDual_leaf 64 64) (shaniDual_leafOk w 64 64),
    shipped_extern w 16 (by decide) rfl (shaniDual_leaf 32 32) (shaniDual_leafOk w 32 32),
    shipped_extern w 17 (by decide) rfl (shaniDual_leaf 32 0) (shaniDual_leafOk w 32 0),
    shipped_extern w 3 (by decide) rfl (avx512x2_leaf 64 64) (avx512x2_leafOk w 64 64),
    shipped_extern w 4 (by decide) rfl (avx512x2_leaf 32 32) (avx512x2_leafOk w 32 32),
    shipped_extern w 5 (by decide) rfl (avx512x2_leaf 32 0) (avx512x2_leafOk w 32 0),
    shipped_extern w 6 (by decide) rfl (avx2_leaf 64 64) (avx2_leafOk w 64 64),
    shipped_extern w 7 (by decide) rfl (avx2_leaf 32 32) (avx2_leafOk w 32 32),
    shipped_extern w 8 (by decide) rfl (avx2_leaf 32 0) (avx2_leafOk w 32 0),
    shipped_extern w 9 (by decide) rfl (baseline_leaf 64 64) (baseline_leafOk w 64 64),
    shipped_extern w 10 (by decide) rfl (baseline_leaf 32 32) (baseline_leafOk w 32 32),
    shipped_extern w 11 (by decide) rfl (baseline_leaf 32 0) (baseline_leafOk w 32 0),
    shipped_extern w 18 (by decide) rfl gather_leaf (gather_leafOk w),
    shipped_extern w 19 (by decide) rfl (gatherNode_leaf 1 (by decide)) (gatherNode_leafOk w 1 (by decide)),
    shipped_extern w 20 (by decide) rfl (gatherNode_leaf 2 (by decide)) (gatherNode_leafOk w 2 (by decide)),
    shipped_extern w 21 (by decide) rfl (gatherNode_leaf 4 (by decide)) (gatherNode_leafOk w 4 (by decide)),
    shipped_extern w 22 (by decide) rfl (gatherNode_leaf 8 (by decide)) (gatherNode_leafOk w 8 (by decide)),
    shipped_extern w 23 (by decide) rfl (gatherNode_leaf 16 (by decide)) (gatherNode_leafOk w 16 (by decide)),
    shipped_extern w 24 (by decide) rfl (gatherNode_leaf 32 (by decide)) (gatherNode_leafOk w 32 (by decide)),
    shipped_extern w 25 (by decide) rfl gatherKey_leaf (gatherKey_leafOk w),
    shipped_extern w 26 (by decide) rfl Kernel.detect_leaf (Kernel.detect_leafOk w)⟩

/-- Every call to the shipped module, compiled into the shipped image, computes its meaning. -/
theorem shipped_ok (w : World) (fuel : Nat) (name : String) :
    CallOk shippedImage w name (callSpec shippedModule w fuel name) := by
  refine module_ok shippedModule shippedImage w (placed_of_linkCheck _ _ _ shipped_linkCheck) ?_ fuel name
  intro name e _ found
  obtain ⟨i, hi, at_i⟩ := lookup_getElem _ name e found
  have := shipped_contracts w _ (List.getElem_mem hi)
  rwa [at_i] at this

/-! ## Calls on the whole machine -/

/--
A call to a name, from a call instruction inside an image, returns with a result and memory.

The machine must be running at the call, with the stack pointer, the arguments in their registers, and the memory off
the stack the call is given.
It comes back to the next instruction with the result in rax and memory off the stack as given.
The stack pointer, the kept registers and the stack from the stack pointer up are as before.
-/
def Returns (image : Image) (w : World) (name : String) (sp : Nat) (args : List UInt64) (mem : Memory) (res : UInt64)
    (mem' : Memory) : Prop :=
  ∀ (r : Nat) (s : State), (image.code r)[s.pc]? = some (.call name) → s.status = .running → s.cpu = w.cpu →
    r < image.size → r < 2 ^ 31 → s.pc + 1 < 2 ^ 32 →
    s.gpr .rsp = sp.toUInt64 → sp ≤ w.stackHi → w.stackHi ≤ addressBound →
    args.length ≤ 6 → (∀ i < args.length, s.gpr (argReg i) = args.getD i 0) →
    (∀ a, a < w.stackLo ∨ w.stackHi ≤ a → s.mem a = mem a) →
    ∃ s', Reaches image r s s' ∧ s'.pc = s.pc + 1 ∧ s'.gpr .rax = res ∧ s'.gpr .rsp = sp.toUInt64 ∧
      (∀ g ∈ keptRegs, s'.gpr g = s.gpr g) ∧ (∀ a, a < w.stackLo ∨ w.stackHi ≤ a → s'.mem a = mem' a) ∧
      (∀ a, sp ≤ a → a < w.stackHi → s'.mem a = s.mem a) ∧ s'.cpu = s.cpu ∧ s'.status = .running

/-- A call the shipped module makes returns as it means on the machine running the shipped image. -/
theorem shipped_returns {w : World} {name : String} {sp : Nat} {args : List UInt64} {mem mem' : Memory}
    {res : UInt64} (call : Calls shippedModule w name sp args mem res mem') :
    Returns shippedImage w name sp args mem res mem' := by
  obtain ⟨fuel, spec⟩ := call
  intro r s fetch running cpu rIn rSmall pcSmall rsp spHi hiBound few argRegs heap
  exact shipped_ok w fuel name r s sp args mem mem' res fetch running cpu rIn rSmall pcSmall rsp spHi hiBound few
    argRegs heap spec

/-! ## The exported routines on the shipped image -/

open Ssz in
/--
The root of an encoding validation accepted, on the shipped image: the call returns zero and writes the
specification's root of the value the encoding holds.
-/
theorem shipped_hashTreeRoot {w : World} {d : Desc} {sp : Nat} (room : w.stackLo + 128 + 256 + rootStack d ≤ sp)
    {mem : Memory} {plan data out scratch ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : RangePre w mem d plan data 0 b.size out scratch ctx table zeros pad mask b) :
    ∃ mem', Returns shippedImage w "ssz_hash_tree_root" sp [UInt64.ofNat plan, UInt64.ofNat data,
        UInt64.ofNat b.size, UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx] mem 0 mem' ∧
      (do let v ← deserialize d b.data; Ssz.hashTreeRoot d v) = .ok (Driver.nodeAt mem' out) ∧
      RootReady w ctx table zeros pad mask mem' ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (scratch ≤ a ∧ a < scratch + rootScratch d b.size) →
        ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a := by
  obtain ⟨mem', call, root, ready, keep⟩ :=
    hashTreeRoot_calls (shipped_hashing w) shipped_gather shipped_range room pre
  exact ⟨mem', shipped_returns call, root, ready, keep⟩

open Ssz Ssz.Native.Driver.Validate in
/--
The native decoding check on the shipped image, for a type whose fields carry any names.

The call returns what the Lean check gives on the type: zero and memory untouched when it accepts, one and the
refusal's words written when it refuses.
-/
theorem shipped_validate {w : World} (d : Desc) (wf : d.wellFormed = .ok ()) (fit : fitsNative d = true)
    (deep : d.nesting ≤ maxNesting) (plan data err sp : Nat) (mem : Memory) (b : ByteArray)
    (hplan : PlanBytes w mem plan d) (hd : DataAt w mem data b)
    (cp : Clear err plan (Plan.encode d).size) (cd : Clear err data b.size) (ok : w.access err 32 = true)
    (small : b.size < 2 ^ 60) (room : Room w sp (2 * d.nesting) 5) :
    Returns shippedImage w "ssz_validate" sp [UInt64.ofNat plan, UInt64.ofNat (Plan.encode d).size,
      UInt64.ofNat data, UInt64.ofNat b.size, UInt64.ofNat err] mem (res (validate d b))
      (after mem err (validate d b)) :=
  shipped_returns (Plan.validate_calls_named shipped_loaded d wf fit deep plan data err sp mem b hplan hd cp cd ok
    small room)

open Ssz Ssz.Native.Driver.Validate in
/--
The plan's own check on the shipped image accepts the bytes of a plan of a legal type that fits the native check,
names its fields by position, and nests no deeper than a plan may be: it returns zero and leaves memory as it was.
-/
theorem shipped_checkPlan_accepts {w : World} (plan len sp : Nat) (mem : Memory) (acc : w.access plan len = true)
    (room : Room w sp (2 * maxNesting) 3) (legal : ∃ d, d.wellFormed = .ok () ∧ fitsNative d = true ∧
      named d = true ∧ d.nesting ≤ maxNesting ∧ PlanBytes w mem plan d ∧ (Plan.encode d).size = len) :
    ∃ mem', Returns shippedImage w "ssz_check_plan" sp [UInt64.ofNat plan, UInt64.ofNat len] mem 0 mem' := by
  obtain ⟨mem', call⟩ := (checkPlan_iff shipped_loaded plan len sp mem acc room).mpr legal
  exact ⟨mem', shipped_returns call⟩

open Ssz Ssz.Native.Driver.Validate in
/--
Any answer of the plan's own check runs on the shipped image, and is zero exactly when the bytes are the plan of a
legal type that fits the native check, names its fields by position, and nests no deeper than a plan may be.
-/
theorem shipped_checkPlan {w : World} (plan len sp : Nat) (mem : Memory) (acc : w.access plan len = true)
    (room : Room w sp (2 * maxNesting) 3) {r : UInt64} {mem' : Memory}
    (call : Calls shippedModule w "ssz_check_plan" sp [UInt64.ofNat plan, UInt64.ofNat len] mem r mem') :
    Returns shippedImage w "ssz_check_plan" sp [UInt64.ofNat plan, UInt64.ofNat len] mem r mem' ∧
      (r = 0 ↔ ∃ d, d.wellFormed = .ok () ∧ fitsNative d = true ∧ named d = true ∧ d.nesting ≤ maxNesting ∧
        PlanBytes w mem plan d ∧ (Plan.encode d).size = len) := by
  refine ⟨shipped_returns call, ⟨fun zero => ?_, fun legal => ?_⟩⟩
  · subst zero
    exact (checkPlan_iff shipped_loaded plan len sp mem acc room).mp ⟨mem', call⟩
  · obtain ⟨mem'', zero⟩ := (checkPlan_iff shipped_loaded plan len sp mem acc room).mpr legal
    exact (Calls.unique call zero).1

open Ssz in
/-- The tree store's build on the shipped image leaves the whole tree over the leaves in memory, and returns zero. -/
theorem shipped_treeBuild {w : World} {sp : Nat} {mem : Memory} {tree leaves count K ctx table zeros pad : Nat}
    {mask : UInt64} (pre : BuildPre w mem tree leaves count K ctx table zeros pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + storeStack ≤ sp) :
    ∃ mem', Returns shippedImage w "ssz_tree_build" sp [UInt64.ofNat tree, UInt64.ofNat leaves,
        UInt64.ofNat count, UInt64.ofNat ctx] mem 0 mem' ∧
      TreeOk mem' tree (2 ^ K) (nodesFrom (bytesAt mem leaves (32 * count)) 0 count) ∧
      BuildFrame mem mem' tree K pad := by
  obtain ⟨mem', call, ok, frame⟩ := treeBuild_calls (shipped_hashing w) rfl pre kernels room
  exact ⟨mem', shipped_returns call, ok, frame⟩

open Ssz in
/--
The tree store's update on the shipped image, after some leaves are rewritten in place, leaves the whole tree over
the new leaves, and returns zero.
-/
theorem shipped_treeUpdate {w : World} {sp : Nat} {mem mem0 : Memory}
    {tree K indices c scratch ctx table zeros pad : Nat} {mask : UInt64}
    (pre : UpdatePre w mem tree K indices c scratch ctx table zeros pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + storeStack ≤ sp)
    {old new : Array Bytes} {idx : Nat → Nat} (idxAt : ∀ i < c, slotWord mem indices i = idx i)
    (inside : ∀ x < c, idx x < 2 ^ K) (sorted : ∀ i j, i < j → j < c → idx i < idx j)
    (fits : new.size ≤ 2 ^ K) (was : TreeAt mem0 tree K old)
    (inner : ∀ a, tree + 32 ≤ a → a < tree + 32 * 2 ^ K → mem a = mem0 a)
    (leavesAt : ∀ j < 2 ^ K, Driver.nodeAt mem (tree + 32 * (2 ^ K + j)) = subtreeAt new 0 j)
    (kept : ∀ j < 2 ^ K, (∀ x < c, idx x ≠ j) → subtreeAt new 0 j = subtreeAt old 0 j) :
    ∃ mem', Returns shippedImage w "ssz_tree_update" sp [UInt64.ofNat tree, UInt64.ofNat (2 ^ K),
        UInt64.ofNat indices, UInt64.ofNat c, UInt64.ofNat scratch, UInt64.ofNat ctx] mem 0 mem' ∧
      TreeOk mem' tree (2 ^ K) new ∧ UpdateFrame mem mem' tree K c scratch pad := by
  obtain ⟨mem', call, ok, frame⟩ := treeUpdate_calls (shipped_hashing w) rfl pre kernels room idxAt inside sorted
    fits was inner leavesAt kept
  exact ⟨mem', shipped_returns call, ok, frame⟩

open Ssz in
/--
The tree store's root on the shipped image writes the specification's root of the leaves at the depth, with the word
mixed in if one is given, and returns zero.
-/
theorem shipped_treeRoot {w : World} {sp : Nat} {mem : Memory} {tree K depth mixin out ctx table zeros pad : Nat}
    {mask : UInt64} (pre : RootPre w mem tree K depth mixin out ctx table zeros pad mask)
    (kernels : KernelsRun w mask) (room : w.stackLo + storeStack ≤ sp) {leaves : Array Bytes}
    (ok : TreeOk mem tree (2 ^ K) leaves) :
    ∃ mem', Returns shippedImage w "ssz_tree_root" sp [UInt64.ofNat tree, UInt64.ofNat (2 ^ K),
        UInt64.ofNat depth, UInt64.ofNat mixin, UInt64.ofNat out, UInt64.ofNat ctx] mem 0 mem' ∧
      Driver.nodeAt mem' out =
        withMixin (subtreeAt leaves depth 0) (if mixin = 0 then none else some (Driver.nodeAt mem mixin)) ∧
      RootFrame mem mem' tree out pad := by
  obtain ⟨mem', call, root, frame⟩ := treeRoot_calls (shipped_hashing w) rfl pre kernels room ok
  exact ⟨mem', shipped_returns call, root, frame⟩

open Ssz.Native.Driver.BranchProof in
/--
The branch verifier on the shipped image answers what the Lean verifier answers on the leaf, branch, index and root
its job names.
-/
theorem shipped_verifyBranch {w : World} {ctx : UInt64} {table pad : Nat} {mask : UInt64} {sp : Nat}
    (deep : w.stackLo + 256 + hashStack ≤ sp) {mem : Memory} (rd : CtxReady w ctx.toNat table pad mask mem)
    {job leaf proof count index root scratch : UInt64}
    (j : BranchJob w (CtxFree ctx.toNat table pad) mem job leaf proof count index root scratch) :
    ∃ mem', Returns shippedImage w "ssz_verify_branch" sp [job, ctx] mem
        (answerCode (verifyMerkleProof (readNode mem leaf.toNat) (nodesAt mem proof.toNat count.toNat) index.toNat
          (readNode mem root.toNat))) mem' ∧
      CtxReady w ctx.toNat table pad mask mem' ∧
      ∀ a, CtxFree ctx.toNat table pad a → ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + 64) → mem' a = mem a := by
  obtain ⟨mem', call, ready, keep⟩ := verify_branch_hashing (shipped_hashing w) rfl rfl rfl deep rd j
  exact ⟨mem', shipped_returns call, ready, keep⟩

open Ssz.Native.Driver.BranchProof in
/--
The multiproof verifier on the shipped image answers what the Lean verifier answers on the leaves, proof nodes,
indices and root its job names.
-/
theorem shipped_verifyMultiproof {w : World} {ctx : UInt64} {table pad : Nat} {mask : UInt64} {sp : Nat}
    (deep : w.stackLo + 512 + hashStack ≤ sp) {mem : Memory} (rd : CtxReady w ctx.toNat table pad mask mem)
    {job leaves leafCount proof proofCount indices count root scratch : UInt64}
    (j : MultiJob w (CtxFree ctx.toNat table pad) mem job leaves leafCount proof proofCount indices count root
      scratch) :
    ∃ mem', Returns shippedImage w "ssz_verify_multiproof" sp [job, ctx] mem
        (answerCode (verifyMerkleMultiproof (nodesAt mem leaves.toNat leafCount.toNat)
          (nodesAt mem proof.toNat proofCount.toNat) (wordsAt mem indices.toNat count.toNat)
          (readNode mem root.toNat))) mem' ∧
      CtxReady w ctx.toNat table pad mask mem' ∧
      ∀ a, CtxFree ctx.toNat table pad a →
        ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + multiScratch count.toNat proofCount.toNat) → mem' a = mem a := by
  obtain ⟨mem', call, ready, keep⟩ := verify_multiproof_hashing (shipped_hashing w) shipped_multi deep rd j
  exact ⟨mem', shipped_returns call, ready, keep⟩

open Ssz Ssz.Native.Driver.ProveProof Ssz.Native.Driver.BranchProof in
/--
The node builder on the shipped image answers what the Lean node answers on an encoding validation accepts, and writes
the node when there is one.

The type nests at most 64 deep, and the scratch holds the prover's scratch bound.
Memory changes only at the node, in the scratch, and in the padding area.
-/
theorem shipped_proveNode {w : World} {d : Desc} {b : ByteArray} {plan data ctx table zeros pad : Nat}
    {mask : UInt64} (st : ProveStatic w d b plan data ctx table zeros pad) {sp : Nat}
    (deep : w.stackLo + 8 + 8 * ProveNode.fn.frame + nodeStack d ≤ sp) (job index out scr : UInt64) (mem : Memory)
    (r0 : ProveReady w d b plan data ctx table zeros pad mask mem)
    (j : ProveJob w (ProveFree ctx table zeros pad plan (8 * (Plan.words d).length) data b.size) mem job
      (UInt64.ofNat plan) (UInt64.ofNat data) b.size.toUInt64 index out scr 1 (proveScratch d b.size - 24)) :
    ∃ r mem', Returns shippedImage w "ssz_prove_node" sp [job, UInt64.ofNat ctx] mem r mem' ∧
      r = proveCode (nodeRoot d b index.toNat) ∧
      (∀ node, nodeRoot d b index.toNat = .ok node → readNode mem' out.toNat = node) ∧
      ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 32) →
        ¬ (scr.toNat ≤ a ∧ a < scr.toNat + 24 + (proveScratch d b.size - 24)) → ¬ (pad ≤ a ∧ a < pad + 1536) →
        mem' a = mem a := by
  obtain ⟨r, mem', call, rc, node, keep⟩ := prove_node_ok shipped_prove (shipped_hashing w)
    rfl st deep job index out scr mem r0 j
  exact ⟨r, mem', shipped_returns call, rc, node, keep⟩

open Ssz Ssz.Native.Driver.ProveProof Ssz.Native.Driver.BranchProof in
/--
The branch builder on the shipped image answers what the Lean branch answers on an encoding validation accepts, and
writes the branch when there is one.

The type nests at most 64 deep, and the scratch holds the prover's scratch bound.
Memory changes only at the branch, in the scratch, and in the padding area.
-/
theorem shipped_proveBranch {w : World} {d : Desc} {b : ByteArray} {plan data ctx table zeros pad : Nat}
    {mask : UInt64} (st : ProveStatic w d b plan data ctx table zeros pad) {sp : Nat}
    (deep : w.stackLo + 8 + 8 * ProveBranch.fn.frame + nodeStack d + 32 ≤ sp) (job index out scr : UInt64)
    (mem : Memory) (r0 : ProveReady w d b plan data ctx table zeros pad mask mem)
    (j : ProveJob w (ProveFree ctx table zeros pad plan (8 * (Plan.words d).length) data b.size) mem job
      (UInt64.ofNat plan) (UInt64.ofNat data) b.size.toUInt64 index out scr (Nat.log2 index.toNat)
      (proveScratch d b.size - 24))
    (jobPad : ∀ k < 48, ¬ (pad ≤ job.toNat + k ∧ job.toNat + k < pad + 1536)) :
    ∃ r mem', Returns shippedImage w "ssz_prove_branch" sp [job, UInt64.ofNat ctx] mem r mem' ∧
      r = proveCode (buildProof d b index.toNat) ∧
      (∀ nodes, buildProof d b index.toNat = .ok nodes → nodesAt mem' out.toNat (Nat.log2 index.toNat) = nodes) ∧
      ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 32 * Nat.log2 index.toNat) →
        ¬ (scr.toNat ≤ a ∧ a < scr.toNat + 24 + (proveScratch d b.size - 24)) → ¬ (pad ≤ a ∧ a < pad + 1536) →
        mem' a = mem a := by
  obtain ⟨r, mem', call, rc, nodes, keep⟩ := prove_branch_ok shipped_prove (shipped_hashing w)
    rfl st deep job index out scr mem r0 j jobPad
  exact ⟨r, mem', shipped_returns call, rc, nodes, keep⟩

open Ssz Ssz.Native.Driver.ProveProof Ssz.Native.Driver.BranchProof in
/--
The multiproof builder on the shipped image answers what the Lean multiproof answers on an encoding validation
accepts, and writes its nodes and their count when there are some.

The type nests at most 64 deep, and the scratch holds the prover's scratch bound past the helper indices.
Memory changes only at the nodes, in the scratch, at the node count's word, and in the padding area.
-/
theorem shipped_proveMultiproof {w : World} {d : Desc} {b : ByteArray} {plan data ctx table zeros pad : Nat}
    {mask : UInt64} (st : ProveStatic w d b plan data ctx table zeros pad) {sp : Nat}
    (deep : w.stackLo + 8 + 8 * ProveMultiproof.fn.frame + nodeStack d + 304 ≤ sp)
    (job indices count out scr : UInt64) (mem : Memory) (r0 : ProveReady w d b plan data ctx table zeros pad mask mem)
    (j : ProveProof.MultiJob w (ProveFree ctx table zeros pad plan (8 * (Plan.words d).length) data b.size) mem job
      (UInt64.ofNat plan) (UInt64.ofNat data) b.size.toUInt64 indices count out scr (proveScratch d b.size - 24))
    (jobPad : ∀ k < 56, ¬ (pad ≤ job.toNat + k ∧ job.toNat + k < pad + 1536)) :
    ∃ r mem', Returns shippedImage w "ssz_prove_multiproof" sp [job, UInt64.ofNat ctx] mem r mem' ∧
      r = proveCode (buildMultiproof d b (BranchProof.wordsAt mem indices.toNat count.toNat)) ∧
      (∀ nodes, buildMultiproof d b (BranchProof.wordsAt mem indices.toNat count.toNat) = .ok nodes →
        readLE mem' (job.toNat + 56) 8 = nodes.length.toUInt64 ∧ nodesAt mem' out.toNat nodes.length = nodes) ∧
      ∀ a, MultiOutside job.toNat out.toNat scr.toNat count.toNat (proveScratch d b.size - 24) pad a →
        mem' a = mem a := by
  obtain ⟨r, mem', call, rc, nodes, keep⟩ := prove_multiproof_ok shipped_prove (shipped_hashing w)
    rfl shipped_helpers st deep job indices count out scr mem r0 j
    jobPad
  exact ⟨r, mem', shipped_returns call, rc, nodes, keep⟩

open Ssz in
/-- The prover's scratch bound on the shipped image returns the Lean bound, and leaves memory as it was. -/
theorem shipped_proveScratch {w : World} (d : Desc) (a size sp : Nat) (mem : Memory)
    (hw : WordsAt w mem a (Plan.words d)) (fits : Driver.Fits (Plan.words d)) (hp : d.wellFormed = .ok ())
    (hsz : size < 2 ^ 64) (stack : w.stackLo + 64 + 256 * (d.nesting + 2) ≤ sp) :
    Returns shippedImage w "ssz_prove_scratch" sp [a.toUInt64, size.toUInt64] mem (proveScratch d size).toUInt64
      mem :=
  shipped_returns (prove_scratch_calls shipped_plan rfl rfl d a size sp mem hw fits hp hsz stack)

end Ssz.Native
