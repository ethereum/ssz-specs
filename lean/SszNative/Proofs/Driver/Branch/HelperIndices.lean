import SszNative.Proofs.Driver.Branch.Select

/-! The compiled helper indices answer what the specification's helper indices answer. -/

namespace EthLib.Consensus.Ssz.Native.Driver.BranchProof

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm

/-- The word a helper-index computation answers: zero when it succeeds, or the code of its refusal. -/
def helperCode : Except Err (List Nat) → UInt64
  | .ok _ => 0
  | .error e => answerCode (.error e)

/-- The functions of the helper-index computation, each under its exported name. -/
structure HelperFns (m : Module) : Prop where
  /-- The search. -/
  find : m.fns.lookup "ssz_branch_find" = some Find.fn
  /-- The claim check. -/
  check : m.fns.lookup "ssz_branch_check_claims" = some CheckClaims.fn
  /-- The path walk. -/
  collect : m.fns.lookup "ssz_branch_paths" = some CollectPaths.fn
  /-- The candidate walk. -/
  candidates : m.fns.lookup "ssz_branch_candidates" = some Candidates.fn
  /-- The selection. -/
  select : m.fns.lookup "ssz_branch_select" = some SelectDesc.fn
  /-- The helper indices. -/
  helpers : m.fns.lookup "ssz_branch_helpers" = some HelperIndices.fn

/-- A refusal is never answered as zero. -/
theorem answerCode_error_ne_zero (e : Err) : answerCode (.error e) ≠ 0 := by
  cases e <;> simp only [answerCode] <;> decide

/-- A refusal of the claims is the refusal of the helper indices. -/
theorem getHelperIndices_error {l : List Nat} {e : Err} (h : rejectRelated l = .error e) :
    getHelperIndices l = .error e := by
  simp [getHelperIndices, h, bind, Except.bind]

/--
A call of the helper-index computation answers what the specification answers on the claims.

When it succeeds, the helper indices are written, and their number is written to the output word.
Only the scratch area, the helper area, and the output word change.
-/
theorem helper_indices_calls {m : Module} {w : World} (fns : HelperFns m) {sp : Nat} (room : w.stackLo + 304 ≤ sp)
    (indices count scratch helpers out : UInt64) (mem : Memory)
    (ai : w.access indices.toNat (8 * count.toNat) = true) (as : w.access scratch.toNat (1024 * count.toNat) = true)
    (ah : w.access helpers.toNat (512 * count.toNat) = true) (ao : w.access out.toNat 8 = true)
    (si : Apart (scratch.toNat, 1024 * count.toNat) (indices.toNat, 8 * count.toNat))
    (hs : Apart (helpers.toNat, 512 * count.toNat) (scratch.toNat, 1024 * count.toNat))
    (oi : Apart (out.toNat, 8) (helpers.toNat, 512 * count.toNat)) :
    ∃ mem', Calls m w "ssz_branch_helpers" sp [indices, count, scratch, helpers, out] mem
        (helperCode (getHelperIndices (wordsAt mem indices.toNat count.toNat))) mem' ∧
      (∀ hs, getHelperIndices (wordsAt mem indices.toNat count.toNat) = .ok hs →
        readLE mem' out.toNat 8 = hs.length.toUInt64 ∧ wordsAt mem' helpers.toNat hs.length = hs) ∧
      ∀ a, ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + 1024 * count.toNat) →
        ¬ (helpers.toNat ≤ a ∧ a < helpers.toNat + 512 * count.toNat) → ¬ (out.toNat ≤ a ∧ a < out.toNat + 8) →
        mem' a = mem a := by
  have frameSize : HelperIndices.fn.frame = 13 := by decide
  generalize hL : wordsAt mem indices.toNat count.toNat = L
  have bs := access_bound as
  have bh := access_bound ah
  have bo := access_bound ao
  have bi := access_bound ai
  let Post := fun (r : UInt64) (mem' : Memory) => r = helperCode (getHelperIndices L) ∧
    (∀ hs, getHelperIndices L = .ok hs → readLE mem' out.toNat 8 = hs.length.toUInt64 ∧
      wordsAt mem' helpers.toNat hs.length = hs) ∧
    ∀ a, ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + 1024 * count.toNat) →
      ¬ (helpers.toNat ≤ a ∧ a < helpers.toNat + 512 * count.toNat) → ¬ (out.toNat ≤ a ∧ a < out.toNat + 8) →
      mem' a = mem a
  suffices body : Wp m w (sp - 112) HelperIndices.fn.body (entryEnv [indices, count, scratch, helpers, out]) mem
      fun env mem' => ∃ r, eval w env mem' (Ir.Expr.var 5) = some r ∧ Post r mem' by
    obtain ⟨r, mem', call, hr, words, frame⟩ := Calls.of_wp (Q := Post)
      (w := w) (sp := sp) (args := [indices, count, scratch, helpers, out]) (mem := mem) fns.helpers (by omega) rfl
      (by rw [frameSize]; exact body)
    rw [hr] at call
    exact ⟨mem', call, words, frame⟩
  simp only [HelperIndices.fn]
  -- The claims are checked first.
  have check := check_claims_calls (w := w) fns.check fns.find (sp := sp - 112) (by omega) indices count mem ai
  rw [hL] at check
  refine Wp.cons (Wp.call (values := [indices, count]) rfl ⟨_, mem, check, ?_⟩)
  refine Wp.cons (Wp.ite (eval_eq rfl rfl) (fun ok => ?_) (fun refused => ?_))
  · -- The claims pass: paths, candidates, then the selection.
    have accepted : rejectRelated L = .ok () := by
      cases h : rejectRelated L with
      | ok u => rfl
      | error e =>
        simp only [assign, ↓reduceIte, h, unitCode, ite_eq_right (answerCode_error_ne_zero e)] at ok
        exact absurd rfl ok
    let P := L.flatMap pathOf
    have lenP : P.length ≤ 63 * count.toNat := by
      have := flatMap_pathOf_length mem indices.toNat count.toNat
      rw [hL] at this; exact this
    have collect := collect_paths_calls (w := w) fns.collect (sp := sp - 112) (by omega) indices count scratch mem ai
      (access_prefix as (by omega)) (Apart.sub si (by omega))
    rw [hL] at collect
    obtain ⟨mem1, call1, wordsP, frame1⟩ := collect
    refine Wp.cons (Wp.call (values := [indices, count, scratch]) rfl ⟨_, mem1, call1, ?_⟩)
    have pTo : P.length.toUInt64.toNat = P.length := toNat_ofNat_of_lt _ (by have := count.toNat_lt; omega)
    have candAddr : (scratch + 512 * count).toNat = scratch.toNat + 512 * count.toNat := by
      rw [toNat_addr _ _ _ (by simp; omega)]; simp
    have cands := candidates_calls (w := w) fns.candidates fns.find (sp := sp - 112) (by omega) scratch
      P.length.toUInt64 (scratch + 512 * count) mem1 (by rw [pTo]; exact access_prefix as (by omega))
      (by rw [pTo, candAddr]; exact access_sub as (by omega))
      (by rw [pTo, candAddr]; simp only [Apart]; omega)
    rw [pTo, show wordsAt mem1 scratch.toNat P.length = P from wordsP] at cands
    obtain ⟨mem2, call2, wordsC, frame2⟩ := cands
    refine Wp.cons (Wp.call (values := [scratch, P.length.toUInt64, scratch + 512 * count]) rfl
      ⟨_, mem2, call2, ?_⟩)
    let C := candidatesOf P
    have lenC : C.length ≤ P.length := Nat.le_trans (List.length_filter_le _ _) (by simp)
    have cTo : C.length.toUInt64.toNat = C.length := toNat_ofNat_of_lt _ (by have := count.toNat_lt; omega)
    have sel := select_calls (w := w) fns.select (sp := sp - 112) (by omega) (scratch + 512 * count)
      C.length.toUInt64 helpers mem2 (by rw [cTo, candAddr]; exact access_sub as (by omega))
      (by rw [cTo]; exact access_prefix ah (by omega))
      (by rw [cTo, candAddr]; simp only [Apart] at hs ⊢; omega)
    rw [cTo, candAddr, show wordsAt mem2 (scratch.toNat + 512 * count.toNat) C.length = C by rw [← candAddr]; exact wordsC] at sel
    obtain ⟨S, mem3, call3, wordsS, desc, members, frame3⟩ := sel
    refine Wp.cons (Wp.call (values := [scratch + 512 * count, C.length.toUInt64, helpers]) rfl
      ⟨_, mem3, call3, ?_⟩)
    have helpersOk : getHelperIndices L = .ok S := getHelperIndices_eq accepted desc members
    have lenS : S.length ≤ C.length := length_le_of_pairwise desc fun x hx => (members x).mp hx
    refine Wp.store (x := out) (y := S.length.toUInt64) rfl rfl (by simpa [Width.bytes] using ao)
      (Wp.nil ⟨_, rfl, ?_, ?_, ?_⟩)
    · simp [assign, helperCode, helpersOk, accepted, unitCode]
    · intro hs' h
      rw [helpersOk] at h; cases h
      refine ⟨by simp [Width.bytes, readLE_store8], ?_⟩
      rw [wordsAt_congr (fun k hk => store_outside _ _ _ _ _ (by simp only [Apart] at oi; simp [Width.bytes]; omega))]
      exact wordsS
    · intro a outS outH outO
      rw [store_outside _ _ _ _ _ (by simpa [Width.bytes] using outO), frame3 a (by omega), frame2 a (by omega),
        frame1 a (by omega)]
  · -- A refusal is answered as it is, with nothing written.
    cases accepted : rejectRelated L with
    | ok u =>
      simp [assign, accepted, unitCode] at refused
    | error e =>
      refine Wp.skip (Wp.nil ⟨_, rfl, ?_, ?_, fun _ _ _ _ => rfl⟩)
      · simp [assign, unitCode, helperCode, getHelperIndices_error accepted]
      · intro hs h; rw [getHelperIndices_error accepted] at h; cases h

end EthLib.Consensus.Ssz.Native.Driver.BranchProof
