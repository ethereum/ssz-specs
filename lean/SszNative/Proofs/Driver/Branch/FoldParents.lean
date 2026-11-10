import SszNative.Proofs.Driver.Branch.FoldKept

/-! The compiled first pass of a fold level builds the level's parents in order, or refuses as the Lean fold does. -/

namespace EthLib.Consensus.Ssz.Native.Driver.BranchProof

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm

/-- The first entries are a prefix of the entries. -/
theorem entriesAt_take (mem : Memory) (a n i : Nat) (h : i ≤ n) : (entriesAt mem a n).take i = entriesAt mem a i := by
  simp only [entriesAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- A refusal among the first entries is a refusal of all of them. -/
theorem levelParents_error_prefix (depth : Nat) (nodes : List (Nat × ByteArray)) (a b : List (Nat × ByteArray))
    {e : Err} (h : levelParents depth nodes a = .error e) : levelParents depth nodes (a ++ b) = .error e := by
  rw [levelParents_append, h]; rfl

/-- One more entry: the parents so far, then the entry's own. -/
theorem levelParents_snoc (depth : Nat) (nodes : List (Nat × ByteArray)) (a : List (Nat × ByteArray))
    (entry : Nat × ByteArray) {ps : List (Nat × ByteArray)} (h : levelParents depth nodes a = .ok ps) :
    levelParents depth nodes (a ++ [entry]) = (levelParents depth nodes [entry]).map fun qs => ps ++ qs := by
  rw [levelParents_append, h]; rfl

/-- An entry off the level has no parent of its own. -/
theorem levelParents_off (depth : Nat) (nodes : List (Nat × ByteArray)) (index : Nat) (node : ByteArray)
    (off : levelOf index ≠ depth) : levelParents depth nodes [(index, node)] = .ok [] := by
  simp [levelParents, off]

/-- An even entry on the level joins the entry holding the next index. -/
theorem levelParents_even (depth : Nat) (nodes : List (Nat × ByteArray)) (index : Nat) (node : ByteArray)
    (on : levelOf index = depth) (even : index % 2 = 0) :
    levelParents depth nodes [(index, node)] = match nodeAt nodes (index + 1) with
      | some sibling => .ok [(index / 2, combine node sibling)]
      | none => .error .proofIncomplete := by
  simp only [levelParents, on, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, even, beq_self_eq_true]
  cases nodeAt nodes (index + 1) <;> rfl

/-- An odd entry on the level needs the entry holding the index before, and has no parent of its own. -/
theorem levelParents_odd (depth : Nat) (nodes : List (Nat × ByteArray)) (index : Nat) (node : ByteArray)
    (on : levelOf index = depth) (odd : index % 2 = 1) :
    levelParents depth nodes [(index, node)] =
      if (nodeAt nodes (index - 1)).isNone then .error .proofIncomplete else .ok [] := by
  simp only [levelParents, on, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    show (index % 2 == 0) = false by simp; omega]

/-- The first match depends only on the values below the count. -/
theorem firstAt_congr {f g : Nat → UInt64} (key : UInt64) :
    ∀ n, (∀ j < n, f j = g j) → firstAt f key n = firstAt g key n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [firstAt, firstAt_congr key n (fun j hj => h j (by omega)), h n (by omega)]

/-- The entries split at a position: those before it, the one there, and the rest. -/
theorem entriesAt_split (mem : Memory) (a n i : Nat) (h : i < n) :
    entriesAt mem a n = (entriesAt mem a i ++
      [((readLE mem (a + 40 * i) 8).toNat, readNode mem (a + 40 * i + 8))]) ++ (entriesAt mem a n).drop (i + 1) := by
  rw [← entriesAt_succ, ← entriesAt_take mem a n (i + 1) (by omega), List.take_append_drop]

/-- The first pass: arguments kept, parents so far written in order, or the refusal found. -/
private def ParentInv (ready : Memory → Prop) (free : Nat → Prop) (mem : Memory)
    (src count dst depth ctx out : UInt64) (env : Env) (mem' : Memory) : Prop :=
  env 0 = src ∧ env 1 = count ∧ env 2 = dst ∧ env 3 = depth ∧ env 4 = ctx ∧ env 5 = out ∧ env 13 = 0 ∧
    (env 10).toNat ≤ count.toNat ∧ ready mem' ∧ (∀ a, free a → ¬ (dst.toNat ≤ a ∧ a < dst.toNat + 40 * (env 10).toNat) → mem' a = mem a) ∧
    ((env 11 = 0 ∧ (env 6).toNat ≤ count.toNat ∧
        levelParents depth.toNat (entriesAt mem src.toNat count.toNat) (entriesAt mem src.toNat (env 6).toNat) =
          .ok (entriesAt mem' dst.toNat (env 10).toNat)) ∨
      (env 11 = 11 ∧ (env 6).toNat = count.toNat + 1 ∧
        ∃ e, levelParents depth.toNat (entriesAt mem src.toNat count.toNat)
          (entriesAt mem src.toNat count.toNat) = .error e))

/-- What the first pass answers and writes, by the Lean pass's outcome. -/
def ParentsPost (mem' : Memory) (dst out : UInt64) (r : UInt64) :
    Except Err (List (Nat × ByteArray)) → Prop
  | .ok ps => r = 0 ∧ readLE mem' out.toNat 8 = ps.length.toUInt64 ∧ entriesAt mem' dst.toNat ps.length = ps
  | .error _ => r = 11

/--
A call of the first pass answers what the Lean pass refuses, or writes the parents in order and their number.

It keeps the hashing context, and changes no free memory outside the parents' area and the output word.
-/
theorem fold_parents_calls {m : Module} {w : World} {ctx : UInt64} {ready : Memory → Prop} {free : Nat → Prop}
    {room : Nat} (hp : m.fns.lookup "ssz_branch_fold_parents" = some FoldParents.fn)
    (hl : m.fns.lookup "ssz_branch_level" = some Level.fn) (hf : m.fns.lookup "ssz_branch_find" = some Find.fn)
    (hash : PairHashing m w ctx ready free room) {sp : Nat} (deep : w.stackLo + 240 + room ≤ sp)
    (src count dst depth out : UInt64) (mem : Memory) (rd : ready mem)
    (as : w.access src.toNat (40 * count.toNat) = true) (ad : w.access dst.toNat (40 * count.toNat) = true)
    (ao : w.access out.toNat 8 = true)
    (fs : ∀ k < 40 * count.toNat, free (src.toNat + k)) (fd : ∀ k < 40 * count.toNat, free (dst.toNat + k))
    (fo : ∀ k < 8, free (out.toNat + k))
    (ds : Apart (dst.toNat, 40 * count.toNat) (src.toNat, 40 * count.toNat))
    (od : Apart (out.toNat, 8) (dst.toNat, 40 * count.toNat)) :
    ∃ r mem', Calls m w "ssz_branch_fold_parents" sp [src, count, dst, depth, ctx, out] mem r mem' ∧ ready mem' ∧
      ParentsPost mem' dst out r
        (levelParents depth.toNat (entriesAt mem src.toNat count.toNat) (entriesAt mem src.toNat count.toNat)) ∧
      ∀ a, free a → ¬ (dst.toNat ≤ a ∧ a < dst.toNat + 40 * count.toNat) → ¬ (out.toNat ≤ a ∧ a < out.toNat + 8) →
        mem' a = mem a := by
  have frameSize : FoldParents.fn.frame = 19 := by decide
  let E := entriesAt mem src.toNat count.toNat
  have bs := access_bound as
  have bd := access_bound ad
  have bo := access_bound ao
  suffices body : Wp m w (sp - 160) FoldParents.fn.body (entryEnv [src, count, dst, depth, ctx, out]) mem
      fun env mem' => ∃ r, eval w env mem' (Ir.Expr.var 11) = some r ∧ (ready mem' ∧
        ParentsPost mem' dst out r (levelParents depth.toNat E E) ∧
        ∀ a, free a → ¬ (dst.toNat ≤ a ∧ a < dst.toNat + 40 * count.toNat) → ¬ (out.toNat ≤ a ∧ a < out.toNat + 8) →
          mem' a = mem a) by
    obtain ⟨r, mem', call, post⟩ := Calls.of_wp (Q := fun r mem' => ready mem' ∧
        ParentsPost mem' dst out r (levelParents depth.toNat E E) ∧
        ∀ a, free a → ¬ (dst.toNat ≤ a ∧ a < dst.toNat + 40 * count.toNat) → ¬ (out.toNat ≤ a ∧ a < out.toNat + 8) →
          mem' a = mem a)
      (w := w) (sp := sp) (args := [src, count, dst, depth, ctx, out]) (mem := mem) hp (by omega) rfl
      (by rw [frameSize]; exact body)
    exact ⟨r, mem', call, post⟩
  have room' : w.stackLo + room ≤ sp - 160 := by omega
  simp only [FoldParents.fn]
  refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons ?_))))))))
  refine Wp.loop (ParentInv ready free mem src count dst depth ctx out)
    (fun env _ => count.toNat + 1 - (env 6).toNat)
    ⟨by simp [assign, entryEnv], by simp [assign, entryEnv], by simp [assign, entryEnv], by simp [assign, entryEnv],
      by simp [assign, entryEnv], by simp [assign, entryEnv], by simp [assign], by simp [assign], rd, fun _ _ _ => rfl,
      .inl ⟨by simp [assign], by simp [assign], by simp [assign, entriesAt, levelParents]⟩⟩ ?_
  intro env mem' ⟨e0, e1, e2, e3, e4, e5, e13, kc, rd', frame, state⟩
  -- The source entries read as they were, since only the parents' area is written.
  have srcNow : ∀ k < 40 * count.toNat, mem' (src.toNat + k) = mem (src.toNat + k) :=
    fun k hk => frame _ (fs k hk) (by simp only [Apart] at ds; omega)
  have entriesNow : entriesAt mem' src.toNat count.toNat = E := entriesAt_congr srcNow
  refine ⟨_, eval_cmp .b rfl rfl, fun nz => ?_, fun z => ?_⟩
  · have lt : (env 6).toNat < count.toNat := by rw [← e1]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using nz
    have running : env 11 = 0 ∧ levelParents depth.toNat E (entriesAt mem src.toNat (env 6).toNat) =
        .ok (entriesAt mem' dst.toNat (env 10).toNat) := by
      rcases state with ⟨s, _, ok⟩ | ⟨_, e, _⟩
      · exact ⟨s, ok⟩
      · omega
    have kLe : (env 10).toNat ≤ (env 6).toNat := by
      have := levelParents_length depth.toNat E _ _ running.2
      rw [entriesAt_length, entriesAt_length] at this; omega
    obtain ⟨addr, eacc⟩ := entry_addr as (env 6) lt
    have bc := count.toNat_lt
    -- The entry's index, read where nothing was written.
    have word := eval_ld (w := w) (env := env) (mem := mem') (eval_add (a := Ir.Expr.var 0)
      (b := 40 * Ir.Expr.var 6) rfl (eval_mul rfl rfl)) (by rw [e0, addr]; exact access_prefix eacc (by omega))
    rw [e0, addr, readLE_congr mem' mem _ 8 (fun k hk => by
      rw [Nat.add_assoc]; exact srcNow _ (by omega))] at word
    have split := entriesAt_split mem src.toNat count.toNat (env 6).toNat lt
    generalize hx : readLE mem (src.toNat + 40 * (env 6).toNat) 8 = x at word split
    let node := readNode mem (src.toNat + 40 * (env 6).toNat + 8)
    have nodeNow : readNode mem' (src.toNat + 40 * (env 6).toNat + 8) = node :=
      readNode_congr fun k hk => by
        have := srcNow (40 * (env 6).toNat + 8 + k) (by omega)
        rwa [show src.toNat + (40 * (env 6).toNat + 8 + k) = src.toNat + 40 * (env 6).toNat + 8 + k by omega] at this
    -- The search reads the source entries, which are as they were.
    have searchNow : ∀ key, firstAt (big32 mem' src.toNat 40) key count.toNat =
        firstAt (big32 mem src.toNat 40) key count.toNat := fun key =>
      firstAt_congr key _ fun j hj => readLE_congr mem' mem _ 8 fun k hk => by
        rw [Nat.add_assoc]; exact srcNow _ (by omega)
    have fcall := fun key => find_calls (w := w) hf (sp := sp - 160) (by omega) src 40 count key mem' fun j hj =>
      by simpa using access_sub (k := 40 * j) (j := 8) as (by omega)
    have lv := level_calls (w := w) hl (sp := sp - 160) (by omega) x mem'
    have small := log2_lt_64 x
    have next : (env 6 + 1).toNat = (env 6).toNat + 1 := by
      rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
    have afterEnd : ((count + 1).toNat) = count.toNat + 1 := by
      rw [toNat_add_of_lt _ _ (by simp; have := access_bound as; omega)]; simp
    -- A refusal at this entry is a refusal of the whole pass.
    have refuse : ∀ e, levelParents depth.toNat E [(x.toNat, node)] = .error e →
        levelParents depth.toNat E E = .error e := by
      intro e h
      show levelParents depth.toNat E (entriesAt mem src.toNat count.toNat) = _
      rw [split]
      apply levelParents_error_prefix
      rw [levelParents_snoc _ _ _ _ running.2, h]; rfl
    refine Wp.cons (Wp.set word (Wp.cons (Wp.call (values := [x]) rfl ⟨_, mem', lv, ?_⟩)))
    refine Wp.cons (Wp.ite (eval_eq rfl rfl) (fun on => ?_) (fun off => ?_))
    · have onLevel : levelOf x.toNat = depth.toNat := by
        by_cases h : (Nat.log2 x.toNat).toUInt64 = depth
        · show Nat.log2 x.toNat = _
          rw [← h, toNat_ofNat_of_lt _ (by omega)]
        · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, e3, ite_eq_right h] at on
          exact absurd rfl on
      have xParity : (x &&& 1).toNat = x.toNat % 2 := toNat_and_one x
      -- The entry where the search stops, and what the node set holds at the searched index.
      have found : ∀ key : UInt64, (firstAt (big32 mem src.toNat 40) key count.toNat).toUInt64 = count ↔
          nodeAt E key.toNat = none := by
        intro key
        have le := firstAt_le (big32 mem src.toNat 40) key count.toNat
        show _ ↔ nodeAt (entriesAt mem src.toNat count.toNat) key.toNat = none
        rw [nodeAt_entriesAt]
        constructor
        · intro h
          have := congrArg UInt64.toNat h
          rw [toNat_ofNat_of_lt _ (by omega)] at this
          rw [ite_eq_right (by omega)]
        · intro h
          split at h
          · cases h
          · apply UInt64.toNat_inj.mp
            rw [toNat_ofNat_of_lt _ (by omega)]; omega
      have foundAt : ∀ key : UInt64, (firstAt (big32 mem src.toNat 40) key count.toNat) < count.toNat →
          nodeAt E key.toNat = some (readNode mem (src.toNat + 40 * firstAt (big32 mem src.toNat 40) key count.toNat + 8)) :=
        fun key h => by
          show nodeAt (entriesAt mem src.toNat count.toNat) key.toNat = _
          rw [nodeAt_entriesAt, ite_eq_left h]
      refine Wp.cons (Wp.ite (eval_eq (eval_and rfl rfl) rfl) (fun even => ?_) (fun odd => ?_))
      · -- An even index joins the entry holding the next index.
        have xEven : x.toNat % 2 = 0 := by
          by_cases h : x &&& 1 = 0
          · rw [← xParity, h]; rfl
          · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, ite_eq_right h] at even; exact absurd rfl even
        have up : (x + 1).toNat = x.toNat + 1 := by
          rw [toNat_add_of_lt _ _ (by have := x.toNat_lt; simp; omega)]; simp
        have c := fcall (x + 1)
        simp only [UInt64.reduceToNat] at c
        rw [searchNow] at c
        generalize hJ : firstAt (big32 mem src.toNat 40) (x + 1) count.toNat = J at c
        have hJle : J ≤ count.toNat := by rw [← hJ]; exact firstAt_le _ _ _
        refine Wp.cons (Wp.call (values := [src, 40, count, x + 1])
          (by rw [show src = env 0 from e0.symm, show count = env 1 from e1.symm]; rfl) ⟨_, mem', c, ?_⟩)
        refine Wp.cons (Wp.ite (eval_eq rfl rfl) (fun none_ => ?_) (fun some_ => ?_))
        · -- No sibling: the pass is refused.
          have miss : J.toUInt64 = count := by
            by_cases h : J.toUInt64 = count
            · exact h
            · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, e1, ite_eq_right h] at none_; exact absurd rfl none_
          rw [← hJ, found, up] at miss
          refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.nil (Wp.nil (Wp.nil
            (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨?_, ?_⟩))))))))) <;>
            simp only [ParentInv, assign, ↓reduceIte, Nat.reduceEqDiff]
          · refine ⟨e0, e1, e2, e3, e4, e5, e13, kc, rd', frame, .inr ⟨trivial, ?_, .proofIncomplete, refuse _ ?_⟩⟩
            · rw [e1, afterEnd]
            · rw [levelParents_even _ _ _ _ onLevel xEven, miss]
          · rw [e1, afterEnd]; omega
        · -- A sibling: the parent is hashed into the next place, and its index written before it.
          have hit : J < count.toNat := by
            by_cases h : J.toUInt64 = count
            · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, e1, ite_eq_left h] at some_; exact absurd some_ (by decide)
            · rcases Nat.lt_or_eq_of_le hJle with l | l
              · exact l
              · exact absurd (by rw [l]; exact UInt64.ofNat_toNat) h
          have sib := foundAt (x + 1) (by rw [hJ]; exact hit)
          rw [hJ, up] at sib
          have bs := access_bound as
          have bd := access_bound ad
          have kLt : (env 10).toNat < count.toNat := by omega
          obtain ⟨daddr, dacc⟩ := entry_addr ad (env 10) kLt
          have jTo : J.toUInt64.toNat = J := toNat_ofNat_of_lt _ (by omega)
          obtain ⟨jaddr, jacc⟩ := entry_addr as J.toUInt64 (by rw [jTo]; exact hit)
          rw [jTo] at jaddr jacc
          have outN : (env 2 + 40 * env 10 + 8).toNat = dst.toNat + 40 * (env 10).toNat + 8 := by
            rw [toNat_add_of_lt _ _ (by rw [e2, daddr]; simp; omega), e2, daddr]; simp
          have leftN : (env 0 + 40 * env 6 + 8).toNat = src.toNat + 40 * (env 6).toNat + 8 := by
            rw [toNat_add_of_lt _ _ (by rw [e0, addr]; simp; omega), e0, addr]; simp
          have rightN : (env 0 + 40 * J.toUInt64 + 8).toNat = src.toNat + 40 * J + 8 := by
            rw [toNat_add_of_lt _ _ (by rw [e0, jaddr]; simp; omega), e0, jaddr]; simp
          simp only [Apart] at ds
          obtain ⟨mem2, call, rd2, parent, frame2⟩ := hash.pair_node (out := env 2 + 40 * env 10 + 8)
            (left := env 0 + 40 * env 6 + 8) (right := env 0 + 40 * J.toUInt64 + 8) rd' room'
            (by rw [outN]; exact access_sub dacc (by omega)) (by rw [leftN]; exact access_sub eacc (by omega))
            (by rw [rightN]; exact access_sub jacc (by omega))
            (fun k hk => by rw [outN, show dst.toNat + 40 * (env 10).toNat + 8 + k =
              dst.toNat + (40 * (env 10).toNat + 8 + k) by omega]; exact fd _ (by omega))
            (fun k hk => by rw [leftN, show src.toNat + 40 * (env 6).toNat + 8 + k =
              src.toNat + (40 * (env 6).toNat + 8 + k) by omega]; exact fs _ (by omega))
            (fun k hk => by rw [rightN, show src.toNat + 40 * J + 8 + k =
              src.toNat + (40 * J + 8 + k) by omega]; exact fs _ (by omega))
            (by rw [outN, leftN]; simp only [Apart]; omega) (by rw [outN, rightN]; simp only [Apart]; omega)
          rw [← e4] at call
          rw [outN, leftN, rightN, nodeNow] at parent
          rw [outN] at frame2
          have sibNow : readNode mem' (src.toNat + 40 * J + 8) = readNode mem (src.toNat + 40 * J + 8) :=
            readNode_congr fun k hk => by
              have := srcNow (40 * J + 8 + k) (by omega)
              rwa [show src.toNat + (40 * J + 8 + k) = src.toNat + 40 * J + 8 + k by omega] at this
          rw [sibNow] at parent
          have nextK : (env 10 + 1).toNat = (env 10).toNat + 1 := by
            rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
          refine Wp.cons (Wp.call (values := [env 2 + 40 * env 10 + 8, env 0 + 40 * env 6 + 8,
            env 0 + 40 * J.toUInt64 + 8, 1, env 4]) rfl ⟨_, mem2, call, ?_⟩)
          refine Wp.cons (Wp.set (eval_or rfl rfl) (Wp.cons (Wp.store (x := env 2 + 40 * env 10)
            (y := x >>> (1 : Nat).toUInt64) (eval_add rfl (eval_mul rfl rfl)) (eval_shr1 rfl)
            (by rw [e2, daddr]; exact access_prefix dacc (by simp [Width.bytes]))
            (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil (Wp.nil (Wp.nil
              (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨?_, ?_⟩))))))))))) <;>
            simp only [ParentInv, assign, ↓reduceIte, Nat.reduceEqDiff, next, nextK]
          · rw [e2, daddr]
            simp only [Width.bytes]
            refine ⟨e0, e1, trivial, e3, e4, e5, by rw [e13]; rfl, by omega,
              hash.ready_frame _ _ rd2 fun a nf => store_outside _ _ _ _ _ fun inside => nf (by
                rw [show a = dst.toNat + (a - dst.toNat) by omega]; exact fd _ (by omega)),
              fun a fa outside => by
                rw [store_outside _ _ _ _ _ (by omega), frame2 a fa (by omega), frame a fa (by omega)],
              .inl ⟨running.1, by omega, ?_⟩⟩
            rw [entriesAt_succ, hx, levelParents_snoc _ _ _ _ running.2,
              levelParents_even _ _ _ _ onLevel xEven, sib]
            rw [entriesAt_write mem' (store mem2 (dst.toNat + 40 * (env 10).toNat) 8 (qwordByte (x >>> (1 : Nat).toUInt64)))
              dst.toNat (env 10).toNat (x >>> (1 : Nat).toUInt64) (combine node (readNode mem (src.toNat + 40 * J + 8)))
              (fun k hk => by rw [store_outside _ _ _ _ _ (by omega), frame2 _ (by
                rw [show dst.toNat + k = dst.toNat + k by rfl]; exact fd _ (by omega)) (by omega)])
              (readLE_store8 _ _ _)
              (by rw [readNode_congr (fun k hk => store_outside _ _ _ _ _ (by omega)), parent]),
              toNat_shr_one]
            rfl
          · omega
      · -- An odd index needs the entry holding the index before.
        have xOdd : x.toNat % 2 = 1 := by
          by_cases h : x &&& 1 = 0
          · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, ite_eq_left h] at odd; exact absurd odd (by decide)
          · have : (x &&& 1).toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by rw [e]; rfl))
            omega
        have down : (x - 1).toNat = x.toNat - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
        have c := fcall (x - 1)
        simp only [UInt64.reduceToNat] at c
        rw [searchNow] at c
        refine Wp.cons (Wp.call (values := [src, 40, count, x - 1])
          (by rw [show src = env 0 from e0.symm, show count = env 1 from e1.symm]; rfl) ⟨_, mem', c, ?_⟩)
        refine Wp.ite (eval_eq rfl rfl) (fun none_ => ?_) (fun some_ => ?_)
        · -- No entry before: the pass is refused.
          have miss : (firstAt (big32 mem src.toNat 40) (x - 1) count.toNat).toUInt64 = count := by
            by_cases h : (firstAt (big32 mem src.toNat 40) (x - 1) count.toNat).toUInt64 = count
            · exact h
            · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, e1, ite_eq_right h] at none_; exact absurd rfl none_
          rw [found, down] at miss
          refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.nil (Wp.nil
            (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨?_, ?_⟩)))))))) <;>
            simp only [ParentInv, assign, ↓reduceIte, Nat.reduceEqDiff]
          · refine ⟨e0, e1, e2, e3, e4, e5, e13, kc, rd', frame, .inr ⟨trivial, ?_, .proofIncomplete, refuse _ ?_⟩⟩
            · rw [e1, afterEnd]
            · rw [levelParents_odd _ _ _ _ onLevel xOdd, miss]; rfl
          · rw [e1, afterEnd]; omega
        · -- The entry before exists: no parent of its own.
          have there : (firstAt (big32 mem src.toNat 40) (x - 1) count.toNat).toUInt64 ≠ count := by
            intro h
            simp only [assign, ↓reduceIte, Nat.reduceEqDiff, e1, ite_eq_left h] at some_; exact absurd some_ (by decide)
          rw [Ne, found, down] at there
          refine Wp.skip (Wp.nil (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨?_, ?_⟩)))) <;>
            simp only [ParentInv, assign, ↓reduceIte, Nat.reduceEqDiff, next]
          · refine ⟨e0, e1, e2, e3, e4, e5, e13, kc, rd', frame, .inl ⟨running.1, by omega, ?_⟩⟩
            rw [entriesAt_succ, hx, levelParents_snoc _ _ _ _ running.2, levelParents_odd _ _ _ _ onLevel xOdd]
            cases h : nodeAt E (x.toNat - 1) with
            | none => exact absurd h there
            | some _ => simp [Except.map]
          · omega
    · -- An entry off the level has no parent.
      have offLevel : levelOf x.toNat ≠ depth.toNat := by
        intro h
        simp only [assign, ↓reduceIte, Nat.reduceEqDiff, e3] at off
        rw [ite_eq_left (UInt64.toNat_inj.mp (by rw [toNat_ofNat_of_lt _ (by omega)]; exact h))] at off
        exact absurd off (by decide)
      refine Wp.skip (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨?_, ?_⟩)))
      · simp only [ParentInv, assign, ↓reduceIte, Nat.reduceEqDiff, next]
        refine ⟨e0, e1, e2, e3, e4, e5, e13, kc, rd', frame, .inl ⟨running.1, by omega, ?_⟩⟩
        rw [entriesAt_succ, hx, levelParents_snoc _ _ _ _ running.2, levelParents_off _ _ _ _ offLevel]
        simp [Except.map]
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]; omega
  · -- The pass is over: the number of parents goes to the output word.
    have done : ¬ (env 6).toNat < count.toNat := by rw [← e1]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using z
    refine Wp.cons (Wp.ite (eval_ne rfl rfl) (fun bad => ?_) (fun _ => ?_))
    · simp [e13] at bad
    refine Wp.skip (Wp.store (x := out) (y := env 10) (by rw [← e5]; rfl) rfl (by simpa [Width.bytes] using ao)
      ⟨env 11, rfl, ?_, ?_, ?_⟩)
    · exact hash.ready_frame _ _ rd' fun a nf => store_outside _ _ _ _ _ fun inOut => nf (by
        have := fo (a - out.toNat) (by simp [Width.bytes] at inOut; omega)
        rwa [show out.toNat + (a - out.toNat) = a by simp [Width.bytes] at inOut; omega] at this)
    · have outDst : ∀ j < 40 * (env 10).toNat, store mem' out.toNat 8 (qwordByte (env 10)) (dst.toNat + j) =
          mem' (dst.toNat + j) := fun j hj => store_outside _ _ _ _ _ (by simp only [Apart] at od; omega)
      rcases state with ⟨s, _, ok⟩ | ⟨s, _, e, err⟩
      · rw [show (env 6).toNat = count.toNat by omega] at ok
        show ParentsPost _ dst out (env 11) (levelParents depth.toNat E E)
        rw [show levelParents depth.toNat E E = .ok (entriesAt mem' dst.toNat (env 10).toNat) from ok]
        refine ⟨s, ?_, ?_⟩
        · rw [entriesAt_length]; simp only [Width.bytes, readLE_store8]
          apply UInt64.toNat_inj.mp
          rw [toNat_ofNat_of_lt _ (env 10).toNat_lt]
        · rw [entriesAt_length]; exact entriesAt_congr outDst
      · show ParentsPost _ dst out (env 11) (levelParents depth.toNat E E)
        rw [show levelParents depth.toNat E E = .error e from err]
        exact s
    · intro a fa outD outO
      rw [store_outside _ _ _ _ _ (by simpa [Width.bytes] using outO), frame a fa (by omega)]

end EthLib.Consensus.Ssz.Native.Driver.BranchProof
