import SszNative.Proofs.Driver.Branch.Copy

/-! The compiled second pass of a fold level keeps the entries off the level, in order. -/

namespace Ssz.Native.Driver.BranchProof

open Ssz.Native.Ir Ssz.Native.Asm

/-- An entry address inside a usable node set does not wrap. -/
theorem entry_addr {w : World} {a : UInt64} {n : Nat} (acc : w.access a.toNat (40 * n) = true) (i : UInt64)
    (hi : i.toNat < n) : (a + 40 * i).toNat = a.toNat + 40 * i.toNat ∧ w.access (a.toNat + 40 * i.toNat) 40 = true := by
  have := access_bound acc
  exact ⟨by rw [toNat_addr _ _ _ (by simp; omega)]; simp, access_sub acc (by omega)⟩

/-- Memories agreeing on the entries' bytes read the same entries. -/
theorem entriesAt_congr {mem mem' : Memory} {a n : Nat} (h : ∀ k < 40 * n, mem' (a + k) = mem (a + k)) :
    entriesAt mem' a n = entriesAt mem a n := by
  simp only [entriesAt]
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  have word : readLE mem' (a + 40 * j) 8 = readLE mem (a + 40 * j) 8 :=
    readLE_congr mem' mem (a + 40 * j) 8 fun k hk => by
      have := h (40 * j + k) (by omega); rwa [show a + (40 * j + k) = a + 40 * j + k by omega] at this
  have node : readNode mem' (a + 40 * j + 8) = readNode mem (a + 40 * j + 8) :=
    readNode_congr fun k hk => by
      have := h (40 * j + 8 + k) (by omega); rwa [show a + (40 * j + 8 + k) = a + 40 * j + 8 + k by omega] at this
  rw [word, node]

/-- One more entry, written after the others: the entries so far, then it. -/
theorem entriesAt_write (mem mem' : Memory) (a n : Nat) (index : UInt64) (node : ByteArray)
    (keep : ∀ k < 40 * n, mem' (a + k) = mem (a + k)) (word : readLE mem' (a + 40 * n) 8 = index)
    (bytes : readNode mem' (a + 40 * n + 8) = node) :
    entriesAt mem' a (n + 1) = entriesAt mem a n ++ [(index.toNat, node)] := by
  rw [entriesAt_succ, entriesAt_congr keep, word, bytes]

/-- The entries off a level, one more entry read: the kept ones so far, then it if it is off the level. -/
theorem levelKept_succ (depth : Nat) (mem : Memory) (a n : Nat) :
    levelKept depth (entriesAt mem a (n + 1)) = levelKept depth (entriesAt mem a n) ++
      (if levelOf (readLE mem (a + 40 * n) 8).toNat != depth then
        [((readLE mem (a + 40 * n) 8).toNat, readNode mem (a + 40 * n + 8))] else []) := by
  rw [entriesAt_succ, levelKept, List.filter_append]
  split <;> simp_all [levelKept]

/-- The second pass: the entries kept so far are written in order. -/
private def KeptInv (mem : Memory) (src count dst depth : UInt64) (env : Env) (mem' : Memory) : Prop :=
  env 0 = src ∧ env 1 = count ∧ env 2 = dst ∧ env 3 = depth ∧ (env 4).toNat ≤ count.toNat ∧
    (∀ a, ¬ (dst.toNat ≤ a ∧ a < dst.toNat + 40 * (env 6).toNat) → mem' a = mem a) ∧
    entriesAt mem' dst.toNat (env 6).toNat = levelKept depth.toNat (entriesAt mem src.toNat (env 4).toNat)

/-- A call of the second pass copies the entries off the level in order and returns how many. -/
theorem fold_kept_calls {m : Module} {w : World} (hk : m.fns.lookup "ssz_branch_fold_kept" = some FoldKept.fn)
    (hl : m.fns.lookup "ssz_branch_level" = some Level.fn) {sp : Nat} (room : w.stackLo + 128 ≤ sp)
    (src count dst depth : UInt64) (mem : Memory)
    (as : w.access src.toNat (40 * count.toNat) = true) (ad : w.access dst.toNat (40 * count.toNat) = true)
    (apart : Apart (dst.toNat, 40 * count.toNat) (src.toNat, 40 * count.toNat)) :
    ∃ mem', Calls m w "ssz_branch_fold_kept" sp [src, count, dst, depth] mem
        (levelKept depth.toNat (entriesAt mem src.toNat count.toNat)).length.toUInt64 mem' ∧
      entriesAt mem' dst.toNat (levelKept depth.toNat (entriesAt mem src.toNat count.toNat)).length =
        levelKept depth.toNat (entriesAt mem src.toNat count.toNat) ∧
      ∀ a, ¬ (dst.toNat ≤ a ∧ a < dst.toNat + 40 * count.toNat) → mem' a = mem a := by
  have frameSize : FoldKept.fn.frame = 11 := by decide
  generalize hK : levelKept depth.toNat (entriesAt mem src.toNat count.toNat) = K
  have bs := access_bound as
  have bd := access_bound ad
  suffices body : Wp m w (sp - 96) FoldKept.fn.body (entryEnv [src, count, dst, depth]) mem
      fun env mem' => ∃ r, eval w env mem' (Ir.Expr.var 6) = some r ∧ (r = K.length.toUInt64 ∧
        entriesAt mem' dst.toNat K.length = K ∧
        ∀ a, ¬ (dst.toNat ≤ a ∧ a < dst.toNat + 40 * count.toNat) → mem' a = mem a) by
    obtain ⟨r, mem', call, hr, words, frame⟩ := Calls.of_wp (Q := fun r mem' => r = K.length.toUInt64 ∧
        entriesAt mem' dst.toNat K.length = K ∧
        ∀ a, ¬ (dst.toNat ≤ a ∧ a < dst.toNat + 40 * count.toNat) → mem' a = mem a)
      (w := w) (sp := sp) (args := [src, count, dst, depth]) (mem := mem) hk (by omega) rfl
      (by rw [frameSize]; exact body)
    rw [hr] at call
    exact ⟨mem', call, words, frame⟩
  simp only [FoldKept.fn]
  refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons ?_))))
  refine Wp.loop (KeptInv mem src count dst depth) (fun env _ => count.toNat - (env 4).toNat)
    ⟨by simp [assign, entryEnv], by simp [assign, entryEnv], by simp [assign, entryEnv], by simp [assign, entryEnv],
      by simp [assign], fun _ _ => rfl, by simp [assign, entriesAt, levelKept]⟩ ?_
  intro env mem' ⟨e0, e1, e2, e3, le, frame, kept⟩
  refine ⟨_, eval_cmp .b rfl rfl, fun nz => ?_, fun z => ?_⟩
  · have lt : (env 4).toNat < count.toNat := by rw [← e1]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using nz
    have lenK : (env 6).toNat = (levelKept depth.toNat (entriesAt mem src.toNat (env 4).toNat)).length := by
      rw [← kept, entriesAt_length]
    have kLe : (env 6).toNat ≤ (env 4).toNat := by
      rw [lenK]; exact Nat.le_trans (List.length_filter_le _ _) (by rw [entriesAt_length]; exact Nat.le_refl _)
    obtain ⟨addr, eacc⟩ := entry_addr as (env 4) lt
    -- The source entry reads as it was, since only the destination is written.
    have same : ∀ k < 40, mem' (src.toNat + 40 * (env 4).toNat + k) = mem (src.toNat + 40 * (env 4).toNat + k) :=
      fun k hk => frame _ (by simp only [Apart] at apart; omega)
    have word := eval_ld (w := w) (env := env) (mem := mem') (eval_add (a := Ir.Expr.var 0)
      (b := 40 * Ir.Expr.var 4) rfl (eval_mul rfl rfl)) (by rw [e0, addr]; exact access_prefix eacc (by omega))
    rw [e0, addr, readLE_congr mem' mem _ 8 (fun k hk => same k (by omega))] at word
    generalize hx : readLE mem (src.toNat + 40 * (env 4).toNat) 8 = x at word
    have lv := level_calls (w := w) hl (sp := sp - 96) (by omega) x mem'
    refine Wp.cons (Wp.call (values := [x]) (by simp only [List.mapM_cons, List.mapM_nil, word]; rfl)
      ⟨_, mem', lv, ?_⟩)
    have next : (env 4 + 1).toNat = (env 4).toNat + 1 := by
      have := count.toNat_lt
      rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
    have small := log2_lt_64 x
    refine Wp.cons (Wp.ite (eval_ne rfl rfl) (fun off => ?_) (fun on => ?_))
    · -- An entry off the level is copied after the kept ones.
      have offLevel : Nat.log2 x.toNat ≠ depth.toNat := by
        intro h
        simp only [assign, ↓reduceIte, Nat.reduceEqDiff, e3] at off
        rw [if_pos (UInt64.toNat_inj.mp (by rw [toNat_ofNat_of_lt _ (by omega), h]))] at off
        exact off rfl
      obtain ⟨daddr, dacc⟩ := entry_addr ad (env 6) (by omega)
      have nodeSrc : (env 0 + 40 * env 4 + 8).toNat = src.toNat + 40 * (env 4).toNat + 8 := by
        rw [toNat_add_of_lt _ _ (by rw [e0, addr]; simp; omega), e0, addr]; simp
      have nodeDst : (env 2 + 40 * env 6 + 8).toNat = dst.toNat + 40 * (env 6).toNat + 8 := by
        rw [toNat_add_of_lt _ _ (by rw [e2, daddr]; simp; omega), e2, daddr]; simp
      let env1 := assign env 5 (Nat.log2 x.toNat).toUInt64
      refine Wp.append (Wp.append (Wp.cons (Wp.store (x := env 2 + 40 * env 6) (y := x)
        (eval_add (a := Ir.Expr.var 2) (b := 40 * Ir.Expr.var 6) rfl (eval_mul rfl rfl)) word
        (by rw [e2, daddr]; exact access_prefix dacc (by simp [Width.bytes])) (Wp.nil ?_))))
      refine (copy32_wp (d := env 2 + 40 * env 6 + 8) (s := env 0 + 40 * env 4 + 8)
        (fun _ => eval_add (eval_add rfl (eval_mul rfl rfl)) rfl) (fun _ => eval_add (eval_add rfl (eval_mul rfl rfl)) rfl)
        (by rw [nodeDst]; exact access_sub dacc (by omega)) (by rw [nodeSrc]; exact access_sub eacc (by omega))
        (by rw [nodeDst, nodeSrc]; simp only [Apart] at apart ⊢; omega) fun mem2 copied outside => ?_)
      have daddr' : (env 2 + 40 * env 6).toNat = dst.toNat + 40 * (env 6).toNat := by rw [e2, daddr]
      simp only [nodeDst, nodeSrc, daddr', Width.bytes] at copied outside
      have nextK : (env 6 + 1).toNat = (env 6).toNat + 1 := by
        have := count.toNat_lt
        rw [toNat_add_of_lt _ _ (by simp; omega)]; simp
      refine Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨?_, ?_⟩)))))
      · simp only [KeptInv, assign, ↓reduceIte, Nat.reduceEqDiff, next, nextK]
        refine ⟨e0, e1, e2, e3, by omega, fun a ha => ?_, ?_⟩
        · rw [outside a (by omega), store_outside _ _ _ _ _ (by omega)]
          exact frame a (by omega)
        · -- The new entry: its index word, then its node, after the kept ones.
          have keepEq : ∀ j < 40 * (env 6).toNat, mem2 (dst.toNat + j) = mem' (dst.toNat + j) := by
            intro j hj
            rw [outside _ (by omega), store_outside _ _ _ _ _ (by omega)]
          have wordEq : readLE mem2 (dst.toNat + 40 * (env 6).toNat) 8 = x := by
            rw [readLE_congr mem2 (store mem' (dst.toNat + 40 * (env 6).toNat) 8 (qwordByte x)) _ 8
              (fun j hj => outside _ (by omega)), readLE_store8]
          have nodeEq : readNode mem2 (dst.toNat + 40 * (env 6).toNat + 8) =
              readNode mem (src.toNat + 40 * (env 4).toNat + 8) := by
            apply readNode_ext
            intro j hj
            have s1 := same (8 + j) (by omega)
            rw [show src.toNat + 40 * (env 4).toNat + (8 + j) = src.toNat + 40 * (env 4).toNat + 8 + j by omega] at s1
            have far : ¬ (dst.toNat + 40 * (env 6).toNat ≤ src.toNat + 40 * (env 4).toNat + 8 + j ∧
                src.toNat + 40 * (env 4).toNat + 8 + j < dst.toNat + 40 * (env 6).toNat + 8) := by
              simp only [Apart] at apart; omega
            rw [copied j hj, store_outside _ _ _ _ _ far, s1]
          rw [entriesAt_write mem' mem2 dst.toNat (env 6).toNat x _ keepEq wordEq nodeEq, kept, levelKept_succ, hx]
          have this : (levelOf x.toNat != depth.toNat) = true := by simpa [levelOf] using offLevel
          rw [if_pos this]
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]; omega
    · -- An entry on the level is left for the first pass.
      have onLevel : Nat.log2 x.toNat = depth.toNat := by
        by_cases h : (Nat.log2 x.toNat).toUInt64 = depth
        · rw [← h, toNat_ofNat_of_lt _ (by omega)]
        · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, e3, if_neg h] at on
          exact absurd on (by decide)
      refine Wp.skip (Wp.cons (Wp.set (eval_add rfl rfl) (Wp.nil ⟨?_, ?_⟩)))
      · simp only [KeptInv, assign, ↓reduceIte, Nat.reduceEqDiff, next]
        refine ⟨e0, e1, e2, e3, by omega, frame, ?_⟩
        rw [kept, levelKept_succ, hx]
        have this : (levelOf x.toNat != depth.toNat) = false := by simpa [levelOf] using onLevel
        rw [if_neg (by rw [this]; decide), List.append_nil]
      · simp only [assign, ↓reduceIte, Nat.reduceEqDiff, next]; omega
  · -- Every entry was read.
    have done : ¬ (env 4).toNat < count.toNat := by rw [← e1]; simpa [Cond.holds, UInt64.lt_iff_toNat_lt] using z
    rw [show (env 4).toNat = count.toNat by omega, hK] at kept
    have len : (env 6).toNat = K.length := by rw [← kept, entriesAt_length]
    have bound : K.length ≤ count.toNat := by
      rw [← hK]; exact Nat.le_trans (List.length_filter_le _ _) (by rw [entriesAt_length]; exact Nat.le_refl _)
    refine Wp.nil ⟨env 6, rfl, ?_, by rw [← len]; exact kept, fun a ha => frame a (by omega)⟩
    apply UInt64.toNat_inj.mp
    rw [len, toNat_ofNat_of_lt _ (by have := count.toNat_lt; omega)]

end Ssz.Native.Driver.BranchProof
