import SszNative.Proofs.Driver.TreeStore.Parents

/-!
The update driver hashes one level's parents in a single call.

Adjacent parents have their children side by side in the heap, so their pairs are hashed in place.
Otherwise the children are gathered into a run of pairs in the scratch buffer, hashed into digests there, and each
digest is copied back to its parent.
Either way, each parent ends as the hash of its two children, and nothing else in the tree changes.
-/

namespace Ssz.Native.Driver

open Ssz Ssz.Native.Asm Ssz.Native.Ir

/--
What the update driver needs: its context, the tree, the indices, and a scratch buffer of 104 bytes per index.

The scratch buffer holds the list of nodes, 8 bytes each, then the gathered pairs, 64 bytes each, then the digests,
32 bytes each.
-/
structure UpdatePre (w : World) (mem : Memory) (tree K indices c scratch ctx table zeros pad : Nat) (mask : UInt64) :
    Prop where
  /-- The context, its tables, and the padding area. -/
  ctxOk : StoreCtx w mem ctx table zeros pad mask
  /-- The width fits a word with room to spare. -/
  narrow : K < 58
  /-- The tree buffer lies in memory the program may use. -/
  treeAccess : w.access tree (64 * 2 ^ K) = true
  /-- A node past the tree's end is still within reach, as the kernels' moved pointers need. -/
  treeReach : tree + 64 * 2 ^ K + 32 ≤ 2 ^ 63
  /-- The indices lie in memory the program may use. -/
  indicesAccess : w.access indices (8 * c) = true
  /-- So does the scratch buffer. -/
  scratchAccess : w.access scratch (104 * c) = true
  /-- The scratch buffer misses the tree. -/
  scratchTree : Apart (scratch, 104 * c) (tree, 64 * 2 ^ K)
  /-- It misses the indices. -/
  scratchIndices : Apart (scratch, 104 * c) (indices, 8 * c)
  /-- It misses the context. -/
  scratchCtx : Apart (ctx, 32) (scratch, 104 * c)
  /-- It misses the constant table. -/
  scratchTable : Apart (scratch, 104 * c) (table, Kernel.tableSize)
  /-- It misses the zero-tree roots. -/
  scratchZeros : Apart (scratch, 104 * c) (zeros, 32 * (zeroHeights + 1))
  /-- It misses the padding area. -/
  scratchPad : Apart (pad, 1536) (scratch, 104 * c)
  /-- The tree misses the zero-tree roots. -/
  treeZeros : Apart (tree, 64 * 2 ^ K) (zeros, 32 * (zeroHeights + 1))
  /-- It misses the constant table. -/
  treeTable : Apart (tree, 64 * 2 ^ K) (table, Kernel.tableSize)
  /-- It misses the context. -/
  treeCtx : Apart (ctx, 32) (tree, 64 * 2 ^ K)
  /-- It misses the padding area. -/
  treePad : Apart (pad, 1536) (tree, 64 * 2 ^ K)

/-- The update driver's variables a level's hashing reads and keeps. -/
def HashVals (e : Env) (tree ctx scratch c k : Nat) : Prop :=
  e 0 = UInt64.ofNat tree ∧ e 5 = UInt64.ofNat ctx ∧ e 6 = UInt64.ofNat scratch ∧
    e 7 = UInt64.ofNat (scratch + 8 * c) ∧ e 8 = UInt64.ofNat (scratch + 8 * c + 64 * c) ∧
    e 9 = UInt64.ofNat k ∧ e 15 = 0

/-- Writing a variable a level's hashing does not keep leaves the kept ones. -/
theorem HashVals.assign {e : Env} {tree ctx scratch c k x : Nat} {v : UInt64} (r : HashVals e tree ctx scratch c k)
    (hx : x = 10 ∨ x = 12 ∨ x = 13 ∨ x = 14 ∨ x = 16 ∨ x = 17 ∨ x = 18) :
    HashVals (Asm.assign e x v) tree ctx scratch c k := by
  obtain ⟨a, b, c', d, f, g, i⟩ := r
  exact ⟨(assign_ne (by omega)).trans a, (assign_ne (by omega)).trans b, (assign_ne (by omega)).trans c',
    (assign_ne (by omega)).trans d, (assign_ne (by omega)).trans f, (assign_ne (by omega)).trans g,
    (assign_ne (by omega)).trans i⟩

/-- The kept variables survive a copy loop over the loop index and two address variables. -/
theorem HashVals.agree {e0 e : Env} {tree ctx scratch c k : Nat} (r : HashVals e0 tree ctx scratch c k)
    (ag : Agree e0 e 10 18 17) : HashVals e tree ctx scratch c k := by
  obtain ⟨a, b, c', d, f, g, i⟩ := r
  exact ⟨(ag 0 (by decide) (by decide) (by decide)).trans a, (ag 5 (by decide) (by decide) (by decide)).trans b,
    (ag 6 (by decide) (by decide) (by decide)).trans c', (ag 7 (by decide) (by decide) (by decide)).trans d,
    (ag 8 (by decide) (by decide) (by decide)).trans f, (ag 9 (by decide) (by decide) (by decide)).trans g,
    (ag 15 (by decide) (by decide) (by decide)).trans i⟩

/-- The same, for a copy loop whose two address variables come in the other order. -/
theorem HashVals.agree' {e0 e : Env} {tree ctx scratch c k : Nat} (r : HashVals e0 tree ctx scratch c k)
    (ag : Agree e0 e 10 17 18) : HashVals e tree ctx scratch c k :=
  r.agree fun y a b c' => ag y a c' b

/-- The memory a level's hashing may change: the pairs and digests, the padding area, and the parents. -/
def RehashFrame (mm mm' : Memory) (tree scratch c pad k : Nat) (q : Nat → Nat) : Prop :=
  ∀ a, ¬ (scratch + 8 * c ≤ a ∧ a < scratch + 104 * c) → ¬ (pad ≤ a ∧ a < pad + 1536) →
    (∀ i < k, ¬ (tree + 32 * q i ≤ a ∧ a < tree + 32 * q i + 32)) → mm' a = mm a

set_option maxHeartbeats 8000000 in
/--
Hashing one level's parents leaves each parent as the hash of its two children.

The parents are the list's entries, sorted and each once, all at one height of the tree.
-/
theorem rehash_ends {m : Module} {w : World} {sp : Nat} {mem : Memory}
    {tree K indices c scratch ctx table zeros pad : Nat} {mask : UInt64} (okP : HashCalls m w .pairs)
    (pre : UpdatePre w mem tree K indices c scratch ctx table zeros pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + hashStack ≤ sp)
    {e : Env} {mm : Memory} {h k : Nat} (ctxm : StoreCtx w mm ctx table zeros pad mask)
    (vals : HashVals e tree ctx scratch c k) (pv : e 12 = UInt64.ofNat (slotWord mm scratch (k - 1)))
    (below : h < K) (k1 : 1 ≤ k) (kc : k ≤ c)
    (sorted : ∀ i j, i < j → j < k → slotWord mm scratch i < slotWord mm scratch j)
    (level : ∀ i < k, 2 ^ (K - (h + 1)) ≤ slotWord mm scratch i ∧ slotWord mm scratch i < 2 ^ (K - h)) :
    Ends m w sp e mm (.block [Stmt.assign TreeUpdate.first (Expr.ld (Expr.var 6)),
      Stmt.ifElse (Expr.eq (Expr.var 12 - Expr.var 14 + 1) (Expr.var 9)) TreeUpdate.adjacent
        TreeUpdate.scattered]) fun e' mm' =>
      HashVals e' tree ctx scratch c k ∧
      (∀ i < k, nodeAt mm' (tree + 32 * slotWord mm scratch i) =
        combine (nodeAt mm (tree + 64 * slotWord mm scratch i)) (nodeAt mm (tree + 64 * slotWord mm scratch i + 32))) ∧
      RehashFrame mm mm' tree scratch c pad k (slotWord mm scratch) := by
  obtain ⟨v0, v5, v6, v7, v8, v9, v15⟩ := vals
  have bt := access_bound pre.treeAccess
  have bs := access_bound pre.scratchAccess
  have tr := pre.treeReach
  have st := pre.scratchTree
  have stab := pre.scratchTable
  have sz := pre.scratchZeros
  have sc := pre.scratchCtx
  have sp' := pre.scratchPad
  have tz := pre.treeZeros
  have tt := pre.treeTable
  have tc := pre.treeCtx
  have tp := pre.treePad
  simp only [Apart] at st stab sz sc sp' tz tt tc tp
  have hz : zeroHeights = 64 := rfl
  have wK : 2 ^ K < 2 ^ 58 := Nat.pow_lt_pow_right (by decide) pre.narrow
  have twice : 2 ^ (K - h) = 2 * 2 ^ (K - (h + 1)) := by
    rw [show K - h = (K - (h + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  have up : 2 ^ (K - h) ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) (by omega)
  generalize hs : 2 ^ (K - h) = S at twice up level
  generalize hf : 2 ^ (K - (h + 1)) = F at twice level
  generalize hq : slotWord mm scratch = q at sorted level pv ⊢
  have q0 := level 0 k1
  have ql := level (k - 1) (by omega)
  -- The first parent, then whether the parents are adjacent.
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (by
    have := eval_slotWord0 (w := w) (env := e) (mem := mm) (eval_var v6) (access_sub pre.scratchAccess (by omega)
      (by omega))
    rw [hq] at this
    exact this)) ?_
  have le0 : q 0 ≤ q (k - 1) := by
    by_cases k1' : k = 1
    · rw [k1']; exact Nat.le_refl _
    · exact Nat.le_of_lt (sorted 0 (k - 1) (by omega) (by omega))
  refine Ends.cons (Ends.ite _ (eval_eq (eval_add (eval_sub (eval_var ((assign_ne (by decide)).trans pv))
    (eval_var assign_eq) le0) (eval_lit 1)) (eval_var ((assign_ne (by decide)).trans v9)) (by omega) (by omega))
    (fun v => ?_) (fun v => ?_)) fun _ _ h => Ends.nil h
  · -- Adjacent parents: their pairs hashed in place.
    have span : q (k - 1) - q 0 + 1 = k := by
      by_cases hb : q (k - 1) - q 0 + 1 = k
      · exact hb
      · rw [if_neg hb] at v; exact absurd rfl v
    have cons := sorted_consecutive sorted k1 span
    have run := StoreCtx.runPre (lo := tree + 32 * S) (len := 32 * S) (lo' := tree + 32 * S) (len' := 32 * S)
      (ls := 64) (rs := 64) (left := tree + 64 * q 0) (right := tree + 64 * q 0 + 32) (n := k)
      (out := tree + 32 * q 0) ctxm (access_sub pre.treeAccess (by omega) (by omega))
      (access_sub pre.treeAccess (by omega) (by omega)) (access_sub pre.treeAccess (by omega) (by omega))
      (fun p hp => ⟨Or.inl ⟨by omega, by omega⟩, Or.inl ⟨by omega, by omega⟩⟩) ⟨by omega, by omega⟩
      (by simp only [Apart]; omega) (by simp only [Apart]; omega) (by simp only [Apart]; omega)
      (by simp only [Apart]; omega) (by simp only [Apart]; omega) (by simp only [Apart]; omega)
      (by simp only [Apart]; omega) (by simp only [Apart]; omega)
    have e14 : Asm.assign e 14 (UInt64.ofNat (q 0)) 14 = UInt64.ofNat (q 0) := assign_eq
    have e0' := (assign_ne (x := 14) (y := 0) (v := UInt64.ofNat (q 0)) (by decide)).trans v0
    obtain ⟨mm1, r1, h1⟩ := hash_call (name := "ssz_hash_pairs") okP rfl rfl rfl run kernels room
      (eval_five (eval_add (eval_var e0') (eval_mul (eval_lit 32) (eval_var e14)))
        (eval_add (eval_var e0') (eval_mul (eval_lit 64) (eval_var e14)))
        (eval_add (eval_add (eval_var e0') (eval_mul (eval_lit 64) (eval_var e14))) (eval_lit 32))
        (eval_var ((assign_ne (by decide)).trans v9)) (eval_var ((assign_ne (by decide)).trans v5)))
    refine Ends.step r1 (Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_or (eval_var ((assign_ne (by decide)).trans
      ((assign_ne (by decide)).trans v15))) (eval_var assign_eq))) (Ends.nil ⟨?_, fun i hi => ?_, fun a ha hp hn => ?_⟩))
    · have := ((HashVals.assign (x := 16) (v := 0) (HashVals.assign (x := 14) (v := UInt64.ofNat (q 0))
        ⟨v0, v5, v6, v7, v8, v9, v15⟩ (by omega)) (by omega)))
      obtain ⟨a, b, c', d, f, g, _⟩ := this
      exact ⟨(assign_ne (by decide)).trans a, (assign_ne (by decide)).trans b, (assign_ne (by decide)).trans c',
        (assign_ne (by decide)).trans d, (assign_ne (by decide)).trans f, (assign_ne (by decide)).trans g, by
          rw [assign_eq]; rfl⟩
    · rw [nodeAt_congr (m₂ := hashed mm (tree + 32 * q 0) (tree + 64 * q 0) (tree + 64 * q 0 + 32) k 64 64)
        fun j hj => h1 _ (by have := cons i hi; omega), show tree + 32 * q i = tree + 32 * q 0 + 32 * i by
          rw [cons i hi]; omega, nodeAt_hashed _ _ _ _ _ _ _ _ hi, cons i hi]
      rw [show tree + 64 * q 0 + 64 * i = tree + 64 * (q 0 + i) by omega,
        show tree + 64 * q 0 + 32 + 64 * i = tree + 64 * (q 0 + i) + 32 by omega]
    · rw [h1 a hp, hashed_outside]
      intro hin
      have := hn ((a - (tree + 32 * q 0)) / 32) (by omega)
      rw [cons _ (by omega)] at this
      omega
  · -- Scattered parents: their children gathered, hashed into digests, and copied back.
    have hv1 : HashVals (Asm.assign e 14 (UInt64.ofNat (q 0))) tree ctx scratch c k :=
      HashVals.assign ⟨v0, v5, v6, v7, v8, v9, v15⟩ (by omega)
    -- The list's words, read from any memory that keeps the list.
    have word : ∀ mm' : Memory, (∀ a, scratch ≤ a → a < scratch + 8 * c → mm' a = mm a) → ∀ i < k,
        slotWord mm' scratch i = q i := fun mm' same i hi => by
      rw [← hq]; exact slotWord_congr fun r hr => same _ (by omega) (by omega)
    have qb : ∀ i < k, q i < S := fun i hi => (level i hi).2
    simp only [TreeUpdate.scattered]
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 0)) ?_
    have hv2 := hv1.assign (x := 10) (v := UInt64.ofNat 0) (by omega)
    -- The left children.
    refine Ends.cons (copy_loop (I := 10) (D := 18) (S := 17) (i0 := 0) (n := k)
      (fun i => scratch + 8 * c + 64 * i) (fun i => tree + 64 * q i) (by decide) (by decide) (by decide)
      (fun e' mm' ag => by obtain ⟨_, _, _, _, _, a9, _⟩ := hv2.agree ag; exact eval_var a9)
      (fun e' mm' i ag iv _ _ _ => by
        obtain ⟨_, _, _, a7, _, _, _⟩ := hv2.agree ag
        exact eval_add (eval_var a7) (eval_mul (eval_lit 64) (eval_var iv)))
      (fun e' mm' i ag iv _ hi kept => by
        obtain ⟨a0, _, a6, _, _, _, _⟩ := hv2.agree ag
        have := eval_add (eval_var a0) (eval_mul (eval_lit 64) (eval_slotWord (w := w) (mem := mm') (eval_var a6)
          (eval_var iv) (access_sub pre.scratchAccess (by omega) (by omega))))
        rwa [word mm' (fun a h1 h2 => kept a fun j _ hj => by dsimp only; omega) i hi] at this)
      assign_eq (Nat.zero_le _) (by omega)
      (fun i _ hi => access_sub pre.scratchAccess (by omega) (by omega))
      (fun i _ hi => access_sub pre.treeAccess (by have := qb i hi; omega) (by have := qb i hi; omega))
      (fun i j _ hi _ hj => by have := qb j hj; simp only [Apart]; omega)
      (fun i j _ _ _ => by simp only [Apart]; omega)) ?_
    rintro e3 mm1 ⟨ag1, _, fill1, kept1⟩
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 0)) ?_
    have hv3 := (hv2.agree ag1).assign (x := 10) (v := UInt64.ofNat 0) (by omega)
    -- The right children.
    refine Ends.cons (copy_loop (I := 10) (D := 18) (S := 17) (i0 := 0) (n := k)
      (fun i => scratch + 8 * c + 64 * i + 32) (fun i => tree + 64 * q i + 32) (by decide) (by decide) (by decide)
      (fun e' mm' ag => by obtain ⟨_, _, _, _, _, a9, _⟩ := hv3.agree ag; exact eval_var a9)
      (fun e' mm' i ag iv _ _ _ => by
        obtain ⟨_, _, _, a7, _, _, _⟩ := hv3.agree ag
        exact eval_add (eval_add (eval_var a7) (eval_mul (eval_lit 64) (eval_var iv))) (eval_lit 32))
      (fun e' mm' i ag iv _ hi kept => by
        obtain ⟨a0, _, a6, _, _, _, _⟩ := hv3.agree ag
        have := eval_add (eval_add (eval_var a0) (eval_mul (eval_lit 64) (eval_slotWord (w := w) (mem := mm')
          (eval_var a6) (eval_var iv) (access_sub pre.scratchAccess (by omega) (by omega))))) (eval_lit 32)
        rwa [word mm' (fun a h1 h2 => by
          rw [kept a fun j _ hj => by dsimp only; omega, kept1 a fun j _ hj => by dsimp only; omega]) i hi] at this)
      assign_eq (Nat.zero_le _) (by omega)
      (fun i _ hi => access_sub pre.scratchAccess (by omega) (by omega))
      (fun i _ hi => access_sub pre.treeAccess (by have := qb i hi; omega) (by have := qb i hi; omega))
      (fun i j _ hi _ hj => by have := qb j hj; simp only [Apart]; omega)
      (fun i j _ _ _ => by simp only [Apart]; omega)) ?_
    rintro e4 mm2 ⟨ag2, _, fill2, kept2⟩
    have hv4 := hv3.agree ag2
    obtain ⟨b0, b5, b6, b7, b8, b9, b15⟩ := hv4
    -- Memory differs from the start only in the pairs.
    have same2 : ∀ a, ¬ (scratch + 8 * c ≤ a ∧ a < scratch + 8 * c + 64 * k) → mm2 a = mm a := fun a ha => by
      rw [kept2 a fun j _ hj => show ¬ (scratch + 8 * c + 64 * j + 32 ≤ a ∧ a < scratch + 8 * c + 64 * j + 32 + 32)
        by omega, kept1 a fun j _ hj => show ¬ (scratch + 8 * c + 64 * j ≤ a ∧ a < scratch + 8 * c + 64 * j + 32)
        by omega]
    have ctx2 := ctxm.congr (mm := mm2) fun a ha => same2 a (by omega)
    -- The pairs, hashed in one call into the digests.
    have run := StoreCtx.runPre (lo := scratch + 8 * c) (len := 64 * k) (lo' := scratch + 8 * c) (len' := 64 * k)
      (ls := 64) (rs := 64) (left := scratch + 8 * c) (right := scratch + 8 * c + 32) (n := k)
      (out := scratch + 8 * c + 64 * c) ctx2 (access_sub pre.scratchAccess (by omega) (by omega))
      (access_sub pre.scratchAccess (by omega) (by omega)) (access_sub pre.scratchAccess (by omega) (by omega))
      (fun p hp => ⟨Or.inl ⟨by omega, by omega⟩, Or.inl ⟨by omega, by omega⟩⟩) ⟨by omega, by omega⟩
      (by simp only [Apart]; omega) (by simp only [Apart]; omega) (by simp only [Apart]; omega)
      (by simp only [Apart]; omega) (by simp only [Apart]; omega) (by simp only [Apart]; omega)
      (by simp only [Apart]; omega) (by simp only [Apart]; omega)
    obtain ⟨mm3, r3, h3⟩ := hash_call (name := "ssz_hash_pairs") okP rfl rfl rfl run kernels room
      (eval_five (eval_var b8) (eval_var b7) (eval_add (eval_var b7) (eval_lit 32)) (eval_var b9) (eval_var b5))
    refine Ends.step r3 (Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_or (eval_var ((assign_ne (by decide)).trans b15))
      (eval_var assign_eq))) (Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 0)) ?_))
    have hv5 : HashVals (Asm.assign (Asm.assign (Asm.assign e4 16 0) 15 (0 ||| 0)) 10 (UInt64.ofNat 0)) tree ctx
        scratch c k := by
      refine HashVals.assign ⟨?_, ?_, ?_, ?_, ?_, ?_, assign_eq⟩ (by omega) <;>
        rw [assign_ne (by decide), assign_ne (by decide)] <;> assumption
    -- Memory after hashing: the digests, and the pairs as gathered.
    have same3 : ∀ a, ¬ (scratch + 8 * c ≤ a ∧ a < scratch + 104 * c) → ¬ (pad ≤ a ∧ a < pad + 1536) →
        mm3 a = mm a := fun a ha hp => by
      rw [h3 a hp, hashed_outside (by omega), same2 a (by omega)]
    have digest : ∀ i < k, nodeAt mm3 (scratch + 8 * c + 64 * c + 32 * i) =
        combine (nodeAt mm (tree + 64 * q i)) (nodeAt mm (tree + 64 * q i + 32)) := fun i hi => by
      rw [nodeAt_congr (m₂ := hashed mm2 (scratch + 8 * c + 64 * c) (scratch + 8 * c) (scratch + 8 * c + 32) k 64 64)
        fun j hj => h3 _ (by omega), nodeAt_hashed _ _ _ _ _ _ _ _ hi,
        show scratch + 8 * c + 32 + 64 * i = scratch + 8 * c + 64 * i + 32 by omega, fill2 i (Nat.zero_le _) hi,
        nodeAt_congr (m₂ := mm1) (a := scratch + 8 * c + 64 * i) fun j hj => kept2 (scratch + 8 * c + 64 * i + j)
          fun r _ hr => by dsimp only; omega,
        fill1 i (Nat.zero_le _) hi]
      rw [nodeAt_congr (m₂ := mm) (a := tree + 64 * q i + 32) fun j hj => kept1 (tree + 64 * q i + 32 + j) fun r _ hr => by
        have := qb i hi; dsimp only; omega]
    -- The digests, copied back to the parents.
    refine Ends.cons (copy_loop (I := 10) (D := 17) (S := 18) (i0 := 0) (n := k)
      (fun i => tree + 32 * q i) (fun i => scratch + 8 * c + 64 * c + 32 * i) (by decide) (by decide) (by decide)
      (fun e' mm' ag => by obtain ⟨_, _, _, _, _, a9, _⟩ := hv5.agree' ag; exact eval_var a9)
      (fun e' mm' i ag iv _ hi kept => by
        obtain ⟨a0, _, a6, _, _, _, _⟩ := hv5.agree' ag
        have := eval_add (eval_var a0) (eval_mul (eval_lit 32) (eval_slotWord (w := w) (mem := mm') (eval_var a6)
          (eval_var iv) (access_sub pre.scratchAccess (by omega) (by omega))))
        rwa [word mm' (fun a h1 h2 => by
          rw [kept a fun j _ hj => by have := qb j hj; dsimp only; omega, same3 a (by omega) (by omega)]) i hi]
          at this)
      (fun e' mm' i ag iv _ _ _ => by
        obtain ⟨_, _, _, _, a8, _, _⟩ := hv5.agree' ag
        exact eval_add (eval_var a8) (eval_mul (eval_lit 32) (eval_var iv)))
      assign_eq (Nat.zero_le _) (by omega)
      (fun i _ hi => access_sub pre.treeAccess (by have := qb i hi; omega) (by have := qb i hi; omega))
      (fun i _ hi => access_sub pre.scratchAccess (by omega) (by omega))
      (fun i j _ hi _ hj => by have := qb i hi; simp only [Apart]; omega)
      (fun i j _ ij hj => by have := sorted i j ij hj; simp only [Apart]; omega)) fun e6 mm4 ⟨ag6, _, fill3, kept3⟩ =>
      Ends.nil ⟨hv5.agree' ag6, fun i hi => by rw [fill3 i (Nat.zero_le _) hi, digest i hi], fun a ha hp hn => by
        rw [kept3 a fun j _ hj => hn j hj, same3 a ha hp]⟩

end Ssz.Native.Driver
