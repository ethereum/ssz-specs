import SszNative.Proofs.Driver.Prove.Small
import EthLib.Consensus.Ssz.Codec.Proof

/-! The compiled walk down a progressive spine stops where the Lean walk stops, or refuses as it refuses. -/

namespace EthLib.Consensus.Ssz.Native.Driver.ProveProof

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Driver.BranchProof

/-- A word and a power of two keep that power exactly when the word's bit there is set. -/
theorem and_two_pow (n i : Nat) : n &&& 2 ^ i = if n.testBit i then 2 ^ i else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases e : i = j
  · subst e
    by_cases h : n.testBit i <;> simp [h]
  · by_cases h : n.testBit i <;> simp [h, e]

/-- A word and a power of two below the word's width are nonzero exactly when the word's bit there is set. -/
theorem and_pow_ne (x : UInt64) {i : Nat} (hi : i < 64) :
    x &&& UInt64.ofNat (2 ^ i) ≠ 0 ↔ x.toNat.testBit i = true := by
  have pow : (UInt64.ofNat (2 ^ i)).toNat = 2 ^ i := toNat_ofNat_of_lt _ (Nat.pow_lt_pow_right (by decide) hi)
  rw [Ne, ← UInt64.toNat_inj, UInt64.toNat_and, pow, and_two_pow]
  by_cases h : x.toNat.testBit i <;> simp [h]

/-- An at-most comparison evaluates to one exactly when the first value is at most the second. -/
theorem eval_le {w : World} {env : Env} {mem : Memory} {a b : Ir.Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (Ir.Expr.le a b) = some (if x.toNat ≤ y.toNat then 1 else 0) := by
  rw [Ir.Expr.le, eval_cmp .be ha hb]
  by_cases h : x.toNat ≤ y.toNat
  · -- At most is equal or below.
    rcases Nat.lt_or_eq_of_le h with l | e
    · simp [Cond.holds, UInt64.lt_iff_toNat_lt.mpr l, h]
    · simp [Cond.holds, UInt64.toNat_inj.mp e]
  · have n1 : x ≠ y := fun e => h (by rw [e]; exact Nat.le_refl _)
    have n2 : ¬ x < y := fun l => h (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp l))
    simp [Cond.holds, n1, n2, h]

/-- A flag that is not zero is the flag of a condition that holds. -/
theorem flag_ne {p : Prop} [Decidable p] (h : (if p then 1 else 0 : UInt64) ≠ 0) : p := by
  by_cases hp : p
  · exact hp
  · simp [hp] at h

/-- A flag that is zero is the flag of a condition that fails. -/
theorem flag_eq {p : Prop} [Decidable p] (h : (if p then 1 else 0 : UInt64) = 0) : ¬ p := by
  intro hp
  simp [hp] at h

/-- A word written before others at higher addresses still reads back. -/
theorem readLE_under (mem : Memory) (a b n : Nat) (f : Nat → UInt8) (apart : a + 8 ≤ b) :
    readLE (store mem b n f) a 8 = readLE mem a 8 :=
  readLE_congr _ _ a 8 fun i hi => store_outside mem b n f (a + i) (by omega)

/-- Four words written one after another read back in order. -/
theorem four_words (mem : Memory) (a : Nat) (v0 v1 v2 v3 : UInt64) :
    (List.range 4).map (fun k => (readLE (store (store (store (store mem a 8 (qwordByte v0)) (a + 8) 8
      (qwordByte v1)) (a + 16) 8 (qwordByte v2)) (a + 24) 8 (qwordByte v3)) (a + 8 * k) 8).toNat) =
      [v0.toNat, v1.toNat, v2.toNat, v3.toNat] := by
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, Nat.mul_zero, Nat.add_zero,
    show a + 8 * 1 = a + 8 by omega, show a + 8 * 2 = a + 16 by omega, show a + 8 * 3 = a + 24 by omega]
  -- Each word is read under the writes after it.
  rw [readLE_under _ a (a + 24) 8 _ (by omega), readLE_under _ a (a + 16) 8 _ (by omega),
    readLE_under _ a (a + 8) 8 _ (by omega), readLE_store8,
    readLE_under _ (a + 8) (a + 24) 8 _ (by omega), readLE_under _ (a + 8) (a + 16) 8 _ (by omega),
    readLE_store8, readLE_under _ (a + 16) (a + 24) 8 _ (by omega), readLE_store8, readLE_store8]

/-- The words a stop is written as: the turns left, the first leaf, the capacity, and whether the walk turned. -/
def stopWords (s : SpineStop) : List Nat :=
  [s.depth, s.leavesFrom, s.capacity, if s.turnedLeft then 1 else 0]

/-- What a walk's answer and written words say: the Lean walk's stop, or its refusal of a level past the end. -/
def WalkAnswer : Except Err SpineStop → UInt64 → List Nat → Prop
  | .ok s, r, words => r = 0 ∧ words = stopWords s
  | .error e, r, _ => r = 15 ∧ e = .pathPastSpine

/-- The walk's state: either still walking toward the Lean walk's answer, or stopped with it in its variables. -/
private def WalkInv (mem : Memory) (count index out : UInt64) (goal : Except Err SpineStop) (env : Env)
    (mem' : Memory) : Prop :=
  mem' = mem ∧ env 0 = count ∧ env 1 = index ∧ env 5 = out ∧
    ((env 8 = 1 ∧ env 6 = 0 ∧ env 7 = 0 ∧ (env 2).toNat < 64 ∧ (env 3).toNat ≤ 4 * count.toNat + 1 ∧
      (env 4).toNat ≤ 3 * (env 3).toNat + 1 ∧
      spineWalk count.toNat index.toNat (env 2).toNat (env 3).toNat (env 4).toNat = goal) ∨
    (env 8 = 0 ∧ WalkAnswer goal (env 6) [(env 2).toNat, (env 3).toNat, (env 4).toNat, (env 7).toNat]))

/--
A call of the spine walk answers zero and writes the Lean walk's stop, or answers 15 where the Lean walk refuses
a level past the end.

The leaf count stays far below the word's width, and the capacity is at most one more than three times the first
leaf, as it is from the spine's top.
Memory changes only in the four words written.
-/
theorem spine_walk_calls {m : Module} {w : World}
    (hf : m.fns.lookup "ssz_prove_spine_walk" = some ProveSpineWalk.fn)
    (hp : m.fns.lookup "ssz_prove_pow2" = some ProvePow2.fn) {sp : Nat}
    (room : w.stackLo + 8 + 8 * ProveSpineWalk.fn.frame + 8 + 8 * ProvePow2.fn.frame ≤ sp)
    (count index depth start cap out : UInt64) (mem : Memory) (acc : w.access out.toNat 32 = true)
    (small : count.toNat < 2 ^ 59) (shallow : depth.toNat < 64) (first : start.toNat ≤ 4 * count.toNat + 1)
    (capped : cap.toNat ≤ 3 * start.toNat + 1) :
    ∃ r mem', Calls m w "ssz_prove_spine_walk" sp [count, index, depth, start, cap, out] mem r mem' ∧
      WalkAnswer (spineWalk count.toNat index.toNat depth.toNat start.toNat cap.toNat) r
        ((List.range 4).map fun k => (readLE mem' (out.toNat + 8 * k) 8).toNat) ∧
      ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 32) → mem' a = mem a := by
  generalize hG : spineWalk count.toNat index.toNat depth.toNat start.toNat cap.toNat = goal
  have bo := access_bound acc
  suffices body : Wp m w (sp - 8 - 8 * ProveSpineWalk.fn.frame) ProveSpineWalk.fn.body
      (entryEnv [count, index, depth, start, cap, out]) mem fun env mem' => ∃ r,
        eval w env mem' ProveSpineWalk.fn.result = some r ∧
        WalkAnswer goal r ((List.range 4).map fun k => (readLE mem' (out.toNat + 8 * k) 8).toNat) ∧
        ∀ a, ¬ (out.toNat ≤ a ∧ a < out.toNat + 32) → mem' a = mem a by
    exact Calls.of_wp hf (by omega) rfl body
  simp only [ProveSpineWalk.fn]
  refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl (Wp.cons ?_))))))
  refine Wp.loop (WalkInv mem count index out goal) (fun env _ => 2 * (env 2).toNat + (env 8).toNat)
    ⟨rfl, by simp [assign, entryEnv], by simp [assign, entryEnv], by simp [assign, entryEnv],
      .inl ⟨by simp [assign], by simp [assign], by simp [assign], by simp [assign, entryEnv]; exact shallow,
        by simp [assign, entryEnv]; exact first, by simp [assign, entryEnv]; exact capped,
        by simp [assign, entryEnv]; exact hG⟩⟩ ?_
  intro env mem' ⟨same, e0, e1, e5, st⟩
  subst same
  refine ⟨env 8, rfl, fun nz => ?_, fun z => ?_⟩
  · -- Still walking: one more level, or the stop.
    rcases st with ⟨g, r0, t0, dlt, sle, cle, walk⟩ | ⟨g, _⟩
    rotate_left
    · exact absurd g nz
    refine Wp.cons (Wp.ite (eval_eq rfl rfl) (fun d0 => ?_) (fun d0 => ?_))
    · -- No turns left: the walk stops here, on the spine.
      have dz : env 2 = 0 := by simpa using d0
      rw [dz] at walk
      simp only [UInt64.toNat_zero, spineWalk] at walk
      subst walk
      refine Wp.cons (Wp.set rfl ?_)
      repeat refine Wp.nil ?_
      refine ⟨⟨rfl, ?_, ?_, ?_, .inr ⟨?_, ?_⟩⟩, ?_⟩ <;> simp only [assign, ↓reduceIte, Nat.reduceEqDiff]
      · exact e0
      · exact e1
      · exact e5
      · exact ⟨r0, by simp [stopWords, t0, dz]⟩
      · rw [g]; simp
    · have dpos : 0 < (env 2).toNat := by
        have : env 2 ≠ 0 := by simpa using d0
        exact Nat.pos_of_ne_zero (fun h => this (UInt64.toNat_inj.mp (by simpa using h)))
      obtain ⟨d, hd⟩ : ∃ d, (env 2).toNat = d + 1 := ⟨(env 2).toNat - 1, by omega⟩
      rw [hd] at walk
      refine Wp.cons (Wp.ite (eval_le rfl rfl) (fun past => ?_) (fun past => ?_))
      · -- The level's first leaf is past the data: the walk refuses.
        have hpast : count.toNat ≤ (env 3).toNat := by
          rw [← e0]; exact flag_ne past
        simp only [spineWalk, show (env 3).toNat ≥ count.toNat from hpast, ite_true] at walk
        subst walk
        refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl ?_)))
        repeat refine Wp.nil ?_
        refine ⟨⟨rfl, ?_, ?_, ?_, .inr ⟨?_, ?_⟩⟩, ?_⟩ <;> simp only [assign, ↓reduceIte, Nat.reduceEqDiff]
        · exact e0
        · exact e1
        · exact e5
        · exact ⟨rfl, rfl⟩
        · rw [g]; simp
      · have hin : (env 3).toNat < count.toNat := by
          have := flag_eq past
          rw [e0] at this; omega
        simp only [spineWalk, show ¬ ((env 3).toNat ≥ count.toNat) by omega, ite_false] at walk
        have dec : (env 2 - 1).toNat = d := by
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega
        have pc := pow2_calls (w := w) hp (sp := sp - 8 - 8 * ProveSpineWalk.fn.frame) (by omega) (env 2 - 1) mem'
        rw [dec] at pc
        refine Wp.cons (Wp.set (eval_sub rfl rfl) (Wp.cons (Wp.call (values := [env 2 - 1])
          rfl ⟨_, mem', pc, ?_⟩)))
        have bit := and_pow_ne index (i := d) (by omega)
        refine Wp.cons (Wp.ite (eval_eq (eval_and rfl rfl) rfl) (fun turn => ?_) (fun turn => ?_))
        · -- A clear bit: the walk turns into this level's subtree.
          have clear : index.toNat.testBit d = false := by
            have z := flag_ne turn
            simp only [assign, ↓reduceIte, Nat.reduceEqDiff, e1] at z
            have : ¬ (index &&& UInt64.ofNat (2 ^ d) ≠ 0) := fun h => h z
            rw [bit] at this
            simpa using this
          simp only [clear, gindexBit, Bool.not_false, ite_true] at walk
          subst walk
          refine Wp.cons (Wp.set rfl (Wp.cons (Wp.set rfl ?_)))
          repeat refine Wp.nil ?_
          refine ⟨⟨rfl, ?_, ?_, ?_, .inr ⟨?_, ?_⟩⟩, ?_⟩ <;> simp only [assign, ↓reduceIte, Nat.reduceEqDiff]
          · exact e0
          · exact e1
          · exact e5
          · exact ⟨r0, by simp [stopWords, dec]⟩
          · rw [g]; simp; omega
        · -- A set bit: the walk moves onto the next level, four times as wide.
          have set : index.toNat.testBit d = true := by
            have z := flag_eq turn
            simp only [assign, ↓reduceIte, Nat.reduceEqDiff, e1] at z
            exact bit.mp z
          simp only [set, gindexBit, Bool.not_true] at walk
          have sum : (env 3 + env 4).toNat = (env 3).toNat + (env 4).toNat :=
            toNat_add_of_lt _ _ (by omega)
          have four : (env 4 * 4).toNat = (env 4).toNat * 4 :=
            toNat_mul_of_lt _ _ (by simp; omega)
          refine Wp.cons (Wp.set (eval_add rfl rfl) (Wp.cons (Wp.set (eval_mul rfl rfl) ?_)))
          repeat refine Wp.nil ?_
          refine ⟨⟨rfl, ?_, ?_, ?_, .inl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_⟩ <;>
            simp only [assign, ↓reduceIte, Nat.reduceEqDiff]
          · exact e0
          · exact e1
          · exact e5
          · exact g
          · exact r0
          · exact t0
          · omega
          · rw [sum]; omega
          · rw [four, sum]; omega
          · rw [four, sum, dec]; exact walk
          · rw [dec, g]; simp; omega
  · -- The walk has stopped: its stop is written, and the answer is the code it set.
    rcases st with ⟨g, _⟩ | ⟨_, fin⟩
    · exact absurd (g.symm.trans z) (by decide)
    have off : ∀ k, k ≤ 24 → (env 5 + UInt64.ofNat k).toNat = out.toNat + k := fun k hk => by
      rw [toNat_add_of_lt _ _ (by rw [e5]; simp; omega), e5]; simp; omega
    have at0 : w.access (env 5).toNat 8 = true := by rw [e5]; exact access_prefix acc (by omega)
    have atk : ∀ k, k ≤ 24 → w.access (env 5 + UInt64.ofNat k).toNat 8 = true := fun k hk => by
      rw [off k hk]; exact access_sub acc (by omega)
    refine Wp.cons (Wp.store (x := env 5) (y := env 2) rfl rfl at0 ?_)
    refine Wp.cons (Wp.store (x := env 5 + UInt64.ofNat 8) (y := env 3) (eval_add rfl rfl) rfl (atk 8 (by omega)) ?_)
    refine Wp.cons (Wp.store (x := env 5 + UInt64.ofNat 16) (y := env 4) (eval_add rfl rfl) rfl
      (atk 16 (by omega)) ?_)
    refine Wp.store (x := env 5 + UInt64.ofNat 24) (y := env 7) (eval_add rfl rfl) rfl (atk 24 (by omega)) ?_
    refine ⟨env 6, rfl, ?_⟩
    rw [off 8 (by omega), off 16 (by omega), off 24 (by omega), e5]
    simp only [Width.bytes]
    rw [four_words]
    refine ⟨fin, fun a ha => ?_⟩
    rw [store_outside _ _ _ _ _ (by omega), store_outside _ _ _ _ _ (by omega), store_outside _ _ _ _ _ (by omega),
      store_outside _ _ _ _ _ (by omega)]

end EthLib.Consensus.Ssz.Native.Driver.ProveProof
