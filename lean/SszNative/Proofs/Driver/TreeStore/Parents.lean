import SszNative.Proofs.Driver.TreeStore.Copy

/-!
The update driver's list of nodes, and the pass that moves it one height up.

The list holds the heap indices of one level's nodes above rewritten leaves, sorted and each once.
A leaf x has, at height h, the ancestor 2^(K-h) + x / 2^h.
Halving every entry gives the parents, and since the list is sorted, equal parents sit next to each other:
keeping an entry only when it differs from the last one kept leaves each parent once, still sorted.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir

/-! ## Words in memory -/

/-- Word i of an array of eight-byte words, as a number. -/
def slotWord (mem : Memory) (a i : Nat) : Nat :=
  (readLE mem (a + 8 * i) 8).toNat

/-- A word is below the word size. -/
theorem slotWord_lt (mem : Memory) (a i : Nat) : slotWord mem a i < 2 ^ 64 :=
  (readLE mem (a + 8 * i) 8).toNat_lt

/-- A word reads only its own eight bytes. -/
theorem slotWord_congr {mem mm : Memory} {a i : Nat} (same : ∀ q < 8, mm (a + 8 * i + q) = mem (a + 8 * i + q)) :
    slotWord mm a i = slotWord mem a i := by
  unfold slotWord
  rw [readLE_congr _ _ _ _ same]

/-- Storing a word at one index changes that word only. -/
theorem slotWord_store (mem : Memory) (a j i v : Nat) (hv : v < 2 ^ 64) :
    slotWord (store mem (a + 8 * j) 8 (qwordByte (UInt64.ofNat v))) a i = if i = j then v else slotWord mem a i := by
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl]
    unfold slotWord
    rw [readLE_store8, ofNat_toNat hv]
  · rw [ite_eq_right h]
    exact slotWord_congr fun q hq => by
      simp only [store]
      rw [ite_eq_right (by omega)]

/-- Loading the word at an index computed from an address and an index variable. -/
theorem eval_slotWord {w : World} {env : Env} {mem : Memory} {L T : Expr} {a i : Nat}
    (hl : eval w env mem L = some (UInt64.ofNat a)) (ht : eval w env mem T = some (UInt64.ofNat i))
    (acc : w.access (a + 8 * i) 8 = true) :
    eval w env mem (Expr.ld (L + 8 * T)) = some (UInt64.ofNat (slotWord mem a i)) := by
  rw [eval_ld (eval_add hl (eval_mul (eval_lit 8) ht)) acc, slotWord, UInt64.ofNat_toNat]

/-- Loading the first word of an array. -/
theorem eval_slotWord0 {w : World} {env : Env} {mem : Memory} {L : Expr} {a : Nat}
    (hl : eval w env mem L = some (UInt64.ofNat a)) (acc : w.access a 8 = true) :
    eval w env mem (Expr.ld L) = some (UInt64.ofNat (slotWord mem a 0)) := by
  rw [eval_ld hl acc, slotWord, Nat.mul_zero, Nat.add_zero, UInt64.ofNat_toNat]

/-- Storing a word at an index computed from an address and an index variable. -/
theorem store_slotWord {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {L T V : Expr} {a i v : Nat}
    (hl : eval w env mem L = some (UInt64.ofNat a)) (ht : eval w env mem T = some (UInt64.ofNat i))
    (hv : eval w env mem V = some (UInt64.ofNat v)) (acc : w.access (a + 8 * i) 8 = true) :
    Runs m w sp env mem (Stmt.st (L + 8 * T) V) env (store mem (a + 8 * i) 8 (qwordByte (UInt64.ofNat v))) := by
  have b := access_bound acc
  have := Runs.store m w sp env mem .b8 _ _ _ _ (eval_add hl (eval_mul (eval_lit 8) ht)) hv
    (by rw [ofNat_toNat (by omega)]; exact acc)
  rwa [ofNat_toNat (by omega)] at this

/-- Storing the first word of an array, at the array's own address. -/
theorem store_slotWord0 {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {L V : Expr} {a v : Nat}
    (hl : eval w env mem L = some (UInt64.ofNat a)) (hv : eval w env mem V = some (UInt64.ofNat v))
    (acc : w.access a 8 = true) :
    Runs m w sp env mem (Stmt.st L V) env (store mem (a + 8 * 0) 8 (qwordByte (UInt64.ofNat v))) := by
  have b := access_bound acc
  have := Runs.store m w sp env mem .b8 _ _ _ _ hl hv (by rw [ofNat_toNat (by omega)]; exact acc)
  rw [ofNat_toNat (by omega)] at this
  rw [Nat.mul_zero, Nat.add_zero]
  exact this

/-! ## Ancestors -/

/-- The heap index of a leaf's ancestor at a height, in a tree of height K. -/
def anc (K h x : Nat) : Nat :=
  2 ^ (K - h) + x / 2 ^ h

/-- Halving an ancestor's index gives the ancestor one height up. -/
theorem anc_up (K h x : Nat) (below : h < K) : anc K h x / 2 = anc K (h + 1) x := by
  unfold anc
  rw [show K - h = (K - (h + 1)) + 1 by omega, Nat.pow_succ, Nat.pow_succ, ← Nat.div_div_eq_div_mul,
    show 2 ^ (K - (h + 1)) * 2 + x / 2 ^ h = x / 2 ^ h + 2 * 2 ^ (K - (h + 1)) by omega, Nat.add_mul_div_left _ _
    (by decide)]
  omega

/-- A leaf's ancestor lies in the level of its height. -/
theorem anc_bounds (K h x : Nat) (hh : h ≤ K) (hx : x < 2 ^ K) :
    2 ^ (K - h) ≤ anc K h x ∧ anc K h x < 2 * 2 ^ (K - h) := by
  unfold anc
  have : x / 2 ^ h < 2 ^ (K - h) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos h), ← Nat.pow_add, Nat.sub_add_cancel hh]
    exact hx
  generalize x / 2 ^ h = q at this ⊢
  omega

/-- At the top, every ancestor is the root. -/
theorem anc_top (K x : Nat) (hx : x < 2 ^ K) : anc K K x = 1 := by
  have := anc_bounds K K x (Nat.le_refl _) hx
  rw [Nat.sub_self, Nat.pow_zero] at this
  omega

/-! ## The list -/

/--
The list holds the ancestors at height h of the rewritten leaves: sorted, each once, and all of them.

The indices of the rewritten leaves are given as a function over the first c numbers.
-/
structure ListAt (mm : Memory) (list K c : Nat) (idx : Nat → Nat) (h k : Nat) : Prop where
  /-- At least one entry. -/
  pos : 1 ≤ k
  /-- At most one per leaf. -/
  le : k ≤ c
  /-- Sorted, each once. -/
  sorted : ∀ i j, i < j → j < k → slotWord mm list i < slotWord mm list j
  /-- Each entry is an ancestor. -/
  sound : ∀ i < k, ∃ x < c, slotWord mm list i = anc K h (idx x)
  /-- Each ancestor is an entry. -/
  complete : ∀ x < c, ∃ i < k, slotWord mm list i = anc K h (idx x)

/-- In a sorted list, entries grow at least by their distance. -/
theorem sorted_gap {f : Nat → Nat} {k : Nat} (sorted : ∀ i j, i < j → j < k → f i < f j) :
    ∀ i j, i ≤ j → j < k → f i + (j - i) ≤ f j := by
  intro i j hij hj
  induction j with
  | zero => obtain rfl : i = 0 := by omega
            simp
  | succ j ih =>
    by_cases e : i = j + 1
    · subst e; simp
    · have := ih (by omega) (by omega)
      have := sorted j (j + 1) (by omega) hj
      omega

/-- A sorted list whose last entry is its first plus its length less one runs through consecutive numbers. -/
theorem sorted_consecutive {f : Nat → Nat} {k : Nat} (sorted : ∀ i j, i < j → j < k → f i < f j) (pos : 1 ≤ k)
    (span : f (k - 1) - f 0 + 1 = k) : ∀ i < k, f i = f 0 + i := by
  intro i hi
  have a := sorted_gap sorted 0 i (Nat.zero_le _) hi
  have b := sorted_gap sorted i (k - 1) (by omega) (by omega)
  omega

/-- The parents pass's fixed variables: all but the index, the count kept, the last parent, and a parent. -/
def ParentsAgree (e0 e : Env) : Prop :=
  ∀ y, y ≠ 10 → y ≠ 11 → y ≠ 12 → y ≠ 13 → e y = e0 y

set_option maxHeartbeats 4000000 in
/--
The parents pass replaces a level's list by the list one height up.

It changes only the list's words, and leaves the new count in both the count and the kept-count variables, and the
last entry in the last-parent variable.
-/
theorem parents_ends {m : Module} {w : World} {sp : Nat} {mem : Memory} {list K c h k : Nat} {idx : Nat → Nat}
    {e : Env} (lv : e 6 = UInt64.ofNat list) (kv : e 9 = UInt64.ofNat k) (L : ListAt mem list K c idx h k)
    (below : h < K) (acc : w.access list (8 * c) = true) (narrow : K < 58) (inside : ∀ x < c, idx x < 2 ^ K) :
    Ends m w sp e mem (.block TreeUpdate.parents) fun e' mm' =>
      (∀ y, y ≠ 9 → y ≠ 10 → y ≠ 11 → y ≠ 12 → y ≠ 13 → e' y = e y) ∧ ∃ k', e' 9 = UInt64.ofNat k' ∧
        e' 12 = UInt64.ofNat (slotWord mm' list (k' - 1)) ∧ ListAt mm' list K c idx (h + 1) k' ∧
        ∀ a, ¬ (list ≤ a ∧ a < list + 8 * c) → mm' a = mem a := by
  have bl := access_bound acc
  have kc := L.le
  have k1 := L.pos
  have wK : 2 ^ K < 2 ^ 58 := Nat.pow_lt_pow_right (by decide) narrow
  -- Every entry is an ancestor, so small.
  have small : ∀ i < k, slotWord mem list i < 2 * 2 ^ K := fun i hi => by
    obtain ⟨x, hx, eq⟩ := L.sound i hi
    have b := anc_bounds K h (idx x) (by omega) (inside x hx)
    have : 2 ^ (K - h) ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  generalize hps : slotWord mem list = ps at small
  have sorted : ∀ i j, i < j → j < k → ps i < ps j := hps ▸ L.sorted
  have sound : ∀ i < k, ∃ x < c, ps i = anc K h (idx x) := hps ▸ L.sound
  have complete : ∀ x < c, ∃ i < k, ps i = anc K h (idx x) := hps ▸ L.complete
  have p0 := small 0 k1
  -- The first parent, kept.
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_shr1' (eval_slotWord0 (eval_var lv) (access_sub acc (by omega)
    (by omega))) (slotWord_lt _ _ _))) ?_
  rw [hps]
  refine Ends.step (store_slotWord0 (eval_var ((assign_ne (by decide)).trans lv)) (eval_var assign_eq)
    (access_sub acc (by omega) (by omega))) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 1)) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 1)) ?_
  generalize hm1 : store mem (list + 8 * 0) 8 (qwordByte (UInt64.ofNat (ps 0 / 2))) = mem1
  have w1 : ∀ i, slotWord mem1 list i = if i = 0 then ps 0 / 2 else ps i := fun i => by
    rw [← hm1, slotWord_store mem list 0 i (ps 0 / 2) (by omega), ← hps]
  have f1 : ∀ a, ¬ (list ≤ a ∧ a < list + 8 * c) → mem1 a = mem a := fun a ha => by
    rw [← hm1]; simp only [store]; rw [ite_eq_right (by omega)]
  refine Ends.cons (Ends.loop (fun e' mm' => (∀ y, y ≠ 10 → y ≠ 11 → y ≠ 12 → y ≠ 13 → e' y = e y) ∧
      ∃ t n, 1 ≤ n ∧ n ≤ t ∧ t ≤ k ∧ e' 10 = UInt64.ofNat t ∧ e' 11 = UInt64.ofNat n ∧
      e' 12 = UInt64.ofNat (slotWord mm' list (n - 1)) ∧ (∀ i, t ≤ i → i < k → slotWord mm' list i = ps i) ∧
      (∀ i j, i < j → j < n → slotWord mm' list i < slotWord mm' list j) ∧ slotWord mm' list (n - 1) = ps (t - 1) / 2 ∧
      (∀ i < n, ∃ i' < t, slotWord mm' list i = ps i' / 2) ∧ (∀ i' < t, ∃ i < n, slotWord mm' list i = ps i' / 2) ∧
      ∀ a, ¬ (list ≤ a ∧ a < list + 8 * c) → mm' a = mem a)
    (fun e' _ => k - (e' 10).toNat)
    ⟨fun y a b c' _ => by rw [assign_ne a, assign_ne b, assign_ne c'], 1, 1, Nat.le_refl _, Nat.le_refl _, k1,
      assign_eq, by rw [assign_ne (by decide), assign_eq],
      by rw [assign_ne (by decide), assign_ne (by decide), assign_eq, w1, ite_eq_left rfl],
      fun i hi _ => by rw [w1, ite_eq_right (by omega)], fun i j _ hj => absurd hj (by omega),
      by rw [w1, ite_eq_left rfl], fun i hi => ⟨0, by omega, by rw [show i = 0 by omega, w1, ite_eq_left rfl]⟩,
      fun i' hi => ⟨0, by omega, by rw [show i' = 0 by omega, w1, ite_eq_left rfl]⟩, f1⟩ ?_ ?_) ?_
  · rintro e' mm' ⟨ag, t, n, _, _, tk, tv, _⟩
    exact ⟨_, eval_lt (eval_var tv) (eval_var ((ag 9 (by decide) (by decide) (by decide) (by decide)).trans kv))
      (by omega) (by omega)⟩
  · rintro e' mm' v ⟨ag, t, n, n1, nt, tk, tv, nv, pv, unread, srt, last, snd, cpl, fr⟩ hv nz
    have kv' := (ag 9 (by decide) (by decide) (by decide) (by decide)).trans kv
    have lv' := (ag 6 (by decide) (by decide) (by decide) (by decide)).trans lv
    have hv := Option.some.inj (hv.symm.trans (eval_lt (eval_var tv) (eval_var kv') (by omega) (by omega)))
    have tk' : t < k := by
      by_cases hb : t < k
      · exact hb
      · rw [ite_eq_right hb] at hv; exact absurd hv nz
    have pt := small t tk'
    have mono : ps (t - 1) / 2 ≤ ps t / 2 := Nat.div_le_div_right (Nat.le_of_lt (sorted _ _ (by omega) tk'))
    -- The parent of the next entry.
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_shr1' (eval_slotWord (eval_var lv') (eval_var tv)
      (access_sub acc (by omega) (by omega))) (slotWord_lt _ _ _))) ?_
    rw [unread t (Nat.le_refl _) tk']
    have p13 : Asm.assign e' 13 (UInt64.ofNat (ps t / 2)) 13 = UInt64.ofNat (ps t / 2) := assign_eq
    have p12 : Asm.assign e' 13 (UInt64.ofNat (ps t / 2)) 12 = UInt64.ofNat (slotWord mm' list (n - 1)) :=
      (assign_ne (by decide)).trans pv
    refine Ends.cons (Q := fun e2 mm2 => (∀ y, y ≠ 10 → y ≠ 11 → y ≠ 12 → y ≠ 13 → e2 y = e y) ∧
        e2 10 = UInt64.ofNat t ∧ ∃ n', 1 ≤ n' ∧ n' ≤ t + 1 ∧ e2 11 = UInt64.ofNat n' ∧
        e2 12 = UInt64.ofNat (slotWord mm2 list (n' - 1)) ∧ (∀ i, t + 1 ≤ i → i < k → slotWord mm2 list i = ps i) ∧
        (∀ i j, i < j → j < n' → slotWord mm2 list i < slotWord mm2 list j) ∧ slotWord mm2 list (n' - 1) = ps t / 2 ∧
        (∀ i < n', ∃ i' < t + 1, slotWord mm2 list i = ps i' / 2) ∧
        (∀ i' < t + 1, ∃ i < n', slotWord mm2 list i = ps i' / 2) ∧
        ∀ a, ¬ (list ≤ a ∧ a < list + 8 * c) → mm2 a = mem a)
      (Ends.when _ (eval_ne (eval_var p13) (eval_var p12)) (fun v => ?_) (fun v => ?_)) ?_
    · -- A new parent: kept after the last one.
      have ne : ps t / 2 ≠ slotWord mm' list (n - 1) := fun h => ite_ne_zero v (by rw [h])
      rw [last] at ne
      have gt : ps (t - 1) / 2 < ps t / 2 := by omega
      have stn := store_slotWord (m := m) (sp := sp) (mem := mm') (eval_var ((assign_ne (by decide)).trans lv'))
        (eval_var ((assign_ne (by decide)).trans nv)) (eval_var p13) (access_sub acc (by omega) (by omega))
      refine Ends.step stn (Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_add (eval_var ((assign_ne (by decide)).trans
        nv)) (eval_lit 1))) (Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_var ((assign_ne (by decide)).trans p13)))
          (Ends.nil ?_)))
      have w2 : ∀ i, slotWord (store mm' (list + 8 * n) 8 (qwordByte (UInt64.ofNat (ps t / 2)))) list i =
          if i = n then ps t / 2 else slotWord mm' list i := fun i => slotWord_store mm' list n i (ps t / 2) (by omega)
      refine ⟨fun y a b c' d => by
          rw [assign_ne c', assign_ne b, assign_ne d]; exact ag y a b c' d,
        by rw [assign_ne (by decide), assign_ne (by decide), assign_ne (by decide)]; exact tv,
        n + 1, by omega, by omega, by rw [assign_ne (by decide), assign_eq],
        by rw [assign_eq, Nat.add_sub_cancel, w2, ite_eq_left rfl], fun i hi hk => by
          rw [w2, ite_eq_right (by omega)]; exact unread i (by omega) hk, fun i j hij hj => ?_,
        by rw [Nat.add_sub_cancel, w2, ite_eq_left rfl], fun i hi => ?_, fun i' hi => ?_, fun a ha => ?_⟩
      · rw [w2, w2, ite_eq_right (by omega)]
        by_cases jn : j = n
        · rw [ite_eq_left jn]
          by_cases i1 : i = n - 1
          · rw [i1, last]; exact gt
          · have := srt i (n - 1) (by omega) (by omega)
            rw [last] at this; omega
        · rw [ite_eq_right jn]; exact srt i j hij (by omega)
      · rw [w2]
        by_cases jn : i = n
        · rw [ite_eq_left jn]; exact ⟨t, by omega, rfl⟩
        · rw [ite_eq_right jn]
          obtain ⟨i', hi', eq⟩ := snd i (by omega)
          exact ⟨i', by omega, eq⟩
      · by_cases it : i' = t
        · exact ⟨n, by omega, by rw [w2, ite_eq_left rfl, it]⟩
        · obtain ⟨i, hi, eq⟩ := cpl i' (by omega)
          exact ⟨i, by omega, by rw [w2, ite_eq_right (by omega)]; exact eq⟩
      · simp only [store]
        rw [ite_eq_right (by omega)]
        exact fr a ha
    · -- The same parent as the last one: nothing to keep.
      have eq : ps t / 2 = slotWord mm' list (n - 1) := by
        have := ite_eq_zero v
        exact (ofNat_inj (by omega) (slotWord_lt _ _ _)).mp this
      refine ⟨fun y a b c' d => by rw [assign_ne d]; exact ag y a b c' d,
        by rw [assign_ne (by decide)]; exact tv, n, n1, by omega, by rw [assign_ne (by decide)]; exact nv,
        by rw [assign_ne (by decide)]; exact pv, fun i hi hk => unread i (by omega) hk, srt, eq.symm,
        fun i hi => ?_, fun i' hi => ?_, fr⟩
      · obtain ⟨i', hi', e2⟩ := snd i hi
        exact ⟨i', by omega, e2⟩
      · by_cases it : i' = t
        · exact ⟨n - 1, by omega, by rw [← eq, it]⟩
        · obtain ⟨i, hi, e2⟩ := cpl i' (by omega)
          exact ⟨i, hi, e2⟩
    · -- The next entry.
      rintro e2 mm2 ⟨ag2, tv2, n', n1', nt', nv', pv', unread', srt', last', snd', cpl', fr'⟩
      refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_add (eval_var tv2) (eval_lit 1))) (Ends.nil ⟨⟨fun y a b c' d =>
        by rw [assign_ne a]; exact ag2 y a b c' d, t + 1, n', n1', nt', by omega, assign_eq,
        by rw [assign_ne (by decide)]; exact nv', by rw [assign_ne (by decide)]; exact pv', unread', srt',
        by rw [Nat.add_sub_cancel]; exact last', snd', cpl', fr'⟩, ?_⟩)
      rw [assign_eq, tv, ofNat_toNat (by omega), ofNat_toNat (by omega)]
      omega
  · rintro e' mm' ⟨⟨ag, t, n, n1, nt, tk, tv, nv, pv, _, srt, _, snd, cpl, fr⟩, done⟩
    have kv' := (ag 9 (by decide) (by decide) (by decide) (by decide)).trans kv
    have done := Option.some.inj (done.symm.trans (eval_lt (eval_var tv) (eval_var kv') (by omega) (by omega)))
    have tk' : t = k := by
      by_cases hb : t < k
      · rw [ite_eq_left hb] at done; exact absurd done (by decide)
      · omega
    subst tk'
    -- The count of parents kept is the new count.
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_var nv)) (Ends.nil ⟨fun y a b c' d f => by
      rw [assign_ne a]; exact ag y b c' d f, n, assign_eq, by rw [assign_ne (by decide)]; exact pv,
      ⟨n1, by omega, srt, fun i hi => ?_, fun x hx => ?_⟩, fr⟩)
    · obtain ⟨i', hi', eq⟩ := snd i hi
      obtain ⟨x, hx, ex⟩ := sound i' hi'
      exact ⟨x, hx, by rw [eq, ex, anc_up K h _ below]⟩
    · obtain ⟨i', hi', ex⟩ := complete x hx
      obtain ⟨i, hi, eq⟩ := cpl i' hi'
      exact ⟨i, hi, by rw [eq, ex, anc_up K h _ below]⟩

end EthLib.Consensus.Ssz.Native.Driver
