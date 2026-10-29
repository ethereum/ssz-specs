import SszNative.Proofs.Driver.TreeStore.Rehash

/-!
The update driver rehashes the paths above rewritten leaves, and the tree is whole again.

A node is dirty when a rewritten leaf sits under it.
Before the update, the leaves and every clean node are right; dirty nodes may hold anything.
After the pass at height h, every node up to that height is right too.
Each pass moves the list of dirty nodes one height up and hashes them, so after the top, every node is right.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir

/-- A node of a height has a rewritten leaf under it. -/
def Dirty (idx : Nat → Nat) (c g j : Nat) : Prop :=
  ∃ x < c, idx x / 2 ^ g = j

/-- Every node up to a height, and every clean node above it, holds the root of the subtree under it. -/
def UpTo (mm : Memory) (tree K : Nat) (leaves : Array Bytes) (idx : Nat → Nat) (c h : Nat) : Prop :=
  ∀ g ≤ K, ∀ j < 2 ^ (K - g), (g ≤ h ∨ ¬ Dirty idx c g j) →
    nodeAt mm (tree + 32 * (2 ^ (K - g) + j)) = subtreeAt leaves g (j * 2 ^ g)

/-- A number lies in the window of at most one power of two. -/
theorem window_unique {K g g' j j' : Nat} (hg : g ≤ K) (hg' : g' ≤ K) (hj : j < 2 ^ (K - g)) (hj' : j' < 2 ^ (K - g'))
    (eq : 2 ^ (K - g) + j = 2 ^ (K - g') + j') : g = g' := by
  -- A smaller power's whole window lies below the larger power.
  have key : ∀ a b, a < b → 2 ^ a + 2 ^ a ≤ 2 ^ b := fun a b lt => by
    rw [← Nat.two_mul, ← Nat.pow_succ']; exact Nat.pow_le_pow_right (by decide) lt
  rcases Nat.lt_trichotomy (K - g) (K - g') with lt | e | gt
  · have := key _ _ lt; omega
  · omega
  · have := key _ _ gt; omega

/-- A list holding the same words is the same list. -/
theorem ListAt.congr {mm mm' : Memory} {list K c : Nat} {idx : Nat → Nat} {h k : Nat}
    (L : ListAt mm list K c idx h k) (same : ∀ i < k, slotWord mm' list i = slotWord mm list i) :
    ListAt mm' list K c idx h k :=
  ⟨L.pos, L.le, fun i j ij jk => by rw [same i (by omega), same j jk]; exact L.sorted i j ij jk,
    fun i hi => by rw [same i hi]; exact L.sound i hi,
    fun x hx => by obtain ⟨i, hi, e⟩ := L.complete x hx; exact ⟨i, hi, by rw [same i hi]; exact e⟩⟩

/-- Memory as at the start, outside the scratch buffer, the padding area, and the tree. -/
def UpdateFrame (mem mm : Memory) (tree K c scratch pad : Nat) : Prop :=
  ∀ a, ¬ (scratch ≤ a ∧ a < scratch + 104 * c) → ¬ (pad ≤ a ∧ a < pad + 1536) →
    ¬ (tree ≤ a ∧ a < tree + 64 * 2 ^ K) → mm a = mem a

/-- The context still holds in memory changed only in the scratch buffer, the padding area, and the tree. -/
theorem UpdatePre.ctxAt {w : World} {mem mm : Memory} {tree K indices c scratch ctx table zeros pad : Nat}
    {mask : UInt64} (pre : UpdatePre w mem tree K indices c scratch ctx table zeros pad mask)
    (fr : UpdateFrame mem mm tree K c scratch pad) : StoreCtx w mm ctx table zeros pad mask := by
  have pc := pre.ctxOk.padCtx
  have ptab := pre.ctxOk.padTable
  have pz := pre.ctxOk.padZeros
  have tz := pre.treeZeros
  have tt := pre.treeTable
  have tc := pre.treeCtx
  have stab := pre.scratchTable
  have sz := pre.scratchZeros
  have sc := pre.scratchCtx
  simp only [Apart] at pc ptab pz tz tt tc stab sz sc
  exact pre.ctxOk.congr fun a ha => fr a (by omega) (by omega) (by omega)

/-- The update loop's state at a height: the list one level's dirty nodes, and the tree right up to there. -/
structure UpdateLevel (mem mm : Memory) (leaves : Array Bytes) (idx : Nat → Nat)
    (tree K c scratch ctx pad : Nat) (e : Env) (h k : Nat) : Prop where
  /-- The kept variables. -/
  vals : HashVals e tree ctx scratch c k
  /-- No higher than the tree. -/
  height : h ≤ K
  /-- The list of the level's dirty nodes. -/
  list : ListAt mm scratch K c idx h k
  /-- The tree is right up to the level, and at every clean node. -/
  upTo : UpTo mm tree K leaves idx c h
  /-- Memory is as at the start outside the scratch buffer, the padding area, and the tree. -/
  frame : UpdateFrame mem mm tree K c scratch pad

set_option maxHeartbeats 8000000 in
/-- One pass of the update loop moves the tree's right part one height up. -/
theorem update_level {m : Module} {w : World} {sp : Nat} {mem : Memory}
    {tree K indices c scratch ctx table zeros pad : Nat} {mask : UInt64} (okP : HashCalls m w .pairs)
    (pre : UpdatePre w mem tree K indices c scratch ctx table zeros pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + hashStack ≤ sp)
    {leaves : Array Bytes} {idx : Nat → Nat} (inside : ∀ x < c, idx x < 2 ^ K)
    {e : Env} {mm : Memory} {h k : Nat} (lv : UpdateLevel mem mm leaves idx tree K c scratch ctx pad e h k)
    (below : h < K) :
    Ends m w sp e mm (.block TreeUpdate.level) fun e' mm' => ∃ k', UpdateLevel mem mm' leaves idx tree K c scratch
      ctx pad e' (h + 1) k' ∧ slotWord mm' scratch 0 < slotWord mm scratch 0 := by
  obtain ⟨v0, v5, v6, v7, v8, v9, v15⟩ := lv.vals
  have bt := access_bound pre.treeAccess
  have bs := access_bound pre.scratchAccess
  have st := pre.scratchTree
  have sp' := pre.scratchPad
  have tp := pre.treePad
  simp only [Apart] at st sp' tp
  have wK : 2 ^ K < 2 ^ 58 := Nat.pow_lt_pow_right (by decide) pre.narrow
  have L := lv.list
  have upK : 2 ^ (K - h) ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) (by omega)
  -- The smallest entry before the pass, as an ancestor.
  obtain ⟨x0, hx0, w0⟩ := L.sound 0 L.pos
  refine Ends.append (parents_ends v6 v9 L below (access_sub pre.scratchAccess (by omega) (by omega)) pre.narrow
    inside) ?_
  rintro e1 mm1 ⟨ag1, k', kv', pv', L', fr1⟩
  have fr1' : UpdateFrame mem mm1 tree K c scratch pad := fun a h1 h2 h3 => by
    rw [fr1 a (by omega)]; exact lv.frame a h1 h2 h3
  have L1 := L'
  -- The parents lie one height up.
  have lvl : ∀ i < k', 2 ^ (K - (h + 1)) ≤ slotWord mm1 scratch i ∧ slotWord mm1 scratch i < 2 ^ (K - h) := by
    intro i hi
    obtain ⟨x, hx, eq⟩ := L'.sound i hi
    have := anc_bounds K (h + 1) (idx x) (by omega) (inside x hx)
    rw [show 2 * 2 ^ (K - (h + 1)) = 2 ^ (K - h) by
      rw [show K - h = (K - (h + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]] at this
    rw [eq]; exact this
  have hv1 : HashVals e1 tree ctx scratch c k' :=
    ⟨(ag1 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans v0,
      (ag1 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans v5,
      (ag1 6 (by decide) (by decide) (by decide) (by decide) (by decide)).trans v6,
      (ag1 7 (by decide) (by decide) (by decide) (by decide) (by decide)).trans v7,
      (ag1 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans v8, kv',
      (ag1 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans v15⟩
  refine Ends.mono (rehash_ends okP pre kernels room (pre.ctxAt fr1') hv1 pv' below L'.pos L'.le L'.sorted lvl)
    fun e2 mm2 ⟨hv2, parent, rf⟩ => ⟨k', ⟨hv2, by omega, ?_, ?_, ?_⟩, ?_⟩
  all_goals
    -- The list's words lie apart from all the hashing writes.
    have keepList : ∀ i < c, slotWord mm2 scratch i = slotWord mm1 scratch i := fun i hi =>
      slotWord_congr fun r hr => rf _ (by omega) (by omega) fun j hj => by have := lvl j hj; omega
  · exact L'.congr fun i hi => keepList i (by have := L'.le; omega)
  · intro g hg j hj cond
    have gb : 2 ^ (K - g) ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) (by omega)
    by_cases isParent : ∃ i < k', slotWord mm1 scratch i = 2 ^ (K - g) + j
    · -- A parent: the hash of its two children, which were right.
      obtain ⟨i, hi, eq⟩ := isParent
      have li := lvl i hi
      have twice : 2 ^ (K - h) = 2 * 2 ^ (K - (h + 1)) := by
        rw [show K - h = (K - (h + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
      have gh : g = h + 1 := by
        have := window_unique (j := j) (j' := slotWord mm1 scratch i - 2 ^ (K - (h + 1))) (by omega)
          (show h + 1 ≤ K by omega) hj (by omega) (by omega)
        exact this
      subst gh
      rw [← eq, parent i hi, eq, ← parent_pair,
        show tree + 64 * (2 ^ (K - (h + 1)) + j) + 32 = tree + 32 * (2 ^ (K - h) + (2 * j + 1)) by omega,
        show tree + 64 * (2 ^ (K - (h + 1)) + j) = tree + 32 * (2 ^ (K - h) + 2 * j) by omega,
        nodeAt_congr (m₂ := mm) (a := tree + 32 * (2 ^ (K - h) + 2 * j)) fun r hr => fr1 _ (by omega),
        nodeAt_congr (m₂ := mm) (a := tree + 32 * (2 ^ (K - h) + (2 * j + 1))) fun r hr => fr1 _ (by omega),
        lv.upTo h (by omega) _ (by omega) (Or.inl (Nat.le_refl _)),
        lv.upTo h (by omega) _ (by omega) (Or.inl (Nat.le_refl _))]
    · -- Any other node is untouched, and was right before the pass.
      have notP : ∀ i < k', ¬ (tree + 32 * slotWord mm1 scratch i ≤ tree + 32 * (2 ^ (K - g) + j) ∧
          tree + 32 * (2 ^ (K - g) + j) < tree + 32 * slotWord mm1 scratch i + 32) := fun i hi hin =>
        isParent ⟨i, hi, by omega⟩
      have was : g ≤ h ∨ ¬ Dirty idx c g j := by
        rcases cond with le | clean
        · by_cases gh : g ≤ h
          · exact Or.inl gh
          · obtain rfl : g = h + 1 := by omega
            refine Or.inr fun ⟨x, hx, dx⟩ => isParent ?_
            obtain ⟨i, hi, eq⟩ := L'.complete x hx
            exact ⟨i, hi, by rw [eq, anc, dx]⟩
        · exact Or.inr clean
      rw [nodeAt_congr (m₂ := mm) fun r hr => by
        rw [rf _ (by omega) (by omega) fun i hi hin => notP i hi (by omega), fr1 _ (by omega)]]
      exact lv.upTo g hg j hj was
  · intro a h1 h2 h3
    rw [rf a (by omega) h2 fun i hi => by have := lvl i hi; omega]
    exact fr1' a h1 h2 h3
  · -- The smallest entry halves, at least.
    obtain ⟨i, hi, eq⟩ := L'.complete x0 hx0
    have sm : slotWord mm1 scratch 0 ≤ slotWord mm1 scratch i := by
      by_cases i0 : i = 0
      · rw [i0]; exact Nat.le_refl _
      · exact Nat.le_of_lt (L'.sorted 0 i (by omega) hi)
    have pos := (anc_bounds K h (idx x0) (by omega) (inside x0 hx0)).1
    have one : 1 ≤ 2 ^ (K - h) := Nat.one_le_two_pow
    rw [keepList 0 (by have := L'.le; have := L'.pos; omega), w0]
    rw [eq, ← anc_up K h _ below] at sm
    omega

set_option maxHeartbeats 8000000 in
/--
The update driver ends with the whole tree right over the new leaves, and a zero result.

Before it, the leaves and every clean node must be right; memory changes only in the scratch buffer, the padding
area, and the tree.
-/
theorem update_ends {m : Module} {w : World} {sp : Nat} {mem : Memory}
    {tree K indices c scratch ctx table zeros pad : Nat} {mask : UInt64} (okP : HashCalls m w .pairs)
    (pre : UpdatePre w mem tree K indices c scratch ctx table zeros pad mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + hashStack ≤ sp)
    {leaves : Array Bytes} {idx : Nat → Nat} (idxAt : ∀ i < c, slotWord mem indices i = idx i)
    (inside : ∀ x < c, idx x < 2 ^ K) (sorted : ∀ i j, i < j → j < c → idx i < idx j)
    (start : UpTo mem tree K leaves idx c 0) :
    Ends m w sp (entryEnv [UInt64.ofNat tree, UInt64.ofNat (2 ^ K), UInt64.ofNat indices, UInt64.ofNat c,
      UInt64.ofNat scratch, UInt64.ofNat ctx]) mem TreeUpdate.fn.body fun env mem' =>
        env 15 = 0 ∧ TreeAt mem' tree K leaves ∧ UpdateFrame mem mem' tree K c scratch pad := by
  have bt := access_bound pre.treeAccess
  have bs := access_bound pre.scratchAccess
  have bi := access_bound pre.indicesAccess
  have st := pre.scratchTree
  have si := pre.scratchIndices
  have sp' := pre.scratchPad
  simp only [Apart] at st si sp'
  have wK : 2 ^ K < 2 ^ 58 := Nat.pow_lt_pow_right (by decide) pre.narrow
  simp only [TreeUpdate.fn]
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 0)) ?_
  refine Ends.cons (Ends.when _ (eval_ne (eval_var (x := 3) (v := UInt64.ofNat c) rfl) (eval_lit 0))
    (fun v => ?_) (fun v => ?_)) fun _ _ h => Ends.nil h
  · have c0 : c ≠ 0 := fun z => ite_ne_zero v (by rw [z])
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_var (x := 4) (v := UInt64.ofNat scratch) rfl)) ?_
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_add (eval_var (x := 4) (v := UInt64.ofNat scratch) rfl)
      (eval_mul (eval_lit 8) (eval_var (x := 3) (v := UInt64.ofNat c) rfl)))) ?_
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_add (eval_var (x := 7) (v := UInt64.ofNat (scratch + 8 * c)) rfl)
      (eval_mul (eval_lit 64) (eval_var (x := 3) (v := UInt64.ofNat c) rfl)))) ?_
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 0)) ?_
    generalize hE : Asm.assign (Asm.assign (Asm.assign (Asm.assign (Asm.assign (entryEnv [UInt64.ofNat tree,
      UInt64.ofNat (2 ^ K), UInt64.ofNat indices, UInt64.ofNat c, UInt64.ofNat scratch, UInt64.ofNat ctx]) 15
      (UInt64.ofNat 0)) 6 (UInt64.ofNat scratch)) 7 (UInt64.ofNat (scratch + 8 * c))) 8
      (UInt64.ofNat (scratch + 8 * c + 64 * c))) 10 (UInt64.ofNat 0) = E
    have E0 : E 0 = UInt64.ofNat tree := by rw [← hE]; rfl
    have E1 : E 1 = UInt64.ofNat (2 ^ K) := by rw [← hE]; rfl
    have E2 : E 2 = UInt64.ofNat indices := by rw [← hE]; rfl
    have E3 : E 3 = UInt64.ofNat c := by rw [← hE]; rfl
    have E5 : E 5 = UInt64.ofNat ctx := by rw [← hE]; rfl
    have E6 : E 6 = UInt64.ofNat scratch := by rw [← hE]; rfl
    have E7 : E 7 = UInt64.ofNat (scratch + 8 * c) := by rw [← hE]; rfl
    have E8 : E 8 = UInt64.ofNat (scratch + 8 * c + 64 * c) := by rw [← hE]; rfl
    have E10 : E 10 = UInt64.ofNat 0 := by rw [← hE]; rfl
    have E15 : E 15 = 0 := by rw [← hE]; rfl
    -- The leaves' node indices.
    refine Ends.cons (Ends.loop (fun e mm => (∀ y, y ≠ 10 → e y = E y) ∧ ∃ t ≤ c, e 10 = UInt64.ofNat t ∧
        (∀ i < t, slotWord mm scratch i = 2 ^ K + idx i) ∧ ∀ a, ¬ (scratch ≤ a ∧ a < scratch + 8 * c) → mm a = mem a)
      (fun e _ => c - (e 10).toNat) ⟨fun _ _ => rfl, 0, Nat.zero_le _, E10, fun i hi => absurd hi (by omega),
        fun _ _ => rfl⟩ ?_ ?_) ?_
    · rintro e mm ⟨ag, t, ht, tv, _⟩
      exact ⟨_, eval_lt (eval_var tv) (eval_var ((ag 3 (by decide)).trans E3)) (by omega) (by omega)⟩
    · rintro e mm v ⟨ag, t, ht, tv, words, fr⟩ hv nz
      have hv := Option.some.inj (hv.symm.trans (eval_lt (eval_var tv) (eval_var ((ag 3 (by decide)).trans E3))
        (by omega) (by omega)))
      have tc : t < c := by
        by_cases hb : t < c
        · exact hb
        · rw [ite_eq_right hb] at hv; exact absurd hv nz
      have it : slotWord mm indices t = idx t := by
        rw [← idxAt t tc]; exact slotWord_congr fun r hr => fr _ (by omega)
      have ib := inside t tc
      have sw := store_slotWord (m := m) (sp := sp) (mem := mm) (eval_var ((ag 6 (by decide)).trans E6)) (eval_var tv)
        (eval_add (eval_var ((ag 1 (by decide)).trans E1)) (eval_slotWord (eval_var ((ag 2 (by decide)).trans E2))
          (eval_var tv) (access_sub pre.indicesAccess (by omega) (by omega))))
        (access_sub pre.scratchAccess (by omega) (by omega))
      rw [it] at sw
      refine Ends.step sw (Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_add (eval_var tv) (eval_lit 1)))
        (Ends.nil ⟨⟨fun y hy => by rw [assign_ne hy]; exact ag y hy, t + 1, by omega, assign_eq, fun i hi => ?_,
          fun a ha => ?_⟩, ?_⟩))
      · rw [slotWord_store _ _ _ _ _ (by omega)]
        by_cases e' : i = t
        · rw [ite_eq_left e', e']
        · rw [ite_eq_right e']; exact words i (by omega)
      · simp only [store]; rw [ite_eq_right (by omega)]; exact fr a ha
      · rw [assign_eq, tv, ofNat_toNat (by omega), ofNat_toNat (by omega)]
        omega
    rintro e1 mm1 ⟨⟨ag1, t, ht, tv, words, fr1⟩, done⟩
    have done := Option.some.inj (done.symm.trans (eval_lt (eval_var tv) (eval_var ((ag1 3 (by decide)).trans E3))
      (by omega) (by omega)))
    have tc : t = c := by
      by_cases hb : t < c
      · rw [ite_eq_left hb] at done; exact absurd done (by decide)
      · omega
    subst tc
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_var ((ag1 3 (by decide)).trans E3))) ?_
    -- The levels, one height up per pass.
    have frame1 : UpdateFrame mem mm1 tree K t scratch pad := fun a h1 _ _ => fr1 a (by omega)
    refine Ends.cons (Ends.loop (fun e mm => ∃ h k, UpdateLevel mem mm leaves idx tree K t scratch ctx pad e h k)
      (fun _ mm => slotWord mm scratch 0)
      ⟨0, t, ⟨⟨(assign_ne (by decide)).trans ((ag1 0 (by decide)).trans E0),
        (assign_ne (by decide)).trans ((ag1 5 (by decide)).trans E5),
        (assign_ne (by decide)).trans ((ag1 6 (by decide)).trans E6),
        (assign_ne (by decide)).trans ((ag1 7 (by decide)).trans E7),
        (assign_ne (by decide)).trans ((ag1 8 (by decide)).trans E8), assign_eq,
        (assign_ne (by decide)).trans ((ag1 15 (by decide)).trans E15)⟩, Nat.zero_le _,
        ⟨by omega, Nat.le_refl _, fun i j ij jt => by rw [words i (by omega), words j jt]; have := sorted i j ij jt; omega,
          fun i hi => ⟨i, hi, by rw [words i hi]; simp [anc]⟩, fun x hx => ⟨x, hx, by rw [words x hx]; simp [anc]⟩⟩,
        fun g hg j hj cond => by
          rw [nodeAt_congr (m₂ := mem) fun r hr => fr1 _ (by
            have : 2 ^ (K - g) ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) (by omega)
            omega)]
          exact start g hg j hj (by omega), frame1⟩⟩ ?_ ?_) ?_
    · rintro e mm ⟨h, k, lv⟩
      obtain ⟨_, _, v6, _⟩ := lv.vals
      exact ⟨_, eval_lt (eval_lit 1) (eval_slotWord0 (eval_var v6) (access_sub pre.scratchAccess (by omega) (by omega)))
        (by decide) (slotWord_lt _ _ _)⟩
    · rintro e mm v ⟨h, k, lv⟩ hv nz
      obtain ⟨_, _, v6, _⟩ := lv.vals
      have hv := Option.some.inj (hv.symm.trans (eval_lt (eval_lit 1) (eval_slotWord0 (eval_var v6)
        (access_sub pre.scratchAccess (by omega) (by omega))) (by decide) (slotWord_lt _ _ _)))
      have below : h < K := by
        by_cases hk : h < K
        · exact hk
        · obtain ⟨x, hx, eq⟩ := lv.list.sound 0 lv.list.pos
          rw [show h = K by have := lv.height; omega, anc_top K _ (inside x hx)] at eq
          rw [eq, ite_eq_right (by decide)] at hv; exact absurd hv nz
      exact Ends.mono (update_level okP pre kernels room inside lv below) fun e' mm' ⟨k', lv', dec⟩ =>
        ⟨⟨_, _, lv'⟩, dec⟩
    rintro e mm ⟨⟨h, k, lv⟩, done⟩
    obtain ⟨_, _, v6, _, _, _, v15⟩ := lv.vals
    have done := Option.some.inj (done.symm.trans (eval_lt (eval_lit 1) (eval_slotWord0 (eval_var v6)
      (access_sub pre.scratchAccess (by omega) (by omega))) (by decide) (slotWord_lt _ _ _)))
    have top : h = K := by
      by_cases hk : h < K
      · obtain ⟨x, hx, eq⟩ := lv.list.sound 0 lv.list.pos
        have := (anc_bounds K h (idx x) (by omega) (inside x hx)).1
        have : 2 ≤ 2 ^ (K - h) := Nat.one_lt_two_pow (by omega)
        rw [eq, ite_eq_left (by omega)] at done; exact absurd done (by decide)
      · exact Nat.le_antisymm lv.height (by omega)
    subst top
    exact Ends.nil ⟨v15, fun g hg j hj => lv.upTo g hg j hj (Or.inl hg), lv.frame⟩
  · -- No leaves were rewritten: every node is clean, so the tree is already right.
    have c0 : c = 0 := by
      have := ite_eq_zero v
      exact (ofNat_inj (by omega) (by decide)).mp this
    subst c0
    exact ⟨rfl, fun g hg j hj => start g hg j hj (Or.inr fun ⟨x, hx, _⟩ => absurd hx (by omega)), fun _ _ _ _ => rfl⟩

end EthLib.Consensus.Ssz.Native.Driver
