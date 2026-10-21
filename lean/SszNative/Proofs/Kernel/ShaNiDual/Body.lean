import SszNative.Proofs.Kernel.ShaNiDual.Digest

/-! One pass of the interleaved kernel's loop: two pairs' digests, written side by side at the output. -/

namespace Ssz.Native.Kernel.ShaNiDual

open Ssz.Native.Asm Ssz.Sha256
open ShaNi (writes VecOnly exec_vec Packed Wm MaskReady Recurs rounds K P recurs_schedule compress_rounds
  exec_range_succ pairMessage_size)

/-- Both pairs' first-block groups, alternating, up to a count of groups. -/
def firstGroups (m : Nat) : List Instr :=
  (List.range m).flatMap fun r => firstRounds first r ++ firstRounds second r

/-- Both pairs' padding-block groups, alternating, up to a count of groups. -/
def paddingGroups (m : Nat) : List Instr :=
  (List.range m).flatMap fun r => paddingRounds first r ++ paddingRounds second r

/-- The body for two pairs, phase by phase. -/
theorem pairsCode_split (ls rs : Nat) :
    pairsCode ls rs = loadCode first 0 0 ++ loadCode second ls rs ++ firstGroups 16 ++ middleCode first ++
      middleCode second ++ paddingGroups 16 ++ finishCode first 0 ++ finishCode second 32 := rfl

/-- Running a block of one pair's instructions keeps everything the other pair keeps, the mask, memory, and the table. -/
structure Kept (g : Lane) (s t : State) : Prop where
  /-- Every register outside the pair's own and the shared scratch registers is unchanged. -/
  vec : ∀ v, ¬ Touches g v → t.vec v = s.vec v
  /-- The general registers are unchanged. -/
  gpr : t.gpr = s.gpr
  /-- Memory is unchanged. -/
  mem : t.mem = s.mem

/-- A block of one pair's instructions keeps what that pair does not touch. -/
theorem kept_of (g : Lane) (body : List Instr) (hb : ∀ i ∈ body, ∃ d, writes i = some d ∧ Touches g d)
    (s : State) : Kept g s (exec body s) :=
  ⟨fun v hv => untouched g body hb v hv s, (lane_frame g body hb s).1, (lane_frame g body hb s).2.1⟩

/-- A machine whose mask and memory are another's keeps its mask and its table. -/
theorem mask_kept (g : Lane) (hg : Good g) (s t : State) (k : Kept g s t) (mask : MaskReady s) : MaskReady t :=
  fun l hl => by rw [k.vec _ (bswap_untouched g hg)]; exact mask l hl

/-- The table is where it was when memory and the general registers are. -/
theorem table_kept (s t : State) (gpr : t.gpr = s.gpr) (mem : t.mem = s.mem)
    (table : TableAt s.mem (s.gpr tbl).toNat) : TableAt t.mem (t.gpr tbl).toNat := by
  rw [gpr, mem]; exact table

/-- The first-block groups of both pairs: each pair's sixty-four rounds over its own schedule. -/
theorem firstGroups_spec (s : State) (st : Vector UInt32 8) (w₁ w₂ : Nat → UInt32)
    (table : TableAt s.mem (s.gpr tbl).toNat) (rec₁ : Recurs w₁) (rec₂ : Recurs w₂)
    (h₁ : Ready first s st w₁ 0) (h₂ : Ready second s st w₂ 0) :
    ∀ m ≤ 16, Ready first (exec (firstGroups m) s) st w₁ m ∧ Ready second (exec (firstGroups m) s) st w₂ m ∧
      (exec (firstGroups m) s).gpr = s.gpr ∧ (exec (firstGroups m) s).mem = s.mem ∧
      (∀ v, ¬ Touches first v → ¬ Touches second v → (exec (firstGroups m) s).vec v = s.vec v) := by
  intro m hm
  -- Induction on the groups run so far.
  induction m with
  | zero => exact ⟨h₁, h₂, rfl, rfl, fun _ _ _ => rfl⟩
  | succ m ih =>
    obtain ⟨r₁, r₂, g₀, m₀, v₀⟩ := ih (by omega)
    simp only [firstGroups] at *
    rw [exec_range_succ, exec_append]
    generalize hu : exec ((List.range m).flatMap fun r => firstRounds first r ++ firstRounds second r) s = u at *
    have tab : TableAt u.mem (u.gpr tbl).toNat := table_kept s u g₀ m₀ table
    -- The first pair's group, which the second pair's registers do not see.
    have k₁ := kept_of first _ (firstRounds_touches first m) u
    have a₁ := firstRounds_spec first good_first m (by omega) u st w₁ tab rec₁ r₁
    have b₁ := ready_congr second u _ st w₂ m (fun v hv => k₁.vec v (second_apart v hv)) r₂
    -- The second pair's group, which the first pair's registers do not see.
    have k₂ := kept_of second _ (firstRounds_touches second m) (exec (firstRounds first m) u)
    have b₂ := firstRounds_spec second good_second m (by omega) _ st w₂
      (table_kept u _ k₁.gpr k₁.mem tab) rec₂ b₁
    have a₂ := ready_congr first _ _ st w₁ (m + 1) (fun v hv => k₂.vec v (first_apart v hv)) a₁
    refine ⟨a₂, b₂, by rw [k₂.gpr, k₁.gpr, g₀], by rw [k₂.mem, k₁.mem, m₀], fun v h₁ h₂ => ?_⟩
    rw [k₂.vec v h₂, k₁.vec v h₁, v₀ v h₁ h₂]

/-- Every padding-block group writes only the word register and the pair's state registers. -/
theorem paddingRounds_writes (g : Lane) (r : Nat) :
    ∀ i ∈ paddingRounds g r, writes i = some wk ∨ writes i = some g.abef ∨ writes i = some g.cdgh := by
  -- The table load writes the word register, and the rounds the state registers.
  simp [paddingRounds, fourRounds, writes]

/-- A padding-block group keeps the pair's schedule vectors, where its first block's state is kept. -/
theorem paddingRounds_keep (g : Lane) (hg : Good g) (r q : Nat) (s : State) :
    (exec (paddingRounds g r) s).vec (g.msg q) = s.vec (g.msg q) := by
  obtain ⟨ma, mc, mw, -, -⟩ := msg_apart g hg q
  exact exec_vec _ (fun i hi => by rcases paddingRounds_writes g r i hi with e | e | e <;> simp [e]) _
    (fun i hi e => by
      rcases paddingRounds_writes g r i hi with e' | e' | e' <;> rw [e'] at e <;> have := Option.some.inj e
      · exact mw this.symm
      · exact ma this.symm
      · exact mc this.symm) s

/-- The padding-block groups of both pairs: each pair's sixty-four rounds, keeping each pair's first block. -/
theorem paddingGroups_spec (s : State) (c₁ c₂ : Vector UInt32 8) (table : TableAt s.mem (s.gpr tbl).toNat)
    (h₁ : Packed (s.vec first.abef) (s.vec first.cdgh) c₁) (h₂ : Packed (s.vec second.abef) (s.vec second.cdgh) c₂) :
    ∀ m ≤ 16,
      Packed ((exec (paddingGroups m) s).vec first.abef) ((exec (paddingGroups m) s).vec first.cdgh)
        (rounds c₁ K P (4 * m)) ∧
      Packed ((exec (paddingGroups m) s).vec second.abef) ((exec (paddingGroups m) s).vec second.cdgh)
        (rounds c₂ K P (4 * m)) ∧
      (exec (paddingGroups m) s).gpr = s.gpr ∧ (exec (paddingGroups m) s).mem = s.mem ∧
      (∀ q, (exec (paddingGroups m) s).vec (first.msg q) = s.vec (first.msg q)) ∧
      (∀ q, (exec (paddingGroups m) s).vec (second.msg q) = s.vec (second.msg q)) ∧
      (∀ v, ¬ Touches first v → ¬ Touches second v → (exec (paddingGroups m) s).vec v = s.vec v) := by
  intro m hm
  -- Induction on the groups run so far.
  induction m with
  | zero => exact ⟨h₁, h₂, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl⟩
  | succ m ih =>
    obtain ⟨p₁, p₂, g₀, m₀, f₀, s₀, v₀⟩ := ih (by omega)
    simp only [paddingGroups] at *
    rw [exec_range_succ, exec_append]
    generalize hu : exec ((List.range m).flatMap fun r => paddingRounds first r ++ paddingRounds second r) s = u at *
    have tab : TableAt u.mem (u.gpr tbl).toNat := table_kept s u g₀ m₀ table
    have k₁ := kept_of first _ (paddingRounds_touches first m) u
    have k₂ := kept_of second _ (paddingRounds_touches second m) (exec (paddingRounds first m) u)
    -- The first pair's group, which the second pair's registers do not see.
    have a₁ := paddingRounds_spec first good_first m (by omega) u c₁ tab p₁
    have b₁ : Packed ((exec (paddingRounds first m) u).vec second.abef)
        ((exec (paddingRounds first m) u).vec second.cdgh) (rounds c₂ K P (4 * m)) := by
      rw [k₁.vec _ (second_apart _ (Or.inl rfl)), k₁.vec _ (second_apart _ (Or.inr (Or.inl rfl)))]
      exact p₂
    -- The second pair's group, which the first pair's registers do not see.
    have b₂ := paddingRounds_spec second good_second m (by omega) _ c₂ (table_kept u _ k₁.gpr k₁.mem tab) b₁
    refine ⟨?_, b₂, by rw [k₂.gpr, k₁.gpr, g₀], by rw [k₂.mem, k₁.mem, m₀], fun q => ?_, fun q => ?_,
      fun v h₁ h₂ => ?_⟩
    · rw [k₂.vec _ (first_apart _ (Or.inl rfl)), k₂.vec _ (first_apart _ (Or.inr (Or.inl rfl)))]
      exact a₁
    · rw [k₂.vec _ (first_apart _ (Or.inr (Or.inr ⟨q, rfl⟩))), paddingRounds_keep first good_first, f₀]
    · rw [paddingRounds_keep second good_second, k₁.vec _ (second_apart _ (Or.inr (Or.inr ⟨q, rfl⟩))), s₀]
    · rw [k₂.vec v h₂, k₁.vec v h₁, v₀ v h₁ h₂]

/-- Packed words held in registers the other pair never writes stay packed. -/
theorem packed_kept (g h : Lane) (apart : ∀ v, Holds h v → ¬ Touches g v) (s t : State) (k : Kept g s t)
    (st : Vector UInt32 8) (p : Packed (s.vec h.abef) (s.vec h.cdgh) st) :
    Packed (t.vec h.abef) (t.vec h.cdgh) st := by
  -- Both state registers of the other pair are untouched.
  rw [k.vec _ (apart _ (Or.inl rfl)), k.vec _ (apart _ (Or.inr (Or.inl rfl)))]
  exact p

/-- A pair's first-block state kept in its schedule vectors stays packed when the other pair runs. -/
theorem mids_kept (g h : Lane) (hh : Good h) (apart : ∀ v, Holds h v → ¬ Touches g v) (s t : State) (k : Kept g s t)
    (st : Vector UInt32 8) (p : Packed (s.vec h.midAbef) (s.vec h.midCdgh) st) :
    Packed (t.vec h.midAbef) (t.vec h.midCdgh) st := by
  -- The kept state sits in the other pair's first two schedule vectors.
  rw [hh.mid_abef, hh.mid_cdgh] at p ⊢
  rw [k.vec _ (apart _ (Or.inr (Or.inr ⟨0, rfl⟩))), k.vec _ (apart _ (Or.inr (Or.inr ⟨1, rfl⟩)))]
  exact p

/-- A pair's message is always 64 bytes. -/
theorem messageAt_size (s : State) (leftDisp rightDisp : Nat) : (messageAt s leftDisp rightDisp).size = 64 :=
  pairMessage_size _ _ _

/-- What the two pairs' final registers hold: each pair's digest words in the order the stores read them. -/
theorem final_ordered (g : Lane) (hg : Good g) (t : State) (M : ByteArray) (mask : MaskReady t)
    (pad : Packed (t.vec g.abef) (t.vec g.cdgh) (rounds (compress initialState M 0) K P 64))
    (mid : Packed (t.vec g.midAbef) (t.vec g.midCdgh) (compress initialState M 0)) :
    ShaNi.Ordered ((exec (finishRegs g) t).vec tmp) ((exec (finishRegs g) t).vec g.cdgh)
      (compress (compress initialState M 0) paddingBlock 0) := by
  -- The register work orders the second feed-forward, which is the second compression.
  have o := finishRegs_spec g hg t _ _ mask pad mid
  rwa [← compress_rounds] at o

/-- The bytes a pass writes: the first pair's digest, then the second pair's, and memory elsewhere unchanged. -/
def passBytes (s : State) (ls rs x : Nat) : UInt8 :=
  let o := (s.gpr out).toNat
  if o + 32 ≤ x ∧ x < o + 32 + 32 then (Sha256.hash (messageAt s ls rs)).get! (x - (o + 32))
  else if o ≤ x ∧ x < o + 32 then (Sha256.hash (messageAt s 0 0)).get! (x - o)
  else s.mem x

/--
One pass of the loop body: the SHA-256 digests of the pairs at the left and right addresses and one stride further.

They are stored side by side at the output address.
Nothing else in memory changes, and the general registers and the mask register keep their values.
-/
theorem pairs_spec (ls rs : Nat) (s : State) (table : TableAt s.mem (s.gpr tbl).toNat) (mask : MaskReady s) :
    (exec (pairsCode ls rs) s).gpr = s.gpr ∧ MaskReady (exec (pairsCode ls rs) s) ∧
    ∀ x, (exec (pairsCode ls rs) s).mem x = passBytes s ls rs x := by
  rw [pairsCode_split]
  simp only [exec_append]
  generalize h1 : exec (loadCode first 0 0) s = t₁
  generalize h2 : exec (loadCode second ls rs) t₁ = t₂
  generalize h3 : exec (firstGroups 16) t₂ = t₃
  generalize h4 : exec (middleCode first) t₃ = t₄
  generalize h5 : exec (middleCode second) t₄ = t₅
  generalize h6 : exec (paddingGroups 16) t₅ = t₆
  generalize h7 : exec (finishCode first 0) t₆ = t₇
  generalize h8 : exec (finishCode second 32) t₇ = t₈
  generalize hM₁ : messageAt s 0 0 = M₁
  generalize hM₂ : messageAt s ls rs = M₂
  -- Phase 1: each pair's message and the initial state, the second load leaving the first pair's registers alone.
  have k1 := h1 ▸ kept_of first _ (loadCode_touches first 0 0) s
  have k2 := h2 ▸ kept_of second _ (loadCode_touches second ls rs) t₁
  have l1 := loadCode_spec first good_first s 0 0 table mask
  have l2 := loadCode_spec second good_second t₁ ls rs (table_kept s t₁ k1.gpr k1.mem table)
    (mask_kept first good_first s t₁ k1 mask)
  rw [h1] at l1
  rw [h2] at l2
  have m₂ : messageAt t₁ ls rs = M₂ := by rw [← hM₂]; simp [messageAt, k1.gpr, k1.mem]
  rw [m₂] at l2
  have tab₂ : TableAt t₂.mem (t₂.gpr tbl).toNat := table_kept s t₂ (k2.gpr.trans k1.gpr) (k2.mem.trans k1.mem) table
  have ready₁ : Ready first t₂ initialState (Wm M₁) 0 := by
    refine ⟨packed_kept second first first_apart t₁ t₂ k2 _ l1.1, fun j hj _ l hl => ?_⟩
    rw [k2.vec _ (first_apart _ (Or.inr (Or.inr ⟨_, rfl⟩))), ← hM₁]
    simpa using l1.2 j hj l hl
  have ready₂ : Ready second t₂ initialState (Wm M₂) 0 :=
    ⟨l2.1, fun j hj _ l hl => by simpa using l2.2 j hj l hl⟩
  -- Phase 2: both pairs' first-block rounds.
  obtain ⟨f₁, f₂, g3, m3, -⟩ := firstGroups_spec t₂ initialState _ _ tab₂ (recurs_schedule M₁)
    (recurs_schedule M₂) ready₁ ready₂ 16 (by omega)
  rw [h3] at f₁ f₂ g3 m3
  have tab₃ : TableAt t₃.mem (t₃.gpr tbl).toNat := table_kept t₂ t₃ g3 m3 tab₂
  -- Phase 3: both pairs' first feed-forwards, each kept aside.
  have k4 := h4 ▸ kept_of first _ (middleCode_touches first good_first) t₃
  have k5 := h5 ▸ kept_of second _ (middleCode_touches second good_second) t₄
  have mid₁ := middleCode_spec first good_first t₃ tab₃ _ f₁.1
  rw [h4, ← compress_rounds] at mid₁
  have mid₂ := middleCode_spec second good_second t₄ (table_kept t₃ t₄ k4.gpr k4.mem tab₃) _
    (packed_kept first second second_apart t₃ t₄ k4 _ f₂.1)
  rw [h5, ← compress_rounds] at mid₂
  have tab₅ : TableAt t₅.mem (t₅.gpr tbl).toNat := table_kept t₃ t₅ (k5.gpr.trans k4.gpr) (k5.mem.trans k4.mem) tab₃
  -- Phase 4: both pairs' padding-block rounds, which keep both first blocks.
  obtain ⟨p₁, p₂, g6, m6, keep₁, keep₂, keep⟩ := paddingGroups_spec t₅ _ _ tab₅
    (packed_kept second first first_apart t₄ t₅ k5 _ mid₁.1) mid₂.1 16 (by omega)
  rw [h6] at p₁ p₂ g6 m6 keep₁ keep₂ keep
  have midA : Packed (t₆.vec first.midAbef) (t₆.vec first.midCdgh) (compress initialState M₁ 0) := by
    have := mids_kept second first good_first first_apart t₄ t₅ k5 _ mid₁.2
    rw [good_first.mid_abef, good_first.mid_cdgh] at this ⊢
    rw [keep₁, keep₁]
    exact this
  have midB : Packed (t₆.vec second.midAbef) (t₆.vec second.midCdgh) (compress initialState M₂ 0) := by
    have := mid₂.2
    rw [good_second.mid_abef, good_second.mid_cdgh] at this ⊢
    rw [keep₂, keep₂]
    exact this
  -- The mask has survived every phase so far.
  have mask₆ : MaskReady t₆ := by
    have mask₅ := mask_kept second good_second t₄ t₅ k5 (mask_kept first good_first t₃ t₄ k4
      (fun l hl => by
        rw [← h3, (firstGroups_spec t₂ initialState _ _ tab₂ (recurs_schedule M₁) (recurs_schedule M₂) ready₁ ready₂
          16 (by omega)).2.2.2.2 _ (bswap_untouched first good_first) (bswap_untouched second good_second)]
        exact mask_kept second good_second t₁ t₂ k2 (mask_kept first good_first s t₁ k1 mask) l hl))
    exact fun l hl => by
      rw [keep _ (bswap_untouched first good_first) (bswap_untouched second good_second)]
      exact mask₅ l hl
  -- Phase 5: the first pair's digest, stored first.
  rw [finishCode_split, exec_append] at h7
  generalize h7a : exec (finishRegs first) t₆ = t₆'
  rw [h7a] at h7
  have k7a := h7a ▸ kept_of first _ (finishRegs_touches first) t₆
  have ord₁ := h7a ▸ final_ordered first good_first t₆ M₁ mask₆ p₁ midA
  have st₁ := fun x => h7 ▸ storesAt_spec first 0 t₆' _ ord₁ x
  obtain ⟨sg₁, sv₁, -⟩ := h7 ▸ storesAt_frame first 0 t₆'
  -- Phase 6: the second pair's digest, stored after it.
  rw [finishCode_split, exec_append] at h8
  generalize h8a : exec (finishRegs second) t₇ = t₇'
  rw [h8a] at h8
  have k8a := h8a ▸ kept_of second _ (finishRegs_touches second) t₇
  have mask₇ : MaskReady t₇ := fun l hl => by
    rw [sv₁]; exact mask_kept first good_first t₆ t₆' k7a mask₆ l hl
  have p₂' : Packed (t₇.vec second.abef) (t₇.vec second.cdgh) (rounds (compress initialState M₂ 0) K P 64) := by
    rw [sv₁]; exact packed_kept first second second_apart t₆ t₆' k7a _ p₂
  have midB' : Packed (t₇.vec second.midAbef) (t₇.vec second.midCdgh) (compress initialState M₂ 0) := by
    rw [sv₁]; exact mids_kept first second good_second second_apart t₆ t₆' k7a _ midB
  have ord₂ := h8a ▸ final_ordered second good_second t₇ M₂ mask₇ p₂'
    midB'
  have st₂ := fun x => h8 ▸ storesAt_spec second 32 t₇' _ ord₂ x
  obtain ⟨sg₂, sv₂, -⟩ := h8 ▸ storesAt_frame second 32 t₇'
  -- The general registers never change.
  have gs : t₈.gpr = s.gpr := by
    rw [sg₂, k8a.gpr, sg₁, k7a.gpr, g6, k5.gpr, k4.gpr, g3, k2.gpr, k1.gpr]
  have g7 : t₇'.gpr = s.gpr := by rw [k8a.gpr, sg₁, k7a.gpr, g6, k5.gpr, k4.gpr, g3, k2.gpr, k1.gpr]
  have g6' : t₆'.gpr = s.gpr := by rw [k7a.gpr, g6, k5.gpr, k4.gpr, g3, k2.gpr, k1.gpr]
  have ms : t₆'.mem = s.mem := by rw [k7a.mem, m6, k5.mem, k4.mem, m3, k2.mem, k1.mem]
  refine ⟨gs, fun l hl => ?_, fun x => ?_⟩
  · rw [sv₂]; exact mask_kept second good_second t₇ t₇' k8a mask₇ l hl
  · -- The second store over the first, over the original memory.
    rw [st₂, g7, k8a.mem, st₁, g6', ms]
    unfold passBytes
    rw [hM₁, hM₂, hash_pair M₂ (by rw [← hM₂]; exact messageAt_size _ _ _),
      hash_pair M₁ (by rw [← hM₁]; exact messageAt_size _ _ _)]
    simp only [Nat.add_zero]

end Ssz.Native.Kernel.ShaNiDual
