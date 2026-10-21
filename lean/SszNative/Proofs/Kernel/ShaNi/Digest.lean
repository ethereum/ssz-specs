import SszNative.Proofs.Kernel.ShaNi.Pair

/-! The SHA-NI kernel's last phase: the second feed-forward, the digest's words in order, and the stores. -/

namespace Ssz.Native.Kernel.ShaNi

open Ssz.Native.Asm Ssz.Sha256

/-- Reversing a register's four lanes. -/
theorem quad_pshufd_1B (t : State) (d r : Vreg) (a b c e : UInt32) (q : Quad (t.vec r) a b c e) :
    Quad ((exec1 (.pshufd d r 0x1B) t).vec d) e c b a := by
  -- The immediate reads lanes 3, 2, 1, 0, in that order.
  obtain ⟨q0, q1, q2, q3⟩ := q
  exact ⟨(lane_pshufd t d r _ 0 (by decide)).trans q3, (lane_pshufd t d r _ 1 (by decide)).trans q2,
    (lane_pshufd t d r _ 2 (by decide)).trans q1, (lane_pshufd t d r _ 3 (by decide)).trans q0⟩

/-- Swapping the lanes of each half of a register. -/
theorem quad_pshufd_B1 (t : State) (d r : Vreg) (a b c e : UInt32) (q : Quad (t.vec r) a b c e) :
    Quad ((exec1 (.pshufd d r 0xB1) t).vec d) b a e c := by
  -- The immediate reads lanes 1, 0, 3, 2, in that order.
  obtain ⟨q0, q1, q2, q3⟩ := q
  exact ⟨(lane_pshufd t d r _ 0 (by decide)).trans q1, (lane_pshufd t d r _ 1 (by decide)).trans q0,
    (lane_pshufd t d r _ 2 (by decide)).trans q3, (lane_pshufd t d r _ 3 (by decide)).trans q2⟩

/-- Four lanes carry over to a register equal to theirs. -/
theorem quad_keep (u t : Lanes) (h : u = t) (a b c d : UInt32) (q : Quad t a b c d) : Quad u a b c d := h ▸ q

/-- The digest's words as the stores read them: lane j of each register reversed. -/
def Ordered (lo hi : Lanes) (f : Vector UInt32 8) : Prop :=
  Quad lo (bswap32 f[0]) (bswap32 f[1]) (bswap32 f[2]) (bswap32 f[3]) ∧
  Quad hi (bswap32 f[4]) (bswap32 f[5]) (bswap32 f[6]) (bswap32 f[7])

/-- The second feed-forward, and the digest's words put in order and byte-reversed. -/
theorem finish_spec (s : State) (r st : Vector UInt32 8) (mask : MaskReady s)
    (hr : Packed (s.vec abef) (s.vec cdgh) r) (hs : Packed (s.vec midAbef) (s.vec midCdgh) st) :
    Ordered ((exec finish s).vec tmp) ((exec finish s).vec cdgh) (st.zipWith (· + ·) r) ∧
    (exec finish s).mem = s.mem ∧ (exec finish s).gpr = s.gpr ∧ MaskReady (exec finish s) := by
  have e : exec finish s = exec1 (.pshufb cdgh bswap) (exec1 (.pshufb tmp bswap) (exec1 (.palignr cdgh abef 8)
      (exec1 (.pblendw tmp cdgh 0xF0) (exec1 (.movdqa tmp abef) (exec1 (.pshufd cdgh cdgh 0xB1)
      (exec1 (.pshufd abef abef 0x1B) (exec1 (.paddd cdgh midCdgh) (exec1 (.paddd abef midAbef) s)))))))) := rfl
  rw [e]
  generalize h1 : exec1 (.paddd abef midAbef) s = u₁
  generalize h2 : exec1 (.paddd cdgh midCdgh) u₁ = u₂
  generalize h3 : exec1 (.pshufd abef abef 0x1B) u₂ = u₃
  generalize h4 : exec1 (.pshufd cdgh cdgh 0xB1) u₃ = u₄
  generalize h5 : exec1 (.movdqa tmp abef) u₄ = u₅
  generalize h6 : exec1 (.pblendw tmp cdgh 0xF0) u₅ = u₆
  generalize h7 : exec1 (.palignr cdgh abef 8) u₆ = u₇
  generalize h8 : exec1 (.pshufb tmp bswap) u₇ = u₈
  generalize h9 : exec1 (.pshufb cdgh bswap) u₈ = u₉
  obtain ⟨m1, g1, v1⟩ := h1 ▸ step_frame (.paddd abef midAbef) abef rfl s
  obtain ⟨m2, g2, v2⟩ := h2 ▸ step_frame (.paddd cdgh midCdgh) cdgh rfl u₁
  obtain ⟨m3, g3, v3⟩ := h3 ▸ step_frame (.pshufd abef abef 0x1B) abef rfl u₂
  obtain ⟨m4, g4, v4⟩ := h4 ▸ step_frame (.pshufd cdgh cdgh 0xB1) cdgh rfl u₃
  obtain ⟨m5, g5, v5⟩ := h5 ▸ step_frame (.movdqa tmp abef) tmp rfl u₄
  obtain ⟨m6, g6, v6⟩ := h6 ▸ step_frame (.pblendw tmp cdgh 0xF0) tmp rfl u₅
  obtain ⟨m7, g7, v7⟩ := h7 ▸ step_frame (.palignr cdgh abef 8) cdgh rfl u₆
  obtain ⟨m8, g8, v8⟩ := h8 ▸ step_frame (.pshufb tmp bswap) tmp rfl u₇
  obtain ⟨m9, g9, v9⟩ := h9 ▸ step_frame (.pshufb cdgh bswap) cdgh rfl u₈
  -- The mask register is never written.
  have k7 : u₇.vec bswap = s.vec bswap := by
    rw [v7 _ (by decide), v6 _ (by decide), v5 _ (by decide), v4 _ (by decide), v3 _ (by decide),
      v2 _ (by decide), v1 _ (by decide)]
  have k9 : u₉.vec bswap = s.vec bswap := by rw [v9 _ (by decide), v8 _ (by decide), k7]
  -- Phase 1: the feed-forward packs the final state.
  have p2 : Packed (u₂.vec abef) (u₂.vec cdgh) (st.zipWith (· + ·) r) := by
    apply packed_add _ _ _ _ _ _ _ _ _ _ hr hs
    · intro l hl
      rw [v2 _ (by decide), ← h1, lane_paddd _ _ _ l hl]
    · intro l hl
      rw [← h2, lane_paddd _ _ _ l hl, v1 _ (by decide), v1 _ (by decide)]
  generalize f : st.zipWith (· + ·) r = F at p2 ⊢
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨c0, c1, c2, c3⟩⟩ := p2
  -- Phase 2: A, B, E, F and G, H, C, D, from the lowest lane up.
  have q3 : Quad (u₃.vec abef) F[0] F[1] F[4] F[5] := h3 ▸ quad_pshufd_1B _ _ _ _ _ _ _ ⟨a0, a1, a2, a3⟩
  have q4c : Quad (u₄.vec cdgh) F[6] F[7] F[2] F[3] := by
    rw [← h4]
    exact quad_pshufd_B1 _ _ _ _ _ _ _ (quad_keep _ _ (v3 _ (by decide)) _ _ _ _ ⟨c0, c1, c2, c3⟩)
  have q4a : Quad (u₄.vec abef) F[0] F[1] F[4] F[5] := quad_keep _ _ (v4 _ (by decide)) _ _ _ _ q3
  have q5 : Quad (u₅.vec tmp) F[0] F[1] F[4] F[5] := by
    obtain ⟨b0, b1, b2, b3⟩ := q4a
    rw [← h5]
    exact ⟨(lane_movdqa _ _ _ 0 (by decide)).trans b0, (lane_movdqa _ _ _ 1 (by decide)).trans b1,
      (lane_movdqa _ _ _ 2 (by decide)).trans b2, (lane_movdqa _ _ _ 3 (by decide)).trans b3⟩
  -- Phase 3: A, B, C, D, then E, F, G, H.
  have q6 : Quad (u₆.vec tmp) F[0] F[1] F[2] F[3] := by
    obtain ⟨b0, b1, _, _⟩ := q5
    obtain ⟨_, _, d2, d3⟩ := q4c
    rw [← h6]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [pblendw_high _ _ _ 0 (by decide), if_pos (by decide)]; exact b0
    · rw [pblendw_high _ _ _ 1 (by decide), if_pos (by decide)]; exact b1
    · rw [pblendw_high _ _ _ 2 (by decide), if_neg (by decide), v5 _ (by decide)]; exact d2
    · rw [pblendw_high _ _ _ 3 (by decide), if_neg (by decide), v5 _ (by decide)]; exact d3
  have q7 : Quad (u₇.vec cdgh) F[4] F[5] F[6] F[7] := by
    obtain ⟨_, _, b2, b3⟩ := q4a
    obtain ⟨d0, d1, _, _⟩ := q4c
    rw [← h7]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [palignr8 _ _ _ 0 (by decide), dif_pos (by decide), v6 _ (by decide), v5 _ (by decide)]; exact b2
    · rw [palignr8 _ _ _ 1 (by decide), dif_pos (by decide), v6 _ (by decide), v5 _ (by decide)]; exact b3
    · rw [palignr8 _ _ _ 2 (by decide), dif_neg (by decide), v6 _ (by decide), v5 _ (by decide)]; exact d0
    · rw [palignr8 _ _ _ 3 (by decide), dif_neg (by decide), v6 _ (by decide), v5 _ (by decide)]; exact d1
  -- Phase 4: every word byte-reversed, for the big-endian digest.
  have rev : ∀ (u : State) (d : Vreg), u.vec bswap = s.vec bswap → ∀ l : Fin 16, l.val < 4 →
      (exec1 (.pshufb d bswap) u).vec d l = bswap32 (u.vec d l) := fun u d hk l hl => by
    rw [lane_pshufb _ _ _ l hl]
    exact shuffle_reverse _ _ (by rw [hk]; exact mask 0 (by decide)) (by rw [hk]; exact mask 1 (by decide))
      (by rw [hk]; exact mask 2 (by decide)) (by rw [hk]; exact mask 3 (by decide)) l hl
  have q8 : Quad (u₈.vec tmp) (bswap32 F[0]) (bswap32 F[1]) (bswap32 F[2]) (bswap32 F[3]) := by
    obtain ⟨b0, b1, b2, b3⟩ := q6
    rw [← h8]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [rev _ _ k7 0 (by decide), v7 _ (by decide), b0]
    · rw [rev _ _ k7 1 (by decide), v7 _ (by decide), b1]
    · rw [rev _ _ k7 2 (by decide), v7 _ (by decide), b2]
    · rw [rev _ _ k7 3 (by decide), v7 _ (by decide), b3]
  have k8 : u₈.vec bswap = s.vec bswap := by rw [v8 _ (by decide), k7]
  have q9 : Quad (u₉.vec cdgh) (bswap32 F[4]) (bswap32 F[5]) (bswap32 F[6]) (bswap32 F[7]) := by
    obtain ⟨b0, b1, b2, b3⟩ := q7
    rw [← h9]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [rev _ _ k8 0 (by decide), v8 _ (by decide), b0]
    · rw [rev _ _ k8 1 (by decide), v8 _ (by decide), b1]
    · rw [rev _ _ k8 2 (by decide), v8 _ (by decide), b2]
    · rw [rev _ _ k8 3 (by decide), v8 _ (by decide), b3]
  refine ⟨⟨quad_keep _ _ (v9 _ (by decide)) _ _ _ _ q8, q9⟩, ?_, ?_, fun l hl => ?_⟩
  · rw [m9, m8, m7, m6, m5, m4, m3, m2, m1]
  · rw [g9, g8, g7, g6, g5, g4, g3, g2, g1]
  · rw [k9]; exact mask l hl

/-- A byte of a register holding four reversed words: big-endian bytes of the words, in order. -/
theorem laneByte_reversed (v : Lanes) (f : Vector UInt32 8) (b : Nat) (hb : b + 3 < 8)
    (q : Quad v (bswap32 f[b]) (bswap32 f[b + 1]) (bswap32 f[b + 2]) (bswap32 f[b + 3])) (k : Nat) (hk : k < 16) :
    laneByte v k = (f[b + k / 4]'(by omega) >>> (24 - 8 * UInt32.ofNat (k % 4))).toUInt8 := by
  -- Byte k sits in lane k / 4, which holds a byte-reversed word of the digest.
  obtain ⟨q0, q1, q2, q3⟩ := q
  simp only [laneByte]
  have : k / 4 = 0 ∨ k / 4 = 1 ∨ k / 4 = 2 ∨ k / 4 = 3 := by omega
  rcases this with h | h | h | h
  · rw [show laneOf k = 0 from Fin.ext (by simp [laneOf]; omega), q0, wordByte_bswap32]
    simp only [h, Nat.add_zero]
  · rw [show laneOf k = 1 from Fin.ext (by simp [laneOf]; omega), q1, wordByte_bswap32]
    simp only [h]
  · rw [show laneOf k = 2 from Fin.ext (by simp [laneOf]; omega), q2, wordByte_bswap32]
    simp only [h]
  · rw [show laneOf k = 3 from Fin.ext (by simp [laneOf]; omega), q3, wordByte_bswap32]
    simp only [h]

/-- The two stores write the digest's 32 bytes at the output address, and nothing else. -/
theorem stores_spec (t : State) (f : Vector UInt32 8) (o : Ordered (t.vec tmp) (t.vec cdgh) f) (x : Nat) :
    (exec stores t).mem x =
      if (t.gpr out).toNat ≤ x ∧ x < (t.gpr out).toNat + 32 then (digest f).get! (x - (t.gpr out).toNat)
      else t.mem x := by
  -- The two stores write 16 bytes each, the lower and upper halves of the digest.
  simp only [stores, exec_cons, exec_nil, exec1_movdquStore, store, State.addr, Nat.add_zero]
  have lo := laneByte_reversed _ f 0 (by omega) (by simpa using o.1)
  have hi := laneByte_reversed _ f 4 (by omega) o.2
  by_cases a : (t.gpr out).toNat + 16 ≤ x ∧ x < (t.gpr out).toNat + 16 + 16
  · -- The upper half: words 4 to 7.
    rw [if_pos a, if_pos (by omega), hi _ (by omega), digest_get _ _ (by omega)]
    congr 2
    · congr 1; omega
    · congr 3; omega
  · rw [if_neg a]
    by_cases b : (t.gpr out).toNat ≤ x ∧ x < (t.gpr out).toNat + 16
    · -- The lower half: words 0 to 3.
      rw [if_pos b, if_pos (by omega), lo _ (by omega), digest_get _ _ (by omega)]
      congr 2
      congr 1; omega
    · rw [if_neg b, if_neg (by omega)]

/-- The stores keep every register. -/
theorem stores_frame (t : State) : (exec stores t).gpr = t.gpr ∧ (exec stores t).vec = t.vec := by
  simp [stores, exec1_movdquStore]
-- Stores write only memory.

/-- The initial state's loads write only vector registers. -/
theorem ivLoads_vecOnly : VecOnly ivLoads := by simp [VecOnly, ivLoads, writes]

/-- The first feed-forward writes only vector registers. -/
theorem middle_vecOnly : VecOnly middle := by simp [VecOnly, middle, writes]

/--
One pass of the loop body: the SHA-256 digest of the pair at the left and right addresses, stored at the output address.

Nothing else in memory changes, and the general registers and the mask register keep their values.
-/
theorem pair_spec (s : State) (table : TableAt s.mem (s.gpr tbl).toNat) (mask : MaskReady s) :
    (exec pairCode s).gpr = s.gpr ∧ MaskReady (exec pairCode s) ∧
    ∀ x, (exec pairCode s).mem x =
      if (s.gpr out).toNat ≤ x ∧ x < (s.gpr out).toNat + 32 then
        (Sha256.hash (pairMessage s.mem (s.gpr left).toNat (s.gpr right).toNat)).get! (x - (s.gpr out).toNat)
      else s.mem x := by
  rw [pairCode_split]
  simp only [exec_append]
  generalize h1 : exec loads s = t₁
  generalize h2 : exec ivLoads t₁ = t₂
  generalize h3 : exec firsts t₂ = t₃
  generalize h4 : exec middle t₃ = t₄
  generalize h5 : exec pads t₄ = t₅
  generalize h6 : exec finish t₅ = t₆
  generalize hm : pairMessage s.mem (s.gpr left).toNat (s.gpr right).toNat = M
  -- Memory and the general registers stay put until the stores.
  obtain ⟨g1, m1, _⟩ := h1 ▸ exec_frame _ loads_vecOnly s
  obtain ⟨g2, m2, _⟩ := h2 ▸ exec_frame _ ivLoads_vecOnly t₁
  obtain ⟨g3, m3, _⟩ := h3 ▸ exec_frame _ (vecOnly_flatMap _ firstRounds_vecOnly 16) t₂
  obtain ⟨g4, m4, _⟩ := h4 ▸ exec_frame _ middle_vecOnly t₃
  obtain ⟨g5, m5, _⟩ := h5 ▸ exec_frame _ (vecOnly_flatMap _ paddingRounds_vecOnly 16) t₄
  have tab : ∀ t : State, t.mem = s.mem → t.gpr = s.gpr → TableAt t.mem (t.gpr tbl).toNat :=
    fun t hm hg => by rw [hm, hg]; exact table
  -- The mask register survives every phase before the last.
  have k1 : t₁.vec bswap = s.vec bswap := h1 ▸ exec_vec _ loads_vecOnly _ (by
    simp [loads_blocks, loadBlock, writes, Fin.ext_iff, msg_val, bswap] <;> decide) s
  have k2 : t₂.vec bswap = t₁.vec bswap := h2 ▸ exec_vec _ ivLoads_vecOnly _ (by
    simp [ivLoads, writes, Fin.ext_iff, bswap, abef, cdgh] <;> decide) t₁
  have k3 : t₃.vec bswap = t₂.vec bswap := h3 ▸ exec_vec _ (vecOnly_flatMap _ firstRounds_vecOnly 16) _
    (writes_flatMap _ _ (fun r => firstRounds_writes r _ (by decide)) 16) t₂
  have k4 : t₄.vec bswap = t₃.vec bswap := h4 ▸ exec_vec _ middle_vecOnly _ (by
    simp [middle, writes, Fin.ext_iff, bswap, abef, cdgh, midAbef, midCdgh] <;> decide) t₃
  have k5 : t₅.vec bswap = t₄.vec bswap := h5 ▸ exec_vec _ (vecOnly_flatMap _ paddingRounds_vecOnly 16) _
    (writes_flatMap _ _ (fun r => paddingRounds_writes r _ (by decide)) 16) t₄
  have mask5 : MaskReady t₅ := fun l hl => by rw [k5, k4, k3, k2, k1]; exact mask l hl
  -- Phase 1: the schedule's first sixteen words and the initial state.
  have ready : Ready t₂ initialState (Wm M) 0 := by
    refine ⟨h2 ▸ ivLoads_spec t₁ (tab t₁ m1 g1), fun j hj _ l hl => ?_⟩
    rw [← h2, exec_vec _ ivLoads_vecOnly _ (by
      simp [ivLoads, writes, Fin.ext_iff, msg_val, abef, cdgh]; omega), ← h1, ← hm]
    simpa using loads_spec s mask j (by omega) l hl
  -- Phase 2: the first block's rounds and feed-forward.
  have first := h3 ▸ firstAll t₂ initialState (Wm M) (tab t₂ (m2.trans m1) (g2.trans g1)) (recurs_schedule M) ready
  have mid := h4 ▸ middle_spec t₃ (tab t₃ (m3.trans (m2.trans m1)) (g3.trans (g2.trans g1))) _ first
  rw [← compress_rounds] at mid
  obtain ⟨midState, midCopy⟩ := mid
  -- Phase 3: the padding block's rounds, which leave the kept copy alone.
  have pad := h5 ▸ paddingAll t₄ _ (tab t₄ (m4.trans (m3.trans (m2.trans m1)))
    (g4.trans (g3.trans (g2.trans g1)))) midState
  have keepA : t₅.vec midAbef = t₄.vec midAbef := h5 ▸ exec_vec _ (vecOnly_flatMap _ paddingRounds_vecOnly 16) _
    (writes_flatMap _ _ (fun r => paddingRounds_writes r _ (by decide)) 16) t₄
  have keepC : t₅.vec midCdgh = t₄.vec midCdgh := h5 ▸ exec_vec _ (vecOnly_flatMap _ paddingRounds_vecOnly 16) _
    (writes_flatMap _ _ (fun r => paddingRounds_writes r _ (by decide)) 16) t₄
  rw [← keepA, ← keepC] at midCopy
  -- Phase 4: the second feed-forward, the digest's order, and the stores.
  obtain ⟨ordered, m6, g6, mask6⟩ := h6 ▸ finish_spec t₅ _ _ mask5 pad midCopy
  have final : (compress initialState M 0).zipWith (· + ·)
      (rounds (compress initialState M 0) K P 64) = compress (compress initialState M 0) paddingBlock 0 :=
    (compress_rounds _ _ _).symm
  rw [final] at ordered
  have gs : t₆.gpr = s.gpr := g6.trans (g5.trans (g4.trans (g3.trans (g2.trans g1))))
  have ms : t₆.mem = s.mem := m6.trans (m5.trans (m4.trans (m3.trans (m2.trans m1))))
  refine ⟨?_, ?_, fun x => ?_⟩
  · rw [(stores_frame t₆).1, gs]
  · intro l hl
    rw [(stores_frame t₆).2]
    exact mask6 l hl
  · rw [stores_spec t₆ _ ordered x, gs, ms, hash_pair M (by rw [← hm]; exact pairMessage_size _ _ _)]

end Ssz.Native.Kernel.ShaNi
