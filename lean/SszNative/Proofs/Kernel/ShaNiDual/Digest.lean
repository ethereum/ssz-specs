import SszNative.Proofs.Kernel.ShaNiDual.Pair

/-! One pair's last phase: the second feed-forward, the digest's words in order, and the stores. -/

namespace Ssz.Native.Kernel.ShaNiDual

open Ssz.Native.Asm Ssz.Sha256
open ShaNi (writes VecOnly exec_frame exec_vec step_frame Quad Packed MaskReady packed_add quad_pshufd_1B
  quad_pshufd_B1 quad_keep lane_movdqa lane_paddd lane_pshufb pblendw_high palignr8 shuffle_reverse bswap32 Ordered
  laneByte_reversed digest_get exec1_movdquStore)

/-- A pair's second feed-forward and the digest's words put in order, before the stores. -/
def finishRegs (g : Lane) : List Instr :=
  [.paddd g.abef g.midAbef, .paddd g.cdgh g.midCdgh, .pshufd g.abef g.abef 0x1B, .pshufd g.cdgh g.cdgh 0xB1,
    .movdqa tmp g.abef, .pblendw tmp g.cdgh 0xF0, .palignr g.cdgh g.abef 8, .pshufb tmp bswap, .pshufb g.cdgh bswap]

/-- A pair's two stores, at a displacement from the output address. -/
def storesAt (g : Lane) (disp : Nat) : List Instr :=
  [.movdquStore ⟨out, disp⟩ tmp, .movdquStore ⟨out, disp + 16⟩ g.cdgh]

/-- A pair's last phase is its register work, then its stores. -/
theorem finishCode_split (g : Lane) (disp : Nat) : finishCode g disp = finishRegs g ++ storesAt g disp := rfl

/-- Every instruction of a pair's register work writes the pair's state registers or the temporary. -/
theorem finishRegs_touches (g : Lane) : ∀ i ∈ finishRegs g, ∃ d, writes i = some d ∧ Touches g d := by
  -- Each instruction writes one of three registers.
  simp only [finishRegs, List.mem_cons, List.not_mem_nil, or_false]
  intro i hi
  rcases hi with h | h | h | h | h | h | h | h | h <;> subst h <;> refine ⟨_, rfl, ?_⟩ <;> unfold Touches <;>
    first
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

/-- The second feed-forward, and the digest's words put in order and byte-reversed. -/
theorem finishRegs_spec (g : Lane) (hg : Good g) (s : State) (r st : Vector UInt32 8) (mask : MaskReady s)
    (hr : Packed (s.vec g.abef) (s.vec g.cdgh) r) (hs : Packed (s.vec g.midAbef) (s.vec g.midCdgh) st) :
    Ordered ((exec (finishRegs g) s).vec tmp) ((exec (finishRegs g) s).vec g.cdgh) (st.zipWith (· + ·) r) := by
  obtain ⟨ac, -, at', ab, -, ct, cb⟩ := state_apart g hg
  have tb : tmp ≠ bswap := by decide
  rw [hg.mid_abef, hg.mid_cdgh] at hs
  obtain ⟨m0a, m0c, -, -, -⟩ := msg_apart g hg 0
  obtain ⟨m1a, m1c, -, -, -⟩ := msg_apart g hg 1
  have e : exec (finishRegs g) s = exec1 (.pshufb g.cdgh bswap) (exec1 (.pshufb tmp bswap)
      (exec1 (.palignr g.cdgh g.abef 8) (exec1 (.pblendw tmp g.cdgh 0xF0) (exec1 (.movdqa tmp g.abef)
      (exec1 (.pshufd g.cdgh g.cdgh 0xB1) (exec1 (.pshufd g.abef g.abef 0x1B) (exec1 (.paddd g.cdgh g.midCdgh)
      (exec1 (.paddd g.abef g.midAbef) s)))))))) := rfl
  rw [e, hg.mid_abef, hg.mid_cdgh]
  generalize h1 : exec1 (.paddd g.abef (g.msg 0)) s = u₁
  generalize h2 : exec1 (.paddd g.cdgh (g.msg 1)) u₁ = u₂
  generalize h3 : exec1 (.pshufd g.abef g.abef 0x1B) u₂ = u₃
  generalize h4 : exec1 (.pshufd g.cdgh g.cdgh 0xB1) u₃ = u₄
  generalize h5 : exec1 (.movdqa tmp g.abef) u₄ = u₅
  generalize h6 : exec1 (.pblendw tmp g.cdgh 0xF0) u₅ = u₆
  generalize h7 : exec1 (.palignr g.cdgh g.abef 8) u₆ = u₇
  generalize h8 : exec1 (.pshufb tmp bswap) u₇ = u₈
  generalize h9 : exec1 (.pshufb g.cdgh bswap) u₈ = u₉
  obtain ⟨-, -, v1⟩ := h1 ▸ step_frame (.paddd g.abef (g.msg 0)) g.abef rfl s
  obtain ⟨-, -, v2⟩ := h2 ▸ step_frame (.paddd g.cdgh (g.msg 1)) g.cdgh rfl u₁
  obtain ⟨-, -, v3⟩ := h3 ▸ step_frame (.pshufd g.abef g.abef 0x1B) g.abef rfl u₂
  obtain ⟨-, -, v4⟩ := h4 ▸ step_frame (.pshufd g.cdgh g.cdgh 0xB1) g.cdgh rfl u₃
  obtain ⟨-, -, v5⟩ := h5 ▸ step_frame (.movdqa tmp g.abef) tmp rfl u₄
  obtain ⟨-, -, v6⟩ := h6 ▸ step_frame (.pblendw tmp g.cdgh 0xF0) tmp rfl u₅
  obtain ⟨-, -, v7⟩ := h7 ▸ step_frame (.palignr g.cdgh g.abef 8) g.cdgh rfl u₆
  obtain ⟨-, -, v8⟩ := h8 ▸ step_frame (.pshufb tmp bswap) tmp rfl u₇
  obtain ⟨-, -, v9⟩ := h9 ▸ step_frame (.pshufb g.cdgh bswap) g.cdgh rfl u₈
  -- The mask register is never written.
  have k7 : u₇.vec bswap = s.vec bswap := by
    rw [v7 _ cb.symm, v6 _ tb.symm, v5 _ tb.symm, v4 _ cb.symm, v3 _ ab.symm, v2 _ cb.symm, v1 _ ab.symm]
  -- Phase 1: the feed-forward packs the final state.
  have p2 : Packed (u₂.vec g.abef) (u₂.vec g.cdgh) (st.zipWith (· + ·) r) := by
    apply packed_add _ _ _ _ _ _ _ _ _ _ hr hs
    · intro l hl
      rw [v2 _ ac, ← h1, lane_paddd _ _ _ l hl]
    · intro l hl
      rw [← h2, lane_paddd _ _ _ l hl, v1 _ ac.symm, v1 _ m1a]
  generalize f : st.zipWith (· + ·) r = F at p2 ⊢
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨c0, c1, c2, c3⟩⟩ := p2
  -- Phase 2: A, B, E, F and G, H, C, D, from the lowest lane up.
  have q3 : Quad (u₃.vec g.abef) F[0] F[1] F[4] F[5] := h3 ▸ quad_pshufd_1B _ _ _ _ _ _ _ ⟨a0, a1, a2, a3⟩
  have q4c : Quad (u₄.vec g.cdgh) F[6] F[7] F[2] F[3] := by
    rw [← h4]
    exact quad_pshufd_B1 _ _ _ _ _ _ _ (quad_keep _ _ (v3 _ ac.symm) _ _ _ _ ⟨c0, c1, c2, c3⟩)
  have q4a : Quad (u₄.vec g.abef) F[0] F[1] F[4] F[5] := quad_keep _ _ (v4 _ ac) _ _ _ _ q3
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
    · rw [pblendw_high _ _ _ 2 (by decide), if_neg (by decide), v5 _ ct]; exact d2
    · rw [pblendw_high _ _ _ 3 (by decide), if_neg (by decide), v5 _ ct]; exact d3
  have q7 : Quad (u₇.vec g.cdgh) F[4] F[5] F[6] F[7] := by
    obtain ⟨_, _, b2, b3⟩ := q4a
    obtain ⟨d0, d1, _, _⟩ := q4c
    rw [← h7]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [palignr8 _ _ _ 0 (by decide), dif_pos (by decide), v6 _ at', v5 _ at']; exact b2
    · rw [palignr8 _ _ _ 1 (by decide), dif_pos (by decide), v6 _ at', v5 _ at']; exact b3
    · rw [palignr8 _ _ _ 2 (by decide), dif_neg (by decide), v6 _ ct, v5 _ ct]; exact d0
    · rw [palignr8 _ _ _ 3 (by decide), dif_neg (by decide), v6 _ ct, v5 _ ct]; exact d1
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
    · rw [rev _ _ k7 0 (by decide), v7 _ ct.symm, b0]
    · rw [rev _ _ k7 1 (by decide), v7 _ ct.symm, b1]
    · rw [rev _ _ k7 2 (by decide), v7 _ ct.symm, b2]
    · rw [rev _ _ k7 3 (by decide), v7 _ ct.symm, b3]
  have k8 : u₈.vec bswap = s.vec bswap := by rw [v8 _ tb.symm, k7]
  have q9 : Quad (u₉.vec g.cdgh) (bswap32 F[4]) (bswap32 F[5]) (bswap32 F[6]) (bswap32 F[7]) := by
    obtain ⟨b0, b1, b2, b3⟩ := q7
    rw [← h9]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [rev _ _ k8 0 (by decide), v8 _ ct, b0]
    · rw [rev _ _ k8 1 (by decide), v8 _ ct, b1]
    · rw [rev _ _ k8 2 (by decide), v8 _ ct, b2]
    · rw [rev _ _ k8 3 (by decide), v8 _ ct, b3]
  exact ⟨quad_keep _ _ (v9 _ ct.symm) _ _ _ _ q8, q9⟩

/-- A pair's two stores write the digest's 32 bytes at the output address plus the displacement, and nothing else. -/
theorem storesAt_spec (g : Lane) (disp : Nat) (t : State) (f : Vector UInt32 8)
    (o : Ordered (t.vec tmp) (t.vec g.cdgh) f) (x : Nat) :
    (exec (storesAt g disp) t).mem x =
      if (t.gpr out).toNat + disp ≤ x ∧ x < (t.gpr out).toNat + disp + 32 then
        (digest f).get! (x - ((t.gpr out).toNat + disp))
      else t.mem x := by
  -- The two stores write 16 bytes each, the lower and upper halves of the digest.
  simp only [storesAt, exec_cons, exec_nil, exec1_movdquStore, store, State.addr]
  have lo := laneByte_reversed _ f 0 (by omega) (by simpa using o.1)
  have hi := laneByte_reversed _ f 4 (by omega) o.2
  by_cases a : (t.gpr out).toNat + (disp + 16) ≤ x ∧ x < (t.gpr out).toNat + (disp + 16) + 16
  · -- The upper half: words 4 to 7.
    rw [if_pos a, if_pos (by omega), hi _ (by omega), digest_get _ _ (by omega)]
    congr 2
    · congr 1; omega
    · congr 3; omega
  · rw [if_neg a]
    by_cases b : (t.gpr out).toNat + disp ≤ x ∧ x < (t.gpr out).toNat + disp + 16
    · -- The lower half: words 0 to 3.
      rw [if_pos b, if_pos (by omega), lo _ (by omega), digest_get _ _ (by omega)]
      congr 2
      congr 1; omega
    · rw [if_neg b, if_neg (by omega)]

/-- The stores keep every register and the flag. -/
theorem storesAt_frame (g : Lane) (disp : Nat) (t : State) :
    (exec (storesAt g disp) t).gpr = t.gpr ∧ (exec (storesAt g disp) t).vec = t.vec ∧
      (exec (storesAt g disp) t).zf = t.zf := by
  -- Stores write only memory.
  simp [storesAt, exec1_movdquStore]

end Ssz.Native.Kernel.ShaNiDual
