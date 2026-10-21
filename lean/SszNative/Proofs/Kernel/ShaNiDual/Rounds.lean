import SszNative.Proofs.Kernel.ShaNiDual.Lane

/-! The interleaved kernel's round groups, for either pair's registers. -/

namespace Ssz.Native.Kernel.ShaNiDual

open Ssz.Native.Asm Ssz.Sha256
open ShaNi (writes VecOnly exec_frame exec_vec Quad Packed rounds2_packed schedule_step Recurs rounds rounds_four
  K P read_table tableWord_k tableWord_pad)

/-- Four rounds of one pair: the low half of the words plus constants, then the high half moved down. -/
theorem fourRounds_spec (g : Lane) (hg : Good g) (s : State) (st : Vector UInt32 8) (k w : Fin 4 → UInt32)
    (hp : Packed (s.vec g.abef) (s.vec g.cdgh) st)
    (hw : Quad (s.vec wk) (k 0 + w 0) (k 1 + w 1) (k 2 + w 2) (k 3 + w 3)) :
    Packed ((exec (fourRounds g) s).vec g.abef) ((exec (fourRounds g) s).vec g.cdgh)
      (round (round (round (round st (k 0) (w 0)) (k 1) (w 1)) (k 2) (w 2)) (k 3) (w 3)) := by
  obtain ⟨w0, w1, w2, w3⟩ := hw
  obtain ⟨ac, aw, -, -, cw, -, -⟩ := state_apart g hg
  -- The first instruction leaves the new ABEF where CDGH was, and the second swaps them back.
  have first := rounds2_packed _ _ _ (k 0) (w 0) (k 1) (w 1) hp
  have second := rounds2_packed _ _ _ (k 2) (w 2) (k 3) (w 3) first
  simp only [wk] at *
  simp [fourRounds, exec1, assign, low, ac, ac.symm, aw, cw, cw.symm, w0, w1]
  simpa [w2, w3] using second

/-- Every instruction of four rounds writes one vector register of the pair or a shared one. -/
theorem fourRounds_touches (g : Lane) : ∀ i ∈ fourRounds g, ∃ d, writes i = some d ∧ Touches g d := by
  -- The round instructions write the state registers, and the shuffle writes the shared word register.
  simp [fourRounds, writes, Touches]

/-- The words plus constants of a group, from a schedule vector and the table. -/
theorem loadWK (g : Lane) (r : Nat) (hr : r < 16) (s : State) (table : TableAt s.mem (s.gpr tbl).toNat)
    (w : Nat → UInt32) (h : ∀ l : Fin 16, l.val < 4 → s.vec (g.msg r) l = w (4 * r + l.val))
    (l : Fin 16) (hl : l.val < 4) :
    (exec [.movdqa wk (g.msg r), .padddMem wk (tableEntry (kShaNi r))] s).vec wk l =
      K (4 * r + l.val) + w (4 * r + l.val) := by
  simp only [exec_cons, exec_nil, exec1, assign, low, hl, if_true]
  -- The constant's address is the table's register plus the group's offset.
  have addr : ({ s with vec := assign s.vec wk (low (s.vec wk) (s.vec (g.msg r))) } : State).addr
      (tableEntry (kShaNi r)) = s.addr ⟨tbl, kShaNi r⟩ := rfl
  rw [addr, read_table s table _ _ (by simp [kShaNi]; omega) (by simp [kShaNi, tableSize]; omega),
    tableWord_k r l hr hl, h l hl, UInt32.add_comm]

/-- The registers of one pair before its group r of the first block: the state after 4r rounds, and the next words. -/
def Ready (g : Lane) (s : State) (st : Vector UInt32 8) (w : Nat → UInt32) (r : Nat) : Prop :=
  Packed (s.vec g.abef) (s.vec g.cdgh) (rounds st K w (4 * r)) ∧
  ∀ j < 4, r + j < 16 → ∀ l : Fin 16, l.val < 4 → s.vec (g.msg (r + j)) l = w (4 * (r + j) + l.val)

/-- A pair's readiness reads only the registers that pair keeps. -/
theorem ready_congr (g : Lane) (s t : State) (st : Vector UInt32 8) (w : Nat → UInt32) (r : Nat)
    (same : ∀ v, Holds g v → t.vec v = s.vec v) (h : Ready g s st w r) : Ready g t st w r := by
  -- The state registers and every schedule vector hold what they held.
  obtain ⟨p, m⟩ := h
  refine ⟨?_, fun j hj hr l hl => ?_⟩
  · rw [same _ (Or.inl rfl), same _ (Or.inr (Or.inl rfl))]
    exact p
  · rw [same _ (Or.inr (Or.inr ⟨_, rfl⟩))]
    exact m j hj hr l hl

/-- A block of one pair's instructions leaves alone every register that pair does not touch. -/
theorem untouched (g : Lane) (body : List Instr) (hb : ∀ i ∈ body, ∃ d, writes i = some d ∧ Touches g d)
    (v : Vreg) (hv : ¬ Touches g v) (s : State) : (exec body s).vec v = s.vec v :=
  exec_vec body (fun i hi => by obtain ⟨d, hd, _⟩ := hb i hi; simp [hd]) v
    (fun i hi e => by obtain ⟨d, hd, ht⟩ := hb i hi; rw [hd] at e; cases e; exact hv ht) s

/-- A block of one pair's instructions keeps memory, the general registers, and the flag. -/
theorem lane_frame (g : Lane) (body : List Instr) (hb : ∀ i ∈ body, ∃ d, writes i = some d ∧ Touches g d)
    (s : State) : (exec body s).gpr = s.gpr ∧ (exec body s).mem = s.mem ∧ (exec body s).zf = s.zf :=
  exec_frame body (fun i hi => by obtain ⟨d, hd, _⟩ := hb i hi; simp [hd]) s

/-- The schedule step of group r writes the group's vector and the temporary only. -/
def stepCode (g : Lane) (r : Nat) : List Instr :=
  [.sha256msg1 (g.msg r) (g.msg (r + 1)), .movdqa tmp (g.msg (r + 3)), .palignr tmp (g.msg (r + 2)) 4,
    .paddd (g.msg r) tmp, .sha256msg2 (g.msg r) (g.msg (r + 3))]

/-- A first-block group: the words plus constants, four rounds, and the schedule step while words remain. -/
theorem firstRounds_split (g : Lane) (r : Nat) :
    firstRounds g r = [.movdqa wk (g.msg r), .padddMem wk (tableEntry (kShaNi r))] ++ fourRounds g ++
      (if r < 12 then stepCode g r else []) := by
  unfold firstRounds stepCode
  split <;> rfl

/-- Every instruction of the schedule step writes the group's vector or the temporary. -/
theorem stepCode_writes (g : Lane) (r : Nat) :
    ∀ i ∈ stepCode g r, writes i = some (g.msg r) ∨ writes i = some tmp := by
  -- Two of the five instructions write the temporary, and three the vector.
  simp [stepCode, writes]

/-- Every instruction of a first-block group writes one of the pair's registers or a shared one. -/
theorem firstRounds_touches (g : Lane) (r : Nat) : ∀ i ∈ firstRounds g r, ∃ d, writes i = some d ∧ Touches g d := by
  intro i hi
  rw [firstRounds_split] at hi
  simp only [List.mem_append] at hi
  rcases hi with (h | h) | h
  · -- The word register's two loads.
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h <;> subst h <;> exact ⟨wk, rfl, Or.inl rfl⟩
  · exact fourRounds_touches g i h
  · -- The schedule step, when there is one.
    split at h
    · rcases stepCode_writes g r i h with e | e
      · exact ⟨_, e, Or.inr (Or.inr (Or.inr (Or.inr ⟨r, rfl⟩)))⟩
      · exact ⟨_, e, Or.inr (Or.inl rfl)⟩
    · simp at h

/-- A block of the schedule step leaves alone every register but the group's vector and the temporary. -/
theorem stepCode_keep (g : Lane) (r : Nat) (v : Vreg) (h1 : v ≠ g.msg r) (h2 : v ≠ tmp) (s : State) :
    (exec (stepCode g r) s).vec v = s.vec v :=
  exec_vec _ (fun i hi => by rcases stepCode_writes g r i hi with e | e <;> simp [e]) v
    (fun i hi e => by rcases stepCode_writes g r i hi with e' | e' <;> rw [e'] at e <;> cases e <;> simp_all) s

/-- One first-block group of one pair: four rounds, and when words remain to schedule, four more of them. -/
theorem firstRounds_spec (g : Lane) (hg : Good g) (r : Nat) (hr : r < 16) (s : State) (st : Vector UInt32 8)
    (w : Nat → UInt32) (table : TableAt s.mem (s.gpr tbl).toNat) (rec : Recurs w) (h : Ready g s st w r) :
    Ready g (exec (firstRounds g r) s) st w (r + 1) := by
  obtain ⟨hp, hm⟩ := h
  obtain ⟨_, aw, at', _, cw, ct, _⟩ := state_apart g hg
  have msgVal := hg.msg_val
  rw [firstRounds_split, exec_append, exec_append]
  generalize e1 : exec [.movdqa wk (g.msg r), .padddMem wk (tableEntry (kShaNi r))] s = s₁
  generalize e2 : exec (fourRounds g) s₁ = s₂
  -- Phase 1: the words plus constants, with every other register untouched.
  have v1 : ∀ v, v ≠ wk → s₁.vec v = s.vec v := fun v hv => by
    rw [← e1]
    exact exec_vec _ (by simp [VecOnly, writes]) v (by simp [writes]; exact fun e => hv e.symm) s
  have k1 := fun l hl => (e1 ▸ loadWK g r hr s table w (by simpa using hm 0 (by omega) (by omega)) l hl)
  -- Phase 2: four rounds.
  have p2 : Packed (s₂.vec g.abef) (s₂.vec g.cdgh) (rounds st K w (4 * (r + 1))) := by
    rw [rounds_four, ← e2]
    apply fourRounds_spec g hg s₁ _ (fun i => K (4 * r + i.val)) (fun i => w (4 * r + i.val))
    · rw [v1 _ aw, v1 _ cw]
      exact hp
    · exact ⟨k1 0 (by decide), k1 1 (by decide), k1 2 (by decide), k1 3 (by decide)⟩
  -- The schedule vectors are untouched by the first two phases.
  have v2 : ∀ q, s₂.vec (g.msg q) = s.vec (g.msg q) := fun q => by
    obtain ⟨ma, mc, mw, _, _⟩ := msg_apart g hg q
    rw [← e2, exec_vec _ (by simp [VecOnly, fourRounds, writes]) _ (by
      simp only [fourRounds, List.mem_cons, List.not_mem_nil, or_false]
      rintro i (h | h | h) <;> subst h <;> simp [writes] <;> intro e <;> simp_all), v1 _ mw]
  have w2 : ∀ j < 4, r + j < 16 → ∀ l : Fin 16, l.val < 4 → s₂.vec (g.msg (r + j)) l = w (4 * (r + j) + l.val) :=
    fun j hj hr' l hl => by rw [v2]; exact hm j hj hr' l hl
  refine ⟨?_, ?_⟩
  · -- The schedule step writes neither state register.
    split
    · rw [stepCode_keep g r _ (msg_apart g hg r).1.symm at', stepCode_keep g r _ (msg_apart g hg r).2.1.symm ct]
      exact p2
    · exact p2
  · intro j hj hrj l hl
    split
    · rename_i small
      by_cases last : j = 3
      · -- The vector sixteen words ahead is the one the step rewrote.
        subst last
        have same : g.msg (r + 1 + 3) = g.msg r := Fin.ext (by rw [msgVal, msgVal r]; omega)
        rw [same]
        have := schedule_step (g.msg r) (g.msg (r + 1)) (g.msg (r + 2)) (g.msg (r + 3))
          (msg_ne g hg _ _ (by omega)) (msg_ne g hg _ _ (by omega)) (msg_apart g hg r).2.2.2.1
          (msg_apart g hg _).2.2.2.1 (msg_apart g hg _).2.2.2.1 s₂
        simp only at this
        obtain ⟨l0, l1, l2, l3⟩ := this
        -- The words the step reads, from the four vectors.
        have F : ∀ j l (hj : j < 4) (hl : l < 4) n, n = 4 * (r + j) + l →
            s₂.vec (g.msg (r + j)) ⟨l, by omega⟩ = w n := fun j l hj hl n hn => by
          rw [hn]; exact w2 j hj (by omega) ⟨l, by omega⟩ hl
        have f00 : s₂.vec (g.msg r) 0 = w (4 * r) := F 0 0 (by omega) (by omega) _ (by omega)
        have f01 : s₂.vec (g.msg r) 1 = w (4 * r + 1) := F 0 1 (by omega) (by omega) _ (by omega)
        have f02 : s₂.vec (g.msg r) 2 = w (4 * r + 2) := F 0 2 (by omega) (by omega) _ (by omega)
        have f03 : s₂.vec (g.msg r) 3 = w (4 * r + 3) := F 0 3 (by omega) (by omega) _ (by omega)
        have f10 : s₂.vec (g.msg (r + 1)) 0 = w (4 * r + 4) := F 1 0 (by omega) (by omega) _ (by omega)
        have f21 : s₂.vec (g.msg (r + 2)) 1 = w (4 * r + 9) := F 2 1 (by omega) (by omega) _ (by omega)
        have f22 : s₂.vec (g.msg (r + 2)) 2 = w (4 * r + 10) := F 2 2 (by omega) (by omega) _ (by omega)
        have f23 : s₂.vec (g.msg (r + 2)) 3 = w (4 * r + 11) := F 2 3 (by omega) (by omega) _ (by omega)
        have f30 : s₂.vec (g.msg (r + 3)) 0 = w (4 * r + 12) := F 3 0 (by omega) (by omega) _ (by omega)
        have f32 : s₂.vec (g.msg (r + 3)) 2 = w (4 * r + 14) := F 3 2 (by omega) (by omega) _ (by omega)
        have f33 : s₂.vec (g.msg (r + 3)) 3 = w (4 * r + 15) := F 3 3 (by omega) (by omega) _ (by omega)
        simp only [f00, f01, f02, f03, f10, f21, f22, f23, f30, f32, f33] at l0 l1 l2 l3
        -- The recurrence at the four new positions.
        have r16 := rec (4 * r + 16) (by omega) (by omega)
        have r17 := rec (4 * r + 17) (by omega) (by omega)
        have r18 := rec (4 * r + 18) (by omega) (by omega)
        have r19 := rec (4 * r + 19) (by omega) (by omega)
        simp only [show 4 * r + 16 - 16 = 4 * r by omega, show 4 * r + 16 - 15 = 4 * r + 1 by omega,
          show 4 * r + 16 - 7 = 4 * r + 9 by omega, show 4 * r + 16 - 2 = 4 * r + 14 by omega] at r16
        simp only [show 4 * r + 17 - 16 = 4 * r + 1 by omega, show 4 * r + 17 - 15 = 4 * r + 2 by omega,
          show 4 * r + 17 - 7 = 4 * r + 10 by omega, show 4 * r + 17 - 2 = 4 * r + 15 by omega] at r17
        simp only [show 4 * r + 18 - 16 = 4 * r + 2 by omega, show 4 * r + 18 - 15 = 4 * r + 3 by omega,
          show 4 * r + 18 - 7 = 4 * r + 11 by omega, show 4 * r + 18 - 2 = 4 * r + 16 by omega] at r18
        simp only [show 4 * r + 19 - 16 = 4 * r + 3 by omega, show 4 * r + 19 - 15 = 4 * r + 4 by omega,
          show 4 * r + 19 - 7 = 4 * r + 12 by omega, show 4 * r + 19 - 2 = 4 * r + 17 by omega] at r19
        rw [← r16] at l0
        rw [← r17] at l1
        rw [← r16, ← r18] at l2
        rw [← r17, ← r19] at l3
        have e : exec (stepCode g r) s₂ = exec [.sha256msg1 (g.msg r) (g.msg (r + 1)), .movdqa tmp (g.msg (r + 3)),
          .palignr tmp (g.msg (r + 2)) 4, .paddd (g.msg r) tmp, .sha256msg2 (g.msg r) (g.msg (r + 3))] s₂ := rfl
        rw [e]
        rcases l with ⟨_ | _ | _ | _ | l, hl'⟩
        · rw [show 4 * (r + 1 + 3) + 0 = 4 * r + 16 by omega]; exact l0
        · rw [show 4 * (r + 1 + 3) + (0 + 1) = 4 * r + 17 by omega]; exact l1
        · rw [show 4 * (r + 1 + 3) + (0 + 1 + 1) = 4 * r + 18 by omega]; exact l2
        · rw [show 4 * (r + 1 + 3) + (0 + 1 + 1 + 1) = 4 * r + 19 by omega]; exact l3
        · simp at hl
          omega
      · -- The other vectors are untouched since the group started.
        rw [stepCode_keep g r _ (msg_ne g hg _ _ (by omega)) (msg_apart g hg _).2.2.2.1,
          show r + 1 + j = r + (j + 1) by omega]
        exact w2 (j + 1) (by omega) (by omega) l hl
    · rw [exec_nil, show r + 1 + j = r + (j + 1) by omega]
      exact w2 (j + 1) (by omega) (by omega) l hl

/-- Every instruction of a padding-block group writes one of the pair's registers or a shared one. -/
theorem paddingRounds_touches (g : Lane) (r : Nat) :
    ∀ i ∈ paddingRounds g r, ∃ d, writes i = some d ∧ Touches g d := by
  -- The table load writes the word register, and the rounds the state registers.
  intro i hi
  simp only [paddingRounds, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h
  · subst h; exact ⟨wk, rfl, Or.inl rfl⟩
  · exact fourRounds_touches g i h

/-- One padding-block group of one pair: four rounds from the precomputed words plus constants. -/
theorem paddingRounds_spec (g : Lane) (hg : Good g) (r : Nat) (hr : r < 16) (s : State) (st : Vector UInt32 8)
    (table : TableAt s.mem (s.gpr tbl).toNat)
    (h : Packed (s.vec g.abef) (s.vec g.cdgh) (rounds st K P (4 * r))) :
    Packed ((exec (paddingRounds g r) s).vec g.abef) ((exec (paddingRounds g r) s).vec g.cdgh)
      (rounds st K P (4 * (r + 1))) := by
  obtain ⟨_, aw, -, -, cw, -, -⟩ := state_apart g hg
  -- The group's four rounds, from four table words.
  rw [rounds_four]
  simp only [paddingRounds, List.cons_append, List.nil_append, exec_cons]
  apply fourRounds_spec g hg _ _ (fun i => K (4 * r + i.val)) (fun i => P (4 * r + i.val))
  · simpa [exec1, assign, low, aw, cw] using h
  · -- Each lane is one table word: the constant plus the padding block's word.
    have lane : ∀ l : Fin 16, l.val < 4 →
        (exec1 (.movdqu wk (tableEntry (padShaNi r))) s).vec wk l = K (4 * r + l.val) + P (4 * r + l.val) := by
      intro l hl
      simp only [exec1, assign, low, hl, if_true]
      rw [show s.addr (tableEntry (padShaNi r)) = s.addr ⟨tbl, padShaNi r⟩ from rfl,
        read_table s table _ _ (by simp [padShaNi]; omega) (by simp [padShaNi, tableSize]; omega),
        tableWord_pad r l hr hl, paddingWK, Nat.mod_eq_of_lt (by omega)]
    exact ⟨lane 0 (by decide), lane 1 (by decide), lane 2 (by decide), lane 3 (by decide)⟩

end Ssz.Native.Kernel.ShaNiDual
