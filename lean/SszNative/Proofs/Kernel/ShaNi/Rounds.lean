import SszNative.Proofs.Kernel.ShaNi.Basic

/-! The SHA-NI kernel's round groups: four rounds per group, and the schedule kept sixteen words ahead. -/

namespace Ssz.Native.Kernel.ShaNi

open Ssz.Native.Asm Ssz.Sha256

/-- Round constant i. -/
abbrev K (i : Nat) : UInt32 := roundConstants[i]!

/-- Two rounds of the SHA instruction are two rounds of the specification, its word plus constant split back apart. -/
theorem rounds2_packed (abef cdgh : Lanes) (st : Vector UInt32 8) (k₀ w₀ k₁ w₁ : UInt32)
    (h : Packed abef cdgh st) :
    Packed (rounds2 cdgh abef (k₀ + w₀) (k₁ + w₁)) abef (round (round st k₀ w₀) k₁ w₁) := by
  obtain ⟨⟨a0, a1, a2, a3⟩, ⟨c0, c1, c2, c3⟩⟩ := h
  simp only [Packed, Quad, rounds2, round, a0, a1, a2, a3, c0, c1, c2, c3]
  simp
  -- Each new word is the same sum, added in another order.
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ac_rfl

/-- Four rounds: the low half of the words plus constants, then the high half moved down. -/
theorem fourRounds_spec (s : State) (st : Vector UInt32 8) (k w : Fin 4 → UInt32)
    (hp : Packed (s.vec abef) (s.vec cdgh) st)
    (hw : Quad (s.vec wk) (k 0 + w 0) (k 1 + w 1) (k 2 + w 2) (k 3 + w 3)) :
    Packed ((exec fourRounds s).vec abef) ((exec fourRounds s).vec cdgh)
      (round (round (round (round st (k 0) (w 0)) (k 1) (w 1)) (k 2) (w 2)) (k 3) (w 3)) := by
  obtain ⟨w0, w1, w2, w3⟩ := hw
  -- The first instruction leaves the new ABEF where CDGH was, and the second swaps them back.
  have first := rounds2_packed _ _ _ (k 0) (w 0) (k 1) (w 1) hp
  have second := rounds2_packed _ _ _ (k 2) (w 2) (k 3) (w 3) first
  simp only [abef, cdgh, wk] at *
  simp [fourRounds, exec1, assign, low, abef, cdgh, wk, w0, w1]
  simpa [w2, w3] using second

/-- Four rounds only write the state and the words plus constants. -/
theorem fourRounds_vecOnly : VecOnly fourRounds := by
  simp [VecOnly, fourRounds, writes]

/-- The words plus constants of a group, from a schedule vector and the table. -/
theorem loadWK (r : Nat) (hr : r < 16) (s : State) (table : TableAt s.mem (s.gpr tbl).toNat)
    (w : Nat → UInt32) (h : ∀ l : Fin 16, l.val < 4 → s.vec (msg r) l = w (4 * r + l.val))
    (l : Fin 16) (hl : l.val < 4) :
    (exec [.movdqa wk (msg r), .padddMem wk (tableEntry (kShaNi r))] s).vec wk l = K (4 * r + l.val) + w (4 * r + l.val) := by
  simp only [exec_cons, exec_nil, exec1, assign, low, hl, if_true]
  -- The constant's address is the table's register plus the group's offset.
  have addr : ({ s with vec := assign s.vec wk (low (s.vec wk) (s.vec (msg r))) } : State).addr (tableEntry (kShaNi r)) =
      s.addr ⟨tbl, kShaNi r⟩ := rfl
  rw [addr, read_table s table _ _ (by simp [kShaNi]; omega) (by simp [kShaNi, tableSize]; omega),
    tableWord_k r l hr hl, h l hl, UInt32.add_comm]

set_option linter.unusedSimpArgs false in
/-- Four schedule words, sixteen ahead of the vector they overwrite. -/
theorem schedule_step (a b c d : Vreg) (ac : a ≠ c) (ad : a ≠ d) (tableEntry : a ≠ tmp) (ct : c ≠ tmp) (dt : d ≠ tmp)
    (s : State) :
    let s' := exec [.sha256msg1 a b, .movdqa tmp d, .palignr tmp c 4, .paddd a tmp, .sha256msg2 a d] s
    let A := s.vec a
    let B := s.vec b
    let C := s.vec c
    let D := s.vec d
    s'.vec a 0 = A 0 + sigma0 (A 1) + C 1 + sigma1 (D 2) ∧
    s'.vec a 1 = A 1 + sigma0 (A 2) + C 2 + sigma1 (D 3) ∧
    s'.vec a 2 = A 2 + sigma0 (A 3) + C 3 + sigma1 (A 0 + sigma0 (A 1) + C 1 + sigma1 (D 2)) ∧
    s'.vec a 3 = A 3 + sigma0 (B 0) + D 0 + sigma1 (A 1 + sigma0 (A 2) + C 2 + sigma1 (D 3)) := by
  intro s' A B C D
  -- The rotated window: words 9 to 12 of the sixteen, from the third and fourth vectors.
  generalize h3 : exec1 (.palignr tmp c 4) (exec1 (.movdqa tmp d) (exec1 (.sha256msg1 a b) s)) = s₃
  have w3 : ∀ l : Fin 16, (hl : l.val < 4) →
      s₃.vec tmp l = if h : l.val < 3 then C ⟨l.val + 1, by omega⟩ else D 0 := by
    intro l hl
    rw [← h3, palignr4 _ _ _ l hl]
    simp [exec1, assign, low, ac, ad, tableEntry, ct, dt, ac.symm, ad.symm, tableEntry.symm, ct.symm, dt.symm, C, D]
  -- The first vector after the first half of the step.
  have a3 : ∀ l : Fin 16, l.val < 4 → s₃.vec a l = (exec1 (.sha256msg1 a b) s).vec a l := by
    intro l _
    rw [← h3]
    simp [exec1, assign, ac, ad, tableEntry, ct, dt, ac.symm, ad.symm, tableEntry.symm, ct.symm, dt.symm]
  have d3 : s₃.vec d = D := by
    rw [← h3]
    simp [exec1, assign, ac, ad, tableEntry, ct, dt, ac.symm, ad.symm, tableEntry.symm, ct.symm, dt.symm, D]
  have e : s' = exec1 (.sha256msg2 a d) (exec1 (.paddd a tmp) s₃) := by
    simp only [s', exec_cons, exec_nil, h3]
  rw [e]
  have t0 := w3 0 (by decide)
  have t1 := w3 1 (by decide)
  have t2 := w3 2 (by decide)
  have t3 := w3 3 (by decide)
  have m0 := a3 0 (by decide)
  have m1 := a3 1 (by decide)
  have m2 := a3 2 (by decide)
  have m3 := a3 3 (by decide)
  simp [exec1, assign, low, A, B] at t0 t1 t2 t3 m0 m1 m2 m3
  -- The second half adds the window and the second-order terms.
  simp [exec1, assign, low, t0, t1, t2, t3, m0, m1, m2, m3, d3, ad.symm, A, B, C, D]

/-- Whether a function of indices satisfies the schedule's four-term recurrence. -/
def Recurs (w : Nat → UInt32) : Prop :=
  ∀ c, 16 ≤ c → c < 64 → w c = w (c - 16) + sigma0 (w (c - 15)) + w (c - 7) + sigma1 (w (c - 2))

/-- The registers before group r of the first block: the state after 4r rounds, and the next sixteen words. -/
def Ready (s : State) (st : Vector UInt32 8) (w : Nat → UInt32) (r : Nat) : Prop :=
  Packed (s.vec abef) (s.vec cdgh) (rounds st K w (4 * r)) ∧
  ∀ j < 4, r + j < 16 → ∀ l : Fin 16, l.val < 4 → s.vec (msg (r + j)) l = w (4 * (r + j) + l.val)

/-- Four more rounds of a run. -/
theorem rounds_four (st : Vector UInt32 8) (k w : Nat → UInt32) (r : Nat) :
    rounds st k w (4 * (r + 1)) =
      round (round (round (round (rounds st k w (4 * r)) (k (4 * r)) (w (4 * r))) (k (4 * r + 1)) (w (4 * r + 1)))
        (k (4 * r + 2)) (w (4 * r + 2))) (k (4 * r + 3)) (w (4 * r + 3)) := by
  -- Four more rounds unfold one at a time.
  rw [show 4 * (r + 1) = 4 * r + 3 + 1 by omega]
  rfl

/-- Schedule vector r's register number. -/
theorem msg_val (r : Nat) : (msg r).val = 3 + r % 4 := rfl

/-- A first-block group writes only vector registers. -/
theorem firstRounds_vecOnly (r : Nat) : VecOnly (firstRounds r) := by
  -- Every instruction of a group writes a vector register.
  unfold firstRounds
  split <;> simp [VecOnly, fourRounds, writes]

/-- A first-block group writes only the registers below 8. -/
theorem firstRounds_writes (r : Nat) (v : Vreg) (hv : 8 ≤ v.val) : ∀ i ∈ firstRounds r, writes i ≠ some v := by
  -- A group writes its schedule vector, the round registers, and the temporary, all below 8.
  have : msg r ≠ v := fun e => by have := msg_val r; rw [e] at this; omega
  unfold firstRounds
  split <;> simp [fourRounds, writes, Fin.ext_iff, tmp, wk, abef, cdgh, msg_val] <;> omega

/-- One first-block group: four rounds, and when words remain to schedule, four more of them. -/
theorem firstRounds_spec (r : Nat) (hr : r < 16) (s : State) (st : Vector UInt32 8) (w : Nat → UInt32)
    (table : TableAt s.mem (s.gpr tbl).toNat) (rec : Recurs w) (h : Ready s st w r) :
    Ready (exec (firstRounds r) s) st w (r + 1) := by
  obtain ⟨hp, hm⟩ := h
  -- Registers of the group's four schedule vectors.
  have ne : ∀ j, j < 4 → (msg (r + j)).val = 3 + (r + j) % 4 := fun _ _ => rfl
  have split : firstRounds r = [.movdqa wk (msg r), .padddMem wk (tableEntry (kShaNi r))] ++ fourRounds ++
      (if r < 12 then [.sha256msg1 (msg r) (msg (r + 1)), .movdqa tmp (msg (r + 3)), .palignr tmp (msg (r + 2)) 4,
        .paddd (msg r) tmp, .sha256msg2 (msg r) (msg (r + 3))] else []) := by
    unfold firstRounds
    split <;> rfl
  rw [split, exec_append, exec_append]
  generalize e1 : exec [.movdqa wk (msg r), .padddMem wk (tableEntry (kShaNi r))] s = s₁
  generalize e2 : exec fourRounds s₁ = s₂
  -- Phase 1: the words plus constants, with every other register untouched.
  have v1 : ∀ v, v ≠ wk → s₁.vec v = s.vec v := fun v hv => by
    rw [← e1]
    exact exec_vec _ (by simp [VecOnly, writes]) v (by simp [writes]; exact fun e => hv e.symm) s
  have k1 := fun l hl => (e1 ▸ loadWK r hr s table w (by simpa using hm 0 (by omega) (by omega)) l hl)
  -- Phase 2: four rounds.
  have p2 : Packed (s₂.vec abef) (s₂.vec cdgh) (rounds st K w (4 * (r + 1))) := by
    rw [rounds_four, ← e2]
    apply fourRounds_spec s₁ _ (fun i => K (4 * r + i.val)) (fun i => w (4 * r + i.val))
    · rw [v1 abef (by decide), v1 cdgh (by decide)]
      exact hp
    · exact ⟨k1 0 (by decide), k1 1 (by decide), k1 2 (by decide), k1 3 (by decide)⟩
  have v2 : ∀ v, 3 ≤ v.val → s₂.vec v = s.vec v := fun v hv => by
    rw [← e2, exec_vec _ fourRounds_vecOnly v (by
      simp [fourRounds, writes, Fin.ext_iff, abef, cdgh, wk]; omega), v1 v (by
      intro e; subst e; simp [wk] at hv)]
  have w2 : ∀ j < 4, r + j < 16 → ∀ l : Fin 16, l.val < 4 → s₂.vec (msg (r + j)) l = w (4 * (r + j) + l.val) :=
    fun j hj hr' l hl => by rw [v2 _ (by rw [ne j hj]; omega)]; exact hm j hj hr' l hl
  refine ⟨?_, ?_⟩
  · -- The schedule step writes neither state register.
    split
    · rw [exec_vec _ (by simp [VecOnly, writes]) abef (by
        simp [writes, Fin.ext_iff, tmp, abef, msg_val]; omega),
        exec_vec _ (by simp [VecOnly, writes]) cdgh (by
        simp [writes, Fin.ext_iff, tmp, cdgh, msg_val]; omega)]
      exact p2
    · exact p2
  · intro j hj hrj l hl
    split
    · rename_i small
      by_cases last : j = 3
      · -- The vector sixteen words ahead is the one the step rewrote.
        subst last
        have same : msg (r + 1 + 3) = msg r := Fin.ext (by simp [msg_val]; omega)
        rw [same]
        have := schedule_step (msg r) (msg (r + 1)) (msg (r + 2)) (msg (r + 3))
          (by simp [Fin.ext_iff, msg_val]; omega) (by simp [Fin.ext_iff, msg_val]; omega)
          (by simp [Fin.ext_iff, msg_val, tmp]; omega) (by simp [Fin.ext_iff, msg_val, tmp]; omega)
          (by simp [Fin.ext_iff, msg_val, tmp]; omega) s₂
        simp only at this
        obtain ⟨l0, l1, l2, l3⟩ := this
        -- The words the step reads, from the four vectors.
        have F : ∀ j l (hj : j < 4) (hl : l < 4) n, n = 4 * (r + j) + l →
            s₂.vec (msg (r + j)) ⟨l, by omega⟩ = w n := fun j l hj hl n hn => by
          rw [hn]; exact w2 j hj (by omega) ⟨l, by omega⟩ hl
        have f00 : s₂.vec (msg r) 0 = w (4 * r) := F 0 0 (by omega) (by omega) _ (by omega)
        have f01 : s₂.vec (msg r) 1 = w (4 * r + 1) := F 0 1 (by omega) (by omega) _ (by omega)
        have f02 : s₂.vec (msg r) 2 = w (4 * r + 2) := F 0 2 (by omega) (by omega) _ (by omega)
        have f03 : s₂.vec (msg r) 3 = w (4 * r + 3) := F 0 3 (by omega) (by omega) _ (by omega)
        have f10 : s₂.vec (msg (r + 1)) 0 = w (4 * r + 4) := F 1 0 (by omega) (by omega) _ (by omega)
        have f21 : s₂.vec (msg (r + 2)) 1 = w (4 * r + 9) := F 2 1 (by omega) (by omega) _ (by omega)
        have f22 : s₂.vec (msg (r + 2)) 2 = w (4 * r + 10) := F 2 2 (by omega) (by omega) _ (by omega)
        have f23 : s₂.vec (msg (r + 2)) 3 = w (4 * r + 11) := F 2 3 (by omega) (by omega) _ (by omega)
        have f30 : s₂.vec (msg (r + 3)) 0 = w (4 * r + 12) := F 3 0 (by omega) (by omega) _ (by omega)
        have f32 : s₂.vec (msg (r + 3)) 2 = w (4 * r + 14) := F 3 2 (by omega) (by omega) _ (by omega)
        have f33 : s₂.vec (msg (r + 3)) 3 = w (4 * r + 15) := F 3 3 (by omega) (by omega) _ (by omega)
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
        rcases l with ⟨_ | _ | _ | _ | l, hl'⟩
        · rw [show 4 * (r + 1 + 3) + 0 = 4 * r + 16 by omega]; exact l0
        · rw [show 4 * (r + 1 + 3) + (0 + 1) = 4 * r + 17 by omega]; exact l1
        · rw [show 4 * (r + 1 + 3) + (0 + 1 + 1) = 4 * r + 18 by omega]; exact l2
        · rw [show 4 * (r + 1 + 3) + (0 + 1 + 1 + 1) = 4 * r + 19 by omega]; exact l3
        · simp at hl
          omega
      · -- The other vectors are untouched since the group started.
        rw [exec_vec _ (by simp [VecOnly, writes]) _ (by
          simp [writes, Fin.ext_iff, tmp, msg_val]; omega), show r + 1 + j = r + (j + 1) by omega]
        exact w2 (j + 1) (by omega) (by omega) l hl
    · rw [show r + 1 + j = r + (j + 1) by omega]
      exact w2 (j + 1) (by omega) (by omega) l hl

/-- A block made of groups is register-only when every group is. -/
theorem vecOnly_flatMap (f : Nat → List Instr) (h : ∀ r, VecOnly (f r)) (m : Nat) :
    VecOnly ((List.range m).flatMap f) := by
  -- Each instruction comes from some group.
  intro i hi
  obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp hi
  exact h r i hr

/-- A block made of groups leaves a register alone when every group does. -/
theorem writes_flatMap (f : Nat → List Instr) (v : Vreg) (h : ∀ r, ∀ i ∈ f r, writes i ≠ some v) (m : Nat) :
    ∀ i ∈ (List.range m).flatMap f, writes i ≠ some v := by
  -- Each instruction comes from some group.
  intro i hi
  obtain ⟨r, _, hr⟩ := List.mem_flatMap.mp hi
  exact h r i hr

/-- Running the first groups in order. -/
theorem exec_range_succ (f : Nat → List Instr) (m : Nat) (s : State) :
    exec ((List.range (m + 1)).flatMap f) s = exec (f m) (exec ((List.range m).flatMap f) s) := by
  -- The range up to m + 1 is the range up to m, then m.
  rw [List.range_succ, List.flatMap_append, exec_append]
  simp

/-- The sixteen first-block groups: sixty-four rounds over the message's schedule. -/
theorem firstAll (s : State) (st : Vector UInt32 8) (w : Nat → UInt32) (table : TableAt s.mem (s.gpr tbl).toNat)
    (rec : Recurs w) (h : Ready s st w 0) :
    Packed ((exec ((List.range 16).flatMap firstRounds) s).vec abef)
      ((exec ((List.range 16).flatMap firstRounds) s).vec cdgh) (rounds st K w 64) := by
  -- Induction on the groups run so far.
  have all : ∀ m ≤ 16, Ready (exec ((List.range m).flatMap firstRounds) s) st w m := by
    intro m hm
    induction m with
    | zero => exact h
    | succ m ih =>
      rw [exec_range_succ]
      -- The table is where it was, since the groups never touch memory or the general registers.
      obtain ⟨g, mem, _⟩ := exec_frame _ (vecOnly_flatMap _ firstRounds_vecOnly m) s
      exact firstRounds_spec m (by omega) _ st w (by rw [g, mem]; exact table) rec (ih (by omega))
  exact (all 16 (by omega)).1

/-- Padding-block word i. -/
abbrev P (i : Nat) : UInt32 := (schedule paddingBlock 0)[i]!

/-- A padding-block group writes only vector registers. -/
theorem paddingRounds_vecOnly (r : Nat) : VecOnly (paddingRounds r) := by
  -- Every instruction of a group writes a vector register.
  simp [VecOnly, paddingRounds, fourRounds, writes]

/-- A padding-block group writes only the registers below 3. -/
theorem paddingRounds_writes (r : Nat) (v : Vreg) (hv : 3 ≤ v.val) : ∀ i ∈ paddingRounds r, writes i ≠ some v := by
  -- A group writes only the words plus constants and the two state registers.
  simp [paddingRounds, fourRounds, writes, Fin.ext_iff, wk, abef, cdgh]
  omega

/-- One padding-block group: four rounds from the precomputed words plus constants. -/
theorem paddingRounds_spec (r : Nat) (hr : r < 16) (s : State) (st : Vector UInt32 8)
    (table : TableAt s.mem (s.gpr tbl).toNat) (h : Packed (s.vec abef) (s.vec cdgh) (rounds st K P (4 * r))) :
    Packed ((exec (paddingRounds r) s).vec abef) ((exec (paddingRounds r) s).vec cdgh) (rounds st K P (4 * (r + 1))) := by
  -- The group's four rounds, from four table words.
  rw [rounds_four]
  simp only [paddingRounds, List.cons_append, List.nil_append, exec_cons]
  apply fourRounds_spec _ _ (fun i => K (4 * r + i.val)) (fun i => P (4 * r + i.val))
  · simpa [exec1, assign, low, abef, cdgh, wk] using h
  · -- Each lane is one table word: the constant plus the padding block's word.
    have lane : ∀ l : Fin 16, l.val < 4 →
        (exec1 (.movdqu wk (tableEntry (padShaNi r))) s).vec wk l = K (4 * r + l.val) + P (4 * r + l.val) := by
      intro l hl
      simp only [exec1, assign, low, hl, if_true]
      rw [show s.addr (tableEntry (padShaNi r)) = s.addr ⟨tbl, padShaNi r⟩ from rfl,
        read_table s table _ _ (by simp [padShaNi]; omega) (by simp [padShaNi, tableSize]; omega),
        tableWord_pad r l hr hl, paddingWK, Nat.mod_eq_of_lt (by omega)]
    exact ⟨lane 0 (by decide), lane 1 (by decide), lane 2 (by decide), lane 3 (by decide)⟩

/-- The sixteen padding-block groups: sixty-four rounds over the padding block's schedule. -/
theorem paddingAll (s : State) (st : Vector UInt32 8) (table : TableAt s.mem (s.gpr tbl).toNat)
    (h : Packed (s.vec abef) (s.vec cdgh) st) :
    Packed ((exec ((List.range 16).flatMap paddingRounds) s).vec abef)
      ((exec ((List.range 16).flatMap paddingRounds) s).vec cdgh) (rounds st K P 64) := by
  have all : ∀ m ≤ 16, Packed ((exec ((List.range m).flatMap paddingRounds) s).vec abef)
      -- Induction on the groups run so far.
      ((exec ((List.range m).flatMap paddingRounds) s).vec cdgh) (rounds st K P (4 * m)) := by
    intro m hm
    induction m with
    | zero => exact h
    | succ m ih =>
      rw [exec_range_succ]
      obtain ⟨g, mem, _⟩ := exec_frame _ (vecOnly_flatMap _ paddingRounds_vecOnly m) s
      exact paddingRounds_spec m (by omega) _ st (by rw [g, mem]; exact table) (ih (by omega))
  exact all 16 (by omega)

end Ssz.Native.Kernel.ShaNi
