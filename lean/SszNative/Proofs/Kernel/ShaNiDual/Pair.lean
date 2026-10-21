import SszNative.Proofs.Kernel.ShaNiDual.Rounds

/-! One pair's message and initial state loaded into its registers, and its first feed-forward. -/

namespace Ssz.Native.Kernel.ShaNiDual

open Ssz.Native.Asm Ssz.Sha256
open ShaNi (writes VecOnly exec_frame exec_vec step_frame Quad Packed Wm MaskReady load_lanes pairMessage_get read_table
  tableWord_iv quad_of_eq packed_add lane_padddMem lane_movdqa)

/-- Where schedule vector r of a pair reads from: its left node for the first two, its right node for the others. -/
def sourceAt (leftDisp rightDisp r : Nat) : Mem :=
  if r < 2 then ⟨left, leftDisp + 16 * r⟩ else ⟨right, rightDisp + 16 * (r - 2)⟩

/-- The pair a register set reads: its left node and its right node, each a displacement from its register. -/
def messageAt (s : State) (leftDisp rightDisp : Nat) : ByteArray :=
  pairMessage s.mem ((s.gpr left).toNat + leftDisp) ((s.gpr right).toNat + rightDisp)

/-- The big-endian word a load reads is the pair's schedule word. -/
theorem source_word (s : State) (leftDisp rightDisp r l : Nat) (hr : r < 4) (hl : l < 4) :
    (s.mem (s.addr (sourceAt leftDisp rightDisp r) + 4 * l)).toUInt32 <<< 24 |||
        (s.mem (s.addr (sourceAt leftDisp rightDisp r) + 4 * l + 1)).toUInt32 <<< 16 |||
        (s.mem (s.addr (sourceAt leftDisp rightDisp r) + 4 * l + 2)).toUInt32 <<< 8 |||
        (s.mem (s.addr (sourceAt leftDisp rightDisp r) + 4 * l + 3)).toUInt32 =
      Wm (messageAt s leftDisp rightDisp) (4 * r + l) := by
  -- A schedule word below 16 is the message's big-endian word at four times its index.
  simp only [Wm, messageAt]
  rw [getElem!_pos _ _ (by omega), schedule_input _ _ _ (by omega), wordAt]
  simp only [Nat.zero_add]
  rw [pairMessage_get _ _ _ _ (by omega), pairMessage_get _ _ _ _ (by omega), pairMessage_get _ _ _ _ (by omega),
    pairMessage_get _ _ _ _ (by omega)]
  unfold sourceAt
  -- The first two vectors read the left node, the last two the right node.
  split
  · simp only [State.addr]
    simp (disch := omega) only [if_pos]
    rw [show (s.gpr left).toNat + (leftDisp + 16 * r) + 4 * l = (s.gpr left).toNat + leftDisp + 4 * (4 * r + l) by
      omega]
    simp only [Nat.add_assoc]
  · simp only [State.addr]
    simp (disch := omega) only [if_neg]
    rw [show 4 * (4 * r + l) - 32 = 16 * (r - 2) + 4 * l by omega,
      show 4 * (4 * r + l) + 1 - 32 = 16 * (r - 2) + 4 * l + 1 by omega,
      show 4 * (4 * r + l) + 2 - 32 = 16 * (r - 2) + 4 * l + 2 by omega,
      show 4 * (4 * r + l) + 3 - 32 = 16 * (r - 2) + 4 * l + 3 by omega]
    simp only [Nat.add_assoc]

/-- The load of one schedule vector. -/
def loadBlock (g : Lane) (leftDisp rightDisp r : Nat) : List Instr :=
  [.movdqu (g.msg r) (sourceAt leftDisp rightDisp r), .pshufb (g.msg r) bswap]

/-- The initial state's loads. -/
def ivLoads (g : Lane) : List Instr := [.movdqu g.abef (tableEntry ivAbef), .movdqu g.cdgh (tableEntry ivCdgh)]

/-- A pair's loads, block by block. -/
theorem loadCode_blocks (g : Lane) (leftDisp rightDisp : Nat) :
    loadCode g leftDisp rightDisp = loadBlock g leftDisp rightDisp 0 ++ loadBlock g leftDisp rightDisp 1 ++
      loadBlock g leftDisp rightDisp 2 ++ loadBlock g leftDisp rightDisp 3 ++ ivLoads g := rfl

/-- Every instruction of a pair's loads writes one of its registers. -/
theorem loadCode_touches (g : Lane) (leftDisp rightDisp : Nat) :
    ∀ i ∈ loadCode g leftDisp rightDisp, ∃ d, writes i = some d ∧ Touches g d := by
  -- Each load writes a schedule vector or a state register.
  rw [loadCode_blocks]
  simp only [loadBlock, ivLoads, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  intro i hi
  rcases hi with ((((h | h) | h | h) | h | h) | h | h) | h | h <;> subst h <;> refine ⟨_, rfl, ?_⟩ <;>
    unfold Touches <;>
    first
      | exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, rfl⟩)))
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

/-- One load, from any machine whose memory and general registers are the original's. -/
theorem loadBlock_lane (g : Lane) (hg : Good g) (s t : State) (leftDisp rightDisp r : Nat) (hr : r < 4)
    (mem : t.mem = s.mem) (gpr : t.gpr = s.gpr) (mask : MaskReady t) (l : Fin 16) (hl : l.val < 4) :
    (exec (loadBlock g leftDisp rightDisp r) t).vec (g.msg r) l = Wm (messageAt s leftDisp rightDisp) (4 * r + l.val) := by
  -- The load reads the pair's words, through the same addresses in both machines.
  rw [loadBlock, load_lanes t (g.msg r) _ (msg_apart g hg r).2.2.2.2 mask l hl]
  have := source_word t leftDisp rightDisp r l.val hr hl
  have e : messageAt t leftDisp rightDisp = messageAt s leftDisp rightDisp := by simp [messageAt, mem, gpr]
  rw [e] at this
  exact this

/-- A pair's loads: its four schedule vectors hold the message's words, and its state registers the initial state. -/
theorem loadCode_spec (g : Lane) (hg : Good g) (s : State) (leftDisp rightDisp : Nat)
    (table : TableAt s.mem (s.gpr tbl).toNat) (mask : MaskReady s) :
    let t := exec (loadCode g leftDisp rightDisp) s
    Packed (t.vec g.abef) (t.vec g.cdgh) initialState ∧
    ∀ r < 4, ∀ l : Fin 16, l.val < 4 → t.vec (g.msg r) l = Wm (messageAt s leftDisp rightDisp) (4 * r + l.val) := by
  intro t
  -- Every block keeps memory, the general registers, and the mask.
  have frame : ∀ (body : List Instr), (∀ i ∈ body, ∃ d, writes i = some d ∧ Touches g d) → ∀ u : State,
      u.mem = s.mem → u.gpr = s.gpr → MaskReady u →
      (exec body u).mem = s.mem ∧ (exec body u).gpr = s.gpr ∧ MaskReady (exec body u) := by
    intro body hb u hm hg' hmask
    obtain ⟨g1, m1, _⟩ := lane_frame g body hb u
    refine ⟨m1.trans hm, g1.trans hg', fun l hl => ?_⟩
    rw [untouched g body hb bswap (bswap_untouched g hg) u]
    exact hmask l hl
  have blockT : ∀ q, ∀ i ∈ loadBlock g leftDisp rightDisp q, ∃ d, writes i = some d ∧ Touches g d := fun q i hi => by
    simp only [loadBlock, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h <;> subst h <;> exact ⟨g.msg q, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨q, rfl⟩)))⟩
  have ivT : ∀ i ∈ ivLoads g, ∃ d, writes i = some d ∧ Touches g d := fun i hi => by
    simp only [ivLoads, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h <;> subst h
    · exact ⟨g.abef, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨g.cdgh, rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  -- A block writes only its own vector.
  have keep : ∀ q v, v ≠ g.msg q → ∀ u : State, (exec (loadBlock g leftDisp rightDisp q) u).vec v = u.vec v :=
    fun q v hv u => exec_vec _ (by simp [VecOnly, loadBlock, writes]) v
      (by simp [loadBlock, writes]; exact fun e => hv e.symm) u
  simp only [t, loadCode_blocks, exec_append]
  obtain ⟨m0, g0, k0⟩ := frame _ (blockT 0) s rfl rfl mask
  obtain ⟨m1, g1, k1⟩ := frame _ (blockT 1) _ m0 g0 k0
  obtain ⟨m2, g2, k2⟩ := frame _ (blockT 2) _ m1 g1 k1
  obtain ⟨m3, g3, _⟩ := frame _ (blockT 3) _ m2 g2 k2
  refine ⟨?_, fun r hr l hl => ?_⟩
  · -- The initial state comes from the table, in the order the SHA instructions read it.
    obtain ⟨_, aw, -, -, cw, -, -⟩ := state_apart g hg
    obtain ⟨qa, qc⟩ := tableWord_iv
    generalize hu : exec (loadBlock g leftDisp rightDisp 3) (exec (loadBlock g leftDisp rightDisp 2)
      (exec (loadBlock g leftDisp rightDisp 1) (exec (loadBlock g leftDisp rightDisp 0) s))) = u at m3 g3
    have tab : TableAt u.mem (u.gpr tbl).toNat := by rw [m3, g3]; exact table
    have ac := (state_apart g hg).1
    refine ⟨quad_of_eq _ _ (fun l hl => ?_) _ _ _ _ qa, quad_of_eq _ _ (fun l hl => ?_) _ _ _ _ qc⟩
    · have := read_table u tab ivAbef l.val (by decide) (by simp [ivAbef, tableSize]; omega)
      simp only [ivLoads, exec_cons, exec_nil, exec1, assign, ac, ac.symm, if_false, if_true, low, hl]
      simpa [State.addr, tableEntry] using this
    · have := read_table u tab ivCdgh l.val (by decide) (by simp [ivCdgh, tableSize]; omega)
      simp only [ivLoads, exec_cons, exec_nil, exec1, assign, if_true, low, hl]
      simpa [State.addr, tableEntry] using this
  · -- Vector r keeps its words through the loads after its own, and through the initial state's loads.
    obtain ⟨ma, mc, _, _, _⟩ := msg_apart g hg r
    rw [exec_vec _ (by simp [VecOnly, ivLoads, writes]) _ (by simp [ivLoads, writes]; exact ⟨ma.symm, mc.symm⟩)]
    have ne : ∀ q, q < 4 → q ≠ r → g.msg r ≠ g.msg q := fun q hq hne => msg_ne g hg r q (by omega)
    have hr' : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hr' with rfl | rfl | rfl | rfl
    · rw [keep 3 _ (ne 3 (by omega) (by omega)), keep 2 _ (ne 2 (by omega) (by omega)),
        keep 1 _ (ne 1 (by omega) (by omega))]
      exact loadBlock_lane g hg s s _ _ 0 (by omega) rfl rfl mask l hl
    · rw [keep 3 _ (ne 3 (by omega) (by omega)), keep 2 _ (ne 2 (by omega) (by omega))]
      exact loadBlock_lane g hg s _ _ _ 1 (by omega) m0 g0 k0 l hl
    · rw [keep 3 _ (ne 3 (by omega) (by omega))]
      exact loadBlock_lane g hg s _ _ _ 2 (by omega) m1 g1 k1 l hl
    · exact loadBlock_lane g hg s _ _ _ 3 (by omega) m2 g2 k2 l hl

/-- Every instruction of a pair's first feed-forward writes one of its registers. -/
theorem middleCode_touches (g : Lane) (hg : Good g) : ∀ i ∈ middleCode g, ∃ d, writes i = some d ∧ Touches g d := by
  -- The sums write the state registers, and the copies the first two schedule vectors.
  simp only [middleCode, List.mem_cons, List.not_mem_nil, or_false, hg.mid_abef, hg.mid_cdgh]
  intro i hi
  rcases hi with h | h | h | h <;> subst h
  · exact ⟨_, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
  · exact ⟨_, rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  · exact ⟨_, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨0, rfl⟩)))⟩
  · exact ⟨_, rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨1, rfl⟩)))⟩

/-- A pair's first feed-forward adds the initial state, and a copy of the result is kept aside. -/
theorem middleCode_spec (g : Lane) (hg : Good g) (s : State) (table : TableAt s.mem (s.gpr tbl).toNat)
    (r : Vector UInt32 8) (h : Packed (s.vec g.abef) (s.vec g.cdgh) r) :
    Packed ((exec (middleCode g) s).vec g.abef) ((exec (middleCode g) s).vec g.cdgh) (initialState.zipWith (· + ·) r) ∧
    Packed ((exec (middleCode g) s).vec g.midAbef) ((exec (middleCode g) s).vec g.midCdgh)
      (initialState.zipWith (· + ·) r) := by
  obtain ⟨ac, -, -, -, -, -, -⟩ := state_apart g hg
  obtain ⟨m0a, m0c, -, -, -⟩ := msg_apart g hg 0
  obtain ⟨m1a, m1c, -, -, -⟩ := msg_apart g hg 1
  have m01 : g.msg 0 ≠ g.msg 1 := msg_ne g hg 0 1 (by omega)
  rw [hg.mid_abef, hg.mid_cdgh]
  -- The four instructions, one at a time.
  have e : exec (middleCode g) s = exec1 (.movdqa (g.msg 1) g.cdgh) (exec1 (.movdqa (g.msg 0) g.abef)
      (exec1 (.padddMem g.cdgh (tableEntry ivCdgh)) (exec1 (.padddMem g.abef (tableEntry ivAbef)) s))) := by
    simp [middleCode, hg.mid_abef, hg.mid_cdgh]
  rw [e]
  generalize h1 : exec1 (.padddMem g.abef (tableEntry ivAbef)) s = t₁
  generalize h2 : exec1 (.padddMem g.cdgh (tableEntry ivCdgh)) t₁ = t₂
  generalize h3 : exec1 (.movdqa (g.msg 0) g.abef) t₂ = t₃
  generalize h4 : exec1 (.movdqa (g.msg 1) g.cdgh) t₃ = t₄
  -- Each instruction writes one vector register and keeps everything else.
  obtain ⟨m1, g1, v1⟩ := h1 ▸ step_frame (.padddMem g.abef (tableEntry ivAbef)) g.abef rfl s
  obtain ⟨-, -, v2⟩ := h2 ▸ step_frame (.padddMem g.cdgh (tableEntry ivCdgh)) g.cdgh rfl t₁
  obtain ⟨-, -, v3⟩ := h3 ▸ step_frame (.movdqa (g.msg 0) g.abef) (g.msg 0) rfl t₂
  obtain ⟨-, -, v4⟩ := h4 ▸ step_frame (.movdqa (g.msg 1) g.cdgh) (g.msg 1) rfl t₃
  -- Each state lane gains the initial state's word from the table.
  have ha : ∀ l : Fin 16, l.val < 4 → t₄.vec g.abef l = s.vec g.abef l + tableWord (ivAbef / 4 + l.val) := by
    intro l hl
    rw [v4 _ m1a.symm, v3 _ m0a.symm, v2 _ ac, ← h1, lane_padddMem _ _ _ l hl]
    exact congrArg _ (read_table s table ivAbef l.val (by decide) (by simp [ivAbef, tableSize]; omega))
  have hc : ∀ l : Fin 16, l.val < 4 → t₄.vec g.cdgh l = s.vec g.cdgh l + tableWord (ivCdgh / 4 + l.val) := by
    intro l hl
    rw [v4 _ m1c.symm, v3 _ m0c.symm, ← h2, lane_padddMem _ _ _ l hl, v1 _ ac.symm, m1,
      ShaNi.addr_congr _ _ g1]
    exact congrArg _ (read_table s table ivCdgh l.val (by decide) (by simp [ivCdgh, tableSize]; omega))
  have p := packed_add _ _ _ _ _ _ _ _ ha hc h tableWord_iv
  refine ⟨p, ?_⟩
  -- The copies are the sums themselves.
  have ma : ∀ l : Fin 16, l.val < 4 → t₄.vec (g.msg 0) l = t₄.vec g.abef l := by
    intro l hl
    rw [v4 _ m01, ← h3, lane_movdqa _ _ _ l hl, v4 _ m1a.symm, v3 _ m0a.symm]
  have mc : ∀ l : Fin 16, l.val < 4 → t₄.vec (g.msg 1) l = t₄.vec g.cdgh l := by
    intro l hl
    rw [← h4, lane_movdqa _ _ _ l hl, h4, v4 _ m1c.symm]
  obtain ⟨p1, p2⟩ := p
  exact ⟨quad_of_eq _ _ ma _ _ _ _ p1, quad_of_eq _ _ mc _ _ _ _ p2⟩

end Ssz.Native.Kernel.ShaNiDual
