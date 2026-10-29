import SszNative.Proofs.Kernel.ShaNi.Rounds

/-! One pass of the SHA-NI kernel's loop: the parent of one pair of nodes, written to the output. -/

namespace Ssz.Native.Kernel.ShaNi

open Ssz.Native.Asm Ssz.Sha256

/-- A pair is always a 64-byte message. -/
theorem pairMessage_size (mem : Nat → UInt8) (l r : Nat) : (pairMessage mem l r).size = 64 := by
  -- The message is built from 64 bytes.
  simp [pairMessage, ByteArray.size]

/-- Byte i of a pair: the left node's bytes, then the right node's. -/
theorem pairMessage_get (mem : Nat → UInt8) (l r i : Nat) (hi : i < 64) :
    (pairMessage mem l r).get! i = if i < 32 then mem (l + i) else mem (r + (i - 32)) := by
  -- The message's byte i is read from the left node below 32, and from the right node above.
  rw [Kernel.get!_eq _ _ (by rw [pairMessage_size]; exact hi)]
  simp [pairMessage, ByteArray.getElem_eq_getElem_data]

/-- Byte k of a digest: byte k mod 4 of word k / 4, the most significant first. -/
theorem digest_get (st : Vector UInt32 8) (k : Nat) (hk : k < 32) :
    (digest st).get! k = (st[k / 4]'(by omega) >>> (24 - 8 * UInt32.ofNat (k % 4))).toUInt8 := by
  -- The digest writes each word's bytes, the most significant first.
  rw [Kernel.get!_eq _ _ (by simp [digest, ByteArray.size]; exact hk)]
  simp [digest, ByteArray.getElem_eq_getElem_data]

/-- The message's schedule word i, as a function of the index. -/
abbrev Wm (m : ByteArray) (i : Nat) : UInt32 := (schedule m 0)[i]!

/-- Any block's schedule satisfies the recurrence. -/
theorem recurs_schedule (m : ByteArray) : Recurs (Wm m) := by
  -- Each schedule word past the sixteenth follows the recurrence of the specification.
  intro c lo hi
  simp only [Wm]
  rw [getElem!_pos _ c hi, getElem!_pos _ (c - 16) (by omega), getElem!_pos _ (c - 15) (by omega),
    getElem!_pos _ (c - 7) (by omega), getElem!_pos _ (c - 2) (by omega)]
  exact schedule_recurrence m 0 c lo hi

/-- The byte-reversal mask sits in its register. -/
def MaskReady (s : State) : Prop :=
  ∀ l : Fin 16, l.val < 4 → s.vec bswap l = reverseLane l.val

/-- Loading four words of a node and reversing their bytes gives four big-endian words. -/
theorem load_lanes (s : State) (d : Vreg) (m : Mem) (hd : d ≠ bswap) (mask : MaskReady s) (l : Fin 16) (hl : l.val < 4) :
    (exec [.movdqu d m, .pshufb d bswap] s).vec d l =
      (s.mem (s.addr m + 4 * l.val)).toUInt32 <<< 24 ||| (s.mem (s.addr m + 4 * l.val + 1)).toUInt32 <<< 16 |||
        (s.mem (s.addr m + 4 * l.val + 2)).toUInt32 <<< 8 ||| (s.mem (s.addr m + 4 * l.val + 3)).toUInt32 := by
  -- The load reads four little-endian words, and the shuffle reverses each.
  simp only [exec_cons, exec_nil]
  generalize e : exec1 (.movdqu d m) s = t
  have keep : t.vec bswap = s.vec bswap := by rw [← e]; simp [exec1, assign, hd.symm]
  have word : t.vec d l = readWord s.mem (s.addr m + 4 * l.val) := by rw [← e]; simp [exec1, assign, low, hl]
  simp only [exec1, assign, if_true, low, hl]
  rw [shuffle_reverse (t.vec d) (t.vec bswap) (by rw [keep]; exact mask 0 (by decide))
    (by rw [keep]; exact mask 1 (by decide)) (by rw [keep]; exact mask 2 (by decide))
    (by rw [keep]; exact mask 3 (by decide)) l hl, word, bswap32_readWord]

/-- Where schedule vector r's bytes come from: the left node for the first two, the right node for the others. -/
def source (r : Nat) : Mem :=
  if r < 2 then ⟨left, 16 * r⟩ else ⟨right, 16 * (r - 2)⟩

/-- The big-endian word a load reads is the message's schedule word. -/
theorem source_word (s : State) (r l : Nat) (hr : r < 4) (hl : l < 4) :
    (s.mem (s.addr (source r) + 4 * l)).toUInt32 <<< 24 ||| (s.mem (s.addr (source r) + 4 * l + 1)).toUInt32 <<< 16 |||
        (s.mem (s.addr (source r) + 4 * l + 2)).toUInt32 <<< 8 ||| (s.mem (s.addr (source r) + 4 * l + 3)).toUInt32 =
      Wm (pairMessage s.mem (s.gpr left).toNat (s.gpr right).toNat) (4 * r + l) := by
  -- A schedule word below 16 is the message's big-endian word at four times its index.
  simp only [Wm]
  rw [getElem!_pos _ _ (by omega), schedule_input _ _ _ (by omega), wordAt]
  simp only [Nat.zero_add]
  rw [pairMessage_get _ _ _ _ (by omega), pairMessage_get _ _ _ _ (by omega), pairMessage_get _ _ _ _ (by omega),
    pairMessage_get _ _ _ _ (by omega)]
  unfold source
  -- The first two vectors read the left node, the last two the right node.
  split
  · simp only [State.addr]
    simp (disch := omega) only [if_pos]
    rw [show (s.gpr left).toNat + 16 * r + 4 * l = (s.gpr left).toNat + 4 * (4 * r + l) by omega]
    simp only [Nat.add_assoc]
  · simp only [State.addr]
    simp (disch := omega) only [if_neg]
    rw [show 4 * (4 * r + l) - 32 = 16 * (r - 2) + 4 * l by omega,
      show 4 * (4 * r + l) + 1 - 32 = 16 * (r - 2) + 4 * l + 1 by omega,
      show 4 * (4 * r + l) + 2 - 32 = 16 * (r - 2) + 4 * l + 2 by omega,
      show 4 * (4 * r + l) + 3 - 32 = 16 * (r - 2) + 4 * l + 3 by omega]
    simp only [Nat.add_assoc]

/-- The load of schedule vector r. -/
def loadBlock (r : Nat) : List Instr :=
  [.movdqu (msg r) (source r), .pshufb (msg r) bswap]

/-- The four loads open the pair's code. -/
def loads : List Instr :=
  (List.range 4).flatMap (fun r =>
    [.movdqu (msg r) (if r < 2 then ⟨left, 16 * r⟩ else ⟨right, 16 * (r - 2)⟩), .pshufb (msg r) bswap])

/-- The loads, one block per schedule vector. -/
theorem loads_blocks : loads = loadBlock 0 ++ loadBlock 1 ++ loadBlock 2 ++ loadBlock 3 := rfl

/-- A load writes only its schedule vector. -/
theorem loadBlock_writes (r : Nat) (v : Vreg) (hv : v ≠ msg r) : ∀ i ∈ loadBlock r, writes i ≠ some v := by
  -- A load writes its schedule vector and nothing else.
  simp [loadBlock, writes]
  exact fun e => hv e.symm

/-- A load writes only vector registers. -/
theorem loadBlock_vecOnly (r : Nat) : VecOnly (loadBlock r) := by
  -- Both instructions write a vector register.
  simp [VecOnly, loadBlock, writes]

/-- The loads write only vector registers. -/
theorem loads_vecOnly : VecOnly loads := by
  -- Every load writes a vector register.
  simp [VecOnly, loads_blocks, loadBlock, writes]

/-- One load, from any machine whose memory and general registers are the pair's. -/
theorem loadBlock_lane (s t : State) (r : Nat) (hr : r < 4) (mem : t.mem = s.mem) (gpr : t.gpr = s.gpr)
    (mask : MaskReady t) (l : Fin 16) (hl : l.val < 4) :
    (exec (loadBlock r) t).vec (msg r) l = Wm (pairMessage s.mem (s.gpr left).toNat (s.gpr right).toNat) (4 * r + l.val) := by
  -- The load reads the pair's words, through the same addresses in both machines.
  rw [loadBlock, load_lanes t (msg r) (source r) (by simp [Fin.ext_iff, msg_val, bswap]; omega) mask l hl]
  have := source_word t r l.val hr hl
  rw [mem, gpr] at this
  rw [← this, show t.addr (source r) = s.addr (source r) by simp [State.addr, gpr], mem]

/-- After the loads, schedule vector r holds the message's words 4r to 4r + 3. -/
theorem loads_spec (s : State) (mask : MaskReady s) (r : Nat) (hr : r < 4) (l : Fin 16) (hl : l.val < 4) :
    (exec loads s).vec (msg r) l = Wm (pairMessage s.mem (s.gpr left).toNat (s.gpr right).toNat) (4 * r + l.val) := by
  -- Every load keeps memory, the general registers, and the mask.
  have frame : ∀ (body : List Instr), VecOnly body → (∀ i ∈ body, writes i ≠ some bswap) → ∀ t : State,
      t.mem = s.mem → t.gpr = s.gpr → MaskReady t →
      (exec body t).mem = s.mem ∧ (exec body t).gpr = s.gpr ∧ MaskReady (exec body t) := by
    intro body hb hk t hm hg hmask
    obtain ⟨g, m, _⟩ := exec_frame body hb t
    refine ⟨m.trans hm, g.trans hg, fun l hl => ?_⟩
    rw [exec_vec body hb bswap hk t]
    exact hmask l hl
  have keepMask : ∀ q, ∀ i ∈ loadBlock q, writes i ≠ some bswap := fun q =>
    loadBlock_writes q bswap (by simp [Fin.ext_iff, msg_val, bswap]; omega)
  have ne : ∀ q, q < 4 → q ≠ r → msg r ≠ msg q := fun q hq hne e => by
    have := congrArg Fin.val e
    simp [msg_val] at this
    omega
  simp only [loads_blocks, exec_append]
  -- The block that loads vector r, and the blocks after it that leave it alone.
  have B : ∀ q, q < 4 → ∀ t : State, t.mem = s.mem → t.gpr = s.gpr → MaskReady t →
      (exec (loadBlock q) t).mem = s.mem ∧ (exec (loadBlock q) t).gpr = s.gpr ∧ MaskReady (exec (loadBlock q) t) :=
    fun q _ => frame _ (loadBlock_vecOnly q) (keepMask q)
  have keep : ∀ q, q < 4 → q ≠ r → ∀ t : State, (exec (loadBlock q) t).vec (msg r) = t.vec (msg r) :=
    fun q hq hne t => exec_vec _ (loadBlock_vecOnly q) _ (loadBlock_writes q _ (ne q hq hne)) t
  obtain ⟨m0, g0, k0⟩ := B 0 (by omega) s rfl rfl mask
  obtain ⟨m1, g1, k1⟩ := B 1 (by omega) _ m0 g0 k0
  obtain ⟨m2, g2, k2⟩ := B 2 (by omega) _ m1 g1 k1
  have hr' : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
  -- Vector r keeps its words through the loads after its own.
  rcases hr' with rfl | rfl | rfl | rfl
  · rw [keep 3 (by omega) (by omega), keep 2 (by omega) (by omega), keep 1 (by omega) (by omega)]
    exact loadBlock_lane s s 0 (by omega) rfl rfl mask l hl
  · rw [keep 3 (by omega) (by omega), keep 2 (by omega) (by omega)]
    exact loadBlock_lane s _ 1 (by omega) m0 g0 k0 l hl
  · rw [keep 3 (by omega) (by omega)]
    exact loadBlock_lane s _ 2 (by omega) m1 g1 k1 l hl
  · exact loadBlock_lane s _ 3 (by omega) m2 g2 k2 l hl

/-- The initial state's loads. -/
def ivLoads : List Instr := [.movdqu abef (tableEntry ivAbef), .movdqu cdgh (tableEntry ivCdgh)]

/-- The first block's sixteen groups. -/
def firsts : List Instr := (List.range 16).flatMap firstRounds

/-- The first feed-forward, kept aside for the second. -/
def middle : List Instr :=
  [.padddMem abef (tableEntry ivAbef), .padddMem cdgh (tableEntry ivCdgh), .movdqa midAbef abef, .movdqa midCdgh cdgh]

/-- The padding block's sixteen groups. -/
def pads : List Instr := (List.range 16).flatMap paddingRounds

/-- The second feed-forward, then the digest's words put in order and byte-reversed. -/
def finish : List Instr :=
  [.paddd abef midAbef, .paddd cdgh midCdgh, .pshufd abef abef 0x1B, .pshufd cdgh cdgh 0xB1, .movdqa tmp abef,
    .pblendw tmp cdgh 0xF0, .palignr cdgh abef 8, .pshufb tmp bswap, .pshufb cdgh bswap]

/-- The digest's two stores. -/
def stores : List Instr := [.movdquStore ⟨out, 0⟩ tmp, .movdquStore ⟨out, 16⟩ cdgh]

/-- The pair's code, phase by phase. -/
theorem pairCode_split : pairCode = loads ++ ivLoads ++ firsts ++ middle ++ pads ++ finish ++ stores := by
  simp only [pairCode, loads, ivLoads, firsts, middle, pads, finish, stores, List.append_assoc, List.cons_append,
    List.nil_append]

/-- Four lanes that agree with another four hold the same words. -/
theorem quad_of_eq (v f : Lanes) (h : ∀ l : Fin 16, l.val < 4 → v l = f l) (a b c d : UInt32) (q : Quad f a b c d) :
    Quad v a b c d := by
  obtain ⟨q0, q1, q2, q3⟩ := q
  exact ⟨(h 0 (by decide)).trans q0, (h 1 (by decide)).trans q1, (h 2 (by decide)).trans q2,
    (h 3 (by decide)).trans q3⟩

/-- The initial state's loads give the initial state, in the SHA instructions' order. -/
theorem ivLoads_spec (s : State) (table : TableAt s.mem (s.gpr tbl).toNat) :
    Packed ((exec ivLoads s).vec abef) ((exec ivLoads s).vec cdgh) initialState := by
  -- The table holds the initial state in the order the SHA instructions read it.
  obtain ⟨qa, qc⟩ := tableWord_iv
  refine ⟨quad_of_eq _ _ (fun l hl => ?_) _ _ _ _ qa, quad_of_eq _ _ (fun l hl => ?_) _ _ _ _ qc⟩
  · simp only [ivLoads, exec_cons, exec_nil, exec1, assign]
    rw [if_neg (by decide)]
    simp only [low, hl, if_true]
    exact read_table s table ivAbef l.val (by decide) (by simp [ivAbef, tableSize]; omega)
  · simp only [ivLoads, exec_cons, exec_nil, exec1, assign, if_true]
    simp only [low, hl, if_true]
    exact read_table _ table ivCdgh l.val (by decide) (by simp [ivCdgh, tableSize]; omega)

/-- Lanes that add two others' words hold the sums. -/
theorem quad_add (x u v : Lanes) (h : ∀ l : Fin 16, l.val < 4 → x l = u l + v l) (a b c d a' b' c' d' : UInt32)
    (qu : Quad u a b c d) (qv : Quad v a' b' c' d') : Quad x (a + a') (b + b') (c + c') (d + d') := by
  -- Each of the four lanes adds its two words.
  obtain ⟨u0, u1, u2, u3⟩ := qu
  obtain ⟨v0, v1, v2, v3⟩ := qv
  exact ⟨by rw [h 0 (by decide), u0, v0], by rw [h 1 (by decide), u1, v1], by rw [h 2 (by decide), u2, v2],
    by rw [h 3 (by decide), u3, v3]⟩

/-- Packed states that add lane by lane pack the feed-forward. -/
theorem packed_add (x y u v p q : Lanes) (st r : Vector UInt32 8)
    (hx : ∀ l : Fin 16, l.val < 4 → x l = u l + p l) (hy : ∀ l : Fin 16, l.val < 4 → y l = v l + q l)
    (hr : Packed u v r) (hs : Packed p q st) : Packed x y (st.zipWith (· + ·) r) := by
  -- Lane by lane, the sums are the feed-forward's words.
  have a := quad_add x p u (fun l hl => by rw [hx l hl, UInt32.add_comm]) _ _ _ _ _ _ _ _ hs.1 hr.1
  have b := quad_add y q v (fun l hl => by rw [hy l hl, UInt32.add_comm]) _ _ _ _ _ _ _ _ hs.2 hr.2
  simp only [Packed, Vector.getElem_zipWith]
  exact ⟨a, b⟩

/-- The first feed-forward adds the initial state, and a copy of the result is kept aside. -/
theorem middle_spec (s : State) (table : TableAt s.mem (s.gpr tbl).toNat) (r : Vector UInt32 8)
    (h : Packed (s.vec abef) (s.vec cdgh) r) :
    Packed ((exec middle s).vec abef) ((exec middle s).vec cdgh) (initialState.zipWith (· + ·) r) ∧
    Packed ((exec middle s).vec midAbef) ((exec middle s).vec midCdgh) (initialState.zipWith (· + ·) r) := by
  -- The four instructions, one at a time.
  have e : exec middle s = exec1 (.movdqa midCdgh cdgh) (exec1 (.movdqa midAbef abef)
      (exec1 (.padddMem cdgh (tableEntry ivCdgh)) (exec1 (.padddMem abef (tableEntry ivAbef)) s))) := rfl
  rw [e]
  generalize h1 : exec1 (.padddMem abef (tableEntry ivAbef)) s = t₁
  generalize h2 : exec1 (.padddMem cdgh (tableEntry ivCdgh)) t₁ = t₂
  generalize h3 : exec1 (.movdqa midAbef abef) t₂ = t₃
  generalize h4 : exec1 (.movdqa midCdgh cdgh) t₃ = t₄
  -- Each instruction writes one vector register and keeps everything else.
  obtain ⟨m1, g1, v1⟩ := h1 ▸ step_frame (.padddMem abef (tableEntry ivAbef)) abef rfl s
  obtain ⟨m2, g2, v2⟩ := h2 ▸ step_frame (.padddMem cdgh (tableEntry ivCdgh)) cdgh rfl t₁
  obtain ⟨_, _, v3⟩ := h3 ▸ step_frame (.movdqa midAbef abef) midAbef rfl t₂
  obtain ⟨_, _, v4⟩ := h4 ▸ step_frame (.movdqa midCdgh cdgh) midCdgh rfl t₃
  -- Each state lane gains the initial state's word from the table.
  have ha : ∀ l : Fin 16, l.val < 4 → t₄.vec abef l = s.vec abef l + tableWord (ivAbef / 4 + l.val) := by
    intro l hl
    rw [v4 _ (by decide), v3 _ (by decide), v2 _ (by decide), ← h1, lane_padddMem _ _ _ l hl]
    exact congrArg _ (read_table s table ivAbef l.val (by decide) (by simp [ivAbef, tableSize]; omega))
  have hc : ∀ l : Fin 16, l.val < 4 → t₄.vec cdgh l = s.vec cdgh l + tableWord (ivCdgh / 4 + l.val) := by
    intro l hl
    rw [v4 _ (by decide), v3 _ (by decide), ← h2, lane_padddMem _ _ _ l hl, v1 _ (by decide), m1,
      addr_congr _ _ g1]
    exact congrArg _ (read_table s table ivCdgh l.val (by decide) (by simp [ivCdgh, tableSize]; omega))
  have p := packed_add _ _ _ _ _ _ _ _ ha hc h tableWord_iv
  refine ⟨p, ?_⟩
  -- The copies are the sums themselves.
  have ma : ∀ l : Fin 16, l.val < 4 → t₄.vec midAbef l = t₄.vec abef l := by
    intro l hl
    rw [v4 _ (by decide), ← h3, lane_movdqa _ _ _ l hl, v4 _ (by decide), v3 _ (by decide)]
  have mc : ∀ l : Fin 16, l.val < 4 → t₄.vec midCdgh l = t₄.vec cdgh l := by
    intro l hl
    rw [← h4, lane_movdqa _ _ _ l hl, h4, v4 _ (by decide)]
  obtain ⟨p1, p2⟩ := p
  exact ⟨quad_of_eq _ _ ma _ _ _ _ p1, quad_of_eq _ _ mc _ _ _ _ p2⟩

end Ssz.Native.Kernel.ShaNi
