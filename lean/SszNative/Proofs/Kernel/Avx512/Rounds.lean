import SszNative.Kernel.Avx512
import SszNative.Proofs.Asm.Run
import SszNative.Proofs.Kernel.Sha256

/-!
The sixteen-lane kernel's compute core: from the messages' words to their digests' words, lane by lane.

Every instruction between the transposes acts on each lane alone.
So each lane runs as one scalar SHA-256 over its own message:

- the initial state is loaded into registers 0 to 7;
- the first block runs 64 rounds, with its schedule in registers 8 to 23;
- the first feed-forward ends the first compression, with a copy kept in registers 8 to 15;
- the padding block runs 64 rounds over constant words;
- the second feed-forward ends the second compression, in registers 0 to 7.
-/

namespace Ssz.Native.Kernel.Avx512

open Ssz.Sha256 Ssz.Native.Asm

/-- Whether an instruction reads and writes each lane on its own, and writes only a vector register. -/
def lanewise : Instr → Bool
  | .vmov .. | .vadd .. | .vaddMem .. | .vror .. | .vshr .. | .vternlog .. | .vload .. => true
  | _ => false

/-- One lane of the vector registers after a lanewise instruction. -/
def laneStep (mem : Nat → UInt8) (gpr : Gpr → UInt64) (l : Fin 16) (regs : Vreg → UInt32) :
    Instr → Vreg → UInt32
  | .vmov d a => assign regs d (regs a)
  | .vadd d a b => assign regs d (regs a + regs b)
  | .vaddMem d a m => assign regs d (regs a + readWord mem ((gpr m.base).toNat + m.disp + 4 * l.val))
  | .vror d a k => assign regs d (rotr (regs a) k.toUInt32)
  | .vshr d a k => assign regs d (if k < 32 then regs a >>> k.toUInt32 else 0)
  | .vternlog d a b t => assign regs d (ternlog t.toNat.toUInt8 (regs d) (regs a) (regs b))
  | .vload d m => assign regs d (readWord mem ((gpr m.base).toNat + m.disp + 4 * l.val))
  | _ => regs

/-- One lane of the vector registers after a list of lanewise instructions. -/
def laneRun (mem : Nat → UInt8) (gpr : Gpr → UInt64) (l : Fin 16) : List Instr → (Vreg → UInt32) → Vreg → UInt32
  | [], regs => regs
  | i :: rest, regs => laneRun mem gpr l rest (laneStep mem gpr l regs i)

/-- A lanewise instruction changes each lane of the vector registers as one lane of it does. -/
theorem exec1_lanewise (i : Instr) (h : lanewise i) (s : State) :
    exec1 i s = { s with vec := fun r l => laneStep s.mem s.gpr l (fun r => s.vec r l) i r } := by
  -- Each lanewise instruction writes its destination with a value computed from the same lane.
  cases i <;> simp [lanewise] at h <;>
    · simp only [exec1, laneStep, State.addr]
      congr
      funext r l
      simp only [assign]
      split <;> rfl

/-- A list of lanewise instructions runs lane by lane, leaving everything but the vector registers alone. -/
theorem exec_lanewise (body : List Instr) (h : ∀ i ∈ body, lanewise i) (s : State) :
    exec body s = { s with vec := fun r l => laneRun s.mem s.gpr l body (fun r => s.vec r l) r } := by
  -- The first instruction runs lane by lane, and the rest by induction.
  induction body generalizing s with
  | nil => rfl
  | cons i rest ih =>
    rw [exec_cons, exec1_lanewise i (h i (by simp)) s, ih (fun j hj => h j (by simp [hj]))]
    rfl

/-- Reading the replaced argument gives the new value. -/
theorem assign_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : assign f a b a = b := by
  -- The replaced argument reads the new value.
  simp [assign]

/-- Reading any other argument gives the old value. -/
theorem assign_ne {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) (x : α) (h : x ≠ a) :
    assign f a b x = f x := by
  -- Another argument reads the old value.
  simp [assign, h]

/-- Table 0xCA is the choice function. -/
theorem ternlog_ca (a b c : UInt32) : ternlog 0xCA a b c = choose a b c := by
  simp (config := { decide := true }) only [ternlog, choose, ite_true, ite_false]
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  -- Bit by bit, the table is the function on every pattern of the three inputs.
  simp [hi]
  cases a.toBitVec[i] <;> cases b.toBitVec[i] <;> cases c.toBitVec[i] <;> rfl

/-- Table 0x96 is the three-way exclusive or. -/
theorem ternlog_96 (a b c : UInt32) : ternlog 0x96 a b c = a ^^^ b ^^^ c := by
  simp (config := { decide := true }) only [ternlog, ite_true, ite_false]
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  -- Bit by bit, the table is the function on every pattern of the three inputs.
  simp [hi]
  cases a.toBitVec[i] <;> cases b.toBitVec[i] <;> cases c.toBitVec[i] <;> rfl

/-- Table 0xE8 is the majority function. -/
theorem ternlog_e8 (a b c : UInt32) : ternlog 0xE8 a b c = majority a b c := by
  simp (config := { decide := true }) only [ternlog, majority, ite_true, ite_false]
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  -- Bit by bit, the table is the function on every pattern of the three inputs.
  simp [hi]
  cases a.toBitVec[i] <;> cases b.toBitVec[i] <;> cases c.toBitVec[i] <;> rfl

/-- Reading a function with one argument's value replaced. -/
theorem assign_apply {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) (x : α) :
    assign f a b x = if x = a then b else f x := rfl

/-- A round's instructions after the one that seeds its running sum. -/
def roundTail (t : Nat) : List Instr := (roundCode t .ret).tail

/-- A round is its seed, then its tail. -/
theorem roundCode_eq (t : Nat) (seed : Instr) : roundCode t seed = seed :: roundTail t := rfl

/-- A first-block round: the seed with the constant, the schedule word added, then the tail. -/
theorem firstRound_eq (t : Nat) :
    firstRound t = .vaddMem t1 (role t 7) (tableEntry (kAvx512 t)) :: .vadd t1 t1 (ring t) :: roundTail t := rfl

/-- One round from the sum that seeds it: the sum is H plus the round's constant and word. -/
def roundT (st : Vector UInt32 8) (sum : UInt32) : Vector UInt32 8 :=
  let t1 := sum + choose st[4] st[5] st[6] + bigSigma1 st[4]
  #v[t1 + (bigSigma0 st[0] + majority st[0] st[1] st[2]), st[0], st[1], st[2], st[3] + t1, st[4], st[5], st[6]]

/-- A round of the specification is a round seeded with H plus the constant plus the word. -/
theorem round_eq_roundT (st : Vector UInt32 8) (k w : UInt32) : round st k w = roundT st (st[7] + k + w) := by
  -- The specification's sum and the seeded sum add the same five words in another order.
  have t1 : st[7] + bigSigma1 st[4] + choose st[4] st[5] st[6] + k + w =
      st[7] + k + w + choose st[4] st[5] st[6] + bigSigma1 st[4] := by ac_rfl
  simp only [round, roundT, t1]


set_option maxHeartbeats 4000000 in
/-- A round's tail on one lane takes the working words one round on, from the seeded sum. -/
theorem tail_lane (mem gpr l regs) (t j : Nat) (hj : j < 8) :
    laneRun mem gpr l (roundTail t) regs (role (t + 1) j) =
      (roundT (Vector.ofFn fun j : Fin 8 => regs (role t j)) (regs t1))[j] := by
  -- Register roles rotate by one each round, so eight round positions and eight words cover every case.
  have k' : (t + 1) % 8 = (t % 8 + 1) % 8 := by omega
  simp only [roundTail, roundCode, List.tail_cons, role, k']
  have hc : t % 8 = 0 ∨ t % 8 = 1 ∨ t % 8 = 2 ∨ t % 8 = 3 ∨ t % 8 = 4 ∨ t % 8 = 5 ∨ t % 8 = 6 ∨ t % 8 = 7 := by
    omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hc with h | h | h | h | h | h | h | h <;> rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [h, laneRun, laneStep, home, t1, tmp, assign_apply, Fin.mk.injEq, Fin.isValue] <;>
    simp [roundT, ternlog_ca, ternlog_96, ternlog_e8, bigSigma0, bigSigma1] <;> ac_rfl

/-- The register a lanewise instruction writes. -/
def dest : Instr → Option Vreg
  | .vmov d _ | .vadd d _ _ | .vaddMem d _ _ | .vror d _ _ | .vshr d _ _ | .vternlog d _ _ _ | .vload d _ => some d
  | _ => none

/-- An instruction leaves every register but the one it writes. -/
theorem laneStep_other (mem gpr l regs) (i : Instr) (r : Vreg) (h : dest i ≠ some r) :
    laneStep mem gpr l regs i r = regs r := by
  -- An instruction that writes some other register leaves this one alone.
  cases i <;> simp only [dest, ne_eq, Option.some.injEq] at h <;> simp [laneStep, assign, Ne.symm h]

/-- A list of instructions leaves every register none of them writes. -/
theorem laneRun_other (mem gpr l) (body : List Instr) (regs : Vreg → UInt32) (r : Vreg)
    (h : ∀ i ∈ body, dest i ≠ some r) : laneRun mem gpr l body regs r = regs r := by
  induction body generalizing regs with
  -- The first instruction leaves the register alone, and so does the rest.
  | nil => rfl
  | cons i rest ih =>
    simp only [laneRun]
    rw [ih _ (fun j hj => h j (by simp [hj])), laneStep_other _ _ _ _ _ _ (h i (by simp))]

/-- Two lists run one after the other. -/
theorem laneRun_append (mem gpr l) (a b : List Instr) (regs : Vreg → UInt32) :
    laneRun mem gpr l (a ++ b) regs = laneRun mem gpr l b (laneRun mem gpr l a regs) := by
  -- The first list runs, then the second.
  induction a generalizing regs with
  | nil => rfl
  | cons i rest ih => exact ih _

/-- The blocks for indices below n + 1 run as those below n, then block n. -/
theorem laneRun_flatMap_succ (mem gpr l) (f : Nat → List Instr) (n : Nat) (regs : Vreg → UInt32) :
    laneRun mem gpr l ((List.range (n + 1)).flatMap f) regs =
      laneRun mem gpr l (f n) (laneRun mem gpr l ((List.range n).flatMap f) regs) := by
  -- The range up to n + 1 is the range up to n, then n.
  rw [List.range_succ, List.flatMap_append, laneRun_append]
  simp

/-- The tail of a round writes only the working words, the running sum, and the temporaries. -/
theorem tail_other (mem gpr l regs) (t : Nat) (r : Vreg) (low : 8 ≤ r.val) (high : r.val < 24) :
    laneRun mem gpr l (roundTail t) regs r = regs r := by
  -- Every register a round's tail writes is a working word, the sum, or a temporary.
  apply laneRun_other
  simp only [roundTail, roundCode, List.tail_cons, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, dest, ne_eq, Option.some.injEq, Fin.ext_iff, role, home, tmp, t1,
    show ((24 : Vreg) : Nat) = 24 from rfl]
  omega

/-- The working words live in the first eight registers. -/
theorem role_lt (t j : Nat) : (role t j).val < 8 := by
  -- Roles are taken modulo 8.
  simp only [role, home]; omega

/-- Schedule word t lives in register 8 + t mod 16. -/
theorem ring_val (u : Nat) : (ring u).val = 8 + u % 16 := rfl

/-- No schedule register is the running sum. -/
theorem ring_ne_t1 (u : Nat) : ring u ≠ t1 := by
  -- Schedule registers are 8 to 23, and the sum is 24.
  simp only [ne_eq, Fin.ext_iff, ring_val, t1, show ((24 : Vreg) : Nat) = 24 from rfl]; omega

/-- No working-word register is the running sum. -/
theorem role_ne_t1 (t j : Nat) : role t j ≠ t1 := by
  -- Working words are 0 to 7, and the sum is 24.
  have := role_lt t j
  simp only [ne_eq, Fin.ext_iff, t1, show ((24 : Vreg) : Nat) = 24 from rfl]; omega

/-- No schedule register is a temporary. -/
theorem ring_ne_tmp (u k : Nat) : ring u ≠ tmp k := by
  -- Schedule registers are 8 to 23, and temporaries 25 to 31.
  simp only [ne_eq, Fin.ext_iff, ring_val, tmp]; omega

/-- Schedule words less than sixteen apart, and not equal, live in different registers. -/
theorem ring_add_ne (u i : Nat) (h : i % 16 ≠ 0) : ring (u + i) ≠ ring u := by
  -- Distinct words modulo 16 sit in distinct registers.
  simp only [ne_eq, Fin.ext_iff, ring_val]; omega

/-- Schedule word t + 16 overwrites word t. -/
theorem ring_add_sixteen (u : Nat) : ring (u + 16) = ring u := by
  -- Indices sixteen apart share a register.
  apply Fin.ext; simp only [ring_val]; omega

/-- A lane of a sixteen-lane table row: the row's word at that lane. -/
theorem table_lane (mem : Nat → UInt8) (gpr : Gpr → UInt64) (table : TableAt mem (gpr tbl).toNat)
    (l : Fin 16) (row : Nat) (within : row < 149) :
    readWord mem ((gpr (tableEntry (64 * row)).base).toNat + (tableEntry (64 * row)).disp + 4 * l.val) = tableWord (16 * row + l.val) := by
  -- Row r of the table sits 64 r bytes past its base, word l of it 4 l bytes further.
  simp only [tableEntry]
  rw [show (gpr tbl).toNat + 64 * row + 4 * l.val = (gpr tbl).toNat + 4 * (16 * row + l.val) by omega]
  exact readWord_table mem _ table _ (by simp only [tableSize]; omega)

/-- The constants row of round t. -/
theorem tableWord_k (t : Nat) (l : Nat) (ht : t < 64) (hl : l < 16) :
    tableWord (16 * t + l) = roundConstants[t]! := by
  -- The word falls in the constants rows.
  simp only [tableWord]
  rw [if_pos (by omega), show (16 * t + l) / 16 % 64 = t by omega]

/-- The padding row of round t: the constant plus the padding block's schedule word. -/
theorem tableWord_pad (t : Nat) (l : Nat) (ht : t < 64) (hl : l < 16) :
    tableWord (16 * (64 + t) + l) = roundConstants[t]! + (schedule paddingBlock 0)[t]! := by
  -- The word falls in the padding rows.
  simp only [tableWord]
  rw [if_neg (by omega), if_pos (by omega), paddingWK, show (16 * (64 + t) + l - 1024) / 16 % 64 = t by omega]

/-- The initial-state row of word j. -/
theorem tableWord_iv (j : Nat) (l : Nat) (hj : j < 8) (hl : l < 16) :
    tableWord (16 * (128 + j) + l) = initialState[j]! := by
  -- The word falls in the initial-state rows.
  simp only [tableWord]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show (16 * (128 + j) + l - 2048) / 16 % 8 = j by omega]

/-- A first-block round on one lane: the working words take one round of the constant and the schedule word. -/
theorem firstRound_lane (mem gpr l regs) (table : TableAt mem (gpr tbl).toNat) (t : Nat) (ht : t < 64) :
    (Vector.ofFn fun j : Fin 8 => laneRun mem gpr l (firstRound t) regs (role (t + 1) j)) =
      round (Vector.ofFn fun j : Fin 8 => regs (role t j)) roundConstants[t]! (regs (ring t)) := by
  -- Compare the eight working words one by one.
  rw [round_eq_roundT]
  apply Vector.ext
  intro j hj
  simp only [Vector.getElem_ofFn]
  rw [firstRound_eq]
  simp only [laneRun]
  rw [tail_lane _ _ _ _ _ _ hj]
  -- The seed reads H plus the table's constant, then adds the schedule word.
  simp only [laneStep, assign_same, assign_ne _ _ _ _ (ring_ne_t1 t)]
  congr 2
  · apply Vector.ext; intro i hi
    simp only [Vector.getElem_ofFn, assign_ne _ _ _ _ (role_ne_t1 t i)]
  · rw [show kAvx512 t = 64 * t from rfl, table_lane mem gpr table l t (by omega), tableWord_k t l.val ht l.isLt]

/-- A first-block round leaves the schedule registers alone. -/
theorem firstRound_other (mem gpr l regs) (t : Nat) (r : Vreg) (low : 8 ≤ r.val) (high : r.val < 24) :
    laneRun mem gpr l (firstRound t) regs r = regs r := by
  -- Neither the seed, the word's addition, nor the tail writes a schedule register.
  rw [firstRound_eq]
  simp only [laneRun]
  have ne : r ≠ t1 := by
    simp only [ne_eq, Fin.ext_iff, t1, show ((24 : Vreg) : Nat) = 24 from rfl]; omega
  rw [tail_other _ _ _ _ _ _ low high]
  simp only [laneStep, assign_ne _ _ _ _ ne]

/-- A schedule step on one lane: the next word from the four words it reads. -/
theorem schedule_lane (mem gpr l regs) (t : Nat) :
    laneRun mem gpr l (scheduleCode t) regs (ring t) =
      regs (ring t) + sigma0 (regs (ring (t + 1))) + regs (ring (t + 9)) + sigma1 (regs (ring (t + 14))) := by
  -- The step adds the four words, with the two small sigmas built from rotations and a shift.
  simp only [scheduleCode, laneRun, laneStep, assign_same, assign_ne _ _ _ _ (ring_ne_tmp _ _),
    assign_ne _ _ _ _ (ring_add_ne t 1 (by decide)), assign_ne _ _ _ _ (ring_add_ne t 9 (by decide))]
  simp [tmp, assign, ternlog_96, sigma0, sigma1]
  ac_rfl

/-- A schedule step leaves every register below the last three temporaries alone, except the word it writes. -/
theorem schedule_other (mem gpr l regs) (t : Nat) (r : Vreg) (ne : r ≠ ring t) (high : r.val < 29) :
    laneRun mem gpr l (scheduleCode t) regs r = regs r := by
  -- The step writes its word and three temporaries above register 28.
  apply laneRun_other
  have := ne
  simp only [ne_eq, Fin.ext_iff, ring_val] at this
  simp only [scheduleCode, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true, dest, ne_eq,
    Option.some.injEq, Fin.ext_iff, tmp, ring_val]
  omega

/-- The working words after the first rounds of a block, round i reading constant k i and word w i. -/
def roundsTo (st : Vector UInt32 8) (k w : Nat → UInt32) (t : Nat) : Vector UInt32 8 :=
  (List.range t).foldl (fun cur i => round cur (k i) (w i)) st

/-- One more round. -/
theorem roundsTo_succ (st : Vector UInt32 8) (k w : Nat → UInt32) (t : Nat) :
    roundsTo st k w (t + 1) = round (roundsTo st k w t) (k t) (w t) := by
  -- The range up to t + 1 is the range up to t, then t.
  simp [roundsTo, List.range_succ]

/-- The first n indices, read from the finite range. -/
private theorem range_eq_finRange (n : Nat) : List.range n = (List.finRange n).map Fin.val := by
  -- Both lists hold the numbers below n, in order.
  apply List.ext_getElem <;> simp

/-- Compression as the working words after sixty-four rounds, added to the state. -/
theorem compress_rounds (st : Vector UInt32 8) (b : ByteArray) (start : Nat) :
    compress st b start =
      st.zipWith (· + ·) (roundsTo st (fun i => roundConstants[i]!) (fun i => (schedule b start)[i]!) 64) := by
  -- The specification's fold reads its constants and words in range, so the defaulted reads agree.
  have same : (fun cur (i : Fin 64) => round cur roundConstants[i] (schedule b start)[i]) =
      fun cur i => round cur roundConstants[i.val]! (schedule b start)[i.val]! := by
    funext cur i
    rw [getElem!_pos roundConstants i.val i.isLt, getElem!_pos (schedule b start) i.val i.isLt]
    rfl
  simp only [compress, roundsTo, range_eq_finRange, List.foldl_map]
  rw [same]

/-- The round constant of round i. -/
abbrev K (i : Nat) : UInt32 := roundConstants[i]!

/-- Word i of a block's schedule. -/
abbrev W (m : ByteArray) (i : Nat) : UInt32 := (schedule m 0)[i]!

/-- The first sixteen schedule words are the block's big-endian words. -/
theorem W_input (m : ByteArray) (i : Nat) (h : i < 16) : W m i = wordAt m (4 * i) := by
  -- Schedule words below 16 are the block's input words.
  rw [W, getElem!_pos (schedule m 0) i (by omega), schedule_input m 0 i h, Nat.zero_add]

/-- Later schedule words follow the four-term recurrence. -/
theorem W_next (m : ByteArray) (t : Nat) (h : t < 48) :
    W m (t + 16) = W m t + sigma0 (W m (t + 1)) + W m (t + 9) + sigma1 (W m (t + 14)) := by
  -- Read the recurrence at index t + 16.
  simp only [W]
  rw [getElem!_pos (schedule m 0) (t + 16) (by omega), schedule_recurrence m 0 (t + 16) (by omega) (by omega),
    getElem!_pos (schedule m 0) t (by omega), getElem!_pos (schedule m 0) (t + 1) (by omega),
    getElem!_pos (schedule m 0) (t + 9) (by omega), getElem!_pos (schedule m 0) (t + 14) (by omega)]
  simp only [show t + 16 - 16 = t by omega, show t + 16 - 15 = t + 1 by omega, show t + 16 - 7 = t + 9 by omega,
    show t + 16 - 2 = t + 14 by omega]

/-- One lane of the first block before round t: the working words, and the schedule words not yet consumed. -/
def FirstInv (m : ByteArray) (t : Nat) (regs : Vreg → UInt32) : Prop :=
  (Vector.ofFn fun j : Fin 8 => regs (role t j)) = roundsTo initialState K (W m) t ∧
  ∀ u, t ≤ u → u < t + 16 → u < 64 → regs (ring u) = W m u

/-- One first-block round with its schedule step. -/
def firstStep (t : Nat) : List Instr := firstRound t ++ (if t < 48 then scheduleCode t else [])

/-- The schedule registers are 8 to 23. -/
theorem ring_range (u : Nat) : 8 ≤ (ring u).val ∧ (ring u).val < 24 := by
  simp only [ring_val]; omega

/-- A first-block round and its schedule step keep the invariant one round on. -/
theorem first_step (mem gpr l) (table : TableAt mem (gpr tbl).toNat) (m : ByteArray) (t : Nat) (ht : t < 64)
    (regs : Vreg → UInt32) (inv : FirstInv m t regs) :
    FirstInv m (t + 1) (laneRun mem gpr l (firstStep t) regs) := by
  -- The working words take one round, and the schedule window moves one word on.
  obtain ⟨roles, rings⟩ := inv
  -- The schedule step never touches a working word.
  have sched_role : ∀ j, laneRun mem gpr l (if t < 48 then scheduleCode t else [])
      (laneRun mem gpr l (firstRound t) regs) (role (t + 1) j) =
      laneRun mem gpr l (firstRound t) regs (role (t + 1) j) := by
    intro j
    split
    · apply schedule_other
      · simp only [ne_eq, Fin.ext_iff, ring_val]; have := role_lt (t + 1) j; omega
      · have := role_lt (t + 1) j; omega
    · rfl
  constructor
  · simp only [firstStep, laneRun_append, sched_role]
    rw [firstRound_lane mem gpr l regs table t ht, roles, rings t (by omega) (by omega) ht, roundsTo_succ]
  -- Each schedule word in the new window is either kept or the one this step computes.
  · intro u lo hi top
    simp only [firstStep, laneRun_append]
    have r1 : ∀ v, laneRun mem gpr l (firstRound t) regs (ring v) = regs (ring v) := fun v =>
      firstRound_other mem gpr l regs t _ (ring_range v).1 (ring_range v).2
    split
    · rename_i early
      by_cases last : u = t + 16
      · subst last
        rw [ring_add_sixteen, schedule_lane, r1, r1, r1, r1, rings t (by omega) (by omega) (by omega),
          rings (t + 1) (by omega) (by omega) (by omega), rings (t + 9) (by omega) (by omega) (by omega),
          rings (t + 14) (by omega) (by omega) (by omega), W_next m t early]
      · rw [schedule_other, r1, rings u (by omega) (by omega) top]
        · simp only [ne_eq, Fin.ext_iff, ring_val]; omega
        · have := ring_range u; omega
    · simp only [laneRun]
      rw [r1, rings u (by omega) (by omega) top]

/-- The initial state's eight words, loaded into every lane. -/
def ivCode : List Instr := (List.range 8).map fun j => .vload (home j) (tableEntry (ivAvx512 j))

/-- The first block's sixty-four rounds and their schedule steps. -/
def firstBlock : List Instr := (List.range 64).flatMap firstStep

/-- The feed-forward of the first block, kept aside for the second one. -/
def feed : List Instr :=
  (List.range 8).flatMap fun j => [.vaddMem (home j) (home j) (tableEntry (ivAvx512 j)), .vmov (ring j) (home j)]

/-- The padding block's sixty-four rounds. -/
def paddingBlockCode : List Instr := (List.range 64).flatMap paddingRound

/-- The feed-forward of the padding block. -/
def finish : List Instr := (List.range 8).map fun j => .vadd (home j) (home j) (ring j)

/-- Everything between loading the messages and storing the digests. -/
def core : List Instr := ivCode ++ firstBlock ++ feed ++ paddingBlockCode ++ finish

/-- A batch is the moves in, the compute core, and the moves out. -/
theorem batchCode_eq (ls rs : Nat) :
    batchCode ls rs = (loadCode ls rs ++ transposeIn ++ swapIn) ++ core ++ (transposeOut ++ storeCode) := by
  simp only [batchCode, core, ivCode, firstBlock, feed, paddingBlockCode, finish, List.append_assoc]
  rfl

/-- Before the first round, working word j is in register j. -/
theorem home_eq_role (j : Nat) (hj : j < 8) : home j = role 0 j := by
  -- At round zero the roles are the identity.
  apply Fin.ext; simp only [role, home]; omega

/-- After sixty-four rounds, working word j is back in register j. -/
theorem home_eq_role64 (j : Nat) (hj : j < 8) : home j = role 64 j := by
  -- Sixty-four rounds turn the roles eight full times.
  apply Fin.ext; simp only [role, home]; omega

/-- The first eight indices. -/
theorem range8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl

/-- After the initial-state loads, register j holds word j of the initial state. -/
theorem ivCode_lane (mem gpr l regs) (table : TableAt mem (gpr tbl).toNat) (j : Nat) (hj : j < 8) :
    laneRun mem gpr l ivCode regs (home j) = initialState[j]! := by
  -- Each of the eight words is loaded from its table row.
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  have row : ∀ i, i < 8 → readWord mem ((gpr (tableEntry (ivAvx512 i)).base).toNat + (tableEntry (ivAvx512 i)).disp + 4 * l.val) =
      initialState[i]! := fun i hi => by
    rw [show ivAvx512 i = 64 * (128 + i) by simp only [ivAvx512]; omega, table_lane mem gpr table l _ (by omega),
      tableWord_iv i l.val hi l.isLt]
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [ivCode, range8, List.map_cons, List.map_nil, laneRun, laneStep, assign_apply, home] <;>
    simp [row]

/-- The initial-state loads leave registers 8 and up alone. -/
theorem ivCode_other (mem gpr l regs) (r : Vreg) (low : 8 ≤ r.val) :
    laneRun mem gpr l ivCode regs r = regs r := by
  -- The loads write only registers 0 to 7.
  apply laneRun_other
  simp only [ivCode, range8, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil, false_implies,
    implies_true, and_true, dest, ne_eq, Option.some.injEq, Fin.ext_iff, home]
  omega

/-- The first block's invariant holds before its first round. -/
theorem first_start (mem gpr l regs) (table : TableAt mem (gpr tbl).toNat) (m : ByteArray)
    (words : ∀ t < 16, regs (ring t) = wordAt m (4 * t)) : FirstInv m 0 (laneRun mem gpr l ivCode regs) := by
  -- The working words are the initial state, and the schedule window is the input words.
  constructor
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, roundsTo, List.range_zero, List.foldl_nil]
    rw [← home_eq_role i hi, ivCode_lane mem gpr l regs table i hi, getElem!_pos initialState i hi]
  · intro u _ hi _
    rw [ivCode_other _ _ _ _ _ (ring_range u).1, words u (by omega), W_input m u (by omega)]

/-- The first block's invariant holds after any number of its rounds. -/
theorem first_block (mem gpr l regs) (table : TableAt mem (gpr tbl).toNat) (m : ByteArray)
    (start : FirstInv m 0 regs) (t : Nat) (ht : t ≤ 64) :
    FirstInv m t (laneRun mem gpr l ((List.range t).flatMap firstStep) regs) := by
  -- Induction on the rounds, one step at a time.
  induction t with
  | zero => exact start
  | succ t ih =>
    rw [laneRun_flatMap_succ]
    exact first_step mem gpr l table m t (by omega) _ (ih (by omega))

/-- Word i of the padding block's schedule. -/
abbrev PW (i : Nat) : UInt32 := (schedule paddingBlock 0)[i]!

/-- One lane of the padding block before round t: the working words, and the first block's result kept aside. -/
def PadInv (mid : Vector UInt32 8) (t : Nat) (regs : Vreg → UInt32) : Prop :=
  (Vector.ofFn fun j : Fin 8 => regs (role t j)) = roundsTo mid K PW t ∧
  ∀ j < 8, regs (ring j) = mid[j]!

/-- The feed-forward adds the initial state to each working word and keeps a copy aside. -/
theorem feed_lane (mem gpr l regs) (table : TableAt mem (gpr tbl).toNat) (j : Nat) (hj : j < 8) :
    laneRun mem gpr l feed regs (home j) = regs (home j) + initialState[j]! ∧
    laneRun mem gpr l feed regs (ring j) = regs (home j) + initialState[j]! := by
  -- Each of the eight words gains its initial-state word, and a copy is kept aside.
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  have row : ∀ i, i < 8 → readWord mem ((gpr (tableEntry (ivAvx512 i)).base).toNat + (tableEntry (ivAvx512 i)).disp + 4 * l.val) =
      initialState[i]! := fun i hi => by
    rw [show ivAvx512 i = 64 * (128 + i) by simp only [ivAvx512]; omega, table_lane mem gpr table l _ (by omega),
      tableWord_iv i l.val hi l.isLt]
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [feed, range8, List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
      List.append_nil, laneRun, laneStep, assign_apply, home, ring] <;>
    simp [row]

/-- The padding block's invariant holds before its first round, with the first block's result kept aside. -/
theorem feed_start (mem gpr l regs) (table : TableAt mem (gpr tbl).toNat) (m : ByteArray)
    (inv : FirstInv m 64 regs) :
    PadInv (compress initialState m 0) 0 (laneRun mem gpr l feed regs) := by
  -- The first compression is the initial state plus the working words after sixty-four rounds.
  have mid : ∀ j (hj : j < 8), (compress initialState m 0)[j] = initialState[j]! + regs (home j) := by
    intro j hj
    have := congrArg (·[j]) inv.1
    simp only [Vector.getElem_ofFn] at this
    rw [compress_rounds, Vector.getElem_zipWith, ← this, home_eq_role64 j hj, getElem!_pos initialState j hj]
  constructor
  · apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, roundsTo, List.range_zero, List.foldl_nil]
    rw [← home_eq_role i hi, (feed_lane mem gpr l regs table i hi).1, mid i hi, UInt32.add_comm]
  · intro j hj
    rw [(feed_lane mem gpr l regs table j hj).2, getElem!_pos (compress initialState m 0) j hj, mid j hj,
      UInt32.add_comm]

/-- A padding round keeps the invariant one round on. -/
theorem pad_step (mem gpr l) (table : TableAt mem (gpr tbl).toNat) (mid : Vector UInt32 8) (t : Nat) (ht : t < 64)
    (regs : Vreg → UInt32) (inv : PadInv mid t regs) :
    PadInv mid (t + 1) (laneRun mem gpr l (paddingRound t) regs) := by
  -- The padding round's seed reads H plus the precomputed constant and word, and the copy stays.
  obtain ⟨roles, rings⟩ := inv
  constructor
  · apply Vector.ext
    intro j hj
    simp only [Vector.getElem_ofFn, paddingRound, roundCode_eq, laneRun]
    rw [tail_lane _ _ _ _ _ _ hj, roundsTo_succ, round_eq_roundT, ← roles]
    simp only [laneStep, assign_same]
    congr 2
    · apply Vector.ext; intro i hi
      simp only [Vector.getElem_ofFn, assign_ne _ _ _ _ (role_ne_t1 t i)]
    · rw [show padAvx512 t = 64 * (64 + t) by simp only [padAvx512]; omega, table_lane mem gpr table l _ (by omega),
        tableWord_pad t l.val ht l.isLt, Vector.getElem_ofFn, UInt32.add_assoc]
  · intro j hj
    simp only [paddingRound, roundCode_eq, laneRun]
    rw [tail_other _ _ _ _ _ _ (ring_range j).1 (ring_range j).2]
    simp only [laneStep, assign_ne _ _ _ _ (ring_ne_t1 j)]
    exact rings j hj

/-- The padding block's invariant holds after any number of its rounds. -/
theorem pad_block (mem gpr l) (table : TableAt mem (gpr tbl).toNat) (mid : Vector UInt32 8) (regs : Vreg → UInt32)
    (start : PadInv mid 0 regs) (t : Nat) (ht : t ≤ 64) :
    PadInv mid t (laneRun mem gpr l ((List.range t).flatMap paddingRound) regs) := by
  -- Induction on the rounds, one step at a time.
  induction t with
  | zero => exact start
  | succ t ih =>
    rw [laneRun_flatMap_succ]
    exact pad_step mem gpr l table mid t (by omega) _ (ih (by omega))

/-- The final feed-forward adds the copy kept aside to each working word. -/
theorem finish_lane (mem gpr l regs) (j : Nat) (hj : j < 8) :
    laneRun mem gpr l finish regs (home j) = regs (home j) + regs (ring j) := by
  -- Each of the eight words adds its kept copy.
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
  rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [finish, range8, List.map_cons, List.map_nil, laneRun, laneStep, assign_apply, home, ring] <;>
    simp

/-- One lane of the whole compute core: two compressions of that lane's message. -/
theorem core_lane (mem gpr l regs) (table : TableAt mem (gpr tbl).toNat) (m : ByteArray)
    (words : ∀ t < 16, regs (ring t) = wordAt m (4 * t)) (j : Nat) (hj : j < 8) :
    laneRun mem gpr l core regs (home j) = (compress (compress initialState m 0) paddingBlock 0)[j] := by
  -- Run the first block, the feed-forward, the padding block, and the final feed-forward.
  simp only [core, laneRun_append]
  have first := first_block mem gpr l _ table m (first_start mem gpr l regs table m words) 64 (Nat.le_refl _)
  have pad := pad_block mem gpr l table _ _ (feed_start mem gpr l _ table m first) 64 (Nat.le_refl _)
  rw [firstBlock, paddingBlockCode, finish_lane _ _ _ _ j hj, pad.2 j hj]
  have := congrArg (·[j]) pad.1
  simp only [Vector.getElem_ofFn] at this
  rw [← home_eq_role64 j hj] at this
  rw [this, compress_rounds _ paddingBlock 0, Vector.getElem_zipWith, getElem!_pos _ j hj, UInt32.add_comm]

/-- A first-block round and its schedule step are all lanewise. -/
theorem firstStep_all (t : Nat) : (firstStep t).all lanewise = true := by
  -- Every instruction of a round and of a schedule step is lanewise.
  unfold firstStep
  split <;> simp [firstRound_eq, roundTail, roundCode, scheduleCode, lanewise]

/-- The compute core is all lanewise. -/
theorem core_lanewise : ∀ i ∈ core, lanewise i := by
  -- Every part of the core is made of lanewise instructions.
  rw [← List.all_eq_true]
  simp only [core, ivCode, firstBlock, feed, paddingBlockCode, finish, paddingRound, roundCode,
    List.all_append, List.all_map, List.all_flatMap, firstStep_all]
  simp [lanewise]

set_option maxRecDepth 100000 in
/--
The compute core: from the sixteen messages' input words, each lane ends with its message's two compressions.

Only vector registers change.
-/
theorem core_spec (s : State) (table : TableAt s.mem (s.gpr tbl).toNat) (m : Fin 16 → ByteArray)
    (words : ∀ t < 16, ∀ p, s.vec (ring t) p = wordAt (m p) (4 * t)) :
    (∀ j (hj : j < 8), ∀ p,
      (exec core s).vec (home j) p = (compress (compress initialState (m p) 0) paddingBlock 0)[j]) ∧
    (exec core s).gpr = s.gpr ∧ (exec core s).mem = s.mem ∧ (exec core s).zf = s.zf := by
  -- The core runs lane by lane, and each lane computes its own two compressions.
  have h := exec_lanewise core core_lanewise s
  refine ⟨fun j hj p => ?_, by rw [h], by rw [h], by rw [h]⟩
  refine (congrArg (fun s : State => s.vec (home j) p) h).trans ?_
  exact core_lane s.mem s.gpr p (fun r => s.vec r p) table (m p) (fun t ht => words t ht p) j hj
