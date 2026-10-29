import SszNative.Proofs.Asm.Run
import SszNative.Proofs.Asm.Spec
import SszNative.Proofs.Kernel.Sha256
import SszNative.Kernel.ShaNi

/-! Facts the SHA-NI kernel's proof leans on: register frames, byte shuffles, table words, and rounds. -/

namespace Ssz.Native.Kernel.ShaNi

open Ssz.Native.Asm Ssz.Sha256

/-- The vector register an instruction writes, when it writes one and touches nothing else. -/
def writes : Instr → Option Vreg
  | .vload d _ | .vloadHalf d _ | .vinsertHigh d _ _ | .vmov d _ | .vadd d _ _ | .vaddMem d _ _
  | .vror d _ _ | .vshr d _ _ | .vternlog d _ _ _ | .vshufb d _ _ | .vshufps d _ _ _ | .vpermi2q d _ _
  | .vpermi2d d _ _ | .movdqu d _ | .movdqa d _ | .paddd d _ | .padddMem d _ | .pshufb d _ | .pshufd d _ _
  | .palignr d _ _ | .pblendw d _ _ | .sha256rnds2 d _ | .sha256msg1 d _ | .sha256msg2 d _ => some d
  | _ => none

/-- A register-only instruction leaves the general registers, memory, and the flag alone. -/
theorem writes_frame (i : Instr) (d : Vreg) (h : writes i = some d) (s : State) :
    (exec1 i s).gpr = s.gpr ∧ (exec1 i s).mem = s.mem ∧ (exec1 i s).zf = s.zf := by
  -- Each register-only instruction updates one vector register and nothing else.
  cases i <;> simp_all [writes, exec1]

/-- A register-only instruction leaves every other vector register alone. -/
theorem writes_other (i : Instr) (d v : Vreg) (h : writes i = some d) (ne : v ≠ d) (s : State) :
    (exec1 i s).vec v = s.vec v := by
  -- Each register-only instruction assigns only its destination.
  cases i <;> simp_all [writes, exec1, assign]

/-- Whether every instruction of a block writes one vector register and nothing else. -/
def VecOnly (body : List Instr) : Prop := ∀ i ∈ body, (writes i).isSome

/-- A register-only block leaves the general registers, memory, and the flag alone. -/
theorem exec_frame (body : List Instr) (h : VecOnly body) (s : State) :
    (exec body s).gpr = s.gpr ∧ (exec body s).mem = s.mem ∧ (exec body s).zf = s.zf := by
  induction body generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons i rest ih =>
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (h i (by simp))
    -- The first instruction keeps them, and so does the rest of the block.
    obtain ⟨g, m, z⟩ := writes_frame i d hd s
    obtain ⟨g', m', z'⟩ := ih (fun j hj => h j (by simp [hj])) (exec1 i s)
    simp only [exec_cons]
    exact ⟨g'.trans g, m'.trans m, z'.trans z⟩

/-- A block leaves alone every vector register none of its instructions writes. -/
theorem exec_vec (body : List Instr) (h : VecOnly body) (v : Vreg) (keep : ∀ i ∈ body, writes i ≠ some v)
    (s : State) : (exec body s).vec v = s.vec v := by
  induction body generalizing s with
  | nil => rfl
  | cons i rest ih =>
    -- The first instruction leaves the register alone, and so does the rest of the block.
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (h i (by simp))
    simp only [exec_cons]
    rw [ih (fun j hj => h j (by simp [hj])) (fun j hj => keep j (by simp [hj]))]
    exact writes_other i d v hd (fun e => keep i (by simp) (e ▸ hd)) s

/-- A word's low byte, widened back, is the word masked to its low eight bits. -/
theorem low_byte (x : UInt32) : x.toUInt8.toUInt32 = x &&& 255 := by
  -- Masking to the low eight bits keeps the value modulo 256.
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, show (255 : UInt32).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp

/-- A word modulo 256 is the word masked to its low eight bits. -/
theorem mod_byte (x : UInt32) : x % 256 = x &&& 255 := by
  -- Masking to the low eight bits keeps the value modulo 256.
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, show (255 : UInt32).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp

/-- Two words with the same low eight bits have the same low byte. -/
theorem byte_eq (a b : UInt32) (h : a &&& 255 = b &&& 255) : a.toUInt8 = b.toUInt8 := by
  -- The widened bytes are equal, and widening loses nothing.
  have : a.toUInt8.toUInt32 = b.toUInt8.toUInt32 := by rw [low_byte, low_byte, h]
  exact UInt8.toUInt32_inj.mp this

/-- Prove a word identity bit by bit, for each of the thirty-two bits. -/
macro "bits" : tactic => `(tactic| (
  try simp only [low_byte, mod_byte]
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
  simp))

/-- Lanes 0 to 3 hold four words. -/
def Quad (v : Lanes) (a b c d : UInt32) : Prop :=
  v 0 = a ∧ v 1 = b ∧ v 2 = c ∧ v 3 = d

/-- Two registers hold a state as the SHA instructions read it: A, B, E, F and C, D, G, H, from the top lane down. -/
def Packed (abef cdgh : Lanes) (st : Vector UInt32 8) : Prop :=
  Quad abef st[5] st[4] st[1] st[0] ∧ Quad cdgh st[7] st[6] st[3] st[2]

/-- A word with its four bytes in reverse order. -/
def bswap32 (w : UInt32) : UInt32 :=
  (w >>> (24 : UInt32)) ||| ((w >>> (8 : UInt32)) &&& (0xFF00 : UInt32)) |||
    ((w <<< (8 : UInt32)) &&& (0xFF0000 : UInt32)) ||| (w <<< (24 : UInt32))

/-- The byte-reversal mask turns each of the low four lanes around. -/
theorem shuffle_reverse (v mask : Lanes)
    (h0 : mask 0 = reverseLane 0) (h1 : mask 1 = reverseLane 1) (h2 : mask 2 = reverseLane 2)
    (h3 : mask 3 = reverseLane 3) (l : Fin 16) (hl : l.val < 4) :
    ofBytes (shuffleBytes v mask) l = bswap32 (v l) := by
  -- Each of the four lanes reads its own bytes, highest first.
  rcases l with ⟨_ | _ | _ | _ | l, hl'⟩
  all_goals first
    | (simp at hl; omega)
    | simp +decide [ofBytes, shuffleBytes, laneByte, laneOf, wordByte, h0, h1, h2, h3, reverseLane, bswap32]
      bits

/-- A little-endian word read and reversed is the big-endian word at that address. -/
theorem bswap32_readWord (mem : Nat → UInt8) (a : Nat) :
    bswap32 (readWord mem a) = (mem a).toUInt32 <<< 24 ||| (mem (a + 1)).toUInt32 <<< 16 |||
      (mem (a + 2)).toUInt32 <<< 8 ||| (mem (a + 3)).toUInt32 := by
  -- Name the four bytes, then compare the words bit by bit.
  simp only [readWord, bswap32]
  generalize mem a = b₀
  generalize mem (a + 1) = b₁
  generalize mem (a + 2) = b₂
  generalize mem (a + 3) = b₃
  bits

/-- Byte k of a reversed word, as the digest writes it: the most significant byte first. -/
theorem wordByte_bswap32 (w : UInt32) (k : Nat) :
    wordByte (bswap32 w) k = (w >>> (24 - 8 * UInt32.ofNat (k % 4))).toUInt8 := by
  -- Each byte position of a word is one of four cases, checked bit by bit.
  have : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases this with h | h | h | h <;>
    simp only [wordByte, h, bswap32, Nat.reduceMul, Nat.toUInt32, UInt32.reduceOfNat] <;> apply byte_eq <;> bits

/-- A word of the table, at a 4-aligned offset from the table's register. -/
theorem read_table (s : State) (table : TableAt s.mem (s.gpr tbl).toNat) (off l : Nat)
    (aligned : off % 4 = 0) (within : off / 4 + l < tableSize / 4) :
    readWord s.mem (s.addr ⟨tbl, off⟩ + 4 * l) = tableWord (off / 4 + l) := by
  -- The table holds its words little-endian from its base address.
  rw [← readWord_table s.mem _ table (off / 4 + l) within]
  congr 1
  simp only [State.addr]
  omega

/-- The table's four-lane round constants. -/
theorem tableWord_k (r l : Nat) (hr : r < 16) (hl : l < 4) :
    tableWord (kShaNi r / 4 + l) = roundConstants[4 * r + l]! := by
  -- The offset falls in the four-lane constants' part of the table.
  unfold kShaNi
  unfold tableWord
  simp (disch := omega) only [if_neg, if_pos]
  exact congrArg (roundConstants[·]!) (by omega)

/-- The table's four-lane padding words plus constants. -/
theorem tableWord_pad (r l : Nat) (hr : r < 16) (hl : l < 4) :
    tableWord (padShaNi r / 4 + l) = paddingWK (4 * r + l) := by
  -- The offset falls in the four-lane padding words' part of the table.
  unfold padShaNi
  unfold tableWord
  simp (disch := omega) only [if_neg, if_pos]
  exact congrArg paddingWK (by omega)

/-- The table's four-lane byte-reversal mask. -/
theorem tableWord_reverse (l : Nat) (hl : l < 4) : tableWord (bswapShaNi / 4 + l) = reverseLane l := by
  -- The offset falls in the four-lane byte-reversal mask's part of the table.
  unfold bswapShaNi
  unfold tableWord
  simp (disch := omega) only [if_neg]
  exact congrArg reverseLane (by omega)

/-- The table's initial state, as ABEF and CDGH. -/
theorem tableWord_iv :
    Packed (fun l => tableWord (ivAbef / 4 + l.val)) (fun l => tableWord (ivCdgh / 4 + l.val)) initialState := by
  -- Each of the eight words is a literal, checked by evaluation.
  simp only [Packed, Quad]
  decide

/-- The state after the first rounds, each from a constant and a word. -/
def rounds (st : Vector UInt32 8) (k w : Nat → UInt32) : Nat → Vector UInt32 8
  | 0 => st
  | n + 1 => round (rounds st k w n) (k n) (w n)

/-- Folding over the first indices is counting up through them. -/
theorem foldl_finRange (n : Nat) (f : Vector UInt32 8 → Nat → Vector UInt32 8) (st : Vector UInt32 8) :
    (List.finRange n).foldl (fun c i => f c i.val) st =
      Nat.rec (motive := fun _ => Vector UInt32 8) st (fun j acc => f acc j) n := by
  induction n with
  -- The last index folds last, after the fold over the others.
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
    simp only [Fin.val_castSucc, List.foldl_cons, List.foldl_nil, Fin.val_last]
    rw [ih]

/-- Compression is the feed-forward of sixty-four rounds. -/
theorem compress_rounds (st : Vector UInt32 8) (block : ByteArray) (start : Nat) :
    compress st block start =
      st.zipWith (· + ·) (rounds st (fun i => roundConstants[i]!) (fun i => (schedule block start)[i]!) 64) := by
  -- Both fold the same rounds over the same indices.
  simp only [compress]
  congr 1

/-- The fourth lane's index, which simp does not compute on its own. -/
@[simp] theorem lane_three : ((3 : Fin 16) : Nat) = 3 := rfl

/-- Unfold an instruction's effect on one lane down to literal arithmetic. -/
macro "lanes" : tactic => `(tactic| simp only [exec1, assign, low, ofBytes, laneByte, laneOf, wordByte, ↓reduceIte,
  eq_self_iff_true, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceLT,
  Nat.toUInt32, UInt32.reduceOfNat])

/-- Shifting a pair of registers right by four bytes: the source's upper three lanes, then the destination's first. -/
theorem palignr4 (s : State) (d r : Vreg) (l : Fin 16) (hl : l.val < 4) :
    (exec1 (.palignr d r 4) s).vec d l = if h : l.val < 3 then s.vec r ⟨l.val + 1, by omega⟩ else s.vec d 0 := by
  -- Each of the four low lanes is computed and compared bit by bit.
  rcases l with ⟨_ | _ | _ | _ | l, hl'⟩
  all_goals first
    | (simp at hl; omega)
    | (lanes; bits)

/-- Shifting a pair of registers right by eight bytes: the source's upper two lanes, then the destination's lower two. -/
theorem palignr8 (s : State) (d r : Vreg) (l : Fin 16) (hl : l.val < 4) :
    (exec1 (.palignr d r 8) s).vec d l =
      if h : l.val < 2 then s.vec r ⟨l.val + 2, by omega⟩ else s.vec d ⟨l.val - 2, by omega⟩ := by
  -- Each of the four low lanes is computed and compared bit by bit.
  rcases l with ⟨_ | _ | _ | _ | l, hl'⟩
  all_goals first
    | (simp at hl; omega)
    | (lanes; bits)

/-- Blending the upper four half-lanes: the destination's lower two lanes, then the source's upper two. -/
theorem pblendw_high (s : State) (d r : Vreg) (l : Fin 16) (hl : l.val < 4) :
    (exec1 (.pblendw d r 0xF0) s).vec d l = if l.val < 2 then s.vec d l else s.vec r l := by
  -- Each of the four low lanes is computed and compared bit by bit.
  rcases l with ⟨_ | _ | _ | _ | l, hl'⟩
  all_goals first
    | (simp at hl; omega)
    | (lanes; bits)

/-- What a load into the low lanes does. -/
theorem exec1_movdqu (d : Vreg) (m : Mem) (s : State) : exec1 (.movdqu d m) s =
    { s with vec := assign s.vec d (low (s.vec d) fun l => readWord s.mem (s.addr m + 4 * l.val)) } := rfl

/-- What a copy of the low lanes does. -/
theorem exec1_movdqa (d r : Vreg) (s : State) : exec1 (.movdqa d r) s =
    { s with vec := assign s.vec d (low (s.vec d) (s.vec r)) } := rfl

/-- What a lane-wise sum of two registers does. -/
theorem exec1_paddd (d r : Vreg) (s : State) : exec1 (.paddd d r) s =
    { s with vec := assign s.vec d (low (s.vec d) fun l => s.vec d l + s.vec r l) } := rfl

/-- What a lane-wise sum with memory does. -/
theorem exec1_padddMem (d : Vreg) (m : Mem) (s : State) : exec1 (.padddMem d m) s =
    { s with vec := assign s.vec d (low (s.vec d) fun l => s.vec d l + readWord s.mem (s.addr m + 4 * l.val)) } := rfl

/-- What a byte shuffle does. -/
theorem exec1_pshufb (d r : Vreg) (s : State) : exec1 (.pshufb d r) s =
    { s with vec := assign s.vec d (low (s.vec d) (ofBytes (shuffleBytes (s.vec d) (s.vec r)))) } := rfl

/-- What a lane shuffle does. -/
theorem exec1_pshufd (d r : Vreg) (imm : BitVec 8) (s : State) : exec1 (.pshufd d r imm) s =
    { s with vec := assign s.vec d (low (s.vec d) fun l => s.vec r ⟨(imm.toNat >>> (2 * l.val)) % 4, by omega⟩) } :=
  rfl

/-- What a 16-byte store does. -/
theorem exec1_movdquStore (m : Mem) (r : Vreg) (s : State) : exec1 (.movdquStore m r) s =
    { s with mem := store s.mem (s.addr m) 16 (laneByte (s.vec r)) } := rfl

/-- Lane l of a load's destination, for the low four lanes. -/
theorem lane_movdqu (t : State) (d : Vreg) (m : Mem) (l : Fin 16) (hl : l.val < 4) :
    (exec1 (.movdqu d m) t).vec d l = readWord t.mem (t.addr m + 4 * l.val) := by
  simp [exec1_movdqu, assign, low, hl]

/-- Lane l of a copy's destination, for the low four lanes. -/
theorem lane_movdqa (t : State) (d r : Vreg) (l : Fin 16) (hl : l.val < 4) :
    (exec1 (.movdqa d r) t).vec d l = t.vec r l := by
  simp [exec1_movdqa, assign, low, hl]

/-- Lane l of a sum's destination, for the low four lanes. -/
theorem lane_paddd (t : State) (d r : Vreg) (l : Fin 16) (hl : l.val < 4) :
    (exec1 (.paddd d r) t).vec d l = t.vec d l + t.vec r l := by
  simp [exec1_paddd, assign, low, hl]

/-- Lane l of a sum with memory, for the low four lanes. -/
theorem lane_padddMem (t : State) (d : Vreg) (m : Mem) (l : Fin 16) (hl : l.val < 4) :
    (exec1 (.padddMem d m) t).vec d l = t.vec d l + readWord t.mem (t.addr m + 4 * l.val) := by
  simp [exec1_padddMem, assign, low, hl]

/-- Lane l of a lane shuffle, for the low four lanes. -/
theorem lane_pshufd (t : State) (d r : Vreg) (imm : BitVec 8) (l : Fin 16) (hl : l.val < 4) :
    (exec1 (.pshufd d r imm) t).vec d l = t.vec r ⟨(imm.toNat >>> (2 * l.val)) % 4, by omega⟩ := by
  simp [exec1_pshufd, assign, low, hl]

/-- Lane l of a byte shuffle, for the low four lanes. -/
theorem lane_pshufb (t : State) (d r : Vreg) (l : Fin 16) (hl : l.val < 4) :
    (exec1 (.pshufb d r) t).vec d l = ofBytes (shuffleBytes (t.vec d) (t.vec r)) l := by
  simp [exec1_pshufb, assign, low, hl]

/-- Machines that agree on the general registers agree on every address. -/
theorem addr_congr (s t : State) (h : t.gpr = s.gpr) (m : Mem) : t.addr m = s.addr m := by
  -- An address reads only its base register.
  simp [State.addr, h]

/-- A register-only instruction keeps memory, the general registers, and every other register. -/
theorem step_frame (i : Instr) (d : Vreg) (h : writes i = some d) (s : State) :
    (exec1 i s).mem = s.mem ∧ (exec1 i s).gpr = s.gpr ∧ ∀ v, v ≠ d → (exec1 i s).vec v = s.vec v :=
  ⟨(writes_frame i d h s).2.1, (writes_frame i d h s).1, fun v hv => writes_other i d v h hv s⟩

end Ssz.Native.Kernel.ShaNi
