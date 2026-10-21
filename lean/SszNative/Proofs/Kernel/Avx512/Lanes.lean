import SszNative.Proofs.Asm.Run
import SszNative.Proofs.Kernel.Sha256

/-!
Where each lane comes from, after instructions that only move lanes between registers.

Shuffles, permutes, and table loads never compute new words.
Each lane then holds a starting lane, that lane byte-reversed, or a table constant.
Following those sources over a fixed list of instructions is a finite computation the kernel can check.
-/

namespace Ssz.Native.Asm

open Ssz.Native.Kernel

/-- A word with its four bytes in reverse order. -/
def bswap (w : UInt32) : UInt32 :=
  (w >>> 24) ||| ((w >>> 16) &&& 0xFF) <<< 8 ||| ((w >>> 8) &&& 0xFF) <<< 16 ||| (w &&& 0xFF) <<< 24

/-- Words agree when every one of their 32 bits does. -/
theorem word_ext {x y : UInt32} (h : ∀ i, i < 32 → x.toBitVec.getLsbD i = y.toBitVec.getLsbD i) : x = y :=
  UInt32.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq h)

/-- Bytes agree when every one of their 8 bits does. -/
theorem byte_ext {x y : UInt8} (h : ∀ i, i < 8 → x.toBitVec.getLsbD i = y.toBitVec.getLsbD i) : x = y :=
  UInt8.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq h)

/-- Reversing a word's bytes twice gives the word back. -/
theorem bswap_bswap (w : UInt32) : bswap (bswap w) = w := by
  -- One goal per bit position, each a fixed bit of the word.
  apply word_ext
  simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
  simp [bswap]

/-- Where a lane's word comes from. -/
inductive Src where
  /-- A lane of a register, as it was at the start. -/
  | reg (r : Vreg) (l : Fin 16)
  /-- A lane of a register at the start, byte-reversed. -/
  | swap (r : Vreg) (l : Fin 16)
  /-- A known word. -/
  | const (v : UInt32)
  /-- A lane nothing is known about. -/
  | bad
  deriving DecidableEq

/-- The word a source names, given the starting registers. -/
def Src.denote (v : Vreg → Lanes) : Src → UInt32
  | .reg r l => v r l
  | .swap r l => bswap (v r l)
  | .const c => c
  | .bad => 0

/-- A source byte-reversed. -/
def Src.swapped : Src → Src
  | .reg r l => .swap r l
  | .swap r l => .reg r l
  | .const c => .const (bswap c)
  | .bad => .bad

/-- A known source byte-reversed names the reversed word. -/
theorem Src.denote_swapped (v : Vreg → Lanes) (x : Src) (good : x.swapped ≠ .bad) :
    x.swapped.denote v = bswap (x.denote v) := by
  -- Reversing twice restores the word.
  cases x <;> simp_all [Src.swapped, Src.denote, bswap_bswap]

/-- The source of every lane of every register. -/
abbrev Abs := Vreg → Fin 16 → Src

/-- Every register lane is its own source, at the start. -/
def Abs.start : Abs := fun r l => .reg r l

/-- Whether an instruction only moves lanes, reading memory at most through the constant table. -/
def Instr.moves : Instr → Bool
  | .vload _ _ | .vmov _ _ | .vshufps _ _ _ _ | .vpermi2q _ _ _ | .vpermi2d _ _ _ | .vshufb _ _ _ => true
  | _ => false

/-- The sources after one instruction that moves lanes. -/
def absExec1 (i : Instr) (A : Abs) : Abs :=
  match i with
  | .vload d m =>
    -- Only a whole-row load from the table is known.
    if m.base = .r8 ∧ m.disp % 4 = 0 ∧ m.disp / 4 + 16 ≤ tableSize / 4 then
      assign A d fun l => .const (tableWord (m.disp / 4 + l.val))
    else assign A d fun _ => .bad
  | .vmov d r => assign A d (A r)
  | .vshufps d a b imm =>
    assign A d fun l =>
      let base := 4 * (l.val / 4)
      let field := (imm.toNat >>> (2 * (l.val % 4))) % 4
      let src := if l.val % 4 < 2 then A a else A b
      src ⟨base + field, by omega⟩
  | .vpermi2q d a b =>
    assign A d fun l =>
      match A d ⟨2 * (l.val / 2), by omega⟩ with
      | .const c =>
        let index := c.toNat
        let src := if index / 8 % 2 == 0 then A a else A b
        src ⟨2 * (index % 8) + l.val % 2, by omega⟩
      | _ => .bad
  | .vpermi2d d a b =>
    assign A d fun l =>
      match A d l with
      | .const c =>
        let index := c.toNat
        let src := if index / 16 % 2 == 0 then A a else A b
        src ⟨index % 16, by omega⟩
      | _ => .bad
  | .vshufb d a b =>
    -- Only the shuffle that reverses each lane's bytes is known.
    assign A d fun l =>
      match A b l with
      | .const c => if c = reverseLane l.val then (A a l).swapped else .bad
      | _ => .bad
  | _ => fun _ _ => .bad

/-- The sources after a list of instructions. -/
def absExec : List Instr → Abs → Abs
  | [], A => A
  | i :: rest, A => absExec rest (absExec1 i A)

/-- Whether every known lane of a state holds what its source names, in a starting state. -/
def Agrees (start : Vreg → Lanes) (A : Abs) (s : State) : Prop :=
  ∀ r l, A r l ≠ .bad → s.vec r l = (A r l).denote start

/-- Each byte of the byte-reversal mask names the mirrored byte of its own lane. -/
private theorem reverseLane_byte : ∀ l : Fin 16, ∀ b : Fin 4,
    -- Each of the 64 cases is checked by evaluation.
    wordByte (reverseLane l.val) (4 * l.val + b.val) = UInt8.ofNat (4 * (l.val % 4) + 3 - b.val) := by
  decide

/-- A small index byte has its top bit clear and names its own position. -/
private theorem index_bits : ∀ x : Fin 16,
    -- Each of the 16 cases is checked by evaluation.
    (UInt8.ofNat x.val &&& 0x80 != 0) = false ∧ (UInt8.ofNat x.val &&& 0x0F).toNat = x.val := by
  decide

/-- Byte b of lane l, for b below 4, lies in lane l. -/
private theorem laneOf_at (l : Fin 16) (b : Nat) (small : b < 4) : laneOf (4 * l.val + b) = l := by
  -- Byte 4 l + b, divided by four, is lane l.
  simp only [laneOf]
  ext
  simp only
  omega

/-- Byte b of lane l, through the shuffle with the byte-reversal index in lane l. -/
private theorem shuffle_byte (src mask : Lanes) (l : Fin 16) (h : mask l = reverseLane l.val) (b : Nat)
    (small : b < 4) : shuffleBytes src mask (4 * l.val + b) = wordByte (src l) (3 - b) := by
  -- The index byte names byte 3 - b of the same lane.
  have index : laneByte mask (4 * l.val + b) = UInt8.ofNat (4 * (l.val % 4) + 3 - b) := by
    rw [laneByte, laneOf_at l b small, h]
    exact reverseLane_byte l ⟨b, small⟩
  have bits := index_bits ⟨4 * (l.val % 4) + 3 - b, by omega⟩
  simp only [shuffleBytes, index, bits.1, Bool.false_eq_true, ↓reduceIte, bits.2]
  rw [show 16 * ((4 * l.val + b) / 16) + (4 * (l.val % 4) + 3 - b) = 4 * l.val + (3 - b) by omega]
  rw [laneByte, laneOf_at l (3 - b) (by omega)]
  simp only [wordByte]
  congr 3
  omega

/-- The shuffle with a byte-reversal index in a lane reverses that lane's bytes. -/
theorem shuffle_reverse (src mask : Lanes) (l : Fin 16) (h : mask l = reverseLane l.val) :
    ofBytes (shuffleBytes src mask) l = bswap (src l) := by
  -- Each of the four bytes reads its mirror, then the word is compared bit by bit.
  have e0 : shuffleBytes src mask (4 * l.val) = wordByte (src l) 3 := by
    simpa using shuffle_byte src mask l h 0 (by omega)
  simp only [ofBytes]
  rw [e0, shuffle_byte src mask l h 1 (by omega), shuffle_byte src mask l h 2 (by omega),
    shuffle_byte src mask l h 3 (by omega)]
  apply word_ext
  simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
  simp [bswap, wordByte, -UInt32.toUInt32_toUInt8]

/-- Writing a register keeps agreement when every known new lane holds its source's word. -/
theorem agrees_assign (start : Vreg → Lanes) (A : Abs) (s : State) (agrees : Agrees start A s)
    (d : Vreg) (F : Fin 16 → Src) (v : Lanes) (lanes : ∀ l, F l ≠ .bad → v l = (F l).denote start) :
    Agrees start (assign A d F) { s with vec := assign s.vec d v } := by
  -- The written register's lanes hold their sources, and every other register keeps its agreement.
  intro r l good
  simp only [assign] at good ⊢
  split
  · subst_vars
    simp only [↓reduceIte] at good
    exact lanes l good
  · simp only [*, ↓reduceIte] at good
    exact agrees r l good

/-- A source chosen by a condition agrees when both choices do. -/
private theorem pick_agrees (start : Vreg → Lanes) (A : Abs) (s : State) (agrees : Agrees start A s)
    (c : Prop) [Decidable c] (a b : Vreg) (l : Fin 16)
    (good : (if c then A a else A b) l ≠ .bad) :
    (if c then s.vec a else s.vec b) l = ((if c then A a else A b) l).denote start := by
  -- Whichever source is chosen, it agrees.
  by_cases hc : c
  · simp only [hc, ↓reduceIte] at good ⊢
    exact agrees a l good
  · simp only [hc, ↓reduceIte] at good ⊢
    exact agrees b l good

/-- One lane move keeps every known lane equal to what its source names. -/
theorem absExec1_sound (i : Instr) (moves : i.moves) (start : Vreg → Lanes) (A : Abs) (s : State)
    (agrees : Agrees start A s) (table : TableAt s.mem (s.gpr .r8).toNat) :
    Agrees start (absExec1 i A) (exec1 i s) := by
  -- Each kind of lane move is checked on its own.
  cases i <;> simp only [Instr.moves, Bool.false_eq_true] at moves
  case vload d m =>
    -- A table load is known lane by lane, and any other load forgets the register.
    by_cases inside : m.base = .r8 ∧ m.disp % 4 = 0 ∧ m.disp / 4 + 16 ≤ tableSize / 4
    · simp only [absExec1, inside, and_self, ↓reduceIte]
      apply agrees_assign start A s agrees
      intro l _
      have := l.isLt
      simp only [Src.denote, State.addr, inside.1]
      rw [show (s.gpr .r8).toNat + m.disp + 4 * l.val = (s.gpr .r8).toNat + 4 * (m.disp / 4 + l.val) by omega]
      exact readWord_table _ _ table _ (by omega)
    · simp only [absExec1, inside, ↓reduceIte]
      exact agrees_assign start A s agrees _ _ _ fun _ good => absurd rfl good
  case vmov d a =>
    -- A copy moves each lane's source.
    exact agrees_assign start A s agrees _ _ _ fun l good => agrees a l good
  case vshufps d a b imm =>
    -- A lane shuffle takes each lane from one of the two sources.
    exact agrees_assign start A s agrees _ _ _ fun l good => pick_agrees start A s agrees _ a b _ good
  case vpermi2q d a b =>
    -- A known index picks a known source lane, and an unknown index forgets the lane.
    apply agrees_assign start A s agrees
    intro l good
    split at good
    · rename_i c hc
      have index := agrees d ⟨2 * (l.val / 2), by omega⟩ (by simp [hc])
      simp only [hc, Src.denote] at index
      simp only [index]
      exact pick_agrees start A s agrees _ a b _ good
    · exact absurd rfl good
  case vpermi2d d a b =>
    -- A known index picks a known source lane, and an unknown index forgets the lane.
    apply agrees_assign start A s agrees
    intro l good
    split at good
    · rename_i c hc
      have index := agrees d l (by simp [hc])
      simp only [hc, Src.denote] at index
      simp only [index]
      exact pick_agrees start A s agrees _ a b _ good
    · exact absurd rfl good
  case vshufb d a b =>
    -- The byte-reversal mask reverses the source lane, and any other mask forgets it.
    apply agrees_assign start A s agrees
    intro l good
    split at good
    · rename_i c hc
      split at good
      · rename_i rev
        have mask := agrees b l (by simp [hc])
        simp only [hc, Src.denote, rev] at mask
        simp only [rev, ↓reduceIte]
        rw [shuffle_reverse _ _ l mask, Src.denote_swapped _ _ good]
        have known : A a l ≠ .bad := by
          intro e
          simp [e, Src.swapped] at good
        rw [agrees a l known]
      · exact absurd rfl good
    · exact absurd rfl good

/-- A lane move leaves memory, the general registers, and the zero flag alone. -/
theorem exec1_moves (i : Instr) (moves : i.moves) (s : State) :
    (exec1 i s).mem = s.mem ∧ (exec1 i s).gpr = s.gpr ∧ (exec1 i s).zf = s.zf := by
  -- Lane moves write only vector registers.
  cases i <;> simp_all [Instr.moves, exec1]

/-- A list of lane moves keeps every known lane equal to what its source names, and touches only vector registers. -/
theorem absExec_sound (body : List Instr) (moves : body.all Instr.moves) (start : Vreg → Lanes) (A : Abs)
    (s : State) (agrees : Agrees start A s) (table : TableAt s.mem (s.gpr .r8).toNat) :
    Agrees start (absExec body A) (exec body s) ∧
      (exec body s).mem = s.mem ∧ (exec body s).gpr = s.gpr ∧ (exec body s).zf = s.zf := by
  induction body generalizing A s with
  -- No instructions keep the agreement.
  | nil => exact ⟨agrees, rfl, rfl, rfl⟩
  | cons i rest ih =>
    -- The first move keeps it, and so does the rest, by induction.
    simp only [List.all_cons, Bool.and_eq_true] at moves
    have same := exec1_moves i moves.1 s
    have := ih moves.2 (absExec1 i A) (exec1 i s) (absExec1_sound i moves.1 start A s agrees table)
      (by rw [same.1, same.2.1]; exact table)
    simp only [exec_cons, absExec]
    exact ⟨this.1, this.2.1.trans same.1, this.2.2.1.trans same.2.1, this.2.2.2.trans same.2.2⟩

/-- Every lane is its own source at the start. -/
theorem agrees_start (s : State) : Agrees s.vec Abs.start s := by
  -- Every lane names itself.
  intro r l _
  rfl

end Ssz.Native.Asm
