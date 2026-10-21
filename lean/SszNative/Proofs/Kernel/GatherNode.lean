import SszNative.Proofs.Kernel.Gather

/-!
The gathering routines for one field width, run on the machine model: each field lands in its zero-padded slot.

```text
    source:   [ field 0 | skip ][ field 1 | skip ] ...    a width plus a skip apart
    output:   [ field 0 | zeros ][ field 1 | zeros ] ...  one slot apart
```

One zero-extending load and one or two stores move a whole slot, so no byte copy runs.
-/

namespace Ssz.Native.Asm

/-- Byte j of a word read from memory is the memory byte j places on. -/
theorem readWord_byte (mem : Nat → UInt8) (a j : Nat) (hj : j < 4) :
    wordByte (readWord mem a) j = mem (a + j) := by
  -- Each of the four byte positions, checked bit by bit.
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
  · simp only [wordByte, readWord]
    apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
    simp [-UInt32.toUInt32_toUInt8]

/-- Every byte of a zero word is zero. -/
theorem zero_byte (j : Nat) : wordByte 0 j = 0 := by
  simp [wordByte]

/-- A byte loaded into a register and moved into a lane fills only the lane's lowest byte. -/
theorem byte_lane (b : UInt8) (j : Nat) (hj : j < 4) :
    wordByte b.toUInt32 j = if j = 0 then b else 0 := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
  · simp only [wordByte]
    apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
    simp [-UInt32.toUInt32_toUInt8]

/-- Two bytes loaded into a register and moved into a lane fill only the lane's two lowest bytes. -/
theorem pair_lane (b₀ b₁ : UInt8) (j : Nat) (hj : j < 4) :
    wordByte (b₀.toUInt32 ||| b₁.toUInt32 <<< 8) j = if j = 0 then b₀ else if j = 1 then b₁ else 0 := by
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;>
  · simp only [wordByte]
    apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_getLsbD_eq
    simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
    simp [-UInt32.toUInt32_toUInt8]

/-- A word's byte depends only on the position within the word. -/
theorem wordByte_mod (w : UInt32) (k : Nat) : wordByte w k = wordByte w (k % 4) := by
  simp [wordByte]

/-- The bytes of lanes loaded from memory, the lanes from a count up cleared: the memory bytes, then zeros. -/
theorem laneByte_loaded (mem : Nat → UInt8) (a n k : Nat) (hk : k < 64) (v : Lanes)
    (hv : ∀ l : Fin 16, v l = if l.val < n then readWord mem (a + 4 * l.val) else 0) :
    laneByte v k = if k < 4 * n then mem (a + k) else 0 := by
  -- Byte k sits in lane k / 4, at position k mod 4 within it.
  simp only [laneByte, laneOf, hv, Nat.mod_eq_of_lt (show k / 4 < 16 by omega)]
  by_cases inside : k / 4 < n
  · rw [if_pos inside, if_pos (by omega), wordByte_mod, readWord_byte _ _ _ (by omega)]
    congr 1
    omega
  · rw [if_neg inside, if_neg (by omega), zero_byte]

/-- The bytes of a register whose lowest lane alone is set: that lane's bytes, then zeros. -/
theorem laneByte_low (w : UInt32) (k : Nat) (hk : k < 64) :
    laneByte (fun l => if l = 0 then w else 0) k = if k < 4 then wordByte w k else 0 := by
  simp only [laneByte]
  -- Byte k sits in the lowest lane exactly when it is one of the first four.
  have lowest : laneOf k = 0 ↔ k < 4 := by
    simp only [laneOf, Fin.ext_iff, Fin.val_zero]
    omega
  by_cases low : k < 4
  · rw [if_pos (lowest.mpr low), if_pos low]
  · rw [if_neg (fun h => low (lowest.mp h)), if_neg low, zero_byte]

/-- Stores that agree on every byte they write leave the same memory. -/
theorem store_congr (mem : Nat → UInt8) (a n : Nat) (f g : Nat → UInt8) (h : ∀ k < n, f k = g k) :
    store mem a n f = store mem a n g := by
  funext x
  simp only [store]
  split
  · exact h _ (by omega)
  · rfl

/-- Two adjacent 32-byte stores are one 64-byte store. -/
theorem store_halves (mem : Nat → UInt8) (a : Nat) (f g : Nat → UInt8) :
    store (store mem a 32 f) (a + 32) 32 g = store mem a 64 (fun k => if k < 32 then f k else g (k - 32)) := by
  funext x
  simp only [store]
  by_cases high : a + 32 ≤ x ∧ x < a + 32 + 32
  · rw [if_pos high, if_pos (by omega), if_neg (by omega), show x - (a + 32) = x - a - 32 by omega]
  · rw [if_neg high]
    by_cases low : a ≤ x ∧ x < a + 32
    · rw [if_pos low, if_pos (by omega), if_pos (by omega)]
    · rw [if_neg low, if_neg (by omega)]

end Ssz.Native.Asm

namespace Ssz.Native.Kernel

open Ssz.Native.Asm

/-- The straight-line part of a record: load, store, and advance, without the branch back. -/
def straight (width slot : Nat) : List Instr :=
  loadField width ++ [.vstoreHalf ⟨.rdi, 0⟩ 0, .addReg .rsi .r8, .addImm .rsi width, .addImm .rdi slot, .subImm .rdx 1]

/-- The straight-line part of a record of the public-key routine. -/
def straightKey : List Instr :=
  [.vloadHalf 0 ⟨.rsi, 0⟩, .vload16 1 ⟨.rsi, 32⟩, .vstoreHalf ⟨.rdi, 0⟩ 0, .vstoreHalf ⟨.rdi, 32⟩ 1,
    .addReg .rsi .r8, .addImm .rsi 48, .addImm .rdi 64, .subImm .rdx 1]

/-- What one record's straight-line part does, for a field width and a slot. -/
def RecordEffect (code : List Instr) (width slot : Nat) : Prop :=
  ∀ t : State,
    (exec code t).mem = store t.mem (t.gpr .rdi).toNat slot
      (fun k => if k < width then t.mem ((t.gpr .rsi).toNat + k) else 0) ∧
    (exec code t).gpr .rdi = t.gpr .rdi + slot.toUInt64 ∧
    (exec code t).gpr .rsi = t.gpr .rsi + t.gpr .r8 + width.toUInt64 ∧
    (exec code t).gpr .rdx = t.gpr .rdx - 1 ∧
    (exec code t).zf = (t.gpr .rdx - 1 == 0) ∧
    ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rax → (exec code t).gpr r = t.gpr r

section

variable (program : Array Instr) (code : List Instr) (width slot : Nat)

/-- The routine's layout: the empty-count check, the record, the branch back, and the return. -/
def Shape : Prop :=
  program.toList = [.test .rdx, .jz (code.length + 3)] ++ code ++ [.jnz 2, .vzeroupper, .ret] ∧
  ∀ i ∈ code, i.straight

variable (s : State) (out src count skip : Nat)

/-- The machine at the loop head, i records in, about to run the instruction at an index. -/
private def Inv (i pc : Nat) (t : State) : Prop :=
  t.pc = pc ∧ t.status = .running ∧
  (t.gpr .rdi).toNat = out + slot * i ∧ (t.gpr .rsi).toNat = src + (width + skip) * i ∧
  (t.gpr .rdx).toNat = count - i ∧ t.gpr .r8 = s.gpr .r8 ∧
  (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
  ∀ x, t.mem x = if out ≤ x ∧ x < out + slot * i then recordByte s.mem out src width skip (slot - width) x
    else s.mem x

/-- No register the caller keeps is one the loop moves. -/
private theorem saved_ne (r : Gpr) (hr : r ∈ calleeSaved) :
    r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .rdx ∧ r ≠ .rax := by
  -- None of the registers the caller keeps is one the loop moves.
  simp [calleeSaved] at hr
  rcases hr with h | h | h | h | h | h | h <;> subst h <;> decide

/-- One more pass of the loop keeps the invariant with one more record written. -/
private theorem record (shape : Shape program code) (effect : RecordEffect code width slot)
    (fits : width ≤ slot) (slotBound : slot < 2 ^ 63) (widthBound : width < 2 ^ 63)
    (t : State) (i : Nat) (inv : Inv width slot s out src count skip i 2 t) (more : i < count)
    (hskip : (s.gpr .r8).toNat = skip)
    (outBound : out + slot * count ≤ addressBound)
    (srcBound : src + (width + skip) * count ≤ addressBound)
    (apart : ∀ i < count, ∀ k < width, ¬ (out ≤ src + (width + skip) * i + k ∧
      src + (width + skip) * i + k < out + slot * count)) :
    Inv width slot s out src count skip (i + 1) (if i + 1 < count then 2 else code.length + 3)
      (run program (code.length + 1) t) := by
  obtain ⟨pc, running, rdi, rsi, rdx, r8, saved, mem⟩ := inv
  obtain ⟨layout, straightCode⟩ := shape
  -- User-space addresses sit far below the point where a 64-bit sum wraps.
  have top : addressBound = 9223372036854775808 := rfl
  rw [top] at outBound srcBound
  -- The straight-line part, then the branch back.
  rw [run_add, run_block program [.test .rdx, .jz (code.length + 3)] code [.jnz 2, .vzeroupper, .ret] layout
    straightCode t pc running]
  obtain ⟨bmem, brdi, brsi, brdx, bzf, bkeep⟩ := effect t
  have grow : slot * (i + 1) ≤ slot * count := Nat.mul_le_mul_left _ more
  have growSrc : (width + skip) * (i + 1) ≤ (width + skip) * count := Nat.mul_le_mul_left _ more
  rw [Nat.mul_succ] at grow growSrc
  have w8 : (t.gpr .r8).toNat = skip := by rw [r8, hskip]
  have slotNat : slot.toUInt64.toNat = slot := by simp <;> omega
  have widthNat : width.toUInt64.toNat = width := by simp <;> omega
  have rdi2 : (t.gpr .rdi + slot.toUInt64).toNat = out + slot * (i + 1) := by
    rw [toNat_add_of_lt _ _ (by omega), rdi, slotNat, Nat.mul_succ]; omega
  have rsi2 : (t.gpr .rsi + t.gpr .r8 + width.toUInt64).toNat = src + (width + skip) * (i + 1) := by
    rw [toNat_add_of_lt _ _ (by rw [toNat_add_of_lt _ _ (by omega), rsi, w8, widthNat]; omega),
      toNat_add_of_lt _ _ (by omega), rsi, w8, widthNat, Nat.mul_succ]; omega
  have rdx1 : (t.gpr .rdx - 1).toNat = count - (i + 1) := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega)), rdx]
    simp; omega
  -- The branch goes back while records remain.
  have zf : (t.gpr .rdx - 1 == 0) = !decide (i + 1 < count) := by
    by_cases last : i + 1 < count
    · have : t.gpr .rdx - 1 ≠ 0 := fun h => by rw [h] at rdx1; simp at rdx1; omega
      simp [this, last]
    · have : t.gpr .rdx - 1 = 0 := UInt64.toNat_inj.mp (by rw [rdx1]; simp; omega)
      simp [this, last]
  simp only [run, step]
  have fetch : program[[Instr.test .rdx, .jz (code.length + 3)].length + code.length]? = some (.jnz 2) := by
    rw [← Array.getElem?_toList, layout, ← List.length_append, List.getElem?_append_right (Nat.le_refl _)]
    simp
  simp only [running, exec_status, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, fetch, bzf, zf]
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases last : i + 1 < count <;> simp [last]; omega
  · simpa using brdi ▸ rdi2
  · simpa using brsi ▸ rsi2
  · simpa using brdx ▸ rdx1
  · simp only; rw [bkeep _ (by decide) (by decide) (by decide) (by decide), r8]
  · intro r hr
    obtain ⟨a, b, c, d⟩ := saved_ne r hr
    simp only; rw [bkeep r a b c d]; exact saved r hr
  · intro x
    simp only [bmem, store]
    rw [rdi, rsi]
    have pad : width + (slot - width) = slot := by omega
    by_cases here : out + slot * i ≤ x ∧ x < out + slot * i + slot
    · -- A byte of slot i: a field byte, read from a source address the output never covers, or a zero.
      obtain ⟨k, rfl⟩ : ∃ k, x = out + slot * i + k := ⟨x - (out + slot * i), by omega⟩
      have tableEntry := recordByte_at s.mem out src width skip (slot - width) i k (by omega)
      rw [pad] at tableEntry
      have offset : out + slot * i + k - (out + slot * i) = k := by omega
      have inside : out ≤ out + slot * i + k ∧ out + slot * i + k < out + slot * (i + 1) := by
        rw [Nat.mul_succ]; omega
      rw [if_pos here, if_pos inside, tableEntry, offset]
      by_cases field : k < width
      · have outside := apart i more k field
        rw [if_pos field, if_pos field, mem, if_neg (by omega)]
      · rw [if_neg field, if_neg field]
    · -- Any other byte: an earlier slot, or untouched.
      rw [if_neg here, mem]
      by_cases earlier : out ≤ x ∧ x < out + slot * i
      · rw [if_pos earlier, if_pos ⟨earlier.1, by rw [Nat.mul_succ]; omega⟩]
      · rw [if_neg earlier, if_neg (by rw [Nat.mul_succ]; omega)]

/-- The loop, from any record on, writes every remaining record and leaves the routine at its branch. -/
private theorem records (shape : Shape program code) (effect : RecordEffect code width slot)
    (fits : width ≤ slot) (slotBound : slot < 2 ^ 63) (widthBound : width < 2 ^ 63)
    (hskip : (s.gpr .r8).toNat = skip)
    (outBound : out + slot * count ≤ addressBound)
    (srcBound : src + (width + skip) * count ≤ addressBound)
    (apart : ∀ i < count, ∀ k < width, ¬ (out ≤ src + (width + skip) * i + k ∧
      src + (width + skip) * i + k < out + slot * count)) (m : Nat) :
    ∀ (t : State) (i : Nat), i + m = count → 0 < m → Inv width slot s out src count skip i 2 t →
    Inv width slot s out src count skip count (code.length + 3) (run program ((code.length + 1) * m) t) := by
  induction m with
  | zero => intro _ _ _ h; omega
  | succ m ih =>
    intro t i total _ inv
    have next := record program code width slot s out src count skip shape effect fits slotBound widthBound
      t i inv (by omega) hskip outBound srcBound apart
    rw [Nat.mul_succ, Nat.add_comm ((code.length + 1) * m), run_add]
    by_cases last : m = 0
    · -- The last record falls through to the end.
      subst last
      rw [if_neg (by omega), show i + 1 = count by omega] at next
      simpa only [Nat.mul_zero, run] using next
    · rw [if_pos (by omega)] at next
      exact ih _ (i + 1) (by omega) (by omega) next

/-- A routine of this shape copies each record's field into its slot and zeroes the rest of the slot. -/
theorem shaped_correct (shape : Shape program code) (effect : RecordEffect code width slot)
    (fits : width ≤ slot) (slotBound : slot < 2 ^ 63) (widthBound : width < 2 ^ 63)
    (start : s.pc = 0) (running : s.status = .running)
    (hout : (s.gpr .rdi).toNat = out) (hsrc : (s.gpr .rsi).toNat = src) (hcount : (s.gpr .rdx).toNat = count)
    (hskip : (s.gpr .r8).toNat = skip)
    (outBound : out + slot * count ≤ addressBound)
    (srcBound : src + (width + skip) * count ≤ addressBound)
    (apart : ∀ i < count, ∀ k < width, ¬ (out ≤ src + (width + skip) * i + k ∧
      src + (width + skip) * i + k < out + slot * count)) :
    ∃ steps, let f := run program steps s
      f.status = .returned ∧
      (∀ i < count, ∀ k < slot, f.mem (out + slot * i + k) =
        if k < width then s.mem (src + (width + skip) * i + k) else 0) ∧
      (∀ x, ¬ (out ≤ x ∧ x < out + slot * count) → f.mem x = s.mem x) ∧
      ∀ r ∈ calleeSaved, f.gpr r = s.gpr r := by
  have layout := shape.1
  -- The last two instructions, from the loop's exit.
  have atEnd : program[code.length + 4]? = some .ret := by
    rw [← Array.getElem?_toList, layout]; simp
  have atZero : program[code.length + 3]? = some .vzeroupper := by
    rw [← Array.getElem?_toList, layout]; simp
  have at0 : program[0]? = some (.test .rdx) := by rw [← Array.getElem?_toList, layout]; simp
  have at1 : program[1]? = some (.jz (code.length + 3)) := by rw [← Array.getElem?_toList, layout]; simp
  by_cases empty : count = 0
  · -- No records: the test sends control to the return's predecessor.
    subst empty
    have zero : s.gpr .rdx = 0 := UInt64.toNat_inj.mp (by simpa using hcount)
    refine ⟨4, ?_⟩
    simp [run, step, start, running, at0, at1, exec1, zero, atZero, atEnd]
  · -- Two instructions check the count, the loop runs once per record, and two more return.
    have nonzero : s.gpr .rdx ≠ 0 := fun h => by rw [h] at hcount; simp at hcount; omega
    have setup : Inv width slot s out src count skip 0 2 (run program 2 s) := by
      simp [run, step, start, running, at0, at1, exec1, nonzero, Inv, hout, hsrc, hcount]
      intro x low high
      omega
    have loop := records program code width slot s out src count skip shape effect fits slotBound widthBound
      hskip outBound srcBound apart count _ 0 (by omega) (by omega) setup
    obtain ⟨pc, status, -, -, -, -, saved, mem⟩ := loop
    refine ⟨2 + (code.length + 1) * count + 2, ?_⟩
    rw [run_add, run_add]
    generalize run program ((code.length + 1) * count) (run program 2 s) = t at pc status saved mem
    simp only [run, step, status, pc, atZero, atEnd, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, exec1]
    refine ⟨trivial, fun i hi k hk => ?_, fun x hx => ?_, saved⟩
    · -- Byte k of slot i lies inside the output.
      have grow := Nat.mul_le_mul_left slot (show i + 1 ≤ count by omega)
      rw [Nat.mul_succ] at grow
      have tableEntry := recordByte_at s.mem out src width skip (slot - width) i k (by omega)
      rw [show width + (slot - width) = slot by omega] at tableEntry
      rw [mem, if_pos ⟨by omega, by omega⟩, tableEntry]
    · rw [mem, if_neg hx]

end

/-- One record of the single-load routine of each width: its field, then zeros, in one 32-byte slot. -/
theorem straight_effect (width : Nat) (known : width ∈ [1, 2, 4, 8, 16, 32]) :
    RecordEffect (straight width 32) width 32 := by
  intro t
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at known
  rcases known with rfl | rfl | rfl | rfl | rfl | rfl <;>
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  -- No register outside the loop's own is written.
  try (intro r a b c d; simp [straight, loadField, exec, exec1, assign, a, b, c, d]; done)
  -- The pointer and count updates, and the flag the count leaves.
  all_goals try (simp [straight, loadField, exec, exec1, assign, State.addr]; done)
  -- What remains is the slot's bytes: the loaded lanes' bytes, then zeros.
  all_goals simp [straight, loadField, exec, exec1, assign, State.addr]
  all_goals apply store_congr
  all_goals intro k hk
  -- One byte, moved through a general register into the lowest lane.
  · rw [laneByte_low _ _ (by omega)]
    by_cases low : k < 4
    · rw [if_pos low, byte_lane _ _ low]
      by_cases z : k = 0 <;> simp [z]
    · rw [if_neg low, if_neg (by omega)]
  -- Two bytes, moved the same way.
  · rw [laneByte_low _ _ (by omega)]
    by_cases low : k < 4
    · rw [if_pos low, pair_lane _ _ _ low]
      by_cases z : k = 0
      · simp [z]
      · by_cases o : k = 1
        · simp [o]
        · rw [if_neg z, if_neg o, if_neg (by omega)]
    · rw [if_neg low, if_neg (by omega)]
  -- A lane count fits each width: one, two, four, or eight lanes.
  · rw [laneByte_loaded _ _ 1 k (by omega) _ (fun l => by
      by_cases h : l = 0
      · subst h; rfl
      · have above : ¬ l.val < 1 := fun e => h (Fin.ext (by simp; omega))
        simp [h, above])]
  · rw [laneByte_loaded _ _ 2 k (by omega) _ (fun l => rfl)]
  · rw [laneByte_loaded _ _ 4 k (by omega) _ (fun l => rfl)]
  · rw [laneByte_loaded _ _ 8 k (by omega) _ (fun l => rfl)]

/-- One record of the public-key routine: its 48 bytes, then 16 zeros, in one 64-byte slot. -/
theorem key_effect : RecordEffect straightKey 48 64 := by
  intro t
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The two 32-byte stores are one 64-byte store of the two loaded registers' bytes.
    simp [straightKey, exec, exec1, assign, State.addr]
    rw [store_halves]
    apply store_congr
    intro k hk
    by_cases low : k < 32
    · rw [if_pos low, laneByte_loaded _ _ 8 k (by omega) _ (fun l => rfl), if_pos (by omega), if_pos (by omega)]
    · rw [if_neg low, laneByte_loaded _ _ 4 (k - 32) (by omega) _ (fun l => rfl)]
      by_cases key : k < 48
      · rw [if_pos (by omega), if_pos key]
        congr 1
        omega
      · rw [if_neg (by omega), if_neg key]
  -- The pointer and count updates, and the flag the count leaves.
  all_goals try (simp [straightKey, exec, exec1, assign]; done)
  -- No other register is written.
  intro r a b c _
  simp [straightKey, exec, exec1, assign, a, b, c]

/-- Each single-load routine is the empty-count check, its record, the branch back, and the return. -/
theorem node_shape (width : Nat) (known : width ∈ [1, 2, 4, 8, 16, 32]) :
    Shape (gatherNode width) (straight width 32) := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at known
  rcases known with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, by decide⟩

/-- The public-key routine has the same shape. -/
theorem key_shape : Shape gatherKey straightKey :=
  ⟨rfl, by decide⟩

/--
The routine for one field width copies each record's field into a 32-byte slot and zeroes the rest of the slot.

The output must not cover any source field, and every address stays below the top of user space.
Nothing else in memory changes, and the registers the caller keeps are handed back unchanged.
-/
theorem gatherNode_correct (width : Nat) (known : width ∈ [1, 2, 4, 8, 16, 32])
    (s : State) (out src count skip : Nat)
    (start : s.pc = 0) (running : s.status = .running)
    (hout : (s.gpr .rdi).toNat = out) (hsrc : (s.gpr .rsi).toNat = src) (hcount : (s.gpr .rdx).toNat = count)
    (hskip : (s.gpr .r8).toNat = skip)
    (outBound : out + 32 * count ≤ addressBound)
    (srcBound : src + (width + skip) * count ≤ addressBound)
    (apart : ∀ i < count, ∀ k < width, ¬ (out ≤ src + (width + skip) * i + k ∧
      src + (width + skip) * i + k < out + 32 * count)) :
    ∃ steps, let f := run (gatherNode width) steps s
      f.status = .returned ∧
      (∀ i < count, ∀ k < 32, f.mem (out + 32 * i + k) =
        if k < width then s.mem (src + (width + skip) * i + k) else 0) ∧
      (∀ x, ¬ (out ≤ x ∧ x < out + 32 * count) → f.mem x = s.mem x) ∧
      ∀ r ∈ calleeSaved, f.gpr r = s.gpr r := by
  have small : width ≤ 32 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at known
    omega
  exact shaped_correct _ _ width 32 s out src count skip (node_shape width known) (straight_effect width known)
    small (by omega) (by omega) start running hout hsrc hcount hskip outBound srcBound apart

/--
The public-key routine copies each record's 48-byte field into a 64-byte slot and zeroes the last 16 bytes.

Its hypotheses and guarantees are those of the routine for one field width.
-/
theorem gatherKey_correct (s : State) (out src count skip : Nat)
    (start : s.pc = 0) (running : s.status = .running)
    (hout : (s.gpr .rdi).toNat = out) (hsrc : (s.gpr .rsi).toNat = src) (hcount : (s.gpr .rdx).toNat = count)
    (hskip : (s.gpr .r8).toNat = skip)
    (outBound : out + 64 * count ≤ addressBound)
    (srcBound : src + (48 + skip) * count ≤ addressBound)
    (apart : ∀ i < count, ∀ k < 48, ¬ (out ≤ src + (48 + skip) * i + k ∧
      src + (48 + skip) * i + k < out + 64 * count)) :
    ∃ steps, let f := run gatherKey steps s
      f.status = .returned ∧
      (∀ i < count, ∀ k < 64, f.mem (out + 64 * i + k) =
        if k < 48 then s.mem (src + (48 + skip) * i + k) else 0) ∧
      (∀ x, ¬ (out ≤ x ∧ x < out + 64 * count) → f.mem x = s.mem x) ∧
      ∀ r ∈ calleeSaved, f.gpr r = s.gpr r :=
  shaped_correct _ _ 48 64 s out src count skip key_shape key_effect (by omega) (by omega) (by omega)
    start running hout hsrc hcount hskip outBound srcBound apart

end Ssz.Native.Kernel
