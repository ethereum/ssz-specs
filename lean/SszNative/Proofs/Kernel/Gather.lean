import SszNative.Kernel.Gather
import SszNative.Proofs.Asm.Run
import SszNative.Proofs.Asm.Spec

/-!
The gathering kernel, run on the machine model: each record's field lands in its zero-padded slot.

```text
    source:   [ field 0 | skip ][ field 1 | skip ] ...    a width plus a skip apart
    output:   [ field 0 | zeros ][ field 1 | zeros ] ...  a width plus a pad apart
```
-/

namespace Ssz.Native.Asm

/-- A forward copy between ranges that share no address is a plain copy. -/
theorem copyForward_apart (mem : Nat → UInt8) (dst src n : Nat)
    (apart : ∀ k < n, ¬ (dst ≤ src + k ∧ src + k < dst + n)) (x : Nat) :
    copyForward mem dst src n x = if dst ≤ x ∧ x < dst + n then mem (src + (x - dst)) else mem x := by
  induction n generalizing mem dst src with
  | zero => simp only [copyForward]; rw [if_neg (by omega)]
  | succ n ih =>
    -- The first byte is written, then the rest is copied from one address further on.
    simp only [copyForward]
    rw [ih _ _ _ (fun k hk h => apart (k + 1) (by omega) (by omega))]
    by_cases inside : dst + 1 ≤ x ∧ x < dst + 1 + n
    · have : src + 1 + (x - (dst + 1)) = src + (x - dst) := by omega
      -- The source byte read later is never the destination byte written first.
      have away := apart (x - dst) (by omega)
      simp only [inside, and_self, ↓reduceIte, this, assign]
      rw [if_neg (by omega), if_pos (by omega)]
    · simp only [inside, ↓reduceIte, assign]
      by_cases e : x = dst
      · subst e; simp
      · rw [if_neg e, if_neg (by omega)]

/-- A sum of two registers that does not reach the top of the address space. -/
theorem toNat_add_of_lt (a b : UInt64) (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]
  exact Nat.mod_eq_of_lt h

end Ssz.Native.Asm

namespace Ssz.Native.Kernel

open Ssz.Native.Asm

/-- The loop body: one record's field, its padding, and on to the next record. -/
private def body : List Instr :=
  [.movReg .rcx .r10, .repMovsb, .movReg .rcx .r9, .repStosb, .addReg .rsi .r8, .subImm .rdx 1]

/-- The routine is its entry check, its setup, the loop body, and the loop branch. -/
private theorem layout :
    gather.toList = [.test .rdx, .jz 11, .movReg .r10 .rcx, .zeroReg .rax] ++ body ++ [.jnz 4, .ret] := rfl

/-- One pass of the loop body copies a field, pads its slot with zeros, and advances every pointer. -/
private theorem exec_body (t : State) :
    (exec body t).mem = store (copyForward t.mem (t.gpr .rdi).toNat (t.gpr .rsi).toNat (t.gpr .r10).toNat)
      (t.gpr .rdi + t.gpr .r10).toNat (t.gpr .r9).toNat (fun _ => (t.gpr .rax).toUInt8) ∧
    (exec body t).gpr .rdi = t.gpr .rdi + t.gpr .r10 + t.gpr .r9 ∧
    (exec body t).gpr .rsi = t.gpr .rsi + t.gpr .r10 + t.gpr .r8 ∧
    (exec body t).gpr .rdx = t.gpr .rdx - 1 ∧
    (exec body t).zf = (t.gpr .rdx - 1 == 0) ∧
    ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → (exec body t).gpr r = t.gpr r := by
  -- Each claim follows the six instructions' register and memory updates.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [body, exec, exec1, assign]
  intro r a b c d
  simp [a, b, c, d]

/-- What the output holds at an address: the field byte or a padding zero of the slot it falls in. -/
def recordByte (mem : Nat → UInt8) (out src width skip pad x : Nat) : UInt8 :=
  let j := (x - out) / (width + pad)
  let k := (x - out) % (width + pad)
  if k < width then mem (src + (width + skip) * j + k) else 0

/-- A byte of the output region, named by its record and its place in the slot. -/
theorem recordByte_at (mem : Nat → UInt8) (out src width skip pad i k : Nat) (within : k < width + pad) :
    recordByte mem out src width skip pad (out + (width + pad) * i + k) =
      if k < width then mem (src + (width + skip) * i + k) else 0 := by
  -- The address sits k bytes into slot i.
  have shift : out + (width + pad) * i + k - out = k + (width + pad) * i := by omega
  have slot : (k + (width + pad) * i) / (width + pad) = i := by
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt within, Nat.zero_add]
  have offset : (k + (width + pad) * i) % (width + pad) = k := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt within]
  simp only [recordByte, shift, slot, offset]

section

variable (s : State) (out src count width skip pad : Nat)

/-- The machine at the loop head, i records in, about to run the instruction at an index. -/
private def Inv (i pc : Nat) (t : State) : Prop :=
  t.pc = pc ∧ t.status = .running ∧
  (t.gpr .rdi).toNat = out + (width + pad) * i ∧ (t.gpr .rsi).toNat = src + (width + skip) * i ∧
  (t.gpr .rdx).toNat = count - i ∧
  t.gpr .r10 = s.gpr .rcx ∧ t.gpr .r8 = s.gpr .r8 ∧ t.gpr .r9 = s.gpr .r9 ∧ t.gpr .rax = 0 ∧
  (∀ r ∈ calleeSaved, t.gpr r = s.gpr r) ∧
  ∀ x, t.mem x = if out ≤ x ∧ x < out + (width + pad) * i then recordByte s.mem out src width skip pad x
    else s.mem x

/-- One more pass of the loop keeps the invariant with one more record written. -/
private theorem record (t : State) (i : Nat) (inv : Inv s out src count width skip pad i 4 t) (more : i < count)
    (hwidth : (s.gpr .rcx).toNat = width) (hskip : (s.gpr .r8).toNat = skip) (hpad : (s.gpr .r9).toNat = pad)
    (outBound : out + (width + pad) * count ≤ addressBound)
    (srcBound : src + (width + skip) * count ≤ addressBound)
    (apart : ∀ i < count, ∀ k < width, ¬ (out ≤ src + (width + skip) * i + k ∧
      src + (width + skip) * i + k < out + (width + pad) * count)) :
    Inv s out src count width skip pad (i + 1) (if i + 1 < count then 4 else 11) (run gather 7 t) := by
  obtain ⟨pc, running, rdi, rsi, rdx, r10, r8, r9, rax, saved, mem⟩ := inv
  -- User-space addresses sit far below the point where a 64-bit sum wraps.
  have top : addressBound = 9223372036854775808 := rfl
  rw [top] at outBound srcBound
  -- Six straight-line instructions, then the branch back.
  rw [show 7 = 6 + 1 from rfl, run_add,
    show 6 = body.length from rfl, run_block gather _ body _ layout (by decide) t pc running]
  obtain ⟨bmem, brdi, brsi, brdx, bzf, bkeep⟩ := exec_body t
  -- Slot i and its field both stay below the top of the address space, so no pointer sum wraps.
  have grow : (width + pad) * (i + 1) ≤ (width + pad) * count := Nat.mul_le_mul_left _ more
  have growSrc : (width + skip) * (i + 1) ≤ (width + skip) * count := Nat.mul_le_mul_left _ more
  rw [Nat.mul_succ] at grow growSrc
  have w10 : (t.gpr .r10).toNat = width := by rw [r10, hwidth]
  have w9 : (t.gpr .r9).toNat = pad := by rw [r9, hpad]
  have w8 : (t.gpr .r8).toNat = skip := by rw [r8, hskip]
  have rdi1 : (t.gpr .rdi + t.gpr .r10).toNat = out + (width + pad) * i + width := by
    rw [toNat_add_of_lt _ _ (by omega), rdi, w10]
  have rdi2 : (t.gpr .rdi + t.gpr .r10 + t.gpr .r9).toNat = out + (width + pad) * (i + 1) := by
    rw [toNat_add_of_lt _ _ (by omega), rdi1, w9, Nat.mul_succ]; omega
  have rsi2 : (t.gpr .rsi + t.gpr .r10 + t.gpr .r8).toNat = src + (width + skip) * (i + 1) := by
    rw [toNat_add_of_lt _ _ (by rw [toNat_add_of_lt _ _ (by omega), rsi, w10, w8]; omega),
      toNat_add_of_lt _ _ (by omega), rsi, w10, w8, Nat.mul_succ]; omega
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
  have fetch : gather[10]? = some (.jnz 4) := rfl
  have at10 : [Instr.test .rdx, .jz 11, .movReg .r10 .rcx, .zeroReg .rax].length + body.length = 10 := rfl
  simp only [at10, running, exec_status, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, fetch, bzf, zf]
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases last : i + 1 < count <;> simp [last]
  · simpa using brdi ▸ rdi2
  · simpa using brsi ▸ rsi2
  · simpa using brdx ▸ rdx1
  · simp only; rw [bkeep _ (by decide) (by decide) (by decide) (by decide), r10]
  · simp only; rw [bkeep _ (by decide) (by decide) (by decide) (by decide), r8]
  · simp only; rw [bkeep _ (by decide) (by decide) (by decide) (by decide), r9]
  · simp only; rw [bkeep _ (by decide) (by decide) (by decide) (by decide), rax]
  · intro r hr
    simp only
    rw [bkeep r (by simp [calleeSaved] at hr; rcases hr with h | h | h | h | h | h | h <;> subst h <;> decide)
      (by simp [calleeSaved] at hr; rcases hr with h | h | h | h | h | h | h <;> subst h <;> decide)
      (by simp [calleeSaved] at hr; rcases hr with h | h | h | h | h | h | h <;> subst h <;> decide)
      (by simp [calleeSaved] at hr; rcases hr with h | h | h | h | h | h | h <;> subst h <;> decide)]
    exact saved r hr
  · intro x
    simp only [bmem]
    rw [rdi1, w9, rax, rdi, rsi, w10]
    -- The field's source bytes lie outside the output, so the copy reads them as they were.
    have fieldApart : ∀ k < width, ¬ (out + (width + pad) * i ≤ src + (width + skip) * i + k ∧
        src + (width + skip) * i + k < out + (width + pad) * i + width) :=
      fun k hk h => apart i more k hk ⟨by omega, by omega⟩
    simp only [store, copyForward_apart _ _ _ _ fieldApart, mem]
    by_cases padding : out + (width + pad) * i + width ≤ x ∧ x < out + (width + pad) * i + width + pad
    · -- A padding byte of slot i.
      obtain ⟨k, rfl⟩ : ∃ k, x = out + (width + pad) * i + width + k := ⟨x - (out + (width + pad) * i + width), by omega⟩
      rw [if_pos padding, if_pos ⟨by omega, by rw [Nat.mul_succ]; omega⟩, Nat.add_assoc,
        recordByte_at _ _ _ _ _ _ _ _ (by omega), if_neg (by omega)]
      rfl
    rw [if_neg padding]
    by_cases field : out + (width + pad) * i ≤ x ∧ x < out + (width + pad) * i + width
    · -- A field byte of slot i, read from a source address the output never covers.
      obtain ⟨k, rfl⟩ : ∃ k, x = out + (width + pad) * i + k := ⟨x - (out + (width + pad) * i), by omega⟩
      have outside := apart i more k (by omega)
      rw [if_pos field, if_neg (by omega), if_pos ⟨by omega, by rw [Nat.mul_succ]; omega⟩,
        recordByte_at _ _ _ _ _ _ _ _ (by omega), if_pos (by omega)]
      congr 1
      omega
    · -- Any other byte: an earlier slot, or untouched.
      rw [if_neg field]
      by_cases earlier : out ≤ x ∧ x < out + (width + pad) * i
      · rw [if_pos earlier, if_pos ⟨earlier.1, by rw [Nat.mul_succ]; omega⟩]
      · rw [if_neg earlier, if_neg (by rw [Nat.mul_succ]; omega)]

/-- The loop, from any record on, writes every remaining record and leaves the routine at its branch. -/
private theorem records (m : Nat) : ∀ (t : State) (i : Nat), i + m = count → 0 < m →
    Inv s out src count width skip pad i 4 t →
    (s.gpr .rcx).toNat = width → (s.gpr .r8).toNat = skip → (s.gpr .r9).toNat = pad →
    out + (width + pad) * count ≤ addressBound → src + (width + skip) * count ≤ addressBound →
    (∀ i < count, ∀ k < width, ¬ (out ≤ src + (width + skip) * i + k ∧
      src + (width + skip) * i + k < out + (width + pad) * count)) →
    Inv s out src count width skip pad count 11 (run gather (7 * m) t) := by
  induction m with
  | zero => intro _ _ _ h; omega
  | succ m ih =>
    intro t i total _ inv hw hs hp ob sb apart
    have next := record s out src count width skip pad t i inv (by omega) hw hs hp ob sb apart
    rw [Nat.mul_succ, Nat.add_comm, run_add]
    by_cases last : m = 0
    · -- The last record falls through to the return.
      subst last
      simp only [show i + 1 = count by omega, Nat.lt_irrefl, ↓reduceIte] at next
      simpa [run] using next
    · rw [if_pos (by omega)] at next
      exact ih _ (i + 1) (by omega) (by omega) next hw hs hp ob sb apart

end

/--
The kernel copies each record's field into its slot and zeroes the rest of the slot.

The output must not cover any source field, and every address stays below the top of user space.
Nothing else in memory changes, and the registers the caller keeps are handed back unchanged.
-/
theorem gather_correct (s : State) (out src count width skip pad : Nat)
    (start : s.pc = 0) (running : s.status = .running)
    (hout : (s.gpr .rdi).toNat = out) (hsrc : (s.gpr .rsi).toNat = src) (hcount : (s.gpr .rdx).toNat = count)
    (hwidth : (s.gpr .rcx).toNat = width) (hskip : (s.gpr .r8).toNat = skip) (hpad : (s.gpr .r9).toNat = pad)
    (outBound : out + (width + pad) * count ≤ addressBound)
    (srcBound : src + (width + skip) * count ≤ addressBound)
    (apart : ∀ i < count, ∀ k < width, ¬ (out ≤ src + (width + skip) * i + k ∧
      src + (width + skip) * i + k < out + (width + pad) * count)) :
    ∃ steps, let f := run gather steps s
      f.status = .returned ∧
      (∀ i < count, ∀ k < width + pad, f.mem (out + (width + pad) * i + k) =
        if k < width then s.mem (src + (width + skip) * i + k) else 0) ∧
      (∀ x, ¬ (out ≤ x ∧ x < out + (width + pad) * count) → f.mem x = s.mem x) ∧
      ∀ r ∈ calleeSaved, f.gpr r = s.gpr r := by
  by_cases empty : count = 0
  · -- No records: the test sends control straight to the return.
    subst empty
    have zero : s.gpr .rdx = 0 := UInt64.toNat_inj.mp (by simpa using hcount)
    refine ⟨3, ?_⟩
    simp [run, step, start, running, gather, exec1, zero]
  · -- Four instructions set the loop up, the loop runs once per record, and the routine returns.
    have nonzero : s.gpr .rdx ≠ 0 := fun h => by rw [h] at hcount; simp at hcount; omega
    have setup : Inv s out src count width skip pad 0 4 (run gather 4 s) := by
      simp [run, step, start, running, gather, exec1, assign, nonzero, Inv, calleeSaved, hout, hsrc, hcount]
      intro x low high
      omega
    have loop := records s out src count width skip pad count _ 0 (by omega) (by omega) setup hwidth hskip hpad
      outBound srcBound apart
    obtain ⟨pc, status, -, -, -, -, -, -, -, saved, mem⟩ := loop
    refine ⟨4 + 7 * count + 1, ?_⟩
    rw [run_add, run_add]
    generalize run gather (7 * count) (run gather 4 s) = t at pc status saved mem
    have fetch : gather[11]? = some .ret := rfl
    simp only [run, step, status, pc, fetch, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    refine ⟨trivial, fun i hi k hk => ?_, fun x hx => ?_, saved⟩
    · -- Byte k of slot i lies inside the output.
      have := Nat.mul_le_mul_left (width + pad) (show i + 1 ≤ count by omega)
      rw [Nat.mul_succ] at this
      rw [mem, if_pos ⟨by omega, by omega⟩, recordByte_at _ _ _ _ _ _ _ _ hk]
    · rw [mem, if_neg hx]

end Ssz.Native.Kernel
