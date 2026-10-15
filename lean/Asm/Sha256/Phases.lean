import Asm.Memory
import Asm.Sha256.Rounds

/-! The kernel's entry and exit: spilling registers, loading the block and the state, and writing back. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm

/-- The bytes of a range of memory. -/
def Machine.bytes (m : Machine) (a : BitVec 64) (n : Nat) : ByteArray :=
  ⟨Array.ofFn fun i : Fin n => ⟨m.mem (a + BitVec.ofNat 64 i.val)⟩⟩

/-- The native-endian 32-bit word at an address. -/
def Machine.word32 (m : Machine) (a : BitVec 64) : BitVec 32 :=
  (m.load a 4).setWidth 32

/-- Eight consecutive native-endian words, read as a SHA-256 chaining state. -/
def Machine.stateAt (m : Machine) (a : BitVec 64) : Ssz.Sha256.Spec.State :=
  let word := fun (j : Nat) => m.word32 (a + BitVec.ofNat 64 (4 * j))
  ⟨word 0, word 1, word 2, word 3, word 4, word 5, word 6, word 7⟩

theorem Machine.bytes_get {m : Machine} {a : BitVec 64} {n k : Nat} (within : k < n) :
    ((m.bytes a n).get! k).toNat = (m.mem (a + BitVec.ofNat 64 k)).toNat := by
  simp [Machine.bytes, ByteArray.get!, within]

theorem Machine.load_one {m : Machine} {a : BitVec 64} : m.load a 1 = (m.mem a).setWidth 64 := by
  simp [Machine.load]

/-- Four bytes assembled most significant first, as the word loads do it. -/
theorem bigEndian (b0 b1 b2 b3 : BitVec 8) :
    (((b0.setWidth 64).setWidth 32 <<< 24).signExtend 64 ||| b1.setWidth 64 <<< 16 |||
      b2.setWidth 64 <<< 8 ||| b3.setWidth 64) =
    (BitVec.ofNat 32 b0.toNat <<< 24 ||| BitVec.ofNat 32 b1.toNat <<< 16 |||
      BitVec.ofNat 32 b2.toNat <<< 8 ||| BitVec.ofNat 32 b3.toNat).signExtend 64 := by
  simp only [BitVec.ofNat_toNat]
  bitwise

end Ssz.Asm

namespace Ssz.Asm.Sha256

open Ssz.Sha256 (Spec.inputWord Spec.inputWords)

theorem loadWordFrom_spec {m : Machine} {k : Nat} {base : Reg} {start size : Nat}
    (wa : ringSlot k ≠ base) (ta : t0 ≠ base) (inside : start + 3 < size) (short : start + 3 < 2048) :
    let m' := execBlock (loadWordFrom k base start) m
    Holds m' (ringSlot k) (Spec.inputWord (m.bytes (m.read base) size) start) ∧ m'.mem = m.mem ∧
      ∀ x, x ≠ ringSlot k → x ≠ t0 → m'.read x = m.read x := by
  intro m'
  have z : (0 : Reg) ≠ ringSlot k := (nonzero 0 0 k 0).2.1
  have wt : ringSlot k ≠ t0 := (ringSlot_ne k 0).2.1
  have zt : (0 : Reg) ≠ t0 := by decide
  simp (disch := reg_ne) only [m', loadWordFrom, execBlock_cons, execBlock_nil, Instr.run,
    Machine.read_write_self', Machine.read_write_ne', Machine.read_write_ne, Machine.mem_write,
    Machine.load_write]
  refine ⟨?_, trivial, fun x xw xt => ?_⟩
  all_goals simp (disch := reg_ne) only [Holds, Machine.read_write_self', Machine.read_write_ne',
    Machine.read_write_ne]
  -- Each byte load reads one byte of the block, at a small offset from its base.
  simp only [Spec.inputWord, Machine.load_one, Nat.reduceMod, Nat.add_zero,
    signExtend_ofNat12 (show start < 2048 by omega),
    signExtend_ofNat12 (show start + 1 < 2048 by omega),
    signExtend_ofNat12 (show start + 2 < 2048 by omega),
    signExtend_ofNat12 (show start + 3 < 2048 by omega),
    Machine.bytes_get (show start < size by omega), Machine.bytes_get (show start + 1 < size by omega),
    Machine.bytes_get (show start + 2 < size by omega), Machine.bytes_get (show start + 3 < size by omega)]
  exact bigEndian _ _ _ _

theorem loadWord_spec {m : Machine} {k : Nat} (small : k < 16) :
    let m' := execBlock (loadWordCode k) m
    Holds m' (ringSlot k) (Spec.inputWord (m.bytes (m.read a1) 64) (4 * k)) ∧ m'.mem = m.mem ∧
      ∀ x, x ≠ ringSlot k → x ≠ t0 → m'.read x = m.read x :=
  loadWordFrom_spec (ringSlot_ne k 0).1 (by decide) (by omega) (by omega)

/-- The first n message words, each in its ring slot. -/
theorem loadBlock_upto {m : Machine} :
    ∀ n, n ≤ 16 →
      let m' := execBlock ((List.range n).flatMap loadWordCode) m
      (∀ k, k < n → Holds m' (ringSlot k) (Spec.inputWord (m.bytes (m.read a1) 64) (4 * k))) ∧
        m'.mem = m.mem ∧ ∀ x, x ∉ wordRegs.toList → x ≠ t0 → m'.read x = m.read x
  | 0, _ => by simp
  | n + 1, bound => by
    intro m'
    obtain ⟨loaded, mem, frame⟩ := loadBlock_upto n (by omega)
    simp only [m', List.range_succ, List.flatMap_append, List.flatMap_singleton, execBlock_append]
    generalize execBlock ((List.range n).flatMap loadWordCode) m = mn at loaded mem frame
    obtain ⟨fresh, mem', frame'⟩ := loadWord_spec (m := mn) (k := n) (by omega)
    -- The block address and the block bytes are as they were on entry.
    have base : mn.read a1 = m.read a1 := frame a1 (by decide) (by decide)
    have bytes : mn.bytes (m.read a1) 64 = m.bytes (m.read a1) 64 := by
      simp [Machine.bytes, mem]
    rw [base, bytes] at fresh
    refine ⟨fun k below => ?_, mem'.trans mem, fun x outside xt => ?_⟩
    · by_cases now : k = n
      · subst now
        exact fresh
      · -- An earlier word sits in a different slot, which this load leaves alone.
        rw [Holds, frame' _ (ringSlot_ne_ringSlot (by omega)) (ringSlot_ne k 0).2.1]
        exact loaded k (by omega)
    · have : x ≠ ringSlot n := by
        rintro rfl
        exact outside (by simp [ringSlot, Vector.getElem_mem])
      rw [frame' x this xt, frame x outside xt]

theorem loadState_eq : loadStateCode =
    [.lw 12 a0 0, .lw 13 a0 4, .lw 14 a0 8, .lw 15 a0 12, .lw 16 a0 16, .lw 17 a0 20,
      .lw 28 a0 24, .lw 10 a0 28] := by
  rfl

/-- The eight state words, each in the home of its working word at round zero. -/
theorem loadState_spec {m : Machine} :
    let m' := execBlock loadStateCode m
    (∀ j, j < 8 → Holds m' (wordHome 0 j) (m.word32 (m.read a0 + BitVec.ofNat 64 (4 * j)))) ∧
      m'.mem = m.mem ∧ ∀ x, x ∉ stateRegs.toList → m'.read x = m.read x := by
  intro m'
  simp only [m', loadState_eq, execBlock_cons, execBlock_nil, Instr.run]
  refine ⟨fun j small => ?_, rfl, fun x outside => ?_⟩
  · simp only [Nat.lt_succ_iff_lt_or_eq] at small
    repeat' rcases small with small | rfl
    all_goals try (exfalso; omega)
    -- Each word lands in its home, and the address register is overwritten only last.
    all_goals simp (disch := decide) only [Holds, wordHome, Machine.read_write_self,
      Machine.read_write_ne, sext32, Machine.word32, signExtend_ofNat12 (show 0 < 2048 by omega),
      signExtend_ofNat12 (show 4 < 2048 by omega), signExtend_ofNat12 (show 8 < 2048 by omega),
      signExtend_ofNat12 (show 12 < 2048 by omega), signExtend_ofNat12 (show 16 < 2048 by omega),
      signExtend_ofNat12 (show 20 < 2048 by omega), signExtend_ofNat12 (show 24 < 2048 by omega),
      signExtend_ofNat12 (show 28 < 2048 by omega)]
    all_goals rfl
  · -- A register outside the eight homes is never written.
    have ne : ∀ r ∈ stateRegs.toList, x ≠ r := fun r inside same => outside (same ▸ inside)
    simp only [stateRegs, Vector.toList_mk, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at ne
    obtain ⟨n12, n13, n14, n15, n16, n17, n28, n10⟩ := ne
    simp only [Machine.read_write_ne n12, Machine.read_write_ne n13, Machine.read_write_ne n14,
      Machine.read_write_ne n15, Machine.read_write_ne n16, Machine.read_write_ne n17,
      Machine.read_write_ne n28, Machine.read_write_ne n10]

end Ssz.Asm.Sha256
