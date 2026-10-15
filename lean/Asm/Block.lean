import Asm.Machine

/-! How registers, memory, and straight-line code behave, stated once for every kernel. -/

namespace Ssz.Asm

namespace Machine

@[simp] theorem read_write_self {m : Machine} {r : Reg} {v : BitVec 64} (nonzero : r ≠ 0) :
    (m.write r v).read r = v := by
  -- A nonzero register reads back what was last written to it.
  simp [read, write, nonzero]

@[simp] theorem read_write_ne {m : Machine} {r q : Reg} {v : BitVec 64} (other : q ≠ r) :
    (m.write r v).read q = m.read q := by
  -- Writing one register leaves every other register alone.
  simp [read, write, other]

theorem read_write_self' {m : Machine} {r : Reg} {v : BitVec 64} (nonzero : 0 ≠ r) :
    (m.write r v).read r = v :=
  read_write_self (Ne.symm nonzero)

theorem read_write_ne' {m : Machine} {r q : Reg} {v : BitVec 64} (other : r ≠ q) :
    (m.write r v).read q = m.read q :=
  read_write_ne (Ne.symm other)

@[simp] theorem mem_write {m : Machine} {r : Reg} {v : BitVec 64} : (m.write r v).mem = m.mem :=
  rfl

@[simp] theorem read_store {m : Machine} {a : BitVec 64} {n : Nat} {v : BitVec 64} {r : Reg} :
    (m.store a n v).read r = m.read r :=
  rfl

@[simp] theorem read_zero {m : Machine} : m.read 0 = 0 := by
  -- The zero register is hardwired.
  simp [read]

/-- Machines with the same registers and memory are the same machine. -/
theorem ext {m m' : Machine} (regs : m.regs = m'.regs) (mem : m.mem = m'.mem) : m = m' := by
  cases m
  cases m'
  simp_all

/-- A second write to a register discards the first. -/
@[simp] theorem write_write_same {m : Machine} {r : Reg} {v w : BitVec 64} :
    (m.write r v).write r w = m.write r w := by
  -- Both sides answer w for the register and defer to the original machine elsewhere.
  refine ext ?_ rfl
  funext q
  by_cases same : q = r <;> simp [write, same]

/-- A write that is overwritten later, with another register written in between, is discarded. -/
@[simp] theorem write_shadow {m : Machine} {r q : Reg} {v w u : BitVec 64} :
    ((m.write r v).write q w).write r u = (m.write q w).write r u := by
  -- Every register reads the same on both sides once the last write to r is in place.
  refine ext ?_ rfl
  funext x
  by_cases first : x = r <;> by_cases second : x = q <;> simp [write, first, second]

/-- Bytes outside a store keep their old contents. -/
theorem mem_store_outside {m : Machine} {a x : BitVec 64} {n : Nat} {v : BitVec 64}
    (outside : n ≤ (x - a).toNat) : (m.store a n v).mem x = m.mem x := by
  -- The stored range is the n addresses at offsets 0 to n - 1 from its start.
  simp only [store]
  rw [if_neg (Nat.not_lt.mpr outside)]

/-- Bytes inside a store hold the matching byte of the stored value. -/
theorem mem_store_inside {m : Machine} {a : BitVec 64} {n k : Nat} {v : BitVec 64}
    (inside : k < n) (small : k < 2 ^ 64) :
    (m.store a n v).mem (a + BitVec.ofNat 64 k) = (v >>> (8 * k)).setWidth 8 := by
  -- The offset of the address from the start of the store is k itself.
  have offset : (a + BitVec.ofNat 64 k - a).toNat = k := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  simp only [store, offset, if_pos inside]

/-- A load that only reads memory agrees between machines that agree on its bytes. -/
theorem load_congr {m m' : Machine} {a : BitVec 64} :
    ∀ {n : Nat}, (∀ k < n, m.mem (a + BitVec.ofNat 64 k) = m'.mem (a + BitVec.ofNat 64 k)) →
      m.load a n = m'.load a n
  | 0, _ => rfl
  | n + 1, same => by
    -- The shorter load agrees, and so does the byte on top of it.
    simp only [load]
    rw [load_congr fun k within => same k (by omega), same n (by omega)]

@[simp] theorem load_write {m : Machine} {r : Reg} {v a : BitVec 64} {n : Nat} :
    (m.write r v).load a n = m.load a n :=
  -- A register write leaves every byte alone.
  load_congr fun _ _ => rfl

end Machine

@[simp] theorem execBlock_nil {m : Machine} : execBlock [] m = m :=
  rfl

@[simp] theorem execBlock_cons {i : Instr} {code : List Instr} {m : Machine} :
    execBlock (i :: code) m = execBlock code (i.run m) := by
  -- Stated through the fold lemma, so rewriting with it never asks the kernel to unfold the fold.
  simp only [execBlock, List.foldl_cons]

theorem execBlock_append {first second : List Instr} {m : Machine} :
    execBlock (first ++ second) m = execBlock second (execBlock first m) := by
  -- Running a concatenation is running each half in turn.
  simp [execBlock, List.foldl_append]

theorem runFor_add {program : Array Instr} {a b : Nat} {s : Cpu} :
    runFor program (a + b) s = runFor program b (runFor program a s) := by
  -- Peel instructions off the first count one at a time.
  induction a generalizing s with
  | zero => simp [runFor]
  | succ a ih =>
    rw [Nat.add_right_comm]
    exact ih

/--
Straight-line code laid out in a program runs as a block.

Control falls through every instruction, so the program counter ends just past the code.
-/
theorem runFor_block {program : Array Instr} :
    ∀ (code : List Instr) (s : Cpu),
      (∀ k (within : k < code.length), program[s.pc + k]? = some code[k]) →
      (∀ i ∈ code, i.straight) →
      runFor program code.length s = ⟨execBlock code s.m, s.pc + code.length⟩
  | [], s, _, _ => rfl
  | i :: code, s, here, straight => by
    -- The first instruction sits at the program counter and falls through.
    have first : program[s.pc]? = some i := here 0 (by simp)
    have falls : i.next s.m s.pc = s.pc + 1 := by
      have := straight i (by simp)
      cases i <;> simp_all [Instr.next, Instr.straight]
    -- The remaining instructions sit one index further on.
    have rest := runFor_block code ⟨i.run s.m, s.pc + 1⟩
      (fun k within => by
        have := here (k + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 k] using this)
      (fun j mem => straight j (by simp [mem]))
    simp only [List.length_cons, runFor, step, first, falls] at rest ⊢
    rw [rest]
    simp [Nat.add_assoc, Nat.add_comm 1]

/-- A piece of code sits inside a program assembled from it and its neighbours. -/
theorem here_of_append {before code after : List Instr} {k : Nat} (within : k < code.length) :
    (before ++ code ++ after).toArray[before.length + k]? = some code[k] := by
  -- Indexing past the prefix lands inside the code.
  simp [List.getElem?_append_right, List.getElem?_append_left, within]

end Ssz.Asm
