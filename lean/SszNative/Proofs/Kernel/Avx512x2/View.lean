import SszNative.Proofs.Kernel.Avx512.Rounds
import SszNative.Kernel.Avx512x2

/-!
One lane of the machine, memory included, for code that moves whole 64-byte rows between registers and memory.

The sixteen-lane kernel's compute core never touches memory but to read the table.
The thirty-two-lane kernel also keeps its schedule words and states in memory, in rows of 64 bytes.
Lane l of a row at an address is the word 4l bytes past it, so a row load or store moves each lane alone.

A store changes every row overlapping it, but a lane of a row that coincides with it or misses it changes as one lane.
So each lane runs alone over the rows that every store either coincides with or misses, lane for lane.
-/

namespace Ssz.Native.Kernel.Avx512x2

open Ssz.Sha256 Ssz.Native.Asm
open Ssz.Native.Kernel.Avx512 (laneStep laneRun lanewise assign_same assign_ne assign_apply)

/-- Whether an instruction acts on each lane alone, reading and writing memory only in whole 64-byte rows. -/
def rowwise : Instr → Bool
  | .vmov .. | .vadd .. | .vaddMem .. | .vror .. | .vshr .. | .vternlog .. | .vload .. | .vstore .. => true
  | _ => false

/-- One lane of the machine: that lane of every vector register, and that lane of the row at every address. -/
structure View where
  /-- The lane of each vector register. -/
  regs : Vreg → UInt32
  /-- The lane of the 64-byte row at each address: the word four bytes per lane past it. -/
  mem : Nat → UInt32

/-- The address a memory operand names, for given registers. -/
def addrOf (gpr : Gpr → UInt64) (m : Mem) : Nat := (gpr m.base).toNat + m.disp

/-- One lane after a rowwise instruction. -/
def viewStep (gpr : Gpr → UInt64) (v : View) : Instr → View
  | .vmov d a => { v with regs := assign v.regs d (v.regs a) }
  | .vadd d a b => { v with regs := assign v.regs d (v.regs a + v.regs b) }
  | .vaddMem d a m => { v with regs := assign v.regs d (v.regs a + v.mem (addrOf gpr m)) }
  | .vror d a k => { v with regs := assign v.regs d (rotr (v.regs a) k.toUInt32) }
  | .vshr d a k => { v with regs := assign v.regs d (if k < 32 then v.regs a >>> k.toUInt32 else 0) }
  | .vternlog d a b t => { v with regs := assign v.regs d (ternlog t.toNat.toUInt8 (v.regs d) (v.regs a) (v.regs b)) }
  | .vload d m => { v with regs := assign v.regs d (v.mem (addrOf gpr m)) }
  | .vstore m r => { v with mem := assign v.mem (addrOf gpr m) (v.regs r) }
  | _ => v

/-- One lane after a list of rowwise instructions. -/
def viewRun (gpr : Gpr → UInt64) : List Instr → View → View
  | [], v => v
  | i :: rest, v => viewRun gpr rest (viewStep gpr v i)

/-- The address an instruction stores to, if it stores. -/
def storeOf (gpr : Gpr → UInt64) : Instr → Option Nat
  | .vstore m _ => some (addrOf gpr m)
  | _ => none

/-- The address an instruction reads, if it reads memory. -/
def readOf (gpr : Gpr → UInt64) : Instr → Option Nat
  | .vaddMem _ _ m | .vload _ m => some (addrOf gpr m)
  | _ => none

/-- Whether a row at an address coincides, lane for lane, with every row of a list of stores, or misses it. -/
def Clear (stores : List Nat) (a : Nat) : Prop :=
  ∀ A ∈ stores, a % 64 = A % 64 ∨ a + 64 ≤ A ∨ A + 64 ≤ a

/-- A lane of a state. -/
def view (s : State) (l : Fin 16) : View :=
  ⟨fun r => s.vec r l, fun a => readWord s.mem (a + 4 * l.val)⟩

/-- A word whose four bytes are in memory reads back as that word. -/
theorem readWord_bytes (f : Nat → UInt8) (a : Nat) (w : UInt32) (h : ∀ k < 4, f (a + k) = wordByte w k) :
    readWord f a = w := by
  -- The four bytes recombine into the word, bit by bit.
  simp only [readWord]
  rw [show a = a + 0 from rfl, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega)]
  simp only [wordByte, Nat.zero_mod, Nat.mul_zero, Nat.one_mod, Nat.reduceMod, Nat.reduceMul]
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
  simp [-UInt32.toUInt32_toUInt8]

/-- A row store, read back at its own address, gives the stored register's lane. -/
theorem readWord_store_same (mem : Nat → UInt8) (A : Nat) (v : Lanes) (l : Fin 16) :
    readWord (store mem A 64 (laneByte v)) (A + 4 * l.val) = v l := by
  -- Byte k of lane l is byte 4l + k of the stored row.
  apply readWord_bytes
  intro k hk
  have := l.isLt
  simp only [store, show A ≤ A + 4 * l.val + k ∧ A + 4 * l.val + k < A + 64 by omega, and_self, ↓reduceIte,
    laneByte, laneOf]
  rw [show A + 4 * l.val + k - A = 4 * l.val + k by omega]
  have lane : (⟨(4 * l.val + k) / 4 % 16, by omega⟩ : Fin 16) = l := by
    apply Fin.ext; simp only; omega
  rw [lane]
  simp only [wordByte]
  congr 3
  omega

/-- A row store leaves a lane of a row it misses, or coincides with only at another address. -/
theorem readWord_store_other (mem : Nat → UInt8) (A a : Nat) (v : Lanes) (l : Fin 16) (ne : a ≠ A)
    (clear : a % 64 = A % 64 ∨ a + 64 ≤ A ∨ A + 64 ≤ a) :
    readWord (store mem A 64 (laneByte v)) (a + 4 * l.val) = readWord mem (a + 4 * l.val) := by
  -- Rows at the same offset modulo 64, and distinct, are 64 bytes apart, so the lane misses the store.
  have := l.isLt
  have far : a + 64 ≤ A ∨ A + 64 ≤ a := by omega
  simp only [readWord, store]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The row of a store or a read is the base register plus the displacement. -/
theorem state_addr (s : State) (m : Mem) : s.addr m = addrOf s.gpr m := rfl

/-- A rowwise instruction changes neither the general registers nor the flags. -/
theorem exec1_rowwise_regs (i : Instr) (h : rowwise i) (s : State) :
    (exec1 i s).gpr = s.gpr ∧ (exec1 i s).zf = s.zf ∧ (exec1 i s).cf = s.cf := by
  -- Each rowwise instruction writes a vector register or memory.
  cases i <;> simp [rowwise] at h <;> simp [exec1]

set_option maxHeartbeats 400000 in
/-- One rowwise instruction, on every lane and on every row clear of the stores still to come. -/
theorem exec1_view (i : Instr) (h : rowwise i) (s : State) (V : Fin 16 → View) (stores : List Nat)
    (hv : ∀ r l, s.vec r l = (V l).regs r) (hm : ∀ l a, Clear stores a → readWord s.mem (a + 4 * l.val) = (V l).mem a)
    (sub : ∀ A, storeOf s.gpr i = some A → A ∈ stores)
    (clear : ∀ a, readOf s.gpr i = some a → Clear stores a) :
    (∀ r l, (exec1 i s).vec r l = (viewStep s.gpr (V l) i).regs r) ∧
    (∀ l a, Clear stores a → readWord (exec1 i s).mem (a + 4 * l.val) = (viewStep s.gpr (V l) i).mem a) ∧
    (∀ x, (∀ A, storeOf s.gpr i = some A → x < A ∨ A + 64 ≤ x) → (exec1 i s).mem x = s.mem x) := by
  cases i <;> simp [rowwise] at h
  -- The register-only instructions: each lane reads and writes registers alone.
  case vmov d a | vadd d a b | vror d a k | vshr d a k | vternlog d a b t =>
    refine ⟨fun r l => ?_, fun l a ha => ?_, fun x _ => rfl⟩
    · simp only [exec1, viewStep, assign]; split <;> simp [hv]
    · simp only [exec1, viewStep]; exact hm l a ha
  -- The reads: each lane reads its word of a clear row.
  case vaddMem d a m | vload d m =>
    have row := clear _ rfl
    refine ⟨fun r l => ?_, fun l a ha => ?_, fun x _ => rfl⟩
    · simp only [exec1, viewStep, assign, hv, State.addr]
      split
      · rw [← hm l _ row]; rfl
      · exact hv r l
    · simp only [exec1, viewStep]; exact hm l a ha
  -- The store: the row it writes takes the register's lane, and every other clear row keeps its lane.
  case vstore m r =>
    have mine := sub _ rfl
    refine ⟨fun r' l => ?_, fun l a ha => ?_, fun x hx => ?_⟩
    · simp only [exec1, viewStep, hv]
    · simp only [exec1, viewStep, assign, State.addr]
      by_cases same : a = addrOf s.gpr m
      · rw [if_pos same, same]
        exact (readWord_store_same _ _ _ l).trans (hv r l)
      · rw [if_neg same, ← hm l a ha]
        exact readWord_store_other _ _ _ _ l same (ha _ mine)
    · have := hx _ rfl
      simp only [addrOf] at this
      simp only [exec1, store, State.addr]
      rw [if_neg (by omega)]

/-- The addresses a list stores to. -/
def storesOf (gpr : Gpr → UInt64) (body : List Instr) : List Nat := body.filterMap (storeOf gpr)

/-- The addresses a list reads. -/
def readsOf (gpr : Gpr → UInt64) (body : List Instr) : List Nat := body.filterMap (readOf gpr)

/--
A list of rowwise instructions runs lane by lane, on every row clear of its stores.

Memory outside its stores keeps its bytes, and the general registers and flags keep their values.
-/
theorem exec_view (body : List Instr) (h : ∀ i ∈ body, rowwise i) (s : State)
    (clear : ∀ a ∈ readsOf s.gpr body, Clear (storesOf s.gpr body) a) :
    (∀ r l, (exec body s).vec r l = (viewRun s.gpr body (view s l)).regs r) ∧
    (∀ l a, Clear (storesOf s.gpr body) a →
      readWord (exec body s).mem (a + 4 * l.val) = (viewRun s.gpr body (view s l)).mem a) ∧
    (∀ x, (∀ A ∈ storesOf s.gpr body, x < A ∨ A + 64 ≤ x) → (exec body s).mem x = s.mem x) ∧
    (exec body s).gpr = s.gpr ∧ (exec body s).zf = s.zf ∧ (exec body s).cf = s.cf := by
  -- Generalize over the lanes so far and over a list of stores that holds the ones still to come.
  suffices key : ∀ (body : List Instr), (∀ i ∈ body, rowwise i) → ∀ (s : State) (V : Fin 16 → View)
      (stores : List Nat), (∀ r l, s.vec r l = (V l).regs r) →
      (∀ l a, Clear stores a → readWord s.mem (a + 4 * l.val) = (V l).mem a) →
      (∀ A ∈ storesOf s.gpr body, A ∈ stores) → (∀ a ∈ readsOf s.gpr body, Clear stores a) →
      (∀ r l, (exec body s).vec r l = (viewRun s.gpr body (V l)).regs r) ∧
      (∀ l a, Clear stores a → readWord (exec body s).mem (a + 4 * l.val) = (viewRun s.gpr body (V l)).mem a) ∧
      (∀ x, (∀ A ∈ storesOf s.gpr body, x < A ∨ A + 64 ≤ x) → (exec body s).mem x = s.mem x) ∧
      (exec body s).gpr = s.gpr ∧ (exec body s).zf = s.zf ∧ (exec body s).cf = s.cf from
    key body h s (view s) _ (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ hA => hA) clear
  intro body
  induction body with
  | nil =>
    intro _ s V stores hv hm _ _
    exact ⟨hv, hm, fun _ _ => rfl, rfl, rfl, rfl⟩
  | cons i rest ih =>
    intro hrow s V stores hv hm sub clear
    have hi := hrow i (by simp)
    obtain ⟨g1, z1, c1⟩ := exec1_rowwise_regs i hi s
    obtain ⟨v1, m1, f1⟩ := exec1_view i hi s V stores hv hm
      (fun A hA => sub A (by simp [storesOf, hA]))
      (fun a ha => clear a (by simp [readsOf, ha]))
    -- The rest runs from the first instruction's lanes, with the same general registers.
    have := ih (fun j hj => hrow j (by simp [hj])) (exec1 i s) (fun l => viewStep s.gpr (V l) i) stores v1 m1
      (fun A hA => sub A (by rw [g1] at hA; simp only [storesOf, List.filterMap_cons]; split <;> simp_all [storesOf]))
      (fun a ha => clear a (by rw [g1] at ha; simp only [readsOf, List.filterMap_cons]; split <;> simp_all [readsOf]))
    obtain ⟨v2, m2, f2, g2, z2, c2⟩ := this
    rw [g1] at v2 m2 f2
    refine ⟨v2, m2, fun x hx => ?_, g2.trans g1, z2.trans z1, c2.trans c1⟩
    rw [exec_cons, f2 x (fun A hA => hx A (by simp only [storesOf, List.filterMap_cons]; split <;> simp_all [storesOf])),
      f1 x (fun A hA => hx A (by simp [storesOf, hA]))]

/-- An instruction that acts on registers alone. -/
def pure : Instr → Bool
  | .vmov .. | .vadd .. | .vror .. | .vshr .. | .vternlog .. => true
  | _ => false

/-- On registers alone, a lane runs as the sixteen-lane kernel's lanes do, whatever memory they would read. -/
theorem viewRun_pure (gpr : Gpr → UInt64) (body : List Instr) (h : ∀ i ∈ body, pure i) (v : View)
    (mem : Nat → UInt8) (l : Fin 16) : viewRun gpr body v = ⟨laneRun mem gpr l body v.regs, v.mem⟩ := by
  induction body generalizing v with
  | nil => rfl
  | cons i rest ih =>
    have hi := h i (by simp)
    -- The first instruction acts on registers as the register-only lane step does.
    have one : viewStep gpr v i = ⟨laneStep mem gpr l v.regs i, v.mem⟩ := by
      cases i <;> simp [pure] at hi <;> rfl
    simp only [viewRun, laneRun, one]
    exact ih (fun j hj => h j (by simp [hj])) _

/-- Lists run one after the other. -/
theorem viewRun_append (gpr : Gpr → UInt64) (a b : List Instr) (v : View) :
    viewRun gpr (a ++ b) v = viewRun gpr b (viewRun gpr a v) := by
  induction a generalizing v with
  | nil => rfl
  | cons i rest ih => exact ih _

/-- The blocks for indices below n + 1 run as those below n, then block n. -/
theorem viewRun_flatMap_succ (gpr : Gpr → UInt64) (f : Nat → List Instr) (n : Nat) (v : View) :
    viewRun gpr ((List.range (n + 1)).flatMap f) v = viewRun gpr (f n) (viewRun gpr ((List.range n).flatMap f) v) := by
  -- The range up to n + 1 is the range up to n, then n.
  rw [List.range_succ, List.flatMap_append, viewRun_append]
  simp

/-- The register an instruction writes, if it writes one. -/
def destOf : Instr → Option Vreg
  | .vmov d _ | .vadd d _ _ | .vaddMem d _ _ | .vror d _ _ | .vshr d _ _ | .vternlog d _ _ _ | .vload d _ => some d
  | _ => none

/-- A list leaves every register none of its instructions writes. -/
theorem viewRun_regs_other (gpr : Gpr → UInt64) (body : List Instr) (v : View) (r : Vreg)
    (h : ∀ i ∈ body, destOf i ≠ some r) : (viewRun gpr body v).regs r = v.regs r := by
  induction body generalizing v with
  | nil => rfl
  | cons i rest ih =>
    simp only [viewRun]
    rw [ih _ (fun j hj => h j (by simp [hj]))]
    -- The first instruction writes some other register, if any.
    have hi := h i (by simp)
    cases i <;> simp only [destOf, ne_eq, Option.some.injEq] at hi <;> simp [viewStep, assign, Ne.symm hi]

/-- A list leaves every row it does not store to. -/
theorem viewRun_mem_other (gpr : Gpr → UInt64) (body : List Instr) (v : View) (a : Nat)
    (h : ∀ i ∈ body, storeOf gpr i ≠ some a) : (viewRun gpr body v).mem a = v.mem a := by
  induction body generalizing v with
  | nil => rfl
  | cons i rest ih =>
    simp only [viewRun]
    rw [ih _ (fun j hj => h j (by simp [hj]))]
    -- The first instruction stores to some other row, if any.
    have hi := h i (by simp)
    cases i <;> simp only [storeOf, ne_eq, Option.some.injEq] at hi <;> simp [viewStep, assign, Ne.symm hi]

/-- Renaming registers by an involution renames a lane's registers, on the sixteen-lane kernel's lanes. -/
theorem laneRun_rename (f : Vreg → Vreg) (inv : ∀ r, f (f r) = r) (mem : Nat → UInt8) (gpr : Gpr → UInt64)
    (l : Fin 16) (body : List Instr) (regs : Vreg → UInt32) (r : Vreg) :
    laneRun mem gpr l (body.map (rename f)) regs r = laneRun mem gpr l body (fun x => regs (f x)) (f r) := by
  induction body generalizing regs with
  | nil => simp [laneRun, inv]
  | cons i rest ih =>
    simp only [List.map_cons, laneRun]
    rw [ih]
    congr 1
    -- One renamed instruction writes the renamed register with the renamed sources.
    funext x
    have swap : ∀ d, (f x = f d) = (x = d) := fun d =>
      propext ⟨fun e => by rw [← inv x, e, inv], fun e => e ▸ rfl⟩
    cases i <;> simp only [rename, laneStep, assign, swap]

/-- The second batch's renaming undoes itself. -/
theorem swapReg_swapReg : ∀ r, swapReg (swapReg r) = r := by
  -- Every register, checked by evaluation.
  decide

end Ssz.Native.Kernel.Avx512x2
