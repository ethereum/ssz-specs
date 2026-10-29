import SszNative.Proofs.Kernel.Avx512.Lanes
import SszNative.Proofs.Kernel.Avx512x2.View
import SszNative.Kernel.Avx2

/-!
One lane of the machine, memory included, for 256-bit code that moves whole 32-byte rows.

Lane l, below 8, of a row at an address is the word 4l bytes past it, so a row load or store moves each lane alone.
A store changes every row overlapping it, but a lane of a row that coincides with it or misses it changes as one lane.
So each of the eight lanes runs alone over the rows that every store either coincides with or misses.
-/

namespace Ssz.Native.Kernel.Avx2

open Ssz.Sha256 Ssz.Native.Asm
open Ssz.Native.Kernel.Avx512x2 (View addrOf readWord_bytes)

/-- Whether an instruction acts on each of the low eight lanes alone, moving memory only in whole 32-byte rows. -/
def rowwise : Instr → Bool
  | .ymov .. | .yadd .. | .yaddMem .. | .yxor .. | .yand .. | .yandn .. | .yor .. | .yshr .. | .yshl ..
  | .vloadHalf .. | .vstoreHalf .. => true
  | _ => false

/-- One lane after a rowwise instruction. -/
def viewStep (gpr : Gpr → UInt64) (v : View) : Instr → View
  | .ymov d a => { v with regs := assign v.regs d (v.regs a) }
  | .yadd d a b => { v with regs := assign v.regs d (v.regs a + v.regs b) }
  | .yaddMem d a m => { v with regs := assign v.regs d (v.regs a + v.mem (addrOf gpr m)) }
  | .yxor d a b => { v with regs := assign v.regs d (v.regs a ^^^ v.regs b) }
  | .yand d a b => { v with regs := assign v.regs d (v.regs a &&& v.regs b) }
  | .yandn d a b => { v with regs := assign v.regs d (~~~(v.regs a) &&& v.regs b) }
  | .yor d a b => { v with regs := assign v.regs d (v.regs a ||| v.regs b) }
  | .yshr d a k => { v with regs := assign v.regs d (if k < 32 then v.regs a >>> k.toUInt32 else 0) }
  | .yshl d a k => { v with regs := assign v.regs d (if k < 32 then v.regs a <<< k.toUInt32 else 0) }
  | .vloadHalf d m => { v with regs := assign v.regs d (v.mem (addrOf gpr m)) }
  | .vstoreHalf m r => { v with mem := assign v.mem (addrOf gpr m) (v.regs r) }
  | _ => v

/-- One lane after a list of rowwise instructions. -/
def viewRun (gpr : Gpr → UInt64) : List Instr → View → View
  | [], v => v
  | i :: rest, v => viewRun gpr rest (viewStep gpr v i)

/-- The address an instruction stores to, if it stores. -/
def storeOf (gpr : Gpr → UInt64) : Instr → Option Nat
  | .vstoreHalf m _ => some (addrOf gpr m)
  | _ => none

/-- The address an instruction reads, if it reads memory. -/
def readOf (gpr : Gpr → UInt64) : Instr → Option Nat
  | .yaddMem _ _ m | .vloadHalf _ m => some (addrOf gpr m)
  | _ => none

/-- Whether a row at an address coincides, lane for lane, with every row of a list of stores, or misses it. -/
def Clear (stores : List Nat) (a : Nat) : Prop :=
  ∀ A ∈ stores, a % 32 = A % 32 ∨ a + 32 ≤ A ∨ A + 32 ≤ a

/-- Lane l of the low eight, as a lane of the whole register. -/
def lane (l : Fin 8) : Fin 16 := ⟨l.val, by omega⟩

/-- A lane of a state, among the low eight. -/
def view (s : State) (l : Fin 8) : View :=
  ⟨fun r => s.vec r (lane l), fun a => readWord s.mem (a + 4 * l.val)⟩

/-- A half-row store, read back at its own address, gives the stored register's lane. -/
theorem readWord_store_same (mem : Nat → UInt8) (A : Nat) (v : Lanes) (l : Fin 8) :
    readWord (store mem A 32 (laneByte v)) (A + 4 * l.val) = v (lane l) := by
  -- Byte k of lane l is byte 4l + k of the stored row.
  apply readWord_bytes
  intro k hk
  have := l.isLt
  simp only [store, show A ≤ A + 4 * l.val + k ∧ A + 4 * l.val + k < A + 32 by omega, and_self, ↓reduceIte,
    laneByte, laneOf]
  rw [show A + 4 * l.val + k - A = 4 * l.val + k by omega]
  have same : (⟨(4 * l.val + k) / 4 % 16, by omega⟩ : Fin 16) = lane l := by
    apply Fin.ext; simp only [lane]; omega
  rw [same]
  simp only [wordByte]
  congr 3
  omega

/-- A half-row store leaves a lane of a row it misses, or coincides with only at another address. -/
theorem readWord_store_other (mem : Nat → UInt8) (A a : Nat) (v : Lanes) (l : Fin 8) (ne : a ≠ A)
    (clear : a % 32 = A % 32 ∨ a + 32 ≤ A ∨ A + 32 ≤ a) :
    readWord (store mem A 32 (laneByte v)) (a + 4 * l.val) = readWord mem (a + 4 * l.val) := by
  -- Rows at the same offset modulo 32, and distinct, are 32 bytes apart, so the lane misses the store.
  have := l.isLt
  have far : a + 32 ≤ A ∨ A + 32 ≤ a := by omega
  simp only [readWord, store]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- A rowwise instruction changes neither the general registers nor the flags. -/
theorem exec1_rowwise_regs (i : Instr) (h : rowwise i) (s : State) :
    (exec1 i s).gpr = s.gpr ∧ (exec1 i s).zf = s.zf ∧ (exec1 i s).cf = s.cf := by
  -- Each rowwise instruction writes a vector register or memory.
  cases i <;> simp [rowwise] at h <;> simp [exec1]

set_option maxHeartbeats 400000 in
/-- One rowwise instruction, on each of the low lanes and on every row clear of the stores still to come. -/
theorem exec1_view (i : Instr) (h : rowwise i) (s : State) (V : Fin 8 → View) (stores : List Nat)
    (hv : ∀ r l, s.vec r (lane l) = (V l).regs r)
    (hm : ∀ l a, Clear stores a → readWord s.mem (a + 4 * l.val) = (V l).mem a)
    (sub : ∀ A, storeOf s.gpr i = some A → A ∈ stores)
    (clear : ∀ a, readOf s.gpr i = some a → Clear stores a) :
    (∀ r l, (exec1 i s).vec r (lane l) = (viewStep s.gpr (V l) i).regs r) ∧
    (∀ l a, Clear stores a → readWord (exec1 i s).mem (a + 4 * l.val) = (viewStep s.gpr (V l) i).mem a) ∧
    (∀ x, (∀ A, storeOf s.gpr i = some A → x < A ∨ A + 32 ≤ x) → (exec1 i s).mem x = s.mem x) := by
  have hv' : ∀ r (l : Fin 8), s.vec r ⟨l.val, by omega⟩ = (V l).regs r := hv
  cases i <;> simp [rowwise] at h
  -- The register-only instructions: each lane reads and writes registers alone.
  case ymov d a | yadd d a b | yxor d a b | yand d a b | yandn d a b | yor d a b | yshr d a k | yshl d a k =>
    refine ⟨fun r l => ?_, fun l a ha => ?_, fun x _ => rfl⟩
    · simp only [exec1, viewStep, assign]; split <;> simp [ylanes, lane, hv']
    · simp only [exec1, viewStep]; exact hm l a ha
  -- The reads: each lane reads its word of a clear row.
  case yaddMem d a m | vloadHalf d m =>
    have row := clear _ rfl
    refine ⟨fun r l => ?_, fun l a ha => ?_, fun x _ => rfl⟩
    · simp only [exec1, viewStep, assign]
      split
      · rw [← hm l _ row]; simp [ylanes, lane, hv', addrOf, State.addr]
      · exact hv r l
    · simp only [exec1, viewStep]; exact hm l a ha
  -- The store: the row it writes takes the register's lane, and every other clear row keeps its lane.
  case vstoreHalf m r =>
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
A list of rowwise instructions runs lane by lane on the low eight lanes, on every row clear of its stores.

Memory outside its stores keeps its bytes, and the general registers and flags keep their values.
-/
theorem exec_view (body : List Instr) (h : ∀ i ∈ body, rowwise i) (s : State)
    (clear : ∀ a ∈ readsOf s.gpr body, Clear (storesOf s.gpr body) a) :
    (∀ r l, (exec body s).vec r (lane l) = (viewRun s.gpr body (view s l)).regs r) ∧
    (∀ l a, Clear (storesOf s.gpr body) a →
      readWord (exec body s).mem (a + 4 * l.val) = (viewRun s.gpr body (view s l)).mem a) ∧
    (∀ x, (∀ A ∈ storesOf s.gpr body, x < A ∨ A + 32 ≤ x) → (exec body s).mem x = s.mem x) ∧
    (exec body s).gpr = s.gpr ∧ (exec body s).zf = s.zf ∧ (exec body s).cf = s.cf := by
  -- Generalize over the lanes so far and over a list of stores that holds the ones still to come.
  suffices key : ∀ (body : List Instr), (∀ i ∈ body, rowwise i) → ∀ (s : State) (V : Fin 8 → View)
      (stores : List Nat), (∀ r l, s.vec r (lane l) = (V l).regs r) →
      (∀ l a, Clear stores a → readWord s.mem (a + 4 * l.val) = (V l).mem a) →
      (∀ A ∈ storesOf s.gpr body, A ∈ stores) → (∀ a ∈ readsOf s.gpr body, Clear stores a) →
      (∀ r l, (exec body s).vec r (lane l) = (viewRun s.gpr body (V l)).regs r) ∧
      (∀ l a, Clear stores a → readWord (exec body s).mem (a + 4 * l.val) = (viewRun s.gpr body (V l)).mem a) ∧
      (∀ x, (∀ A ∈ storesOf s.gpr body, x < A ∨ A + 32 ≤ x) → (exec body s).mem x = s.mem x) ∧
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
  | .ymov d _ | .yadd d _ _ | .yaddMem d _ _ | .yxor d _ _ | .yand d _ _ | .yandn d _ _ | .yor d _ _
  | .yshr d _ _ | .yshl d _ _ | .vloadHalf d _ => some d
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

end Ssz.Native.Kernel.Avx2
