import SszNative.Proofs.Kernel.Avx512x2.Lane
import SszNative.Proofs.Kernel.Avx512.Main

/-!
Tools for running the thirty-two-lane kernel: loops whose body is a straight block, and blocks of rowwise code.

A loop is a block followed by a branch back to its start while the zero flag is clear.
Run a number of times, it is the block run that many times, then the instruction after the branch.

A rowwise block reads and writes scratch rows through pointers into the scratch area, and reads table rows.
Each lane of it runs alone on the rows the invariants mention: scratch rows, and rows outside the scratch area.
-/

namespace EthLib.Consensus.Ssz.Native.Kernel.Avx512x2

open EthLib.Cryptography.Hash.Sha256 hiding K IV
open EthLib.Consensus.Ssz.Native.Asm
open EthLib.Consensus.Ssz.Native.Kernel.Avx512 (fetch step_jnz run_one assign_apply)

/-- One pass of a loop: the block, then the branch back or out. -/
theorem loop_iteration (p : Array Instr) (pre B post : List Instr)
    (layout : p.toList = pre ++ B ++ .jnz pre.length :: post) (straight : ∀ i ∈ B, i.straight) (x : State)
    (start : x.pc = pre.length) (running : x.status = .running) :
    run p (B.length + 1) x =
      { exec B x with pc := if (exec B x).zf then pre.length + B.length + 1 else pre.length } := by
  -- The block runs as straight-line code, then the branch reads the flag.
  have f := fetch _ _ _ _ (show p.toList = (pre ++ B) ++ .jnz pre.length :: post by rw [layout])
  rw [List.length_append] at f
  rw [run_add, run_block _ _ _ _ layout straight x start running, run_one,
    step_jnz _ _ pre.length f (by simpa using running)]

/--
A loop run a number of times: the block that many times, each time keeping an invariant, then out of the loop.

The invariant, numbered by the passes done, sets the zero flag after the block exactly on the last pass.
-/
theorem loop_run (p : Array Instr) (pre B post : List Instr)
    (layout : p.toList = pre ++ B ++ .jnz pre.length :: post) (straight : ∀ i ∈ B, i.straight)
    (Inv : Nat → State → Prop) (n : Nat) (hn : 0 < n)
    (step : ∀ i < n, ∀ x, x.pc = pre.length → x.status = .running → Inv i x →
      Inv (i + 1) (exec B x) ∧ ((exec B x).zf = true ↔ i + 1 = n))
    (x : State) (start : x.pc = pre.length) (running : x.status = .running) (inv : Inv 0 x) :
    ∃ y, Inv n y ∧ y.status = .running ∧ y.pc = pre.length ∧
      run p (n * (B.length + 1)) x = { y with pc := pre.length + B.length + 1 } := by
  -- Before the last pass, the loop is back at its start with the invariant of the passes so far.
  have before : ∀ i < n, ∃ y, Inv i y ∧ y.status = .running ∧ y.pc = pre.length ∧
      run p (i * (B.length + 1)) x = y := by
    intro i hi
    induction i with
    | zero => exact ⟨x, inv, running, start, by rw [Nat.zero_mul]; rfl⟩
    | succ i ih =>
      obtain ⟨y, iy, ry, py, hy⟩ := ih (by omega)
      obtain ⟨inv', last⟩ := step i (by omega) y py ry iy
      refine ⟨exec B y, inv', by simpa using ry, by simpa using py, ?_⟩
      rw [Nat.succ_mul, run_add, hy, loop_iteration p pre B post layout straight y py ry]
      have : (exec B y).zf = false := by
        cases h : (exec B y).zf
        · rfl
        · have := last.mp h; omega
      rw [this]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← py]
      cases e : exec B y
      simp only [State.mk.injEq]
      have := exec_pc B y
      rw [e] at this
      simp_all
  -- The last pass sets the flag, and the loop exits.
  obtain ⟨y, iy, ry, py, hy⟩ := before (n - 1) (by omega)
  obtain ⟨inv', last⟩ := step (n - 1) (by omega) y py ry iy
  rw [show n - 1 + 1 = n by omega] at inv' last
  refine ⟨exec B y, inv', by simpa using ry, by simpa using py, ?_⟩
  rw [show n * (B.length + 1) = (n - 1) * (B.length + 1) + (B.length + 1) by
    rw [← Nat.succ_mul, show (n - 1).succ = n by omega], run_add, hy,
    loop_iteration p pre B post layout straight y py ry, ite_eq_left (last.mpr rfl)]

/-- Whether a memory operand is a 64-byte-aligned row through the scratch base, or a row through the table base. -/
def rowOp (fb tb : Gpr) (fmax tmax : Nat) (m : Mem) : Bool :=
  (m.base == fb && m.disp % 64 == 0 && decide (m.disp ≤ fmax)) || (m.base == tb && decide (m.disp + 64 ≤ tmax))

/-- Whether an instruction is rowwise, reads only such rows, and stores only through the scratch base. -/
def shapeOK (fb tb : Gpr) (fmax tmax : Nat) : Instr → Bool
  | .vaddMem _ _ m | .vload _ m => rowOp fb tb fmax tmax m
  | .vstore m _ => m.base == fb && m.disp % 64 == 0 && decide (m.disp ≤ fmax)
  | i => rowwise i

/-- An address is a scratch row, or lies wholly outside the scratch area. -/
def RowOrOut (S a : Nat) : Prop := a % 64 = S % 64 ∨ a + 64 ≤ S ∨ S + frame ≤ a

/--
A rowwise block of the kernel, through a scratch base inside the scratch area and a table base inside the table.

Each lane runs alone on every scratch row and every row outside the scratch area.
Memory outside the scratch area keeps its bytes, and the general registers and flags keep their values.
-/
theorem exec_rows (body : List Instr) (fb tb : Gpr) (fmax tmax : Nat) (shape : body.all (shapeOK fb tb fmax tmax) = true)
    (x : State) (S T f0 t0 : Nat) (hf : (x.gpr fb).toNat = S + f0) (f0row : f0 % 64 = 0)
    (fIn : f0 + fmax + 64 ≤ frame) (ht : (x.gpr tb).toNat = T + t0) (tIn : t0 + tmax ≤ tableSize)
    (apart : FrameApart S T) :
    (∀ r l, (exec body x).vec r l = (viewRun x.gpr body (view x l)).regs r) ∧
    (∀ l a, RowOrOut S a → readWord (exec body x).mem (a + 4 * l.val) = (viewRun x.gpr body (view x l)).mem a) ∧
    (∀ a, a < S ∨ S + frame ≤ a → (exec body x).mem a = x.mem a) ∧
    (exec body x).gpr = x.gpr ∧ (exec body x).zf = x.zf ∧ (exec body x).cf = x.cf := by
  have each := List.all_eq_true.mp shape
  simp only [frame] at fIn
  -- Each store is a scratch row inside the scratch area.
  have stores : ∀ A ∈ storesOf x.gpr body, A % 64 = S % 64 ∧ S ≤ A ∧ A + 64 ≤ S + frame := by
    intro A hA
    obtain ⟨i, hi, hA⟩ := List.mem_filterMap.mp hA
    have := each i hi
    cases i <;> simp only [storeOf, reduceCtorEq] at hA
    rename_i m r
    simp only [Option.some.injEq] at hA
    subst hA
    simp only [shapeOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    obtain ⟨⟨base, row⟩, small⟩ := this
    simp only [addrOf, base, hf, frame]
    omega
  -- Each read is a scratch row, or a table row outside the scratch area.
  have reads : ∀ a ∈ readsOf x.gpr body, RowOrOut S a := by
    intro a ha
    obtain ⟨i, hi, ha⟩ := List.mem_filterMap.mp ha
    have := each i hi
    simp only [FrameApart, tableSize, frame] at apart tIn
    cases i <;> simp only [readOf, reduceCtorEq] at ha <;> simp only [Option.some.injEq] at ha <;> subst ha <;>
      simp only [shapeOK, rowOp, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this <;>
      rcases this with ⟨⟨base, row⟩, small⟩ | ⟨base, small⟩ <;> simp only [addrOf, base, hf, ht, RowOrOut, frame] <;>
      omega
  have clear : ∀ a, RowOrOut S a → Clear (storesOf x.gpr body) a := by
    intro a ha A hA
    obtain ⟨row, lo, hi⟩ := stores A hA
    simp only [RowOrOut, frame] at ha hi
    omega
  have rw' : ∀ i ∈ body, rowwise i := by
    intro i hi
    have := each i hi
    cases i <;> simp_all [shapeOK, rowwise]
  obtain ⟨v, m, f, g, z, c⟩ := exec_view body rw' x (fun a ha => clear a (reads a ha))
  refine ⟨v, fun l a ha => m l a (clear a ha), fun a ha => f a (fun A hA => ?_), g, z, c⟩
  obtain ⟨_, lo, hi⟩ := stores A hA
  omega

/-- Stores of registers to rows, one per index: each row takes its register's lane. -/
theorem viewRun_stores (G : Gpr → UInt64) (row : Nat → Nat) (reg : Nat → Vreg) (n : Nat) (v : View)
    (inj : ∀ u u', u < n → u' < n → row u = row u' → u = u') :
    ∀ u < n, (viewRun G ((List.range n).map fun u => .vstore ⟨sp, row u⟩ (reg u)) v).mem
      ((G sp).toNat + row u) = v.regs (reg u) := by
  induction n with
  | zero => intro u hu; omega
  | succ n ih =>
    intro u hu
    rw [List.range_succ, List.map_append, viewRun_append]
    simp only [List.map_cons, List.map_nil, viewRun, viewStep, addrOf]
    by_cases last : u = n
    · subst last; rw [assign_apply, ite_eq_left rfl]
      -- The earlier stores write no register.
      have keep : (viewRun G ((List.range u).map fun u => .vstore ⟨sp, row u⟩ (reg u)) v).regs = v.regs := by
        funext r
        apply viewRun_regs_other
        intro i hi
        obtain ⟨w, -, rfl⟩ := List.mem_map.mp hi
        simp [destOf]
      rw [keep]
    · rw [assign_apply, ite_eq_right (fun e => last (inj u n hu (by omega) (by omega)))]
      exact ih (fun a b ha hb => inj a b (by omega) (by omega)) u (by omega)

end EthLib.Consensus.Ssz.Native.Kernel.Avx512x2
