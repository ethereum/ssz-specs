import SszNative.Proofs.Ir.Leaf
import SszNative.Proofs.Kernel.Avx512.Main
import SszNative.Proofs.Kernel.Avx2.Main
import SszNative.Proofs.Kernel.Baseline.Main
import SszNative.Proofs.Kernel.Avx512x2.Main
import SszNative.Proofs.Kernel.ShaNi.Main
import SszNative.Proofs.Kernel.ShaNiDual.Main
import SszNative.Proofs.Kernel.GatherNode

/-!
The hand-written kernels as routines compiled code may call.

Each kernel's meaning is what its correctness theorem proves, read on the memory the language sees.
A call whose arguments break the theorem's hypotheses has no meaning, so the compiler's proof never relies on it.

The meanings return zero, and change only the output, which lies off the stack.
-/

namespace Ssz.Native.Ir

open Ssz.Native.Asm

/-- An instruction alone never changes the processor. -/
theorem exec1_cpu (i : Instr) (s : State) : (exec1 i s).cpu = s.cpu := by
  -- No instruction's own effect touches what the processor reports.
  cases i <;> first | rfl | (simp only [exec1]; split <;> rfl)

/-- A step never changes the processor. -/
theorem step_cpu (p : Array Instr) (s : State) : (step p s).cpu = s.cpu := by
  -- Every outcome of a step is the state, an instruction's effect, or either with control moved.
  unfold step
  split
  · rfl
  · split <;> (try split) <;> simp [exec1_cpu]

/-- A run never changes the processor. -/
theorem run_cpu (p : Array Instr) (n : Nat) (s : State) : (run p n s).cpu = s.cpu := by
  -- Each step keeps it.
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [run, ih, step_cpu]

/-- Bytes a program may use end within reach, and lie wholly below the stack or wholly above it. -/
theorem access_iff (w : World) (a n : Nat) :
    w.access a n = true ↔ a + n ≤ addressBound ∧ (a + n ≤ w.stackLo ∨ w.stackHi ≤ a) := by
  -- Both tests are plain comparisons.
  simp [World.access]

/-- Each byte of a range a program may use lies off the stack. -/
theorem access_off {w : World} {a n : Nat} (h : w.access a n = true) (k : Nat) (hk : k < n) :
    a + k < w.stackLo ∨ w.stackHi ≤ a + k := by
  -- The whole range is on one side of the stack.
  rw [access_iff] at h
  omega

/-- Each register the language's calls keep is one the calling convention saves. -/
theorem kept_saved (g : Gpr) (hg : g ∈ keptRegs) : g ∈ calleeSaved := by
  -- The kept registers are the saved ones, less the stack pointer.
  simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved]

/-- A straight-line instruction is not a call. -/
theorem not_call {i : Instr} (h : i.straight = true) (name : String) : i ≠ .call name := by
  -- A call is not straight-line.
  rintro rfl
  simp [Instr.straight] at h

/-! ## Hashing pairs -/

/--
Memory after hashing a count of pairs: digest p lands 32 p bytes past the output.

Pair p is the 32-byte node at the left address plus ls p, then the one at the right address plus rs p.
Every other byte is as it was.
-/
def hashed (mem : Memory) (out left right count ls rs : Nat) : Memory :=
  fun a =>
    if out ≤ a ∧ a < out + 32 * count then
      let p := (a - out) / 32
      (Sha256.hash (pairMessage mem (left + ls * p) (right + rs * p))).get! ((a - out) % 32)
    else mem a

/-- When hashing a count of pairs has a meaning: what the hashing kernels' theorems need, off the stack. -/
structure HashPre (w : World) (mem : Memory) (out left right count ls rs table : Nat) : Prop where
  /-- The constant table is in memory. -/
  tableAt : Kernel.TableAt mem table
  /-- The digests lie in memory the program may use. -/
  outAccess : w.access out (32 * count)
  /-- So does the constant table. -/
  tableAccess : w.access table Kernel.tableSize
  /-- So does every input node. -/
  inputsAccess : ∀ p < count, w.access (left + ls * p) 32 ∧ w.access (right + rs * p) 32
  /-- The left and right addresses, moved past every pair, stay within reach. -/
  reach : left + ls * count ≤ addressBound ∧ right + rs * count ≤ addressBound
  /-- The digests miss the table. -/
  tableApart : Apart (out, 32 * count) (table, Kernel.tableSize)
  /-- The digests miss every input node. -/
  inputsApart : ∀ p < count, Apart (out, 32 * count) (left + ls * p, 32) ∧ Apart (out, 32 * count) (right + rs * p, 32)

open Classical in
/--
A hashing kernel's meaning, for a number of pairs per unit of its count.

The arguments are the output, the left nodes, the right nodes, the count, and the constant table.
It has one only on a processor that runs the kernel, and only where the kernel's theorem holds.
-/
noncomputable def hashExtern (code : Array Instr) (batch ls rs : Nat) : Extern where
  run w _ args mem :=
    match args with
    | [out, left, right, count, table] =>
      if w.cpu.runs code = true ∧
          HashPre w mem out.toNat left.toNat right.toNat (batch * count.toNat) ls rs table.toNat then
        some (0, hashed mem out.toNat left.toNat right.toNat (batch * count.toNat) ls rs)
      else none
    | _ => none

/-- A hashing kernel's meaning, when it has one, unfolded. -/
theorem hashExtern_some {code : Array Instr} {batch ls rs : Nat} {w : World} {sp : Nat} {args : List UInt64}
    {mem mem' : Memory} {res : UInt64} (h : (hashExtern code batch ls rs).run w sp args mem = some (res, mem')) :
    ∃ out left right count table : UInt64, args = [out, left, right, count, table] ∧ w.cpu.runs code = true ∧
      HashPre w mem out.toNat left.toNat right.toNat (batch * count.toNat) ls rs table.toNat ∧ res = 0 ∧
      mem' = hashed mem out.toNat left.toNat right.toNat (batch * count.toNat) ls rs := by
  -- Only five arguments meeting the conditions give a meaning.
  simp only [hashExtern] at h
  split at h
  · split at h
    · rename_i _ out left right count table cond
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨out, left, right, count, table, rfl, cond.1, cond.2, h.1.symm, h.2.symm⟩
    · cases h
  · cases h

/-- The table seen through a memory that agrees off the stack is the same table. -/
theorem HashPre.transfer {w : World} {mem mem' : Memory} {out left right count ls rs table : Nat}
    (pre : HashPre w mem out left right count ls rs table) (agree : ∀ a, a < w.stackLo ∨ w.stackHi ≤ a → mem' a = mem a) :
    HashPre w mem' out left right count ls rs table := by
  -- The table lies off the stack, where the two memories agree.
  refine ⟨fun i hi => ?_, pre.outAccess, pre.tableAccess, pre.inputsAccess, pre.reach, pre.tableApart, pre.inputsApart⟩
  rw [agree _ (access_off pre.tableAccess i hi)]
  exact pre.tableAt i hi

/-- What a hashing kernel's theorem gives, from a start whose registers meet the meaning's conditions. -/
def HashRuns (w : World) (code : Array Instr) (batch ls rs : Nat) : Prop :=
  ∀ s : State, s.pc = 0 → s.status = .running →
    HashPre w s.mem (s.gpr .rdi).toNat (s.gpr .rsi).toNat (s.gpr .rdx).toNat (batch * (s.gpr .rcx).toNat) ls rs
      (s.gpr .r8).toNat →
    ∃ n, (run code n s).status = .returned ∧
      (∀ p < batch * (s.gpr .rcx).toNat, ∀ k < 32, (run code n s).mem ((s.gpr .rdi).toNat + 32 * p + k) =
        (Sha256.hash (pairMessage s.mem ((s.gpr .rsi).toNat + ls * p) ((s.gpr .rdx).toNat + rs * p))).get! k) ∧
      (∀ a, ¬ ((s.gpr .rdi).toNat ≤ a ∧ a < (s.gpr .rdi).toNat + 32 * (batch * (s.gpr .rcx).toNat)) →
        (run code n s).mem a = s.mem a) ∧
      (∀ r ∈ calleeSaved, (run code n s).gpr r = s.gpr r) ∧ (run code n s).gpr .rax = 0

/-- A hashing kernel whose theorem holds keeps the call contract of its meaning. -/
theorem hash_leafOk {w : World} {code : Array Instr} {batch ls rs : Nat} (runs : HashRuns w code batch ls rs) :
    LeafOk w code (hashExtern code batch ls rs) := by
  intro s sp args ir ir' res start running _ _ spLo _ _ _ argRegs heap spec
  obtain ⟨o, l, r, c, t, rfl, cr, pre, rfl, rfl⟩ := hashExtern_some spec
  -- The five arguments sit in the first five argument registers.
  have rdi : s.gpr .rdi = o := by simpa [argReg] using argRegs 0 (by simp)
  have rsi : s.gpr .rsi = l := by simpa [argReg] using argRegs 1 (by simp)
  have rdx : s.gpr .rdx = r := by simpa [argReg] using argRegs 2 (by simp)
  have rcx : s.gpr .rcx = c := by simpa [argReg] using argRegs 3 (by simp)
  have r8 : s.gpr .r8 = t := by simpa [argReg] using argRegs 4 (by simp)
  -- The kernel reads the table and the nodes off the stack, where the machine holds the language's memory.
  have pre' := pre.transfer heap
  rw [← rdi, ← rsi, ← rdx, ← rcx, ← r8] at pre'
  obtain ⟨n, st, outs, frame, saved, rax⟩ := runs s start running pre'
  simp only [rdi, rsi, rdx, rcx] at outs frame
  have outOff := (access_iff w _ _).mp pre.outAccess
  refine ⟨cr, n, st, rax, saved .rsp (by simp [calleeSaved]), fun g hg => saved g (kept_saved g hg),
    fun a ha => ?_, fun a lo hi => frame a (by omega), run_cpu _ _ _⟩
  unfold hashed
  by_cases inside : o.toNat ≤ a ∧ a < o.toNat + 32 * (batch * c.toNat)
  · -- Byte k of digest p: the kernel hashed the same two nodes the meaning reads.
    obtain ⟨p, k, hp, hk, rfl⟩ : ∃ p k, p < batch * c.toNat ∧ k < 32 ∧ a = o.toNat + 32 * p + k :=
      ⟨(a - o.toNat) / 32, (a - o.toNat) % 32, by omega, by omega, by omega⟩
    rw [if_pos inside, outs p hp k hk]
    simp only [show (o.toNat + 32 * p + k - o.toNat) / 32 = p by omega,
      show (o.toNat + 32 * p + k - o.toNat) % 32 = k by omega]
    obtain ⟨al, ar⟩ := pre.inputsAccess p hp
    rw [Kernel.Avx512.pairMessage_congr s.mem ir _ _ (fun i hi => heap _ (access_off al i hi))
      (fun i hi => heap _ (access_off ar i hi))]
  · -- Any other byte is as the kernel found it.
    rw [if_neg inside, frame a inside]
    exact heap a ha

open Classical in
/--
A hashing kernel's meaning when it keeps scratch bytes below its return address.

It is the meaning of hashing without scratch, given only when the stack has room for the scratch as well.
-/
noncomputable def hashFrameExtern (code : Array Instr) (batch ls rs frame : Nat) : Extern where
  run w sp args mem :=
    if w.stackLo + 8 + frame ≤ sp then (hashExtern code batch ls rs).run w sp args mem else none

/-- What a hashing kernel with scratch guarantees, from a start whose registers meet the meaning's conditions. -/
def HashFrameRuns (w : World) (code : Array Instr) (batch ls rs frame : Nat) : Prop :=
  ∀ s : State, s.pc = 0 → s.status = .running →
    HashPre w s.mem (s.gpr .rdi).toNat (s.gpr .rsi).toNat (s.gpr .rdx).toNat (batch * (s.gpr .rcx).toNat) ls rs
      (s.gpr .r8).toNat →
    w.stackLo + frame ≤ (s.gpr .rsp).toNat → (s.gpr .rsp).toNat ≤ w.stackHi → w.stackHi ≤ addressBound →
    ∃ n, (run code n s).status = .returned ∧
      (∀ p < batch * (s.gpr .rcx).toNat, ∀ k < 32, (run code n s).mem ((s.gpr .rdi).toNat + 32 * p + k) =
        (Sha256.hash (pairMessage s.mem ((s.gpr .rsi).toNat + ls * p) ((s.gpr .rdx).toNat + rs * p))).get! k) ∧
      (∀ a, ¬ ((s.gpr .rdi).toNat ≤ a ∧ a < (s.gpr .rdi).toNat + 32 * (batch * (s.gpr .rcx).toNat)) →
        ¬ ((s.gpr .rsp).toNat - frame ≤ a ∧ a < (s.gpr .rsp).toNat) → (run code n s).mem a = s.mem a) ∧
      (∀ r ∈ calleeSaved, (run code n s).gpr r = s.gpr r) ∧ (run code n s).gpr .rax = 0

/-- A hashing kernel with scratch whose theorem holds keeps the call contract of its meaning. -/
theorem hashFrame_leafOk {w : World} {code : Array Instr} {batch ls rs frame : Nat}
    (runs : HashFrameRuns w code batch ls rs frame) : LeafOk w code (hashFrameExtern code batch ls rs frame) := by
  intro s sp args ir ir' res start running _ rspAt spLo spHi hiBound _ argRegs heap spec
  simp only [hashFrameExtern] at spec
  split at spec
  rotate_left
  · cases spec
  rename_i room
  obtain ⟨o, l, r, c, t, rfl, cr, pre, rfl, rfl⟩ := hashExtern_some spec
  -- The five arguments sit in the first five argument registers.
  have rdi : s.gpr .rdi = o := by simpa [argReg] using argRegs 0 (by simp)
  have rsi : s.gpr .rsi = l := by simpa [argReg] using argRegs 1 (by simp)
  have rdx : s.gpr .rdx = r := by simpa [argReg] using argRegs 2 (by simp)
  have rcx : s.gpr .rcx = c := by simpa [argReg] using argRegs 3 (by simp)
  have r8 : s.gpr .r8 = t := by simpa [argReg] using argRegs 4 (by simp)
  -- The stack pointer sits eight bytes below the caller's, with room for the scratch below it.
  have spNat : (s.gpr .rsp).toNat = sp - 8 := by
    rw [rspAt]; simp only [addressBound] at hiBound; simp; omega
  -- The kernel reads the table and the nodes off the stack, where the machine holds the language's memory.
  have pre' := pre.transfer heap
  rw [← rdi, ← rsi, ← rdx, ← rcx, ← r8] at pre'
  obtain ⟨n, st, outs, frame', saved, rax⟩ := runs s start running pre' (by omega) (by omega) hiBound
  simp only [rdi, rsi, rdx, rcx, spNat] at outs frame'
  have outOff := (access_iff w _ _).mp pre.outAccess
  refine ⟨cr, n, st, rax, saved .rsp (by simp [calleeSaved]), fun g hg => saved g (kept_saved g hg),
    fun a ha => ?_, fun a lo hi => frame' a (by omega) (by omega), run_cpu _ _ _⟩
  unfold hashed
  by_cases inside : o.toNat ≤ a ∧ a < o.toNat + 32 * (batch * c.toNat)
  · -- Byte k of digest p: the kernel hashed the same two nodes the meaning reads.
    obtain ⟨p, k, hp, hk, rfl⟩ : ∃ p k, p < batch * c.toNat ∧ k < 32 ∧ a = o.toNat + 32 * p + k :=
      ⟨(a - o.toNat) / 32, (a - o.toNat) % 32, by omega, by omega, by omega⟩
    rw [if_pos inside, outs p hp k hk]
    simp only [show (o.toNat + 32 * p + k - o.toNat) / 32 = p by omega,
      show (o.toNat + 32 * p + k - o.toNat) % 32 = k by omega]
    obtain ⟨al, ar⟩ := pre.inputsAccess p hp
    rw [Kernel.Avx512.pairMessage_congr s.mem ir _ _ (fun i hi => heap _ (access_off al i hi))
      (fun i hi => heap _ (access_off ar i hi))]
  · -- Any other byte is as the kernel found it: the scratch lies on the stack, and this byte off it.
    rw [if_neg inside, frame' a inside (by omega)]
    exact heap a ha

/-- The sixteen-lane kernel's theorem, in the shape the call contract reads. -/
theorem avx512_runs (w : World) (ls rs : Nat) : HashRuns w (Kernel.Avx512.program ls rs) 16 ls rs := by
  intro s start running pre
  exact Kernel.Avx512.program_correct ls rs s start running pre.tableAt _ rfl ((access_iff w _ _).mp pre.outAccess).1
    pre.reach.1 pre.reach.2 pre.tableApart pre.inputsApart

/-- The one-pair SHA-NI kernel's theorem, in the shape the call contract reads. -/
theorem shani_runs (w : World) (ls rs : Nat) : HashRuns w (Kernel.ShaNi.program ls rs) 1 ls rs := by
  intro s start running pre
  simp only [Nat.one_mul] at pre ⊢
  exact Kernel.ShaNi.program_correct ls rs s start running pre.tableAt
    ⟨((access_iff w _ _).mp pre.outAccess).1, fun p hp =>
      ⟨((access_iff w _ _).mp (pre.inputsAccess p hp).1).1, ((access_iff w _ _).mp (pre.inputsAccess p hp).2).1⟩⟩
    ⟨pre.tableApart, pre.inputsApart⟩

/-- The two-pair SHA-NI kernel's theorem, in the shape the call contract reads. -/
theorem shaniDual_runs (w : World) (ls rs : Nat) : HashRuns w (Kernel.ShaNiDual.program ls rs) 2 ls rs := by
  intro s start running pre
  exact Kernel.ShaNiDual.program_correct ls rs s start running pre.tableAt
    ⟨((access_iff w _ _).mp pre.outAccess).1, fun p hp =>
      ⟨((access_iff w _ _).mp (pre.inputsAccess p hp).1).1, ((access_iff w _ _).mp (pre.inputsAccess p hp).2).1⟩⟩
    ⟨pre.tableApart, pre.inputsApart⟩

/-- The sixteen-lane kernel keeps the call contract of hashing sixteen pairs per unit of its count. -/
theorem avx512_leafOk (w : World) (ls rs : Nat) :
    LeafOk w (Kernel.Avx512.program ls rs) (hashExtern (Kernel.Avx512.program ls rs) 16 ls rs) :=
  hash_leafOk (avx512_runs w ls rs)

/-- The one-pair SHA-NI kernel keeps the call contract of hashing one pair per unit of its count. -/
theorem shani_leafOk (w : World) (ls rs : Nat) :
    LeafOk w (Kernel.ShaNi.program ls rs) (hashExtern (Kernel.ShaNi.program ls rs) 1 ls rs) :=
  hash_leafOk (shani_runs w ls rs)

/-- The two-pair SHA-NI kernel keeps the call contract of hashing two pairs per unit of its count. -/
theorem shaniDual_leafOk (w : World) (ls rs : Nat) :
    LeafOk w (Kernel.ShaNiDual.program ls rs) (hashExtern (Kernel.ShaNiDual.program ls rs) 2 ls rs) :=
  hash_leafOk (shaniDual_runs w ls rs)

/-- The sixteen-lane kernel calls nothing. -/
theorem avx512_leaf (ls rs : Nat) : Leaf (Kernel.Avx512.program ls rs) := by
  intro i hi name
  rintro rfl
  rw [Kernel.Avx512.program_toList] at hi
  -- The batch is straight-line code, and no other instruction is a call.
  simp [Kernel.Avx512.tailCode] at hi
  simpa [Instr.straight] using Kernel.Avx512.batch_straight ls rs _ hi

/-- The one-pair SHA-NI kernel calls nothing. -/
theorem shani_leaf (ls rs : Nat) : Leaf (Kernel.ShaNi.program ls rs) := by
  intro i hi name
  rintro rfl
  rw [Kernel.ShaNi.program_list] at hi
  -- The body is straight-line code, and no other instruction is a call.
  simp [Kernel.ShaNi.opening] at hi
  simpa [Instr.straight] using Kernel.ShaNi.body_straight ls rs _ hi

/-- The eight-lane AVX2 kernel's theorem, in the shape the call contract reads. -/
theorem avx2_runs (w : World) (ls rs : Nat) :
    HashFrameRuns w (Kernel.Avx2.program ls rs) 8 ls rs Kernel.Avx2.frame := by
  intro s start running pre lo hi hiBound
  have outOff := (access_iff w _ _).mp pre.outAccess
  have tableOff := (access_iff w _ _).mp pre.tableAccess
  -- The scratch area lies on the stack, and the output, the table, and the inputs off it.
  exact Kernel.Avx2.program_correct ls rs s start running pre.tableAt _ rfl
    (show Kernel.Avx2.frame ≤ (s.gpr .rsp).toNat by omega) (show (s.gpr .rsp).toNat ≤ addressBound by omega)
    tableOff.1 outOff.1 pre.reach.1 pre.reach.2 pre.tableApart pre.inputsApart
    ⟨show Apart ((s.gpr .rsp).toNat - _, _) ((s.gpr .r8).toNat, _) by simp only [Apart]; omega,
      show Apart ((s.gpr .rdi).toNat, _) ((s.gpr .rsp).toNat - _, _) by simp only [Apart]; omega, fun p hp => by
      have al := (access_iff w _ _).mp (pre.inputsAccess p hp).1
      have ar := (access_iff w _ _).mp (pre.inputsAccess p hp).2
      show Apart ((s.gpr .rsp).toNat - _, _) ((s.gpr .rsi).toNat + _, _) ∧
        Apart ((s.gpr .rsp).toNat - _, _) ((s.gpr .rdx).toNat + _, _)
      simp only [Apart]; omega⟩

/-- The eight-lane AVX2 kernel keeps the call contract of hashing eight pairs per unit of its count. -/
theorem avx2_leafOk (w : World) (ls rs : Nat) :
    LeafOk w (Kernel.Avx2.program ls rs) (hashFrameExtern (Kernel.Avx2.program ls rs) 8 ls rs Kernel.Avx2.frame) :=
  hashFrame_leafOk (avx2_runs w ls rs)

/-- The four-lane SSE2 kernel's theorem, in the shape the call contract reads. -/
theorem baseline_runs (w : World) (ls rs : Nat) :
    HashFrameRuns w (Kernel.Baseline.program ls rs) 4 ls rs Kernel.Baseline.frame := by
  intro s start running pre lo hi hiBound
  have outOff := (access_iff w _ _).mp pre.outAccess
  have tableOff := (access_iff w _ _).mp pre.tableAccess
  -- The scratch area lies on the stack, and the output, the table, and the inputs off it.
  exact Kernel.Baseline.program_correct ls rs s start running pre.tableAt _ rfl
    (show Kernel.Baseline.frame ≤ (s.gpr .rsp).toNat by omega) (show (s.gpr .rsp).toNat ≤ addressBound by omega)
    tableOff.1 outOff.1 pre.reach.1 pre.reach.2 pre.tableApart pre.inputsApart
    ⟨show Apart ((s.gpr .rsp).toNat - _, _) ((s.gpr .r8).toNat, _) by simp only [Apart]; omega,
      show Apart ((s.gpr .rdi).toNat, _) ((s.gpr .rsp).toNat - _, _) by simp only [Apart]; omega, fun p hp => by
      have al := (access_iff w _ _).mp (pre.inputsAccess p hp).1
      have ar := (access_iff w _ _).mp (pre.inputsAccess p hp).2
      show Apart ((s.gpr .rsp).toNat - _, _) ((s.gpr .rsi).toNat + _, _) ∧
        Apart ((s.gpr .rsp).toNat - _, _) ((s.gpr .rdx).toNat + _, _)
      simp only [Apart]; omega⟩

/-- The four-lane SSE2 kernel keeps the call contract of hashing four pairs per unit of its count. -/
theorem baseline_leafOk (w : World) (ls rs : Nat) :
    LeafOk w (Kernel.Baseline.program ls rs)
      (hashFrameExtern (Kernel.Baseline.program ls rs) 4 ls rs Kernel.Baseline.frame) :=
  hashFrame_leafOk (baseline_runs w ls rs)

/-- The four-lane SSE2 kernel calls nothing. -/
theorem baseline_leaf (ls rs : Nat) : Leaf (Kernel.Baseline.program ls rs) := Kernel.Baseline.leaf ls rs

/-- The thirty-two-lane AVX-512 kernel's theorem, in the shape the call contract reads. -/
theorem avx512x2_runs (w : World) (ls rs : Nat) :
    HashFrameRuns w (Kernel.Avx512x2.program ls rs) 32 ls rs Kernel.Avx512x2.frame := by
  intro s start running pre lo hi hiBound
  have outOff := (access_iff w _ _).mp pre.outAccess
  have tableOff := (access_iff w _ _).mp pre.tableAccess
  -- The scratch area lies on the stack, and the output, the table, and the inputs off it.
  obtain ⟨n, st, outs, frame, saved, rax⟩ := Kernel.Avx512x2.program_correct ls rs s start running pre.tableAt _ rfl
    (show Kernel.Avx512x2.frame ≤ (s.gpr .rsp).toNat by omega) (show (s.gpr .rsp).toNat ≤ addressBound by omega)
    outOff.1 pre.reach.1 pre.reach.2 tableOff.1 pre.tableApart pre.inputsApart
    (show Apart ((s.gpr .rsp).toNat - _, _) ((s.gpr .r8).toNat, _) by simp only [Apart]; omega)
    (show Apart ((s.gpr .rdi).toNat, 32 * (32 * (s.gpr .rcx).toNat)) ((s.gpr .rsp).toNat - _, _) by
      simp only [Apart]; omega)
    (fun p hp => by
      have al := (access_iff w _ _).mp (pre.inputsAccess p hp).1
      have ar := (access_iff w _ _).mp (pre.inputsAccess p hp).2
      show Apart ((s.gpr .rsi).toNat + _, _) ((s.gpr .rsp).toNat - _, _) ∧
        Apart ((s.gpr .rdx).toNat + _, _) ((s.gpr .rsp).toNat - _, _)
      simp only [Apart]; omega)
  exact ⟨n, st, outs, fun a h1 h2 => frame a h1 (show a < (s.gpr .rsp).toNat - _ ∨ (s.gpr .rsp).toNat ≤ a by omega),
    saved, rax⟩

/-- The thirty-two-lane AVX-512 kernel keeps the call contract of hashing thirty-two pairs per unit of its count. -/
theorem avx512x2_leafOk (w : World) (ls rs : Nat) :
    LeafOk w (Kernel.Avx512x2.program ls rs)
      (hashFrameExtern (Kernel.Avx512x2.program ls rs) 32 ls rs Kernel.Avx512x2.frame) :=
  hashFrame_leafOk (avx512x2_runs w ls rs)

/-- The thirty-two-lane AVX-512 kernel calls nothing. -/
theorem avx512x2_leaf (ls rs : Nat) : Leaf (Kernel.Avx512x2.program ls rs) := Kernel.Avx512x2.leaf ls rs

/-- The eight-lane AVX2 kernel calls nothing. -/
theorem avx2_leaf (ls rs : Nat) : Leaf (Kernel.Avx2.program ls rs) := Kernel.Avx2.leaf ls rs

/-- The two-pair SHA-NI kernel calls nothing. -/
theorem shaniDual_leaf (ls rs : Nat) : Leaf (Kernel.ShaNiDual.program ls rs) := by
  intro i hi name
  rintro rfl
  rw [Kernel.ShaNiDual.program_list] at hi
  -- The body is straight-line code, and no other instruction is a call.
  simp [Kernel.ShaNiDual.opening] at hi
  simpa [Instr.straight] using Kernel.ShaNiDual.body_straight ls rs _ hi

/-! ## Gathering fields -/

/--
Memory after gathering a count of records' fields into slots of a width plus a pad.

Slot i holds the width bytes at the source plus i times the width plus the skip, then pad zero bytes.
Every other byte is as it was.
-/
def gathered (mem : Memory) (out src count width skip pad : Nat) : Memory :=
  fun a =>
    if out ≤ a ∧ a < out + (width + pad) * count then Kernel.recordByte mem out src width skip pad a else mem a

/-- When gathering a count of fields has a meaning: what the gathering kernels' theorems need, off the stack. -/
structure GatherPre (w : World) (out src count width skip pad : Nat) : Prop where
  /-- The slots lie in memory the program may use. -/
  outAccess : w.access out ((width + pad) * count)
  /-- So does every field. -/
  srcAccess : ∀ i < count, w.access (src + (width + skip) * i) width
  /-- The source address, moved past every record, stays within reach. -/
  reach : src + (width + skip) * count ≤ addressBound
  /-- The slots miss every field. -/
  apart : ∀ i < count, Apart (out, (width + pad) * count) (src + (width + skip) * i, width)

open Classical in
/--
A gathering kernel's meaning.

The arguments are the output, the first field, the count, the field width, the skip, and the pad.
A kernel for one field width and slot fixes the width and the pad, and has a meaning only for those.
It has one only on a processor that runs the kernel, and only where the kernel's theorem holds.
-/
noncomputable def gatherExtern (code : Array Instr) (fixed : Option (Nat × Nat)) : Extern where
  run w _ args mem :=
    match args with
    | [out, src, count, width, skip, pad] =>
      if w.cpu.runs code = true ∧ (∀ f ∈ fixed, width.toNat = f.1 ∧ pad.toNat = f.2) ∧
          GatherPre w out.toNat src.toNat count.toNat width.toNat skip.toNat pad.toNat then
        some (0, gathered mem out.toNat src.toNat count.toNat width.toNat skip.toNat pad.toNat)
      else none
    | _ => none

/-- A gathering kernel's meaning, when it has one, unfolded. -/
theorem gatherExtern_some {code : Array Instr} {fixed : Option (Nat × Nat)} {w : World} {sp : Nat}
    {args : List UInt64} {mem mem' : Memory} {res : UInt64}
    (h : (gatherExtern code fixed).run w sp args mem = some (res, mem')) :
    ∃ out src count width skip pad : UInt64, args = [out, src, count, width, skip, pad] ∧
      w.cpu.runs code = true ∧ (∀ f ∈ fixed, width.toNat = f.1 ∧ pad.toNat = f.2) ∧
      GatherPre w out.toNat src.toNat count.toNat width.toNat skip.toNat pad.toNat ∧ res = 0 ∧
      mem' = gathered mem out.toNat src.toNat count.toNat width.toNat skip.toNat pad.toNat := by
  -- Only six arguments meeting the conditions give a meaning.
  simp only [gatherExtern] at h
  split at h
  · split at h
    · rename_i _ out src count width skip pad cond
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨out, src, count, width, skip, pad, rfl, cond.1, cond.2.1, cond.2.2, h.1.symm, h.2.symm⟩
    · cases h
  · cases h

/-- What a gathering kernel's theorem gives, from a start whose registers meet the meaning's conditions. -/
def GatherRuns (w : World) (code : Array Instr) (fixed : Option (Nat × Nat)) : Prop :=
  ∀ s : State, s.pc = 0 → s.status = .running →
    (∀ f ∈ fixed, (s.gpr .rcx).toNat = f.1 ∧ (s.gpr .r9).toNat = f.2) →
    GatherPre w (s.gpr .rdi).toNat (s.gpr .rsi).toNat (s.gpr .rdx).toNat (s.gpr .rcx).toNat (s.gpr .r8).toNat
      (s.gpr .r9).toNat →
    ∃ n, (run code n s).status = .returned ∧
      (∀ i < (s.gpr .rdx).toNat, ∀ k < (s.gpr .rcx).toNat + (s.gpr .r9).toNat,
        (run code n s).mem ((s.gpr .rdi).toNat + ((s.gpr .rcx).toNat + (s.gpr .r9).toNat) * i + k) =
          if k < (s.gpr .rcx).toNat then
            s.mem ((s.gpr .rsi).toNat + ((s.gpr .rcx).toNat + (s.gpr .r8).toNat) * i + k)
          else 0) ∧
      (∀ a, ¬ ((s.gpr .rdi).toNat ≤ a ∧
          a < (s.gpr .rdi).toNat + ((s.gpr .rcx).toNat + (s.gpr .r9).toNat) * (s.gpr .rdx).toNat) →
        (run code n s).mem a = s.mem a) ∧
      (∀ r ∈ calleeSaved, (run code n s).gpr r = s.gpr r) ∧ (run code n s).gpr .rax = 0

/-- A gathering kernel whose theorem holds keeps the call contract of its meaning. -/
theorem gather_leafOk_of {w : World} {code : Array Instr} {fixed : Option (Nat × Nat)}
    (runs : GatherRuns w code fixed) : LeafOk w code (gatherExtern code fixed) := by
  intro s sp args ir ir' res start running _ _ spLo _ _ _ argRegs heap spec
  obtain ⟨o, src, c, wd, sk, pd, rfl, cr, fix, pre, rfl, rfl⟩ := gatherExtern_some spec
  -- The six arguments sit in the six argument registers.
  have rdi : s.gpr .rdi = o := by simpa [argReg] using argRegs 0 (by simp)
  have rsi : s.gpr .rsi = src := by simpa [argReg] using argRegs 1 (by simp)
  have rdx : s.gpr .rdx = c := by simpa [argReg] using argRegs 2 (by simp)
  have rcx : s.gpr .rcx = wd := by simpa [argReg] using argRegs 3 (by simp)
  have r8 : s.gpr .r8 = sk := by simpa [argReg] using argRegs 4 (by simp)
  have r9 : s.gpr .r9 = pd := by simpa [argReg] using argRegs 5 (by simp)
  have pre' := pre
  have fix' := fix
  rw [← rdi, ← rsi, ← rdx, ← rcx, ← r8, ← r9] at pre'
  rw [← rcx, ← r9] at fix'
  obtain ⟨n, st, outs, frame, saved, rax⟩ := runs s start running fix' pre'
  simp only [rdi, rsi, rdx, rcx, r8, r9] at outs frame
  have outOff := (access_iff w _ _).mp pre.outAccess
  refine ⟨cr, n, st, rax, saved .rsp (by simp [calleeSaved]), fun g hg => saved g (kept_saved g hg),
    fun a ha => ?_, fun a lo hi => frame a (by omega), run_cpu _ _ _⟩
  unfold gathered
  by_cases inside : o.toNat ≤ a ∧ a < o.toNat + (wd.toNat + pd.toNat) * c.toNat
  · -- Byte k of slot i: a field byte the kernel read off the stack, or a zero.
    have pos : 0 < wd.toNat + pd.toNat := by
      apply Nat.pos_of_ne_zero
      intro z
      rw [z, Nat.zero_mul] at inside
      omega
    obtain ⟨i, k, hi, hk, rfl⟩ : ∃ i k, i < c.toNat ∧ k < wd.toNat + pd.toNat ∧
        a = o.toNat + (wd.toNat + pd.toNat) * i + k := by
      have split := Nat.div_add_mod (a - o.toNat) (wd.toNat + pd.toNat)
      refine ⟨(a - o.toNat) / (wd.toNat + pd.toNat), (a - o.toNat) % (wd.toNat + pd.toNat), ?_,
        Nat.mod_lt _ pos, by omega⟩
      apply Nat.lt_of_mul_lt_mul_left (a := wd.toNat + pd.toNat)
      omega
    rw [if_pos inside, outs i hi k hk, Kernel.recordByte_at _ _ _ _ _ _ _ _ hk]
    by_cases field : k < wd.toNat
    · rw [if_pos field, if_pos field]
      exact heap _ (access_off (pre.srcAccess i hi) k field)
    · rw [if_neg field, if_neg field]
  · -- Any other byte is as the kernel found it.
    rw [if_neg inside, frame a inside]
    exact heap a ha

/-- The general gathering kernel's theorem, in the shape the call contract reads. -/
theorem gather_runs (w : World) : GatherRuns w Kernel.gather none := by
  intro s start running _ pre
  exact Kernel.gather_correct s _ _ _ _ _ _ start running rfl rfl rfl rfl rfl rfl
    ((access_iff w _ _).mp pre.outAccess).1 pre.reach
    (fun i hi k hk => by have := pre.apart i hi; simp only [Apart] at this; omega)

/-- The gathering kernel for one field width's theorem, in the shape the call contract reads. -/
theorem gatherNode_runs (w : World) (width : Nat) (known : width ∈ [1, 2, 4, 8, 16, 32]) :
    GatherRuns w (Kernel.gatherNode width) (some (width, 32 - width)) := by
  intro s start running fix pre
  obtain ⟨hw, hp⟩ := fix _ rfl
  simp only at hw hp
  have small : width ≤ 32 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at known
    omega
  -- The slot is the width plus the pad: 32 bytes.
  have slot : (s.gpr .rcx).toNat + (s.gpr .r9).toNat = 32 := by omega
  have outB := ((access_iff w _ _).mp pre.outAccess).1
  have reach := pre.reach
  have apart := pre.apart
  rw [slot] at outB apart ⊢
  rw [hw] at reach apart ⊢
  exact Kernel.gatherNode_correct width known s _ _ _ _ start running rfl rfl rfl rfl outB reach
    (fun i hi k hk => by have := apart i hi; simp only [Apart] at this; omega)

/-- The public-key gathering kernel's theorem, in the shape the call contract reads. -/
theorem gatherKey_runs (w : World) : GatherRuns w Kernel.gatherKey (some (48, 16)) := by
  intro s start running fix pre
  obtain ⟨hw, hp⟩ := fix _ rfl
  simp only at hw hp
  -- The slot is the 48-byte key plus 16 zero bytes.
  have slot : (s.gpr .rcx).toNat + (s.gpr .r9).toNat = 64 := by omega
  have outB := ((access_iff w _ _).mp pre.outAccess).1
  have reach := pre.reach
  have apart := pre.apart
  rw [slot] at outB apart ⊢
  rw [hw] at reach apart ⊢
  exact Kernel.gatherKey_correct s _ _ _ _ start running rfl rfl rfl rfl outB reach
    (fun i hi k hk => by have := apart i hi; simp only [Apart] at this; omega)

/-- The general gathering kernel keeps the call contract of gathering fields of any width into padded slots. -/
theorem gather_leafOk (w : World) : LeafOk w Kernel.gather (gatherExtern Kernel.gather none) :=
  gather_leafOk_of (gather_runs w)

/-- The gathering kernel for one field width keeps the call contract of gathering fields of that width into 32-byte slots. -/
theorem gatherNode_leafOk (w : World) (width : Nat) (h : width ∈ [1, 2, 4, 8, 16, 32]) :
    LeafOk w (Kernel.gatherNode width) (gatherExtern (Kernel.gatherNode width) (some (width, 32 - width))) :=
  gather_leafOk_of (gatherNode_runs w width h)

/-- The public-key gathering kernel keeps the call contract of gathering 48-byte fields into 64-byte slots. -/
theorem gatherKey_leafOk (w : World) :
    LeafOk w Kernel.gatherKey (gatherExtern Kernel.gatherKey (some (48, 16))) :=
  gather_leafOk_of (gatherKey_runs w)

/-- The general gathering kernel calls nothing. -/
theorem gather_leaf : Leaf Kernel.gather := by
  -- Every instruction is listed, and none is a call.
  intro i hi name
  rintro rfl
  simp [Kernel.gather] at hi

/-- A routine of the gathering shape calls nothing. -/
theorem shape_leaf {program : Array Instr} {code : List Instr} (shape : Kernel.Shape program code) : Leaf program := by
  intro i hi name
  rintro rfl
  rw [shape.1] at hi
  -- The record is straight-line code, and no other instruction is a call.
  simp at hi
  simpa [Instr.straight] using shape.2 _ hi

/-- The gathering kernel for one field width calls nothing. -/
theorem gatherNode_leaf (width : Nat) (h : width ∈ [1, 2, 4, 8, 16, 32]) : Leaf (Kernel.gatherNode width) :=
  shape_leaf (Kernel.node_shape width h)

/-- The public-key gathering kernel calls nothing. -/
theorem gatherKey_leaf : Leaf Kernel.gatherKey :=
  shape_leaf Kernel.key_shape

end Ssz.Native.Ir
