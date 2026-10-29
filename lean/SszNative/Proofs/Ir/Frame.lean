import SszNative.Ir.Compile
import SszNative.Ir.Wf
import SszNative.Proofs.Asm.Reach
import SszNative.Proofs.Asm.Bytes

/-!
How the machine matches a running function's variables and memory.

The frame holds each variable in its slot, memory off the stack is the program's memory, and the kept registers keep the
values the caller gave them.
-/

namespace Ssz.Native.Ir

open Ssz.Native.Asm

/-- Where a compiled function runs. -/
structure Site where
  image : Image
  routine : Nat
  w : World
  base : Nat
  vars : Nat
  frame : Nat
  saved : Gpr → UInt64

/-- The frame lies inside the stack, below the address bound. -/
structure Site.Fits (c : Site) : Prop where
  low : c.w.stackLo ≤ c.base
  high : c.base + 8 * c.frame ≤ c.w.stackHi
  bound : c.w.stackHi ≤ addressBound
  vars : c.vars ≤ c.frame
  /-- The routine is in the image, and its addresses encode in a call's return address. -/
  routine : c.routine < c.image.size ∧ c.routine < 2 ^ 31
  /-- The routine's instruction indices fit a return address's low half. -/
  code : (c.image.code c.routine).size < 2 ^ 32

/-- The registers the calling convention keeps, apart from the stack pointer. -/
def keptRegs : List Gpr := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- The machine matches the program's variables and memory, in a running function's frame. -/
structure Site.Holds (c : Site) (env : Env) (ir : Memory) (s : State) : Prop where
  rsp : s.gpr .rsp = c.base.toUInt64
  vars : ∀ x < c.vars, readLE s.mem (c.base + 8 * x) 8 = env x
  heap : ∀ a, a < c.w.stackLo ∨ c.w.stackHi ≤ a → s.mem a = ir a
  cpu : s.cpu = c.w.cpu
  running : s.status = .running
  kept : ∀ g ∈ keptRegs, s.gpr g = c.saved g

/-- A frame slot's address. -/
theorem slot_addr (c : Site) (fits : c.Fits) (s : State) (rsp : s.gpr .rsp = c.base.toUInt64) (k : Nat) :
    s.addr (slot k) = c.base + 8 * k := by
  have : c.base < 2 ^ 64 := by have := fits.high; have := fits.bound; simp [addressBound] at *; omega
  simp [State.addr, slot, rsp, Nat.mod_eq_of_lt this]

/-- Bytes read only from their own addresses. -/
theorem readLE_congr (m₁ m₂ : Nat → UInt8) (a n : Nat) (h : ∀ k < n, m₁ (a + k) = m₂ (a + k)) :
    readLE m₁ a n = readLE m₂ a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [readLE]
    rw [show m₁ a = m₂ a from by simpa using h 0 (by omega),
      ih (a + 1) (fun k hk => by have := h (k + 1) (by omega); rwa [show a + (k + 1) = a + 1 + k by omega] at this)]

/-- Writing a register other than the stack pointer and the kept ones keeps the frame's correspondence. -/
theorem Site.Holds.setGpr {c : Site} {env : Env} {ir : Memory} {s : State} (h : c.Holds env ir s) (g : Gpr)
    (hg : g ∈ [Gpr.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]) (v : UInt64) :
    c.Holds env ir { s with gpr := assign s.gpr g v } := by
  refine ⟨?_, h.vars, h.heap, h.cpu, h.running, fun r hr => ?_⟩
  · simp only [assign]; split
    · subst_vars; simp at hg
    · exact h.rsp
  · simp only [assign]; split
    · subst_vars; simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hr hg
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp at hg
    · exact h.kept r hr

/-- A state agreeing on registers, memory, processor and status keeps the correspondence. -/
theorem Site.Holds.congr {c : Site} {env : Env} {ir : Memory} {s s' : State} (h : c.Holds env ir s)
    (gpr : s'.gpr = s.gpr) (mem : s'.mem = s.mem) (cpu : s'.cpu = s.cpu) (status : s'.status = s.status) :
    c.Holds env ir s' :=
  ⟨by rw [gpr]; exact h.rsp, by rw [mem]; exact h.vars, by rw [mem]; exact h.heap, by rw [cpu]; exact h.cpu,
    by rw [status]; exact h.running, by rw [gpr]; exact h.kept⟩

/-- A scratch register written, the rest as before, keeps the correspondence. -/
theorem Site.Holds.update {c : Site} {env : Env} {ir : Memory} {s s' : State} (h : c.Holds env ir s) (g : Gpr)
    (hg : g ∈ [Gpr.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]) (v : UInt64)
    (gpr : s'.gpr = assign s.gpr g v) (mem : s'.mem = s.mem) (cpu : s'.cpu = s.cpu) (status : s'.status = s.status) :
    c.Holds env ir s' :=
  (h.setGpr g hg v).congr gpr mem cpu status

/-- Writing a word to a temporary slot keeps the correspondence: the slot is in the stack and above the variables. -/
theorem Site.Holds.setSlot {c : Site} {env : Env} {ir : Memory} {s : State} (h : c.Holds env ir s) (fits : c.Fits)
    (k : Nat) (above : c.vars ≤ k) (inside : k < c.frame) (v : UInt64) :
    c.Holds env ir { s with mem := store s.mem (c.base + 8 * k) 8 (qwordByte v) } := by
  refine ⟨h.rsp, fun x hx => ?_, fun a ha => ?_, h.cpu, h.running, h.kept⟩
  · rw [← h.vars x hx]
    apply readLE_congr
    intro j hj
    simp only [store]
    rw [if_neg (by omega)]
  · simp only [store]
    rw [if_neg (by have := fits.low; have := fits.high; omega)]
    exact h.heap a ha

/-- Two 8-byte slots at different indices share no byte. -/
theorem slots_apart (base x y k : Nat) (hxy : x ≠ y) (hk : k < 8) :
    ¬ (base + 8 * y ≤ base + 8 * x + k ∧ base + 8 * x + k < base + 8 * y + 8) := by
  omega

/-- Writing a variable's slot gives the correspondence with that variable's new value. -/
theorem Site.Holds.setVar {c : Site} {env : Env} {ir : Memory} {s : State} (h : c.Holds env ir s) (fits : c.Fits)
    (x : Nat) (hx : x < c.vars) (v : UInt64) :
    c.Holds (assign env x v) ir { s with mem := store s.mem (c.base + 8 * x) 8 (qwordByte v) } := by
  refine ⟨h.rsp, fun y hy => ?_, fun a ha => ?_, h.cpu, h.running, h.kept⟩
  · simp only [assign]
    split
    · subst_vars; exact readLE_store8 _ _ _
    · rename_i hne
      rw [← h.vars y hy]
      apply readLE_congr
      intro k hk
      simp only [store]
      rw [if_neg (by omega)]
  · simp only [store]
    rw [if_neg (by have := fits.low; have := fits.high; have := fits.vars; omega)]
    exact h.heap a ha

end Ssz.Native.Ir
