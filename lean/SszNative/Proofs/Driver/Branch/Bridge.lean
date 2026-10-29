import SszNative.Proofs.Driver.Branch.VerifyBranch
import SszNative.Proofs.Driver.Tree

/-!
The hashing drivers' proved contract gives the pair-hashing contract the branch proofs take.

A filled context names a mask with a kernel the processor runs, the constant table, and a padding area.
Free memory is everything off the context, the table, and the padding area.
-/

namespace Ssz.Native.Driver.BranchProof

open Ssz.Native.Ir Ssz.Native.Asm

/-- A filled hashing context: its words, the table and padding area they name, and a mask with a kernel. -/
structure CtxReady (w : World) (ctx table pad : Nat) (mask : UInt64) (mem : Memory) : Prop where
  /-- The context's words are usable. -/
  ctxAccess : w.access ctx 32 = true
  /-- The first word is the mask. -/
  maskAt : readLE mem ctx 8 = mask
  /-- The second word is the table's address. -/
  tableAt : readLE mem (ctx + 8) 8 = UInt64.ofNat table
  /-- The fourth word is the padding area's address. -/
  padAt : readLE mem (ctx + 24) 8 = UInt64.ofNat pad
  /-- The table is in memory. -/
  tableHeld : Kernel.TableAt mem table
  /-- The table is usable. -/
  tableAccess : w.access table Kernel.tableSize = true
  /-- The padding area is usable. -/
  padAccess : w.access pad 1536 = true
  /-- The padding area misses the table. -/
  padTable : Apart (pad, 1536) (table, Kernel.tableSize)
  /-- The padding area misses the context. -/
  padCtx : Apart (pad, 1536) (ctx, 32)
  /-- The processor runs every kernel the mask chooses. -/
  kernels : KernelsRun w mask

/-- Memory off the context, the table, and the padding area. -/
def CtxFree (ctx table pad : Nat) (a : Nat) : Prop :=
  ¬ (ctx ≤ a ∧ a < ctx + 32) ∧ ¬ (table ≤ a ∧ a < table + Kernel.tableSize) ∧ ¬ (pad ≤ a ∧ a < pad + 1536)

/-- A range none of whose bytes lies in another, both nonempty, misses it. -/
theorem apart_of_avoid {x n y m : Nat} (hn : 0 < n) (hm : 0 < m)
    (h : ∀ k < n, ¬ (y ≤ x + k ∧ x + k < y + m)) : Apart (x, n) (y, m) := by
  simp only [Apart]
  by_cases c : x ≤ y
  · by_cases inside : y < x + n
    · have := h (y - x) (by omega); omega
    · omega
  · by_cases inside : x < y + m
    · have := h 0 hn; omega
    · omega

/-- The table is nonempty. -/
theorem tableSize_pos : 0 < Kernel.tableSize := by decide

/-- A context stays filled when its words and the table stay. -/
theorem CtxReady.frame {w : World} {ctx table pad : Nat} {mask : UInt64} {mem mem' : Memory}
    (r : CtxReady w ctx table pad mask mem)
    (h : ∀ a, (ctx ≤ a ∧ a < ctx + 32) ∨ (table ≤ a ∧ a < table + Kernel.tableSize) → mem' a = mem a) :
    CtxReady w ctx table pad mask mem' := by
  have inCtx : ∀ k < 32, mem' (ctx + k) = mem (ctx + k) :=
    fun k hk => h _ (.inl ⟨by omega, by omega⟩)
  refine { r with maskAt := ?_, tableAt := ?_, padAt := ?_, tableHeld := ?_ }
  · rw [readLE_congr mem' mem ctx 8 (fun k hk => inCtx k (by omega)), r.maskAt]
  · rw [readLE_congr mem' mem (ctx + 8) 8 (fun k hk => by rw [Nat.add_assoc]; exact inCtx _ (by omega)), r.tableAt]
  · rw [readLE_congr mem' mem (ctx + 24) 8 (fun k hk => by rw [Nat.add_assoc]; exact inCtx _ (by omega)), r.padAt]
  · intro i hi
    rw [h _ (.inr ⟨by omega, by omega⟩)]
    exact r.tableHeld i hi

/-- The proved hashing drivers hash one pair as the branch proofs need, with a filled context. -/
theorem pairHashing_of {m : Module} {w : World} (hash : HashingOk m w) (ctx : UInt64) (table pad : Nat)
    (mask : UInt64) :
    PairHashing m w ctx (CtxReady w ctx.toNat table pad mask) (CtxFree ctx.toNat table pad) hashStack where
  ready_frame _ _ r h := r.frame fun a held => h a fun f => by
    rcases held with c | t
    · exact f.1 c
    · exact f.2.1 t
  pair := by
    intro sp mem out left right r deep ao al ar fo fl fr pl pr
    -- A free range misses the context, the table, and the padding area.
    have avoid : ∀ x : UInt64, (∀ k < 32, CtxFree ctx.toNat table pad (x.toNat + k)) →
        Apart (x.toNat, 32) (ctx.toNat, 32) ∧ Apart (x.toNat, 32) (table, Kernel.tableSize) ∧
          Apart (pad, 1536) (x.toNat, 32) :=
      fun x f => ⟨apart_of_avoid (by decide) (by decide) fun k hk => (f k hk).1,
        apart_of_avoid (by decide) tableSize_pos fun k hk => (f k hk).2.1,
        BranchProof.Apart.symm (apart_of_avoid (by decide) (by decide) fun k hk => (f k hk).2.2)⟩
    obtain ⟨oc, ot, op⟩ := avoid out fo
    obtain ⟨-, -, lp⟩ := avoid left fl
    obtain ⟨-, -, rp⟩ := avoid right fr
    have bl := access_bound al
    have br := access_bound ar
    have p0 : ∀ p < 1, p = 0 := fun p hp => by omega
    have pre : RunPre w mem 32 32 out.toNat left.toNat right.toNat 1 ctx.toNat table pad mask :=
      ⟨r.ctxAccess, r.maskAt, r.tableAt, r.padAt,
        ⟨r.tableHeld, by simpa using ao, r.tableAccess,
          fun p hp => by rw [p0 p hp]; simpa using And.intro al ar,
          by simp only [addressBound]; omega,
          by simpa using ot,
          fun p hp => by rw [p0 p hp]; simpa using And.intro pl pr⟩,
        r.padAccess, by simpa using op, r.padTable,
        fun p hp => by rw [p0 p hp]; simpa using And.intro lp rp,
        by simpa using BranchProof.Apart.symm oc⟩
    obtain ⟨mem', call, after⟩ := (hash.columns sp mem out.toNat left.toNat right.toNat 1 ctx.toNat table pad mask
      pre r.kernels deep)
    simp only [UInt64.ofNat_toNat] at call
    -- Off the padding area, memory is the hashed memory.
    have offPad : ∀ a, CtxFree ctx.toNat table pad a → mem' a = hashed mem out.toNat left.toNat right.toNat 1 32 32 a :=
      fun a f => after a f.2.2
    refine ⟨mem', call, r.frame fun a nf => ?_, fun k hk => ?_, fun a f outside => ?_⟩
    · -- The context's words and the table are neither the digest nor the padding area.
      have pc := r.padCtx
      have pt := r.padTable
      simp only [Apart] at pc pt oc ot
      rw [after a (by omega), hashed_outside (by omega)]
    · have := hashed_inside (mem := mem) (out := out.toNat) (left := left.toNat) (right := right.toNat)
        (count := 1) (ls := 32) (rs := 32) (p := 0) (k := k) (by decide) hk
      simp only [Nat.mul_zero, Nat.add_zero] at this
      rw [offPad _ (fo k hk), this]
    · rw [offPad a f, hashed_outside (by simpa using outside)]

/--
With the proved hashing drivers and a filled context, the compiled branch verifier answers what the Lean verifier
answers on the leaf, branch, index and root its job names.
-/
theorem verify_branch_hashing {m : Module} {w : World} (hash : HashingOk m w)
    (hv : m.fns.lookup "ssz_verify_branch" = some VerifyBranch.fn)
    (hl : m.fns.lookup "ssz_branch_level" = some Level.fn) (hs : m.fns.lookup "ssz_branch_same" = some Same.fn)
    {ctx : UInt64} {table pad : Nat} {mask : UInt64} {sp : Nat} (deep : w.stackLo + 256 + hashStack ≤ sp)
    {mem : Memory} (rd : CtxReady w ctx.toNat table pad mask mem) {job leaf proof count index root scratch : UInt64}
    (j : BranchJob w (CtxFree ctx.toNat table pad) mem job leaf proof count index root scratch) :
    ∃ mem', Calls m w "ssz_verify_branch" sp [job, ctx] mem
        (answerCode (verifyMerkleProof (readNode mem leaf.toNat) (nodesAt mem proof.toNat count.toNat) index.toNat
          (readNode mem root.toNat))) mem' ∧
      CtxReady w ctx.toNat table pad mask mem' ∧
      ∀ a, CtxFree ctx.toNat table pad a → ¬ (scratch.toNat ≤ a ∧ a < scratch.toNat + 64) → mem' a = mem a :=
  verify_branch_calls hv hl hs (pairHashing_of hash ctx table pad mask) deep rd j

end Ssz.Native.Driver.BranchProof
