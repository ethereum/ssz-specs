import SszNative.Proofs.Kernel.ShaNi.Digest

/-!
The SHA-NI kernel computes SHA-256 of every pair it is given.

The loop runs the pair's code once per pair, then moves the three addresses on and counts down.
-/

namespace Ssz.Native.Kernel.ShaNi

open Ssz.Native.Asm Ssz.Sha256

/-- The routine's opening: the empty-count check and the mask's load. -/
def opening : List Instr := [.test count, .jz (loopHead + pairCode.length + 5), .movdqu bswap (tableEntry bswapShaNi)]

/-- The moves to the next pair, and the countdown. -/
def advance (ls rs : Nat) : List Instr := [.addImm left ls, .addImm right rs, .addImm out 32, .subImm count 1]

/-- The loop body without its branch. -/
def body (ls rs : Nat) : List Instr := pairCode ++ advance ls rs

/-- The routine, block by block. -/
theorem program_list (ls rs : Nat) :
    (program ls rs).toList = opening ++ body ls rs ++ [.jnz loopHead, .ret] := by
  -- The routine is the opening, the body, the branch, and the return, in that order.
  simp [program, opening, body, advance, loopHead]

/-- The instruction at an index of the routine. -/
theorem fetch (ls rs i : Nat) : (program ls rs)[i]? = (opening ++ body ls rs ++ [.jnz loopHead, .ret])[i]? := by
  rw [← Array.getElem?_toList, program_list]

/-- The opening is three instructions. -/
theorem opening_length : opening.length = 3 := rfl

/-- The loop body is the pair's code and four more. -/
theorem body_length (ls rs : Nat) : (body ls rs).length = pairCode.length + 4 := by
  simp [body, advance]

/-- The loop body has no branch. -/
theorem body_straight (ls rs : Nat) : ∀ i ∈ body ls rs, i.straight := by
  -- The pair's code is all register-only instructions, loads, and stores, none of them a branch.
  intro i hi
  simp only [body, List.mem_append] at hi
  rcases hi with hi | hi
  · rw [pairCode_split] at hi
    simp only [List.mem_append] at hi
    have vo : ∀ i, (writes i).isSome → i.straight := fun i h => by
      cases i <;> simp_all [writes, Instr.straight]
    rcases hi with ((((((h | h) | h) | h) | h) | h) | h)
    · exact vo i (loads_vecOnly i h)
    · exact vo i (ivLoads_vecOnly i h)
    · exact vo i (vecOnly_flatMap _ firstRounds_vecOnly 16 i h)
    · exact vo i (middle_vecOnly i h)
    · exact vo i (vecOnly_flatMap _ paddingRounds_vecOnly 16 i h)
    · simp [finish] at h
      rcases h with h | h | h | h | h | h | h | h | h <;> simp [h, Instr.straight]
    · simp [stores] at h
      rcases h with h | h <;> simp [h, Instr.straight]
  -- The moves and the countdown are plain arithmetic.
  · simp [advance] at hi
    rcases hi with h | h | h | h <;> simp [h, Instr.straight]

/-- The countdown and the three moves, and nothing else. -/
theorem advance_spec (ls rs : Nat) (t : State) :
    let u := exec (advance ls rs) t
    u.mem = t.mem ∧ u.vec = t.vec ∧ u.gpr left = t.gpr left + ls.toUInt64 ∧
    u.gpr right = t.gpr right + rs.toUInt64 ∧ u.gpr out = t.gpr out + (32 : Nat).toUInt64 ∧
    u.gpr count = t.gpr count - (1 : Nat).toUInt64 ∧ u.zf = (t.gpr count - (1 : Nat).toUInt64 == 0) ∧
    u.gpr tbl = t.gpr tbl ∧ ∀ r ∈ calleeSaved, u.gpr r = t.gpr r := by
  -- Each of the four instructions writes one general register.
  simp [advance, exec1, assign, left, right, out, count, tbl, calleeSaved]

/-- An address moved forward, when the sum stays below 2^64. -/
theorem toNat_add_lt (a : UInt64) (n : Nat) (h : a.toNat + n < 2 ^ 64) : (a + n.toUInt64).toNat = a.toNat + n := by
  -- Both summands fit, so the machine sum is the plain sum.
  rw [UInt64.toNat_add]
  simp only [Nat.toUInt64, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (show n < 2 ^ 64 by omega)]
  exact Nat.mod_eq_of_lt h

/-- A positive count, less one. -/
theorem toNat_sub_one (c : UInt64) (h : 1 ≤ c.toNat) : (c - (1 : Nat).toUInt64).toNat = c.toNat - 1 := by
  -- A count of at least one never wraps below zero.
  rw [UInt64.toNat_sub_of_le]
  · rfl
  · rw [UInt64.le_iff_toNat_le]; exact h

/-- The countdown reaches zero exactly when one pair was left. -/
theorem sub_one_zero (c : UInt64) (h : 1 ≤ c.toNat) : (c - (1 : Nat).toUInt64 == 0) = (c.toNat == 1) := by
  -- The difference is zero exactly when the count was one.
  have := toNat_sub_one c h
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro e; rw [e] at this; simp at this; omega
  · intro e; apply UInt64.toNat_inj.mp; rw [this, e]; rfl

/-- A pair reads only its own 64 bytes. -/
theorem pairMessage_congr (m₁ m₂ : Nat → UInt8) (l r : Nat) (hl : ∀ i < 32, m₁ (l + i) = m₂ (l + i))
    (hr : ∀ i < 32, m₁ (r + i) = m₂ (r + i)) : pairMessage m₁ l r = pairMessage m₂ l r := by
  -- The message reads 32 bytes from each address, which agree in both memories.
  unfold pairMessage
  congr 2
  funext i
  split
  · exact hl i.val (by omega)
  · exact hr (i.val - 32) (by omega)

/-- What the routine is given: the addresses fit, and the output overlaps neither the table nor any input. -/
def Fits (s : State) (ls rs : Nat) : Prop :=
  let n := (s.gpr count).toNat
  let o := (s.gpr out).toNat
  (s.gpr out).toNat + 32 * n ≤ addressBound ∧
  (∀ p < n, (s.gpr left).toNat + ls * p + 32 ≤ addressBound ∧ (s.gpr right).toNat + rs * p + 32 ≤ addressBound) ∧
  Apart (o, 32 * n) ((s.gpr tbl).toNat, tableSize) ∧
  ∀ p < n, Apart (o, 32 * n) ((s.gpr left).toNat + ls * p, 32) ∧ Apart (o, 32 * n) ((s.gpr right).toNat + rs * p, 32)

/-- Memory once k parents are written: their digests at the output, and the initial memory elsewhere. -/
def Expect (s : State) (ls rs k x : Nat) : UInt8 :=
  let o := (s.gpr out).toNat
  if o ≤ x ∧ x < o + 32 * k then
    (Sha256.hash (pairMessage s.mem ((s.gpr left).toNat + ls * ((x - o) / 32))
      ((s.gpr right).toNat + rs * ((x - o) / 32)))).get! ((x - o) % 32)
  else s.mem x

/-- The machine at the loop's head with k pairs done. -/
def Inv (s : State) (ls rs k : Nat) (u : State) : Prop :=
  u.pc = loopHead ∧ u.status = .running ∧
  (u.gpr left).toNat = (s.gpr left).toNat + ls * k ∧ (u.gpr right).toNat = (s.gpr right).toNat + rs * k ∧
  (u.gpr out).toNat = (s.gpr out).toNat + 32 * k ∧ (u.gpr count).toNat = (s.gpr count).toNat - k ∧
  u.gpr tbl = s.gpr tbl ∧ (∀ r ∈ calleeSaved, u.gpr r = s.gpr r) ∧ MaskReady u ∧ ∀ x, u.mem x = Expect s ls rs k x

/-- An address past the first k outputs reads the initial memory. -/
theorem expect_outside (s : State) (ls rs k x : Nat)
    (h : x < (s.gpr out).toNat ∨ (s.gpr out).toNat + 32 * k ≤ x) : Expect s ls rs k x = s.mem x := by
  -- The address lies outside the first k output slots.
  unfold Expect
  rw [if_neg (by omega)]

/-- One pass of the loop body: pair k's digest written, the addresses moved on, and the count down by one. -/
theorem iterate (ls rs k : Nat) (s u : State) (table₀ : TableAt s.mem (s.gpr tbl).toNat) (fits : Fits s ls rs)
    (hk : k < (s.gpr count).toNat)
    (inv : Inv s ls rs k u) :
    let v := { exec (body ls rs) u with pc := loopHead + (body ls rs).length }
    run (program ls rs) (body ls rs).length u = v ∧ v.status = .running ∧ MaskReady v ∧
    (∀ x, v.mem x = Expect s ls rs (k + 1) x) ∧ v.zf = (k + 1 == (s.gpr count).toNat) ∧
    v.gpr tbl = s.gpr tbl ∧ (∀ r ∈ calleeSaved, v.gpr r = s.gpr r) ∧
    (k + 1 < (s.gpr count).toNat → (v.gpr left).toNat = (s.gpr left).toNat + ls * (k + 1) ∧
      (v.gpr right).toNat = (s.gpr right).toNat + rs * (k + 1) ∧
      (v.gpr out).toNat = (s.gpr out).toNat + 32 * (k + 1) ∧
      (v.gpr count).toNat = (s.gpr count).toNat - (k + 1)) := by
  intro v
  obtain ⟨pc, running, hl, hr, ho, hc, ht, hsaved, mask, hmem⟩ := inv
  obtain ⟨bo, bin, atab, ain⟩ := fits
  -- The table and both nodes of pair k lie outside every output.
  have table : TableAt u.mem (u.gpr tbl).toNat := by
    intro i hi
    rw [hmem, ht, expect_outside _ _ _ _ _ (by simp only [Apart, tableSize] at atab hi ⊢; omega)]
    exact table₀ i hi
  have msg : pairMessage u.mem (u.gpr left).toNat (u.gpr right).toNat =
      pairMessage s.mem ((s.gpr left).toNat + ls * k) ((s.gpr right).toNat + rs * k) := by
    rw [hl, hr]
    obtain ⟨al, ar⟩ := ain k hk
    simp only [Apart] at al ar
    apply pairMessage_congr
    · intro i hi; rw [hmem, expect_outside _ _ _ _ _ (by omega)]
    · intro i hi; rw [hmem, expect_outside _ _ _ _ _ (by omega)]
  -- The pair's code writes the digest of the pair it reads.
  obtain ⟨g, mask', memf⟩ := pair_spec u table mask
  have e : exec (body ls rs) u = exec (advance ls rs) (exec pairCode u) := by rw [body, exec_append]
  obtain ⟨am, av, al, ar, ao, ac, az, at', asaved⟩ := advance_spec ls rs (exec pairCode u)
  -- The body has no branch, so its steps are its instructions in order.
  have run_eq : run (program ls rs) (body ls rs).length u = v := by
    rw [run_block (program ls rs) opening (body ls rs) [.jnz loopHead, .ret] (program_list ls rs) (body_straight ls rs)
      u pc running]
    rfl
  refine ⟨run_eq, by simp [v, e, running], fun l hl => ?_, fun x => ?_, ?_, ?_, fun r hr' => ?_, fun more => ?_⟩
  · simp only [v, e, av]; exact mask' l hl
  · -- Pair k's digest lands in the k-th output slot.
    simp only [v, e, am, memf, msg, ho, hmem]
    unfold Expect
    by_cases slot : (s.gpr out).toNat + 32 * k ≤ x ∧ x < (s.gpr out).toNat + 32 * k + 32
    · rw [if_pos slot, if_pos (by omega), show (x - (s.gpr out).toNat) / 32 = k by omega,
        show (x - (s.gpr out).toNat) % 32 = x - ((s.gpr out).toNat + 32 * k) by omega]
    · rw [if_neg slot]
      by_cases before : (s.gpr out).toNat ≤ x ∧ x < (s.gpr out).toNat + 32 * k
      · rw [if_pos before, if_pos (by omega)]
      · rw [if_neg before, if_neg (by omega)]
  -- The countdown's zero flag says whether this was the last pair.
  · simp only [v, e, az, g]
    rw [sub_one_zero _ (by omega), hc]
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    omega
  · simp only [v, e, at', g, ht]
  · simp only [v, e, asaved r hr', g, hsaved r hr']
  · -- Pair k + 1 exists, so its addresses fit, and the moves do not wrap.
    obtain ⟨bl, br⟩ := bin (k + 1) more
    simp only [v, e, al, ar, ao, ac, g]
    rw [Nat.mul_succ] at bl br ⊢
    rw [Nat.mul_succ, Nat.mul_succ]
    have bo' : (s.gpr out).toNat + 32 * k + 32 ≤ addressBound := by omega
    simp only [addressBound] at bl br bo'
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [toNat_add_lt _ _ (by rw [hl]; omega), hl]; omega
    · rw [toNat_add_lt _ _ (by rw [hr]; omega), hr]; omega
    · rw [toNat_add_lt _ _ (by rw [ho]; omega), ho]; omega
    · rw [toNat_sub_one _ (by omega), hc]; omega

/-- The branch closing the loop sits right after its body. -/
theorem fetch_branch (ls rs : Nat) : (program ls rs)[loopHead + (body ls rs).length]? = some (.jnz loopHead) := by
  -- The branch is the first instruction after the body.
  rw [fetch, List.append_assoc, List.getElem?_append_right (by simp [opening, loopHead]),
    List.getElem?_append_right (by simp [opening, loopHead])]
  simp [opening, loopHead]

/-- The return sits right after the branch. -/
theorem fetch_ret (ls rs : Nat) : (program ls rs)[loopHead + (body ls rs).length + 1]? = some .ret := by
  -- The return is the second instruction after the body.
  rw [fetch, List.append_assoc, List.getElem?_append_right (by simp [opening, loopHead]; omega),
    List.getElem?_append_right (by simp [opening, loopHead]; omega)]
  simp [opening, loopHead, show ∀ b : Nat, 3 + b - 2 - b = 1 from fun b => by omega]

/-- The loop from pair k on: it returns with every remaining digest written. -/
theorem loop (ls rs : Nat) (s : State) (table₀ : TableAt s.mem (s.gpr tbl).toNat) (fits : Fits s ls rs) :
    ∀ m k u, k + m = (s.gpr count).toNat → 0 < m → Inv s ls rs k u →
      ∃ steps, (run (program ls rs) steps u).status = .returned ∧
        (∀ x, (run (program ls rs) steps u).mem x = Expect s ls rs (s.gpr count).toNat x) ∧
        ∀ r ∈ calleeSaved, (run (program ls rs) steps u).gpr r = s.gpr r := by
  intro m
  -- Induction on the pairs left.
  induction m with
  | zero => intro _ _ _ hm; omega
  | succ m ih =>
    intro k u hkm _ inv
    obtain ⟨hrun, running, mask, hmem, hzf, ht, hsaved, next⟩ :=
      iterate ls rs k s u table₀ fits (by omega) inv
    generalize hv : ({ exec (body ls rs) u with pc := loopHead + (body ls rs).length } : State) = v at *
    have hpc : v.pc = loopHead + (body ls rs).length := by rw [← hv]
    -- The branch: back to the head while pairs remain, else on to the return.
    have branch : step (program ls rs) v = { v with pc := if v.zf then v.pc + 1 else loopHead } := by
      simp [step, running, hpc, fetch_branch]
    by_cases last : m = 0
    · subst last
      have zf : v.zf = true := by rw [hzf]; simp; omega
      refine ⟨(body ls rs).length + 2, ?_⟩
      have final : run (program ls rs) ((body ls rs).length + 2) u = { v with pc := v.pc + 1, status := .returned } := by
        rw [run_add, hrun]
        simp only [run, branch, zf, if_true]
        simp [step, running, hpc, fetch_ret]
      rw [final]
      exact ⟨rfl, fun x => by rw [show k + 1 = (s.gpr count).toNat by omega] at hmem; exact hmem x, hsaved⟩
    · have zf : v.zf = false := by rw [hzf]; simp; omega
      obtain ⟨hl, hr, ho, hc⟩ := next (by omega)
      have inv' : Inv s ls rs (k + 1) { v with pc := loopHead } :=
        ⟨rfl, running, hl, hr, ho, hc, ht, hsaved, mask, hmem⟩
      obtain ⟨steps, done, dmem, dsaved⟩ := ih (k + 1) _ (by omega) (by omega) inv'
      refine ⟨(body ls rs).length + 1 + steps, ?_⟩
      have back : step (program ls rs) v = { v with pc := loopHead } := by rw [branch, zf]; rfl
      rw [run_add, run_add, hrun]
      simp only [run, back]
      exact ⟨done, dmem, dsaved⟩

/--
The SHA-NI kernel hashes every pair.

Pair p's 32-byte output, at the output address plus 32p, is the SHA-256 digest of its left node then its right node.

The hypotheses are what the bindings guarantee:

- the constant table sits at the address the table register holds;
- the output, every input node, and the table end below 2^63;
- the output overlaps neither the table nor any input node.

The routine returns, writes nothing outside the output, and keeps the registers the calling convention saves.
-/
theorem program_correct (ls rs : Nat) (s : State) (start : s.pc = 0) (running : s.status = .running)
    (table : TableAt s.mem (s.gpr tbl).toNat)
    (bounds : (s.gpr out).toNat + 32 * (s.gpr count).toNat ≤ addressBound ∧
      ∀ p < (s.gpr count).toNat,
        (s.gpr left).toNat + ls * p + 32 ≤ addressBound ∧ (s.gpr right).toNat + rs * p + 32 ≤ addressBound)
    (apart : Apart ((s.gpr out).toNat, 32 * (s.gpr count).toNat) ((s.gpr tbl).toNat, tableSize) ∧
      ∀ p < (s.gpr count).toNat,
        Apart ((s.gpr out).toNat, 32 * (s.gpr count).toNat) ((s.gpr left).toNat + ls * p, 32) ∧
        Apart ((s.gpr out).toNat, 32 * (s.gpr count).toNat) ((s.gpr right).toNat + rs * p, 32)) :
    ∃ steps, let f := run (program ls rs) steps s
      f.status = .returned ∧
      (∀ p < (s.gpr count).toNat, ∀ k < 32, f.mem ((s.gpr out).toNat + 32 * p + k) =
        (Sha256.hash (pairMessage s.mem ((s.gpr left).toNat + ls * p) ((s.gpr right).toNat + rs * p))).get! k) ∧
      (∀ a, ¬ ((s.gpr out).toNat ≤ a ∧ a < (s.gpr out).toNat + 32 * (s.gpr count).toNat) → f.mem a = s.mem a) ∧
      (∀ r ∈ calleeSaved, f.gpr r = s.gpr r) := by
  -- The hypotheses bundle into what the loop needs.
  have fits : Fits s ls rs := ⟨bounds.1, bounds.2, apart.1, apart.2⟩
  -- What the final memory holds, read back at each output byte and outside the output.
  suffices h : ∃ steps, (run (program ls rs) steps s).status = .returned ∧
      (∀ x, (run (program ls rs) steps s).mem x = Expect s ls rs (s.gpr count).toNat x) ∧
      ∀ r ∈ calleeSaved, (run (program ls rs) steps s).gpr r = s.gpr r by
    obtain ⟨steps, done, hmem, hsaved⟩ := h
    refine ⟨steps, done, fun p hp k hk => ?_, fun a ha => ?_, hsaved⟩
    · rw [hmem]
      unfold Expect
      rw [if_pos (by
        have : 32 * p + 32 ≤ 32 * (s.gpr count).toNat := by omega
        omega), show ((s.gpr out).toNat + 32 * p + k - (s.gpr out).toNat) / 32 = p by omega,
        show ((s.gpr out).toNat + 32 * p + k - (s.gpr out).toNat) % 32 = k by omega]
    · rw [hmem, expect_outside _ _ _ _ _ (by omega)]
  -- The opening: the count check, then the mask.
  have f0 : (program ls rs)[s.pc]? = some (.test count) := by rw [start, fetch]; rfl
  have s1 := step_straight _ s _ f0 rfl running
  generalize h1 : ({ exec1 (.test count) s with pc := s.pc + 1 } : State) = u₁ at s1
  have u1pc : u₁.pc = 1 := by rw [← h1, start]
  have u1run : u₁.status = .running := by rw [← h1]; exact running
  have u1zf : u₁.zf = (s.gpr count == 0) := by rw [← h1]; rfl
  have u1gpr : u₁.gpr = s.gpr := by rw [← h1]; rfl
  have u1mem : u₁.mem = s.mem := by rw [← h1]; rfl
  have f1 : (program ls rs)[u₁.pc]? = some (.jz (loopHead + pairCode.length + 5)) := by rw [u1pc, fetch]; rfl
  have s2 : step (program ls rs) u₁ =
      { u₁ with pc := if u₁.zf then loopHead + pairCode.length + 5 else u₁.pc + 1 } := by
    simp [step, u1run, f1]
  by_cases empty : (s.gpr count).toNat = 0
  · -- No pairs: straight to the return.
    have zf : u₁.zf = true := by
      rw [u1zf]; simp only [beq_iff_eq]; exact UInt64.toNat_inj.mp (by rw [empty]; rfl)
    have f2 : (program ls rs)[loopHead + pairCode.length + 5]? = some .ret := by
      rw [show loopHead + pairCode.length + 5 = loopHead + (body ls rs).length + 1 by rw [body_length]; omega]
      exact fetch_ret ls rs
    have e2 : step (program ls rs) u₁ = { u₁ with pc := loopHead + pairCode.length + 5 } := by rw [s2, zf]; rfl
    have e3 : step (program ls rs) { u₁ with pc := loopHead + pairCode.length + 5 } =
        { u₁ with pc := loopHead + pairCode.length + 5, status := .returned } := by
      simp only [step, u1run, f2]
      rfl
    have r3 : run (program ls rs) 3 s = { u₁ with pc := loopHead + pairCode.length + 5, status := .returned } := by
      simp only [run]
      rw [s1, e2, e3]
    refine ⟨3, ?_, fun x => ?_, fun r _ => ?_⟩
    · rw [r3]
    · rw [r3]
      exact (congrFun u1mem x).trans (expect_outside _ _ _ _ x (by rw [empty]; omega)).symm
    · rw [r3]
      exact congrFun u1gpr r
  · have zf : u₁.zf = false := by
      rw [u1zf]; simp only [beq_eq_false_iff_ne, ne_eq]
      intro e; apply empty; rw [e]; rfl
    have u2 : step (program ls rs) u₁ = { u₁ with pc := 2 } := by rw [s2, zf, u1pc]; rfl
    have f2 : (program ls rs)[(({ u₁ with pc := 2 } : State)).pc]? = some (.movdqu bswap (tableEntry bswapShaNi)) := by
      rw [fetch]; rfl
    have s3 := step_straight _ _ _ f2 rfl u1run
    generalize h3 : ({ exec1 (.movdqu bswap (tableEntry bswapShaNi)) { u₁ with pc := 2 } with
      pc := ({ u₁ with pc := 2 } : State).pc + 1 } : State) = u₃ at s3
    -- The mask comes from the table.
    have g3 : u₃.gpr = s.gpr := by rw [← h3, ← u1gpr]; rfl
    have m3 : u₃.mem = s.mem := by rw [← h3, ← u1mem]; rfl
    have inv : Inv s ls rs 0 u₃ := by
      refine ⟨by rw [← h3]; rfl, by rw [← h3]; exact u1run, by simp [g3], by simp [g3], by simp [g3],
        by simp [g3], by rw [g3], fun r _ => by rw [g3], fun l hl => ?_, fun x => ?_⟩
      · rw [← h3]
        show (exec1 (.movdqu bswap (tableEntry bswapShaNi)) { u₁ with pc := 2 }).vec bswap l = _
        rw [lane_movdqu _ _ _ l hl]
        have tab : TableAt ({ u₁ with pc := 2 } : State).mem (({ u₁ with pc := 2 } : State).gpr tbl).toNat := by
          show TableAt u₁.mem (u₁.gpr tbl).toNat
          rw [u1mem, u1gpr]; exact table
        rw [show ({ u₁ with pc := 2 } : State).addr (tableEntry bswapShaNi) =
            ({ u₁ with pc := 2 } : State).addr ⟨tbl, bswapShaNi⟩ from rfl,
          read_table _ tab bswapShaNi l.val (by decide) (by simp [bswapShaNi, tableSize]; omega),
          tableWord_reverse _ hl]
      · rw [m3, expect_outside _ _ _ _ x (by omega)]
    obtain ⟨steps, done, dmem, dsaved⟩ :=
      loop ls rs s table fits (s.gpr count).toNat 0 u₃ (by omega) (by omega) inv
    have r3 : run (program ls rs) 3 s = u₃ := by
      simp only [run]
      rw [s1, u2, s3]
    refine ⟨3 + steps, ?_⟩
    rw [run_add, r3]
    exact ⟨done, dmem, dsaved⟩

end Ssz.Native.Kernel.ShaNi
