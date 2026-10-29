import SszNative.Proofs.Kernel.Baseline.View
import SszNative.Proofs.Kernel.Avx2.Moves

/-!
The four-lane kernel's data movement: words byte-reversed through a general register, four bytes at a time.

```text
    word t of node j    load, reverse, store    lane j of schedule row t
    lane j of row i     load, reverse, store    word i of digest j
```

Each copy reads four bytes and writes them, last first, somewhere else.
A run of copies whose destinations are disjoint, and miss every source, leaves each destination its source reversed.
-/

namespace Ssz.Native.Kernel.Baseline

open Ssz.Sha256 Ssz.Native.Asm
open Ssz.Native.Kernel.Avx512 (assign_apply)

/-- Byte k of a reversed four-byte load is byte 3 - k of memory. -/
theorem swapLow32_byte (mem : Nat → UInt8) (a k : Nat) (hk : k < 4) :
    qwordByte (swapLow32 (readLE mem a 4)) k = mem (a + (3 - k)) := by
  -- Each of the four byte positions is checked bit by bit.
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ =>
    apply byte_ext
    simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
    simp [qwordByte, swapLow32, readLE]

/-- One copy: the general register holds the reversed word, and four bytes past the destination hold it. -/
theorem swapCopy_exec (src dst : Mem) (hd : dst.base ≠ blocks) (s : State) :
    exec (swapCopy src dst) s =
      { s with
        gpr := assign s.gpr blocks (swapLow32 (readLE s.mem (s.addr src) 4))
        mem := store s.mem (s.addr dst) 4 (qwordByte (swapLow32 (readLE s.mem (s.addr src) 4))) } := by
  -- The load and the reversal write only the general register, which the destination's address does not read.
  simp only [swapCopy, exec, exec1, Width.bytes, State.addr, assign_apply, if_true, if_neg hd]
  congr 1
  funext r
  simp only [assign]
  split <;> rfl

/-- The copies for indices below n, from each source to its destination. -/
def copies (src dst : Nat → Mem) (n : Nat) : List Instr :=
  (List.range n).flatMap fun i => swapCopy (src i) (dst i)

/--
A run of copies leaves each destination its source reversed, and every other byte as it was.

The destinations must be disjoint, and miss every source, and no address may be read through the general register.
Only that register changes.
-/
theorem copies_spec (src dst : Nat → Mem) (n : Nat) (s : State)
    (srcBase : ∀ i < n, (src i).base ≠ blocks) (dstBase : ∀ i < n, (dst i).base ≠ blocks)
    (disjoint : ∀ i < n, ∀ j < n, i ≠ j → s.addr (dst i) + 4 ≤ s.addr (dst j) ∨ s.addr (dst j) + 4 ≤ s.addr (dst i))
    (apart : ∀ i < n, ∀ j < n, s.addr (src i) + 4 ≤ s.addr (dst j) ∨ s.addr (dst j) + 4 ≤ s.addr (src i)) :
    let s' := exec (copies src dst n) s
    (∀ i < n, ∀ k < 4, s'.mem (s.addr (dst i) + k) = s.mem (s.addr (src i) + (3 - k))) ∧
    (∀ x, (∀ i < n, x < s.addr (dst i) ∨ s.addr (dst i) + 4 ≤ x) → s'.mem x = s.mem x) ∧
    (∀ r, r ≠ blocks → s'.gpr r = s.gpr r) ∧ s'.vec = s.vec ∧ s'.zf = s.zf ∧ s'.cf = s.cf := by
  intro s'
  induction n with
  | zero => exact ⟨fun _ h => absurd h (by omega), fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨done, rest, gpr, vec, zf, cf⟩ := ih (fun i hi => srcBase i (by omega)) (fun i hi => dstBase i (by omega))
      (fun i hi j hj => disjoint i (by omega) j (by omega)) (fun i hi j hj => apart i (by omega) j (by omega))
    have split : copies src dst (n + 1) = copies src dst n ++ swapCopy (src n) (dst n) := by
      simp [copies, List.range_succ]
    simp only [s', split, exec_append]
    generalize exec (copies src dst n) s = x at done rest gpr vec zf cf
    -- The last copy reads and writes through registers the earlier ones kept.
    have addr : ∀ m : Mem, m.base ≠ blocks → x.addr m = s.addr m := fun m hm => by
      simp only [State.addr, gpr _ hm]
    rw [swapCopy_exec _ _ (dstBase n (by omega)), addr _ (dstBase n (by omega)), addr _ (srcBase n (by omega))]
    refine ⟨fun i hi k hk => ?_, fun y hy => ?_, fun r hr => ?_, vec, zf, cf⟩
    · simp only [store]
      by_cases last : i = n
      · -- The last copy's destination: its source, which no earlier copy wrote.
        subst last
        rw [if_pos (by omega), show s.addr (dst i) + k - s.addr (dst i) = k by omega, swapLow32_byte _ _ _ hk]
        exact rest _ fun j hj => by have := apart i (by omega) j (by omega); omega
      · -- An earlier destination, which the last copy misses.
        have := disjoint i hi n (by omega) last
        rw [if_neg (by omega)]
        exact done i (by omega) k hk
    · simp only [store]
      rw [if_neg (by have := hy n (by omega); omega)]
      exact rest y fun i hi => hy i (by omega)
    · simp only [assign_apply, if_neg hr]; exact gpr r hr

/-- Byte k of a reversed word is byte 3 - k of memory. -/
theorem wordByte_bswap (mem : Nat → UInt8) (a k : Nat) (hk : k < 4) :
    wordByte (bswap (readWord mem a)) k = mem (a + (3 - k)) := by
  -- Each of the four byte positions is checked bit by bit.
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ =>
    apply byte_ext
    simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
    simp [wordByte, bswap, readWord]

/-- Four bytes that are another four in reverse order read as that word reversed. -/
theorem readWord_reversed (f mem : Nat → UInt8) (d a : Nat) (h : ∀ k < 4, f (d + k) = mem (a + (3 - k))) :
    readWord f d = bswap (readWord mem a) :=
  Avx512x2.readWord_bytes f d _ fun k hk => by rw [h k hk, wordByte_bswap _ _ _ hk]

/-- Byte k of a word read from memory is the byte k past its address. -/
theorem wordByte_readWord (mem : Nat → UInt8) (a k : Nat) (hk : k < 4) : wordByte (readWord mem a) k = mem (a + k) := by
  -- Each of the four byte positions is checked bit by bit.
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ =>
    apply byte_ext
    simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
    simp [wordByte, readWord]

/-- Loading four nodes is a run of copies, word n mod 8 of node n / 8 into lane n / 8 of a schedule row. -/
theorem loadWords_eq (base : Gpr) (stride first : Nat) :
    loadWords base stride first = copies (fun n => ⟨base, stride * (n / 8) + 4 * (n % 8)⟩)
      (fun n => ⟨sp, wordSlot (first + n % 8) + 4 * (n / 8)⟩) 32 := rfl

/--
Loading four nodes stores word t of node l, byte-reversed, at schedule row first + t, lane l.

Every byte outside the eight rows is kept, and only the general register the copies pass through changes.
-/
theorem loadWords_spec (base : Gpr) (stride first : Nat) (hf : first ≤ 8) (hb : base ≠ blocks) (s : State)
    (apart : ∀ l < 4, Apart ((s.gpr sp).toNat, frame) ((s.gpr base).toNat + stride * l, 32)) :
    let s' := exec (loadWords base stride first) s
    let S := (s.gpr sp).toNat
    (∀ t < 8, ∀ l : Fin 4, readWord s'.mem (S + wordSlot (first + t) + 4 * l.val) =
      bswap (readWord s.mem ((s.gpr base).toNat + stride * l.val + 4 * t))) ∧
    (∀ x, (∀ t < 8, x < S + wordSlot (first + t) ∨ S + wordSlot (first + t) + 16 ≤ x) → s'.mem x = s.mem x) ∧
    (∀ r, r ≠ blocks → s'.gpr r = s.gpr r) ∧ s'.vec = s.vec ∧ s'.zf = s.zf ∧ s'.cf = s.cf := by
  intro s' S
  rw [show s' = exec (copies _ _ 32) s from congrArg (exec · s) (loadWords_eq base stride first)] at *
  have spb : sp ≠ blocks := by decide
  -- Destinations are distinct words of the scratch area, and sources lie in the nodes, apart from it.
  obtain ⟨done, rest, gpr, vec, zf, cf⟩ := copies_spec (fun n => ⟨base, stride * (n / 8) + 4 * (n % 8)⟩)
    (fun n => ⟨sp, wordSlot (first + n % 8) + 4 * (n / 8)⟩) 32 s (fun _ _ => hb) (fun _ _ => spb)
    (fun i hi j hj ne => by simp only [State.addr, wordSlot, frame]; omega)
    (fun i hi j hj => by
      have := apart (i / 8) (by omega)
      simp only [Apart, frame] at this
      simp only [State.addr, wordSlot, frame]
      omega)
  refine ⟨fun t ht l => ?_, fun x hx => rest x fun i hi => ?_, gpr, vec, zf, cf⟩
  · -- Copy 8l + t lands in lane l of row first + t.
    have := done (8 * l.val + t) (by omega)
    simp only [State.addr, show (8 * l.val + t) / 8 = l.val by omega, show (8 * l.val + t) % 8 = t by omega] at this
    exact readWord_reversed _ _ _ _ fun k hk => by simpa only [Nat.add_assoc] using this k hk
  · have := hx (i % 8) (by omega)
    simp only [State.addr, S] at this ⊢
    omega

/--
The digest copies write each lane's eight stored state words, byte-reversed, as its 32-byte digest.

Byte k of digest p is byte 3 - k mod 4 of lane p of stored row k / 4, and nothing else is written.
-/
theorem outCopies_spec (s : State) (apart : Apart ((s.gpr sp).toNat, frame) ((s.gpr out).toNat, 128)) :
    let s' := exec outCopies s
    (∀ p < 4, ∀ k < 32, s'.mem ((s.gpr out).toNat + 32 * p + k) =
      wordByte (readWord s.mem ((s.gpr sp).toNat + midSlot (k / 4) + 4 * p)) (3 - k % 4)) ∧
    (∀ x, ¬ ((s.gpr out).toNat ≤ x ∧ x < (s.gpr out).toNat + 128) → s'.mem x = s.mem x) ∧
    (∀ r, r ≠ blocks → s'.gpr r = s.gpr r) := by
  intro s'
  have spb : sp ≠ blocks := by decide
  have outb : out ≠ blocks := by decide
  simp only [Apart, frame] at apart
  -- Destinations are distinct words of the output, and sources lie in the scratch area, apart from it.
  obtain ⟨done, rest, gpr, -, -, -⟩ := copies_spec (fun n => ⟨sp, midSlot (n % 8) + 4 * (n / 8)⟩)
    (fun n => ⟨out, 32 * (n / 8) + 4 * (n % 8)⟩) 32 s (fun _ _ => spb) (fun _ _ => outb)
    (fun i hi j hj ne => by simp only [State.addr]; omega)
    (fun i hi j hj => by simp only [State.addr, midSlot]; omega)
  refine ⟨fun p hp k hk => ?_, fun x hx => rest x fun i hi => by simp only [State.addr]; omega, gpr⟩
  -- Copy 8p + k / 4 writes bytes 4 (k / 4) to 4 (k / 4) + 3 of digest p.
  have := done (8 * p + k / 4) (by omega) (k % 4) (by omega)
  simp only [State.addr, show (8 * p + k / 4) / 8 = p by omega, show (8 * p + k / 4) % 8 = k / 4 by omega] at this
  rw [show (s.gpr out).toNat + 32 * p + k = (s.gpr out).toNat + (32 * p + 4 * (k / 4)) + k % 4 by omega]
  refine this.trans ?_
  rw [wordByte_readWord _ _ _ (by omega)]
  congr 1
  omega

end Ssz.Native.Kernel.Baseline
