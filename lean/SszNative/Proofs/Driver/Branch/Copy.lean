import SszNative.Proofs.Driver.Branch.FoldSpec

/-! Copying a node eight bytes at a time, as the drivers do. -/

namespace Ssz.Native.Driver.BranchProof

open Ssz.Native.Ir Ssz.Native.Asm

/-- The digit of a number spelled by bytes is the byte at that position. -/
theorem bytesNat_digit (mem : Memory) : ∀ (a n k : Nat), k < n → bytesNat mem a n / 256 ^ k % 256 = (mem (a + k)).toNat
  | a, n + 1, 0, _ => by
    simp only [bytesNat, Nat.pow_zero, Nat.div_one, Nat.add_zero]
    have := (mem a).toNat_lt
    omega
  | a, n + 1, k + 1, h => by
    simp only [bytesNat]
    have := (mem a).toNat_lt
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, ← Nat.div_div_eq_div_mul,
      show ((mem a).toNat + 256 * bytesNat mem (a + 1) n) / 256 = bytesNat mem (a + 1) n by omega,
      bytesNat_digit mem (a + 1) n k (by omega), Nat.add_assoc, Nat.add_comm 1 k]

/-- A byte of a word read from memory is the byte at its position there. -/
theorem qwordByte_readLE (mem : Memory) (a k : Nat) (hk : k < 8) : qwordByte (readLE mem a 8) k = mem (a + k) := by
  apply UInt8.toNat_inj.mp
  rw [qwordByte_toNat _ _ hk, readLE_toNat _ _ _ (by decide), bytesNat_digit mem a 8 k hk]

/-- Eight bytes copied by one load and one store, between ranges that miss each other. -/
theorem copy8_wp {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {Q : Env → Memory → Prop}
    {dst src : Ir.Expr} {d s : UInt64} (o : Nat) (hd : ∀ mem, eval w env mem dst = some d)
    (hs : ∀ mem, eval w env mem src = some s) (bound : d.toNat + o + 8 ≤ 2 ^ 63 ∧ s.toNat + o + 8 ≤ 2 ^ 63)
    (ad : w.access (d.toNat + o) 8 = true) (as : w.access (s.toNat + o) 8 = true)
    (h : ∀ mem', (∀ b < 8, mem' (d.toNat + o + b) = mem (s.toNat + o + b)) →
      (∀ a, ¬ (d.toNat + o ≤ a ∧ a < d.toNat + o + 8) → mem' a = mem a) → Q env mem') :
    Wp m w sp (Stmt.st (dst + ((o : Nat) : Ir.Expr)) (Ir.Expr.ld (src + ((o : Nat) : Ir.Expr)))) env mem Q := by
  have oNat : o.toUInt64.toNat = o := toNat_ofNat_of_lt _ (by omega)
  have dAddr : (d + o.toUInt64).toNat = d.toNat + o := by rw [toNat_add_of_lt _ _ (by omega), oNat]
  have sAddr : (s + o.toUInt64).toNat = s.toNat + o := by rw [toNat_add_of_lt _ _ (by omega), oNat]
  have load := eval_ld (w := w) (env := env) (mem := mem) (eval_add (hs mem) (b := ((o : Nat) : Ir.Expr)) rfl)
    (by rw [sAddr]; exact as)
  refine Wp.store (eval_add (hd mem) (b := ((o : Nat) : Ir.Expr)) rfl) load (by rw [dAddr]; exact ad) (h _ ?_ ?_)
  · intro b hb
    rw [dAddr, sAddr]
    simp only [store, show d.toNat + o ≤ d.toNat + o + b by omega, show d.toNat + o + b < d.toNat + o + Width.bytes .b8 by
      simp [Width.bytes]; omega, and_self, if_true, show d.toNat + o + b - (d.toNat + o) = b by omega]
    exact qwordByte_readLE _ _ _ hb
  · intro a ha
    rw [dAddr]
    exact store_outside _ _ _ _ _ (by simp [Width.bytes]; omega)

/-- A node copied eight bytes at a time, between ranges that miss each other. -/
theorem copy32_wp {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {Q : Env → Memory → Prop}
    {dst src : Ir.Expr} {d s : UInt64} (hd : ∀ mem, eval w env mem dst = some d)
    (hs : ∀ mem, eval w env mem src = some s)
    (ad : w.access d.toNat 32 = true) (as : w.access s.toNat 32 = true) (apart : Apart (d.toNat, 32) (s.toNat, 32))
    (h : ∀ mem', (∀ k < 32, mem' (d.toNat + k) = mem (s.toNat + k)) →
      (∀ a, ¬ (d.toNat ≤ a ∧ a < d.toNat + 32) → mem' a = mem a) → Q env mem') :
    Wp m w sp (.block (copy32 dst src)) env mem Q := by
  have bd := access_bound ad
  have bs := access_bound as
  simp only [Apart] at apart
  show Wp m w sp (.block [Stmt.st (dst + ((8 * 0 : Nat) : Ir.Expr)) (Ir.Expr.ld (src + ((8 * 0 : Nat) : Ir.Expr))),
    Stmt.st (dst + ((8 * 1 : Nat) : Ir.Expr)) (Ir.Expr.ld (src + ((8 * 1 : Nat) : Ir.Expr))),
    Stmt.st (dst + ((8 * 2 : Nat) : Ir.Expr)) (Ir.Expr.ld (src + ((8 * 2 : Nat) : Ir.Expr))),
    Stmt.st (dst + ((8 * 3 : Nat) : Ir.Expr)) (Ir.Expr.ld (src + ((8 * 3 : Nat) : Ir.Expr)))]) env mem Q
  -- Each store writes one eighth-block of the destination, reading the source, which no store touches.
  refine Wp.cons (copy8_wp (8 * 0) hd hs (by omega) (access_sub ad (by omega)) (access_sub as (by omega)) fun m1 c1 f1 => ?_)
  refine Wp.cons (copy8_wp (8 * 1) hd hs (by omega) (access_sub ad (by omega)) (access_sub as (by omega)) fun m2 c2 f2 => ?_)
  refine Wp.cons (copy8_wp (8 * 2) hd hs (by omega) (access_sub ad (by omega)) (access_sub as (by omega)) fun m3 c3 f3 => ?_)
  refine copy8_wp (8 * 3) hd hs (by omega) (access_sub ad (by omega)) (access_sub as (by omega)) fun m4 c4 f4 => h m4 ?_ ?_
  · intro k hk
    -- The source is never written, so each block reads what was there at the start.
    have src0 : ∀ j < 32, m1 (s.toNat + j) = mem (s.toNat + j) := fun j hj => f1 _ (by omega)
    have src1 : ∀ j < 32, m2 (s.toNat + j) = mem (s.toNat + j) := fun j hj => by rw [f2 _ (by omega), src0 j hj]
    have src2 : ∀ j < 32, m3 (s.toNat + j) = mem (s.toNat + j) := fun j hj => by rw [f3 _ (by omega), src1 j hj]
    by_cases b0 : k < 8
    · have := c1 k b0
      rw [f4 _ (by omega), f3 _ (by omega), f2 _ (by omega), show d.toNat + k = d.toNat + 8 * 0 + k by omega, this]
      simp
    by_cases b1 : k < 16
    · have := c2 (k - 8) (by omega)
      rw [f4 _ (by omega), f3 _ (by omega), show d.toNat + k = d.toNat + 8 * 1 + (k - 8) by omega, this,
        show s.toNat + 8 * 1 + (k - 8) = s.toNat + k by omega, src0 k hk]
    by_cases b2 : k < 24
    · have := c3 (k - 16) (by omega)
      rw [f4 _ (by omega), show d.toNat + k = d.toNat + 8 * 2 + (k - 16) by omega, this,
        show s.toNat + 8 * 2 + (k - 16) = s.toNat + k by omega, src1 k hk]
    · have := c4 (k - 24) (by omega)
      rw [show d.toNat + k = d.toNat + 8 * 3 + (k - 24) by omega, this,
        show s.toNat + 8 * 3 + (k - 24) = s.toNat + k by omega, src2 k hk]
  · intro a ha
    rw [f4 _ (by omega), f3 _ (by omega), f2 _ (by omega), f1 _ (by omega)]

end Ssz.Native.Driver.BranchProof
