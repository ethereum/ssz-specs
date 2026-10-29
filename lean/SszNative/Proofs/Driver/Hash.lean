import SszNative.Proofs.Driver.Memory
import SszNative.Proofs.Kernel.Detect
import SszNative.Driver.Hash
import SszNative.Proofs.Ir.Logic
import SszNative.Proofs.Ir.Kernels

/-!
The hashing driver hashes a whole run of pairs, whatever kernels the processor has.

The run is cut into pieces, each hashed by one kernel call.
Hashing the first pairs, then the rest from the moved pointers, is hashing them all,
because no digest overwrites a node still to be read.
Without the SHA instruction kernels, the last pairs are copied into a padded batch,
and the digests a wide kernel writes there are copied out.
The SSE2 kernel runs on every processor, so every run is hashed.
-/

namespace Ssz.Native.Driver

open Ssz.Native.Asm Ssz.Native.Ir

/-! ## Words -/

/-- A number below the word size survives the conversion to a word. -/
theorem ofNat_toNat {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' h

/-- Words converted from numbers below the word size compare as the numbers. -/
theorem ofNat_lt {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : UInt64.ofNat a < UInt64.ofNat b ↔ a < b := by
  -- Compare the numbers behind the words.
  rw [UInt64.lt_iff_toNat_lt, ofNat_toNat ha, ofNat_toNat hb]

/-- Words converted from numbers below the word size are equal only when the numbers are. -/
theorem ofNat_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : UInt64.ofNat a = UInt64.ofNat b ↔ a = b := by
  constructor
  · intro h
    rw [← ofNat_toNat ha, ← ofNat_toNat hb, h]
  · rintro rfl
    rfl

/-- Sums of converted numbers, as one conversion. -/
theorem ofNat_add' (a b : Nat) : UInt64.ofNat a + UInt64.ofNat b = UInt64.ofNat (a + b) :=
  (UInt64.ofNat_add a b).symm

/-- Products of converted numbers, as one conversion. -/
theorem ofNat_mul' (a b : Nat) : UInt64.ofNat a * UInt64.ofNat b = UInt64.ofNat (a * b) :=
  (UInt64.ofNat_mul a b).symm

/-- A word literal is the conversion of its number. -/
theorem lit_ofNat (n : Nat) : (no_index (OfNat.ofNat n) : UInt64) = UInt64.ofNat n := rfl

/-- A number converted the other way round is the same word. -/
theorem toUInt64_ofNat (n : Nat) : n.toUInt64 = UInt64.ofNat n := rfl

/-- The quotient of a converted number below the word size, as one conversion. -/
theorem ofNat_div {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNat a / UInt64.ofNat b = UInt64.ofNat (a / b) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_div, ofNat_toNat ha, ofNat_toNat hb, ofNat_toNat (by
    have := Nat.div_le_self a b
    omega)]

/-- The difference of converted numbers, the second at most the first, as one conversion. -/
theorem ofNat_sub' {a b : Nat} (h : b ≤ a) : UInt64.ofNat a - UInt64.ofNat b = UInt64.ofNat (a - b) :=
  (UInt64.ofNat_sub h).symm

/-! ## Bytes -/

/-- Digit j of the number some bytes spell is byte j. -/
theorem bytesNat_digit (mem : Nat → UInt8) (a n j : Nat) (hj : j < n) :
    bytesNat mem a n / 256 ^ j % 256 = (mem (a + j)).toNat := by
  induction n generalizing a j with
  | zero => omega
  | succ n ih =>
    simp only [bytesNat]
    have := (mem a).toNat_lt
    cases j with
    | zero => simp
    | succ j =>
      -- Drop the first byte, then read digit j of the rest.
      rw [Nat.pow_succ, Nat.mul_comm (256 ^ j) 256, ← Nat.div_div_eq_div_mul,
        show ((mem a).toNat + 256 * bytesNat mem (a + 1) n) / 256 = bytesNat mem (a + 1) n by omega,
        ih (a + 1) j (by omega), Nat.add_right_comm, Nat.add_assoc]

/-- Byte j of an eight-byte load is the byte j past the address. -/
theorem qwordByte_readLE (mem : Nat → UInt8) (a j : Nat) (hj : j < 8) : qwordByte (readLE mem a 8) j = mem (a + j) := by
  apply UInt8.toNat_inj.mp
  rw [qwordByte_toNat _ _ hj, readLE_toNat _ _ _ (by decide), bytesNat_digit _ _ _ _ hj]

/-- An eight-byte load stored back elsewhere copies the eight bytes. -/
theorem store_load (mem : Memory) (dst src : Nat) :
    store mem dst 8 (qwordByte (readLE mem src 8)) = copied mem dst src 8 := by
  funext a
  simp only [store, copied]
  split
  · exact qwordByte_readLE _ _ _ (by omega)
  · rfl

/-- Copying nothing changes nothing. -/
theorem copied_zero (mem : Memory) (dst src : Nat) : copied mem dst src 0 = mem := by
  funext a
  simp only [copied, store]
  split <;> first | omega | rfl

/-- Copying more bytes after some, apart from their source, extends the copy. -/
theorem copied_succ (mem : Memory) (dst src n k : Nat) (apart : Apart (dst, n + k) (src, n + k)) :
    copied (copied mem dst src n) (dst + n) (src + n) k = copied mem dst src (n + k) := by
  funext a
  simp only [Apart] at apart
  simp only [copied, store]
  -- A new byte reads a source byte the first part of the copy did not write.
  repeat' split
  all_goals first | omega | rfl | (congr 1; omega)

/-- A subrange of bytes a program may use is one too. -/
theorem access_sub {w : World} {a n b k : Nat} (h : w.access a n = true) (lo : a ≤ b) (hi : b + k ≤ a + n) :
    w.access b k = true := by
  rw [access_iff] at h ⊢
  omega

/-- Bytes a program may use end below half the word size. -/
theorem access_bound {w : World} {a n : Nat} (h : w.access a n = true) : a + n ≤ 2 ^ 63 :=
  ((access_iff w a n).mp h).1

/-- A little-endian load reads only its own bytes. -/
theorem readLE_congr (m₁ m₂ : Nat → UInt8) (a n : Nat) (same : ∀ i < n, m₁ (a + i) = m₂ (a + i)) :
    readLE m₁ a n = readLE m₂ a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [readLE]
    rw [show m₁ a = m₂ a from same 0 (by omega), ih (a + 1) fun i hi => by
      rw [show a + 1 + i = a + (i + 1) by omega]; exact same (i + 1) (by omega)]

/-! ## Hashing in pieces -/

/-- Hashing no pairs changes nothing. -/
theorem hashed_zero (mem : Memory) (out left right ls rs : Nat) : hashed mem out left right 0 ls rs = mem := by
  funext a
  simp only [hashed]
  rw [if_neg (by omega)]

/-- Hashing leaves every byte outside the digests as it was. -/
theorem hashed_outside {mem : Memory} {out left right count ls rs a : Nat}
    (outside : ¬ (out ≤ a ∧ a < out + 32 * count)) : hashed mem out left right count ls rs a = mem a := by
  simp only [hashed]
  rw [if_neg outside]

/-- Byte k of digest p, after hashing. -/
theorem hashed_inside {mem : Memory} {out left right count ls rs p k : Nat} (hp : p < count) (hk : k < 32) :
    hashed mem out left right count ls rs (out + 32 * p + k) =
      (Sha256.hash (pairMessage mem (left + ls * p) (right + rs * p))).get! k := by
  simp only [hashed]
  rw [if_pos (by omega), show (out + 32 * p + k - out) / 32 = p by omega,
    show (out + 32 * p + k - out) % 32 = k by omega]

/--
Hashing some pairs, then more from the moved pointers, is hashing them all at once.

No digest may overwrite an input node, so later pairs read what was there at the start.
-/
theorem hashed_append (mem : Memory) (out left right k j ls rs : Nat)
    (apart : ∀ p < k + j, Apart (out, 32 * (k + j)) (left + ls * p, 32) ∧
      Apart (out, 32 * (k + j)) (right + rs * p, 32)) :
    hashed (hashed mem out left right k ls rs) (out + 32 * k) (left + ls * k) (right + rs * k) j ls rs =
      hashed mem out left right (k + j) ls rs := by
  funext a
  by_cases late : out + 32 * k ≤ a ∧ a < out + 32 * k + 32 * j
  · -- A digest of the second piece: pair k + q, read from memory the first piece left alone.
    obtain ⟨q, b, hq, hb, rfl⟩ : ∃ q b, q < j ∧ b < 32 ∧ a = out + 32 * k + 32 * q + b :=
      ⟨(a - (out + 32 * k)) / 32, (a - (out + 32 * k)) % 32, by omega, by omega, by omega⟩
    rw [hashed_inside hq hb, show out + 32 * k + 32 * q + b = out + 32 * (k + q) + b by omega,
      hashed_inside (by omega) hb, Nat.mul_add ls, Nat.mul_add rs, ← Nat.add_assoc, ← Nat.add_assoc]
    obtain ⟨al, ar⟩ := apart (k + q) (by omega)
    simp only [Apart, Nat.mul_add] at al ar
    rw [Kernel.Avx512.pairMessage_congr (hashed mem out left right k ls rs) mem _ _
      (fun i hi => hashed_outside (by omega)) (fun i hi => hashed_outside (by omega))]
  · rw [hashed_outside late]
    by_cases early : out ≤ a ∧ a < out + 32 * k
    · -- A digest of the first piece, the same in both.
      obtain ⟨q, b, hq, hb, rfl⟩ : ∃ q b, q < k ∧ b < 32 ∧ a = out + 32 * q + b :=
        ⟨(a - out) / 32, (a - out) % 32, by omega, by omega, by omega⟩
      rw [hashed_inside hq hb, hashed_inside (by omega) hb]
    · rw [hashed_outside early, hashed_outside (by omega)]

/-- What hashing a whole run needs, it needs for the pairs left after hashing some of them. -/
theorem _root_.Ssz.Native.Ir.HashPre.rest {w : World} {mem : Memory} {out left right count ls rs table k j : Nat}
    (pre : HashPre w mem out left right count ls rs table) (le : k + j ≤ count) :
    HashPre w (hashed mem out left right k ls rs) (out + 32 * k) (left + ls * k) (right + rs * k) j ls rs table := by
  have ta := pre.tableApart
  simp only [Apart] at ta
  have mk := Nat.mul_le_mul_left ls le
  have mr := Nat.mul_le_mul_left rs le
  have reach := pre.reach
  rw [Nat.mul_add] at mk mr
  refine ⟨fun i hi => ?_, access_sub pre.outAccess (by omega) (by omega), pre.tableAccess, fun p hp => ?_,
    ⟨by omega, by omega⟩, by simp only [Apart]; omega, fun p hp => ?_⟩
  · -- The table lies apart from every digest.
    rw [hashed_outside (by omega)]
    exact pre.tableAt i hi
  · -- Node p of the rest is node k + p of the run.
    have := pre.inputsAccess (k + p) (by omega)
    rwa [Nat.mul_add, Nat.mul_add, ← Nat.add_assoc, ← Nat.add_assoc] at this
  · have := pre.inputsApart (k + p) (by omega)
    simp only [Apart, Nat.mul_add] at this ⊢
    omega

/-- A run's digests lie apart from every input node, as the composition of pieces needs. -/
theorem _root_.Ssz.Native.Ir.HashPre.apart {w : World} {mem : Memory} {out left right count ls rs table : Nat}
    (pre : HashPre w mem out left right count ls rs table) :
    ∀ p < count, Apart (out, 32 * count) (left + ls * p, 32) ∧ Apart (out, 32 * count) (right + rs * p, 32) :=
  pre.inputsApart

/-! ## Runs to a condition -/

/-- A block of statements splits into its first statement and the rest. -/
theorem Runs.block_cons_inv {m : Module} {w : World} {sp : Nat} {env₁ env₃ : Env} {mem₁ mem₃ : Memory} {s : Stmt}
    {rest : List Stmt} (h : Runs m w sp env₁ mem₁ (.block (s :: rest)) env₃ mem₃) :
    ∃ env₂ mem₂, Runs m w sp env₁ mem₁ s env₂ mem₂ ∧
      Runs m w sp env₂ mem₂ (.block rest) env₃ mem₃ := by
  cases rest with
  | nil => exact ⟨env₃, mem₃, h, Runs.block_nil m w sp env₃ mem₃⟩
  | cons t more =>
    obtain ⟨fuel, e⟩ := h
    cases fuel with
    | zero => simp [Ir.exec] at e
    | succ fuel =>
      -- The block is the first statement, then the block of the rest.
      simp only [Stmt.block, Ir.exec, bind, Option.bind] at e
      split at e
      · cases e
      · rename_i r hr
        exact ⟨r.1, r.2, ⟨fuel, hr⟩, ⟨fuel, e⟩⟩

/-- Two blocks run one after the other run as the block of both. -/
theorem Runs.block_append {m : Module} {w : World} {sp : Nat} {env₁ env₂ env₃ : Env} {mem₁ mem₂ mem₃ : Memory}
    {a b : List Stmt} (ha : Runs m w sp env₁ mem₁ (.block a) env₂ mem₂)
    (hb : Runs m w sp env₂ mem₂ (.block b) env₃ mem₃) :
    Runs m w sp env₁ mem₁ (.block (a ++ b)) env₃ mem₃ := by
  induction a generalizing env₁ mem₁ with
  | nil =>
    -- An empty block leaves the state as it was.
    obtain ⟨fuel, e⟩ := ha
    cases fuel with
    | zero => simp [Ir.exec] at e
    | succ fuel =>
      simp only [Stmt.block, Ir.exec, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact hb
  | cons s rest ih =>
    obtain ⟨env, mem, hs, hr⟩ := Runs.block_cons_inv ha
    exact Runs.block_cons hs (ih hr)

/-- A statement runs from a state to some state meeting a condition. -/
def Ends (m : Module) (w : World) (sp : Nat) (env : Env) (mem : Memory) (s : Stmt) (P : Env → Memory → Prop) :
    Prop :=
  ∃ env' mem', Runs m w sp env mem s env' mem' ∧ P env' mem'

/-- A weaker condition holds wherever a stronger one does. -/
theorem Ends.mono {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {s : Stmt}
    {P Q : Env → Memory → Prop} (h : Ends m w sp env mem s P) (imp : ∀ e mm, P e mm → Q e mm) :
    Ends m w sp env mem s Q := by
  obtain ⟨e, mm, r, p⟩ := h
  exact ⟨e, mm, r, imp e mm p⟩

/-- A known run ends where its condition holds. -/
theorem Ends.of_runs {m : Module} {w : World} {sp : Nat} {env env' : Env} {mem mem' : Memory} {s : Stmt}
    {P : Env → Memory → Prop} (r : Runs m w sp env mem s env' mem') (p : P env' mem') : Ends m w sp env mem s P :=
  ⟨env', mem', r, p⟩

/-- An empty block ends where it starts. -/
theorem Ends.nil {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {P : Env → Memory → Prop}
    (p : P env mem) : Ends m w sp env mem (.block []) P :=
  ⟨env, mem, Runs.block_nil m w sp env mem, p⟩

/-- A block ends where its rest ends, from where its first statement ends. -/
theorem Ends.cons {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {s : Stmt} {rest : List Stmt}
    {Q P : Env → Memory → Prop} (hs : Ends m w sp env mem s Q)
    (hr : ∀ e mm, Q e mm → Ends m w sp e mm (.block rest) P) : Ends m w sp env mem (.block (s :: rest)) P := by
  obtain ⟨e, mm, r, q⟩ := hs
  obtain ⟨e', mm', r', p⟩ := hr e mm q
  exact ⟨e', mm', Runs.block_cons r r', p⟩

/-- A block ends where its rest ends, from where a known run of its first statement leaves it. -/
theorem Ends.step {m : Module} {w : World} {sp : Nat} {env env' : Env} {mem mem' : Memory} {s : Stmt}
    {rest : List Stmt} {P : Env → Memory → Prop} (hs : Runs m w sp env mem s env' mem')
    (hr : Ends m w sp env' mem' (.block rest) P) : Ends m w sp env mem (.block (s :: rest)) P := by
  obtain ⟨e, mm, r, p⟩ := hr
  exact ⟨e, mm, Runs.block_cons hs r, p⟩

/-- Two blocks one after the other end where the second ends, from where the first does. -/
theorem Ends.append {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {a b : List Stmt}
    {Q P : Env → Memory → Prop} (ha : Ends m w sp env mem (.block a) Q)
    (hb : ∀ e mm, Q e mm → Ends m w sp e mm (.block b) P) : Ends m w sp env mem (.block (a ++ b)) P := by
  obtain ⟨e, mm, r, q⟩ := ha
  obtain ⟨e', mm', r', p⟩ := hb e mm q
  exact ⟨e', mm', Runs.block_append r r', p⟩

/-- A branch ends where the branch its condition picks ends. -/
theorem Ends.ite {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {c : Expr} {t e : Stmt}
    {P : Env → Memory → Prop} (v : UInt64) (hc : eval w env mem c = some v)
    (ht : v ≠ 0 → Ends m w sp env mem t P) (he : v = 0 → Ends m w sp env mem e P) :
    Ends m w sp env mem (.ite c t e) P := by
  by_cases zero : v = 0
  · subst zero
    obtain ⟨e', mm, r, p⟩ := he rfl
    exact ⟨e', mm, Runs.ite_false hc r, p⟩
  · obtain ⟨e', mm, r, p⟩ := ht zero
    exact ⟨e', mm, Runs.ite_true v hc zero r, p⟩

/-- A one-armed branch ends where its body ends, or where it starts when the condition is zero. -/
theorem Ends.when {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {c : Expr} {body : List Stmt}
    {P : Env → Memory → Prop} (v : UInt64) (hc : eval w env mem c = some v)
    (ht : v ≠ 0 → Ends m w sp env mem (.block body) P) (he : v = 0 → P env mem) :
    Ends m w sp env mem (Stmt.when c body) P :=
  Ends.ite v hc ht fun z => ⟨env, mem, Runs.skip m w sp env mem, he z⟩

/--
A loop with an invariant and a measure every pass decreases ends where the invariant holds and the condition is zero.
-/
theorem Ends.loop {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {c : Expr} {body : Stmt}
    (inv : Env → Memory → Prop) (measure : Env → Memory → Nat) (start : inv env mem)
    (cond : ∀ e mm, inv e mm → ∃ v, eval w e mm c = some v)
    (pass : ∀ e mm v, inv e mm → eval w e mm c = some v → v ≠ 0 →
      Ends m w sp e mm body fun e' mm' => inv e' mm' ∧ measure e' mm' < measure e mm) :
    Ends m w sp env mem (.loop c body) fun e mm => inv e mm ∧ eval w e mm c = some 0 :=
  Runs.loop_inv inv measure cond (fun e mm v i hv nz => by
    obtain ⟨e', mm', r, p⟩ := pass e mm v i hv nz
    exact ⟨e', mm', r, p⟩) env mem start

/-! ## Expressions -/

section
variable {w : World} {env : Env} {mem : Memory}

/-- A variable's value. -/
theorem eval_var {x : Nat} {v : UInt64} (h : env x = v) : eval w env mem (.var x) = some v := by
  rw [← h]; rfl

/-- A literal's value. -/
theorem eval_lit (n : Nat) : eval w env mem (no_index (OfNat.ofNat n : Expr)) = some (UInt64.ofNat n) := rfl

/-- A computed constant's value. -/
theorem eval_cast (n : Nat) : eval w env mem ((n : Nat) : Expr) = some (UInt64.ofNat n) := rfl

/-- A sum of converted numbers is the conversion of their sum. -/
theorem eval_add {a b : Expr} {p q : Nat} (ha : eval w env mem a = some (UInt64.ofNat p))
    (hb : eval w env mem b = some (UInt64.ofNat q)) : eval w env mem (a + b) = some (UInt64.ofNat (p + q)) := by
  show eval w env mem (.op .add a b) = _
  simp only [eval, ha, hb, aluResult, Option.bind_eq_bind, Option.bind, ofNat_add']
  rfl

/-- A product of converted numbers is the conversion of their product. -/
theorem eval_mul {a b : Expr} {p q : Nat} (ha : eval w env mem a = some (UInt64.ofNat p))
    (hb : eval w env mem b = some (UInt64.ofNat q)) : eval w env mem (a * b) = some (UInt64.ofNat (p * q)) := by
  show eval w env mem (.op .mul a b) = _
  simp only [eval, ha, hb, aluResult, Option.bind_eq_bind, Option.bind, ofNat_mul']
  rfl

/-- A difference of converted numbers, the second at most the first, is the conversion of their difference. -/
theorem eval_sub {a b : Expr} {p q : Nat} (ha : eval w env mem a = some (UInt64.ofNat p))
    (hb : eval w env mem b = some (UInt64.ofNat q)) (le : q ≤ p) :
    eval w env mem (a - b) = some (UInt64.ofNat (p - q)) := by
  show eval w env mem (.op .sub a b) = _
  simp only [eval, ha, hb, aluResult, Option.bind_eq_bind, Option.bind, ofNat_sub' le]
  rfl

/-- A quotient of converted numbers below the word size is the conversion of their quotient. -/
theorem eval_div {a b : Expr} {p q : Nat} (ha : eval w env mem a = some (UInt64.ofNat p))
    (hb : eval w env mem b = some (UInt64.ofNat q)) (bp : p < 2 ^ 64) (bq : q < 2 ^ 64) (nz : q ≠ 0) :
    eval w env mem (a / b) = some (UInt64.ofNat (p / q)) := by
  show eval w env mem (.div a b) = _
  have : (UInt64.ofNat q == 0) = false := by
    rw [beq_eq_false_iff_ne]
    intro z
    exact nz ((ofNat_inj bq (by decide)).mp z)
  simp only [eval, ha, hb, Option.bind_eq_bind, Option.bind, this, ofNat_div bp bq]
  rfl

/-- The bitwise and of two values. -/
theorem eval_and {a b : Expr} {x y : UInt64} (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (a &&& b) = some (x &&& y) := by
  show eval w env mem (.op .and a b) = _
  simp only [eval, ha, hb, aluResult, Option.bind_eq_bind, Option.bind]
  rfl

/-- Whether two values differ, as one or zero. -/
theorem eval_ne {a b : Expr} {x y : UInt64} (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (Expr.ne a b) = some (if x = y then 0 else 1) := by
  show eval w env mem (.cmp .ne a b) = _
  simp only [eval, ha, hb, Option.bind_eq_bind, Option.bind, Cond.holds]
  by_cases h : x = y <;> simp [h]

/-- Whether one converted number is below another, as one or zero. -/
theorem eval_lt {a b : Expr} {p q : Nat} (ha : eval w env mem a = some (UInt64.ofNat p))
    (hb : eval w env mem b = some (UInt64.ofNat q)) (bp : p < 2 ^ 64) (bq : q < 2 ^ 64) :
    eval w env mem (Expr.lt a b) = some (if p < q then 1 else 0) := by
  show eval w env mem (.cmp .b a b) = _
  simp only [eval, ha, hb, Option.bind_eq_bind, Option.bind, Cond.holds]
  by_cases h : p < q
  · simp [h, (ofNat_lt bp bq).mpr h]
  · simp [h, mt (ofNat_lt bp bq).mp h]

/-- Eight bytes a program may use, loaded. -/
theorem eval_ld {a : Expr} {n : Nat} (ha : eval w env mem a = some (UInt64.ofNat n)) (acc : w.access n 8 = true) :
    eval w env mem (Expr.ld a) = some (readLE mem n 8) := by
  have bn : n < 2 ^ 64 := by have := access_bound acc; omega
  show eval w env mem (.load .b8 a) = _
  simp only [eval, ha, Option.bind_eq_bind, Option.bind, ofNat_toNat bn, Width.bytes, acc]
  rfl

/-- Five arguments evaluated in order. -/
theorem eval_five {a b c d e : Expr} {va vb vc vd ve : UInt64} (ha : eval w env mem a = some va)
    (hb : eval w env mem b = some vb) (hc : eval w env mem c = some vc) (hd : eval w env mem d = some vd)
    (he : eval w env mem e = some ve) : [a, b, c, d, e].mapM (eval w env mem) = some [va, vb, vc, vd, ve] := by
  simp [List.mapM_cons, ha, hb, hc, hd, he]

/-- A right shift of a converted number below the word size divides it by a power of two. -/
theorem eval_shr {a : Expr} {p j : Nat} (ha : eval w env mem a = some (UInt64.ofNat p)) (bp : p < 2 ^ 64)
    (hj : j < 64) : eval w env mem (.shr a j) = some (UInt64.ofNat (p / 2 ^ j)) := by
  have small : p / 2 ^ j < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self p _) bp
  simp only [eval, ha, Option.bind_eq_bind, Option.bind, if_pos hj]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, ofNat_toNat bp, ofNat_toNat small, Nat.shiftRight_eq_div_pow]
  congr 2
  simp [Nat.mod_eq_of_lt hj]

/-- A left shift of a converted number, the product below the word size, multiplies it by a power of two. -/
theorem eval_shl {a : Expr} {p j : Nat} (ha : eval w env mem a = some (UInt64.ofNat p)) (bp : p * 2 ^ j < 2 ^ 64)
    (hj : j < 64) : eval w env mem (.shl a j) = some (UInt64.ofNat (p * 2 ^ j)) := by
  have small : p < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right p (Nat.two_pow_pos j)) bp
  simp only [eval, ha, Option.bind_eq_bind, Option.bind, if_pos hj]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftLeft, ofNat_toNat small, ofNat_toNat bp, Nat.shiftLeft_eq]
  have count : (j.toUInt64).toNat % 64 = j := by simp [Nat.mod_eq_of_lt hj]
  rw [count, Nat.mod_eq_of_lt bp]

end

/-- Writing one variable leaves the others alone. -/
theorem assign_ne {env : Env} {x y : Nat} {v : UInt64} (h : y ≠ x) : assign env x v y = env y := by
  simp [assign, h]

/-- Writing a variable, then reading it back. -/
theorem assign_eq {env : Env} {x : Nat} {v : UInt64} : assign env x v x = v := by
  simp [assign]

/-! ## Copies -/

/-- Eight bytes loaded and stored elsewhere are copied there. -/
theorem copy8_runs {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {dst src : Expr} {d s : Nat}
    (j : Nat) (hd : eval w env mem dst = some (UInt64.ofNat d)) (hs : eval w env mem src = some (UInt64.ofNat s))
    (ad : w.access (d + j) 8 = true) (as : w.access (s + j) 8 = true) :
    Runs m w sp env mem (Stmt.st (dst + ((j : Nat) : Expr)) (Expr.ld (src + ((j : Nat) : Expr)))) env
      (copied mem (d + j) (s + j) 8) := by
  have bd : d + j < 2 ^ 64 := by have := access_bound ad; omega
  have bs : s + j < 2 ^ 64 := by have := access_bound as; omega
  have ea : eval w env mem (dst + ((j : Nat) : Expr)) = some (UInt64.ofNat (d + j)) := by
    show eval w env mem (.op .add dst (.lit j.toUInt64)) = _
    simp [eval, hd, aluResult]
  have el : eval w env mem (Expr.ld (src + ((j : Nat) : Expr))) = some (readLE mem (s + j) 8) := by
    show eval w env mem (.load .b8 (.op .add src (.lit j.toUInt64))) = _
    simp [eval, hs, aluResult, Width.bytes, Nat.mod_eq_of_lt bs, as]
  have := Runs.store m w sp env mem .b8 _ _ _ _ ea el (by rw [ofNat_toNat bd]; exact ad)
  rwa [ofNat_toNat bd, show Width.bytes .b8 = 8 from rfl, store_load] at this

/-- Thirty-two bytes copied apart from their source land at the destination. -/
theorem copy32_runs {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {dst src : Expr} {d s : Nat}
    (hd : ∀ mem, eval w env mem dst = some (UInt64.ofNat d)) (hs : ∀ mem, eval w env mem src = some (UInt64.ofNat s))
    (ad : w.access d 32 = true) (as : w.access s 32 = true) (apart : Apart (d, 32) (s, 32)) :
    Runs m w sp env mem (.block (copy32 dst src)) env (copied mem d s 32) := by
  simp only [Apart] at apart
  -- Each eight bytes extend the copy so far, reading source bytes no earlier store wrote.
  have r0 : Runs m w sp env mem (Stmt.st (dst + ((8 * 0 : Nat) : Expr)) (Expr.ld (src + ((8 * 0 : Nat) : Expr))))
      env (copied mem d s 8) :=
    copy8_runs (8 * 0) (hd mem) (hs mem) (access_sub ad (by omega) (by omega)) (access_sub as (by omega) (by omega))
  have r1 : Runs m w sp env (copied mem d s 8)
      (Stmt.st (dst + ((8 * 1 : Nat) : Expr)) (Expr.ld (src + ((8 * 1 : Nat) : Expr)))) env (copied mem d s 16) := by
    have := copy8_runs (m := m) (sp := sp) (mem := copied mem d s 8) (8 * 1) (hd _) (hs _)
      (access_sub ad (by omega) (by omega)) (access_sub as (by omega) (by omega))
    rwa [copied_succ mem d s 8 8 (by simp only [Apart]; omega)] at this
  have r2 : Runs m w sp env (copied mem d s 16)
      (Stmt.st (dst + ((8 * 2 : Nat) : Expr)) (Expr.ld (src + ((8 * 2 : Nat) : Expr)))) env (copied mem d s 24) := by
    have := copy8_runs (m := m) (sp := sp) (mem := copied mem d s 16) (8 * 2) (hd _) (hs _)
      (access_sub ad (by omega) (by omega)) (access_sub as (by omega) (by omega))
    rwa [copied_succ mem d s 16 8 (by simp only [Apart]; omega)] at this
  have r3 : Runs m w sp env (copied mem d s 24)
      (Stmt.st (dst + ((8 * 3 : Nat) : Expr)) (Expr.ld (src + ((8 * 3 : Nat) : Expr)))) env (copied mem d s 32) := by
    have := copy8_runs (m := m) (sp := sp) (mem := copied mem d s 24) (8 * 3) (hd _) (hs _)
      (access_sub ad (by omega) (by omega)) (access_sub as (by omega) (by omega))
    rwa [copied_succ mem d s 24 8 (by simp only [Apart]; omega)] at this
  exact Runs.seq r0 (Runs.seq r1 (Runs.seq r2 r3))

/-! ## The module -/

/-- A hashing kernel's exported name, by its family and a layout's suffix. -/
def kernelName (family suffix : String) : String :=
  s!"ssz_sha256_{family}_{suffix}"

/-- A hashing driver's exported name. -/
def Layout.name (layout : Layout) : String :=
  s!"ssz_hash_{layout.info.1}"

/-- A module holds a routine outside the language under a name, with a given meaning. -/
def KernelAt (m : Module) (name : String) (ext : Extern) : Prop :=
  m.fns.lookup name = none ∧ m.ext.lookup name = some ext

/-- A meaning that, at one stack pointer, answers every call as a hashing kernel's meaning does. -/
def Answers (w : World) (sp : Nat) (ext : Extern) (code : Array Instr) (batch ls rs : Nat) : Prop :=
  ∀ args mem, ext.run w sp args mem = (hashExtern code batch ls rs).run w sp args mem

/-- A hashing kernel's meaning answers as itself. -/
theorem answers_hash {w : World} {sp : Nat} {code : Array Instr} {batch ls rs : Nat} :
    Answers w sp (hashExtern code batch ls rs) code batch ls rs :=
  fun _ _ => rfl

/-- A hashing kernel's meaning with scratch answers as the one without, where the stack has room for the scratch. -/
theorem answers_frame {w : World} {sp : Nat} {code : Array Instr} {batch ls rs frame : Nat}
    (room : w.stackLo + 8 + frame ≤ sp) : Answers w sp (hashFrameExtern code batch ls rs frame) code batch ls rs :=
  fun _ _ => by simp only [hashFrameExtern, if_pos room]

/-- A module holding the three hashing drivers, and the eighteen kernels they call, under their exported names. -/
structure HashModule (m : Module) : Prop where
  /-- Each driver, compiled from the language. -/
  drivers : ∀ layout : Layout, m.fns.lookup layout.name = some (hashRun layout)
  /-- The thirty-two-lane kernel for each layout, with its scratch. -/
  avx512x2 : ∀ layout : Layout, KernelAt m (kernelName "avx512x2" layout.info.1)
    (hashFrameExtern (Kernel.Avx512x2.program layout.info.2.1 layout.info.2.2) 32 layout.info.2.1 layout.info.2.2
      Kernel.Avx512x2.frame)
  /-- The sixteen-lane kernel for each layout. -/
  avx512 : ∀ layout : Layout, KernelAt m (kernelName "avx512" layout.info.1)
    (hashExtern (Kernel.Avx512.program layout.info.2.1 layout.info.2.2) 16 layout.info.2.1 layout.info.2.2)
  /-- The one-pair SHA-NI kernel for each layout. -/
  shani : ∀ layout : Layout, KernelAt m (kernelName "shani" layout.info.1)
    (hashExtern (Kernel.ShaNi.program layout.info.2.1 layout.info.2.2) 1 layout.info.2.1 layout.info.2.2)
  /-- The two-pair SHA-NI kernel for each layout. -/
  shaniDual : ∀ layout : Layout, KernelAt m (kernelName "shani_dual" layout.info.1)
    (hashExtern (Kernel.ShaNiDual.program layout.info.2.1 layout.info.2.2) 2 layout.info.2.1 layout.info.2.2)
  /-- The eight-lane AVX2 kernel for each layout, with its scratch. -/
  avx2 : ∀ layout : Layout, KernelAt m (kernelName "avx2" layout.info.1)
    (hashFrameExtern (Kernel.Avx2.program layout.info.2.1 layout.info.2.2) 8 layout.info.2.1 layout.info.2.2
      Kernel.Avx2.frame)
  /-- The four-lane SSE2 kernel for each layout, with its scratch. -/
  baseline : ∀ layout : Layout, KernelAt m (kernelName "baseline" layout.info.1)
    (hashFrameExtern (Kernel.Baseline.program layout.info.2.1 layout.info.2.2) 4 layout.info.2.1 layout.info.2.2
      Kernel.Baseline.frame)

/--
The processor runs every kernel of each family the feature mask names.

Bit 1 names both AVX-512 kernels, bit 0 both SHA-NI kernels, and bit 3 the AVX2 kernel.
The SSE2 kernel needs no bit: every processor runs it.
-/
def KernelsRun (w : World) (mask : UInt64) : Prop :=
  (mask &&& 2 ≠ 0 → ∀ ls rs,
      w.cpu.runs (Kernel.Avx512.program ls rs) = true ∧ w.cpu.runs (Kernel.Avx512x2.program ls rs) = true) ∧
    (mask &&& 1 ≠ 0 → ∀ ls rs,
      w.cpu.runs (Kernel.ShaNi.program ls rs) = true ∧ w.cpu.runs (Kernel.ShaNiDual.program ls rs) = true) ∧
    (mask &&& 8 ≠ 0 → ∀ ls rs, w.cpu.runs (Kernel.Avx2.program ls rs) = true)

/--
What a hashing run needs: its context words, its pairs, and a padding area apart from all it touches.

The context holds the feature mask, then the table's address at 8, and the padding area's address at 24.
-/
structure RunPre (w : World) (mem : Memory) (ls rs out left right count ctx table pad : Nat) (mask : UInt64) :
    Prop where
  /-- The context's four words lie in memory the program may use. -/
  ctxAccess : w.access ctx 32 = true
  /-- The first word is the feature mask. -/
  maskAt : readLE mem ctx 8 = mask
  /-- The second word is the constant table's address. -/
  tableAt : readLE mem (ctx + 8) 8 = UInt64.ofNat table
  /-- The fourth word is the padding area's address. -/
  padAt : readLE mem (ctx + 24) 8 = UInt64.ofNat pad
  /-- The whole run of pairs meets the kernels' conditions. -/
  pairs : HashPre w mem out left right count ls rs table
  /-- The padding area lies in memory the program may use. -/
  padAccess : w.access pad 1536 = true
  /-- It misses the digests. -/
  padOut : Apart (pad, 1536) (out, 32 * count)
  /-- It misses the table. -/
  padTable : Apart (pad, 1536) (table, Kernel.tableSize)
  /-- It misses every input node. -/
  padInputs : ∀ p < count, Apart (pad, 1536) (left + ls * p, 32) ∧ Apart (pad, 1536) (right + rs * p, 32)
  /-- The digests miss the context. -/
  ctxOut : Apart (ctx, 32) (out, 32 * count)

/-! ## Steps of a run -/

/--
The variables of a hashing run after k pairs.

The pointers have moved past them, the count has gone down by them, and the rest is as loaded at the start.
-/
structure At (env : Env) (ls rs out left right count ctx table : Nat) (mask : UInt64) (k : Nat) : Prop where
  /-- No more pairs than the run has are done. -/
  le : k ≤ count
  /-- The output pointer. -/
  out : env 0 = UInt64.ofNat (out + 32 * k)
  /-- The left pointer. -/
  left : env 1 = UInt64.ofNat (left + ls * k)
  /-- The right pointer. -/
  right : env 2 = UInt64.ofNat (right + rs * k)
  /-- The pairs left. -/
  count : env 3 = UInt64.ofNat (count - k)
  /-- The context. -/
  ctx : env 4 = UInt64.ofNat ctx
  /-- The feature mask. -/
  mask : env 5 = mask
  /-- The table's address. -/
  table : env 6 = UInt64.ofNat table
  /-- The result so far. -/
  status : env 8 = 0

/-- Writing a scratch variable keeps the state of a run. -/
theorem At.write {env : Env} {ls rs out left right count ctx table : Nat} {mask : UInt64} {k x : Nat} (v : UInt64)
    (h : At env ls rs out left right count ctx table mask k) (hx : 8 < x ∨ x = 7) :
    At (assign env x v) ls rs out left right count ctx table mask k := by
  -- Every variable the state names is another one.
  have r : ∀ y, (y ≤ 6 ∨ y = 8) → assign env x v y = env y := fun y hy => assign_ne (by omega)
  exact ⟨h.le, (r 0 (by omega)).trans h.out, (r 1 (by omega)).trans h.left, (r 2 (by omega)).trans h.right,
    (r 3 (by omega)).trans h.count, (r 4 (by omega)).trans h.ctx, (r 5 (by omega)).trans h.mask,
    (r 6 (by omega)).trans h.table, (r 8 (by omega)).trans h.status⟩

/-- A one-or-zero test that is not zero means its condition fails. -/
theorem ite_ne_zero {p : Prop} [Decidable p] (h : (if p then (0 : UInt64) else 1) ≠ 0) : ¬ p := by
  intro hp; exact h (if_pos hp)

/-- A one-or-zero test that is zero means its condition holds. -/
theorem ite_eq_zero {p : Prop} [Decidable p] (h : (if p then (0 : UInt64) else 1) = 0) : p := by
  by_cases hp : p
  · exact hp
  · rw [if_neg hp] at h; exact absurd h (by decide)

/-- A word converted from a number below the word size is zero only for zero. -/
theorem ofNat_eq_zero {n : Nat} (h : n < 2 ^ 64) : UInt64.ofNat n = 0 ↔ n = 0 :=
  ofNat_inj h (by decide)

/-- Moving the pointers past a number of pairs held in a variable, and counting them off, keeps the state of the run. -/
theorem advance_ends {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory}
    {ls rs out left right count ctx table : Nat} {mask : UInt64} {k : Nat} (d : Nat)
    (h : At env ls rs out left right count ctx table mask k) (hn : env 7 = UInt64.ofNat d) (le : k + d ≤ count) :
    Ends m w sp env mem (.block [Stmt.assign ⟨0⟩ (Expr.var 0 + 32 * Expr.var 7),
      Stmt.assign ⟨1⟩ (Expr.var 1 + ((ls : Nat) : Expr) * Expr.var 7),
      Stmt.assign ⟨2⟩ (Expr.var 2 + ((rs : Nat) : Expr) * Expr.var 7),
      Stmt.assign ⟨3⟩ (Expr.var 3 - Expr.var 7)])
      fun e mm => At e ls rs out left right count ctx table mask (k + d) ∧ mm = mem := by
  -- Each assignment reads variables the earlier ones did not write.
  have n1 := (assign_ne (env := env) (v := env 0 + 32 * env 7) (by decide : (7 : Nat) ≠ 0)).trans hn
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_add (eval_var h.out) (eval_mul (eval_lit 32) (eval_var hn)))) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_add (eval_var ((assign_ne (by decide : (1 : Nat) ≠ 0)).trans h.left))
    (eval_mul (eval_cast ls) (eval_var n1)))) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_add
    (eval_var (((assign_ne (by decide : (2 : Nat) ≠ 1))).trans ((assign_ne (by decide : (2 : Nat) ≠ 0)).trans h.right)))
    (eval_mul (eval_cast rs) (eval_var ((assign_ne (by decide : (7 : Nat) ≠ 1)).trans n1))))) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_sub
    (eval_var ((assign_ne (by decide : (3 : Nat) ≠ 2)).trans ((assign_ne (by decide : (3 : Nat) ≠ 1)).trans
      ((assign_ne (by decide : (3 : Nat) ≠ 0)).trans h.count))))
    (eval_var ((assign_ne (by decide : (7 : Nat) ≠ 2)).trans ((assign_ne (by decide : (7 : Nat) ≠ 1)).trans n1)))
    (by omega))) ?_
  refine Ends.nil ⟨⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · -- The output pointer moves 32 bytes per pair.
    simp only [assign, show (0 : Nat) ≠ 3 by decide, show (0 : Nat) ≠ 2 by decide, show (0 : Nat) ≠ 1 by decide,
      if_false, if_true]
    congr 1; rw [Nat.mul_add]; omega
  · simp only [assign, show (1 : Nat) ≠ 3 by decide, show (1 : Nat) ≠ 2 by decide, if_false, if_true]
    congr 1; rw [Nat.mul_add]; omega
  · simp only [assign, show (2 : Nat) ≠ 3 by decide, if_false, if_true]
    congr 1; rw [Nat.mul_add]; omega
  · simp only [assign, if_true]
    congr 1; omega
  · simp only [assign]; exact h.ctx
  · simp only [assign]; exact h.mask
  · simp only [assign]; exact h.table
  · simp only [assign]; exact h.status

/-- A hashing kernel called on the pairs after the first k hashes the next ones. -/
theorem kernel_runs {m : Module} {w : World} {sp : Nat} {env : Env} {mem mm : Memory} {name : String} {ext : Extern}
    {code : Array Instr} {batch ls rs out left right count table k q : Nat} {args : List Expr} {dst : Nat}
    (pre : HashPre w mem out left right count ls rs table) (le : k + batch * q ≤ count)
    (hm : mm = hashed mem out left right k ls rs) (at_ : KernelAt m name ext)
    (answers : Answers w sp ext code batch ls rs) (room : w.stackLo + 8 ≤ sp) (runs : w.cpu.runs code = true)
    (hv : args.mapM (eval w env mm) = some [UInt64.ofNat (out + 32 * k), UInt64.ofNat (left + ls * k),
      UInt64.ofNat (right + rs * k), UInt64.ofNat q, UInt64.ofNat table]) (hq : q < 2 ^ 64) :
    Runs m w sp env mm (.call name args dst) (assign env dst 0) (hashed mem out left right (k + batch * q) ls rs) := by
  subst hm
  have rest := pre.rest le
  have bo := access_bound rest.outAccess
  have bt := access_bound rest.tableAccess
  have reach := rest.reach
  have ab : addressBound = 2 ^ 63 := rfl
  refine Runs.call hv (Calls.ext at_.1 at_.2 room ?_)
  -- The kernel's meaning, on words that convert back to the numbers.
  rw [answers]
  have e0 := ofNat_toNat (show out + 32 * k < 2 ^ 64 by omega)
  have e1 := ofNat_toNat (show left + ls * k < 2 ^ 64 by omega)
  have e2 := ofNat_toNat (show right + rs * k < 2 ^ 64 by omega)
  have e3 := ofNat_toNat hq
  have e4 := ofNat_toNat (show table < 2 ^ 64 by omega)
  simp only [hashExtern]
  rw [e0, e1, e2, e3, e4]
  rw [if_pos ⟨runs, rest⟩, hashed_append mem out left right k (batch * q) ls rs
    fun p hp => by
      have := pre.inputsApart p (by omega)
      simp only [Apart] at this ⊢
      have : 32 * (k + batch * q) ≤ 32 * count := Nat.mul_le_mul_left 32 le
      omega]

/--
Whole batches of 2^j pairs, from the state after k pairs, hash every pair those batches cover.

The pairs left afterwards are fewer than a batch.
-/
theorem batches_ends {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory}
    {ls rs o l r c x tb : Nat} {mask : UInt64} {k j batch : Nat} {name : String} {ext : Extern} {code : Array Instr}
    (pre : HashPre w mem o l r c ls rs tb) (h : At env ls rs o l r c x tb mask k) (hb : batch = 2 ^ j)
    (hj : j < 64) (at_ : KernelAt m name ext) (answers : Answers w sp ext code batch ls rs)
    (room : w.stackLo + 8 ≤ sp) (runs : w.cpu.runs code = true) :
    Ends m w sp env (hashed mem o l r k ls rs) (.block (batches name j ls rs)) fun e mm =>
      At e ls rs o l r c x tb mask (k + batch * ((c - k) / batch)) ∧
        mm = hashed mem o l r (k + batch * ((c - k) / batch)) ls rs := by
  have kc := h.le
  have bo := access_bound pre.outAccess
  have pos : 0 < batch := by rw [hb]; exact Nat.two_pow_pos j
  have cover : batch * ((c - k) / batch) ≤ c - k := Nat.mul_div_le (c - k) batch
  have qle : (c - k) / batch ≤ c - k := Nat.div_le_self _ _
  -- The count of batches, the call, then the count of pairs they cover.
  refine Ends.append (Q := fun e mm => At e ls rs o l r c x tb mask k ∧
      e 7 = UInt64.ofNat (batch * ((c - k) / batch)) ∧ mm = hashed mem o l r (k + batch * ((c - k) / batch)) ls rs)
    ?_ fun e mm ⟨ate, h7, hm⟩ =>
      Ends.mono (advance_ends _ ate h7 (by omega)) fun _ _ ⟨at', hm'⟩ => ⟨at', hm'.trans hm⟩
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_shr (eval_var h.count) (by omega) hj)) ?_
  rw [← hb]
  refine Ends.cons (Q := fun e mm => At e ls rs o l r c x tb mask k ∧ e 7 = UInt64.ofNat ((c - k) / batch) ∧
      mm = hashed mem o l r (k + batch * ((c - k) / batch)) ls rs)
    (Ends.when _ (eval_ne (eval_var assign_eq) (eval_lit 0)) (fun v => ?_) (fun v => ?_)) ?_
  · exact Ends.of_runs (kernel_runs pre (k := k) (q := (c - k) / batch) (by omega) rfl at_ answers room runs
      (eval_five (eval_var ((assign_ne (by decide : (0 : Nat) ≠ 7)).trans h.out))
        (eval_var ((assign_ne (by decide : (1 : Nat) ≠ 7)).trans h.left))
        (eval_var ((assign_ne (by decide : (2 : Nat) ≠ 7)).trans h.right)) (eval_var assign_eq)
        (eval_var ((assign_ne (by decide : (6 : Nat) ≠ 7)).trans h.table))) (by omega))
      ⟨(h.write _ (Or.inr rfl)).write _ (Or.inl (by decide)),
        (assign_ne (by decide : (7 : Nat) ≠ 9)).trans assign_eq, rfl⟩
  · -- No whole batch: nothing is hashed.
    have cz : (c - k) / batch = 0 := (ofNat_inj (by omega) (by decide)).mp (ite_eq_zero v)
    exact ⟨h.write _ (Or.inr rfl), assign_eq, by rw [cz, Nat.mul_zero, Nat.add_zero]⟩
  · rintro e mm ⟨ate, h7, hm⟩
    have big : (c - k) / batch * 2 ^ j < 2 ^ 64 := by rw [← hb, Nat.mul_comm]; omega
    refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_shl (eval_var h7) big hj)) (Ends.nil ⟨ate.write _ (Or.inr rfl),
      assign_eq.trans (by rw [← hb, Nat.mul_comm]), hm⟩)

/-! ## The padded batch -/

/-- A copied byte inside the destination is the source byte at the same offset. -/
theorem copied_in (mem : Memory) (dst src n q : Nat) (hq : q < n) : copied mem dst src n (dst + q) = mem (src + q) := by
  simp only [copied, store]
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A byte outside the destination is not copied over. -/
theorem copied_out {mem : Memory} {dst src n a : Nat} (h : ¬ (dst ≤ a ∧ a < dst + n)) :
    copied mem dst src n a = mem a := by
  simp only [copied, store]
  rw [if_neg h]

/-- Two pairs whose nodes agree byte for byte have the same message. -/
theorem pairMessage_eq (m₁ m₂ : Nat → UInt8) (a b c d : Nat) (left : ∀ i < 32, m₁ (a + i) = m₂ (c + i))
    (right : ∀ i < 32, m₁ (b + i) = m₂ (d + i)) : pairMessage m₁ a b = pairMessage m₂ c d := by
  -- The message reads 32 bytes from each address, which agree.
  simp only [pairMessage]
  congr 2
  funext i
  split
  · exact left i.val (by omega)
  · exact right (i.val - 32) (by omega)

/-- Adding one to the loop index. -/
theorem incr_runs {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {j : Nat}
    (h : env 9 = UInt64.ofNat j) :
    Runs m w sp env mem (Stmt.assign ⟨9⟩ (Expr.var 9 + 1)) (assign env 9 (UInt64.ofNat (j + 1))) mem :=
  Runs.set _ _ _ _ _ _ _ _ (eval_add (eval_var h) (eval_lit 1))

/-- A loop index below a bound, read back. -/
theorem index_toNat {j bound : Nat} (h : j ≤ bound) (small : bound ≤ 2 ^ 63) : (UInt64.ofNat j).toNat = j :=
  ofNat_toNat (by omega)

/-- The loop copying each remaining pair into the padding area: left node at 64 p, right node 32 bytes on. -/
theorem copyIn_loop {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {ls rs left right count pd : Nat}
    (acc : w.access pd 1536 = true) (h10 : env 10 = UInt64.ofNat pd) (h9 : env 9 = 0)
    (h1 : env 1 = UInt64.ofNat left) (h2 : env 2 = UInt64.ofNat right) (h3 : env 3 = UInt64.ofNat count)
    (small : count ≤ 16)
    (inputs : ∀ p < count, w.access (left + ls * p) 32 = true ∧ w.access (right + rs * p) 32 = true)
    (apart : ∀ p < count, Apart (pd, 1536) (left + ls * p, 32) ∧ Apart (pd, 1536) (right + rs * p, 32)) :
    Ends m w sp env mem (Stmt.while_ (Expr.lt (Expr.var 9) (Expr.var 3))
      (copy32 (Expr.var 10 + 64 * Expr.var 9) (Expr.var 1 + ((ls : Nat) : Expr) * Expr.var 9) ++
        copy32 (Expr.var 10 + 64 * Expr.var 9 + 32) (Expr.var 2 + ((rs : Nat) : Expr) * Expr.var 9) ++
        [Stmt.assign ⟨9⟩ (Expr.var 9 + 1)]))
      fun e mm => (∀ y, y ≠ 9 → e y = env y) ∧ (∀ a, ¬ (pd ≤ a ∧ a < pd + 1536) → mm a = mem a) ∧
        ∀ p < count, ∀ q < 32, mm (pd + 64 * p + q) = mem (left + ls * p + q) ∧
          mm (pd + 64 * p + 32 + q) = mem (right + rs * p + q) := by
  have bp := access_bound acc
  refine Ends.mono (Ends.loop
    (fun e mm => (∀ y, y ≠ 9 → e y = env y) ∧ (∃ j, j ≤ count ∧ e 9 = UInt64.ofNat j ∧
      ∀ p < j, ∀ q < 32, mm (pd + 64 * p + q) = mem (left + ls * p + q) ∧
        mm (pd + 64 * p + 32 + q) = mem (right + rs * p + q)) ∧
      ∀ a, ¬ (pd ≤ a ∧ a < pd + 1536) → mm a = mem a)
    (fun e _ => count - (e 9).toNat)
    ⟨fun _ _ => rfl, ⟨0, by omega, h9, fun _ hp => absurd hp (by omega)⟩, fun _ _ => rfl⟩ ?_ ?_) ?_
  · rintro e mm ⟨frame, ⟨j, hj, h9', _⟩, _⟩
    exact ⟨_, eval_lt (eval_var h9') (eval_var ((frame 3 (by decide)).trans h3)) (by omega) (by omega)⟩
  · rintro e mm v ⟨frame, ⟨j, hj, h9', copiedSoFar⟩, outside⟩ hv nz
    rw [eval_lt (eval_var h9') (eval_var ((frame 3 (by decide)).trans h3)) (by omega) (by omega)] at hv
    have lt : j < count := by
      by_cases h : j < count
      · exact h
      · rw [if_neg h] at hv; cases hv; exact absurd rfl nz
    have e10 := (frame 10 (by decide)).trans h10
    have e1 := (frame 1 (by decide)).trans h1
    have e2 := (frame 2 (by decide)).trans h2
    obtain ⟨al, ar⟩ := inputs j lt
    obtain ⟨pl, pr⟩ := apart j lt
    have bl := access_bound al
    have br := access_bound ar
    simp only [Apart] at pl pr
    -- The left node, then the right node, each into its half of the pair's 64 bytes.
    have cl := copy32_runs (m := m) (sp := sp) (mem := mm)
      (fun _ => eval_add (eval_var e10) (eval_mul (eval_lit 64) (eval_var h9')))
      (fun _ => eval_add (eval_var e1) (eval_mul (eval_cast ls) (eval_var h9')))
      (access_sub acc (by omega) (by omega)) al (by simp only [Apart]; omega)
    have cr := copy32_runs (m := m) (sp := sp) (mem := copied mm (pd + 64 * j) (left + ls * j) 32)
      (fun _ => eval_add (eval_add (eval_var e10) (eval_mul (eval_lit 64) (eval_var h9'))) (eval_lit 32))
      (fun _ => eval_add (eval_var e2) (eval_mul (eval_cast rs) (eval_var h9')))
      (access_sub acc (by omega) (by omega)) ar (by simp only [Apart]; omega)
    refine Ends.of_runs (Runs.block_append (Runs.block_append cl cr) (incr_runs h9'))
      ⟨⟨fun y hy => ?_, ⟨j + 1, by omega, assign_eq, fun p hp q hq => ?_⟩, fun a ha => ?_⟩, ?_⟩
    · rw [assign_ne hy]; exact frame y hy
    · -- Earlier pairs stay; the new pair's nodes read the source, which lies outside the padding area.
      by_cases old : p < j
      · obtain ⟨hl, hr⟩ := copiedSoFar p old q hq
        refine ⟨?_, ?_⟩
        · rw [copied_out (by omega), copied_out (by omega), hl]
        · rw [copied_out (by omega), copied_out (by omega), hr]
      · have pj : p = j := by omega
        subst pj
        refine ⟨?_, ?_⟩
        · rw [copied_out (by omega), copied_in _ _ _ _ _ hq]
          exact outside _ (by omega)
        · rw [show pd + 64 * p + 32 + q = pd + 64 * p + 32 + q from rfl, copied_in _ _ _ _ _ hq, copied_out (by omega)]
          exact outside _ (by omega)
    · rw [copied_out (by omega), copied_out (by omega)]
      exact outside a ha
    · simp only [assign_eq, h9']
      rw [index_toNat (show j + 1 ≤ count by omega) (by omega), index_toNat hj (by omega)]
      omega
  · rintro e mm ⟨⟨frame, ⟨j, hj, h9', copiedAll⟩, outside⟩, done⟩
    -- The loop stops with every pair copied.
    rw [eval_lt (eval_var h9') (eval_var ((frame 3 (by decide)).trans h3)) (by omega) (by omega)] at done
    have all : count ≤ j := by
      by_cases h : j < count
      · rw [if_pos h] at done; cases done
      · omega
    exact ⟨frame, outside, fun p hp => copiedAll p (by omega)⟩

/-- The loop copying each digest from the padding area to its place in the output. -/
theorem copyOut_loop {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {out count pd : Nat}
    (acc : w.access pd 1536 = true) (h10 : env 10 = UInt64.ofNat pd) (h9 : env 9 = 0)
    (h0 : env 0 = UInt64.ofNat out) (h3 : env 3 = UInt64.ofNat count) (small : count ≤ 16)
    (outAcc : w.access out (32 * count) = true) (apart : Apart (pd, 1536) (out, 32 * count)) :
    Ends m w sp env mem (Stmt.while_ (Expr.lt (Expr.var 9) (Expr.var 3))
      (copy32 (Expr.var 0 + 32 * Expr.var 9) (Expr.var 10 + 1024 + 32 * Expr.var 9) ++
        [Stmt.assign ⟨9⟩ (Expr.var 9 + 1)]))
      fun e mm => (∀ y, y ≠ 9 → e y = env y) ∧ (∀ a, ¬ (out ≤ a ∧ a < out + 32 * count) → mm a = mem a) ∧
        ∀ p < count, ∀ q < 32, mm (out + 32 * p + q) = mem (pd + 1024 + 32 * p + q) := by
  have bp := access_bound acc
  have bo := access_bound outAcc
  simp only [Apart] at apart
  refine Ends.mono (Ends.loop
    (fun e mm => (∀ y, y ≠ 9 → e y = env y) ∧ ∃ j, j ≤ count ∧ e 9 = UInt64.ofNat j ∧
      (∀ a, ¬ (out ≤ a ∧ a < out + 32 * j) → mm a = mem a) ∧
      ∀ p < j, ∀ q < 32, mm (out + 32 * p + q) = mem (pd + 1024 + 32 * p + q))
    (fun e _ => count - (e 9).toNat)
    ⟨fun _ _ => rfl, 0, by omega, h9, fun _ _ => rfl, fun _ hp => absurd hp (by omega)⟩ ?_ ?_) ?_
  · rintro e mm ⟨frame, j, hj, h9', _⟩
    exact ⟨_, eval_lt (eval_var h9') (eval_var ((frame 3 (by decide)).trans h3)) (by omega) (by omega)⟩
  · rintro e mm v ⟨frame, j, hj, h9', outside, copiedSoFar⟩ hv nz
    rw [eval_lt (eval_var h9') (eval_var ((frame 3 (by decide)).trans h3)) (by omega) (by omega)] at hv
    have lt : j < count := by
      by_cases h : j < count
      · exact h
      · rw [if_neg h] at hv; cases hv; exact absurd rfl nz
    have e10 := (frame 10 (by decide)).trans h10
    have e0 := (frame 0 (by decide)).trans h0
    -- One digest, read from the padding area, which no earlier copy wrote.
    have c := copy32_runs (m := m) (sp := sp) (mem := mm)
      (fun _ => eval_add (eval_var e0) (eval_mul (eval_lit 32) (eval_var h9')))
      (fun _ => eval_add (eval_add (eval_var e10) (eval_lit 1024)) (eval_mul (eval_lit 32) (eval_var h9')))
      (access_sub outAcc (by omega) (by omega)) (access_sub acc (by omega) (by omega)) (by simp only [Apart]; omega)
    refine Ends.of_runs (Runs.block_append c (incr_runs h9'))
      ⟨⟨fun y hy => ?_, j + 1, by omega, assign_eq, fun a ha => ?_, fun p hp q hq => ?_⟩, ?_⟩
    · rw [assign_ne hy]; exact frame y hy
    · rw [copied_out (by omega)]
      exact outside a (by omega)
    · by_cases old : p < j
      · rw [copied_out (by omega)]
        exact copiedSoFar p old q hq
      · have pj : p = j := by omega
        subst pj
        rw [copied_in _ _ _ _ _ hq]
        exact outside _ (by omega)
    · simp only [assign_eq, h9']
      rw [index_toNat (show j + 1 ≤ count by omega) (by omega), index_toNat hj (by omega)]
      omega
  · rintro e mm ⟨⟨frame, j, hj, h9', outside, copiedAll⟩, done⟩
    rw [eval_lt (eval_var h9') (eval_var ((frame 3 (by decide)).trans h3)) (by omega) (by omega)] at done
    have all : count ≤ j := by
      by_cases h : j < count
      · rw [if_pos h] at done; cases done
      · omega
    have jc : j = count := by omega
    subst jc
    exact ⟨frame, outside, copiedAll⟩

/--
The last pairs, fewer than a batch of at most sixteen, hashed through one padded batch.

The result stays zero, and every byte outside the padding area is as after hashing the whole run.
-/
theorem padded_ends {m : Module} {w : World} {sp : Nat} {e1 : Env} {mem : Memory}
    {ls rs o l r c x tb pd : Nat} {mask : UInt64} {k batch : Nat} {name : String} {ext : Extern} {code : Array Instr}
    (pre : RunPre w mem ls rs o l r c x tb pd mask) (at1 : At e1 ls rs o l r c x tb mask k) (small : c - k < batch)
    (fits : batch ≤ 16) (at_ : KernelAt m name ext) (answers : Answers w sp ext code batch 64 64)
    (room : w.stackLo + 8 ≤ sp) (runs : w.cpu.runs code = true) :
    Ends m w sp e1 (hashed mem o l r k ls rs) (.block (padded name ls rs)) fun env mem' =>
      env 8 = 0 ∧ ∀ a, ¬ (pd ≤ a ∧ a < pd + 1536) → mem' a = hashed mem o l r c ls rs a := by
  have pp := pre.pairs
  have bo := access_bound pp.outAccess
  have bt := access_bound pp.tableAccess
  have bx := access_bound pre.ctxAccess
  have bp := access_bound pre.padAccess
  have kc := at1.le
  have ab : addressBound = 2 ^ 63 := rfl
  refine Ends.cons (Ends.when _ (eval_ne (eval_var at1.count) (eval_lit 0)) (fun vc => ?_) (fun vc => ?_))
    fun _ _ h => Ends.nil h
  case refine_2 =>
    have done : c - k = 0 := (ofNat_inj (by omega) (by decide)).mp (ite_eq_zero vc)
    exact ⟨at1.status, fun a _ => by rw [show k = c by omega]⟩
  -- The last pairs, copied into one padded batch.
  have ctxOut := pre.ctxOut
  have padOut := pre.padOut
  simp only [Apart] at ctxOut padOut
  have k32 : 32 * k ≤ 32 * c := Nat.mul_le_mul_left 32 kc
  have padv : readLE (hashed mem o l r k ls rs) (x + 24) 8 = UInt64.ofNat pd := by
    rw [readLE_congr _ mem _ _ fun i hi => hashed_outside (by omega)]
    exact pre.padAt
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ ((eval_ld (eval_add (eval_var at1.ctx) (eval_lit 24))
    (access_sub pre.ctxAccess (by omega) (by omega))).trans (congrArg some padv))) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 0)) ?_
  have p2 := (assign_ne (env := assign e1 10 (UInt64.ofNat pd)) (v := UInt64.ofNat 0)
    (by decide : (10 : Nat) ≠ 9)).trans assign_eq
  have k2 : ∀ y, y ≠ 9 → y ≠ 10 →
      assign (assign e1 10 (UInt64.ofNat pd)) 9 (UInt64.ofNat 0) y = e1 y := fun y a b =>
    (assign_ne a).trans (assign_ne b)
  refine Ends.cons (copyIn_loop (ls := ls) (rs := rs) (left := l + ls * k) (right := r + rs * k) (count := c - k)
    pre.padAccess p2 assign_eq ((k2 1 (by decide) (by decide)).trans at1.left)
    ((k2 2 (by decide) (by decide)).trans at1.right) ((k2 3 (by decide) (by decide)).trans at1.count) (by omega)
    (fun p hp => by
      have := pp.inputsAccess (k + p) (by omega)
      rwa [Nat.mul_add, Nat.mul_add, ← Nat.add_assoc, ← Nat.add_assoc] at this)
    (fun p hp => by
      have := pre.padInputs (k + p) (by omega)
      rwa [Nat.mul_add, Nat.mul_add, ← Nat.add_assoc, ← Nat.add_assoc] at this)) ?_
  rintro e5 m5 ⟨fr5, out5, pairs5⟩
  have k5 : ∀ y, y ≠ 9 → y ≠ 10 → e5 y = e1 y := fun y a b => (fr5 y a).trans (k2 y a b)
  have p5 : e5 10 = UInt64.ofNat pd := (fr5 10 (by decide)).trans p2
  -- The padded batch meets the kernel's conditions.
  have preB : HashPre w m5 (pd + 1024) pd (pd + 32) batch 64 64 tb := by
    have ta := pre.padTable
    have pt := pp.tableApart
    simp only [Apart] at ta pt
    refine ⟨fun i hi => ?_, access_sub pre.padAccess (by omega) (by omega), pp.tableAccess,
      fun p hp => ⟨access_sub pre.padAccess (by omega) (by omega), access_sub pre.padAccess (by omega) (by omega)⟩,
      ⟨by omega, by omega⟩, by simp only [Apart]; omega,
      fun p hp => ⟨by simp only [Apart]; omega, by simp only [Apart]; omega⟩⟩
    rw [out5 _ (by omega), hashed_outside (by omega)]
    exact pp.tableAt i hi
  have hv : [Expr.var 10 + 1024, Expr.var 10, Expr.var 10 + 32, (1 : Expr), Expr.var 6].mapM (eval w e5 m5) =
      some [UInt64.ofNat (pd + 1024 + 32 * 0), UInt64.ofNat (pd + 64 * 0), UInt64.ofNat (pd + 32 + 64 * 0),
        UInt64.ofNat 1, UInt64.ofNat tb] := by
    simp only [Nat.mul_zero, Nat.add_zero]
    exact eval_five (eval_add (eval_var p5) (eval_lit 1024)) (eval_var p5) (eval_add (eval_var p5) (eval_lit 32))
      (eval_lit 1) (eval_var ((k5 6 (by decide) (by decide)).trans at1.table))
  refine Ends.step (kernel_runs preB (k := 0) (q := 1) (by omega) (hashed_zero _ _ _ _ _ _).symm at_ answers room
    runs hv (by omega)) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _ (eval_lit 0)) ?_
  have k7 : ∀ y, y ≠ 9 → y ≠ 10 → assign (assign e5 9 0) 9 (UInt64.ofNat 0) y = e1 y := fun y a b =>
    (assign_ne a).trans ((assign_ne a).trans (k5 y a b))
  have p7 : assign (assign e5 9 0) 9 (UInt64.ofNat 0) 10 = UInt64.ofNat pd :=
    (assign_ne (by decide)).trans ((assign_ne (by decide)).trans p5)
  refine Ends.cons (copyOut_loop (out := o + 32 * k) (count := c - k) pre.padAccess p7 assign_eq
    ((k7 0 (by decide) (by decide)).trans at1.out) ((k7 3 (by decide) (by decide)).trans at1.count) (by omega)
    (access_sub pp.outAccess (by omega) (by omega)) (by simp only [Apart]; omega)) ?_
  rintro e8 m8 ⟨fr8, out8, digests8⟩
  refine Ends.nil ⟨(fr8 8 (by decide)).trans ((k7 8 (by decide) (by decide)).trans at1.status), fun a ha => ?_⟩
  -- Hashing the whole run is hashing the first pairs, then the last ones.
  have whole := hashed_append mem o l r k (c - k) ls rs
    (by rw [show k + (c - k) = c by omega]; exact pp.inputsApart)
  rw [show k + (c - k) = c by omega] at whole
  rw [← whole]
  by_cases inside : o + 32 * k ≤ a ∧ a < o + 32 * k + 32 * (c - k)
  · -- A digest: the kernel hashed copies of the same two nodes.
    obtain ⟨p, q, hp, hq, rfl⟩ : ∃ p q, p < c - k ∧ q < 32 ∧ a = o + 32 * k + 32 * p + q :=
      ⟨(a - (o + 32 * k)) / 32, (a - (o + 32 * k)) % 32, by omega, by omega, by omega⟩
    rw [digests8 p hp q hq, hashed_inside hp hq, show pd + 1024 + 32 * p + q = pd + 1024 + 32 * p + q from rfl,
      hashed_inside (show p < 0 + batch * 1 by omega) hq]
    rw [pairMessage_eq m5 (hashed mem o l r k ls rs) _ _ (l + ls * k + ls * p) (r + rs * k + rs * p)
      (fun i hi => (pairs5 p hp i hi).1)
      (fun i hi => by rw [show pd + 32 + 64 * p + i = pd + 64 * p + 32 + i by omega]; exact (pairs5 p hp i hi).2)]
  · -- Any other byte outside the padding area is as the first pairs left it.
    rw [out8 a inside, hashed_outside (by omega), out5 a ha, hashed_outside inside]

/-! ## The whole run -/

set_option maxHeartbeats 1000000 in
/--
A hashing run ends with every digest written and a zero result, whatever kernels the processor has.

Every byte outside the padding area is as after hashing the whole run.
-/
theorem hashRun_ends {layout : Layout} {suffix : String} {ls rs : Nat} (hi : layout.info = (suffix, ls, rs))
    {m : Module} {w : World} {sp : Nat} {mem : Memory} {o l r c x tb pd : Nat} {mask : UInt64}
    (mod : HashModule m) (pre : RunPre w mem ls rs o l r c x tb pd mask) (kernels : KernelsRun w mask)
    (room : w.stackLo + 8 + Kernel.Avx512x2.frame ≤ sp) :
    Ends m w sp (entryEnv [UInt64.ofNat o, UInt64.ofNat l, UInt64.ofNat r, UInt64.ofNat c, UInt64.ofNat x]) mem
      (hashRun layout).body fun env mem' =>
        env 8 = 0 ∧ ∀ a, ¬ (pd ≤ a ∧ a < pd + 1536) → mem' a = hashed mem o l r c ls rs a := by
  -- The kernels the run calls, for its layout.
  have kX : KernelAt m (kernelName "avx512x2" suffix)
      (hashFrameExtern (Kernel.Avx512x2.program ls rs) 32 ls rs Kernel.Avx512x2.frame) := by
    have := mod.avx512x2 layout; rwa [hi] at this
  have kA : KernelAt m (kernelName "avx512" suffix) (hashExtern (Kernel.Avx512.program ls rs) 16 ls rs) := by
    have := mod.avx512 layout; rwa [hi] at this
  have kS : KernelAt m (kernelName "shani" suffix) (hashExtern (Kernel.ShaNi.program ls rs) 1 ls rs) := by
    have := mod.shani layout; rwa [hi] at this
  have kD : KernelAt m (kernelName "shani_dual" suffix) (hashExtern (Kernel.ShaNiDual.program ls rs) 2 ls rs) := by
    have := mod.shaniDual layout; rwa [hi] at this
  have kV : KernelAt m (kernelName "avx2" suffix)
      (hashFrameExtern (Kernel.Avx2.program ls rs) 8 ls rs Kernel.Avx2.frame) := by
    have := mod.avx2 layout; rwa [hi] at this
  have kB : KernelAt m (kernelName "baseline" suffix)
      (hashFrameExtern (Kernel.Baseline.program ls rs) 4 ls rs Kernel.Baseline.frame) := by
    have := mod.baseline layout; rwa [hi] at this
  have kP := mod.avx512 .pairs
  have kQ := mod.avx2 .pairs
  have kR := mod.baseline .pairs
  -- The scratch areas fit below the stack pointer.
  have fX : Kernel.Avx512x2.frame = 10240 := rfl
  have fV : Kernel.Avx2.frame = 2560 := rfl
  have fB : Kernel.Baseline.frame = 1280 := rfl
  -- Every address and count fits in a word.
  have pp := pre.pairs
  have bo := access_bound pp.outAccess
  have bt := access_bound pp.tableAccess
  have bx := access_bound pre.ctxAccess
  simp only [hashRun, hi]
  -- The context's mask and table, and a zero result so far.
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _
    (by exact eval_ld (eval_var rfl) (access_sub pre.ctxAccess (Nat.le_refl _) (by omega)))) ?_
  refine Ends.step (Runs.set _ _ _ _ _ _ _ _
    (by exact eval_ld (eval_add (eval_var rfl) (eval_lit 8)) (access_sub pre.ctxAccess (by omega) (by omega)))) ?_
  refine Ends.cons (Q := fun e mm => At e ls rs o l r c x tb mask 0 ∧ mm = mem)
    (Ends.of_runs (Runs.set _ _ _ _ _ _ _ _ rfl)
      ⟨⟨Nat.zero_le _, rfl, rfl, rfl, rfl, rfl, pre.maskAt, pre.tableAt, rfl⟩, rfl⟩) ?_
  rintro e0 m0 ⟨at0, hm0⟩
  subst m0
  -- Whole batches of thirty-two, then of sixteen, when the processor has the AVX-512 kernels.
  refine Ends.cons (Q := fun e mm => ∃ k, At e ls rs o l r c x tb mask k ∧ mm = hashed mem o l r k ls rs ∧
    (mask &&& 2 ≠ 0 → c - k < 16) ∧ (mask &&& 2 = 0 → k = 0)) ?_ ?_
  · refine Ends.when _ (eval_ne (eval_and (eval_var at0.mask) (eval_lit 2)) (eval_lit 0)) (fun v2 => ?_)
      fun v2 => ⟨0, at0, (hashed_zero _ _ _ _ _ _).symm, fun h => absurd (ite_eq_zero v2) h, fun _ => rfl⟩
    have m2 : mask &&& 2 ≠ 0 := ite_ne_zero v2
    obtain ⟨runs16, runs32⟩ := kernels.1 m2 ls rs
    have first := batches_ends (k := 0) (j := 5) (batch := 32) pp at0 rfl (by decide) kX
      (answers_frame (by omega)) (by omega) runs32
    rw [hashed_zero] at first
    refine Ends.append first fun e mm ⟨ate, hm⟩ => ?_
    subst hm
    exact Ends.mono (batches_ends (j := 4) (batch := 16) pp ate rfl (by decide) kA answers_hash (by omega) runs16)
      fun _ _ ⟨at', hm'⟩ => ⟨_, at', hm', fun _ => by omega, fun h => absurd h m2⟩
  rintro e1 m1 ⟨k, at1, rfl, lt16, zero⟩
  have kc := at1.le
  refine Ends.cons (Ends.ite _ (eval_ne (eval_and (eval_var at1.mask) (eval_lit 1)) (eval_lit 0))
    (fun v1 => ?_) (fun v1 => ?_)) fun _ _ h => Ends.nil h
  · -- Pairs two at a time, then a last one, when the processor has the SHA instructions.
    have m1 : mask &&& 1 ≠ 0 := ite_ne_zero v1
    obtain ⟨runsS, runsD⟩ := kernels.2.1 m1 ls rs
    refine Ends.append (Q := fun e mm => ∃ k', At e ls rs o l r c x tb mask k' ∧
        mm = hashed mem o l r k' ls rs ∧ c - k' < 2)
      (Ends.mono (batches_ends (j := 1) (batch := 2) pp at1 rfl (by decide) kD answers_hash (by omega) runsD)
        fun _ _ ⟨at', hm'⟩ => ⟨_, at', hm', by omega⟩) ?_
    rintro e mm ⟨k', at', rfl, lt2⟩
    have kc' := at'.le
    refine Ends.cons (Ends.when _ (eval_ne (eval_var at'.count) (eval_lit 0)) (fun v => ?_) (fun v => ?_))
      fun _ _ h => Ends.nil h
    · exact Ends.of_runs (kernel_runs pp (k := k') (q := c - k') (by omega) rfl kS answers_hash (by omega) runsS
        (eval_five (eval_var at'.out) (eval_var at'.left) (eval_var at'.right) (eval_var at'.count)
          (eval_var at'.table)) (by omega))
        ⟨(assign_ne (by decide : (8 : Nat) ≠ 9)).trans at'.status, fun a _ => by
          rw [show k' + 1 * (c - k') = c by omega]⟩
    · have done : c - k' = 0 := (ofNat_inj (by omega) (by decide)).mp (ite_eq_zero v)
      exact ⟨at'.status, fun a _ => by rw [show k' = c by omega]⟩
  have m1 : mask &&& 1 = 0 := ite_eq_zero v1
  refine Ends.cons (Ends.ite _ (eval_ne (eval_and (eval_var at1.mask) (eval_lit 2)) (eval_lit 0))
    (fun v2 => ?_) (fun v2 => ?_)) fun _ _ h => Ends.nil h
  · -- One padded batch of sixteen for the sixteen-lane kernel.
    have m2 : mask &&& 2 ≠ 0 := ite_ne_zero v2
    exact padded_ends pre at1 (lt16 m2) (by decide) kP answers_hash (by omega) (kernels.1 m2 64 64).1
  have m2 : mask &&& 2 = 0 := ite_eq_zero v2
  have k0 := zero m2
  subst k0
  refine Ends.cons (Ends.ite _ (eval_ne (eval_and (eval_var at1.mask) (eval_lit 8)) (eval_lit 0))
    (fun v8 => ?_) (fun v8 => ?_)) fun _ _ h => Ends.nil h
  · -- Whole batches of eight, then one padded batch, for the AVX2 kernel.
    have m8 : mask &&& 8 ≠ 0 := ite_ne_zero v8
    refine Ends.append (Q := fun e mm => ∃ k', At e ls rs o l r c x tb mask k' ∧
        mm = hashed mem o l r k' ls rs ∧ c - k' < 8)
      (Ends.mono (batches_ends (j := 3) (batch := 8) pp at1 rfl (by decide) kV (answers_frame (by omega)) (by omega)
        (kernels.2.2 m8 ls rs)) fun _ _ ⟨at', hm'⟩ => ⟨_, at', hm', by omega⟩) ?_
    rintro e mm ⟨k', at', rfl, lt8⟩
    exact padded_ends pre at' lt8 (by decide) kQ (answers_frame (by omega)) (by omega) (kernels.2.2 m8 64 64)
  · -- Whole batches of four, then one padded batch, for the SSE2 kernel every processor runs.
    refine Ends.append (Q := fun e mm => ∃ k', At e ls rs o l r c x tb mask k' ∧
        mm = hashed mem o l r k' ls rs ∧ c - k' < 4)
      (Ends.mono (batches_ends (j := 2) (batch := 4) pp at1 rfl (by decide) kB (answers_frame (by omega)) (by omega)
        (Kernel.runs_baseline w.cpu ls rs)) fun _ _ ⟨at', hm'⟩ => ⟨_, at', hm', by omega⟩) ?_
    rintro e mm ⟨k', at', rfl, lt4⟩
    exact padded_ends pre at' lt4 (by decide) kR (answers_frame (by omega)) (by omega)
      (Kernel.runs_baseline w.cpu 64 64)

/-! ## Calls -/

/-- A hashing driver's frame holds seventeen words. -/
theorem hashRun_frame (layout : Layout) : (hashRun layout).frame = 17 := by
  cases layout <;> rfl

/--
The stack a call to a hashing driver needs below its stack pointer.

The driver's return address and frame take 144 bytes, a kernel's return address 8 more,
and the thirty-two-lane kernel's scratch, the largest, 10240 more.
-/
abbrev hashStack : Nat := 10392

/-- What a call to a hashing driver does, for every run meeting its conditions, on a processor running its kernels. -/
def HashCalls (m : Module) (w : World) (layout : Layout) : Prop :=
  ∀ (sp : Nat) (mem : Memory) (out left right count ctx table pad : Nat) (mask : UInt64),
    RunPre w mem layout.info.2.1 layout.info.2.2 out left right count ctx table pad mask → KernelsRun w mask →
    w.stackLo + hashStack ≤ sp →
    ∃ mem', Calls m w layout.name sp [UInt64.ofNat out, UInt64.ofNat left, UInt64.ofNat right,
      UInt64.ofNat count, UInt64.ofNat ctx] mem 0 mem' ∧
      ∀ a, ¬ (pad ≤ a ∧ a < pad + 1536) →
        mem' a = hashed mem out left right count layout.info.2.1 layout.info.2.2 a

/--
Each hashing driver of a module holding them and their kernels does what its call promises.

It returns zero having hashed the whole run, on every processor: the SSE2 kernel is the last resort.
-/
theorem hashCalls {m : Module} (w : World) (mod : HashModule m) (layout : Layout) : HashCalls m w layout := by
  intro sp mem o l r c x tb pd mask pre kernels room
  have frame := hashRun_frame layout
  have stack : hashStack = 10392 := rfl
  have fX : Kernel.Avx512x2.frame = 10240 := rfl
  -- The body runs below the driver's frame, where a kernel still finds room for its return address and scratch.
  obtain ⟨env', mem', run, status, post⟩ := hashRun_ends
    (rfl : layout.info = (layout.info.1, layout.info.2.1, layout.info.2.2))
    (sp := sp - 8 - 8 * (hashRun layout).frame) mod pre kernels (by rw [frame]; omega)
  have call : Calls m w layout.name sp [UInt64.ofNat o, UInt64.ofNat l, UInt64.ofNat r, UInt64.ofNat c,
      UInt64.ofNat x] mem (env' 8) mem' :=
    Calls.fn (mod.drivers layout) (by rw [frame]; omega) (by cases layout <;> rfl) run (eval_var rfl)
  rw [status] at call
  exact ⟨mem', call, post⟩

end Ssz.Native.Driver

namespace Ssz.Native.Driver

open Ssz.Native.Asm Ssz.Native.Ir

/-- The mask the detection routine returns lets the dispatcher call every kernel it chooses. -/
theorem kernelsRun_featureMask (w : World) : KernelsRun w w.cpu.featureMask :=
  ⟨fun bit ls rs => Kernel.runs_of_mask_avx512 w.cpu ls rs bit,
    fun bit ls rs => Kernel.runs_of_mask_shani w.cpu ls rs bit,
    fun bit ls rs => Kernel.runs_of_mask_avx2 w.cpu ls rs bit⟩

end Ssz.Native.Driver
