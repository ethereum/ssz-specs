import EthLib.Consensus.Proofs.Ssz.Merkle.ClaimChecks
import SszNative.Driver.Branch
import SszNative.Proofs.Ir.Logic
import SszNative.Proofs.Verify
import SszNative.Proofs.Asm.Spec

/-!
Facts every branch driver's proof leans on: words and nodes read from memory, sums of addresses that do not wrap,
and the small search and comparison functions.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.BranchProof

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm

/-- The 32 bytes from an address, as a node. -/
def readNode (mem : Memory) (a : Nat) : ByteArray :=
  ⟨Array.ofFn (n := 32) fun i => mem (a + i.val)⟩

/-- A node read from memory is 32 bytes. -/
theorem readNode_size (mem : Memory) (a : Nat) : (readNode mem a).size = 32 := by
  simp [readNode, ByteArray.size]

/-- Memories agreeing on a node's bytes read the same node. -/
theorem readNode_congr {mem mem' : Memory} {a : Nat} (h : ∀ i < 32, mem' (a + i) = mem (a + i)) :
    readNode mem' a = readNode mem a := by
  simp only [readNode]
  congr 2
  funext i
  exact h i.val i.isLt

/-- Nodes 32 bytes apart from an address, as a list. -/
def nodesAt (mem : Memory) (a n : Nat) : List ByteArray :=
  (List.range n).map fun j => readNode mem (a + 32 * j)

/-- A pair read from memory is the two nodes read there, one after the other. -/
theorem pairMessage_readNode (mem : Memory) (l r : Nat) :
    pairMessage mem l r = ⟨(readNode mem l).data ++ (readNode mem r).data⟩ := by
  apply ByteArray.ext
  apply Array.ext
  · simp [pairMessage, readNode]
  · intro i h₁ h₂
    have bound : i < 64 := by simpa [pairMessage] using h₁
    simp only [pairMessage, Array.getElem_ofFn]
    by_cases first : i < 32
    · rw [ite_eq_left first, Array.getElem_append_left (by simp [readNode]; omega)]
      simp [readNode]
    · rw [ite_eq_right first, Array.getElem_append_right (by simp [readNode]; omega)]
      simp [readNode]

/-- Two nodes read from memory join into the digest of the pair there. -/
theorem combine_readNode (mem : Memory) (l r : Nat) :
    combine (readNode mem l) (readNode mem r) = Cryptography.Hash.Sha256.hash (pairMessage mem l r) := by
  apply ByteArray.ext
  rw [combine_eq, pairMessage_readNode]
  rfl

/-- Words 8 bytes apart from an address, as numbers. -/
def wordsAt (mem : Memory) (a n : Nat) : List Nat :=
  (List.range n).map fun j => (readLE mem (a + 8 * j) 8).toNat

/-- Words read from memory, as many as asked. -/
theorem wordsAt_length (mem : Memory) (a n : Nat) : (wordsAt mem a n).length = n := by
  simp [wordsAt]

/-- The word at a position is the one read there. -/
theorem wordsAt_getElem (mem : Memory) (a n j : Nat) (h : j < (wordsAt mem a n).length) :
    (wordsAt mem a n)[j] = (readLE mem (a + 8 * j) 8).toNat := by
  simp [wordsAt]

/-- One more word is the words so far, then the next one. -/
theorem wordsAt_succ (mem : Memory) (a n : Nat) :
    wordsAt mem a (n + 1) = wordsAt mem a n ++ [(readLE mem (a + 8 * n) 8).toNat] := by
  simp [wordsAt, List.range_succ]

/-- The first words are a prefix of the words. -/
theorem wordsAt_take (mem : Memory) (a n i : Nat) (h : i ≤ n) : (wordsAt mem a n).take i = wordsAt mem a i := by
  simp only [wordsAt, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- Memories agreeing on the words' bytes read the same words. -/
theorem wordsAt_congr {mem mem' : Memory} {a n : Nat} (h : ∀ k < 8 * n, mem' (a + k) = mem (a + k)) :
    wordsAt mem' a n = wordsAt mem a n := by
  simp only [wordsAt]
  apply List.map_congr_left
  intro j hj
  have hj := List.mem_range.mp hj
  rw [readLE_congr mem' mem (a + 8 * j) 8 (fun k hk => by
    rw [Nat.add_assoc]; exact h _ (by omega))]

/-- A store leaves every address outside its bytes alone. -/
theorem store_outside (mem : Memory) (x n : Nat) (f : Nat → UInt8) (b : Nat) (h : ¬ (x ≤ b ∧ b < x + n)) :
    store mem x n f b = mem b := by
  simp [store, h]

/-- A word stored right after some words extends them by its value. -/
theorem wordsAt_store_end (mem : Memory) (a n : Nat) (v : UInt64) :
    wordsAt (store mem (a + 8 * n) 8 (qwordByte v)) a (n + 1) = wordsAt mem a n ++ [v.toNat] := by
  rw [wordsAt_succ, readLE_store8, wordsAt_congr (fun k hk => store_outside _ _ _ _ _ (by omega))]

/-- Two nodes read from memory are equal when their bytes agree one for one. -/
theorem readNode_ext {mem mem' : Memory} {a b : Nat} (h : ∀ i < 32, mem (a + i) = mem' (b + i)) :
    readNode mem a = readNode mem' b := by
  simp only [readNode]
  congr 2
  funext i
  exact h i.val i.isLt

/-- A sum below the word size does not wrap. -/
theorem toNat_add_of_lt (a b : UInt64) (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt h]

/-- A product below the word size does not wrap. -/
theorem toNat_mul_of_lt (a b : UInt64) (h : a.toNat * b.toNat < 2 ^ 64) : (a * b).toNat = a.toNat * b.toNat := by
  rw [UInt64.toNat_mul, Nat.mod_eq_of_lt h]

/-- A small number keeps its value as a word. -/
theorem toNat_ofNat_of_lt (n : Nat) (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- The low bit of a word is its value's parity. -/
theorem toNat_and_one (a : UInt64) : (a &&& 1).toNat = a.toNat % 2 := by
  rw [UInt64.toNat_and]
  exact Nat.and_one_is_mod a.toNat

/-- Halving a word is halving its value. -/
theorem toNat_shr_one (a : UInt64) : (a >>> (1 : Nat).toUInt64).toNat = a.toNat / 2 := by
  rw [UInt64.toNat_shiftRight]
  simp [Nat.shiftRight_eq_div_pow]

/-- An address plus a scaled offset below the word size does not wrap. -/
theorem toNat_addr (a b c : UInt64) (h : a.toNat + b.toNat * c.toNat < 2 ^ 64) :
    (a + b * c).toNat = a.toNat + b.toNat * c.toNat := by
  have product := toNat_mul_of_lt b c (by omega)
  rw [toNat_add_of_lt _ _ (by omega), product]

/-- Memory a program may use lies below the address bound. -/
theorem access_bound {w : World} {a n : Nat} (h : w.access a n = true) : a + n ≤ 2 ^ 63 := by
  simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- An address range a program may use, read back as a smaller range inside it. -/
theorem access_sub {w : World} {a n k j : Nat} (h : w.access a n = true) (le : k + j ≤ n) :
    w.access (a + k) j = true := by
  simp only [World.access, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h ⊢
  omega

/-- A usable range's first bytes are usable. -/
theorem access_prefix {w : World} {a n j : Nat} (h : w.access a n = true) (le : j ≤ n) : w.access a j = true := by
  simpa using access_sub (k := 0) h (by omega)

/-- The level of a 64-bit index is below 64. -/
theorem log2_lt_64 (x : UInt64) : Nat.log2 x.toNat < 64 := by
  have := Nat.log2_lt (n := x.toNat) (k := 64)
  by_cases zero : x.toNat = 0
  · rw [zero, log2_small 0 (by omega)]; omega
  · exact (this zero).2 x.toNat_lt

/-- A statement runs from a state to some state where a condition holds. -/
def Wp (m : Module) (w : World) (sp : Nat) (s : Stmt) (env : Env) (mem : Memory) (Q : Env → Memory → Prop) :
    Prop :=
  ∃ env' mem', Runs m w sp env mem s env' mem' ∧ Q env' mem'

/-- Doing nothing reaches a condition that already holds. -/
theorem Wp.skip {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {Q : Env → Memory → Prop}
    (h : Q env mem) : Wp m w sp .skip env mem Q :=
  ⟨env, mem, Runs.skip m w sp env mem, h⟩

/-- An empty block reaches a condition that already holds. -/
theorem Wp.nil {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {Q : Env → Memory → Prop}
    (h : Q env mem) : Wp m w sp (.block []) env mem Q :=
  Wp.skip h

/-- A block reaches a condition when its first statement reaches a state from which the rest reach it. -/
theorem Wp.cons {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {Q : Env → Memory → Prop}
    {s : Stmt} {rest : List Stmt} (h : Wp m w sp s env mem fun env mem => Wp m w sp (.block rest) env mem Q) :
    Wp m w sp (.block (s :: rest)) env mem Q := by
  obtain ⟨env₁, mem₁, r₁, env₂, mem₂, r₂, q⟩ := h
  exact ⟨env₂, mem₂, Runs.block_cons r₁ r₂, q⟩

/-- A block of two or more statements runs its first, then the rest. -/
theorem Runs.block_split {m : Module} {w : World} {sp : Nat} {env env' : Env} {mem mem' : Memory} {s t : Stmt}
    {tail : List Stmt} (h : Runs m w sp env mem (.block (s :: t :: tail)) env' mem') :
    ∃ env₁ mem₁, Runs m w sp env mem s env₁ mem₁ ∧ Runs m w sp env₁ mem₁ (.block (t :: tail)) env' mem' := by
  obtain ⟨fuel, e⟩ := h
  cases fuel with
  | zero => simp [Ir.exec] at e
  | succ f =>
    -- The block is a sequence, which runs its first statement with one less fuel.
    cases ea : Ir.exec m w f sp env mem s with
    | none => simp [Stmt.block, Ir.exec, ea] at e
    | some r =>
      simp only [Stmt.block, Ir.exec, ea, bind, Option.bind] at e
      exact ⟨r.1, r.2, ⟨f, ea⟩, ⟨f, e⟩⟩

/-- Two blocks one after the other reach what the second reaches from where the first ends. -/
theorem Wp.append {m : Module} {w : World} {sp : Nat} {Q : Env → Memory → Prop} :
    ∀ {first rest : List Stmt} {env : Env} {mem : Memory},
      Wp m w sp (.block first) env mem (fun env mem => Wp m w sp (.block rest) env mem Q) →
      Wp m w sp (.block (first ++ rest)) env mem Q
  | [], _, env, mem, h => by
    obtain ⟨env₁, mem₁, ⟨fuel, e⟩, q⟩ := h
    -- An empty block changes nothing.
    cases fuel with
    | zero => simp [Ir.exec] at e
    | succ f =>
      simp only [Stmt.block, Ir.exec, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact q
  | [s], rest, env, mem, h => by
    -- A one-statement block is that statement.
    obtain ⟨env₁, mem₁, r₁, q⟩ := h
    exact Wp.cons ⟨env₁, mem₁, r₁, q⟩
  | s :: t :: tail, rest, env, mem, h => by
    obtain ⟨env₂, mem₂, r, q⟩ := h
    obtain ⟨env₁, mem₁, r₁, r₂⟩ := Runs.block_split r
    exact Wp.cons ⟨env₁, mem₁, r₁, Wp.append ⟨env₂, mem₂, r₂, q⟩⟩

/-- An assignment reaches a condition that holds of the new variables. -/
theorem Wp.set {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {Q : Env → Memory → Prop}
    {x : Nat} {e : Ir.Expr} {v : UInt64} (he : eval w env mem e = some v) (h : Q (assign env x v) mem) :
    Wp m w sp (.set x e) env mem Q :=
  ⟨_, _, Runs.set m w sp env mem x e v he, h⟩

/-- A store reaches a condition that holds of the memory with its bytes written. -/
theorem Wp.store {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {Q : Env → Memory → Prop}
    {wd : Width} {a v : Ir.Expr} {x y : UInt64} (ha : eval w env mem a = some x) (hv : eval w env mem v = some y)
    (ok : w.access x.toNat wd.bytes = true) (h : Q env (store mem x.toNat wd.bytes (qwordByte y))) :
    Wp m w sp (.store wd a v) env mem Q :=
  ⟨_, _, Runs.store m w sp env mem wd a v x y ha hv ok, h⟩

/-- A branch reaches a condition its taken side reaches. -/
theorem Wp.ite {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {Q : Env → Memory → Prop}
    {c : Ir.Expr} {t e : Stmt} {v : UInt64} (hc : eval w env mem c = some v)
    (ht : v ≠ 0 → Wp m w sp t env mem Q) (he : v = 0 → Wp m w sp e env mem Q) :
    Wp m w sp (.ite c t e) env mem Q := by
  by_cases zero : v = 0
  · subst zero
    obtain ⟨env', mem', r, q⟩ := he rfl
    exact ⟨env', mem', Runs.ite_false hc r, q⟩
  · obtain ⟨env', mem', r, q⟩ := ht zero
    exact ⟨env', mem', Runs.ite_true v hc zero r, q⟩

/-- A call reaches a condition that holds of every result and memory the call may leave. -/
theorem Wp.call {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {Q : Env → Memory → Prop}
    {f : String} {args : List Ir.Expr} {dst : Nat} {values : List UInt64}
    (hv : args.mapM (eval w env mem) = some values)
    (h : ∃ r mem', Calls m w f sp values mem r mem' ∧ Q (assign env dst r) mem') :
    Wp m w sp (.call f args dst) env mem Q := by
  obtain ⟨r, mem', c, q⟩ := h
  exact ⟨_, _, Runs.call hv c, q⟩

/--
A loop reaches a condition when an invariant holds on entry, every pass keeps it while a measure falls, and the
condition holds wherever the invariant holds and the loop's test is zero.
-/
theorem Wp.loop {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {Q : Env → Memory → Prop}
    {c : Ir.Expr} {body : Stmt} (inv : Env → Memory → Prop) (measure : Env → Memory → Nat) (h0 : inv env mem)
    (step : ∀ env mem, inv env mem → ∃ v, eval w env mem c = some v ∧
      (v ≠ 0 → Wp m w sp body env mem fun env' mem' => inv env' mem' ∧ measure env' mem' < measure env mem) ∧
      (v = 0 → Q env mem)) :
    Wp m w sp (.loop c body) env mem Q := by
  obtain ⟨env', mem', r, i, done⟩ := Runs.loop_inv (m := m) (w := w) (sp := sp) (c := c) (body := body) inv measure
    (fun env mem hi => by obtain ⟨v, hv, _⟩ := step env mem hi; exact ⟨v, hv⟩)
    (fun env mem v hi hv nz => by
      obtain ⟨v', hv', pass, _⟩ := step env mem hi
      rw [hv] at hv'
      obtain ⟨env', mem', r, q⟩ := pass (by rw [← Option.some.inj hv']; exact nz)
      exact ⟨env', mem', r, q⟩)
    env mem h0
  obtain ⟨v, hv, _, exit⟩ := step env' mem' i
  rw [done] at hv
  exact ⟨env', mem', r, exit (Option.some.inj hv).symm⟩

/-- A condition weakens along an implication. -/
theorem Wp.mono {m : Module} {w : World} {sp : Nat} {s : Stmt} {env : Env} {mem : Memory}
    {P Q : Env → Memory → Prop} (h : Wp m w sp s env mem P) (imp : ∀ env mem, P env mem → Q env mem) :
    Wp m w sp s env mem Q := by
  obtain ⟨env', mem', r, p⟩ := h
  exact ⟨env', mem', r, imp _ _ p⟩

/-- A statement reaches a condition from variables known only through a property they have. -/
theorem Wp.of_env {m : Module} {w : World} {sp : Nat} {s : Stmt} {env : Env} {mem : Memory}
    {Q : Env → Memory → Prop} (P : Env → Prop) (hp : P env) (h : ∀ env, P env → Wp m w sp s env mem Q) :
    Wp m w sp s env mem Q :=
  h env hp

/-- A function whose body reaches a result is a call returning it. -/
theorem Calls.of_wp {m : Module} {w : World} {f : String} {sp : Nat} {args : List UInt64} {mem : Memory}
    {fn : Fn} (hf : m.fns.lookup f = some fn) (room : w.stackLo + 8 + 8 * fn.frame ≤ sp)
    (count : args.length = fn.params) {Q : UInt64 → Memory → Prop}
    (h : Wp m w (sp - 8 - 8 * fn.frame) fn.body (entryEnv args) mem fun env mem' =>
      ∃ r, eval w env mem' fn.result = some r ∧ Q r mem') :
    ∃ r mem', Calls m w f sp args mem r mem' ∧ Q r mem' := by
  obtain ⟨env', mem', run, r, hr, q⟩ := h
  exact ⟨r, mem', Calls.fn hf room count run hr, q⟩

/-- A sum evaluates to the wrapped sum of its operands. -/
theorem eval_add {w : World} {env : Env} {mem : Memory} {a b : Ir.Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) : eval w env mem (a + b) = some (x + y) := by
  show eval w env mem (.op .add a b) = _
  simp [eval, ha, hb, aluResult]

/-- A difference evaluates to the wrapped difference of its operands. -/
theorem eval_sub {w : World} {env : Env} {mem : Memory} {a b : Ir.Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) : eval w env mem (a - b) = some (x - y) := by
  show eval w env mem (.op .sub a b) = _
  simp [eval, ha, hb, aluResult]

/-- A product evaluates to the wrapped product of its operands. -/
theorem eval_mul {w : World} {env : Env} {mem : Memory} {a b : Ir.Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) : eval w env mem (a * b) = some (x * y) := by
  show eval w env mem (.op .mul a b) = _
  simp [eval, ha, hb, aluResult]

/-- A bitwise and evaluates to the and of its operands. -/
theorem eval_and {w : World} {env : Env} {mem : Memory} {a b : Ir.Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (a &&& b) = some (x &&& y) := by
  show eval w env mem (.op .and a b) = _
  simp [eval, ha, hb, aluResult]

/-- A bitwise or evaluates to the or of its operands. -/
theorem eval_or {w : World} {env : Env} {mem : Memory} {a b : Ir.Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (a ||| b) = some (x ||| y) := by
  show eval w env mem (.op .or a b) = _
  simp [eval, ha, hb, aluResult]

/-- A bitwise exclusive or evaluates to the exclusive or of its operands. -/
theorem eval_xor {w : World} {env : Env} {mem : Memory} {a b : Ir.Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (a ^^^ b) = some (x ^^^ y) := by
  show eval w env mem (.op .xor a b) = _
  simp [eval, ha, hb, aluResult]

/-- A right shift by one evaluates to the halved operand. -/
theorem eval_shr1 {w : World} {env : Env} {mem : Memory} {a : Ir.Expr} {x : UInt64}
    (ha : eval w env mem a = some x) : eval w env mem (.shr a 1) = some (x >>> (1 : Nat).toUInt64) := by
  simp [eval, ha]

/-- A load of eight bytes from memory a program may use reads them. -/
theorem eval_ld {w : World} {env : Env} {mem : Memory} {a : Ir.Expr} {x : UInt64} (ha : eval w env mem a = some x)
    (acc : w.access x.toNat 8 = true) : eval w env mem (Ir.Expr.ld a) = some (readLE mem x.toNat 8) := by
  simp [Ir.Expr.ld, eval, ha, Width.bytes, acc]

/-- A load of eight bytes at a constant offset from an address reads them there. -/
theorem eval_ld_off {w : World} {env : Env} {mem : Memory} {a : Ir.Expr} {x n : UInt64}
    (ha : eval w env mem a = some x) (acc : w.access (x.toNat + n.toNat) 8 = true) :
    eval w env mem (Ir.Expr.ld (a + .lit n)) = some (readLE mem (x.toNat + n.toNat) 8) := by
  have bound := access_bound acc
  have sum : (x + n).toNat = x.toNat + n.toNat := toNat_add_of_lt _ _ (by omega)
  rw [eval_ld (eval_add ha rfl) (by rw [sum]; exact acc), sum]

/-- A load of one byte from memory a program may use reads it. -/
theorem eval_ld1 {w : World} {env : Env} {mem : Memory} {a : Ir.Expr} {x : UInt64} (ha : eval w env mem a = some x)
    (acc : w.access x.toNat 1 = true) : eval w env mem (Ir.Expr.ld1 a) = some (readLE mem x.toNat 1) := by
  simp [Ir.Expr.ld1, eval, ha, Width.bytes, acc]

/-- A comparison of two evaluated operands evaluates to one or zero. -/
theorem eval_cmp {w : World} {env : Env} {mem : Memory} {a b : Ir.Expr} {x y : UInt64} (c : Cond)
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (.cmp c a b) = some (if c.holds (x == y) (x < y) then 1 else 0) := by
  simp [eval, ha, hb]

/-- A below-comparison that holds evaluates to one. -/
theorem eval_lt_true {w : World} {env : Env} {mem : Memory} {a b : Ir.Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) (h : x.toNat < y.toNat) :
    eval w env mem (Ir.Expr.lt a b) = some 1 := by
  rw [Ir.Expr.lt, eval_cmp .b ha hb]
  simp [Cond.holds, UInt64.lt_iff_toNat_lt, h]

/-- A below-comparison that fails evaluates to zero. -/
theorem eval_lt_false {w : World} {env : Env} {mem : Memory} {a b : Ir.Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) (h : ¬ x.toNat < y.toNat) :
    eval w env mem (Ir.Expr.lt a b) = some 0 := by
  rw [Ir.Expr.lt, eval_cmp .b ha hb]
  simp [Cond.holds, UInt64.lt_iff_toNat_lt, h]

/-- A below-comparison evaluating to something other than zero held. -/
theorem lt_of_eval {w : World} {env : Env} {mem : Memory} {a b : Ir.Expr} {x y v : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y)
    (hv : eval w env mem (Ir.Expr.lt a b) = some v) (nz : v ≠ 0) : x.toNat < y.toNat := by
  by_cases h : x.toNat < y.toNat
  · exact h
  · rw [eval_lt_false ha hb h] at hv
    exact absurd (Option.some.inj hv).symm nz

/-- A below-comparison evaluating to zero failed. -/
theorem not_lt_of_eval {w : World} {env : Env} {mem : Memory} {a b : Ir.Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y)
    (hv : eval w env mem (Ir.Expr.lt a b) = some 0) : ¬ x.toNat < y.toNat := by
  intro h
  rw [eval_lt_true ha hb h] at hv
  exact absurd (Option.some.inj hv) (by decide)

/-- A below-comparison evaluates to one exactly when the first value is below the second. -/
theorem eval_lt {w : World} {env : Env} {mem : Memory} {a b : Ir.Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (Ir.Expr.lt a b) = some (if x.toNat < y.toNat then 1 else 0) := by
  by_cases h : x.toNat < y.toNat
  · rw [ite_eq_left h]; exact eval_lt_true ha hb h
  · rw [ite_eq_right h]; exact eval_lt_false ha hb h

/-- Two flags joined by a bitwise or are the flag of either holding. -/
theorem or_flags (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : UInt64) ||| (if q then 1 else 0)) = if p ∨ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] <;> decide

/-- An equality test evaluates to one exactly when the operands agree. -/
theorem eval_eq {w : World} {env : Env} {mem : Memory} {a b : Ir.Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (Ir.Expr.eq a b) = some (if x = y then 1 else 0) := by
  rw [Ir.Expr.eq, eval_cmp .e ha hb]
  by_cases h : x = y <;> simp [Cond.holds, h]

/-- A difference test evaluates to one exactly when the operands differ. -/
theorem eval_ne {w : World} {env : Env} {mem : Memory} {a b : Ir.Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (Ir.Expr.ne a b) = some (if x = y then 0 else 1) := by
  rw [Ir.Expr.ne, eval_cmp .ne ha hb]
  by_cases h : x = y <;> simp [Cond.holds, h]

end EthLib.Consensus.Ssz.Native.Driver.BranchProof
