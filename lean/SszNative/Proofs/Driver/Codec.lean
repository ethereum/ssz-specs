import SszNative.Proofs.Driver.Memory
import SszNative.Proofs.Driver.Hash
import SszNative.Driver.Codec
import SszNative.Plan
import SszNative.Proofs.Ir.Logic
import SszNative.Proofs.Asm.Bytes
import Ssz.Proofs.Codec.Admits

/-!
The codec drivers compute what their Lean references compute.

Each theorem is a call of a driver in a module holding them all, from memory holding its inputs.

    ssz_copy               copies bytes between ranges that are apart
    ssz_plan_next          lands right after a node's words, for every real type
    ssz_plan_skip          lands right after a list of nodes
    ssz_plan_width         answers a narrow real type's width, or the word for a variable size
    ssz_plan_fields_width  answers a struct's width the same way

A plan is read from memory as the words the plan format writes, and the stack the walk needs grows with nesting.
-/

namespace Ssz.Native.Driver

open Ssz.Native.Ir Ssz.Native.Asm

/-- A module holds the codec drivers under their exported names. -/
def HasCodec (m : Module) : Prop :=
  ∀ entry ∈ codecFns, m.fns.lookup entry.1 = some entry.2

/-- A byte loaded and stored back as one byte is the byte. -/
theorem qwordByte_readLE1 (mem : Memory) (a : Nat) : qwordByte (readLE mem a 1) 0 = mem a := by
  apply UInt8.toNat_inj.mp
  rw [qwordByte_toNat _ 0 (by decide), readLE_toNat _ _ _ (by decide)]
  simp [bytesNat]

/-- A natural number below the word size is unchanged by a round trip through a word. -/
theorem toNat_toUInt64 (n : Nat) (small : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  simp [Nat.toUInt64, Nat.mod_eq_of_lt small]

/-- Words whose sum fits add without wrapping. -/
theorem add_toNat (a b : UInt64) (fits : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]

/-- A small number is below a word exactly when it is below the word's value. -/
theorem ofNat_lt_iff (k : Nat) (n : UInt64) (small : k < 2 ^ 64) : UInt64.ofNat k < n ↔ k < n.toNat := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' small]

/-- A small number's word is below another's as the number is. -/
theorem ofNat_lt_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : UInt64.ofNat a < UInt64.ofNat b ↔ a < b := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (show a < UInt64.size from ha),
    UInt64.toNat_ofNat_of_lt' (show b < UInt64.size from hb)]

/-- A run of bytes loaded and stored elsewhere, from the next place of a copy, copies that many more. -/
theorem copied_more (mem : Memory) (dst src k c : Nat) (apart : src + (k + c) ≤ dst ∨ dst + (k + c) ≤ src)
    (move : store (copied mem dst src k) (dst + k) c (qwordByte (readLE (copied mem dst src k) (src + k) c)) =
      copied (copied mem dst src k) (dst + k) (src + k) c) :
    store (copied mem dst src k) (dst + k) c (qwordByte (readLE (copied mem dst src k) (src + k) c)) =
      copied mem dst src (k + c) := by
  rw [move, copied_succ _ _ _ _ _ (by simp only [Apart]; omega)]

/-- One byte loaded and stored elsewhere is copied there. -/
theorem store_load1 (mem : Memory) (dst src : Nat) :
    store mem dst 1 (qwordByte (readLE mem src 1)) = copied mem dst src 1 := by
  funext a
  simp only [store, copied]
  split
  · rw [show a - dst = 0 by omega, qwordByte_readLE1]; simp
  · rfl

set_option linter.unusedSimpArgs false in
/--
Copying bytes copies them: arguments where to, where from, how many.

The two ranges are apart, and both lie in memory the program may use.
Whole eight-byte words are copied first, then the bytes left one at a time.
-/
theorem copy_correct (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory) (dst src n : UInt64)
    (room : w.stackLo + 8 + 8 * copyBytes.frame ≤ sp)
    (readable : w.access src.toNat n.toNat) (writable : w.access dst.toNat n.toNat)
    (apart : src.toNat + n.toNat ≤ dst.toNat ∨ dst.toNat + n.toNat ≤ src.toNat) :
    Calls m w "ssz_copy" sp [dst, src, n] mem 0 (copied mem dst.toNat src.toNat n.toNat) := by
  have found : m.fns.lookup "ssz_copy" = some copyBytes := linked ("ssz_copy", copyBytes) (by simp [codecFns])
  have fitsSrc : src.toNat + n.toNat ≤ 2 ^ 63 := by
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at readable; simp [addressBound] at readable; omega
  have fitsDst : dst.toNat + n.toNat ≤ 2 ^ 63 := by
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at writable; simp [addressBound] at writable; omega
  let inner := sp - 8 - 8 * copyBytes.frame
  let args := [dst, src, n]
  let N := n.toNat
  -- The bytes the whole words cover.
  let W := N - N % 8
  have wordsEval : eval w (assign (entryEnv args) 3 0) mem (.op .sub (.var 2) (.mod (.var 2) (.lit 8))) =
      some W.toUInt64 := by
    simp only [eval, assign, entryEnv, args]
    simp [aluResult, Bind.bind, Option.bind]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]; simp; exact Nat.mod_le _ _),
      UInt64.toNat_mod, toNat_toUInt64 _ (by omega)]
    simp [W, N]
  let env₀ := assign (assign (entryEnv args) 3 0) 4 W.toUInt64
  -- After k bytes, a whole number of words, the index is k and those bytes are copied.
  let inv₁ : Env → Memory → Prop := fun env cur =>
    ∃ k, k ≤ W ∧ k % 8 = 0 ∧ env = assign env₀ 3 k.toUInt64 ∧ cur = copied mem dst.toNat src.toNat k
  have loop₁ := Runs.loop_inv (m := m) (w := w) (sp := inner) (c := Expr.lt (.var 3) (.var 4))
    (body := .block [Stmt.st (Expr.var 0 + Expr.var 3) (Expr.ld (Expr.var 1 + Expr.var 3)), .set 3 (.var 3 + 8)])
    inv₁ (fun env _ => W - (env 3).toNat)
    (fun env cur _ => ⟨_, rfl⟩)
    (by
      rintro env cur v ⟨k, within, whole, rfl, rfl⟩ cond nonzero
      have small : k < 2 ^ 64 := by omega
      -- The condition holds, so another word is left.
      have more : k < W := by
        simp only [Expr.lt, eval, assign, env₀, Cond.holds] at cond
        simp at cond
        by_cases done : k < W
        · exact done
        · simp [ofNat_lt_ofNat k W small (by omega), done] at cond
          exact absurd cond.symm nonzero
      have room8 : k + 8 ≤ W := by omega
      have addr : (dst + k.toUInt64).toNat = dst.toNat + k := by
        rw [add_toNat _ _ (by rw [toNat_toUInt64 _ small]; omega), toNat_toUInt64 _ small]
      have addrS : (src + k.toUInt64).toNat = src.toNat + k := by
        rw [add_toNat _ _ (by rw [toNat_toUInt64 _ small]; omega), toNat_toUInt64 _ small]
      have stored := Runs.store m w inner (assign env₀ 3 k.toUInt64) (copied mem dst.toNat src.toNat k) .b8
        (Expr.var 0 + Expr.var 3) (Expr.ld (Expr.var 1 + Expr.var 3)) (dst + k.toUInt64)
        (readLE (copied mem dst.toNat src.toNat k) (src.toNat + k) 8)
        (by simp [eval, assign, env₀, entryEnv, args, aluResult])
        (by simp [eval, Expr.ld, assign, env₀, entryEnv, args, aluResult, addrS, Width.bytes,
          access_sub readable (b := src.toNat + k) (k := 8) (by omega) (by omega)])
        (by rw [addr]; exact access_sub writable (k := 8) (by omega) (by omega))
      rw [addr, Width.bytes, copied_more mem dst.toNat src.toNat k 8 (by omega) (store_load _ _ _)] at stored
      refine ⟨assign (assign env₀ 3 k.toUInt64) 3 (k + 8).toUInt64, copied mem dst.toNat src.toNat (k + 8),
        Runs.block_cons stored (Runs.set _ _ _ _ _ 3 _ _ (by simp [eval, assign, aluResult])),
        ⟨k + 8, room8, by omega, ?_, rfl⟩, ?_⟩
      · funext x; by_cases same : x = 3 <;> simp [assign, same]
      · simp [assign, toNat_toUInt64 _ small, toNat_toUInt64 (k + 8) (by omega)]
        omega)
  -- Then one byte at a time, from where the words stopped.
  let inv₂ : Env → Memory → Prop := fun env cur =>
    ∃ k, W ≤ k ∧ k ≤ N ∧ env = assign env₀ 3 k.toUInt64 ∧ cur = copied mem dst.toNat src.toNat k
  have loop₂ := Runs.loop_inv (m := m) (w := w) (sp := inner) (c := Expr.lt (.var 3) (.var 2))
    (body := .block [Stmt.st1 (Expr.var 0 + Expr.var 3) (Expr.ld1 (Expr.var 1 + Expr.var 3)), .set 3 (.var 3 + 1)])
    inv₂ (fun env _ => N - (env 3).toNat)
    (fun env cur _ => ⟨_, rfl⟩)
    (by
      rintro env cur v ⟨k, after, within, rfl, rfl⟩ cond nonzero
      have small : k < 2 ^ 64 := by omega
      have more : k < N := by
        simp only [Expr.lt, eval, assign, env₀, entryEnv, args, Cond.holds] at cond
        simp at cond
        by_cases done : k < n.toNat
        · exact done
        · simp [ofNat_lt_iff k n small, done] at cond
          exact absurd cond.symm nonzero
      have addr : (dst + k.toUInt64).toNat = dst.toNat + k := by
        rw [add_toNat _ _ (by rw [toNat_toUInt64 _ small]; omega), toNat_toUInt64 _ small]
      have addrS : (src + k.toUInt64).toNat = src.toNat + k := by
        rw [add_toNat _ _ (by rw [toNat_toUInt64 _ small]; omega), toNat_toUInt64 _ small]
      have stored := Runs.store m w inner (assign env₀ 3 k.toUInt64) (copied mem dst.toNat src.toNat k) .b1
        (Expr.var 0 + Expr.var 3) (Expr.ld1 (Expr.var 1 + Expr.var 3)) (dst + k.toUInt64)
        (readLE (copied mem dst.toNat src.toNat k) (src.toNat + k) 1)
        (by simp [eval, assign, env₀, entryEnv, args, aluResult])
        (by simp [eval, Expr.ld1, assign, env₀, entryEnv, args, aluResult, addrS, Width.bytes,
          access_sub readable (b := src.toNat + k) (k := 1) (by omega) (by omega)])
        (by rw [addr]; exact access_sub writable (k := 1) (by omega) (by omega))
      rw [addr, Width.bytes, copied_more mem dst.toNat src.toNat k 1 (by omega) (store_load1 _ _ _)] at stored
      refine ⟨assign (assign env₀ 3 k.toUInt64) 3 (k + 1).toUInt64, copied mem dst.toNat src.toNat (k + 1),
        Runs.block_cons stored (Runs.set _ _ _ _ _ 3 _ _ (by simp [eval, assign, aluResult])),
        ⟨k + 1, by omega, more, ?_, rfl⟩, ?_⟩
      · funext x; by_cases same : x = 3 <;> simp [assign, same]
      · simp [assign, toNat_toUInt64 _ small, toNat_toUInt64 (k + 1) (by omega)]
        omega)
  -- Nothing is copied before the loops.
  have start₀ : Runs m w inner (entryEnv args) mem
      (.block [.set 3 (.lit 0), .set 4 (.op .sub (.var 2) (.mod (.var 2) (.lit 8)))]) env₀ mem :=
    Runs.block_cons (Runs.set _ _ _ _ _ 3 _ _ rfl) (Runs.set _ _ _ _ _ 4 _ _ wordsEval)
  have first : env₀ = assign env₀ 3 (0 : Nat).toUInt64 := by
    funext x; by_cases same : x = 3 <;> simp [env₀, assign, same]
  obtain ⟨env₁, mem₁, runs₁, ⟨k, within, -, rfl, rfl⟩, exit₁⟩ :=
    loop₁ env₀ mem ⟨0, Nat.zero_le _, rfl, first, (copied_zero mem _ _).symm⟩
  -- The words stop at the last whole word.
  have reached : k = W := by
    have small : k < 2 ^ 64 := by omega
    simp only [Expr.lt, eval, assign, env₀, Cond.holds] at exit₁
    simp [ofNat_lt_ofNat k W small (by omega)] at exit₁
    omega
  subst reached
  obtain ⟨env₂, mem₂, runs₂, ⟨k', after, within', rfl, rfl⟩, exit₂⟩ :=
    loop₂ _ _ ⟨W, Nat.le_refl _, by omega, rfl, rfl⟩
  -- The bytes stop at the count, every byte copied.
  have done : k' = N := by
    have small : k' < 2 ^ 64 := by omega
    simp only [Expr.lt, eval, assign, env₀, entryEnv, args, Cond.holds] at exit₂
    simp [ofNat_lt_iff k' n small] at exit₂
    omega
  subst done
  exact Calls.fn found room rfl (Runs.block_append start₀ (Runs.block_cons runs₁ runs₂)) rfl

open Ssz.Native.Plan

/-- A plan's words, each eight little-endian bytes, from an address, in memory the program may read. -/
def PlanAt (w : World) (mem : Memory) (p : Nat) (ws : List Nat) : Prop :=
  p + 8 * ws.length ≤ addressBound ∧
    ∀ k (h : k < ws.length), w.access (p + 8 * k) 8 ∧ readLE mem (p + 8 * k) 8 = ws[k].toUInt64

/-- The words of a plan's first part are where the plan starts. -/
theorem PlanAt.left {w : World} {mem : Memory} {p : Nat} {a b : List Nat} (h : PlanAt w mem p (a ++ b)) :
    PlanAt w mem p a := by
  refine ⟨by have := h.1; simp at this; omega, fun k small => ?_⟩
  have := h.2 k (by simp; omega)
  simpa [List.getElem_append_left small] using this

/-- The words of a plan's second part are past its first part. -/
theorem PlanAt.right {w : World} {mem : Memory} {p : Nat} {a b : List Nat} (h : PlanAt w mem p (a ++ b)) :
    PlanAt w mem (p + 8 * a.length) b := by
  refine ⟨by have := h.1; simp at this; omega, fun k small => ?_⟩
  have := h.2 (a.length + k) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa [Nat.mul_add, Nat.add_assoc] using this

/-- The cost in stack bytes of one level of the plan walk: a node's frame and a node list's frame. -/
abbrev walkLevel : Nat := (8 + 8 * planNext.frame) + (8 + 8 * planSkip.frame)

/-- The walk past a type's node, from enough stack. -/
def NextOk (m : Module) (w : World) (d : Desc) : Prop :=
  ∀ (sp : Nat) (mem : Memory) (p : Nat), PlanAt w mem p (words d) → w.stackLo + walkLevel * d.nesting ≤ sp →
    Calls m w "ssz_plan_next" sp [p.toUInt64] mem (p + 8 * (words d).length).toUInt64 mem

/-- The walk past a list of nodes, from enough stack. -/
def SkipOk (m : Module) (w : World) (ds : List Desc) : Prop :=
  ∀ (sp : Nat) (mem : Memory) (q : Nat), PlanAt w mem q (wordsAll ds) →
    w.stackLo + (8 + 8 * planSkip.frame) + walkLevel * Desc.deepestNesting ds ≤ sp →
    Calls m w "ssz_plan_skip" sp [q.toUInt64, ds.length.toUInt64] mem (q + 8 * (wordsAll ds).length).toUInt64 mem

/-- The words of two lists of types, one after the other. -/
theorem wordsAll_append : ∀ (a b : List Desc), wordsAll (a ++ b) = wordsAll a ++ wordsAll b
  | [], _ => by simp [wordsAll]
  | d :: rest, b => by simp [wordsAll, wordsAll_append rest b]

/-- A type of a list is nested no deeper than the deepest of the list. -/
theorem nesting_le_deepest : ∀ (ds : List Desc) (d : Desc), d ∈ ds → d.nesting ≤ Desc.deepestNesting ds
  | [], _, member => by simp at member
  | e :: rest, d, member => by
    simp only [Desc.deepestNesting]
    rcases List.mem_cons.mp member with rfl | later
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (nesting_le_deepest rest d later) (Nat.le_max_right _ _)

/-- Every type's node takes at least its tag word. -/
theorem words_length_pos (d : Desc) : 1 ≤ (words d).length := by
  cases d <;> simp [words]

/-- A list's nodes take at least a word each. -/
theorem wordsAll_length_ge : ∀ ds : List Desc, ds.length ≤ (wordsAll ds).length
  | [] => by simp [wordsAll]
  | d :: rest => by
    have := words_length_pos d
    have := wordsAll_length_ge rest
    simp [wordsAll]
    omega

/-- Walking past each node of a list, in turn, walks past the list. -/
theorem skip_ok (m : Module) (w : World) (linked : HasCodec m) (ds : List Desc) (each : ∀ d ∈ ds, NextOk m w d) :
    SkipOk m w ds := by
  intro sp mem q at_ room
  have found : m.fns.lookup "ssz_plan_skip" = some planSkip := linked ("ssz_plan_skip", planSkip) (by simp [codecFns])
  have bound := at_.1
  let pos (j : Nat) : Nat := q + 8 * (wordsAll (ds.take j)).length
  -- Every position of the walk lies inside the plan.
  have posLe : ∀ j, pos j ≤ q + 8 * (wordsAll ds).length := by
    intro j
    have : wordsAll ds = wordsAll (ds.take j) ++ wordsAll (ds.drop j) := by
      rw [← wordsAll_append, List.take_append_drop]
    show q + 8 * (wordsAll (ds.take j)).length ≤ _
    rw [this, List.length_append]
    omega
  have lenSmall : ds.length < 2 ^ 63 := by
    have := wordsAll_length_ge ds
    simp only [addressBound] at bound
    omega
  let inner := sp - 8 - 8 * planSkip.frame
  let inv : Env → Memory → Prop := fun env cur =>
    ∃ j, j ≤ ds.length ∧ env 0 = (pos j).toUInt64 ∧ env 1 = ds.length.toUInt64 ∧ env 2 = j.toUInt64 ∧ cur = mem
  have loop := Runs.loop_inv (m := m) (w := w) (sp := inner)
    (c := Expr.lt (.var 2) (.var 1))
    (body := .block [.call "ssz_plan_next" [.var 0] 0, .set 2 (.var 2 + 1)])
    inv (fun env _ => ds.length - (env 2).toNat)
    (fun env cur _ => ⟨_, rfl⟩)
    (by
      rintro env cur v ⟨j, within, e0, e1, e2, hcur⟩ cond nonzero
      subst cur
      have small : j < 2 ^ 64 := by omega
      have lenMod : ds.length % 2 ^ 64 = ds.length := Nat.mod_eq_of_lt (by omega)
      -- The condition holds, so another node is left.
      have more : j < ds.length := by
        simp only [Expr.lt, eval, e1, e2, Cond.holds] at cond
        by_cases done : j < ds.length
        · exact done
        · simp [ofNat_lt_iff j _ small, lenMod, done] at cond
          exact absurd cond.symm nonzero
      -- The node at this position is the next type of the list.
      have split : ds = ds.take j ++ ds[j] :: ds.drop (j + 1) := by simp
      have plan : PlanAt w mem (pos j) (words ds[j]) := by
        have whole := at_
        rw [split, wordsAll_append, wordsAll] at whole
        exact (whole.right).left
      have deep := nesting_le_deepest ds ds[j] (List.getElem_mem more)
      have called := each ds[j] (List.getElem_mem more) inner mem (pos j) plan (by
        have : walkLevel * ds[j].nesting ≤ walkLevel * Desc.deepestNesting ds := Nat.mul_le_mul_left _ deep
        simp only [inner]
        omega)
      have step : pos j + 8 * (words ds[j]).length = pos (j + 1) := by
        simp only [pos, List.take_add_one, List.getElem?_eq_getElem more, Option.toList_some, wordsAll_append,
          wordsAll, List.append_nil, List.length_append]
        omega
      rw [step] at called
      have ran := Runs.call (m := m) (w := w) (sp := inner) (env := env) (args := [.var 0]) (dst := 0)
        (values := [(pos j).toUInt64]) (by simp [eval, e0]) called
      refine ⟨assign (assign env 0 (pos (j + 1)).toUInt64) 2 (j + 1).toUInt64, mem, ?_, ⟨j + 1, more, ?_, ?_, ?_, rfl⟩, ?_⟩
      · exact Runs.block_cons ran (Runs.set _ _ _ _ _ 2 _ _ (by simp [eval, assign, e2, aluResult]))
      · simp [assign]
      · simp [assign, e1]
      · simp [assign]
      · simp [assign, e2, toNat_toUInt64 _ small]
        omega)
  have start := Runs.set m w inner (entryEnv [q.toUInt64, ds.length.toUInt64]) mem 2 (.lit 0) 0 rfl
  obtain ⟨env', mem', runs, ⟨j, within, e0, e1, e2, hmem⟩, exit⟩ :=
    loop (assign (entryEnv [q.toUInt64, ds.length.toUInt64]) 2 0) mem
      ⟨0, Nat.zero_le _, by simp [assign, entryEnv, pos, wordsAll], by simp [assign, entryEnv], by simp [assign],
        rfl⟩
  subst mem'
  -- The loop stops once every node is walked past.
  have done : j = ds.length := by
    have small : j < 2 ^ 64 := by omega
    have lenMod : ds.length % 2 ^ 64 = ds.length := Nat.mod_eq_of_lt (by omega)
    simp only [Expr.lt, eval, e1, e2, Cond.holds] at exit
    simp [ofNat_lt_iff j _ small, lenMod] at exit
    omega
  subst done
  have whole : pos ds.length = q + 8 * (wordsAll ds).length := by simp [pos]
  refine Calls.fn found (by omega) rfl (Runs.block_cons start runs) ?_
  simp [planSkip, Skip.q, eval, e0, whole]

/-- A branch runs the statement its condition picks. -/
theorem runs_ite {m : Module} {w : World} {sp : Nat} {env env' : Env} {mem mem' : Memory} {c : Expr} {t e : Stmt}
    {v : UInt64} (hc : eval w env mem c = some v) (ht : v ≠ 0 → Runs m w sp env mem t env' mem')
    (he : v = 0 → Runs m w sp env mem e env' mem') : Runs m w sp env mem (.ite c t e) env' mem' := by
  by_cases zero : v = 0
  · subst zero; exact Runs.ite_false hc (he rfl)
  · exact Runs.ite_true v hc zero (ht zero)

/-- A word of a plan, read where the plan says it is. -/
theorem PlanAt.read {w : World} {mem : Memory} {p : Nat} {ws : List Nat} (h : PlanAt w mem p ws) (k : Nat)
    (small : k < ws.length) : w.access (p + 8 * k) 8 ∧ readLE mem (p + 8 * k) 8 = ws[k].toUInt64 :=
  h.2 k small

/-- What the walk past a node does once it has read the node's tag. -/
def nextChain : Stmt :=
  match planNext.body with
  | .seq _ chain => chain
  | _ => .skip

/-- The walk past a node reads its tag, then branches on it. -/
theorem planNext_body : planNext.body = .seq (.set 1 (.load .b8 (.var 0))) nextChain := rfl

/-- The walk past a node, from what its branches do once the tag is read. -/
theorem next_calls (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory) (p : Nat)
    (pSmall : p < 2 ^ 64) (readable : w.access p 8) (room : w.stackLo + 8 + 8 * planNext.frame ≤ sp)
    (env' : Env) (target : UInt64)
    (chain : Runs m w (sp - 8 - 8 * planNext.frame) (assign (entryEnv [p.toUInt64]) 1 (readLE mem p 8)) mem
      nextChain env' mem)
    (answer : env' 3 = target) : Calls m w "ssz_plan_next" sp [p.toUInt64] mem target mem := by
  have found : m.fns.lookup "ssz_plan_next" = some planNext := linked ("ssz_plan_next", planNext) (by simp [codecFns])
  refine Calls.fn (env' := env') found room rfl ?_ (by simp [planNext, Next.q, eval, answer])
  rw [planNext_body]
  exact Runs.seq (Runs.set _ _ _ _ _ 1 _ (readLE mem p 8)
      (by simp [eval, entryEnv, toNat_toUInt64 p pSmall, Width.bytes, readable])) chain

/-- A union of real types pairs each selector with one option. -/
theorem wellFormed_union_paired {selectors : List Nat} {options : List Desc}
    (sound : (Desc.compatibleUnion selectors options).wellFormed = .ok ()) : selectors.length = options.length := by
  rw [Desc.wellFormed] at sound
  simp only [Bind.bind, Except.bind, throw_error] at sound
  repeat' split at sound
  all_goals simp_all

/-- Division of expressions is the language's own division. -/
theorem expr_div (a b : Expr) : a / b = .div a b := rfl

/-- Evaluates the expressions of a driver over variables that hold known words. -/
syntax "evaluate" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| evaluate [$ts,*]) =>
    `(tactic| simp [eval, Expr.eq, Expr.lt, Expr.le, Expr.ne, Expr.ld, word, assign, entryEnv, Cond.holds,
        aluResult, Width.bytes, expr_div, $ts,*])
  | `(tactic| evaluate) =>
    `(tactic| simp [eval, Expr.eq, Expr.lt, Expr.le, Expr.ne, Expr.ld, word, assign, entryEnv, Cond.holds,
        aluResult, Width.bytes])

/-- Walks down a chain of branches whose conditions evaluate to known words, taking the branch each picks. -/
syntax "branches" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| branches [$ts,*]) =>
    `(tactic| repeat (first
        | (refine Runs.ite_false ?_ ?_; · evaluate [$ts,*])
        | (refine Runs.ite_true 1 ?_ (by decide) ?_; · evaluate [$ts,*])))

/-- A number below the word size is below the size words are taken modulo. -/
theorem lt_size {n : Nat} (h : n < 2 ^ 64) : n < UInt64.size := h

/-- An optional bound always takes two words. -/
theorem bound_length (limit : Option Nat) : (bound limit).length = 2 := by
  cases limit <;> rfl

/-- The walk past a node whose words are known, for a node that holds no nodes. -/
theorem next_leaf (m : Module) (w : World) (linked : HasCodec m) (d : Desc) (sp : Nat) (mem : Memory) (p : Nat)
    (at_ : PlanAt w mem p (words d)) (room : w.stackLo + walkLevel * d.nesting ≤ sp) (one : 1 ≤ d.nesting)
    (chain : ∀ inner, Runs m w inner (assign (entryEnv [p.toUInt64]) 1 (readLE mem p 8)) mem nextChain
      (assign (assign (entryEnv [p.toUInt64]) 1 (readLE mem p 8)) 3 (p + 8 * (words d).length).toUInt64) mem) :
    Calls m w "ssz_plan_next" sp [p.toUInt64] mem (p + 8 * (words d).length).toUInt64 mem := by
  have t := at_.read 0 (words_length_pos d)
  have pSmall : p < 2 ^ 64 := by have := at_.1; simp [addressBound] at this; omega
  have level : walkLevel ≤ walkLevel * d.nesting := Nat.le_mul_of_pos_right _ one
  have part : 8 + 8 * planNext.frame ≤ walkLevel := by unfold walkLevel; omega
  refine next_calls m w linked sp mem p pSmall (by simpa using t.1) (by omega) _ _
    (chain _) (by simp [assign])

set_option linter.unusedSimpArgs false in
/-- The walk past any type's node lands right after the node's words. -/
theorem next_ok (m : Module) (w : World) (linked : HasCodec m) (d : Desc) (sound : d.wellFormed = .ok ()) :
    NextOk m w d := by
  revert sound
  induction d using Desc.rec
    (motive_2 := fun ds => Desc.allWellFormed ds = .ok () → ∀ d ∈ ds, NextOk m w d) with
  | nil => rename_i member; simp at member
  | cons field fields ihHead ihTail =>
    rename_i sound d member
    have head : field.wellFormed = .ok () := allWellFormed_mem _ sound field (by simp)
    have tail : Desc.allWellFormed fields = .ok () := by
      cases h : field.wellFormed <;> simp_all [Desc.allWellFormed, Bind.bind, Except.bind]
    rcases List.mem_cons.mp member with rfl | later
    · exact ihHead head
    · exact ihTail tail d later
  | bool | uint _ | byteVector _ | byteList _ | bitVector _ | bitList _ | progressiveBitList _ =>
    intro _ sp mem p at_ room
    have t := at_.read 0 (words_length_pos _)
    refine next_leaf m w linked _ sp mem p at_ room (by simp [Desc.nesting]) (fun inner => ?_)
    simp [words] at t
    unfold nextChain planNext
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Next.tag, Next.p, Next.q, Next.n]
    branches [t.2]
    all_goals exact (by simpa [words, bound_length] using Runs.set _ _ _ _ _ 3 _ _ (by evaluate))
  | vector element length ih =>
    intro sound sp mem p at_ room
    have t := at_.read 0 (words_length_pos _)
    simp [words] at t
    have pSmall : p < 2 ^ 64 := by have := at_.1; simp [addressBound] at this; omega
    have part : 8 + 8 * planNext.frame ≤ walkLevel := by unfold walkLevel; omega
    have plan : PlanAt w mem (p + 16) (words element) := by
      have := (show PlanAt w mem p ([7, length] ++ words element) from at_).right
      simpa using this
    have called := ih (wellFormed_vector sound) (sp - 8 - 8 * planNext.frame) mem (p + 16) plan (by
      simp only [Desc.nesting, Nat.mul_succ] at room; omega)
    have size : p + 16 + 8 * (words element).length = p + 8 * (words (.vector element length)).length := by
      simp [words]; omega
    rw [size] at called
    refine next_calls m w linked sp mem p pSmall (by simpa using t.1)
      (by simp only [Desc.nesting, Nat.mul_succ] at room; omega) ?env0 _ ?chain ?answer
    case chain =>
      unfold nextChain planNext
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Next.tag, Next.p, Next.q, Next.n]
      branches [t.2]
      refine Runs.call (values := [(p + 16).toUInt64]) ?_ called
      evaluate
    case answer => simp [assign]
  | list element limit ih =>
    intro sound sp mem p at_ room
    have t := at_.read 0 (words_length_pos _)
    simp [words] at t
    have pSmall : p < 2 ^ 64 := by have := at_.1; simp [addressBound] at this; omega
    have part : 8 + 8 * planNext.frame ≤ walkLevel := by unfold walkLevel; omega
    have plan : PlanAt w mem (p + 16) (words element) := by
      have := (show PlanAt w mem p ([8, limit] ++ words element) from at_).right
      simpa using this
    have called := ih (wellFormed_list sound) (sp - 8 - 8 * planNext.frame) mem (p + 16) plan (by
      simp only [Desc.nesting, Nat.mul_succ] at room; omega)
    have size : p + 16 + 8 * (words element).length = p + 8 * (words (.list element limit)).length := by
      simp [words]; omega
    rw [size] at called
    refine next_calls m w linked sp mem p pSmall (by simpa using t.1)
      (by simp only [Desc.nesting, Nat.mul_succ] at room; omega) ?env1 _ ?chain ?answer
    case chain =>
      unfold nextChain planNext
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Next.tag, Next.p, Next.q, Next.n]
      branches [t.2]
      refine Runs.call (values := [(p + 16).toUInt64]) ?_ called
      evaluate
    case answer => simp [assign]
  | progressiveList element limit ih =>
    intro sound sp mem p at_ room
    have t := at_.read 0 (words_length_pos _)
    simp [words] at t
    have pSmall : p < 2 ^ 64 := by have := at_.1; simp [addressBound] at this; omega
    have part : 8 + 8 * planNext.frame ≤ walkLevel := by unfold walkLevel; omega
    have plan : PlanAt w mem (p + 24) (words element) := by
      have := (show PlanAt w mem p ((9 :: bound limit) ++ words element) from at_).right
      simpa [bound_length] using this
    have called := ih (wellFormed_progressiveList sound) (sp - 8 - 8 * planNext.frame) mem (p + 24) plan (by
      simp only [Desc.nesting, Nat.mul_succ] at room; omega)
    have size : p + 24 + 8 * (words element).length =
        p + 8 * (words (.progressiveList element limit)).length := by
      simp [words, bound_length]; omega
    rw [size] at called
    refine next_calls m w linked sp mem p pSmall (by simpa using t.1)
      (by simp only [Desc.nesting, Nat.mul_succ] at room; omega) ?env2 _ ?chain ?answer
    case chain =>
      unfold nextChain planNext
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Next.tag, Next.p, Next.q, Next.n]
      branches [t.2]
      refine Runs.call (values := [(p + 24).toUInt64]) ?_ called
      evaluate
    case answer => simp [assign]
  | container names fields ih =>
    intro sound sp mem p at_ room
    have t := at_.read 0 (words_length_pos _)
    have t1 := at_.read 1 (by simp [words])
    simp [words] at t t1
    have pSmall : p + 16 < 2 ^ 64 := by have := at_.1; simp [addressBound, words] at this; omega
    have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; simp; omega
    have whole : walkLevel = (8 + 8 * planNext.frame) + (8 + 8 * planSkip.frame) := rfl
    have plan : PlanAt w mem (p + 16) (wordsAll fields) := by
      have := (show PlanAt w mem p ([10, fields.length] ++ wordsAll fields) from at_).right
      simpa using this
    have called := skip_ok m w linked fields (ih (wellFormed_container sound)) (sp - 8 - 8 * planNext.frame) mem
      (p + 16) plan (by simp only [Desc.nesting, Nat.mul_succ] at room; omega)
    have size : p + 16 + 8 * (wordsAll fields).length = p + 8 * (words (.container names fields)).length := by
      simp [words]; omega
    rw [size] at called
    refine next_calls m w linked sp mem p (by omega) (by simpa using t.1)
      (by simp only [Desc.nesting, Nat.mul_succ] at room; omega) ?env3 _ ?chain ?answer
    case chain =>
      unfold nextChain planNext
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Next.tag, Next.p, Next.q, Next.n]
      branches [t.2]
      refine Runs.call (values := [(p + 16).toUInt64, fields.length.toUInt64]) ?_ called
      evaluate [a8, t1.1, t1.2]
    case answer => simp [assign]
  | progressiveContainer active names fields ih =>
    intro sound sp mem p at_ room
    have shape : words (.progressiveContainer active names fields) =
        ([11, active.length] ++ active.map (fun b => if b then 1 else 0) ++ [fields.length]) ++ wordsAll fields := by
      simp [words]
    rw [shape] at at_
    have t := at_.read 0 (by simp)
    have t1 := at_.read 1 (by simp)
    have tn := at_.read (2 + active.length) (by simp; omega)
    simp at t t1
    have count : ([11, active.length] ++ active.map (fun b => if b then 1 else 0) ++ [fields.length] ++
        wordsAll fields)[2 + active.length]'(by simp; omega) = fields.length := by
      rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
      simp
    rw [count] at tn
    have bound := at_.1
    simp [addressBound] at bound
    have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; simp; omega
    have aN : (UInt64.ofNat p + 16 + 8 * UInt64.ofNat active.length).toNat = p + 8 * (2 + active.length) := by
      rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
        UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
      simp
      omega
    have whole : walkLevel = (8 + 8 * planNext.frame) + (8 + 8 * planSkip.frame) := rfl
    have plan : PlanAt w mem (p + 24 + 8 * active.length) (wordsAll fields) := by
      have := at_.right
      have e : p + 8 * ([11, active.length] ++ active.map (fun b : Bool => if b then 1 else 0) ++ [fields.length]).length =
          p + 24 + 8 * active.length := by simp; omega
      rwa [e] at this
    have called := skip_ok m w linked fields (ih (wellFormed_progressiveContainer sound))
      (sp - 8 - 8 * planNext.frame) mem (p + 24 + 8 * active.length) plan
      (by simp only [Desc.nesting, Nat.mul_succ] at room; omega)
    have size : p + 24 + 8 * active.length + 8 * (wordsAll fields).length =
        p + 8 * (words (.progressiveContainer active names fields)).length := by
      rw [shape]; simp; omega
    rw [size] at called
    refine next_calls m w linked sp mem p (by omega) (by simpa using t.1)
      (by simp only [Desc.nesting, Nat.mul_succ] at room; omega) ?env4 _ ?chain ?answer
    case chain =>
      unfold nextChain planNext
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Next.tag, Next.p, Next.q, Next.n]
      branches [t.2]
      refine Runs.seq (Runs.set _ _ _ _ _ 2 _ (UInt64.ofNat active.length) ?_) ?_
      · evaluate [a8, t1.1, t1.2]
      refine Runs.call (values := [(p + 24 + 8 * active.length).toUInt64, fields.length.toUInt64]) ?_ called
      evaluate [aN, tn.1, tn.2]
    case answer => simp [assign]
  | compatibleUnion selectors options ih =>
    intro sound sp mem p at_ room
    have paired := wellFormed_union_paired sound
    have t := at_.read 0 (words_length_pos _)
    have t1 := at_.read 1 (by simp [words])
    simp [words] at t t1
    have bound := at_.1
    simp [addressBound, words] at bound
    have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; simp; omega
    have whole : walkLevel = (8 + 8 * planNext.frame) + (8 + 8 * planSkip.frame) := rfl
    have plan : PlanAt w mem (p + 16 + 8 * options.length) (wordsAll options) := by
      have := (show PlanAt w mem p (([12, options.length] ++ selectors) ++ wordsAll options) from by
        simpa [words] using at_).right
      have e : p + 8 * ([12, options.length] ++ selectors).length = p + 16 + 8 * options.length := by
        simp [paired]; omega
      rwa [e] at this
    have called := skip_ok m w linked options (ih (wellFormed_union sound))
      (sp - 8 - 8 * planNext.frame) mem (p + 16 + 8 * options.length) plan
      (by simp only [Desc.nesting, Nat.mul_succ] at room; omega)
    have size : p + 16 + 8 * options.length + 8 * (wordsAll options).length =
        p + 8 * (words (.compatibleUnion selectors options)).length := by
      simp [words, paired]; omega
    rw [size] at called
    refine next_calls m w linked sp mem p (by omega) (by simpa using t.1)
      (by simp only [Desc.nesting, Nat.mul_succ] at room; omega) ?env5 _ ?chain ?answer
    case chain =>
      unfold nextChain planNext
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Next.tag, Next.p, Next.q, Next.n]
      branches [t.2]
      refine Runs.seq (Runs.set _ _ _ _ _ 2 _ (UInt64.ofNat options.length) ?_) ?_
      · evaluate [a8, t1.1, t1.2]
      refine Runs.call (values := [(p + 16 + 8 * options.length).toUInt64, options.length.toUInt64]) ?_ called
      evaluate
    case answer => simp [assign]

/-- A type's width as the drivers answer it: the width, or the word for a variable size. -/
def widthWord (d : Desc) : UInt64 :=
  match d.fixedSize with
  | some width => width.toUInt64
  | none => (none64 : Nat).toUInt64

mutual

/-- Whether every type inside a type, the type included, has a width below 2^62 where it has one. -/
def narrow : Desc → Bool
  | .vector element length => ((Desc.vector element length).fixedSize.all (· < 2 ^ 62)) && narrow element
  | .list element _ => narrow element
  | .progressiveList element _ => narrow element
  | .container names fields => ((Desc.container names fields).fixedSize.all (· < 2 ^ 62)) && narrowAll fields
  | .progressiveContainer active names fields =>
    ((Desc.progressiveContainer active names fields).fixedSize.all (· < 2 ^ 62)) && narrowAll fields
  | .compatibleUnion _ options => narrowAll options
  -- A bit vector's length is rounded up to bytes, so the length itself stays clear of the word size.
  | .bitVector length => length < 2 ^ 62
  | d => d.fixedSize.all (· < 2 ^ 62)

/-- Whether every type of a list is narrow. -/
def narrowAll : List Desc → Bool
  | [] => true
  | d :: rest => narrow d && narrowAll rest

end

/-- The widths of two lists of fields, one after the other. -/
theorem fieldsFixedSize_append : ∀ (a b : List Desc),
    Desc.fieldsFixedSize (a ++ b) =
      (Desc.fieldsFixedSize a).bind fun x => (Desc.fieldsFixedSize b).map fun y => x + y
  | [], b => by cases h : Desc.fieldsFixedSize b <;> simp [Desc.fieldsFixedSize, h]
  | d :: rest, b => by
    simp only [List.cons_append, Desc.fieldsFixedSize, fieldsFixedSize_append rest b]
    cases d.fixedSize <;> cases Desc.fieldsFixedSize rest <;> cases Desc.fieldsFixedSize b <;>
      simp [Nat.add_assoc]

/-- A variable field leaves its struct variable. -/
theorem fieldsFixedSize_none (fs : List Desc) (f : Desc) (member : f ∈ fs) (varies : f.fixedSize = none) :
    Desc.fieldsFixedSize fs = none := by
  obtain ⟨a, b, rfl⟩ := List.append_of_mem member
  rw [fieldsFixedSize_append]
  cases Desc.fieldsFixedSize a <;> simp [Desc.fieldsFixedSize, varies]

/-- A struct's width as the drivers answer it: the width, or the word for a variable size. -/
def fieldsWord (fs : List Desc) : UInt64 :=
  match Desc.fieldsFixedSize fs with
  | some width => width.toUInt64
  | none => (none64 : Nat).toUInt64

/-- The cost in stack bytes of one level of the width walk: a node's frame and a field list's frame. -/
abbrev widthLevel : Nat := (8 + 8 * planWidth.frame) + (8 + 8 * planFieldsWidth.frame)

/-- The width of a type's node, from enough stack. -/
def WidthOk (m : Module) (w : World) (d : Desc) : Prop :=
  ∀ (sp : Nat) (mem : Memory) (p : Nat), PlanAt w mem p (words d) →
    w.stackLo + (widthLevel + walkLevel) * d.nesting ≤ sp →
    Calls m w "ssz_plan_width" sp [p.toUInt64] mem (widthWord d) mem

/-- The width of a list of field nodes, from enough stack. -/
def FieldsWidthOk (m : Module) (w : World) (fs : List Desc) : Prop :=
  ∀ (sp : Nat) (mem : Memory) (q : Nat), PlanAt w mem q (wordsAll fs) →
    w.stackLo + (8 + 8 * planFieldsWidth.frame) + (widthLevel + walkLevel) * Desc.deepestNesting fs ≤ sp →
    Calls m w "ssz_plan_fields_width" sp [q.toUInt64, fs.length.toUInt64] mem (fieldsWord fs) mem

/-- A narrow type's width word is the word for a variable size exactly when the type is variable. -/
theorem widthWord_none (d : Desc) (width : Nat) (fixed : d.fixedSize = some width) (small : width < 2 ^ 62) :
    widthWord d ≠ (none64 : Nat).toUInt64 := by
  simp only [widthWord, fixed]
  intro same
  have := congrArg UInt64.toNat same
  rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by decide)] at this
  simp only [none64] at this
  omega

/-- A narrow type of a list is narrow. -/
theorem narrow_mem : ∀ (fs : List Desc), narrowAll fs = true → ∀ f ∈ fs, narrow f = true
  | [], _, _, member => by simp at member
  | d :: rest, all, f, member => by
    simp only [narrowAll, Bool.and_eq_true] at all
    rcases List.mem_cons.mp member with rfl | later
    · exact all.1
    · exact narrow_mem rest all.2 f later

/-- A narrow type has a width below 2^62 where it has one. -/
theorem narrow_width (d : Desc) (thin : narrow d = true) (width : Nat) (fixed : d.fixedSize = some width) :
    width < 2 ^ 62 := by
  have self : d.fixedSize.all (· < 2 ^ 62) = true := by
    cases d <;> simp only [narrow, Bool.and_eq_true] at thin <;>
      first | exact thin.1 | exact thin | (simp [Desc.fixedSize] at thin ⊢; try omega)
  rw [fixed] at self
  simpa using self

set_option linter.unusedSimpArgs false in
/-- Walking a list of fields, measuring each, measures the struct. -/
theorem fieldsWidth_ok (m : Module) (w : World) (linked : HasCodec m) (fs : List Desc)
    (sound : ∀ f ∈ fs, f.wellFormed = .ok ()) (thin : ∀ f ∈ fs, narrow f = true)
    (total : ∀ width, Desc.fieldsFixedSize fs = some width → width < 2 ^ 62)
    (each : ∀ f ∈ fs, WidthOk m w f) : FieldsWidthOk m w fs := by
  intro sp mem q at_ room
  have found : m.fns.lookup "ssz_plan_fields_width" = some planFieldsWidth :=
    linked ("ssz_plan_fields_width", planFieldsWidth) (by simp [codecFns])
  have bound := at_.1
  let pos (j : Nat) : Nat := q + 8 * (wordsAll (fs.take j)).length
  have posLe : ∀ j, pos j ≤ q + 8 * (wordsAll fs).length := by
    intro j
    have : wordsAll fs = wordsAll (fs.take j) ++ wordsAll (fs.drop j) := by
      rw [← wordsAll_append, List.take_append_drop]
    show q + 8 * (wordsAll (fs.take j)).length ≤ _
    rw [this, List.length_append]
    omega
  have lenSmall : fs.length < 2 ^ 63 := by
    have := wordsAll_length_ge fs
    simp only [addressBound] at bound
    omega
  have lenMod : fs.length % 2 ^ 64 = fs.length := Nat.mod_eq_of_lt (by omega)
  let noneWord : UInt64 := (none64 : Nat).toUInt64
  let inner := sp - 8 - 8 * planFieldsWidth.frame
  -- After j fields, all fixed so far, the total is their width; or the struct is known to be variable.
  let inv : Env → Memory → Prop := fun env cur =>
    ∃ j, j ≤ fs.length ∧ env 0 = (pos j).toUInt64 ∧ env 1 = fs.length.toUInt64 ∧ env 2 = j.toUInt64 ∧
      cur = mem ∧
      ((∃ s, Desc.fieldsFixedSize (fs.take j) = some s ∧ env 3 = s.toUInt64) ∨
        (env 3 = noneWord ∧ Desc.fieldsFixedSize fs = none))
  have loop := Runs.loop_inv (m := m) (w := w) (sp := inner)
    (c := Expr.op .and (Expr.lt (.var 2) (.var 1)) (Expr.ne (.var 3) (.lit noneWord)))
    (body := .block [.call "ssz_plan_width" [.var 0] 4,
      .ite (Expr.eq (.var 4) (.lit noneWord)) (.block [.set 3 (.lit noneWord)])
        (.block [.set 3 (.op .add (.var 3) (.var 4)), .call "ssz_plan_next" [.var 0] 0,
          .set 2 (.op .add (.var 2) (.lit 1))])])
    inv (fun env _ => 2 * (fs.length - (env 2).toNat) + (if env 3 = noneWord then 0 else 1))
    (fun env cur _ => ⟨_, rfl⟩)
    (by
      rintro env cur v ⟨j, within, e0, e1, e2, hcur, sofar⟩ cond nonzero
      subst cur
      have small : j < 2 ^ 64 := by omega
      -- The condition holds, so another field is left, and the total is still a width.
      have more : j < fs.length ∧ env 3 ≠ noneWord := by
        simp only [Expr.lt, Expr.ne, eval, e1, e2, Cond.holds, aluResult] at cond
        constructor
        · by_cases left : j < fs.length
          · exact left
          · simp [ofNat_lt_iff j _ small, left, lenMod] at cond
            exact absurd cond.symm nonzero
        · intro right
          simp [right] at cond
          exact absurd cond.symm nonzero
      obtain ⟨s, prefix_, e3⟩ : ∃ s, Desc.fieldsFixedSize (fs.take j) = some s ∧ env 3 = s.toUInt64 := by
        rcases sofar with found | ⟨isNone, -⟩
        · exact found
        · exact absurd isNone more.2
      -- The field at this position is the next field of the struct.
      have member : fs[j] ∈ fs := List.getElem_mem more.1
      have split : fs = fs.take j ++ fs[j] :: fs.drop (j + 1) := by simp
      have plan : PlanAt w mem (pos j) (words fs[j]) := by
        have whole := at_
        rw [split, wordsAll_append, wordsAll] at whole
        exact (whole.right).left
      have deep := nesting_le_deepest fs fs[j] member
      have deeper : (widthLevel + walkLevel) * fs[j].nesting ≤ (widthLevel + walkLevel) * Desc.deepestNesting fs :=
        Nat.mul_le_mul_left _ deep
      have measured := each fs[j] member inner mem (pos j) plan (by simp only [inner]; omega)
      have ranWidth := Runs.call (m := m) (w := w) (sp := inner) (env := env) (args := [.var 0]) (dst := 4)
        (values := [(pos j).toUInt64]) (by simp [eval, e0]) measured
      have step : pos j + 8 * (words fs[j]).length = pos (j + 1) := by
        simp only [pos, List.take_add_one, List.getElem?_eq_getElem more.1, Option.toList_some, wordsAll_append,
          wordsAll, List.append_nil, List.length_append]
        omega
      cases fixed : fs[j].fixedSize with
      | none =>
        -- A variable field: the struct is variable, and the walk stops.
        have word : widthWord fs[j] = noneWord := by simp [widthWord, fixed, noneWord]
        refine ⟨assign (assign env 4 (widthWord fs[j])) 3 noneWord, mem, ?_,
          ⟨j, within, ?_, ?_, ?_, rfl, Or.inr ⟨?_, fieldsFixedSize_none fs fs[j] member fixed⟩⟩, ?_⟩
        · refine Runs.block_cons ranWidth (Runs.block_cons ?_ (Runs.block_nil _ _ _ _ _))
          refine Runs.ite_true 1 (by simp [eval, Expr.eq, assign, word, Cond.holds]) (by decide) ?_
          exact Runs.set _ _ _ _ _ 3 _ _ (by simp [eval])
        · simp [assign, e0]
        · simp [assign, e1]
        · simp [assign, e2]
        · simp [assign]
        · simp [assign, e2, more.2, toNat_toUInt64 _ small]
      | some width =>
        -- A fixed field: its width is added, and the walk moves past it.
        have thinField := narrow_width fs[j] (thin _ member) width fixed
        have word : widthWord fs[j] = width.toUInt64 := by simp [widthWord, fixed]
        have notNone := widthWord_none fs[j] width fixed thinField
        have walked := next_ok m w linked fs[j] (sound _ member) inner mem (pos j) plan (by
          have : walkLevel * fs[j].nesting ≤ (widthLevel + walkLevel) * fs[j].nesting :=
            Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
          simp only [inner]; omega)
        rw [step] at walked
        let env₁ := assign (assign env 4 (widthWord fs[j])) 3 (s + width).toUInt64
        have ranNext := Runs.call (m := m) (w := w) (sp := inner) (env := env₁) (args := [.var 0]) (dst := 0)
          (values := [(pos j).toUInt64]) (by simp [env₁, eval, assign, e0]) walked
        refine ⟨assign (assign env₁ 0 (pos (j + 1)).toUInt64) 2 (j + 1).toUInt64, mem, ?_,
          ⟨j + 1, more.1, ?_, ?_, ?_, rfl, Or.inl ⟨s + width, ?_, ?_⟩⟩, ?_⟩
        · refine Runs.block_cons ranWidth (Runs.block_cons ?_ (Runs.block_nil _ _ _ _ _))
          have notNone' : widthWord fs[j] ≠ noneWord := notNone
          refine Runs.ite_false (by simp [eval, Expr.eq, assign, Cond.holds, notNone']) ?_
          refine Runs.block_cons (Runs.set _ _ _ _ _ 3 _ (s + width).toUInt64
            (by simp [eval, assign, e3, word, aluResult])) ?_
          exact Runs.block_cons ranNext (Runs.set _ _ _ _ _ 2 _ _ (by simp [env₁, eval, assign, e2, aluResult]))
        · simp [assign]
        · simp [assign, env₁, e1]
        · simp [assign]
        · rw [List.take_add_one, List.getElem?_eq_getElem more.1, Option.toList_some, fieldsFixedSize_append,
            prefix_]
          simp [Desc.fieldsFixedSize, fixed]
        · simp [assign, env₁]
        · simp only [assign, env₁, if_pos, e2, toNat_toUInt64 _ small]
          simp [toNat_toUInt64 (j + 1) (by omega)]
          split <;> omega)

  let env₀ := assign (assign (entryEnv [q.toUInt64, fs.length.toUInt64]) 2 0) 3 0
  have first := Runs.set m w inner (entryEnv [q.toUInt64, fs.length.toUInt64]) mem 2 (.lit 0) 0 rfl
  have second := Runs.set m w inner (assign (entryEnv [q.toUInt64, fs.length.toUInt64]) 2 0) mem 3 (.lit 0) 0 rfl
  obtain ⟨env', mem', runs, ⟨j, within, e0, e1, e2, hmem, sofar⟩, exit⟩ :=
    loop env₀ mem ⟨0, Nat.zero_le _, by simp [env₀, assign, entryEnv, pos, wordsAll], by simp [env₀, assign, entryEnv],
      by simp [env₀, assign], rfl, Or.inl ⟨0, by simp [Desc.fieldsFixedSize], by simp [env₀, assign]⟩⟩
  subst mem'
  -- The walk stops at the end of the fields, or at the first variable one.
  have answer : env' 3 = fieldsWord fs := by
    have small : j < 2 ^ 64 := by omega
    simp only [Expr.lt, Expr.ne, eval, e1, e2, Cond.holds, aluResult] at exit
    rcases sofar with ⟨s, prefix_, e3⟩ | ⟨e3, varies⟩
    · by_cases ended : j = fs.length
      · subst ended
        rw [List.take_length] at prefix_
        simp [fieldsWord, prefix_, e3]
      · have short : j < fs.length := by omega
        -- The loop stopped early, so the total met the word for a variable size.
        have isNone : env' 3 = noneWord := by
          by_cases differs : env' 3 = noneWord
          · exact differs
          · simp [ofNat_lt_iff j _ small, short, lenMod, differs] at exit
        -- A fixed struct is wider than any prefix, and narrower than that word, so the struct varies.
        cases whole : Desc.fieldsFixedSize fs with
        | none => simp [fieldsWord, whole, isNone, noneWord]
        | some width =>
          exfalso
          have split : fs = fs.take j ++ fs.drop j := (List.take_append_drop j fs).symm
          have sum := whole
          rw [split, fieldsFixedSize_append, prefix_] at sum
          cases rest : Desc.fieldsFixedSize (fs.drop j) <;> simp [rest] at sum
          have narrowTotal := total width whole
          rw [e3] at isNone
          have := congrArg UInt64.toNat isNone
          simp only [noneWord] at this
          rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by decide)] at this
          simp only [none64] at this
          omega
    · simp [fieldsWord, varies, e3, noneWord]
  refine Calls.fn found (by omega) rfl (Runs.block_cons first (Runs.block_cons second runs)) ?_
  simp [planFieldsWidth, Fields.total, eval, answer]

/-- What the width of a node does once it has read the node's tag and set the answer to a variable size. -/
def widthChain : Stmt :=
  match planWidth.body with
  | .seq _ (.seq _ chain) => chain
  | _ => .skip

/-- The width of a node reads its tag, sets the answer to a variable size, then branches on the tag. -/
theorem planWidth_body :
    planWidth.body = .seq (.set 1 (.load .b8 (.var 0))) (.seq (.set 2 (.lit (none64 : Nat).toUInt64)) widthChain) :=
  rfl

/-- The width of a node, from what its branches do once the tag is read. -/
theorem width_calls (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory) (p : Nat)
    (pSmall : p < 2 ^ 64) (readable : w.access p 8) (room : w.stackLo + 8 + 8 * planWidth.frame ≤ sp)
    (env' : Env) (target : UInt64)
    (chain : Runs m w (sp - 8 - 8 * planWidth.frame)
      (assign (assign (entryEnv [p.toUInt64]) 1 (readLE mem p 8)) 2 (none64 : Nat).toUInt64) mem widthChain env' mem)
    (answer : env' 2 = target) : Calls m w "ssz_plan_width" sp [p.toUInt64] mem target mem := by
  have found : m.fns.lookup "ssz_plan_width" = some planWidth := linked ("ssz_plan_width", planWidth) (by simp [codecFns])
  refine Calls.fn (env' := env') found room rfl ?_ (by simp [planWidth, Width_.w, eval, answer])
  rw [planWidth_body]
  exact Runs.seq (Runs.set _ _ _ _ _ 1 _ (readLE mem p 8)
      (by simp [eval, entryEnv, toNat_toUInt64 p pSmall, Width.bytes, readable]))
    (Runs.seq (Runs.set _ _ _ _ _ 2 _ _ rfl) chain)

/-- Doing nothing leaves a variable that already holds a value holding it. -/
theorem runs_skip_same {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} (x : UInt64)
    (holds : env 2 = x) : Runs m w sp env mem .skip (assign env 2 x) mem := by
  have same : assign env 2 x = env := by
    funext k
    by_cases at_ : k = 2
    · subst at_; simp [assign, holds]
    · simp [assign, at_]
  rw [same]
  exact Runs.skip m w sp env mem

/-- The width of a node is the type's width word, from a run of its branches that sets it. -/
theorem width_from (m : Module) (w : World) (linked : HasCodec m) (d : Desc) (sp : Nat) (mem : Memory) (p : Nat)
    (at_ : PlanAt w mem p (words d)) (room : w.stackLo + 8 + 8 * planWidth.frame ≤ sp)
    (chain : Runs m w (sp - 8 - 8 * planWidth.frame)
      (assign (assign (entryEnv [p.toUInt64]) 1 (readLE mem p 8)) 2 (none64 : Nat).toUInt64) mem widthChain
      (assign (assign (assign (entryEnv [p.toUInt64]) 1 (readLE mem p 8)) 2 (none64 : Nat).toUInt64) 2
        (widthWord d)) mem) :
    Calls m w "ssz_plan_width" sp [p.toUInt64] mem (widthWord d) mem := by
  have t := at_.read 0 (words_length_pos d)
  have pSmall : p < 2 ^ 64 := by have := at_.1; simp [addressBound] at this; omega
  exact width_calls m w linked sp mem p pSmall (by simpa using t.1) room _ _ chain (by simp [assign])

set_option linter.unusedSimpArgs false in
/-- The width the driver gives a narrow, real type's node is the type's width, or the word for a variable size. -/
theorem width_ok (m : Module) (w : World) (linked : HasCodec m) (d : Desc) (sound : d.wellFormed = .ok ())
    (thin : narrow d = true) : WidthOk m w d := by
  revert sound thin
  induction d using Desc.rec
    (motive_2 := fun ds => Desc.allWellFormed ds = .ok () → narrowAll ds = true → ∀ d ∈ ds, WidthOk m w d) with
  | nil => rename_i member; simp at member
  | cons field fields ihHead ihTail =>
    rename_i sound thin d member
    have head : field.wellFormed = .ok () := allWellFormed_mem _ sound field (by simp)
    have tail : Desc.allWellFormed fields = .ok () := by
      cases h : field.wellFormed <;> simp_all [Desc.allWellFormed, Bind.bind, Except.bind]
    simp only [narrowAll, Bool.and_eq_true] at thin
    rcases List.mem_cons.mp member with rfl | later
    · exact ihHead head thin.1
    · exact ihTail tail thin.2 d later
  | bool =>
    intro _ thin sp mem p at_ room
    have t := at_.read 0 (words_length_pos _)
    have part : 8 + 8 * planWidth.frame ≤ widthLevel + walkLevel := by unfold widthLevel; omega
    simp only [Desc.nesting, Nat.mul_one] at room
    refine width_from m w linked _ sp mem p at_ (by omega) ?_
    simp [words] at t
    unfold widthChain planWidth
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Width_.tag, Width_.p, Width_.w,
      Width_.e, Width_.k]
    branches [t.2]
    exact Runs.set _ _ _ _ _ 2 _ _ (by evaluate [widthWord, Desc.fixedSize])
  | uint _ | byteVector _ | byteList _ | bitList _ | progressiveBitList _ =>
    intro _ thin sp mem p at_ room
    have t := at_.read 0 (words_length_pos _)
    have pSmall : p + 8 < 2 ^ 64 := by have := at_.1; simp [addressBound, words] at this; omega
    have part : 8 + 8 * planWidth.frame ≤ widthLevel + walkLevel := by unfold widthLevel; omega
    simp only [Desc.nesting, Nat.mul_one] at room
    refine width_from m w linked _ sp mem p at_ (by omega) ?_
    have t1 := at_.read 1 (by simp [words, bound_length])
    simp [words] at t t1
    have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; simp; omega
    unfold widthChain planWidth
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Width_.tag, Width_.p, Width_.w,
      Width_.e, Width_.k]
    branches [t.2]
    all_goals first
      | exact runs_skip_same _ (by simp [assign, widthWord, Desc.fixedSize])
      | exact Runs.set _ _ _ _ _ 2 _ _ (by evaluate [a8, t1.1, t1.2, widthWord, Desc.fixedSize])
  | list _ _ _ | progressiveList _ _ _ | compatibleUnion _ _ _ =>
    intro _ thin sp mem p at_ room
    have t := at_.read 0 (words_length_pos _)
    have part : 8 + 8 * planWidth.frame ≤ widthLevel + walkLevel := by unfold widthLevel; omega
    simp only [Desc.nesting, Nat.mul_succ] at room
    refine width_from m w linked _ sp mem p at_ (by omega) ?_
    simp [words] at t
    unfold widthChain planWidth
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Width_.tag, Width_.p, Width_.w,
      Width_.e, Width_.k]
    branches [t.2]
    exact runs_skip_same _ (by simp [assign, widthWord, Desc.fixedSize])
  | bitVector length =>
    intro _ thin sp mem p at_ room
    have t := at_.read 0 (words_length_pos _)
    have t1 := at_.read 1 (by simp [words])
    have pSmall : p + 8 < 2 ^ 64 := by have := at_.1; simp [addressBound, words] at this; omega
    have part : 8 + 8 * planWidth.frame ≤ widthLevel + walkLevel := by unfold widthLevel; omega
    simp only [Desc.nesting, Nat.mul_one] at room
    simp only [narrow, decide_eq_true_eq] at thin
    refine width_from m w linked _ sp mem p at_ (by omega) ?_
    simp [words] at t t1
    have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; simp; omega
    -- The length is far below the word size, so rounding it up to bytes does not wrap.
    have bytes : (UInt64.ofNat length + 7) / 8 = UInt64.ofNat ((length + 7) / 8) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_div, UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
        UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
      simp
      omega
    unfold widthChain planWidth
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Width_.tag, Width_.p, Width_.w,
      Width_.e, Width_.k]
    branches [t.2]
    exact Runs.set _ _ _ _ _ 2 _ _ (by evaluate [a8, t1.1, t1.2, widthWord, Desc.fixedSize, bytes])
  | vector element length ih =>
    intro sound thin sp mem p at_ room
    simp only [narrow, Bool.and_eq_true] at thin
    have t := at_.read 0 (words_length_pos _)
    have t1 := at_.read 1 (by simp [words])
    have pSmall : p + 16 < 2 ^ 64 := by have := at_.1; simp [addressBound, words] at this; omega
    have whole : widthLevel = (8 + 8 * planWidth.frame) + (8 + 8 * planFieldsWidth.frame) := rfl
    simp only [Desc.nesting, Nat.mul_succ] at room
    have plan : PlanAt w mem (p + 16) (words element) := by
      have := (show PlanAt w mem p ([7, length] ++ words element) from at_).right
      simpa using this
    have measured := ih (wellFormed_vector sound) thin.2 (sp - 8 - 8 * planWidth.frame) mem (p + 16) plan
      (by omega)
    simp [words] at t t1
    have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; simp; omega
    cases fixed : element.fixedSize with
    | none =>
      -- A variable element leaves the vector variable, and the answer stays so.
      have word : widthWord element = (none64 : Nat).toUInt64 := by simp [widthWord, fixed]
      refine width_calls m w linked sp mem p (by omega) t.1 (by omega) ?envN _ ?chainN ?answerN
      case chainN =>
        unfold widthChain planWidth
        dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Width_.tag, Width_.p, Width_.w,
          Width_.e, Width_.k]
        branches [t.2]
        refine Runs.seq (Runs.call (values := [(p + 16).toUInt64]) ?_ measured) ?_
        · evaluate
        refine Runs.ite_false (by evaluate [word]) ?_
        exact Runs.skip _ _ _ _ _
      case answerN => simp [assign, widthWord, Desc.fixedSize, fixed]
    | some width =>
      -- A fixed element: the vector is as wide as its elements together.
      have notNone := widthWord_none element width fixed (narrow_width element thin.2 width fixed)
      have notNone' : widthWord element ≠ 18446744073709551615 := by simpa using notNone
      have word : widthWord element = width.toUInt64 := by simp [widthWord, fixed]
      refine width_calls m w linked sp mem p (by omega) t.1 (by omega) ?envF _ ?chainF ?answerF
      case chainF =>
        unfold widthChain planWidth
        dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Width_.tag, Width_.p, Width_.w,
          Width_.e, Width_.k]
        branches [t.2]
        refine Runs.seq (Runs.call (values := [(p + 16).toUInt64]) ?_ measured) ?_
        · evaluate
        refine Runs.ite_true 1 (by evaluate [notNone']) (by decide) ?_
        refine Runs.set _ _ _ _ _ 2 _ (width.toUInt64 * length.toUInt64) ?_
        evaluate [a8, t1.1, t1.2, word]
      case answerF => simp [assign, widthWord, Desc.fixedSize, fixed]
  | container names fields ih =>
    intro sound thin sp mem p at_ room
    simp only [narrow, Bool.and_eq_true] at thin
    have t := at_.read 0 (words_length_pos _)
    have t1 := at_.read 1 (by simp [words])
    have pSmall : p + 16 < 2 ^ 64 := by have := at_.1; simp [addressBound, words] at this; omega
    have whole : widthLevel = (8 + 8 * planWidth.frame) + (8 + 8 * planFieldsWidth.frame) := rfl
    simp only [Desc.nesting, Nat.mul_succ] at room
    refine width_from m w linked _ sp mem p at_ (by omega) ?_
    have plan : PlanAt w mem (p + 16) (wordsAll fields) := by
      have := (show PlanAt w mem p ([10, fields.length] ++ wordsAll fields) from at_).right
      simpa using this
    have all := wellFormed_container sound
    have measured := fieldsWidth_ok m w linked fields (allWellFormed_mem fields all) (narrow_mem fields thin.2)
      (fun width fixed => by
        have := thin.1
        simp [Desc.fixedSize, fixed] at this
        exact this)
      (ih all thin.2) (sp - 8 - 8 * planWidth.frame) mem (p + 16) plan (by omega)
    have same : fieldsWord fields = widthWord (.container names fields) := by
      simp [fieldsWord, widthWord, Desc.fixedSize]
    rw [same] at measured
    simp [words] at t t1
    have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; simp; omega
    unfold widthChain planWidth
    dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Width_.tag, Width_.p, Width_.w,
      Width_.e, Width_.k]
    branches [t.2]
    refine Runs.call (values := [(p + 16).toUInt64, fields.length.toUInt64]) ?_ measured
    evaluate [a8, t1.1, t1.2]
  | progressiveContainer active names fields ih =>
    intro sound thin sp mem p at_ room
    simp only [narrow, Bool.and_eq_true] at thin
    have shape : words (.progressiveContainer active names fields) =
        ([11, active.length] ++ active.map (fun b => if b then 1 else 0) ++ [fields.length]) ++ wordsAll fields := by
      simp [words]
    have whole : widthLevel = (8 + 8 * planWidth.frame) + (8 + 8 * planFieldsWidth.frame) := rfl
    simp only [Desc.nesting, Nat.mul_succ] at room
    have t0 := at_.read 0 (words_length_pos _)
    have p0 : p < 2 ^ 64 := by have := at_.1; simp [addressBound] at this; omega
    refine width_calls m w linked sp mem p p0 (by simpa using t0.1) (by omega) ?envP _ ?chainP ?answerP
    case chainP =>
      rw [shape] at at_
      have t := at_.read 0 (by simp)
      have t1 := at_.read 1 (by simp)
      have tn := at_.read (2 + active.length) (by simp; omega)
      simp at t t1
      have count : ([11, active.length] ++ active.map (fun b => if b then 1 else 0) ++ [fields.length] ++
          wordsAll fields)[2 + active.length]'(by simp; omega) = fields.length := by
        rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
        simp
      rw [count] at tn
      have bound := at_.1
      simp [addressBound] at bound
      have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; simp; omega
      have aN : (UInt64.ofNat p + 16 + 8 * UInt64.ofNat active.length).toNat = p + 8 * (2 + active.length) := by
        rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
          UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]
        simp
        omega
      have plan : PlanAt w mem (p + 24 + 8 * active.length) (wordsAll fields) := by
        have := at_.right
        have e : p + 8 * ([11, active.length] ++ active.map (fun b : Bool => if b then 1 else 0) ++
            [fields.length]).length = p + 24 + 8 * active.length := by simp; omega
        rwa [e] at this
      have all := wellFormed_progressiveContainer sound
      have measured := fieldsWidth_ok m w linked fields (allWellFormed_mem fields all) (narrow_mem fields thin.2)
        (fun width fixed => by
          have := thin.1
          simp [Desc.fixedSize, fixed] at this
          exact this)
        (ih all thin.2) (sp - 8 - 8 * planWidth.frame) mem (p + 24 + 8 * active.length) plan (by omega)
      have same : fieldsWord fields = widthWord (.progressiveContainer active names fields) := by
        simp [fieldsWord, widthWord, Desc.fixedSize]
      rw [same] at measured
      unfold widthChain planWidth
      dsimp only [Stmt.block, Stmt.ifElse, Stmt.assign, Stmt.callInto, Stmt.when, Width_.tag, Width_.p, Width_.w,
        Width_.e, Width_.k]
      branches [t.2]
      refine Runs.seq (Runs.set _ _ _ _ _ 4 _ (UInt64.ofNat active.length) ?_) ?_
      · evaluate [a8, t1.1, t1.2]
      refine Runs.call (values := [(p + 24 + 8 * active.length).toUInt64, fields.length.toUInt64]) ?_ measured
      evaluate [aN, tn.1, tn.2]

    case answerP => simp [assign]
/-- The fixed part of two lists of fields, one after the other. -/
theorem leadingWidth_append : ∀ (a b : List Desc),
    Desc.leadingWidth (a ++ b) = Desc.leadingWidth a + Desc.leadingWidth b
  | [], _ => by simp [Desc.leadingWidth]
  | d :: rest, b => by simp [Desc.leadingWidth, leadingWidth_append rest b]; omega

set_option linter.unusedSimpArgs false in
/-- Walking a list of fields, adding each one's width or an offset's, measures the struct's fixed part. -/
theorem leading_ok (m : Module) (w : World) (linked : HasCodec m) (fs : List Desc)
    (sound : ∀ f ∈ fs, f.wellFormed = .ok ()) (thin : ∀ f ∈ fs, narrow f = true)
    (each : ∀ f ∈ fs, WidthOk m w f) (sp : Nat) (mem : Memory) (q : Nat) (at_ : PlanAt w mem q (wordsAll fs))
    (room : w.stackLo + (8 + 8 * planLeading.frame) + (widthLevel + walkLevel) * Desc.deepestNesting fs ≤ sp) :
    Calls m w "ssz_plan_leading" sp [q.toUInt64, fs.length.toUInt64] mem (Desc.leadingWidth fs).toUInt64 mem := by
  have found : m.fns.lookup "ssz_plan_leading" = some planLeading :=
    linked ("ssz_plan_leading", planLeading) (by simp [codecFns])
  have bound := at_.1
  let pos (j : Nat) : Nat := q + 8 * (wordsAll (fs.take j)).length
  have lenSmall : fs.length < 2 ^ 63 := by
    have := wordsAll_length_ge fs
    simp only [addressBound] at bound
    omega
  have lenMod : fs.length % 2 ^ 64 = fs.length := Nat.mod_eq_of_lt (by omega)
  let inner := sp - 8 - 8 * planLeading.frame
  -- After j fields, the total is the width of their part of the fixed part.
  let inv : Env → Memory → Prop := fun env cur =>
    ∃ j, j ≤ fs.length ∧ env 0 = (pos j).toUInt64 ∧ env 1 = fs.length.toUInt64 ∧ env 2 = j.toUInt64 ∧
      cur = mem ∧ env 3 = (Desc.leadingWidth (fs.take j)).toUInt64
  have loop := Runs.loop_inv (m := m) (w := w) (sp := inner)
    (c := Expr.lt (.var 2) (.var 1))
    (body := .block [.call "ssz_plan_width" [.var 0] 4,
      .ite (Expr.eq (.var 4) (.lit (none64 : Nat).toUInt64)) (.block [.set 3 (.var 3 + 4)])
        (.block [.set 3 (.var 3 + .var 4)]),
      .call "ssz_plan_next" [.var 0] 0, .set 2 (.var 2 + 1)])
    inv (fun env _ => fs.length - (env 2).toNat)
    (fun env cur _ => ⟨_, rfl⟩)
    (by
      rintro env cur v ⟨j, within, e0, e1, e2, hcur, e3⟩ cond nonzero
      subst cur
      have small : j < 2 ^ 64 := by omega
      have more : j < fs.length := by
        simp only [Expr.lt, eval, e1, e2, Cond.holds] at cond
        by_cases left : j < fs.length
        · exact left
        · simp [ofNat_lt_iff j _ small, left, lenMod] at cond
          exact absurd cond.symm nonzero
      have member : fs[j] ∈ fs := List.getElem_mem more
      have split : fs = fs.take j ++ fs[j] :: fs.drop (j + 1) := by simp
      have plan : PlanAt w mem (pos j) (words fs[j]) := by
        have whole := at_
        rw [split, wordsAll_append, wordsAll] at whole
        exact (whole.right).left
      have deep := nesting_le_deepest fs fs[j] member
      have deeper : (widthLevel + walkLevel) * fs[j].nesting ≤ (widthLevel + walkLevel) * Desc.deepestNesting fs :=
        Nat.mul_le_mul_left _ deep
      have measured := each fs[j] member inner mem (pos j) plan (by simp only [inner]; omega)
      have ranWidth := Runs.call (m := m) (w := w) (sp := inner) (env := env) (args := [.var 0]) (dst := 4)
        (values := [(pos j).toUInt64]) (by simp [eval, e0]) measured
      have step : pos j + 8 * (words fs[j]).length = pos (j + 1) := by
        simp only [pos, List.take_add_one, List.getElem?_eq_getElem more, Option.toList_some, wordsAll_append,
          wordsAll, List.append_nil, List.length_append]
        omega
      have walked := next_ok m w linked fs[j] (sound _ member) inner mem (pos j) plan (by
        have : walkLevel * fs[j].nesting ≤ (widthLevel + walkLevel) * fs[j].nesting :=
          Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
        simp only [inner]; omega)
      rw [step] at walked
      have grown : Desc.leadingWidth (fs.take (j + 1)) = Desc.leadingWidth (fs.take j) + fs[j].fixedSize.getD 4 := by
        rw [List.take_add_one, List.getElem?_eq_getElem more, Option.toList_some, leadingWidth_append]
        simp [Desc.leadingWidth, bytesPerOffset]
      -- The field adds its width, or an offset's.
      have added : ∃ env₁, Runs m w inner (assign env 4 (widthWord fs[j])) mem
          (.ite (Expr.eq (.var 4) (.lit (none64 : Nat).toUInt64)) (.block [.set 3 (.var 3 + 4)])
            (.block [.set 3 (.var 3 + .var 4)])) env₁ mem ∧
          env₁ = assign (assign env 4 (widthWord fs[j])) 3 (Desc.leadingWidth (fs.take (j + 1))).toUInt64 := by
        cases fixed : fs[j].fixedSize with
        | none =>
          have word : widthWord fs[j] = (none64 : Nat).toUInt64 := by simp [widthWord, fixed]
          refine ⟨_, Runs.ite_true 1 (by simp [eval, Expr.eq, assign, word, Cond.holds]) (by decide)
            (Runs.set _ _ _ _ _ 3 _ (Desc.leadingWidth (fs.take (j + 1))).toUInt64 ?_), rfl⟩
          simp [eval, assign, e3, aluResult, grown, fixed]
        | some width =>
          have notNone := widthWord_none fs[j] width fixed (narrow_width fs[j] (thin _ member) width fixed)
          have word : widthWord fs[j] = width.toUInt64 := by simp [widthWord, fixed]
          have notNone' : widthWord fs[j] ≠ 18446744073709551615 := by simpa using notNone
          refine ⟨_, Runs.ite_false (by simp [eval, Expr.eq, assign, Cond.holds, notNone'])
            (Runs.set _ _ _ _ _ 3 _ (Desc.leadingWidth (fs.take (j + 1))).toUInt64 ?_), rfl⟩
          simp [eval, assign, e3, aluResult, grown, fixed, word]
      obtain ⟨env₁, ranAdd, rfl⟩ := added
      have ranNext := Runs.call (m := m) (w := w) (sp := inner)
        (env := assign (assign env 4 (widthWord fs[j])) 3 (Desc.leadingWidth (fs.take (j + 1))).toUInt64)
        (args := [.var 0]) (dst := 0) (values := [(pos j).toUInt64]) (by simp [eval, assign, e0]) walked
      refine ⟨_, mem, Runs.block_cons ranWidth (Runs.block_cons ranAdd (Runs.block_cons ranNext
        (Runs.set _ _ _ _ _ 2 _ (j + 1).toUInt64 (by simp [eval, assign, e2, aluResult])))),
        ⟨j + 1, more, ?_, ?_, ?_, rfl, ?_⟩, ?_⟩
      · simp [assign]
      · simp [assign, e1]
      · simp [assign]
      · simp [assign]
      · simp [assign, e2, toNat_toUInt64 _ small, toNat_toUInt64 (j + 1) (by omega)]
        omega)
  let env₀ := assign (assign (entryEnv [q.toUInt64, fs.length.toUInt64]) 2 0) 3 0
  have first := Runs.set m w inner (entryEnv [q.toUInt64, fs.length.toUInt64]) mem 2 (.lit 0) 0 rfl
  have second := Runs.set m w inner (assign (entryEnv [q.toUInt64, fs.length.toUInt64]) 2 0) mem 3 (.lit 0) 0 rfl
  obtain ⟨env', mem', runs, ⟨j, within, e0, e1, e2, hmem, e3⟩, exit⟩ :=
    loop env₀ mem ⟨0, Nat.zero_le _, by simp [env₀, assign, entryEnv, pos, wordsAll], by simp [env₀, assign, entryEnv],
      by simp [env₀, assign], rfl, by simp [env₀, assign, Desc.leadingWidth]⟩
  subst mem'
  have done : j = fs.length := by
    have small : j < 2 ^ 64 := by omega
    simp only [Expr.lt, eval, e1, e2, Cond.holds] at exit
    simp [ofNat_lt_iff j _ small, lenMod] at exit
    omega
  subst done
  rw [List.take_length] at e3
  refine Calls.fn found (by omega) rfl (Runs.block_cons first (Runs.block_cons second runs)) ?_
  simp [planLeading, Fields.total, eval, e3]

end Ssz.Native.Driver
