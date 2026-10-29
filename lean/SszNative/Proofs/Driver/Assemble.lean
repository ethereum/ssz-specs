import SszNative.Proofs.Driver.Ranges

/-!
The assembly drivers write what `assemble` computes.

Parts sit in memory as a table of pairs, where each part starts and how many bytes it has.
A driver checks the parts whole, then writes the encoding to the output, or answers a code with nothing written.
-/

namespace Ssz.Native.Driver

open Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Plan

/-- Memory after bytes are written from an address. -/
def placed (mem : Memory) (out : Nat) (b : ByteArray) : Memory :=
  store mem out b.size (fun k => b.get! k)

/-- Parts in memory: a table of where each starts and its size, and each part's bytes, all readable. -/
structure PartsAt (w : World) (mem : Memory) (parts : Nat) (ps : List ByteArray) (ptrs : List Nat) : Prop where
  /-- One start per part. -/
  count : ptrs.length = ps.length
  /-- The program may read the table. -/
  table : w.access parts (16 * ps.length)
  /-- The table's first word of a pair is where the part starts. -/
  start : ∀ i (h : i < ps.length), readLE mem (parts + 16 * i) 8 = (ptrs[i]'(by omega)).toUInt64
  /-- The second word is its size. -/
  size : ∀ i (h : i < ps.length), readLE mem (parts + 16 * i + 8) 8 = ps[i].size.toUInt64
  /-- Each part's bytes are in memory. -/
  bytes : ∀ i (h : i < ps.length), BytesAt mem (ptrs[i]'(by omega)) ps[i]
  /-- The program may read them. -/
  readable : ∀ i (h : i < ps.length), w.access (ptrs[i]'(by omega)) ps[i].size

/-- An output the program may write, missing the parts' table and bytes. -/
structure OutAt (w : World) (parts : Nat) (ps : List ByteArray) (ptrs : List Nat) (out cap : Nat) : Prop where
  /-- The program may write it. -/
  writable : w.access out cap
  /-- It misses the table. -/
  apartTable : parts + 16 * ps.length ≤ out ∨ out + cap ≤ parts
  /-- It misses every part. -/
  apartParts : ∀ i (h : i < ptrs.length) (h' : i < ps.length), ptrs[i] + ps[i].size ≤ out ∨ out + cap ≤ ptrs[i]

/-- The code a driver answers for a refusal. -/
def errCode : Err → Nat
  | .overLimit _ _ | .scope _ _ => codeCount
  | .count _ _ => codePart
  | .offsetOverflow _ => codeOverflow
  | .unknownSelector _ | .badDeclaration | .unionSelectorRange _ _ _ => codeSelector
  | .paddingBits => codePadding
  | _ => codeType

/-- What an assembly driver answers for an encoding a reference computes, and the memory after. -/
def assembleOutcome (out cap : Nat) (mem : Memory) : Except Err ByteArray → UInt64 × Memory
  | .ok b => if b.size ≤ cap then (b.size.toUInt64, placed mem out b) else ((codeCapacity : Nat).toUInt64, mem)
  | .error e => ((errCode e).toUInt64, mem)

/-- The bytes of a byte array's parts, joined: the summing loop. -/
def joinSum : Stmt :=
  match joinBytes.body with
  | .seq _ (.seq _ (.seq _ (.seq loop _))) => loop
  | _ => .skip

/-- The bytes of a byte array's parts, joined: the copying loop. -/
def joinCopy : Stmt :=
  match joinBytes.body with
  | .seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.ite _ (.seq _ (.ite _ (.seq _ (.ite _ (.seq _ (.ite _
      (.seq _ (.seq _ (.seq loop _))) _)) _)) _)) _))))) => loop
  | _ => .skip

/-- The byte array driver: sum the sizes, check them, then copy the parts one after the other. -/
theorem joinBytes_body : joinBytes.body =
    .seq (.set 8 (.lit 0)) (.seq (.set 9 (.lit 0)) (.seq (.set 7 (.lit 0)) (.seq (.loop (loopCond joinSum) (loopBody joinSum))
      (.seq (.set 6 (.lit (codeCount : Nat).toUInt64))
        (.ite (Expr.eq (.var 9) 0)
          (.seq (.ite (.var 3) (.ite (Expr.eq (.var 8) (.var 2)) (.set 6 0) .skip)
              (.ite (Expr.le (.var 8) (.var 2)) (.set 6 0) .skip))
            (.ite (Expr.eq (.var 6) 0)
              (.seq (.set 6 (.lit (codeOverflow : Nat).toUInt64))
                (.ite (Expr.lt (.var 8) (.lit (offsetLimit : Nat).toUInt64))
                  (.seq (.set 6 (.lit (codeCapacity : Nat).toUInt64))
                    (.ite (Expr.le (.var 8) (.var 5))
                      (.seq (.set 8 0) (.seq (.set 7 0) (.seq (.loop (loopCond joinCopy) (loopBody joinCopy))
                        (.set 6 (.var 8))))) .skip)) .skip)) .skip)) .skip))))) := rfl

/-- The sizes are summed while parts are left. -/
theorem joinSum_cond : loopCond joinSum = Expr.lt (.var 7) (.var 1) := rfl

/-- One more size, noting when the sum passes what a word holds. -/
theorem joinSum_body : loopBody joinSum =
    .block [.set 10 (Expr.var 8 + Expr.ld (Expr.var 0 + 16 * Expr.var 7 + 8)),
      .ite (Expr.lt (.var 10) (.var 8)) (.block [.set 9 1]) .skip, .set 8 (.var 10), .set 7 (.var 7 + 1)] := rfl

/-- The parts are copied while parts are left. -/
theorem joinCopy_cond : loopCond joinCopy = Expr.lt (.var 7) (.var 1) := rfl

/-- One more part copied after the others. -/
theorem joinCopy_body : loopBody joinCopy =
    .block [.call "ssz_copy" [Expr.var 4 + Expr.var 8, Expr.ld (Expr.var 0 + 16 * Expr.var 7),
        Expr.ld (Expr.var 0 + 16 * Expr.var 7 + 8)] 11,
      .set 8 (Expr.var 8 + Expr.ld (Expr.var 0 + 16 * Expr.var 7 + 8)), .set 7 (.var 7 + 1)] := rfl

/-- The sizes of the first parts, summed. -/
def sizesUpTo (ps : List ByteArray) (i : Nat) : Nat := ((ps.take i).map ByteArray.size).sum

/-- One more part adds its size. -/
theorem sizesUpTo_succ (ps : List ByteArray) (i : Nat) (h : i < ps.length) :
    sizesUpTo ps (i + 1) = sizesUpTo ps i + ps[i].size := by
  unfold sizesUpTo
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, List.map_append, List.sum_append]
  simp

/-- Joining parts one after the other joins the first, then the rest. -/
theorem joinParts_append : ∀ (a b : List ByteArray), joinParts (a ++ b) = joinParts a ++ joinParts b
  | [], b => by simp [joinParts]
  | x :: a, b => by simp [joinParts, joinParts_append a b, ByteArray.append_assoc]

/-- The first parts and one more, joined. -/
theorem joinParts_take_succ (ps : List ByteArray) (i : Nat) (h : i < ps.length) :
    joinParts (ps.take (i + 1)) = joinParts (ps.take i) ++ ps[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, joinParts_append]
  simp [joinParts]

/-- Joined parts are as long as the parts' sizes summed. -/
theorem joinParts_size (ps : List ByteArray) (i : Nat) : (joinParts (ps.take i)).size = sizesUpTo ps i := by
  induction ps generalizing i with
  | nil => simp [joinParts, sizesUpTo]
  | cons x rest ih =>
    cases i with
    | zero => simp [joinParts, sizesUpTo]
    | succ i =>
      have := ih i
      simp only [sizesUpTo] at this ⊢
      simp [joinParts, ByteArray.size_append, this]

/-- Placing nothing changes nothing. -/
theorem placed_empty (mem : Memory) (out : Nat) : placed mem out .empty = mem := by
  funext x; simp [placed, store]; intros; omega

/-- A part copied right after bytes already placed extends them, when the part lies away from the output. -/
theorem copied_placed (mem : Memory) (out : Nat) (J part : ByteArray) (p : Nat) (bytes : BytesAt mem p part)
    (apart : p + part.size ≤ out ∨ out + (J.size + part.size) ≤ p) :
    copied (placed mem out J) (out + J.size) p part.size = placed mem out (J ++ part) := by
  funext x
  simp only [copied, placed, store, ByteArray.size_append]
  by_cases inside : out + J.size ≤ x ∧ x < out + J.size + part.size
  · have away : ¬ (out ≤ p + (x - (out + J.size)) ∧ p + (x - (out + J.size)) < out + J.size) := by omega
    have whole : out ≤ x ∧ x < out + (J.size + part.size) := by omega
    rw [if_pos inside, if_neg away, if_pos whole, bytes _ (by omega),
      show x - out = J.size + (x - (out + J.size)) by omega, Kernel.get!_append_right]
  · rw [if_neg inside]
    by_cases before : out ≤ x ∧ x < out + J.size
    · have whole : out ≤ x ∧ x < out + (J.size + part.size) := by omega
      rw [if_pos before, if_pos whole, Kernel.get!_append_left _ _ _ (by omega)]
    · have outside : ¬ (out ≤ x ∧ x < out + (J.size + part.size)) := by omega
      rw [if_neg before, if_neg outside]

/-- A table address, from the table's start and a part's index, does not wrap. -/
theorem table_addr (parts i : Nat) (small : parts + 16 * i + 8 < 2 ^ 64) :
    (UInt64.ofNat parts + 16 * UInt64.ofNat i).toNat = parts + 16 * i ∧
      (UInt64.ofNat parts + 16 * UInt64.ofNat i + 8).toNat = parts + 16 * i + 8 := by
  have h16 : (16 * UInt64.ofNat i).toNat = 16 * i := by
    rw [UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; simp; omega
  have h0 : (UInt64.ofNat parts + 16 * UInt64.ofNat i).toNat = parts + 16 * i := by
    rw [UInt64.toNat_add, h16, UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; omega
  refine ⟨h0, ?_⟩
  rw [UInt64.toNat_add, h0]; simp; omega

/-- A part's pair of words, read from memory that still holds the table. -/
theorem PartsAt.read {w : World} {mem : Memory} {parts : Nat} {ps : List ByteArray} {ptrs : List Nat}
    (at_ : PartsAt w mem parts ps ptrs) (env : Env) (cur : Memory) (i : Nat) (hi : i < ps.length) (index : Nat)
    (e0 : env 0 = parts.toUInt64) (ei : env index = i.toUInt64)
    (kept : ∀ x, parts ≤ x → x < parts + 16 * ps.length → cur x = mem x) :
    eval w env cur (Expr.ld (Expr.var 0 + 16 * Expr.var index + 8)) = some ps[i].size.toUInt64 ∧
      eval w env cur (Expr.ld (Expr.var 0 + 16 * Expr.var index)) =
        some (ptrs[i]'(by rw [at_.count]; exact hi)).toUInt64 := by
  have bound : parts + 16 * ps.length ≤ 2 ^ 63 := by
    have := at_.table
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  obtain ⟨a0, a8⟩ := table_addr parts i (by omega)
  have same : ∀ c, c + 8 ≤ 16 → readLE cur (parts + 16 * i + c) 8 = readLE mem (parts + 16 * i + c) 8 :=
    fun c hc => readLE_congr _ _ _ _ (fun k hk => kept _ (by omega) (by omega))
  have acc : ∀ c, c + 8 ≤ 16 → w.access (parts + 16 * i + c) 8 :=
    fun c hc => access_sub at_.table (by omega) (by omega)
  have s8 := same 8 (by omega)
  have s0 := same 0 (by omega)
  have c8 := acc 8 (by omega)
  have c0 := acc 0 (by omega)
  simp only [Nat.add_zero] at s0 c0
  constructor
  · evaluate [e0, ei, a8, s8, c8, at_.size i hi]
  · evaluate [e0, ei, a0, s0, c0, at_.start i hi]

/-- A comparison below or equal, as its condition on the words. -/
theorem eval_cmp_le {w : World} {env : Env} {mem : Memory} {a b : Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (Expr.le a b) = some (if x ≤ y then 1 else 0) := by
  rw [show Expr.le a b = .cmp .be a b from rfl, eval_cmp .be ha hb, holds_be]
  by_cases h : x ≤ y <;> simp [h]

/-- An equality test, as its condition on the words. -/
theorem eval_cmp_eq {w : World} {env : Env} {mem : Memory} {a b : Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (Expr.eq a b) = some (if x = y then 1 else 0) := by
  rw [show Expr.eq a b = .cmp .e a b from rfl, eval_cmp .e ha hb]
  by_cases h : x = y <;> simp [h, Cond.holds]

/-- More parts sum to at least as much. -/
theorem sizesUpTo_le (ps : List ByteArray) (i : Nat) : ∀ j, i ≤ j → j ≤ ps.length → sizesUpTo ps i ≤ sizesUpTo ps j
  | 0, h, _ => by rw [show i = 0 by omega]; exact Nat.le_refl _
  | j + 1, h, hj => by
    by_cases same : i = j + 1
    · rw [same]; exact Nat.le_refl _
    · have := sizesUpTo_le ps i j (by omega) (by omega)
      rw [sizesUpTo_succ ps j (by omega)]; omega

/-- A byte array's reference, with its checks spelled out on the joined size. -/
theorem assemble_bytes (exact : Bool) (n : Nat) (ps : List ByteArray) :
    assemble (if exact then .byteVector n else .byteList n) ps =
      if (if exact then (joinParts ps).size = n else (joinParts ps).size ≤ n) then
        (if (joinParts ps).size ≥ offsetBound then .error (.offsetOverflow (joinParts ps).size)
          else .ok (joinParts ps))
      else .error (if exact then .scope n (joinParts ps).size else .overLimit n (joinParts ps).size) := by
  cases exact <;>
    by_cases h1 : (joinParts ps).size ≤ n <;> by_cases h2 : (joinParts ps).size = n <;>
      by_cases h3 : (joinParts ps).size ≥ offsetBound <;>
        simp_all [assemble, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure] <;> omega

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/-- A byte array's encoding from parts: the driver joins them, or refuses as `assemble` does. -/
theorem join_ok (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory)
    (parts out cap n : Nat) (exact : Bool) (ps : List ByteArray) (ptrs : List Nat)
    (at_ : PartsAt w mem parts ps ptrs) (to : OutAt w parts ps ptrs out cap) (smallN : n < 2 ^ 64)
    (room : w.stackLo + 8 + 8 * joinBytes.frame + (8 + 8 * copyBytes.frame) ≤ sp) :
    Calls m w "ssz_assemble_bytes" sp
      [parts.toUInt64, ps.length.toUInt64, n.toUInt64, if exact then 1 else 0, out.toUInt64, cap.toUInt64] mem
      (assembleOutcome out cap mem (assemble (if exact then .byteVector n else .byteList n) ps)).1
      (assembleOutcome out cap mem (assemble (if exact then .byteVector n else .byteList n) ps)).2 := by
  have found : m.fns.lookup "ssz_assemble_bytes" = some joinBytes := linked ("ssz_assemble_bytes", joinBytes) (by simp [codecFns])
  have tableBound : parts + 16 * ps.length ≤ 2 ^ 63 := by
    have := at_.table
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have outBound : out + cap ≤ 2 ^ 63 := by
    have := to.writable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have partBound : ∀ i (h : i < ps.length), (ptrs[i]'(by rw [at_.count]; exact h)) + ps[i].size ≤ 2 ^ 63 := by
    intro i h
    have := at_.readable i h
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  let N := ps.length
  let inner := sp - 8 - 8 * joinBytes.frame
  let args := [parts.toUInt64, N.toUInt64, n.toUInt64, if exact then (1 : UInt64) else 0, out.toUInt64,
    cap.toUInt64]
  have finish : ∀ env' mem' (r : UInt64), Runs m w inner (entryEnv args) mem joinBytes.body env' mem' →
      env' 6 = r → Calls m w "ssz_assemble_bytes" sp args mem r mem' := by
    intro env' mem' r main answer
    exact Calls.fn (env' := env') found (by omega) rfl main (by simp [joinBytes, Bytes_.r, eval, answer])
  -- The sum loop: after i parts, the sum of their sizes, with a note once it passes what a word holds.
  let inv₁ : Env → Memory → Prop := fun env cur => mem = cur ∧ (∀ k, k < 6 → env k = args.getD k 0) ∧
    ∃ i, i ≤ N ∧ env 7 = i.toUInt64 ∧ env 8 = (sizesUpTo ps i).toUInt64 ∧
      ((env 9 = 0 ∧ sizesUpTo ps i < 2 ^ 64) ∨ (env 9 = 1 ∧ 2 ^ 64 ≤ sizesUpTo ps i))
  have loop₁ := Runs.loop_inv (m := m) (w := w) (sp := inner) (c := Expr.lt (.var 7) (.var 1)) (body := loopBody joinSum)
    inv₁ (fun env _ => N - (env 7).toNat) (fun env cur _ => ⟨_, rfl⟩)
    (by
      intro env cur v hinv cond nonzero
      obtain ⟨hm, keep, i, within, e7, e8, e9⟩ := hinv
      subst hm
      have small : i < 2 ^ 64 := by omega
      have more : i < N := by
        simp only [Expr.lt, eval, e7, keep 1 (by decide), Cond.holds] at cond
        simp [args] at cond
        by_cases done : i < N
        · exact done
        · simp [ofNat_lt_ofNat i N small (by omega), done] at cond
          exact absurd cond.symm nonzero
      obtain ⟨readSize, -⟩ := at_.read env mem i more 7 (by rw [keep 0 (by decide)]; rfl) e7 (fun _ _ _ => rfl)
      have z := partBound i more
      have next := sizesUpTo_succ ps i more
      generalize sizesUpTo ps i = a at e8 e9 next
      generalize ps[i].size = b at readSize z next
      -- The sum wraps exactly when the old sum, cut to a word, and the size pass what a word holds.
      have sumNat : ((a.toUInt64 + b.toUInt64 : UInt64)).toNat = (a % 2 ^ 64 + b) % 2 ^ 64 := by
        rw [UInt64.toNat_add]; simp [UInt64.toNat_ofNat]
      have carry : (a.toUInt64 + b.toUInt64 < a.toUInt64) ↔ 2 ^ 64 ≤ a % 2 ^ 64 + b := by
        rw [UInt64.lt_iff_toNat_lt, sumNat]; simp [UInt64.toNat_ofNat]; omega
      let env₁ := assign env 10 (a.toUInt64 + b.toUInt64)
      have s10 : Runs m w inner env mem (.set 10 (Expr.var 8 + Expr.ld (Expr.var 0 + 16 * Expr.var 7 + 8))) env₁ mem :=
        Runs.set _ _ _ _ _ 10 _ _ (by
          simp only [show (Expr.var 8 + Expr.ld (Expr.var 0 + 16 * Expr.var 7 + 8)) =
            .op .add (.var 8) (Expr.ld (Expr.var 0 + 16 * Expr.var 7 + 8)) from rfl, eval, readSize, e8]
          rfl)
      let wrap' : UInt64 := if 2 ^ 64 ≤ a % 2 ^ 64 + b then 1 else env 9
      have test : Runs m w inner env₁ mem (.ite (Expr.lt (.var 10) (.var 8)) (.block [.set 9 1]) .skip)
          (assign env₁ 9 wrap') mem := by
        by_cases over : 2 ^ 64 ≤ a % 2 ^ 64 + b
        · have one : wrap' = 1 := by simp [wrap', over]
          rw [one]
          refine Runs.ite_true 1 ?_ (by decide) (Runs.set m w inner env₁ mem 9 1 1 rfl)
          simp [Expr.lt, eval, env₁, assign, e8, Cond.holds, carry.mpr over]
        · have same : assign env₁ 9 wrap' = env₁ := by
            funext x; by_cases h : x = 9 <;> simp [assign, wrap', over, h, env₁, e9]
          rw [same]
          refine Runs.ite_false ?_ (Runs.skip _ _ _ _ _)
          simp [Expr.lt, eval, env₁, assign, e8, Cond.holds, show ¬ (a.toUInt64 + b.toUInt64 < a.toUInt64) from
            fun h => over (carry.mp h)]
      refine ⟨assign (assign (assign env₁ 9 wrap') 8 (a.toUInt64 + b.toUInt64)) 7 (i + 1).toUInt64, mem, ?_,
        ⟨rfl, ?_, i + 1, more, ?_, ?_, ?_⟩, ?_⟩
      · rw [joinSum_body]
        exact Runs.block_cons s10 (Runs.block_cons test (Runs.block_cons
          (Runs.set _ _ _ _ _ 8 _ _ (by simp [eval, assign, env₁]))
          (Runs.set _ _ _ _ _ 7 _ _ (by simp [eval, assign, e7, aluResult, env₁]))))
      · intro k hk
        simp [assign, env₁, show k ≠ 7 by omega, show k ≠ 8 by omega, show k ≠ 9 by omega, show k ≠ 10 by omega,
          keep k hk]
      · simp [assign]
      · simp [assign, next]
      · simp only [assign, if_neg (show (9 : Nat) ≠ 7 by decide), if_neg (show (9 : Nat) ≠ 8 by decide), if_pos rfl,
          wrap', next]
        rcases e9 with ⟨w0, lo⟩ | ⟨w1, hi⟩
        · by_cases over : 2 ^ 64 ≤ a % 2 ^ 64 + b
          · right; exact ⟨by simp [over], by omega⟩
          · left; exact ⟨by simp [over, w0], by omega⟩
        · right
          refine ⟨?_, by omega⟩
          by_cases o : 2 ^ 64 ≤ a % 2 ^ 64 + b <;> simp [o, w1]
      · simp [assign, e7, toNat_toUInt64 _ small, toNat_toUInt64 (i + 1) (by omega)]
        omega)
  -- The copy loop: after i parts, they are written one after the other.
  let inv₂ : Env → Memory → Prop := fun env cur => (∀ k, k < 6 → env k = args.getD k 0) ∧
    ∃ i, i ≤ N ∧ env 7 = i.toUInt64 ∧ env 8 = (sizesUpTo ps i).toUInt64 ∧
      cur = placed mem out (joinParts (ps.take i))
  have loop₂ : sizesUpTo ps N ≤ cap → ∀ env cur, inv₂ env cur → ∃ env' cur',
      Runs m w inner env cur (.loop (Expr.lt (.var 7) (.var 1)) (loopBody joinCopy)) env' cur' ∧ inv₂ env' cur' ∧
        eval w env' cur' (Expr.lt (.var 7) (.var 1)) = some 0 := by
    intro fits
    refine Runs.loop_inv (m := m) (w := w) (sp := inner) (c := Expr.lt (.var 7) (.var 1)) (body := loopBody joinCopy)
      inv₂ (fun env _ => N - (env 7).toNat) (fun env cur _ => ⟨_, rfl⟩) ?_
    intro env cur v hinv cond nonzero
    obtain ⟨keep, i, within, e7, e8, hc⟩ := hinv
    have small : i < 2 ^ 64 := by omega
    have more : i < N := by
      simp only [Expr.lt, eval, e7, keep 1 (by decide), Cond.holds] at cond
      simp [args] at cond
      by_cases done : i < N
      · exact done
      · simp [ofNat_lt_ofNat i N small (by omega), done] at cond
        exact absurd cond.symm nonzero
    have upTo := sizesUpTo_le ps (i + 1) N (by omega) (Nat.le_refl _)
    have next := sizesUpTo_succ ps i more
    have sizeJ := joinParts_size ps i
    have sizeJ' := joinParts_size ps (i + 1)
    -- The table and the parts lie away from the output, so they read as before.
    have away : ∀ x, (x < out ∨ out + cap ≤ x) → cur x = mem x := by
      intro x far
      rw [hc]; simp only [placed, store]
      rw [if_neg (by rw [sizeJ]; omega)]
    have tableKept : ∀ x, parts ≤ x → x < parts + 16 * ps.length → cur x = mem x := by
      intro x lo hi; apply away; have := to.apartTable; omega
    obtain ⟨readSize, readStart⟩ := at_.read env cur i more 7 (by rw [keep 0 (by decide)]; rfl) e7 tableKept
    have ptrLen : i < ptrs.length := by rw [at_.count]; exact more
    have z := partBound i more
    have apartPart := to.apartParts i ptrLen more
    have copiedNow := copy_correct m w linked inner cur (out + sizesUpTo ps i).toUInt64 (ptrs[i]).toUInt64
      ps[i].size.toUInt64 (by simp only [inner]; omega)
      (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]; exact at_.readable i more)
      (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]
          exact access_sub to.writable (by omega) (by omega))
      (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]; omega)
    have memEq : copied (placed mem out (joinParts (ps.take i))) (out + sizesUpTo ps i) ptrs[i] ps[i].size =
        placed mem out (joinParts (ps.take (i + 1))) := by
      rw [← sizeJ, copied_placed mem out _ _ _ (fun k hk => at_.bytes i more k hk) (by rw [sizeJ]; omega),
        ← joinParts_take_succ ps i more]
    rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), hc, memEq]
      at copiedNow
    -- After the copy, the table still reads as before.
    have r8 : eval w (assign env 11 0) (placed mem out (joinParts (ps.take (i + 1))))
        (Expr.ld (Expr.var 0 + 16 * Expr.var 7 + 8)) = some ps[i].size.toUInt64 :=
      (at_.read (assign env 11 0) _ i more 7 (by simp [assign, keep 0 (by decide), args]) (by simp [assign, e7])
        (fun x lo hi => by
          have := to.apartTable
          simp only [placed, store]
          rw [if_neg (by rw [sizeJ']; omega)])).1
    refine ⟨assign (assign (assign env 11 0) 8 (sizesUpTo ps (i + 1)).toUInt64) 7 (i + 1).toUInt64,
      placed mem out (joinParts (ps.take (i + 1))), ?_, ⟨?_, i + 1, more, ?_, ?_, rfl⟩, ?_⟩
    · rw [joinCopy_body, hc]
      refine Runs.block_cons (Runs.call (values := [(out + sizesUpTo ps i).toUInt64, (ptrs[i]).toUInt64,
        ps[i].size.toUInt64]) ?_ copiedNow) (Runs.block_cons (Runs.set _ _ _ _ _ 8 _ _ ?_)
          (Runs.set _ _ _ _ _ 7 _ _ (by simp [eval, assign, e7, aluResult])))
      · rw [← hc]
        simp only [List.mapM_cons, List.mapM_nil, readSize, readStart]
        simp [eval, keep 4 (by decide), args, e8, aluResult]
      · simp only [show (Expr.var 8 + Expr.ld (Expr.var 0 + 16 * Expr.var 7 + 8)) =
          .op .add (.var 8) (Expr.ld (Expr.var 0 + 16 * Expr.var 7 + 8)) from rfl, eval, r8]
        simp [assign, e8, next, aluResult]
    · intro k hk
      simp [assign, show k ≠ 7 by omega, show k ≠ 8 by omega, show k ≠ 11 by omega, keep k hk]
    · simp [assign]
    · simp [assign]
    · simp [assign, e7, toNat_toUInt64 _ small, toNat_toUInt64 (i + 1) (by omega)]
      omega
  -- Before the sum loop, everything starts at zero.
  let env₀ := assign (assign (assign (entryEnv args) 8 0) 9 0) 7 0
  obtain ⟨env₁, mem₁, ran₁, ⟨hm, keep₁, i, within, e7, e8, e9⟩, exit₁⟩ := loop₁ env₀ mem
    ⟨rfl, fun k hk => by simp [env₀, assign, entryEnv, show k ≠ 7 by omega, show k ≠ 8 by omega,
      show k ≠ 9 by omega], 0, Nat.zero_le _, by simp [env₀, assign], by simp [env₀, assign, sizesUpTo],
      Or.inl ⟨by simp [env₀, assign], by simp [sizesUpTo]⟩⟩
  subst hm
  have reached : i = N := by
    have small : i < 2 ^ 64 := by omega
    simp only [Expr.lt, eval, e7, keep₁ 1 (by decide), Cond.holds] at exit₁
    simp [args, ofNat_lt_ofNat i N small (by omega)] at exit₁
    omega
  subst reached
  have whole : ps.take N = ps := List.take_of_length_le (Nat.le_refl _)
  have sizeS : (joinParts ps).size = sizesUpTo ps N := by rw [← joinParts_size ps N, whole]
  rw [assemble_bytes, sizeS]
  -- The start of the body, through the sum loop and the refusal code.
  have head : ∀ env' mem' r, Runs m w inner (assign env₁ 6 (codeCount : Nat).toUInt64) mem
      (.ite (Expr.eq (.var 9) 0)
          (.seq (.ite (.var 3) (.ite (Expr.eq (.var 8) (.var 2)) (.set 6 0) .skip)
              (.ite (Expr.le (.var 8) (.var 2)) (.set 6 0) .skip))
            (.ite (Expr.eq (.var 6) 0)
              (.seq (.set 6 (.lit (codeOverflow : Nat).toUInt64))
                (.ite (Expr.lt (.var 8) (.lit (offsetLimit : Nat).toUInt64))
                  (.seq (.set 6 (.lit (codeCapacity : Nat).toUInt64))
                    (.ite (Expr.le (.var 8) (.var 5))
                      (.seq (.set 8 0) (.seq (.set 7 0) (.seq (.loop (loopCond joinCopy) (loopBody joinCopy))
                        (.set 6 (.var 8))))) .skip)) .skip)) .skip)) .skip) env' mem' →
      env' 6 = r → Calls m w "ssz_assemble_bytes" sp args mem r mem' := by
    intro env' mem' r tail answer
    refine finish env' mem' r ?_ answer
    rw [joinBytes_body]
    exact Runs.seq (Runs.set _ _ _ _ _ 8 _ _ rfl) (Runs.seq (Runs.set _ _ _ _ _ 9 _ _ rfl)
      (Runs.seq (Runs.set _ _ _ _ _ 7 _ _ rfl) (Runs.seq ran₁ (Runs.seq (Runs.set _ _ _ _ _ 6 _ _ rfl) tail))))
  have a2 : env₁ 2 = n.toUInt64 := by rw [keep₁ 2 (by decide)]; rfl
  have a3 : env₁ 3 = if exact then 1 else 0 := by rw [keep₁ 3 (by decide)]; rfl
  have a5 : env₁ 5 = cap.toUInt64 := by rw [keep₁ 5 (by decide)]; rfl
  rcases e9 with ⟨w0, fitsWord⟩ | ⟨w1, wraps⟩
  case inr =>
    -- The sum passed what a word holds: far past any length or limit.
    have no : ¬ (if exact then sizesUpTo ps N = n else sizesUpTo ps N ≤ n) := by cases exact <;> simp <;> omega
    rw [if_neg no]
    exact head _ mem _ (Runs.ite_false (by simp [Expr.eq, eval, assign, w1, Cond.holds]) (Runs.skip _ _ _ _ _))
      (by cases exact <;> simp [assign, errCode, assembleOutcome])
  -- The sum fits a word, so the word is the sum.
  have sumWord : ∀ c : Nat, c < 2 ^ 64 →
      ((sizesUpTo ps N).toUInt64 = c.toUInt64 ↔ sizesUpTo ps N = c) ∧
      ((sizesUpTo ps N).toUInt64 ≤ c.toUInt64 ↔ sizesUpTo ps N ≤ c) ∧
      ((sizesUpTo ps N).toUInt64 < c.toUInt64 ↔ sizesUpTo ps N < c) := fun c hc =>
    ⟨ofNat_eq_ofNat _ c fitsWord hc, ofNat_le_iff _ c fitsWord hc, ofNat_lt_ofNat _ c fitsWord hc⟩
  have capSmall : cap < 2 ^ 64 := by omega
  let env₂ := assign env₁ 6 (codeCount : Nat).toUInt64
  by_cases fits : (if exact then sizesUpTo ps N = n else sizesUpTo ps N ≤ n)
  case neg =>
    -- A size the type does not allow: the refusal code stays.
    rw [if_neg fits]
    have check : Runs m w inner env₂ mem (.ite (.var 3) (.ite (Expr.eq (.var 8) (.var 2)) (.set 6 0) .skip)
        (.ite (Expr.le (.var 8) (.var 2)) (.set 6 0) .skip)) env₂ mem := by
      cases exact
      · refine Runs.ite_false (by simp [eval, env₂, assign, a3]) (Runs.ite_false ?_ (Runs.skip _ _ _ _ _))
        simp at fits
        rw [eval_cmp_le (x := (sizesUpTo ps N).toUInt64) (y := n.toUInt64) (by simp [eval, env₂, assign, e8])
          (by simp [eval, env₂, assign, a2]), if_neg (fun h => by have := (sumWord n smallN).2.1.mp h; omega)]
      · refine Runs.ite_true 1 (by simp [eval, env₂, assign, a3]) (by decide)
          (Runs.ite_false ?_ (Runs.skip _ _ _ _ _))
        simp at fits
        rw [eval_cmp_eq (x := (sizesUpTo ps N).toUInt64) (y := n.toUInt64) (by simp [eval, env₂, assign, e8])
          (by simp [eval, env₂, assign, a2]), if_neg (fun h => by have := (sumWord n smallN).1.mp h; omega)]
    exact head env₂ mem _ (Runs.ite_true 1 (by simp [Expr.eq, eval, env₂, assign, w0, Cond.holds]) (by decide)
      (Runs.seq check (Runs.ite_false (by simp [Expr.eq, eval, env₂, assign, Cond.holds]; decide)
        (Runs.skip _ _ _ _ _))))
      (by cases exact <;> simp [env₂, assign, errCode, assembleOutcome])
  rw [if_pos fits]
  let env₃ := assign env₂ 6 0
  have check : Runs m w inner env₂ mem (.ite (.var 3) (.ite (Expr.eq (.var 8) (.var 2)) (.set 6 0) .skip)
      (.ite (Expr.le (.var 8) (.var 2)) (.set 6 0) .skip)) env₃ mem := by
    cases exact
    · refine Runs.ite_false (by simp [eval, env₂, assign, a3]) (Runs.ite_true 1 ?_ (by decide)
        (Runs.set _ _ _ _ _ 6 _ _ rfl))
      simp at fits
      rw [eval_cmp_le (x := (sizesUpTo ps N).toUInt64) (y := n.toUInt64) (by simp [eval, env₂, assign, e8])
        (by simp [eval, env₂, assign, a2]), if_pos ((sumWord n smallN).2.1.mpr fits)]
    · refine Runs.ite_true 1 (by simp [eval, env₂, assign, a3]) (by decide) (Runs.ite_true 1 ?_ (by decide)
        (Runs.set _ _ _ _ _ 6 _ _ rfl))
      simp at fits
      rw [eval_cmp_eq (x := (sizesUpTo ps N).toUInt64) (y := n.toUInt64) (by simp [eval, env₂, assign, e8])
        (by simp [eval, env₂, assign, a2]), if_pos ((sumWord n smallN).1.mpr fits)]
  have limitSmall : (offsetLimit : Nat) < 2 ^ 64 := by decide
  by_cases big : sizesUpTo ps N ≥ offsetBound
  · -- Past what a four-byte offset names.
    rw [if_pos big]
    refine head _ mem _ (Runs.ite_true 1 (by simp [Expr.eq, eval, env₂, assign, w0, Cond.holds]) (by decide)
      (Runs.seq check (Runs.ite_true 1 (by simp [Expr.eq, eval, env₃, assign, Cond.holds]) (by decide)
        (Runs.seq (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_false ?_ (Runs.skip _ _ _ _ _))))))
      (by simp [assign, errCode, assembleOutcome])
    simp [Expr.lt, eval, env₃, env₂, assign, e8, Cond.holds, (sumWord _ limitSmall).2.2]
    simp [offsetBound] at big; omega
  rw [if_neg big]
  simp only [assembleOutcome, sizeS]
  have inLimit : eval w (assign env₃ 6 (codeOverflow : Nat).toUInt64) mem
      (Expr.lt (.var 8) (.lit (offsetLimit : Nat).toUInt64)) = some 1 := by
    simp [Expr.lt, eval, env₃, env₂, assign, e8, Cond.holds, (sumWord _ limitSmall).2.2]
    simp [offsetBound] at big; omega
  let env₄ := assign (assign env₃ 6 (codeOverflow : Nat).toUInt64) 6 (codeCapacity : Nat).toUInt64
  by_cases room' : sizesUpTo ps N ≤ cap
  · rw [if_pos room']
    obtain ⟨env₅, mem₅, ran₂, ⟨keep₅, i, within', f7, f8, f9⟩, exit₂⟩ := loop₂ room'
      (assign (assign env₄ 8 0) 7 0) mem
      ⟨fun k hk => by simp [env₄, env₃, env₂, assign, show k ≠ 6 by omega, show k ≠ 7 by omega,
        show k ≠ 8 by omega, keep₁ k hk], 0, Nat.zero_le _, by simp [assign], by simp [assign, sizesUpTo],
        by simp [joinParts, placed_empty]⟩
    have done : i = N := by
      have small : i < 2 ^ 64 := by omega
      simp only [Expr.lt, eval, f7, keep₅ 1 (by decide), Cond.holds] at exit₂
      simp [args, ofNat_lt_ofNat i N small (by omega)] at exit₂
      omega
    subst done
    rw [whole] at f9
    subst f9
    refine head _ _ _ (Runs.ite_true 1 (by simp [Expr.eq, eval, env₂, assign, w0, Cond.holds]) (by decide)
      (Runs.seq check (Runs.ite_true 1 (by simp [Expr.eq, eval, env₃, assign, Cond.holds]) (by decide)
        (Runs.seq (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_true 1 inLimit (by decide)
          (Runs.seq (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_true 1 ?_ (by decide)
            (Runs.seq (Runs.set _ _ _ _ _ 8 _ _ rfl) (Runs.seq (Runs.set _ _ _ _ _ 7 _ _ rfl)
              (Runs.seq ran₂ (Runs.set _ _ _ _ _ 6 _ _ rfl))))))))))) (by simp [assign, f8])
    rw [eval_cmp_le (x := (sizesUpTo ps N).toUInt64) (y := cap.toUInt64) (by simp [eval, env₄, env₃, env₂, assign, e8])
      (by simp [eval, env₄, env₃, env₂, assign, a5]), if_pos ((sumWord _ capSmall).2.1.mpr room')]
  · -- Too big for the output.
    rw [if_neg room']
    refine head _ mem _ (Runs.ite_true 1 (by simp [Expr.eq, eval, env₂, assign, w0, Cond.holds]) (by decide)
      (Runs.seq check (Runs.ite_true 1 (by simp [Expr.eq, eval, env₃, assign, Cond.holds]) (by decide)
        (Runs.seq (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_true 1 inLimit (by decide)
          (Runs.seq (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_false ?_ (Runs.skip _ _ _ _ _)))))))) (by simp [assign])
    rw [eval_cmp_le (x := (sizesUpTo ps N).toUInt64) (y := cap.toUInt64) (by simp [eval, env₄, env₃, env₂, assign, e8])
      (by simp [eval, env₄, env₃, env₂, assign, a5]), if_neg (fun h => room' ((sumWord _ capSmall).2.1.mp h))]

/-! ## Bit lists -/

/-- A byte past the ones placed, placed too. -/
theorem placed_push (mem : Memory) (out : Nat) (J : ByteArray) (f : Nat → UInt8) :
    store (placed mem out J) (out + J.size) 1 f = placed mem out (J.push (f 0)) := by
  funext x
  simp only [placed, store, ByteArray.size_push]
  by_cases last : x = out + J.size
  · subst last
    rw [if_pos (by omega), if_pos (by omega), Nat.sub_self, show out + J.size - out = J.size by omega]
    rw [Kernel.get!_eq _ _ (by simp)]
    cases J with
    | mk d => exact Array.getElem_push_eq.symm
  · rw [if_neg (by omega)]
    by_cases inside : out ≤ x ∧ x < out + J.size
    · rw [if_pos inside, if_pos (by omega), Kernel.get!_eq (J.push (f 0)) (x - out) (by rw [ByteArray.size_push]; omega), Kernel.get!_eq J (x - out) (by omega)]
      cases J with
      | mk d => exact (Array.getElem_push_lt (by simp [ByteArray.size] at inside ⊢; omega)).symm
    · rw [if_neg inside, if_neg (by omega)]

/-- A byte array with one byte changed, at its place. -/
theorem get!_set (J : ByteArray) (i : Nat) (v : UInt8) (k : Nat) (h : k < J.size) :
    (J.set! i v).get! k = if i = k then v else J.get! k := by
  cases J with
  | mk d =>
    show (ByteArray.mk (d.setIfInBounds i v)).get! k = _
    have h' : k < d.size := h
    rw [Kernel.get!_eq _ _ (by simp [ByteArray.size]; exact h'), Kernel.get!_eq _ _ h]
    simp only [ByteArray.getElem_eq_getElem_data]
    rw [Array.getElem_setIfInBounds]

/-- One placed byte stored over, placed so. -/
theorem placed_set (mem : Memory) (out : Nat) (J : ByteArray) (i : Nat) (inside : i < J.size) (f : Nat → UInt8) :
    store (placed mem out J) (out + i) 1 f = placed mem out (J.set! i (f 0)) := by
  funext x
  simp only [placed, store, ByteArray.size_set!]
  by_cases here : x = out + i
  · subst here
    rw [if_pos (by omega), if_pos (by omega), Nat.sub_self, show out + i - out = i by omega,
      get!_set _ _ _ _ inside, if_pos rfl]
  · rw [if_neg (by omega)]
    by_cases within : out ≤ x ∧ x < out + J.size
    · rw [if_pos within, if_pos within, get!_set _ _ _ _ (by omega), if_neg (by omega)]
    · rw [if_neg within, if_neg within]

/-- The closing bit set above the last bit, in a byte. -/
theorem or_bit (x : UInt8) (used : Nat) (h : used < 8) :
    (x.toUInt64 ||| (2 ^ used : Nat).toUInt64).toUInt8 = x ||| (1 <<< UInt8.ofNat used) := by
  have small : 2 ^ used < 256 := by
    have := Nat.pow_lt_pow_right (a := 2) (by decide) h; simpa using this
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8, UInt64.toNat_or, UInt8.toNat_or, UInt8.toNat_toUInt64, UInt8.toNat_shiftLeft]
  simp [Nat.mod_eq_of_lt (show used < 8 from h), Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show 2 ^ used < 2 ^ 64 by omega), Nat.mod_eq_of_lt small]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow (x.toNat_lt) (by simpa using small))

/-- The low byte of a word. -/
theorem qwordByte_zero (v : UInt64) : qwordByte v 0 = v.toUInt8 := by simp [qwordByte]

/-- Bytes copied from where they sit to an output away from them are placed there. -/
theorem copied_whole (mem : Memory) (out p : Nat) (b : ByteArray) (bytes : BytesAt mem p b)
    (apart : p + b.size ≤ out ∨ out + b.size ≤ p) : copied mem out p b.size = placed mem out b := by
  have := copied_placed mem out .empty b p bytes (by simp; omega)
  simpa [placed_empty, ByteArray.empty_append] using this

/-- The bit list driver's loop, doubling a bit up to the bits used in the last byte. -/
def bitsLoop : Stmt :=
  .loop (Expr.lt (.var 10) (.var 8)) (.block [.set 9 (Expr.var 9 + Expr.var 9), .set 10 (Expr.var 10 + 1)])

/-- The bit list driver: the bound, the size, then the closing bit in a byte of its own or in the last one. -/
theorem bitsParts_body : bitsParts.body =
    .block [.set 5 (.lit (codeCount : Nat).toUInt64),
      .ite (Expr.le (.var 1) (.var 2))
        (.block [.set 6 (Expr.ld (.var 0)), .set 7 (Expr.ld (Expr.var 0 + 8)), .set 8 (Expr.var 1 % 8),
          .set 5 (.lit (codePart : Nat).toUInt64),
          .ite (Expr.eq (.var 7) (Expr.var 1 / 8 + Expr.ne (.var 8) 0))
            (.block [.ite (Expr.eq (.var 8) 0)
              (.block [.set 5 (.lit (codeCapacity : Nat).toUInt64),
                .ite (Expr.lt (.var 7) (.var 4))
                  (.block [.call "ssz_copy" [.var 3, .var 6, .var 7] 12, Stmt.st1 (Expr.var 3 + Expr.var 7) 1,
                    .set 5 (Expr.var 7 + 1)]) .skip])
              (.block [.set 9 1, .set 10 0, bitsLoop, .set 11 (Expr.ld1 (Expr.var 6 + Expr.var 7 - 1)),
                .set 5 (.lit (codePadding : Nat).toUInt64),
                .ite (Expr.eq (Expr.var 11 / Expr.var 9) 0)
                  (.block [.set 5 (.lit (codeCapacity : Nat).toUInt64),
                    .ite (Expr.le (.var 7) (.var 4))
                      (.block [.call "ssz_copy" [.var 3, .var 6, .var 7] 12,
                        Stmt.st1 (Expr.var 3 + Expr.var 7 - 1) (Expr.var 11 ||| Expr.var 9),
                        .set 5 (.var 7)]) .skip]) .skip])]) .skip]) .skip] := rfl

/-- A comparison below, as its condition on the words. -/
theorem eval_cmp_lt {w : World} {env : Env} {mem : Memory} {a b : Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (Expr.lt a b) = some (if x < y then 1 else 0) := by
  rw [show Expr.lt a b = .cmp .b a b from rfl, eval_cmp .b ha hb]
  by_cases h : x < y <;> simp [h, Cond.holds]

set_option linter.unusedSimpArgs false in
/-- The bit list reference, with its checks spelled out on numbers. -/
theorem assembleBits_eq (limit : Option Nat) (count : Nat) (packed : ByteArray) (small : count < 2 ^ 64) :
    assembleBits limit count packed =
      if count ≤ limitWord limit then
        if packed.size = (count + 7) / 8 then
          if count % 8 = 0 then .ok (packed.push 1)
          else if (packed.get! (packed.size - 1)).toNat / 2 ^ (count % 8) ≠ 0 then .error .paddingBits
          else .ok (packed.set! (packed.size - 1)
            (packed.get! (packed.size - 1) ||| (1 <<< UInt8.ofNat (count % 8))))
        else .error (.count ((count + 7) / 8) packed.size)
      else .error (.overLimit (limitWord limit) count) := by
  have shift : ∀ x : UInt8, (x >>> UInt8.ofNat (count % 8)).toNat = x.toNat / 2 ^ (count % 8) := by
    intro x
    rw [UInt8.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    congr 2
    simp [UInt8.toNat_ofNat]
  cases limit with
  | none =>
    have : count ≤ limitWord none := by simp [limitWord]; omega
    simp only [this, if_true]
    by_cases s : packed.size = (count + 7) / 8 <;> by_cases u : count % 8 = 0 <;>
      simp_all [assembleBits, boundCheck, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure,
        Except.pure, ← UInt8.toNat_inj]
  | some l =>
    by_cases b : count ≤ l
    · have : count ≤ limitWord (some l) := b
      simp only [this, if_true]
      by_cases s : packed.size = (count + 7) / 8 <;> by_cases u : count % 8 = 0 <;>
        simp_all [assembleBits, boundCheck, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure,
          Except.pure, ← UInt8.toNat_inj]
    · have : ¬ count ≤ limitWord (some l) := b
      simp only [this, if_false]
      simp [assembleBits, boundCheck, b, limitWord, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/-- A bit list from its packed bits and bit count: the driver closes it as `assembleBits` does, or refuses. -/
theorem bits_ok (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory)
    (parts out cap count : Nat) (limit : Option Nat) (packed : ByteArray) (ptr : Nat)
    (at_ : PartsAt w mem parts [packed] [ptr]) (to : OutAt w parts [packed] [ptr] out cap)
    (smallCount : count < 2 ^ 64) (smallLimit : limitWord limit < 2 ^ 64)
    (room : w.stackLo + 8 + 8 * bitsParts.frame + (8 + 8 * copyBytes.frame) ≤ sp) :
    Calls m w "ssz_assemble_bits" sp
      [parts.toUInt64, count.toUInt64, (limitWord limit).toUInt64, out.toUInt64, cap.toUInt64] mem
      (assembleOutcome out cap mem (assembleBits limit count packed)).1
      (assembleOutcome out cap mem (assembleBits limit count packed)).2 := by
  have found : m.fns.lookup "ssz_assemble_bits" = some bitsParts :=
    linked ("ssz_assemble_bits", bitsParts) (by simp [codecFns])
  have tableBound : parts + 16 ≤ 2 ^ 63 := by
    have := at_.table
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have outBound : out + cap ≤ 2 ^ 63 := by
    have := to.writable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have partBound : ptr + packed.size ≤ 2 ^ 63 := by
    have := at_.readable 0 (by simp)
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have apartP : ptr + packed.size ≤ out ∨ out + cap ≤ ptr := to.apartParts 0 (by simp) (by simp)
  have bytesP : BytesAt mem ptr packed := at_.bytes 0 (by simp)
  have capSmall : cap < 2 ^ 64 := by omega
  let len := packed.size
  let inner := sp - 8 - 8 * bitsParts.frame
  let args := [parts.toUInt64, count.toUInt64, (limitWord limit).toUInt64, out.toUInt64, cap.toUInt64]
  have finish : ∀ env' mem' (r : UInt64), Runs m w inner (entryEnv args) mem bitsParts.body env' mem' →
      env' 5 = r → Calls m w "ssz_assemble_bits" sp args mem r mem' := by
    intro env' mem' r main answer
    exact Calls.fn (env' := env') found (by omega) rfl main (by simp [bitsParts, Bits.r, eval, answer])
  rw [assembleBits_eq limit count packed smallCount]
  let env₁ := assign (entryEnv args) 5 (codeCount : Nat).toUInt64
  have bound : eval w env₁ mem (Expr.le (.var 1) (.var 2)) =
      some (if count ≤ limitWord limit then 1 else 0) := by
    rw [eval_cmp_le (x := count.toUInt64) (y := (limitWord limit).toUInt64) (by simp [eval, env₁, assign, entryEnv, args])
      (by simp [eval, env₁, assign, entryEnv, args])]
    simp only [Nat.toUInt64_eq, ofNat_le_iff count _ smallCount smallLimit]
  by_cases within : count ≤ limitWord limit
  case neg =>
    rw [if_neg within]
    refine finish env₁ mem _ ?_ (by simp [env₁, assign, assembleOutcome, errCode])
    rw [bitsParts_body]
    exact Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) (Runs.ite_false (by rw [bound]; simp [within])
      (Runs.skip _ _ _ _ _))
  rw [if_pos within]
  -- The part's start and size, and the bits used in the last byte.
  have r0 := at_.start 0 (by simp)
  have r8 := at_.size 0 (by simp)
  simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at r0 r8
  have c0 : w.access parts 8 := by simpa using access_sub at_.table (b := parts) (k := 8) (by omega) (by simp)
  have c8 : w.access (parts + 8) 8 := access_sub at_.table (by omega) (by simp)
  let used := count % 8
  let env₂ := assign (assign (assign (assign env₁ 6 ptr.toUInt64) 7 len.toUInt64) 8 used.toUInt64) 5
    (codePart : Nat).toUInt64
  have setup : Runs m w inner env₁ mem (.block [.set 6 (Expr.ld (.var 0)), .set 7 (Expr.ld (Expr.var 0 + 8)),
      .set 8 (Expr.var 1 % 8), .set 5 (.lit (codePart : Nat).toUInt64)]) env₂ mem := by
    refine Runs.block_cons (Runs.set _ _ _ _ _ 6 _ _ ?_) (Runs.block_cons (Runs.set _ _ _ _ _ 7 _ _ ?_)
      (Runs.block_cons (Runs.set _ _ _ _ _ 8 _ _ ?_) (Runs.set _ _ _ _ _ 5 _ _ rfl)))
    · simp [Expr.ld, eval, env₁, assign, entryEnv, args, Width.bytes, toNat_toUInt64 parts (by omega), c0, r0]
    · simp [Expr.ld, eval, env₁, assign, entryEnv, args, Width.bytes, aluResult, c8, r8, len,
        show (UInt64.ofNat parts + 8).toNat = parts + 8 by rw [UInt64.toNat_add]; simp; omega]
    · rw [show Expr.var 1 % 8 = .mod (.var 1) (.lit 8) from rfl,
        eval_remainder (x := count.toUInt64) (y := 8) (by simp [eval, assign, env₁, entryEnv, args]) rfl (by decide)]
      simp only [used, Nat.toUInt64_eq]
      rw [show (8 : UInt64) = UInt64.ofNat 8 from rfl, ofNat_mod count 8 smallCount (by decide)]
  have e3 : env₂ 3 = out.toUInt64 := by simp [env₂, env₁, assign, entryEnv, args]
  have e4 : env₂ 4 = cap.toUInt64 := by simp [env₂, env₁, assign, entryEnv, args]
  have e6 : env₂ 6 = ptr.toUInt64 := by simp [env₂, assign]
  have e7 : env₂ 7 = len.toUInt64 := by simp [env₂, assign]
  have e8 : env₂ 8 = used.toUInt64 := by simp [env₂, assign]
  have lenSmall : len < 2 ^ 64 := by omega
  -- The size the bit count needs, as the driver computes it.
  have need : eval w env₂ mem (Expr.var 1 / 8 + Expr.ne (.var 8) 0) = some ((count + 7) / 8).toUInt64 := by
    have q : eval w env₂ mem (Expr.var 1 / 8) = some (count / 8).toUInt64 := by
      rw [show Expr.var 1 / 8 = .div (.var 1) (.lit 8) from rfl,
        eval_quotient (x := count.toUInt64) (y := 8) (by simp [eval, env₂, env₁, assign, entryEnv, args]) rfl
          (by decide)]
      rw [show (8 : UInt64) = UInt64.ofNat 8 from rfl, Nat.toUInt64_eq, ofNat_quotient count 8 smallCount (by decide)]
    have n : eval w env₂ mem (Expr.ne (.var 8) 0) = some (if used ≠ 0 then 1 else 0) := by
      simp only [Expr.ne, eval, e8, Cond.holds]
      by_cases u : used = 0
      · simp [u]
      · have : UInt64.ofNat used ≠ 0 := by
          intro h; have := congrArg UInt64.toNat h; simp [UInt64.toNat_ofNat] at this; omega
        simp [u, this]
    simp only [show (Expr.var 1 / 8 + Expr.ne (.var 8) 0) = .op .add (Expr.var 1 / 8) (Expr.ne (.var 8) 0) from rfl,
      eval, q, n, aluResult, Bind.bind, Option.bind]
    by_cases u : used = 0
    · simp [u]; simp [used] at u; congr 1; omega
    · simp [u]; simp [used] at u
      rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, ← UInt64.ofNat_add]; congr 1; omega
  have sized : eval w env₂ mem (Expr.eq (.var 7) (Expr.var 1 / 8 + Expr.ne (.var 8) 0)) =
      some (if len = (count + 7) / 8 then 1 else 0) := by
    rw [eval_cmp_eq (x := len.toUInt64) (y := ((count + 7) / 8).toUInt64) (by simp [eval, e7]) need]
    by_cases h : len = (count + 7) / 8 <;> simp [h, ofNat_eq_ofNat len ((count + 7) / 8) lenSmall (by omega)]
  -- The start of the body, through the size check.
  have head : ∀ env' mem' (r : UInt64) (rest : Stmt), Runs m w inner env₂ mem rest env' mem' →
      rest = (.ite (Expr.eq (.var 8) 0)
              (.block [.set 5 (.lit (codeCapacity : Nat).toUInt64),
                .ite (Expr.lt (.var 7) (.var 4))
                  (.block [.call "ssz_copy" [.var 3, .var 6, .var 7] 12, Stmt.st1 (Expr.var 3 + Expr.var 7) 1,
                    .set 5 (Expr.var 7 + 1)]) .skip])
              (.block [.set 9 1, .set 10 0, bitsLoop, .set 11 (Expr.ld1 (Expr.var 6 + Expr.var 7 - 1)),
                .set 5 (.lit (codePadding : Nat).toUInt64),
                .ite (Expr.eq (Expr.var 11 / Expr.var 9) 0)
                  (.block [.set 5 (.lit (codeCapacity : Nat).toUInt64),
                    .ite (Expr.le (.var 7) (.var 4))
                      (.block [.call "ssz_copy" [.var 3, .var 6, .var 7] 12,
                        Stmt.st1 (Expr.var 3 + Expr.var 7 - 1) (Expr.var 11 ||| Expr.var 9),
                        .set 5 (.var 7)]) .skip]) .skip])) →
      len = (count + 7) / 8 → env' 5 = r → Calls m w "ssz_assemble_bits" sp args mem r mem' := by
    intro env' mem' r rest ran shape fits answer
    subst shape
    refine finish env' mem' r ?_ answer
    rw [bitsParts_body]
    exact Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) (Runs.ite_true 1 (by rw [bound]; simp [within])
      (by decide) (Runs.block_append setup (Runs.ite_true 1 (by rw [sized]; simp [fits]) (by decide) ran)))
  by_cases fits : len = (count + 7) / 8
  case neg =>
    rw [if_neg fits]
    refine finish env₂ mem _ ?_ (by simp [env₂, assign, assembleOutcome, errCode])
    rw [bitsParts_body]
    exact Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) (Runs.ite_true 1 (by rw [bound]; simp [within])
      (by decide) (Runs.block_append setup (Runs.ite_false (by rw [sized]; simp [fits]) (Runs.skip _ _ _ _ _))))
  rw [if_pos fits]
  have usedSmall : used < 8 := Nat.mod_lt _ (by decide)
  have copyRoom : w.stackLo + 8 + 8 * copyBytes.frame ≤ inner := by simp only [inner]; omega
  by_cases whole : count % 8 = 0
  · -- A whole number of bytes: the closing bit takes a byte of its own.
    rw [if_pos whole]
    have u0 : used = 0 := whole
    simp only [assembleOutcome, ByteArray.size_push]
    let env₃ := assign env₂ 5 (codeCapacity : Nat).toUInt64
    have test : eval w env₃ mem (Expr.lt (.var 7) (.var 4)) = some (if len < cap then 1 else 0) := by
      rw [eval_cmp_lt (x := len.toUInt64) (y := cap.toUInt64) (by simp [eval, env₃, assign, e7])
        (by simp [eval, env₃, assign, e4])]
      simp only [Nat.toUInt64_eq, ofNat_lt_ofNat len cap lenSmall capSmall]
    by_cases fitsOut : packed.size + 1 ≤ cap
    · rw [if_pos fitsOut]
      have copiedNow := copy_correct m w linked inner mem out.toUInt64 ptr.toUInt64 len.toUInt64 copyRoom
        (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]; exact at_.readable 0 (by simp))
        (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]
            exact access_sub to.writable (by omega) (by omega))
        (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]; omega)
      rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega),
        copied_whole mem out ptr packed bytesP (by omega)] at copiedNow
      have stored := Runs.store m w inner (assign env₃ 12 0) (placed mem out packed) .b1 (Expr.var 3 + Expr.var 7) 1
        (out + len).toUInt64 1 (by simp [eval, assign, env₃, e3, e7, aluResult]) rfl
        (by rw [toNat_toUInt64 _ (by omega)]; exact access_sub to.writable (by omega) (by simp [Width.bytes]; omega))
      rw [toNat_toUInt64 _ (by omega), Width.bytes, placed_push mem out packed] at stored
      refine head _ _ _ _ (Runs.ite_true 1 (by simp [Expr.eq, eval, e8, u0, Cond.holds]) (by decide)
        (Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) (Runs.ite_true 1 (by rw [test]; simp; omega) (by decide)
          (Runs.block_cons (Runs.call (values := [out.toUInt64, ptr.toUInt64, len.toUInt64])
            (by simp [eval, env₃, assign, e3, e6, e7]) copiedNow)
            (Runs.block_cons stored (Runs.set _ _ _ _ _ 5 _ (len + 1).toUInt64
              (by simp [eval, assign, env₃, e7, aluResult]))))))) rfl
        fits ?_
      simp [assign, len]
    · rw [if_neg fitsOut]
      exact head _ _ _ _ (Runs.ite_true 1 (by simp [Expr.eq, eval, e8, u0, Cond.holds]) (by decide)
        (Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) (Runs.ite_false (by rw [test]; simp; omega)
          (Runs.skip _ _ _ _ _)))) rfl fits (by simp [assign])
  -- Some bits of the last byte are used: the closing bit goes right above them.
  rw [if_neg whole]
  have u0 : used ≠ 0 := whole
  have lenPos : 1 ≤ len := by simp only [len] at fits ⊢; omega
  have usedNe : (used.toUInt64 == 0) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h; have := congrArg UInt64.toNat h; simp [UInt64.toNat_ofNat] at this; omega
  -- The bit above the used ones: doubled once per used bit.
  let envA := assign (assign env₂ 9 1) 10 0
  let invB : Env → Memory → Prop := fun env cur => mem = cur ∧ (∀ k, k ≠ 9 → k ≠ 10 → env k = envA k) ∧
    ∃ j, j ≤ used ∧ env 10 = j.toUInt64 ∧ env 9 = (2 ^ j).toUInt64
  have loopB := Runs.loop_inv (m := m) (w := w) (sp := inner) (c := Expr.lt (.var 10) (.var 8))
    (body := .block [.set 9 (Expr.var 9 + Expr.var 9), .set 10 (Expr.var 10 + 1)])
    invB (fun env _ => used - (env 10).toNat) (fun env cur _ => ⟨_, rfl⟩)
    (by
      intro env cur v hinv cond nonzero
      obtain ⟨hm, keep, j, hj, e10, e9⟩ := hinv
      subst hm
      have e8' : env 8 = used.toUInt64 := by rw [keep 8 (by decide) (by decide)]; simp [envA, assign, e8]
      have more : j < used := by
        rw [eval_cmp_lt (x := j.toUInt64) (y := used.toUInt64) (by simp [eval, e10]) (by simp [eval, e8'])] at cond
        by_cases done : j < used
        · exact done
        · simp [Nat.toUInt64_eq, ofNat_lt_ofNat j used (by omega) (by omega), done] at cond
          exact absurd cond.symm nonzero
      have pow : (2 ^ j : Nat).toUInt64 + (2 ^ j : Nat).toUInt64 = (2 ^ (j + 1) : Nat).toUInt64 := by
        simp only [Nat.toUInt64_eq]; rw [← UInt64.ofNat_add, Nat.pow_succ]; congr 1; omega
      refine ⟨assign (assign env 9 (2 ^ (j + 1) : Nat).toUInt64) 10 (j + 1).toUInt64, mem,
        Runs.block_cons (Runs.set _ _ _ _ _ 9 _ _ (by simp only [show Expr.var 9 + Expr.var 9 =
          .op .add (.var 9) (.var 9) from rfl, eval, e9, aluResult, Bind.bind, Option.bind]; rw [← pow]; rfl))
          (Runs.set _ _ _ _ _ 10 _ _ (by simp [eval, assign, e10, aluResult])),
        ⟨rfl, fun k h9 h10 => by simp [assign, h9, h10, keep k h9 h10], j + 1, more, by simp [assign],
          by simp [assign]⟩, ?_⟩
      simp [assign, e10, toNat_toUInt64 j (by omega), toNat_toUInt64 (j + 1) (by omega)]
      omega)
  obtain ⟨envB, memB, ranB, ⟨hm, keepB, j, hj, f10, f9⟩, exitB⟩ := loopB envA mem
    ⟨rfl, fun k _ _ => rfl, 0, Nat.zero_le _, by simp [envA, assign], by simp [envA, assign]⟩
  subst hm
  have reached : j = used := by
    have e8' : envB 8 = used.toUInt64 := by rw [keepB 8 (by decide) (by decide)]; simp [envA, assign, e8]
    rw [eval_cmp_lt (x := j.toUInt64) (y := used.toUInt64) (by simp [eval, f10]) (by simp [eval, e8'])] at exitB
    by_cases done : j < used
    · simp [Nat.toUInt64_eq, ofNat_lt_ofNat j used (by omega) (by omega), done] at exitB
    · omega
  subst reached
  have g : ∀ k, k ≠ 9 → k ≠ 10 → envB k = env₂ k := by
    intro k h9 h10; rw [keepB k h9 h10]; simp [envA, assign, h9, h10]
  -- The last byte, read before anything is written.
  let last := packed.get! (len - 1)
  have lastRead : eval w envB mem (Expr.ld1 (Expr.var 6 + Expr.var 7 - 1)) = some last.toUInt64 := by
    have addr : UInt64.ofNat ptr + UInt64.ofNat len - 1 = UInt64.ofNat (ptr + len - 1) := by
      rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, ← UInt64.ofNat_add, ofNat_sub _ _ (by omega) (by omega)]
    have acc : w.access (ptr + len - 1) 1 := access_sub (at_.readable 0 (by simp)) (by simp; omega) (by simp [len]; omega)
    have byte : mem (ptr + len - 1) = last := by
      have := bytesP (len - 1) (by omega)
      rw [show ptr + (len - 1) = ptr + len - 1 by omega] at this
      exact this
    rw [show Expr.var 6 + Expr.var 7 - 1 = .op .sub (.op .add (.var 6) (.var 7)) (.lit 1) from rfl]
    simp [Expr.ld1, eval, g 6 (by decide) (by decide), g 7 (by decide) (by decide), e6, e7, aluResult, addr,
      toNat_toUInt64 _ (show ptr + len - 1 < 2 ^ 64 by omega), acc, Width.bytes, readLE, byte]
  have bitWord : envB 9 = (2 ^ used : Nat).toUInt64 := f9
  have powSmall : 2 ^ used < 256 := by
    have := Nat.pow_lt_pow_right (a := 2) (by decide) usedSmall; simpa using this
  let envC := assign (assign envB 11 last.toUInt64) 5 (codePadding : Nat).toUInt64
  have padTest : eval w envC mem (Expr.eq (Expr.var 11 / Expr.var 9) 0) =
      some (if last.toNat / 2 ^ used = 0 then 1 else 0) := by
    have q : eval w envC mem (Expr.var 11 / Expr.var 9) = some (last.toNat / 2 ^ used).toUInt64 := by
      rw [show Expr.var 11 / Expr.var 9 = .div (.var 11) (.var 9) from rfl,
        eval_quotient (x := last.toNat.toUInt64) (y := (2 ^ used : Nat).toUInt64) (by simp [eval, envC, assign])
          (by simp [eval, envC, assign, bitWord])
          (by intro h; have := congrArg UInt64.toNat h; simp [UInt64.toNat_ofNat] at this
              rw [Nat.mod_eq_of_lt (by omega)] at this; have := Nat.pow_pos (n := used) (by decide : 0 < 2); omega)]
      rw [Nat.toUInt64_eq, Nat.toUInt64_eq, Nat.toUInt64_eq,
        ofNat_quotient _ _ (by have := last.toNat_lt; omega) (by omega)]
    rw [eval_cmp_eq q (show eval w envC mem 0 = some (0 : Nat).toUInt64 from rfl)]
    have small : last.toNat / 2 ^ used < 2 ^ 64 := by have := last.toNat_lt; have := Nat.div_le_self last.toNat (2 ^ used); omega
    have z' : UInt64.ofNat (last.toNat / 2 ^ used) = 0 ↔ last.toNat / 2 ^ used = 0 := by
      rw [show (0 : UInt64) = UInt64.ofNat 0 from rfl]; exact ofNat_eq_ofNat _ 0 small (by decide)
    by_cases z : last.toNat / 2 ^ used = 0 <;> simp [z, z']
  -- The body from the bit loop on, given how its last test runs.
  have tail : ∀ env' mem', Runs m w inner envC mem (.ite (Expr.eq (Expr.var 11 / Expr.var 9) 0)
        (.block [.set 5 (.lit (codeCapacity : Nat).toUInt64),
          .ite (Expr.le (.var 7) (.var 4))
            (.block [.call "ssz_copy" [.var 3, .var 6, .var 7] 12,
              Stmt.st1 (Expr.var 3 + Expr.var 7 - 1) (Expr.var 11 ||| Expr.var 9),
              .set 5 (.var 7)]) .skip]) .skip) env' mem' →
      Runs m w inner env₂ mem (.ite (Expr.eq (.var 8) 0)
              (.block [.set 5 (.lit (codeCapacity : Nat).toUInt64),
                .ite (Expr.lt (.var 7) (.var 4))
                  (.block [.call "ssz_copy" [.var 3, .var 6, .var 7] 12, Stmt.st1 (Expr.var 3 + Expr.var 7) 1,
                    .set 5 (Expr.var 7 + 1)]) .skip])
              (.block [.set 9 1, .set 10 0, bitsLoop, .set 11 (Expr.ld1 (Expr.var 6 + Expr.var 7 - 1)),
                .set 5 (.lit (codePadding : Nat).toUInt64),
                .ite (Expr.eq (Expr.var 11 / Expr.var 9) 0)
                  (.block [.set 5 (.lit (codeCapacity : Nat).toUInt64),
                    .ite (Expr.le (.var 7) (.var 4))
                      (.block [.call "ssz_copy" [.var 3, .var 6, .var 7] 12,
                        Stmt.st1 (Expr.var 3 + Expr.var 7 - 1) (Expr.var 11 ||| Expr.var 9),
                        .set 5 (.var 7)]) .skip]) .skip])) env' mem' := by
    intro env' mem' ran
    have usedNe' : UInt64.ofNat used ≠ 0 := by
      intro h; have := congrArg UInt64.toNat h; simp [UInt64.toNat_ofNat] at this; omega
    refine Runs.ite_false (by simp [Expr.eq, eval, e8, usedNe', Cond.holds]) ?_
    exact Runs.block_cons (Runs.set _ _ _ _ _ 9 _ _ rfl) (Runs.block_cons (Runs.set _ _ _ _ _ 10 _ _ rfl)
      (Runs.block_cons ranB (Runs.block_cons (Runs.set _ _ _ _ _ 11 _ _ lastRead)
        (Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) ran))))
  have lenEq : packed.size - 1 = len - 1 := rfl
  by_cases padded : last.toNat / 2 ^ used ≠ 0
  · -- A padding bit set: refused.
    rw [if_pos (show (packed.get! (packed.size - 1)).toNat / 2 ^ (count % 8) ≠ 0 from padded)]
    exact head _ _ _ _ (tail _ _ (Runs.ite_false (by rw [padTest]; simp [padded]) (Runs.skip _ _ _ _ _))) rfl fits
      (by simp [envC, assign, assembleOutcome, errCode])
  rw [if_neg (show ¬ (packed.get! (packed.size - 1)).toNat / 2 ^ (count % 8) ≠ 0 from padded)]
  simp only [assembleOutcome, ByteArray.size_set!]
  have clear : last.toNat / 2 ^ used = 0 := by simpa using padded
  let envD := assign envC 5 (codeCapacity : Nat).toUInt64
  have test : eval w envD mem (Expr.le (.var 7) (.var 4)) = some (if len ≤ cap then 1 else 0) := by
    rw [eval_cmp_le (x := len.toUInt64) (y := cap.toUInt64)
      (by simp [eval, envD, envC, assign, g 7 (by decide) (by decide), e7])
      (by simp [eval, envD, envC, assign, g 4 (by decide) (by decide), e4])]
    simp only [Nat.toUInt64_eq, ofNat_le_iff len cap lenSmall capSmall]
  by_cases fitsOut : packed.size ≤ cap
  · rw [if_pos fitsOut]
    have copiedNow := copy_correct m w linked inner mem out.toUInt64 ptr.toUInt64 len.toUInt64 copyRoom
      (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]; exact at_.readable 0 (by simp))
      (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]
          exact access_sub to.writable (by omega) (by omega))
      (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]; omega)
    rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega),
      copied_whole mem out ptr packed bytesP (by omega)] at copiedNow
    let envE := assign envD 12 0
    have addr : UInt64.ofNat out + UInt64.ofNat len - 1 = UInt64.ofNat (out + len - 1) := by
      rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, ← UInt64.ofNat_add, ofNat_sub _ _ (by omega) (by omega)]
    let v : UInt64 := last.toUInt64 ||| (2 ^ used : Nat).toUInt64
    have stored := Runs.store m w inner envE (placed mem out packed) .b1 (Expr.var 3 + Expr.var 7 - 1)
      (Expr.var 11 ||| Expr.var 9) (out + len - 1).toUInt64 v
      (by rw [show Expr.var 3 + Expr.var 7 - 1 = .op .sub (.op .add (.var 3) (.var 7)) (.lit 1) from rfl]
          simp [eval, envE, envD, envC, assign, g 3 (by decide) (by decide), g 7 (by decide) (by decide), e3, e7,
            aluResult, addr])
      (by rw [show (Expr.var 11 ||| Expr.var 9) = .op .or (.var 11) (.var 9) from rfl]
          simp [eval, envE, envD, envC, assign, bitWord, aluResult, v])
      (by rw [toNat_toUInt64 _ (by omega)]; exact access_sub to.writable (by omega) (by simp [Width.bytes]; omega))
    rw [toNat_toUInt64 _ (by omega), Width.bytes, show out + len - 1 = out + (len - 1) by omega,
      placed_set mem out packed (len - 1) (by omega), qwordByte_zero,
      show v.toUInt8 = last ||| (1 <<< UInt8.ofNat used) from or_bit last used usedSmall] at stored
    exact head _ _ _ _ (tail _ _ (Runs.ite_true 1 (by rw [padTest]; simp [clear]) (by decide)
      (Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) (Runs.ite_true 1 (by rw [test]; simp [len]; omega) (by decide)
        (Runs.block_cons (Runs.call (values := [out.toUInt64, ptr.toUInt64, len.toUInt64])
          (by simp [eval, envD, envC, assign, g 3 (by decide) (by decide), g 6 (by decide) (by decide),
            g 7 (by decide) (by decide), e3, e6, e7]) copiedNow)
          (Runs.block_cons stored (Runs.set _ _ _ _ _ 5 _ len.toUInt64
            (by simp [eval, assign, envE, envD, envC, g 7 (by decide) (by decide), e7])))))))) rfl fits
      (by simp [assign, len])
  · rw [if_neg fitsOut]
    exact head _ _ _ _ (tail _ _ (Runs.ite_true 1 (by rw [padTest]; simp [clear]) (by decide)
      (Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) (Runs.ite_false (by rw [test]; simp [len]; omega)
        (Runs.skip _ _ _ _ _))))) rfl fits (by simp [envD, assign])

/-! ## Unions -/

/-- The union driver's search for the first selector equal to the selector byte. -/
def unionSearch : Stmt :=
  .loop (.op .and (Expr.lt (.var 8) (.var 7)) (Expr.eq (.var 9) (.lit (none64 : Nat).toUInt64)))
    (.block [.ite (Expr.eq (Expr.ld (Expr.var 0 + 16 + 8 * Expr.var 8)) (.var 6)) (.block [.set 9 (.var 8)]) .skip,
      .set 8 (Expr.var 8 + 1)])

/-- The union driver: two parts, a one-byte selector a declared option takes, a body that fits it, then the write. -/
theorem unionParts_body : unionParts.body =
    .block [.set 5 (.lit (codeCount : Nat).toUInt64),
      .ite (Expr.eq (.var 2) 2)
        (.block [.set 5 (.lit (codePart : Nat).toUInt64),
          .ite (Expr.eq (Expr.ld (Expr.var 1 + 8)) 1)
            (.block [.set 6 (Expr.ld1 (Expr.ld (.var 1))), .set 7 (word (.var 0) 1), .set 8 0,
              .set 9 (.lit (none64 : Nat).toUInt64), unionSearch,
              .set 5 (.lit (codeSelector : Nat).toUInt64),
              .ite (.op .and (.op .and (Expr.ne (.var 9) (.lit (none64 : Nat).toUInt64)) (Expr.le 1 (.var 6)))
                  (Expr.le (.var 6) 127))
                (.block [.call "ssz_plan_skip" [Expr.var 0 + 16 + 8 * Expr.var 7, .var 9] 10,
                  .call "ssz_plan_width" [.var 10] 11, .set 12 (Expr.ld (Expr.var 1 + 24)),
                  .set 5 (.lit (codePart : Nat).toUInt64),
                  .ite (.op .or (Expr.eq (.var 11) (.lit (none64 : Nat).toUInt64)) (Expr.eq (.var 12) (.var 11)))
                    (.block [.set 5 (.lit (codeCapacity : Nat).toUInt64),
                      .ite (Expr.lt (.var 12) (.var 4))
                        (.block [Stmt.st1 (.var 3) (.var 6),
                          .call "ssz_copy" [Expr.var 3 + 1, Expr.ld (Expr.var 1 + 16), .var 12] 13,
                          .set 5 (Expr.var 12 + 1)]) .skip]) .skip]) .skip]) .skip]) .skip] := rfl

/-- A list's first types nest no deeper than the list. -/
theorem deepest_take : ∀ (ds : List Desc) (k : Nat), Desc.deepestNesting (ds.take k) ≤ Desc.deepestNesting ds
  | [], _ => by simp
  | d :: rest, 0 => by simp [Desc.deepestNesting]
  | d :: rest, k + 1 => by
    simp only [List.take_succ_cons, Desc.deepestNesting]
    exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans (deepest_take rest k) (Nat.le_max_right _ _)⟩

/-- The option a selector names is the first one paired with it. -/
theorem lookupOption_first : ∀ (selectors : List Nat) (options : List Desc) (s idx : Nat),
    (len : selectors.length = options.length) → (h : idx < selectors.length) → selectors[idx] = s →
    (∀ k (hk : k < idx), selectors[k]'(by omega) ≠ s) →
    lookupOption selectors options s = .ok (options[idx]'(by omega))
  | [], _, _, _, _, h, _, _ => by simp at h
  | x :: xs, [], _, _, len, _, _, _ => by simp at len
  | x :: xs, o :: os, s, 0, _, _, hx, _ => by simp at hx; simp [lookupOption, hx]
  | x :: xs, o :: os, s, idx + 1, len, h, hx, before => by
    have x0 : x ≠ s := before 0 (by omega)
    simp only [lookupOption, beq_iff_eq, x0, if_false]
    exact lookupOption_first xs os s idx (by simpa using len) (by simpa using h) (by simpa using hx)
      (fun k hk => by simpa using before (k + 1) (by omega))

/-- A selector no option is paired with is refused as unknown. -/
theorem lookupOption_none : ∀ (selectors : List Nat) (options : List Desc) (s : Nat),
    selectors.length = options.length → (∀ k (hk : k < selectors.length), selectors[k] ≠ s) →
    lookupOption selectors options s = .error (.unknownSelector s)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, len, _ => by simp at len
  | _ :: _, [], _, len, _ => by simp at len
  | x :: xs, o :: os, s, len, none_ => by
    have x0 : x ≠ s := none_ 0 (by simp)
    simp only [lookupOption, beq_iff_eq, x0, if_false]
    exact lookupOption_none xs os s (by simpa using len) (fun k hk => by
      have := none_ (k + 1) (by simp; omega)
      simpa using this)

/-- An operation's value, from its operands'. -/
theorem eval_alu {w : World} {env : Env} {mem : Memory} {o : Alu} {a b : Expr} {x y : UInt64}
    (ha : eval w env mem a = some x) (hb : eval w env mem b = some y) :
    eval w env mem (.op o a b) = some (aluResult o x y).1 := by
  simp [eval, ha, hb, pure]

/-- A load's value, from its address's. -/
theorem eval_load {w : World} {env : Env} {mem : Memory} {wd : Width} {a : Expr} {x : UInt64}
    (ha : eval w env mem a = some x) (ok : w.access x.toNat wd.bytes) :
    eval w env mem (.load wd a) = some (readLE mem x.toNat wd.bytes) := by
  simp [eval, ha, ok, pure]

/-- The stack the union driver needs below its own frame: the walk to the option, its width, and a copy. -/
def unionRoom (options : List Desc) : Nat :=
  (8 + 8 * planSkip.frame) + (widthLevel + walkLevel) * Desc.deepestNesting options + (8 + 8 * copyBytes.frame)

/-- A one-byte part stored as its byte is placed. -/
theorem placed_one (mem : Memory) (out : Nat) (sel : ByteArray) (one : sel.size = 1) (f : Nat → UInt8)
    (byte : f 0 = sel.get! 0) : store mem out 1 f = placed mem out sel := by
  funext x
  simp only [placed, store, one]
  split
  · rw [show x - out = 0 by omega, byte]
  · rfl

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/-- A union from its selector byte and its option's encoding: the driver writes both, or refuses as `assemble` does. -/
theorem union_ok (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory)
    (selectors : List Nat) (options : List Desc) (p parts out cap : Nat) (ps : List ByteArray) (ptrs : List Nat)
    (sound : (Desc.compatibleUnion selectors options).wellFormed = .ok ())
    (thin : narrow (.compatibleUnion selectors options) = true)
    (plan : PlanAt w mem p (words (.compatibleUnion selectors options)))
    (at_ : PartsAt w mem parts ps ptrs) (to : OutAt w parts ps ptrs out cap)
    (room : w.stackLo + 8 + 8 * unionParts.frame + unionRoom options ≤ sp) :
    Calls m w "ssz_assemble_union" sp
      [p.toUInt64, parts.toUInt64, ps.length.toUInt64, out.toUInt64, cap.toUInt64] mem
      (assembleOutcome out cap mem (assemble (.compatibleUnion selectors options) ps)).1
      (assembleOutcome out cap mem (assemble (.compatibleUnion selectors options) ps)).2 := by
  have found : m.fns.lookup "ssz_assemble_union" = some unionParts :=
    linked ("ssz_assemble_union", unionParts) (by simp [codecFns])
  have tableBound : parts + 16 * ps.length ≤ 2 ^ 63 := by
    have := at_.table
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have outBound : out + cap ≤ 2 ^ 63 := by
    have := to.writable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have planBound : p + 8 * (words (.compatibleUnion selectors options)).length ≤ 2 ^ 63 := by
    have := plan.1; simpa [addressBound] using this
  have paired := wellFormed_union_paired sound
  have inRange := wellFormed_union_selectors sound
  have optionsSound := allWellFormed_mem _ (wellFormed_union sound)
  simp only [narrow] at thin
  have optionsThin := narrow_mem _ thin
  have ur : unionRoom options = (8 + 8 * planSkip.frame) + (widthLevel + walkLevel) * Desc.deepestNesting options +
    (8 + 8 * copyBytes.frame) := rfl
  let inner := sp - 8 - 8 * unionParts.frame
  let args := [p.toUInt64, parts.toUInt64, ps.length.toUInt64, out.toUInt64, cap.toUInt64]
  have finish : ∀ env' mem' (r : UInt64), Runs m w inner (entryEnv args) mem unionParts.body env' mem' →
      env' 5 = r → Calls m w "ssz_assemble_union" sp args mem r mem' := by
    intro env' mem' r main answer
    exact Calls.fn (env' := env') found (by omega) rfl main (by simp [unionParts, UnionV.r, eval, answer])
  let env₁ := assign (entryEnv args) 5 (codeCount : Nat).toUInt64
  have lenSmall : ps.length < 2 ^ 64 := by omega
  -- Anything but two parts is refused.
  by_cases two : ps.length = 2
  case neg =>
    have refused : assemble (.compatibleUnion selectors options) ps = .error (.scope 2 ps.length) := by
      match ps, two with
      | [], _ => rfl
      | [_], _ => rfl
      | [_, _], two => simp at two
      | _ :: _ :: _ :: _, _ => rfl
    rw [refused]
    refine finish env₁ mem _ ?_ (by simp [env₁, assign, assembleOutcome, errCode])
    rw [unionParts_body]
    refine Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) (Runs.ite_false ?_ (Runs.skip _ _ _ _ _))
    rw [eval_cmp_eq (x := ps.length.toUInt64) (y := (2 : Nat).toUInt64) (by simp [eval, env₁, assign, entryEnv, args])
      rfl]
    have ne2 : UInt64.ofNat ps.length ≠ 2 := by
      intro h; have := congrArg UInt64.toNat h; simp [UInt64.toNat_ofNat] at this; omega
    simp [ne2]
  obtain ⟨sel, body, rfl⟩ : ∃ sel body, ps = [sel, body] := by
    match ps, two with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  obtain ⟨p0, p1, rfl⟩ : ∃ p0 p1, ptrs = [p0, p1] := by
    have := at_.count
    match ptrs, this with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  -- The table's four words.
  have partsBound : parts + 32 ≤ 2 ^ 63 := by simp at tableBound; omega
  have readT : ∀ c, c + 8 ≤ 32 → (UInt64.ofNat parts + UInt64.ofNat c).toNat = parts + c ∧
      w.access (parts + c) 8 := fun c hc =>
    ⟨by rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
        UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; omega,
      access_sub at_.table (by omega) (by simp; omega)⟩
  have r0 : readLE mem parts 8 = p0.toUInt64 := by simpa using at_.start 0 (by simp)
  have r8 : readLE mem (parts + 8) 8 = sel.size.toUInt64 := by simpa using at_.size 0 (by simp)
  have r16 : readLE mem (parts + 16) 8 = p1.toUInt64 := by simpa using at_.start 1 (by simp)
  have r24 : readLE mem (parts + 24) 8 = body.size.toUInt64 := by simpa using at_.size 1 (by simp)
  have selBound : p0 + sel.size ≤ 2 ^ 63 := by
    have := at_.readable 0 (by simp)
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have bodyBound : p1 + body.size ≤ 2 ^ 63 := by
    have := at_.readable 1 (by simp)
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  let env₂ := assign env₁ 5 (codePart : Nat).toUInt64
  have sizeTest : eval w env₂ mem (Expr.eq (Expr.ld (Expr.var 1 + 8)) 1) = some (if sel.size = 1 then 1 else 0) := by
    obtain ⟨a8, c8⟩ := readT 8 (by omega)
    rw [eval_cmp_eq (x := sel.size.toUInt64) (y := (1 : Nat).toUInt64)
      (by simp [Expr.ld, eval, env₂, env₁, assign, entryEnv, args, aluResult, Width.bytes, a8, c8, r8,
        show (parts + 8) % 18446744073709551616 = parts + 8 from Nat.mod_eq_of_lt (by omega)]) rfl]
    have small : sel.size < 2 ^ 64 := by omega
    have iff1 : UInt64.ofNat sel.size = 1 ↔ sel.size = 1 := by
      rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl]; exact ofNat_eq_ofNat _ 1 small (by decide)
    by_cases one : sel.size = 1 <;> simp [one, iff1]
  -- The start of the body, through the selector size check.
  have head : ∀ env' mem' (r : UInt64) (rest : List Stmt),
      Runs m w inner env₂ mem (.block rest) env' mem' → sel.size = 1 →
      rest = [.set 6 (Expr.ld1 (Expr.ld (.var 1))), .set 7 (word (.var 0) 1), .set 8 0,
              .set 9 (.lit (none64 : Nat).toUInt64), unionSearch,
              .set 5 (.lit (codeSelector : Nat).toUInt64),
              .ite (.op .and (.op .and (Expr.ne (.var 9) (.lit (none64 : Nat).toUInt64)) (Expr.le 1 (.var 6)))
                  (Expr.le (.var 6) 127))
                (.block [.call "ssz_plan_skip" [Expr.var 0 + 16 + 8 * Expr.var 7, .var 9] 10,
                  .call "ssz_plan_width" [.var 10] 11, .set 12 (Expr.ld (Expr.var 1 + 24)),
                  .set 5 (.lit (codePart : Nat).toUInt64),
                  .ite (.op .or (Expr.eq (.var 11) (.lit (none64 : Nat).toUInt64)) (Expr.eq (.var 12) (.var 11)))
                    (.block [.set 5 (.lit (codeCapacity : Nat).toUInt64),
                      .ite (Expr.lt (.var 12) (.var 4))
                        (.block [Stmt.st1 (.var 3) (.var 6),
                          .call "ssz_copy" [Expr.var 3 + 1, Expr.ld (Expr.var 1 + 16), .var 12] 13,
                          .set 5 (Expr.var 12 + 1)]) .skip]) .skip]) .skip] →
      env' 5 = r → Calls m w "ssz_assemble_union" sp args mem r mem' := by
    intro env' mem' r rest ran one shape answer
    subst shape
    refine finish env' mem' r ?_ answer
    rw [unionParts_body]
    refine Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) (Runs.ite_true 1 ?_ (by decide)
      (Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) (Runs.ite_true 1 (by rw [sizeTest]; simp [one]) (by decide) ran)))
    rw [eval_cmp_eq (x := (2 : Nat).toUInt64) (y := (2 : Nat).toUInt64) (by simp [eval, env₁, assign, entryEnv, args])
      rfl]
    simp
  by_cases one : sel.size = 1
  case neg =>
    -- The selector is not one byte.
    have refused : assemble (.compatibleUnion selectors options) [sel, body] = .error (.count 1 sel.size) := by
      simp [assemble, one, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
    rw [refused]
    refine finish env₂ mem _ ?_ (by simp [env₂, assign, assembleOutcome, errCode])
    rw [unionParts_body]
    refine Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) (Runs.ite_true 1 ?_ (by decide)
      (Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) (Runs.ite_false (by rw [sizeTest]; simp [one])
        (Runs.skip _ _ _ _ _))))
    rw [eval_cmp_eq (x := (2 : Nat).toUInt64) (y := (2 : Nat).toUInt64) (by simp [eval, env₁, assign, entryEnv, args])
      rfl]
    simp
  -- The selector byte, the option count, and the search for the selector.
  let s := (sel.get! 0).toNat
  have sSmall : s < 256 := (sel.get! 0).toNat_lt
  let n := options.length
  have wordsEq : words (.compatibleUnion selectors options) = [12, n] ++ selectors ++ wordsAll options := rfl
  have wordsLen : (words (.compatibleUnion selectors options)).length = 2 + n + (wordsAll options).length := by
    rw [wordsEq]; simp [n, paired]; omega
  have nWord : readLE mem (p + 8) 8 = n.toUInt64 ∧ w.access (p + 8) 8 := by
    have := plan.2 1 (by rw [wordsLen]; simp [n]; omega)
    exact ⟨by simpa [wordsEq] using this.2, by simpa using this.1⟩
  have selWord : ∀ k (hk : k < selectors.length), readLE mem (p + 16 + 8 * k) 8 = selectors[k].toUInt64 ∧
      w.access (p + 16 + 8 * k) 8 := by
    intro k hk
    have := plan.2 (2 + k) (by rw [wordsLen]; simp [n]; omega)
    rw [show p + 8 * (2 + k) = p + 16 + 8 * k by omega] at this
    refine ⟨?_, this.1⟩
    have opt : (words (.compatibleUnion selectors options))[2 + k]? = some (selectors[k]'(by omega)) := by
      rw [show 2 + k = k + 2 by omega, wordsEq]
      simp [List.getElem?_append_left (show k < selectors.length by omega)]
    rw [this.2, Option.some.inj ((List.getElem?_eq_getElem _).symm.trans opt)]
  have selRange : ∀ k (hk : k < selectors.length), 1 ≤ selectors[k] ∧ selectors[k] ≤ 127 :=
    fun k hk => inRange _ (List.getElem_mem _)
  let env₃ := assign (assign (assign (assign env₂ 6 s.toUInt64) 7 n.toUInt64) 8 0) 9 (none64 : Nat).toUInt64
  have prefix₃ : Runs m w inner env₂ mem (.block [.set 6 (Expr.ld1 (Expr.ld (.var 1))), .set 7 (word (.var 0) 1),
      .set 8 0, .set 9 (.lit (none64 : Nat).toUInt64)]) env₃ mem := by
    obtain ⟨a0, c0⟩ := readT 0 (by omega)
    have selByte : mem p0 = sel.get! 0 := by simpa using at_.bytes 0 (by simp) 0 (by simp [one])
    have cs : w.access p0 1 := access_sub (at_.readable 0 (by simp)) (by simp) (by simp; omega)
    refine Runs.block_cons (Runs.set _ _ _ _ _ 6 _ _ ?_) (Runs.block_cons (Runs.set _ _ _ _ _ 7 _ _ ?_)
      (Runs.block_cons (Runs.set _ _ _ _ _ 8 _ _ rfl) (Runs.set _ _ _ _ _ 9 _ _ rfl)))
    · simp at a0 c0
      have ld0 : eval w env₂ mem (Expr.ld (.var 1)) = some p0.toUInt64 := by
        rw [show Expr.ld (.var 1) = .load .b8 (.var 1) from rfl,
          eval_load (x := parts.toUInt64) (by simp [eval, env₂, env₁, assign, entryEnv, args])
            (by rw [toNat_toUInt64 _ (by omega)]; exact c0), toNat_toUInt64 _ (by omega)]
        simp [Width.bytes, r0]
      rw [show Expr.ld1 (Expr.ld (.var 1)) = .load .b1 (Expr.ld (.var 1)) from rfl,
        eval_load ld0 (by rw [toNat_toUInt64 _ (by omega)]; exact cs), toNat_toUInt64 _ (by omega)]
      simp [Width.bytes, readLE, selByte, s]
    · have a8 : (UInt64.ofNat p + 8).toNat = p + 8 := by
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; simp; omega
      evaluate [env₂, env₁, entryEnv, args, a8, nWord.1, nWord.2]
  have f0 : env₃ 0 = p.toUInt64 := by simp [env₃, env₂, env₁, assign, entryEnv, args]
  have f6 : env₃ 6 = s.toUInt64 := by simp [env₃, assign]
  have f7 : env₃ 7 = n.toUInt64 := by simp [env₃, assign]
  have nSmall : n < 2 ^ 60 := by rw [wordsLen] at planBound; omega
  -- After i selectors, either none matched, or the first match is noted.
  let invS : Env → Memory → Prop := fun env cur => mem = cur ∧ (∀ k, k < 8 → env k = env₃ k) ∧
    ∃ i, ∃ _ : i ≤ selectors.length, env 8 = i.toUInt64 ∧
      ((env 9 = (none64 : Nat).toUInt64 ∧ ∀ k (hk : k < i), selectors[k]'(by omega) ≠ s) ∨
        (∃ idx, ∃ hidx : idx < i, env 9 = idx.toUInt64 ∧ selectors[idx]'(by omega) = s ∧
          ∀ k (hk : k < idx), selectors[k]'(by omega) ≠ s))
  have noneBig : ∀ idx, idx < n → idx.toUInt64 ≠ (none64 : Nat).toUInt64 := by
    intro idx h e; have := congrArg UInt64.toNat e
    rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by decide)] at this; simp at this; omega
  have loopS := Runs.loop_inv (m := m) (w := w) (sp := inner)
    (c := .op .and (Expr.lt (.var 8) (.var 7)) (Expr.eq (.var 9) (.lit (none64 : Nat).toUInt64)))
    (body := .block [.ite (Expr.eq (Expr.ld (Expr.var 0 + 16 + 8 * Expr.var 8)) (.var 6)) (.block [.set 9 (.var 8)])
      .skip, .set 8 (Expr.var 8 + 1)])
    invS (fun env _ => selectors.length - (env 8).toNat) (fun env cur _ => ⟨_, rfl⟩)
    (by
      intro env cur v hinv cond nonzero
      obtain ⟨hm, keep, i, hi, e8, status⟩ := hinv
      subst hm
      have g7 : env 7 = n.toUInt64 := by rw [keep 7 (by decide), f7]
      have nLen : n = selectors.length := paired.symm
      have more : i < selectors.length ∧ env 9 = (none64 : Nat).toUInt64 := by
        rw [eval_alu (eval_cmp_lt (x := i.toUInt64) (y := n.toUInt64) (by simp [eval, e8]) (by simp [eval, g7]))
          (eval_cmp_eq (x := env 9) (y := (none64 : Nat).toUInt64) rfl rfl)] at cond
        have v1 := Option.some.inj cond
        by_cases lt : i < n <;> by_cases nn : env 9 = (none64 : Nat).toUInt64 <;>
          simp [aluResult, nn, ofNat_lt_ofNat i n (by omega) (by omega), lt] at v1
        · exact ⟨by omega, nn⟩
        all_goals (subst v1; simp_all)
      obtain ⟨lt, nn⟩ := more
      have notYet : ∀ k (hk : k < i), selectors[k]'(by omega) ≠ s := by
        rcases status with ⟨_, none_⟩ | ⟨idx, hidx, e9, _, _⟩
        · exact none_
        · exact absurd (e9.symm.trans nn) (noneBig idx (by omega))
      obtain ⟨sw, sa⟩ := selWord i lt
      have addr : (UInt64.ofNat p + 16 + 8 * UInt64.ofNat i).toNat = p + 16 + 8 * i := by
        rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' (lt_size (by omega)),
          UInt64.toNat_ofNat_of_lt' (lt_size (by omega))]; simp; omega
      have test : eval w env mem (Expr.eq (Expr.ld (Expr.var 0 + 16 + 8 * Expr.var 8)) (.var 6)) =
          some (if selectors[i]'(by omega) = s then 1 else 0) := by
        rw [eval_cmp_eq (x := (selectors[i]'(by omega)).toUInt64) (y := s.toUInt64)
          (by simp [Expr.ld, eval, keep 0 (by decide), f0, e8, aluResult, Width.bytes, addr, sa, sw])
          (by simp [eval, keep 6 (by decide), f6])]
        have := selRange i lt
        by_cases same : selectors[i]'(by omega) = s <;>
          simp [same, ofNat_eq_ofNat (selectors[i]'(by omega)) s (by omega) (by omega)]
      by_cases same : selectors[i]'(by omega) = s
      · refine ⟨assign (assign env 9 i.toUInt64) 8 (i + 1).toUInt64, mem,
          Runs.block_cons (Runs.ite_true 1 (by rw [test]; simp [same]) (by decide)
            (Runs.set _ _ _ _ _ 9 _ _ (by simp [eval, e8])))
            (Runs.set _ _ _ _ _ 8 _ _ (by simp [eval, assign, e8, aluResult])),
          ⟨rfl, fun k hk => by simp [assign, show k ≠ 8 by omega, show k ≠ 9 by omega, keep k hk], i + 1, lt,
            by simp [assign], Or.inr ⟨i, by omega, by simp [assign], same, notYet⟩⟩, ?_⟩
        simp [assign, e8, toNat_toUInt64 i (by omega), toNat_toUInt64 (i + 1) (by omega)]; omega
      · refine ⟨assign env 8 (i + 1).toUInt64, mem,
          Runs.block_cons (Runs.ite_false (by rw [test]; simp [same]) (Runs.skip _ _ _ _ _))
            (Runs.set _ _ _ _ _ 8 _ _ (by simp [eval, e8, aluResult])),
          ⟨rfl, fun k hk => by simp [assign, show k ≠ 8 by omega, keep k hk], i + 1, lt, by simp [assign],
            Or.inl ⟨by simp [assign, nn], fun k hk => by
              by_cases last : k = i
              · subst last; exact same
              · exact notYet k (by omega)⟩⟩, ?_⟩
        simp [assign, e8, toNat_toUInt64 i (by omega), toNat_toUInt64 (i + 1) (by omega)]; omega)
  obtain ⟨env₄, mem₄, ranS, ⟨hm, keep₄, i, hi, e8, status⟩, exitS⟩ := loopS env₃ mem
    ⟨rfl, fun _ _ => rfl, 0, Nat.zero_le _, by simp [env₃, assign], Or.inl ⟨by simp [env₃, assign],
      fun k hk => absurd hk (Nat.not_lt_zero _)⟩⟩
  subst hm
  have nLen : n = selectors.length := paired.symm
  have g : ∀ k, k < 8 → env₄ k = env₃ k := keep₄
  -- The selector test after the search: a match, and a selector in the declared range.
  let env₅ := assign env₄ 5 (codeSelector : Nat).toUInt64
  have sel6 : env₅ 6 = s.toUInt64 := by simp [env₅, assign, g 6 (by decide), f6]
  have neTest : eval w env₅ mem (Expr.ne (.var 9) (.lit (none64 : Nat).toUInt64)) =
      some (if env₅ 9 = (none64 : Nat).toUInt64 then 0 else 1) := by
    rw [show Expr.ne (.var 9) (.lit (none64 : Nat).toUInt64) = .cmp .ne (.var 9) (.lit (none64 : Nat).toUInt64)
      from rfl, eval_cmp .ne rfl rfl]
    by_cases a : env₅ 9 = (none64 : Nat).toUInt64 <;> simp [a, Cond.holds]
  have l1 : (1 : UInt64) ≤ s.toUInt64 ↔ 1 ≤ s := by
    rw [show (1 : UInt64) = UInt64.ofNat 1 from rfl, Nat.toUInt64_eq]; exact ofNat_le_iff 1 s (by decide) (by omega)
  have l2 : s.toUInt64 ≤ 127 ↔ s ≤ 127 := by
    rw [show (127 : UInt64) = UInt64.ofNat 127 from rfl, Nat.toUInt64_eq]; exact ofNat_le_iff s 127 (by omega) (by decide)
  have selTest : eval w env₅ mem (.op .and (.op .and (Expr.ne (.var 9) (.lit (none64 : Nat).toUInt64))
      (Expr.le 1 (.var 6))) (Expr.le (.var 6) 127)) =
      some (if env₅ 9 ≠ (none64 : Nat).toUInt64 ∧ 1 ≤ s ∧ s ≤ 127 then 1 else 0) := by
    rw [eval_alu (eval_alu neTest (eval_cmp_le (x := 1) (y := s.toUInt64) rfl (by simp [eval, sel6])))
      (eval_cmp_le (x := s.toUInt64) (y := 127) (by simp [eval, sel6]) rfl)]
    by_cases a : env₅ 9 = (none64 : Nat).toUInt64 <;> by_cases b : 1 ≤ s <;> by_cases c : s ≤ 127 <;>
      simp [aluResult, a, b, c, l1, l2] <;> split <;> rfl
  -- The body through the search and the selector code.
  have through : ∀ env' mem' (r : UInt64) (tail : Stmt), Runs m w inner env₅ mem tail env' mem' →
      tail = .ite (.op .and (.op .and (Expr.ne (.var 9) (.lit (none64 : Nat).toUInt64)) (Expr.le 1 (.var 6)))
                  (Expr.le (.var 6) 127))
                (.block [.call "ssz_plan_skip" [Expr.var 0 + 16 + 8 * Expr.var 7, .var 9] 10,
                  .call "ssz_plan_width" [.var 10] 11, .set 12 (Expr.ld (Expr.var 1 + 24)),
                  .set 5 (.lit (codePart : Nat).toUInt64),
                  .ite (.op .or (Expr.eq (.var 11) (.lit (none64 : Nat).toUInt64)) (Expr.eq (.var 12) (.var 11)))
                    (.block [.set 5 (.lit (codeCapacity : Nat).toUInt64),
                      .ite (Expr.lt (.var 12) (.var 4))
                        (.block [Stmt.st1 (.var 3) (.var 6),
                          .call "ssz_copy" [Expr.var 3 + 1, Expr.ld (Expr.var 1 + 16), .var 12] 13,
                          .set 5 (Expr.var 12 + 1)]) .skip]) .skip]) .skip →
      env' 5 = r → Calls m w "ssz_assemble_union" sp args mem r mem' := by
    intro env' mem' r tail ran shape answer
    subst shape
    exact head env' mem' r _ (Runs.block_append prefix₃ (Runs.block_cons ranS
      (Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) ran))) one rfl answer
  rcases status with ⟨e9, none_⟩ | ⟨idx, hidx, e9, hit, before⟩
  · -- No selector matched: refused.
    have all : i = selectors.length := by
      rw [eval_alu (eval_cmp_lt (x := i.toUInt64) (y := n.toUInt64) (by simp [eval, e8])
        (by simp [eval, g 7 (by decide), f7])) (eval_cmp_eq (x := env₄ 9) (y := (none64 : Nat).toUInt64) rfl rfl)]
        at exitS
      have v := Option.some.inj exitS
      by_cases lt : i < n
      · simp [aluResult, e9, ofNat_lt_ofNat i n (by omega) (by omega), lt] at v
      · omega
    subst all
    have refused : assemble (.compatibleUnion selectors options) [sel, body] = .error (.unknownSelector s) := by
      simp [assemble, one, lookupOption_none selectors options s paired none_, throw, throwThe,
        MonadExceptOf.throw, Bind.bind, Except.bind, s]
    rw [refused]
    exact through _ _ _ _ (Runs.ite_false (by rw [selTest]; simp [env₅, assign, e9]) (Runs.skip _ _ _ _ _)) rfl
      (by simp [env₅, assign, assembleOutcome, errCode])
  -- The first match names the option.
  have idxLen : idx < selectors.length := by omega
  have idxOpt : idx < options.length := by omega
  have range := selRange idx idxLen
  rw [hit] at range
  let option := options[idx]
  have lookup := lookupOption_first selectors options s idx paired idxLen hit before
  have optSound : option.wellFormed = .ok () := optionsSound _ (List.getElem_mem _)
  have optThin : narrow option = true := optionsThin _ (List.getElem_mem _)
  -- Where the option's words start: past the tag, the count, the selectors, and the options before it.
  let q₀ := p + 16 + 8 * n
  have planOptions : PlanAt w mem q₀ (wordsAll options) := by
    have := (show PlanAt w mem p (([12, n] ++ selectors) ++ wordsAll options) from plan).right
    rw [show p + 8 * ([12, n] ++ selectors).length = q₀ by simp [q₀, nLen]; omega] at this
    exact this
  have split : wordsAll options = wordsAll (options.take idx) ++ (words option ++ wordsAll (options.drop (idx + 1))) := by
    have e : options.drop idx = option :: options.drop (idx + 1) := List.drop_eq_getElem_cons idxOpt
    calc wordsAll options = wordsAll (options.take idx ++ options.drop idx) := by
          rw [List.take_append_drop]
      _ = _ := by rw [wordsAll_append, e]; simp [wordsAll]
  rw [split] at planOptions
  have planBefore := planOptions.left
  let q₁ := q₀ + 8 * (wordsAll (options.take idx)).length
  have planOption : PlanAt w mem q₁ (words option) := planOptions.right.left
  have q₁Bound : q₁ + 8 * (words option).length ≤ 2 ^ 63 := by
    have := planOption.1; simpa [addressBound] using this
  have nextAll : ∀ d ∈ options.take idx, NextOk m w d :=
    fun d member => next_ok m w linked d (optionsSound d (List.mem_of_mem_take member))
  have deepTake := deepest_take options idx
  have deepOpt := nesting_le_deepest options option (List.getElem_mem _)
  have skipped := skip_ok m w linked (options.take idx) nextAll inner mem q₀ planBefore (by
    simp only [inner]; have := Nat.mul_le_mul_left walkLevel deepTake
    have := Nat.mul_le_mul_left (widthLevel + walkLevel) (Nat.le_refl (Desc.deepestNesting options)); rw [ur] at room
    simp only [Nat.add_mul] at *; omega)
  have measured := width_ok m w linked option optSound optThin inner mem q₁ planOption (by
    simp only [inner]; have := Nat.mul_le_mul_left (widthLevel + walkLevel) deepOpt; rw [ur] at room; omega)
  have takeLen : (options.take idx).length = idx := by simp; omega
  rw [takeLen] at skipped
  -- The option's checks, in the reference.
  have checked : checkSelector s = .ok () := by simp [checkSelector, minSelector, maxSelector]; omega
  obtain ⟨a24, c24⟩ := readT 24 (by omega)
  obtain ⟨a16, c16⟩ := readT 16 (by omega)
  let env₆ := assign (assign (assign (assign env₅ 10 q₁.toUInt64) 11 (widthWord option)) 12 body.size.toUInt64) 5
    (codePart : Nat).toUInt64
  have qWord : (UInt64.ofNat p + 16 + 8 * UInt64.ofNat n) = q₀.toUInt64 := by
    simp [q₀, Nat.toUInt64_eq]
  have checks : Runs m w inner env₅ mem (.block [.call "ssz_plan_skip" [Expr.var 0 + 16 + 8 * Expr.var 7, .var 9] 10,
      .call "ssz_plan_width" [.var 10] 11, .set 12 (Expr.ld (Expr.var 1 + 24)),
      .set 5 (.lit (codePart : Nat).toUInt64)]) env₆ mem := by
    refine Runs.block_cons (Runs.call (values := [q₀.toUInt64, idx.toUInt64]) ?_ skipped)
      (Runs.block_cons (Runs.call (values := [q₁.toUInt64]) (by simp [eval, assign, q₁]) measured)
        (Runs.block_cons (Runs.set _ _ _ _ _ 12 _ _ ?_) (Runs.set _ _ _ _ _ 5 _ _ rfl)))
    · simp [eval, env₅, assign, g 0 (by decide), g 7 (by decide), f0, f7, e9, aluResult, qWord]
    · simp [Expr.ld, eval, assign, env₅, g 1 (by decide), env₃, env₂, env₁, entryEnv, args, aluResult, Width.bytes,
        a24, c24, r24, show (parts + 24) % 18446744073709551616 = parts + 24 from Nat.mod_eq_of_lt (by omega)]
  have bodySmall : body.size < 2 ^ 64 := by omega
  -- The part must fit the option's width.
  have fitTest : eval w env₆ mem (.op .or (Expr.eq (.var 11) (.lit (none64 : Nat).toUInt64))
      (Expr.eq (.var 12) (.var 11))) = some (if (partFits option body).toBool then 1 else 0) := by
    rw [eval_alu (eval_cmp_eq (x := widthWord option) (y := (none64 : Nat).toUInt64) (by simp [eval, env₆, assign]) rfl)
      (eval_cmp_eq (x := body.size.toUInt64) (y := widthWord option) (by simp [eval, env₆, assign])
        (by simp [eval, env₆, assign]))]
    cases fixed : option.fixedSize with
    | none =>
      simp [widthWord, fixed, partFits, aluResult, Except.toBool] <;> split <;> rfl
    | some width =>
      have wSmall := narrow_width option optThin width fixed
      have notNone := widthWord_none option width fixed wSmall
      simp only [widthWord, fixed] at notNone ⊢
      simp only [partFits, fixed, bne_iff_ne, ne_eq]
      by_cases same : body.size = width
      · simp [same, notNone, aluResult, Except.toBool] <;> split <;> rfl
      · have : body.size.toUInt64 ≠ width.toUInt64 := by
          intro h; exact same ((ofNat_eq_ofNat _ _ bodySmall (by omega)).mp h)
        have nn : UInt64.ofNat width ≠ 18446744073709551615 := by
          intro h; have := congrArg UInt64.toNat h; simp [UInt64.toNat_ofNat] at this; omega
        simp [same, nn, this, aluResult, Except.toBool]
  have reach : ∀ env' mem' (r : UInt64), Runs m w inner env₆ mem (.ite (.op .or (Expr.eq (.var 11)
      (.lit (none64 : Nat).toUInt64)) (Expr.eq (.var 12) (.var 11)))
        (.block [.set 5 (.lit (codeCapacity : Nat).toUInt64),
          .ite (Expr.lt (.var 12) (.var 4))
            (.block [Stmt.st1 (.var 3) (.var 6),
              .call "ssz_copy" [Expr.var 3 + 1, Expr.ld (Expr.var 1 + 16), .var 12] 13,
              .set 5 (Expr.var 12 + 1)]) .skip]) .skip) env' mem' →
      env' 5 = r → Calls m w "ssz_assemble_union" sp args mem r mem' := by
    intro env' mem' r ran answer
    refine through env' mem' r _ (Runs.ite_true 1 ?_ (by decide)
      (Runs.block_append checks (Runs.block_cons ran (Runs.block_nil _ _ _ _ _)))) rfl answer
    have idxNe : UInt64.ofNat idx ≠ 18446744073709551615 := by
      intro h; have := congrArg UInt64.toNat h; simp [UInt64.toNat_ofNat] at this; omega
    rw [selTest]
    simp [env₅, assign, e9, idxNe, range.1, range.2]
  have reduce : assemble (.compatibleUnion selectors options) [sel, body] =
      (partFits option body).bind fun _ => .ok (sel ++ body) := by
    simp [assemble, one, lookup, checked, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, s, option,
      pure, Except.pure]
  rw [reduce]
  cases fitsPart : partFits option body with
  | error e =>
    have code : errCode e = codePart := by
      simp only [partFits] at fitsPart
      split at fitsPart
      · split at fitsPart
        · cases fitsPart; rfl
        · cases fitsPart
      · cases fitsPart
    exact reach _ _ _ (Runs.ite_false (by rw [fitTest]; simp [fitsPart, Except.toBool]) (Runs.skip _ _ _ _ _))
      (by simp [env₆, assign, assembleOutcome, code, Except.bind])
  | ok u =>
    simp only [Except.bind, assembleOutcome, ByteArray.size_append, one]
    let env₇ := assign env₆ 5 (codeCapacity : Nat).toUInt64
    have capSmall : cap < 2 ^ 64 := by omega
    have capTest : eval w env₇ mem (Expr.lt (.var 12) (.var 4)) = some (if body.size < cap then 1 else 0) := by
      rw [eval_cmp_lt (x := body.size.toUInt64) (y := cap.toUInt64) (by simp [eval, env₇, env₆, assign])
        (by simp [eval, env₇, env₆, env₅, assign, g 4 (by decide), env₃, env₂, env₁, entryEnv, args])]
      simp only [Nat.toUInt64_eq, ofNat_lt_ofNat _ cap bodySmall capSmall]
    by_cases fitsOut : 1 + body.size ≤ cap
    case neg =>
      rw [if_neg fitsOut]
      exact reach _ _ _ (Runs.ite_true 1 (by rw [fitTest]; simp [fitsPart, Except.toBool]) (by decide)
        (Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) (Runs.ite_false (by rw [capTest]; simp; omega)
          (Runs.skip _ _ _ _ _)))) (by simp [assign])
    rw [if_pos fitsOut]
    -- The selector byte, then the body after it.
    have apart1 := to.apartParts 1 (by simp) (by simp)
    simp at apart1
    have stored := Runs.store m w inner env₇ mem .b1 (.var 3) (.var 6) out.toUInt64 s.toUInt64
      (by simp [eval, env₇, env₆, env₅, assign, g 3 (by decide), env₃, env₂, env₁, entryEnv, args])
      (by simp [eval, env₇, env₆, assign, sel6])
      (by rw [toNat_toUInt64 _ (by omega)]; exact access_sub to.writable (by omega) (by simp [Width.bytes]; omega))
    rw [toNat_toUInt64 _ (by omega), Width.bytes, placed_one mem out sel one _ (by
      simp [qwordByte_zero, s])] at stored
    have kept16 : readLE (placed mem out sel) (parts + 16) 8 = p1.toUInt64 := by
      rw [← r16]
      apply readLE_congr
      intro k hk
      simp only [placed, store, one]
      rw [if_neg (by have := to.apartTable; simp at this; omega)]
    have copiedNow := copy_correct m w linked inner (placed mem out sel) (out + 1).toUInt64 p1.toUInt64
      body.size.toUInt64 (by simp only [inner]; rw [ur] at room; omega)
      (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]; simpa using at_.readable 1 (by simp))
      (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]
          exact access_sub to.writable (by omega) (by omega))
      (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]; omega)
    have memEq : copied (placed mem out sel) (out + 1) p1 body.size = placed mem out (sel ++ body) := by
      have := copied_placed mem out sel body p1 (by simpa using at_.bytes 1 (by simp)) (by rw [one]; omega)
      rwa [one] at this
    rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), memEq] at copiedNow
    refine reach _ _ _ (Runs.ite_true 1 (by rw [fitTest]; simp [fitsPart, Except.toBool]) (by decide)
      (Runs.block_cons (Runs.set _ _ _ _ _ 5 _ _ rfl) (Runs.ite_true 1 (by rw [capTest]; simp; omega) (by decide)
        (Runs.block_cons stored (Runs.block_cons (Runs.call (values := [(out + 1).toUInt64, p1.toUInt64,
          body.size.toUInt64]) ?_ copiedNow) (Runs.set _ _ _ _ _ 5 _ (body.size + 1).toUInt64
            (by simp [eval, assign, env₇, env₆, aluResult]))))))) (by simp [assign]; first | rfl | rw [Nat.add_comm] | rw [UInt64.add_comm] | omega)
    simp [Expr.ld, eval, assign, env₇, env₆, env₅, g 1 (by decide), g 3 (by decide), env₃, env₂, env₁, entryEnv,
      args, aluResult, Width.bytes, a16, c16, kept16,
      show (parts + 16) % 18446744073709551616 = parts + 16 from Nat.mod_eq_of_lt (by omega)]

end Ssz.Native.Driver
