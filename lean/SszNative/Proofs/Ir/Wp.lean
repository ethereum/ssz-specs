import SszNative.Proofs.Ir.Logic
import SszNative.Ir.Dsl

/-!
Running a program forward from a state, toward a condition on the state it ends in.

A statement reaches a condition when it runs to some state meeting it.
Each kind of statement reaches a condition exactly when its parts do, so these facts rewrite a program's run into the
conditions on what it computes, one statement at a time.
-/

namespace EthLib.Consensus.Ssz.Native.Ir

open EthLib.Consensus.Ssz.Native.Asm

/-- A statement runs from variables and memory to some state meeting a condition. -/
def Wp (m : Module) (w : World) (sp : Nat) (s : Stmt) (env : Env) (mem : Memory) (Q : Env → Memory → Prop) : Prop :=
  ∃ env' mem', Runs m w sp env mem s env' mem' ∧ Q env' mem'

variable {m : Module} {w : World} {sp : Nat}

/-- A weaker condition is reached wherever a stronger one is. -/
theorem Wp.mono {s : Stmt} {env : Env} {mem : Memory} {Q Q' : Env → Memory → Prop} (h : Wp m w sp s env mem Q)
    (imp : ∀ env mem, Q env mem → Q' env mem) : Wp m w sp s env mem Q' := by
  obtain ⟨e, m', r, q⟩ := h
  exact ⟨e, m', r, imp _ _ q⟩

/-- A run with some fuel names the statement's first step: there is fuel left to take it. -/
theorem runs_succ {s : Stmt} {env env' : Env} {mem mem' : Memory} (h : Runs m w sp env mem s env' mem') :
    ∃ fuel, exec m w (fuel + 1) sp env mem s = some (env', mem') := by
  obtain ⟨f, e⟩ := h
  cases f with
  | zero => simp [exec] at e
  | succ f => exact ⟨f, e⟩

/-- Doing nothing reaches what holds already. -/
@[simp] theorem wp_skip (env : Env) (mem : Memory) (Q : Env → Memory → Prop) :
    Wp m w sp .skip env mem Q ↔ Q env mem := by
  constructor
  · rintro ⟨e, m', r, q⟩
    obtain ⟨f, h⟩ := runs_succ r
    simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact q
  · intro q; exact ⟨env, mem, Runs.skip m w sp env mem, q⟩

/-- An assignment reaches what holds of its value. -/
@[simp] theorem wp_set (x : Nat) (e : Expr) (env : Env) (mem : Memory) (Q : Env → Memory → Prop) :
    Wp m w sp (.set x e) env mem Q ↔ ∃ v, eval w env mem e = some v ∧ Q (assign env x v) mem := by
  constructor
  · rintro ⟨e', m', r, q⟩
    obtain ⟨f, h⟩ := runs_succ r
    simp only [exec] at h
    cases hv : eval w env mem e with
    | none => simp [hv] at h
    | some v =>
      simp only [hv, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨v, rfl, q⟩
  · rintro ⟨v, hv, q⟩; exact ⟨_, _, Runs.set m w sp env mem x e v hv, q⟩

/-- A store reaches what holds of the memory it leaves. -/
@[simp] theorem wp_store (wd : Width) (a v : Expr) (env : Env) (mem : Memory) (Q : Env → Memory → Prop) :
    Wp m w sp (.store wd a v) env mem Q ↔ ∃ x y, eval w env mem a = some x ∧ eval w env mem v = some y ∧
      w.access x.toNat wd.bytes = true ∧ Q env (store mem x.toNat wd.bytes (qwordByte y)) := by
  constructor
  · rintro ⟨e', m', r, q⟩
    obtain ⟨f, h⟩ := runs_succ r
    simp only [exec, bind, Option.bind] at h
    cases ha : eval w env mem a with
    | none => simp [ha] at h
    | some x =>
      cases hb : eval w env mem v with
      | none => simp [ha, hb] at h
      | some y =>
        by_cases ok : w.access x.toNat wd.bytes = true
        · simp only [ha, hb, ok, ite_true, pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨x, y, rfl, rfl, ok, q⟩
        · simp [ha, hb, ok] at h
  · rintro ⟨x, y, ha, hb, ok, q⟩; exact ⟨_, _, Runs.store m w sp env mem wd a v x y ha hb ok, q⟩

/-- Two statements reach what the second reaches from where the first ends. -/
@[simp] theorem wp_seq (a b : Stmt) (env : Env) (mem : Memory) (Q : Env → Memory → Prop) :
    Wp m w sp (.seq a b) env mem Q ↔ Wp m w sp a env mem (fun env mem => Wp m w sp b env mem Q) := by
  constructor
  · rintro ⟨e', m', r, q⟩
    obtain ⟨f, h⟩ := runs_succ r
    simp only [exec, bind, Option.bind] at h
    cases ha : exec m w f sp env mem a with
    | none => simp [ha] at h
    | some p =>
      simp only [ha] at h
      exact ⟨p.1, p.2, ⟨f, ha⟩, e', m', ⟨f, h⟩, q⟩
  · rintro ⟨e₂, m₂, ra, e₃, m₃, rb, q⟩; exact ⟨e₃, m₃, Runs.seq ra rb, q⟩

/-- A branch reaches what the branch its condition picks reaches. -/
@[simp] theorem wp_ite (c : Expr) (t e : Stmt) (env : Env) (mem : Memory) (Q : Env → Memory → Prop) :
    Wp m w sp (.ite c t e) env mem Q ↔
      ∃ v, eval w env mem c = some v ∧ (if v ≠ 0 then Wp m w sp t env mem Q else Wp m w sp e env mem Q) := by
  constructor
  · rintro ⟨e', m', r, q⟩
    obtain ⟨f, h⟩ := runs_succ r
    simp only [exec, bind, Option.bind] at h
    cases hc : eval w env mem c with
    | none => simp [hc] at h
    | some v =>
      refine ⟨v, rfl, ?_⟩
      by_cases nz : v = 0
      · subst nz; simp only [hc, bne_self_eq_false, Bool.false_eq_true, ite_false] at h
        simp only [ne_eq, not_true_eq_false, ite_false]; exact ⟨e', m', ⟨f, h⟩, q⟩
      · have : (v != 0) = true := by simpa using nz
        simp only [hc, this, ite_true] at h
        simp only [ne_eq, nz, not_false_eq_true, ite_true]; exact ⟨e', m', ⟨f, h⟩, q⟩
  · rintro ⟨v, hc, h⟩
    by_cases nz : v = 0
    · subst nz; simp only [ne_eq, not_true_eq_false, ite_false] at h
      obtain ⟨e', m', r, q⟩ := h; exact ⟨e', m', Runs.ite_false hc r, q⟩
    · simp only [ne_eq, nz, not_false_eq_true, ite_true] at h
      obtain ⟨e', m', r, q⟩ := h; exact ⟨e', m', Runs.ite_true v hc nz r, q⟩

/-- A call reaches what holds of its result. -/
@[simp] theorem wp_call (f : String) (args : List Expr) (dst : Nat) (env : Env) (mem : Memory)
    (Q : Env → Memory → Prop) :
    Wp m w sp (.call f args dst) env mem Q ↔ ∃ values r mem', args.mapM (eval w env mem) = some values ∧
      Calls m w f sp values mem r mem' ∧ Q (assign env dst r) mem' := by
  constructor
  · rintro ⟨e', m', r, q⟩
    obtain ⟨f', h⟩ := runs_succ r
    rw [exec_call] at h
    simp only [bind, Option.bind] at h
    cases hv : args.mapM (eval w env mem) with
    | none => simp [hv] at h
    | some values =>
      simp only [hv] at h
      cases hc : callSpec m w f' f sp values mem with
      | none => simp [hc] at h
      | some p =>
        simp only [hc, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨values, p.1, p.2, rfl, ⟨f', hc⟩, q⟩
  · rintro ⟨values, r, mem', hv, hc, q⟩; exact ⟨_, _, Runs.call hv hc, q⟩

/-- The statements of a block run one after the other. -/
@[simp] theorem wp_block_nil (env : Env) (mem : Memory) (Q : Env → Memory → Prop) :
    Wp m w sp (.block []) env mem Q ↔ Q env mem := wp_skip env mem Q

/-- A block of one is its statement. -/
@[simp] theorem wp_block_one (s : Stmt) (env : Env) (mem : Memory) (Q : Env → Memory → Prop) :
    Wp m w sp (.block [s]) env mem Q ↔ Wp m w sp s env mem Q := Iff.rfl

/-- A block runs its head, then the rest. -/
@[simp] theorem wp_block_cons (s t : Stmt) (rest : List Stmt) (env : Env) (mem : Memory) (Q : Env → Memory → Prop) :
    Wp m w sp (.block (s :: t :: rest)) env mem Q ↔
      Wp m w sp s env mem (fun env mem => Wp m w sp (.block (t :: rest)) env mem Q) := wp_seq _ _ _ _ _

/--
A loop with an invariant and a measure that every pass decreases ends where the invariant holds and the condition is
zero.
-/
theorem wp_loop {c : Expr} {body : Stmt} (inv : Env → Memory → Prop) (measure : Env → Memory → Nat)
    {env : Env} {mem : Memory} {Q : Env → Memory → Prop} (start : inv env mem)
    (pass : ∀ env mem, inv env mem → ∃ v, eval w env mem c = some v ∧
      (v ≠ 0 → Wp m w sp body env mem (fun env' mem' => inv env' mem' ∧ measure env' mem' < measure env mem)) ∧
      (v = 0 → Q env mem)) :
    Wp m w sp (.loop c body) env mem Q := by
  obtain ⟨e, m', r, i, done⟩ := Runs.loop_inv (m := m) (w := w) (sp := sp) (c := c) (body := body) inv measure
    (fun env mem h => (pass env mem h).elim fun v hv => ⟨v, hv.1⟩)
    (fun env mem v h hv nz => by
      obtain ⟨v', hv', step, _⟩ := pass env mem h
      rw [hv] at hv'; cases hv'
      obtain ⟨e, m', r, i, lt⟩ := step nz
      exact ⟨e, m', r, i, lt⟩) env mem start
  obtain ⟨v, hv, _, fin⟩ := pass e m' i
  rw [hv] at done; cases done
  exact ⟨e, m', r, fin rfl⟩

/-- A function's body reaching its result and memory is a call to it. -/
theorem Calls.of_wp {f : String} {args : List UInt64} {mem mem' : Memory} {fn : Fn} {r : UInt64}
    (hf : m.fns.lookup f = some fn) (room : w.stackLo + 8 + 8 * fn.frame ≤ sp) (count : args.length = fn.params)
    (hb : Wp m w (sp - 8 - 8 * fn.frame) fn.body (entryEnv args) mem
      (fun env' mem'' => eval w env' mem'' fn.result = some r ∧ mem'' = mem')) :
    Calls m w f sp args mem r mem' := by
  obtain ⟨e, m'', run, hr, rfl⟩ := hb
  exact Calls.fn hf room count run hr

/-! Stepping through the notation's statements, one at the head of a block at a time. -/

namespace Wp

open EthLib.Consensus.Ssz.Native.Ir.Stmt

variable {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {Q : Env → Memory → Prop}

/-- Two lists of statements run one after the other as their joined block. -/
theorem block_append (a b : List Stmt) (env : Env) (mem : Memory) :
    Wp m w sp (.block (a ++ b)) env mem Q ↔
      Wp m w sp (.block a) env mem (fun env mem => Wp m w sp (.block b) env mem Q) := by
  induction a generalizing env mem with
  | nil => simp
  | cons s rest ih =>
    cases rest with
    | nil =>
      cases b with
      | nil => simp
      | cons t more => simp
    | cons t more =>
      simp only [List.cons_append, wp_block_cons]
      constructor
      · intro h; exact h.mono fun e m' h' => (ih e m').mp h'
      · intro h; exact h.mono fun e m' h' => (ih e m').mpr h'

/-- The head statement of a block, then the rest. -/
theorem block_cons (s : Stmt) (rest : List Stmt) :
    Wp m w sp (.block (s :: rest)) env mem Q ↔
      Wp m w sp s env mem (fun env mem => Wp m w sp (.block rest) env mem Q) := by
  cases rest with
  | nil => simp
  | cons t more => simp

/-- An empty block reaches the condition it starts in. -/
theorem done (h : Q env mem) : Wp m w sp (.block []) env mem Q := (wp_block_nil env mem Q).mpr h

/-- An assignment at the head of a block. -/
theorem set {x : Var} {e : Expr} {rest : List Stmt} {v : UInt64} (h : eval w env mem e = some v)
    (k : Wp m w sp (.block rest) (assign env x.idx v) mem Q) : Wp m w sp (.block ((x ::= e) :: rest)) env mem Q :=
  (block_cons _ _).mpr ((wp_set _ _ _ _ _).mpr ⟨v, h, k⟩)

/-- A branch at the head of a block, its condition holding. -/
theorem ifElse_t {c : Expr} {yes no rest : List Stmt} {v : UInt64} (h : eval w env mem c = some v) (nz : v ≠ 0)
    (k : Wp m w sp (.block (yes ++ rest)) env mem Q) : Wp m w sp (.block (ifElse c yes no :: rest)) env mem Q := by
  rw [block_cons, ifElse, wp_ite]; refine ⟨v, h, ?_⟩; simp only [ne_eq, nz, not_false_eq_true, ite_true]
  exact (block_append _ _ _ _).mp k

/-- A branch at the head of a block, its condition failing. -/
theorem ifElse_f {c : Expr} {yes no rest : List Stmt} (h : eval w env mem c = some 0)
    (k : Wp m w sp (.block (no ++ rest)) env mem Q) : Wp m w sp (.block (ifElse c yes no :: rest)) env mem Q := by
  rw [block_cons, ifElse, wp_ite]; refine ⟨0, h, ?_⟩; simp only [ne_eq, not_true_eq_false, ite_false]
  exact (block_append _ _ _ _).mp k

/-- A guarded block at the head of a block, its condition holding. -/
theorem when_t {c : Expr} {yes rest : List Stmt} {v : UInt64} (h : eval w env mem c = some v) (nz : v ≠ 0)
    (k : Wp m w sp (.block (yes ++ rest)) env mem Q) : Wp m w sp (.block (when c yes :: rest)) env mem Q := by
  rw [block_cons, when, wp_ite]; refine ⟨v, h, ?_⟩; simp only [ne_eq, nz, not_false_eq_true, ite_true]
  exact (block_append _ _ _ _).mp k

/-- A guarded block at the head of a block, its condition failing. -/
theorem when_f {c : Expr} {yes rest : List Stmt} (h : eval w env mem c = some 0)
    (k : Wp m w sp (.block rest) env mem Q) : Wp m w sp (.block (when c yes :: rest)) env mem Q := by
  rw [block_cons, when, wp_ite]; refine ⟨0, h, ?_⟩; simp only [ne_eq, not_true_eq_false, ite_false]
  exact (wp_skip _ _ _).mpr k

/-- A call at the head of a block. -/
theorem call {x : Var} {f : String} {args : List Expr} {rest : List Stmt} {values : List UInt64} {r : UInt64}
    {mem' : Memory} (hv : args.mapM (eval w env mem) = some values) (hc : Calls m w f sp values mem r mem')
    (k : Wp m w sp (.block rest) (assign env x.idx r) mem' Q) :
    Wp m w sp (.block (callInto x f args :: rest)) env mem Q :=
  (block_cons _ _).mpr ((wp_call _ _ _ _ _ _).mpr ⟨values, r, mem', hv, hc, k⟩)

/-- A store at the head of a block. -/
theorem store {a v : Expr} {wd : Width} {rest : List Stmt} {x y : UInt64} (ha : eval w env mem a = some x)
    (hv : eval w env mem v = some y) (ok : w.access x.toNat wd.bytes = true)
    (k : Wp m w sp (.block rest) env (Asm.store mem x.toNat wd.bytes (qwordByte y)) Q) :
    Wp m w sp (.block (.store wd a v :: rest)) env mem Q :=
  (block_cons _ _).mpr ((wp_store _ _ _ _ _ _).mpr ⟨x, y, ha, hv, ok, k⟩)

/-- A loop at the head of a block: the loop, then the rest. -/
theorem loop {c : Expr} {body rest : List Stmt}
    (k : Wp m w sp (while_ c body) env mem (fun env mem => Wp m w sp (.block rest) env mem Q)) :
    Wp m w sp (.block (while_ c body :: rest)) env mem Q :=
  (block_cons _ _).mpr k

/-- A statement standing alone is a block of one. -/
theorem single {s : Stmt} (k : Wp m w sp (.block [s]) env mem Q) : Wp m w sp s env mem Q := k

/-- A guarded assignment at the head of a block: the variable takes the value when the condition holds. -/
theorem when_assign {x : Var} {c e : Expr} {rest : List Stmt} {cv ev : UInt64} (hc : eval w env mem c = some cv)
    (he : eval w env mem e = some ev)
    (k : Wp m w sp (.block rest) (assign env x.idx (if cv ≠ 0 then ev else env x.idx)) mem Q) :
    Wp m w sp (.block (when c [x ::= e] :: rest)) env mem Q := by
  by_cases z : cv = 0
  · subst z
    refine when_f hc ?_
    have : assign env x.idx (env x.idx) = env := by
      funext y; simp only [Asm.assign]; split <;> simp_all
    simpa [this] using k
  · refine when_t hc z ?_
    simp only [List.singleton_append]
    exact set he (by simpa [z] using k)

end Wp

end EthLib.Consensus.Ssz.Native.Ir
