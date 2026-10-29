import SszNative.Proofs.Ir.Call

/-!
Reasoning about programs of the small language without counting fuel.

A statement runs from some variables and memory to others when some fuel gives it that meaning.
More fuel never changes a meaning, so runs compose: the fuel of the whole is the larger of the parts.
-/

namespace EthLib.Consensus.Ssz.Native.Ir

open EthLib.Consensus.Ssz.Native.Asm

/-- A statement runs from variables and memory to others, with some fuel, from a stack pointer. -/
def Runs (m : Module) (w : World) (sp : Nat) (env : Env) (mem : Memory) (s : Stmt) (env' : Env) (mem' : Memory) :
    Prop :=
  ∃ fuel, exec m w fuel sp env mem s = some (env', mem')

/-- A meaning at some fuel holds at any larger fuel. -/
theorem exec_le (m : Module) (w : World) {fuel fuel' sp : Nat} {env : Env} {mem : Memory} {s : Stmt}
    {r : Env × Memory} (h : exec m w fuel sp env mem s = some r) (le : fuel ≤ fuel') :
    exec m w fuel' sp env mem s = some r := by
  obtain ⟨more, rfl⟩ := Nat.exists_eq_add_of_le le
  exact exec_mono m w fuel more sp env mem s r h

/-- Doing nothing runs to the same state. -/
theorem Runs.skip (m : Module) (w : World) (sp : Nat) (env : Env) (mem : Memory) :
    Runs m w sp env mem .skip env mem := ⟨1, rfl⟩

/-- An assignment runs to the variables with the new value. -/
theorem Runs.set (m : Module) (w : World) (sp : Nat) (env : Env) (mem : Memory) (x : Nat) (e : Expr) (v : UInt64)
    (h : eval w env mem e = some v) : Runs m w sp env mem (.set x e) (assign env x v) mem :=
  ⟨1, by simp [exec, h]⟩

/-- A store to memory the program may use runs to the memory with its bytes written. -/
theorem Runs.store (m : Module) (w : World) (sp : Nat) (env : Env) (mem : Memory) (wd : Width) (a v : Expr)
    (x y : UInt64) (ha : eval w env mem a = some x) (hv : eval w env mem v = some y)
    (ok : w.access x.toNat wd.bytes) :
    Runs m w sp env mem (.store wd a v) env (store mem x.toNat wd.bytes (qwordByte y)) :=
  ⟨1, by simp [exec, ha, hv, ok, bind, Option.bind, pure]⟩

/-- Two statements run one after the other. -/
theorem Runs.seq {m : Module} {w : World} {sp : Nat} {env₁ env₂ env₃ : Env} {mem₁ mem₂ mem₃ : Memory} {a b : Stmt}
    (ha : Runs m w sp env₁ mem₁ a env₂ mem₂) (hb : Runs m w sp env₂ mem₂ b env₃ mem₃) :
    Runs m w sp env₁ mem₁ (.seq a b) env₃ mem₃ := by
  obtain ⟨fa, ea⟩ := ha; obtain ⟨fb, eb⟩ := hb
  refine ⟨max fa fb + 1, ?_⟩
  rw [exec]; simp only [bind, Option.bind]
  rw [exec_le m w ea (Nat.le_max_left _ _)]
  exact exec_le m w eb (Nat.le_max_right _ _)

/-- A branch with a nonzero condition runs its first statement. -/
theorem Runs.ite_true {m : Module} {w : World} {sp : Nat} {env env' : Env} {mem mem' : Memory} {c : Expr}
    {t e : Stmt} (v : UInt64) (hc : eval w env mem c = some v) (nz : v ≠ 0) (ht : Runs m w sp env mem t env' mem') :
    Runs m w sp env mem (.ite c t e) env' mem' := by
  obtain ⟨f, h⟩ := ht
  exact ⟨f + 1, by rw [exec]; simp [hc, nz, h, bind, Option.bind]⟩

/-- A branch with a zero condition runs its second statement. -/
theorem Runs.ite_false {m : Module} {w : World} {sp : Nat} {env env' : Env} {mem mem' : Memory} {c : Expr}
    {t e : Stmt} (hc : eval w env mem c = some 0) (he : Runs m w sp env mem e env' mem') :
    Runs m w sp env mem (.ite c t e) env' mem' := by
  obtain ⟨f, h⟩ := he
  exact ⟨f + 1, by rw [exec]; simp [hc, h, bind, Option.bind]⟩

/-- A loop whose condition is zero runs to the same state. -/
theorem Runs.loop_exit (m : Module) (w : World) (sp : Nat) (env : Env) (mem : Memory) (c : Expr) (body : Stmt)
    (hc : eval w env mem c = some 0) : Runs m w sp env mem (.loop c body) env mem :=
  ⟨1, by rw [exec]; simp [hc, bind, Option.bind, pure]⟩

/-- A loop whose condition is not zero runs its body, then itself again. -/
theorem Runs.loop_step {m : Module} {w : World} {sp : Nat} {env₁ env₂ env₃ : Env} {mem₁ mem₂ mem₃ : Memory}
    {c : Expr} {body : Stmt} (v : UInt64) (hc : eval w env₁ mem₁ c = some v) (nz : v ≠ 0)
    (hb : Runs m w sp env₁ mem₁ body env₂ mem₂) (hl : Runs m w sp env₂ mem₂ (.loop c body) env₃ mem₃) :
    Runs m w sp env₁ mem₁ (.loop c body) env₃ mem₃ := by
  obtain ⟨fb, eb⟩ := hb; obtain ⟨fl, el⟩ := hl
  refine ⟨max fb fl + 1, ?_⟩
  rw [exec]; simp only [hc, bind, Option.bind]
  have : (v == 0) = false := by simpa using nz
  simp only [this, Bool.false_eq_true]
  rw [exec_le m w eb (Nat.le_max_left _ _)]
  exact exec_le m w el (Nat.le_max_right _ _)

/--
A loop with an invariant and a measure that every pass decreases runs to a state where the invariant holds and the
condition is zero.
-/
theorem Runs.loop_inv {m : Module} {w : World} {sp : Nat} {c : Expr} {body : Stmt}
    (inv : Env → Memory → Prop) (measure : Env → Memory → Nat)
    (cond : ∀ env mem, inv env mem → ∃ v, eval w env mem c = some v)
    (pass : ∀ env mem v, inv env mem → eval w env mem c = some v → v ≠ 0 →
      ∃ env' mem', Runs m w sp env mem body env' mem' ∧ inv env' mem' ∧ measure env' mem' < measure env mem) :
    ∀ env mem, inv env mem →
      ∃ env' mem', Runs m w sp env mem (.loop c body) env' mem' ∧ inv env' mem' ∧ eval w env' mem' c = some 0 := by
  intro env mem
  induction h : measure env mem using Nat.strongRecOn generalizing env mem with
  | _ n ih =>
    intro hinv
    obtain ⟨v, hv⟩ := cond env mem hinv
    by_cases zero : v = 0
    · subst zero
      exact ⟨env, mem, Runs.loop_exit m w sp env mem c body hv, hinv, hv⟩
    · obtain ⟨env₂, mem₂, rb, inv₂, dec⟩ := pass env mem v hinv hv zero
      obtain ⟨env₃, mem₃, rl, inv₃, done⟩ := ih (measure env₂ mem₂) (by omega) env₂ mem₂ rfl inv₂
      exact ⟨env₃, mem₃, Runs.loop_step v hv zero rb rl, inv₃, done⟩

/-- Statements in order run as the block of them. -/
theorem Runs.block_cons {m : Module} {w : World} {sp : Nat} {env₁ env₂ env₃ : Env} {mem₁ mem₂ mem₃ : Memory}
    {s : Stmt} {rest : List Stmt} (hs : Runs m w sp env₁ mem₁ s env₂ mem₂)
    (hr : Runs m w sp env₂ mem₂ (.block rest) env₃ mem₃) : Runs m w sp env₁ mem₁ (.block (s :: rest)) env₃ mem₃ := by
  cases rest with
  | nil =>
    obtain ⟨f, e⟩ := hr
    cases f with
    | zero => simp [exec] at e
    | succ f =>
      simp only [Stmt.block, exec, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact hs
  | cons t more => exact Runs.seq hs hr

/-- An empty block runs to the same state. -/
theorem Runs.block_nil (m : Module) (w : World) (sp : Nat) (env : Env) (mem : Memory) :
    Runs m w sp env mem (.block []) env mem := Runs.skip m w sp env mem

/-- A call computes some result and memory with some fuel. -/
def Calls (m : Module) (w : World) (f : String) (sp : Nat) (args : List UInt64) (mem : Memory) (r : UInt64)
    (mem' : Memory) : Prop :=
  ∃ fuel, callSpec m w fuel f sp args mem = some (r, mem')

/-- A call runs to the variables with the result, and the memory the call leaves. -/
theorem Runs.call {m : Module} {w : World} {sp : Nat} {env : Env} {mem mem' : Memory} {f : String}
    {args : List Expr} {dst : Nat} {values : List UInt64} {r : UInt64} (hv : args.mapM (eval w env mem) = some values)
    (hc : Calls m w f sp values mem r mem') : Runs m w sp env mem (.call f args dst) (assign env dst r) mem' := by
  obtain ⟨fuel, h⟩ := hc
  -- A function call's meaning grows with fuel; a routine outside the language needs none.
  refine ⟨fuel + 1, ?_⟩
  rw [exec_call]; simp [hv, h, bind, Option.bind, pure]

/-- A function's body running from its arguments, then its result, is a call to it. -/
theorem Calls.fn {m : Module} {w : World} {f : String} {sp : Nat} {args : List UInt64} {mem mem' : Memory}
    {fn : Fn} {env' : Env} {r : UInt64} (hf : m.fns.lookup f = some fn) (room : w.stackLo + 8 + 8 * fn.frame ≤ sp)
    (count : args.length = fn.params)
    (hb : Runs m w (sp - 8 - 8 * fn.frame) (entryEnv args) mem fn.body env' mem')
    (hr : eval w env' mem' fn.result = some r) : Calls m w f sp args mem r mem' := by
  obtain ⟨fuel, e⟩ := hb
  exact ⟨fuel, by simp [callSpec, hf, room, count, e, hr, bind, Option.bind, pure]⟩

/-- A routine outside the language, given by its meaning, is a call to it. -/
theorem Calls.ext {m : Module} {w : World} {f : String} {sp : Nat} {args : List UInt64} {mem mem' : Memory}
    {e : Extern} {r : UInt64} (hf : m.fns.lookup f = none) (he : m.ext.lookup f = some e) (room : w.stackLo + 8 ≤ sp)
    (run : e.run w sp args mem = some (r, mem')) : Calls m w f sp args mem r mem' :=
  ⟨0, by simp [callSpec, hf, he, room, run]⟩

end EthLib.Consensus.Ssz.Native.Ir
