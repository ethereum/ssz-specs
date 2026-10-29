import SszNative.Proofs.Ir.Wp

/-!
What a run that happened tells about itself.

A run has one meaning: two amounts of fuel that both give one give the same.
A call to a function of the module, whose callees are all functions of the module, keeps its meaning with more stack.
So a call that happened returns what any proof of that call, from any stack pointer, says it returns.

A statement meets a condition after every run of it when each step does.
Unlike reaching a condition, this asks nothing of fuel or of the stack: a run that has no meaning is no run.
-/

namespace Ssz.Native.Ir

open Ssz.Native.Asm

/-! One meaning. -/

/-- Two amounts of fuel giving a statement a meaning give it the same one. -/
theorem exec_unique (m : Module) (w : World) {f₁ f₂ sp : Nat} {env : Env} {mem : Memory} {s : Stmt}
    {r₁ r₂ : Env × Memory} (h₁ : exec m w f₁ sp env mem s = some r₁) (h₂ : exec m w f₂ sp env mem s = some r₂) :
    r₁ = r₂ := by
  have a := exec_le m w h₁ (Nat.le_max_left f₁ f₂)
  have b := exec_le m w h₂ (Nat.le_max_right f₁ f₂)
  rw [a] at b
  exact Option.some.inj b

/-- A meaning of a call at some fuel holds at any larger fuel. -/
theorem callSpec_le (m : Module) (w : World) {fuel fuel' : Nat} {f : String} {sp : Nat} {args : List UInt64}
    {mem : Memory} {r : UInt64 × Memory} (h : callSpec m w fuel f sp args mem = some r) (le : fuel ≤ fuel') :
    callSpec m w fuel' f sp args mem = some r := by
  unfold callSpec at h ⊢
  split at h
  · split at h
    · simp only [bind, Option.bind] at h ⊢
      split at h
      · simp at h
      · rename_i heq
        rw [exec_le m w heq le]
        rw [if_pos (by assumption)]
        exact h
    · simp at h
  · exact h

/-- A call that happened twice, from the same stack pointer, returned the same both times. -/
theorem Calls.unique {m : Module} {w : World} {f : String} {sp : Nat} {args : List UInt64} {mem mem₁ mem₂ : Memory}
    {r₁ r₂ : UInt64} (h₁ : Calls m w f sp args mem r₁ mem₁) (h₂ : Calls m w f sp args mem r₂ mem₂) :
    r₁ = r₂ ∧ mem₁ = mem₂ := by
  obtain ⟨f₁, e₁⟩ := h₁
  obtain ⟨f₂, e₂⟩ := h₂
  have a := callSpec_le m w e₁ (Nat.le_max_left f₁ f₂)
  have b := callSpec_le m w e₂ (Nat.le_max_right f₁ f₂)
  rw [a] at b
  have := Option.some.inj b
  simp only [Prod.mk.injEq] at this
  exact this

/-! More stack. -/

/-- The names a statement calls. -/
def Stmt.callees : Stmt → List String
  | .seq a b => a.callees ++ b.callees
  | .ite _ t e => t.callees ++ e.callees
  | .loop _ body => body.callees
  | .call f _ _ => [f]
  | _ => []

/-- Names that are all functions of the module, each calling only names among them. -/
def Closed (m : Module) (names : List String) : Prop :=
  ∀ f ∈ names, ∃ fn, m.fns.lookup f = some fn ∧ ∀ g ∈ fn.body.callees, g ∈ names

/-- A statement calling only closed names keeps its meaning with a higher stack pointer. -/
theorem exec_sp_mono (m : Module) (w : World) (names : List String) (closed : Closed m names) :
    ∀ (fuel sp sp' : Nat) (env : Env) (mem : Memory) (s : Stmt) (r : Env × Memory),
      (∀ g ∈ s.callees, g ∈ names) → sp ≤ sp' → exec m w fuel sp env mem s = some r →
        exec m w fuel sp' env mem s = some r := by
  intro fuel
  induction fuel with
  | zero => intro sp sp' env mem s r _ _ h; simp [exec] at h
  | succ n ih =>
    intro sp sp' env mem s r calls le h
    cases s with
    | skip => simpa [exec] using h
    | set x e => simpa [exec] using h
    | store wd a v => simpa [exec] using h
    | seq a b =>
      simp only [Stmt.callees, List.mem_append] at calls
      rw [exec] at h ⊢; simp only [bind, Option.bind] at h ⊢
      cases ha : exec m w n sp env mem a with
      | none => simp [ha] at h
      | some p =>
        simp only [ha] at h
        rw [ih _ _ _ _ _ _ (fun g hg => calls g (Or.inl hg)) le ha]
        exact ih _ _ _ _ _ _ (fun g hg => calls g (Or.inr hg)) le h
    | ite c t e =>
      simp only [Stmt.callees, List.mem_append] at calls
      rw [exec] at h ⊢; simp only [bind, Option.bind] at h ⊢
      cases hc : eval w env mem c with
      | none => simp [hc] at h
      | some v =>
        simp only [hc] at h ⊢
        by_cases hv : (v != 0) = true
        · simp only [hv, if_true] at h ⊢; exact ih _ _ _ _ _ _ (fun g hg => calls g (Or.inl hg)) le h
        · simp only [hv, Bool.false_eq_true, if_false] at h ⊢
          exact ih _ _ _ _ _ _ (fun g hg => calls g (Or.inr hg)) le h
    | loop c body =>
      rw [exec] at h ⊢; simp only [bind, Option.bind] at h ⊢
      cases hc : eval w env mem c with
      | none => simp [hc] at h
      | some v =>
        simp only [hc] at h ⊢
        by_cases hz : (v == 0) = true
        · simp only [hz, if_true] at h ⊢; exact h
        · simp only [hz, Bool.false_eq_true, if_false] at h ⊢
          cases hb : exec m w n sp env mem body with
          | none => simp [hb] at h
          | some p =>
            simp only [hb] at h
            have inner : ∀ g ∈ body.callees, g ∈ names := fun g hg => calls g (by simpa [Stmt.callees] using hg)
            rw [ih _ _ _ _ _ _ inner le hb]
            exact ih _ _ _ _ _ _ calls le h
    | call f args dst =>
      simp only [Stmt.callees, List.mem_singleton, forall_eq] at calls
      obtain ⟨fn, hf, inner⟩ := closed f calls
      rw [exec] at h ⊢; simp only [bind, Option.bind] at h ⊢
      cases hv : args.mapM (eval w env mem) with
      | none => simp [hv] at h
      | some values =>
        simp only [hv, hf] at h ⊢
        by_cases room : (decide (w.stackLo + 8 + 8 * fn.frame ≤ sp) && values.length == fn.params) = true
        · simp only [room, if_true] at h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at room
          rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by omega, room.2⟩)]
          cases hb : exec m w n (sp - 8 - 8 * fn.frame) (entryEnv values) mem fn.body with
          | none => simp [hb] at h
          | some p =>
            simp only [hb] at h
            rw [ih (sp - 8 - 8 * fn.frame) (sp' - 8 - 8 * fn.frame) _ _ _ _ inner (by omega) hb]
            exact h
        · simp only [room, Bool.false_eq_true, if_false] at h; simp at h

/-- A call to a closed name keeps its meaning with a higher stack pointer. -/
theorem Calls.sp_mono {m : Module} {w : World} {names : List String} (closed : Closed m names) {f : String}
    (hf : f ∈ names) {sp sp' : Nat} (le : sp ≤ sp') {args : List UInt64} {mem mem' : Memory} {r : UInt64}
    (h : Calls m w f sp args mem r mem') : Calls m w f sp' args mem r mem' := by
  obtain ⟨fuel, e⟩ := h
  obtain ⟨fn, look, inner⟩ := closed f hf
  refine ⟨fuel, ?_⟩
  simp only [callSpec, look] at e ⊢
  by_cases room : (decide (w.stackLo + 8 + 8 * fn.frame ≤ sp) && args.length == fn.params) = true
  · simp only [room, if_true] at e
    simp only [Bool.and_eq_true, decide_eq_true_eq] at room
    rw [if_pos (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by omega, room.2⟩)]
    simp only [bind, Option.bind] at e ⊢
    cases hb : exec m w fuel (sp - 8 - 8 * fn.frame) (entryEnv args) mem fn.body with
    | none => simp [hb] at e
    | some p =>
      simp only [hb] at e
      rw [exec_sp_mono m w names closed _ _ (sp' - 8 - 8 * fn.frame) _ _ _ _ inner (by omega) hb]
      exact e
  · simp only [room, Bool.false_eq_true, if_false] at e; simp at e

/-- A call to a closed name that happened returns what any other run of it, from any stack pointer, returns. -/
theorem Calls.agree {m : Module} {w : World} {names : List String} (closed : Closed m names) {f : String}
    (hf : f ∈ names) {sp sp' : Nat} {args : List UInt64} {mem mem₁ mem₂ : Memory} {r₁ r₂ : UInt64}
    (h₁ : Calls m w f sp args mem r₁ mem₁) (h₂ : Calls m w f sp' args mem r₂ mem₂) : r₁ = r₂ ∧ mem₁ = mem₂ :=
  Calls.unique (Calls.sp_mono closed hf (Nat.le_max_left sp sp') h₁)
    (Calls.sp_mono closed hf (Nat.le_max_right sp sp') h₂)

/-! Memory left alone. -/

/-- Whether a statement writes memory itself. -/
def Stmt.stores : Stmt → Bool
  | .store _ _ _ => true
  | .seq a b => a.stores || b.stores
  | .ite _ t e => t.stores || e.stores
  | .loop _ body => body.stores
  | _ => false

/-- Closed names whose functions never write memory themselves. -/
def Keeps (m : Module) (names : List String) : Prop :=
  ∀ f ∈ names, ∃ fn, m.fns.lookup f = some fn ∧ fn.body.stores = false ∧ ∀ g ∈ fn.body.callees, g ∈ names

/-- Names whose functions keep memory are closed. -/
theorem Keeps.closed {m : Module} {names : List String} (h : Keeps m names) : Closed m names := fun f hf =>
  (h f hf).elim fun fn ⟨look, _, calls⟩ => ⟨fn, look, calls⟩

/-- A statement that writes nothing and calls only names that keep memory leaves memory as it was. -/
theorem exec_keeps (m : Module) (w : World) (names : List String) (keeps : Keeps m names) :
    ∀ (fuel sp : Nat) (env : Env) (mem : Memory) (s : Stmt) (r : Env × Memory),
      s.stores = false → (∀ g ∈ s.callees, g ∈ names) → exec m w fuel sp env mem s = some r → r.2 = mem := by
  intro fuel
  induction fuel with
  | zero => intro sp env mem s r _ _ h; simp [exec] at h
  | succ n ih =>
    intro sp env mem s r ps calls h
    cases s with
    | skip => simp [exec] at h; rw [← h]
    | set x e =>
      simp only [exec] at h
      cases hv : eval w env mem e with
      | none => simp [hv] at h
      | some v => simp only [hv, Option.map_some, Option.some.injEq] at h; rw [← h]
    | store wd a v => simp [Stmt.stores] at ps
    | seq a b =>
      simp only [Stmt.stores, Bool.or_eq_false_iff] at ps
      simp only [Stmt.callees, List.mem_append] at calls
      rw [exec] at h; simp only [bind, Option.bind] at h
      cases ha : exec m w n sp env mem a with
      | none => simp [ha] at h
      | some p =>
        simp only [ha] at h
        rw [ih _ _ _ _ _ ps.2 (fun g hg => calls g (Or.inr hg)) h]
        exact ih _ _ _ _ _ ps.1 (fun g hg => calls g (Or.inl hg)) ha
    | ite c t e =>
      simp only [Stmt.stores, Bool.or_eq_false_iff] at ps
      simp only [Stmt.callees, List.mem_append] at calls
      rw [exec] at h; simp only [bind, Option.bind] at h
      cases hc : eval w env mem c with
      | none => simp [hc] at h
      | some v =>
        simp only [hc] at h
        by_cases hv : (v != 0) = true
        · simp only [hv, if_true] at h; exact ih _ _ _ _ _ ps.1 (fun g hg => calls g (Or.inl hg)) h
        · simp only [hv, Bool.false_eq_true, if_false] at h
          exact ih _ _ _ _ _ ps.2 (fun g hg => calls g (Or.inr hg)) h
    | loop c body =>
      have pb : body.stores = false := by simpa [Stmt.stores] using ps
      have cb : ∀ g ∈ body.callees, g ∈ names := fun g hg => calls g (by simpa [Stmt.callees] using hg)
      rw [exec] at h; simp only [bind, Option.bind] at h
      cases hc : eval w env mem c with
      | none => simp [hc] at h
      | some v =>
        simp only [hc] at h
        by_cases hz : (v == 0) = true
        · simp only [hz, if_true, pure, Option.some.injEq] at h; rw [← h]
        · simp only [hz, Bool.false_eq_true, if_false] at h
          cases hb : exec m w n sp env mem body with
          | none => simp [hb] at h
          | some p =>
            simp only [hb] at h
            rw [ih _ _ _ _ _ ps calls h]
            exact ih _ _ _ _ _ pb cb hb
    | call f args dst =>
      simp only [Stmt.callees, List.mem_singleton, forall_eq] at calls
      obtain ⟨fn, hf, fpure, inner⟩ := keeps f calls
      rw [exec] at h; simp only [bind, Option.bind] at h
      cases hv : args.mapM (eval w env mem) with
      | none => simp [hv] at h
      | some values =>
        simp only [hv, hf] at h
        by_cases room : (decide (w.stackLo + 8 + 8 * fn.frame ≤ sp) && values.length == fn.params) = true
        · simp only [room, if_true] at h
          cases hb : exec m w n (sp - 8 - 8 * fn.frame) (entryEnv values) mem fn.body with
          | none => simp [hb] at h
          | some p =>
            simp only [hb] at h
            cases hr : eval w p.1 p.2 fn.result with
            | none => simp [hr] at h
            | some x =>
              simp only [hr, pure, Option.some.injEq] at h
              rw [← h]
              exact ih _ _ _ _ p fpure inner hb
        · simp only [room, Bool.false_eq_true, if_false] at h; simp at h

/-- A call to a name that keeps memory leaves memory as it was. -/
theorem Calls.keeps {m : Module} {w : World} {names : List String} (keeps : Keeps m names) {f : String}
    (hf : f ∈ names) {sp : Nat} {args : List UInt64} {mem mem' : Memory} {r : UInt64}
    (h : Calls m w f sp args mem r mem') : mem' = mem := by
  obtain ⟨fuel, e⟩ := h
  obtain ⟨fn, look, fpure, inner⟩ := keeps f hf
  simp only [callSpec, look] at e
  split at e
  · simp only [bind, Option.bind] at e
    cases hb : exec m w fuel (sp - 8 - 8 * fn.frame) (entryEnv args) mem fn.body with
    | none => simp [hb] at e
    | some p =>
      simp only [hb] at e
      cases hr : eval w p.1 p.2 fn.result with
      | none => simp [hr] at e
      | some x =>
        simp only [hr, pure, Option.some.injEq, Prod.mk.injEq] at e
        rw [← e.2]
        exact exec_keeps m w names keeps _ _ _ _ _ _ fpure inner hb
  · simp at e

/-! Conditions every run meets. -/

/-- Every run of a statement from variables and memory ends where a condition holds. -/
def Pc (m : Module) (w : World) (sp : Nat) (s : Stmt) (env : Env) (mem : Memory) (Q : Env → Memory → Prop) : Prop :=
  ∀ env' mem', Runs m w sp env mem s env' mem' → Q env' mem'

namespace Pc

variable {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {Q : Env → Memory → Prop}

open Ssz.Native.Ir.Stmt

/-- A run is a run that reaches its own end. -/
theorem wp_of_runs {s : Stmt} {env' : Env} {mem' : Memory} (h : Runs m w sp env mem s env' mem') :
    Wp m w sp s env mem (fun e k => e = env' ∧ k = mem') :=
  ⟨env', mem', h, rfl, rfl⟩

/-- Every run of two statements meets what every run of the second does from where the first ends. -/
theorem seq {a b : Stmt} (h : Pc m w sp a env mem (fun e k => Pc m w sp b e k Q)) : Pc m w sp (.seq a b) env mem Q := by
  intro e' m' r
  obtain ⟨e₂, m₂, ra, e₃, m₃, rb, rfl, rfl⟩ := (wp_seq a b env mem _).mp (wp_of_runs r)
  exact h e₂ m₂ ra e₃ m₃ rb

/-- An empty block ends where it starts. -/
theorem done (h : Q env mem) : Pc m w sp (.block []) env mem Q := by
  intro e' m' r
  obtain ⟨rfl, rfl⟩ := (wp_skip env mem _).mp (wp_of_runs r)
  exact h

/-- The head statement of a block, then the rest. -/
theorem cons {s : Stmt} {rest : List Stmt} (h : Pc m w sp s env mem (fun e k => Pc m w sp (.block rest) e k Q)) :
    Pc m w sp (.block (s :: rest)) env mem Q := by
  cases rest with
  | nil => exact fun e' m' r => h e' m' r e' m' (Runs.block_nil m w sp e' m')
  | cons t more => exact seq h

/-- Two lists of statements one after the other. -/
theorem append {a b : List Stmt}
    (h : Pc m w sp (.block a) env mem (fun e k => Pc m w sp (.block b) e k Q)) :
    Pc m w sp (.block (a ++ b)) env mem Q := by
  intro e' m' r
  obtain ⟨e₂, m₂, ra, e₃, m₃, rb, rfl, rfl⟩ := (Wp.block_append a b env mem).mp (wp_of_runs r)
  exact h e₂ m₂ ra e₃ m₃ rb

/-- An assignment, whatever value its expression has. -/
theorem set {x : Var} {e : Expr} {rest : List Stmt}
    (h : ∀ v, eval w env mem e = some v → Pc m w sp (.block rest) (assign env x.idx v) mem Q) :
    Pc m w sp (.block ((x ::= e) :: rest)) env mem Q := by
  refine cons fun e' m' r => ?_
  obtain ⟨v, hv, rfl, rfl⟩ := (wp_set x.idx e env mem _).mp (wp_of_runs r)
  exact h v hv

/-- An assignment of a known value. -/
theorem set_of {x : Var} {e : Expr} {rest : List Stmt} {v : UInt64} (hv : eval w env mem e = some v)
    (h : Pc m w sp (.block rest) (assign env x.idx v) mem Q) : Pc m w sp (.block ((x ::= e) :: rest)) env mem Q :=
  set fun v' hv' => by rw [hv] at hv'; cases hv'; exact h

/-- A branch, whatever value its condition has. -/
theorem ite {c : Expr} {t e : Stmt}
    (h : ∀ v, eval w env mem c = some v → (v ≠ 0 → Pc m w sp t env mem Q) ∧ (v = 0 → Pc m w sp e env mem Q)) :
    Pc m w sp (.ite c t e) env mem Q := by
  intro e' m' r
  obtain ⟨v, hv, k⟩ := (wp_ite c t e env mem _).mp (wp_of_runs r)
  by_cases z : v = 0
  · simp only [z, ne_eq, not_true_eq_false, if_false] at k
    obtain ⟨_, _, rr, rfl, rfl⟩ := k
    exact (h v hv).2 z _ _ rr
  · simp only [ne_eq, z, not_false_eq_true, if_true] at k
    obtain ⟨_, _, rr, rfl, rfl⟩ := k
    exact (h v hv).1 z _ _ rr

/-- Two blocks run one after the other as their joined block. -/
theorem runs_append {a b : List Stmt} {e₁ e₂ e₃ : Env} {m₁ m₂ m₃ : Memory} (ra : Runs m w sp e₁ m₁ (.block a) e₂ m₂)
    (rb : Runs m w sp e₂ m₂ (.block b) e₃ m₃) : Runs m w sp e₁ m₁ (.block (a ++ b)) e₃ m₃ := by
  obtain ⟨_, _, r, rfl, rfl⟩ := (Wp.block_append (Q := fun e k => e = e₃ ∧ k = m₃) a b e₁ m₁).mpr
    ⟨e₂, m₂, ra, e₃, m₃, rb, rfl, rfl⟩
  exact r

/-- A two-way branch at the head of a block, whatever value its condition has. -/
theorem ifElse {c : Expr} {yes no rest : List Stmt}
    (h : ∀ v, eval w env mem c = some v →
      (v ≠ 0 → Pc m w sp (.block (yes ++ rest)) env mem Q) ∧ (v = 0 → Pc m w sp (.block (no ++ rest)) env mem Q)) :
    Pc m w sp (.block (Stmt.ifElse c yes no :: rest)) env mem Q := by
  refine cons (ite fun v hv => ⟨fun nz => ?_, fun z => ?_⟩)
  · exact fun e' m' r e'' m'' r' => (h v hv).1 nz _ _ (runs_append r r')
  · exact fun e' m' r e'' m'' r' => (h v hv).2 z _ _ (runs_append r r')

/-- A guarded block at the head of a block, whatever value its condition has. -/
theorem when {c : Expr} {yes rest : List Stmt}
    (h : ∀ v, eval w env mem c = some v →
      (v ≠ 0 → Pc m w sp (.block (yes ++ rest)) env mem Q) ∧ (v = 0 → Pc m w sp (.block rest) env mem Q)) :
    Pc m w sp (.block (Stmt.when c yes :: rest)) env mem Q := by
  refine cons (ite fun v hv => ⟨fun nz => ?_, fun z => ?_⟩)
  · exact fun e' m' r e'' m'' r' => (h v hv).1 nz _ _ (runs_append r r')
  · intro e' m' r
    obtain ⟨rfl, rfl⟩ := (wp_skip env mem _).mp (wp_of_runs r)
    exact (h v hv).2 z

/-- A two-way branch whose condition holds. -/
theorem ifElse_t {c : Expr} {yes no rest : List Stmt} {v : UInt64} (hv : eval w env mem c = some v) (nz : v ≠ 0)
    (h : Pc m w sp (.block (yes ++ rest)) env mem Q) : Pc m w sp (.block (Stmt.ifElse c yes no :: rest)) env mem Q :=
  ifElse fun v' hv' => by rw [hv] at hv'; cases hv'; exact ⟨fun _ => h, fun z => absurd z nz⟩

/-- A two-way branch whose condition fails. -/
theorem ifElse_f {c : Expr} {yes no rest : List Stmt} (hv : eval w env mem c = some 0)
    (h : Pc m w sp (.block (no ++ rest)) env mem Q) : Pc m w sp (.block (Stmt.ifElse c yes no :: rest)) env mem Q :=
  ifElse fun v' hv' => by rw [hv] at hv'; cases hv'; exact ⟨fun nz => absurd rfl nz, fun _ => h⟩

/-- A guarded block whose condition holds. -/
theorem when_t {c : Expr} {yes rest : List Stmt} {v : UInt64} (hv : eval w env mem c = some v) (nz : v ≠ 0)
    (h : Pc m w sp (.block (yes ++ rest)) env mem Q) : Pc m w sp (.block (Stmt.when c yes :: rest)) env mem Q :=
  when fun v' hv' => by rw [hv] at hv'; cases hv'; exact ⟨fun _ => h, fun z => absurd z nz⟩

/-- A guarded block whose condition fails. -/
theorem when_f {c : Expr} {yes rest : List Stmt} (hv : eval w env mem c = some 0)
    (h : Pc m w sp (.block rest) env mem Q) : Pc m w sp (.block (Stmt.when c yes :: rest)) env mem Q :=
  when fun v' hv' => by rw [hv] at hv'; cases hv'; exact ⟨fun nz => absurd rfl nz, fun _ => h⟩

/-- A call at the head of a block, whatever it returns. -/
theorem call {x : Var} {f : String} {args : List Expr} {rest : List Stmt}
    (h : ∀ values r mem', args.mapM (eval w env mem) = some values → Calls m w f sp values mem r mem' →
      Pc m w sp (.block rest) (assign env x.idx r) mem' Q) :
    Pc m w sp (.block (callInto x f args :: rest)) env mem Q := by
  refine cons fun e' m' r => ?_
  obtain ⟨values, res, mem', hv, hc, rfl, rfl⟩ := (wp_call f args x.idx env mem _).mp (wp_of_runs r)
  exact h values res mem' hv hc

/-- A call with known arguments at the head of a block, whatever it returns. -/
theorem call_of {x : Var} {f : String} {args : List Expr} {rest : List Stmt} {values : List UInt64}
    (hv : args.mapM (eval w env mem) = some values)
    (h : ∀ r mem', Calls m w f sp values mem r mem' → Pc m w sp (.block rest) (assign env x.idx r) mem' Q) :
    Pc m w sp (.block (callInto x f args :: rest)) env mem Q :=
  call fun values' r mem' hv' hc => by rw [hv] at hv'; cases hv'; exact h r mem' hc

/-- A loop ends where an invariant every pass keeps holds and its condition is zero. -/
theorem loop_inv {c : Expr} {body : Stmt} (inv : Env → Memory → Prop) (start : inv env mem)
    (pass : ∀ e m' v, inv e m' → eval w e m' c = some v → v ≠ 0 → Pc m w sp body e m' inv)
    (exit : ∀ e m', inv e m' → eval w e m' c = some 0 → Q e m') : Pc m w sp (.loop c body) env mem Q := by
  rintro e' m' ⟨fuel, h⟩
  induction fuel generalizing env mem with
  | zero => simp [exec] at h
  | succ n ih =>
    rw [exec] at h; simp only [bind, Option.bind] at h
    cases hc : eval w env mem c with
    | none => simp [hc] at h
    | some v =>
      simp only [hc] at h
      by_cases hz : (v == 0) = true
      · simp only [hz, if_true, pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have : v = 0 := by simpa using hz
        subst this
        exact exit _ _ start hc
      · simp only [hz, Bool.false_eq_true, if_false] at h
        cases hb : exec m w n sp env mem body with
        | none => simp [hb] at h
        | some p =>
          simp only [hb] at h
          have nz : v ≠ 0 := by simpa using hz
          exact ih (pass env mem v start hc nz p.1 p.2 ⟨n, hb⟩) h

/-- A loop at the head of a block, with an invariant every pass keeps. -/
theorem loop {c : Expr} {body rest : List Stmt} (inv : Env → Memory → Prop) (start : inv env mem)
    (pass : ∀ e m' v, inv e m' → eval w e m' c = some v → v ≠ 0 → Pc m w sp (.block body) e m' inv)
    (exit : ∀ e m', inv e m' → eval w e m' c = some 0 → Pc m w sp (.block rest) e m' Q) :
    Pc m w sp (.block (while_ c body :: rest)) env mem Q :=
  cons (loop_inv inv start pass exit)

/-- The head statement of a block, through a condition every run of it meets. -/
theorem cut {s : Stmt} {rest : List Stmt} (P : Env → Memory → Prop) (h : Pc m w sp s env mem P)
    (k : ∀ e k', P e k' → Pc m w sp (.block rest) e k' Q) : Pc m w sp (.block (s :: rest)) env mem Q :=
  cons fun e k' r => k e k' (h e k' r)

/-- A statement standing alone is a block of one. -/
theorem single {s : Stmt} (h : Pc m w sp (.block [s]) env mem Q) : Pc m w sp s env mem Q := h

/-- Weakening what every run meets. -/
theorem mono {s : Stmt} {Q' : Env → Memory → Prop} (h : Pc m w sp s env mem Q) (imp : ∀ e k, Q e k → Q' e k) :
    Pc m w sp s env mem Q' := fun e k r => imp e k (h e k r)

end Pc

/-- What every run of a function's body meets, the call's result included, holds of every call to it. -/
theorem Calls.of_pc {m : Module} {w : World} {f : String} {sp : Nat} {args : List UInt64} {mem mem' : Memory}
    {fn : Fn} {r : UInt64} {P : UInt64 → Memory → Prop} (k : Nat) (hf : m.fns.lookup f = some fn)
    (frame : fn.frame = k)
    (h : Pc m w (sp - 8 - 8 * k) fn.body (entryEnv args) mem
      (fun env' mem'' => ∀ r, eval w env' mem'' fn.result = some r → P r mem''))
    (call : Calls m w f sp args mem r mem') : P r mem' := by
  obtain ⟨fuel, e⟩ := call
  simp only [callSpec, hf] at e
  split at e
  · simp only [bind, Option.bind] at e
    cases hb : exec m w fuel (sp - 8 - 8 * fn.frame) (entryEnv args) mem fn.body with
    | none => simp [hb] at e
    | some p =>
      simp only [hb] at e
      cases hr : eval w p.1 p.2 fn.result with
      | none => simp [hr] at e
      | some v =>
        simp only [hr, pure, Option.some.injEq, Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        subst frame
        exact h p.1 p.2 ⟨fuel, hb⟩ v hr
  · simp at e

end Ssz.Native.Ir
