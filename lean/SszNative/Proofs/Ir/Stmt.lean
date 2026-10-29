import SszNative.Proofs.Ir.Expr
import SszNative.Proofs.Ir.Call

/-!
The code of every statement computes its meaning.

Loops and calls are proved by induction on the fuel their meaning takes.
-/

namespace EthLib.Consensus.Ssz.Native.Ir

open EthLib.Consensus.Ssz.Native.Asm

/-- What a statement's code guarantees, for a meaning of the statement with some fuel. -/
def StmtOk (m : Module) (c : Site) (fuel : Nat) (stmt : Stmt) : Prop :=
  ∀ (pc : Nat) (pre post : List Instr) (env : Env) (ir : Memory) (s : State) (env' : Env) (ir' : Memory),
    (c.image.code c.routine).toList = pre ++ compileStmt c.vars pc stmt ++ post → pre.length = pc → s.pc = pc →
    c.Holds env ir s → c.vars + stmt.temps ≤ c.frame →
    exec m c.w fuel c.base env ir stmt = some (env', ir') →
    ∃ s', Reaches c.image c.routine s s' ∧ s'.pc = pc + (compileStmt c.vars pc stmt).length ∧
      c.Holds env' ir' s' ∧ ∀ a, c.base + 8 * c.frame ≤ a → a < c.w.stackHi → s'.mem a = s.mem a

/-- Doing nothing compiles to no code. -/
theorem skip_ok (m : Module) (c : Site) (fuel : Nat) : StmtOk m c fuel .skip := by
  intro pc pre post env ir s env' ir' layout hpre hpc holds room ex
  cases fuel with
  | zero => simp [exec] at ex
  | succ n =>
    simp only [exec, Option.some.injEq, Prod.mk.injEq] at ex
    obtain ⟨rfl, rfl⟩ := ex
    exact ⟨s, Reaches.refl _ _ _, by simp [compileStmt, hpc], holds, fun _ _ _ => rfl⟩

/-- An assignment is its expression, then one store to the variable's slot. -/
theorem set_ok (m : Module) (c : Site) (fits : c.Fits) (fuel : Nat) (x : Nat) (e : Expr) (hx : x < c.vars)
    (he : e.varsBelow c.vars) : StmtOk m c fuel (.set x e) := by
  intro pc pre post env ir s env' ir' layout hpre hpc holds room ex
  cases fuel with
  | zero => simp [exec] at ex
  | succ n =>
    simp only [exec] at ex
    cases ev : eval c.w env ir e with
    | none => simp [ev] at ex
    | some v =>
      simp only [ev, Option.map_some, Option.some.injEq, Prod.mk.injEq] at ex
      obtain ⟨rfl, rfl⟩ := ex
      have lay1 : (c.image.code c.routine).toList = pre ++ compileExpr c.vars pc e 0 ++
          ([.store .b8 (slot x) .rax] ++ post) := by simpa [compileStmt] using layout
      obtain ⟨s1, r1, p1, rax1, h1, m1⟩ := expr_ok c fits e he 0 pc pre _ env ir s v lay1 hpre hpc holds
        (by simpa [Stmt.temps] using room) ev
      have lay2 : (c.image.code c.routine).toList = (pre ++ compileExpr c.vars pc e 0) ++ [.store .b8 (slot x) .rax] ++
          post := by simpa using lay1
      have r2 := Reaches.one c.image c.routine _ _ _ lay2 (by simp [Instr.straight]) s1 (by simp [p1, hpre])
        h1.running
      refine ⟨_, r1.trans r2, by simp [compileStmt, hpre]; omega, ?_, fun a lo hi => ?_⟩
      · have := h1.setVar fits x hx v
        refine this.congr (by simp [exec1]) ?_ (by simp [exec1]) (by simp [exec1])
        simp [exec1, slot_addr c fits s1 h1.rsp, rax1, Width.bytes]
      · simp only [exec1, slot_addr c fits s1 h1.rsp, store, Width.bytes]
        have := fits.vars
        rw [ite_eq_right (by omega), m1 a (Or.inr lo)]

/-- Two statements compile to their codes one after the other. -/
theorem seq_ok (m : Module) (c : Site) (fuel : Nat) (a b : Stmt) (iha : StmtOk m c fuel a) (ihb : StmtOk m c fuel b) :
    StmtOk m c (fuel + 1) (.seq a b) := by
  intro pc pre post env ir s env' ir' layout hpre hpc holds room ex
  rw [exec] at ex
  simp only [bind, Option.bind] at ex
  cases ea : exec m c.w fuel c.base env ir a with
  | none => simp [ea] at ex
  | some p =>
    obtain ⟨env1, ir1⟩ := p
    simp only [ea] at ex
    let ca := compileStmt c.vars pc a
    obtain ⟨s1, r1, p1, h1, m1⟩ := iha pc pre (compileStmt c.vars (pc + ca.length) b ++ post) env ir s env1 ir1
      (by simpa [compileStmt] using layout) hpre hpc holds (by simp [Stmt.temps] at room; omega) ea
    obtain ⟨s2, r2, p2, h2, m2⟩ := ihb (pc + ca.length) (pre ++ ca) post env1 ir1 s1 env' ir'
      (by simpa [compileStmt, ca] using layout) (by simp [hpre, ca]) p1 h1 (by simp [Stmt.temps] at room; omega) ex
    exact ⟨s2, r1.trans r2, by simp [p2, compileStmt, ca]; omega, h2, fun a lo hi => by rw [m2 a lo hi, m1 a lo hi]⟩

/-- A branch on a clear zero flag goes on, and on a set one goes to its target. -/
theorem Reaches.jz (image : Image) (r : Nat) (s : State) (t : Nat) (fetch : (image.code r)[s.pc]? = some (.jz t))
    (running : s.status = .running) : Reaches image r s { s with pc := if s.zf then t else s.pc + 1 } := by
  refine ⟨1, ?_⟩
  simp only [Image.run, image_step_plain image r s _ fetch (by simp) (by simp)]
  simp [step, running, fetch]

/-- An unconditional branch goes to its target. -/
theorem Reaches.jmp (image : Image) (r : Nat) (s : State) (t : Nat) (fetch : (image.code r)[s.pc]? = some (.jmp t))
    (running : s.status = .running) : Reaches image r s { s with pc := t } := by
  refine ⟨1, ?_⟩
  simp only [Image.run, image_step_plain image r s _ fetch (by simp) (by simp)]
  simp [step, running, fetch]

/-- A condition evaluated and tested: the zero flag says whether it is zero, and nothing else changes. -/
theorem test_ok (c : Site) (fits : c.Fits) (cond : Expr) (hc : cond.varsBelow c.vars) (pc : Nat)
    (pre rest : List Instr) (env : Env) (ir : Memory) (s : State) (v : UInt64)
    (layout : (c.image.code c.routine).toList = pre ++ compileExpr c.vars pc cond 0 ++ [.test .rax] ++ rest)
    (hpre : pre.length = pc) (hpc : s.pc = pc) (holds : c.Holds env ir s) (room : c.vars + cond.temps ≤ c.frame)
    (ev : eval c.w env ir cond = some v) :
    ∃ s', Reaches c.image c.routine s s' ∧ s'.pc = pc + (compileExpr c.vars pc cond 0).length + 1 ∧
      s'.zf = (v == 0) ∧ c.Holds env ir s' ∧ ∀ a, c.base + 8 * c.frame ≤ a → s'.mem a = s.mem a := by
  obtain ⟨s1, r1, p1, rax1, h1, m1⟩ := expr_ok c fits cond hc 0 pc pre ([.test .rax] ++ rest) env ir s v
    (by simpa using layout) hpre hpc holds (by omega) ev
  have r2 := Reaches.one c.image c.routine _ _ _ layout (by simp [Instr.straight]) s1 (by simp [p1, hpre])
    h1.running
  exact ⟨_, r1.trans r2, by simp [hpre], by simp [exec1, rax1], h1.congr (by simp [exec1]) (by simp [exec1])
    (by simp [exec1]) (by simp [exec1]), fun a ha => by simp [exec1, m1 a (Or.inr ha)]⟩

/-- A branch tests its condition, then runs one statement's code and skips the other's. -/
theorem ite_ok (m : Module) (c : Site) (fits : c.Fits) (fuel : Nat) (cond : Expr) (t e : Stmt)
    (hc : cond.varsBelow c.vars) (iht : StmtOk m c fuel t) (ihe : StmtOk m c fuel e) :
    StmtOk m c (fuel + 1) (.ite cond t e) := by
  intro pc pre post env ir s env' ir' layout hpre hpc holds room ex
  rw [exec] at ex
  simp only [bind, Option.bind] at ex
  cases ev : eval c.w env ir cond with
  | none => simp [ev] at ex
  | some v =>
  simp only [ev] at ex
  let cc := compileExpr c.vars pc cond 0
  let yes := compileStmt c.vars (pc + cc.length + 2) t
  let elsePc := pc + cc.length + 2 + yes.length + 1
  let no := compileStmt c.vars elsePc e
  have code : compileStmt c.vars pc (.ite cond t e) =
      cc ++ [.test .rax, .jz elsePc] ++ yes ++ [.jmp (elsePc + no.length)] ++ no := rfl
  simp only [Stmt.temps] at room
  -- The condition and its test.
  obtain ⟨s1, r1, p1, z1, h1, m1⟩ := test_ok c fits cond hc pc pre
    (.jz elsePc :: (yes ++ [.jmp (elsePc + no.length)] ++ no ++ post)) env ir s v
    (by rw [code] at layout; simpa using layout) hpre hpc holds (by omega) ev
  have lay2 : (c.image.code c.routine).toList = (pre ++ cc ++ [.test .rax]) ++ .jz elsePc ::
      (yes ++ [.jmp (elsePc + no.length)] ++ no ++ post) := by rw [code] at layout; simpa using layout
  have f2 := fetch_at c.image c.routine _ _ _ lay2
  have r2 := Reaches.jz c.image c.routine s1 elsePc (by rw [p1]; simpa [hpre, cc, Nat.add_assoc] using f2)
    h1.running
  by_cases zero : v = 0
  · -- The second branch.
    subst zero
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false] at ex
    have jump : (if s1.zf then elsePc else s1.pc + 1) = elsePc := by simp [z1]
    rw [jump] at r2
    obtain ⟨s3, r3, p3, h3, m3⟩ := ihe elsePc (pre ++ cc ++ [.test .rax, .jz elsePc] ++ yes ++
      [.jmp (elsePc + no.length)]) post env ir { s1 with pc := elsePc } env' ir'
      (by rw [code] at layout; simpa using layout)
      (by simp [hpre, elsePc, yes, cc]; omega) rfl (h1.congr rfl rfl rfl rfl) (by omega) ex
    refine ⟨s3, r1.trans (r2.trans r3), by rw [p3, code]; simp [elsePc, no, yes, cc]; omega, h3,
      fun a lo hi => by rw [m3 a lo hi]; exact m1 a lo⟩
  · -- The first branch, then over the second.
    have nz : (v != 0) = true := by simpa using zero
    simp only [nz, ite_true] at ex
    have next : (if s1.zf then elsePc else s1.pc + 1) = pc + cc.length + 2 := by
      simp [z1, zero, p1, cc] <;> omega
    rw [next] at r2
    obtain ⟨s3, r3, p3, h3, m3⟩ := iht (pc + cc.length + 2) (pre ++ cc ++ [.test .rax, .jz elsePc])
      ([.jmp (elsePc + no.length)] ++ no ++ post) env ir { s1 with pc := pc + cc.length + 2 } env' ir'
      (by rw [code] at layout; simpa using layout)
      (by simp [hpre, cc]; omega) rfl (h1.congr rfl rfl rfl rfl) (by omega) ex
    have lay4 : (c.image.code c.routine).toList = (pre ++ cc ++ [.test .rax, .jz elsePc] ++ yes) ++
        .jmp (elsePc + no.length) :: (no ++ post) := by rw [code] at layout; simpa using layout
    have f4 := fetch_at c.image c.routine _ _ _ lay4
    have at4 : s3.pc = (pre ++ cc ++ [Instr.test .rax, Instr.jz elsePc] ++ yes).length := by
      rw [p3]; simp [hpre, cc, yes]; omega
    have r4 := Reaches.jmp c.image c.routine s3 (elsePc + no.length) (by rw [at4]; exact f4) h3.running
    refine ⟨_, r1.trans (r2.trans (r3.trans r4)), by rw [code]; simp [elsePc, no, yes, cc]; omega,
      h3.congr rfl rfl rfl rfl, fun a lo hi => by simp only; rw [m3 a lo hi]; exact m1 a lo⟩

/-- A loop tests its condition, runs its body's code, and jumps back, until the condition is zero. -/
theorem loop_ok (m : Module) (c : Site) (fits : c.Fits) (fuel : Nat) (cond : Expr) (body : Stmt)
    (hc : cond.varsBelow c.vars) (ihb : StmtOk m c fuel body) (ihl : StmtOk m c fuel (.loop cond body)) :
    StmtOk m c (fuel + 1) (.loop cond body) := by
  intro pc pre post env ir s env' ir' layout hpre hpc holds room ex
  rw [exec] at ex
  simp only [bind, Option.bind] at ex
  cases ev : eval c.w env ir cond with
  | none => simp [ev] at ex
  | some v =>
  simp only [ev] at ex
  let cc := compileExpr c.vars pc cond 0
  let inner := compileStmt c.vars (pc + cc.length + 2) body
  let done := pc + cc.length + 2 + inner.length + 1
  have code : compileStmt c.vars pc (.loop cond body) = cc ++ [.test .rax, .jz done] ++ inner ++ [.jmp pc] := rfl
  have room' := room
  simp only [Stmt.temps] at room'
  -- The condition and its test.
  obtain ⟨s1, r1, p1, z1, h1, m1⟩ := test_ok c fits cond hc pc pre (.jz done :: (inner ++ [.jmp pc] ++ post)) env ir s v
    (by rw [code] at layout; simpa using layout) hpre hpc holds (by omega) ev
  have lay2 : (c.image.code c.routine).toList = (pre ++ cc ++ [Instr.test .rax]) ++ .jz done ::
      (inner ++ [.jmp pc] ++ post) := by rw [code] at layout; simpa using layout
  have at2 : s1.pc = (pre ++ cc ++ [Instr.test .rax]).length := by rw [p1]; simp [hpre, cc]; omega
  have r2 := Reaches.jz c.image c.routine s1 done (by rw [at2]; exact fetch_at c.image c.routine _ _ _ lay2)
    h1.running
  by_cases zero : v = 0
  · -- Out of the loop.
    subst zero
    simp only [beq_self_eq_true, ite_true, pure, Option.some.injEq, Prod.mk.injEq] at ex
    obtain ⟨rfl, rfl⟩ := ex
    have jump : (if s1.zf then done else s1.pc + 1) = done := by simp [z1]
    rw [jump] at r2
    exact ⟨_, r1.trans r2, by rw [code]; simp [done, inner, cc]; omega, h1.congr rfl rfl rfl rfl,
      fun a lo _ => m1 a lo⟩
  · -- Once through the body, then back to the test.
    have nz : (v == 0) = false := by simpa using zero
    simp only [nz, Bool.false_eq_true, ite_false] at ex
    cases eb : exec m c.w fuel c.base env ir body with
    | none => simp [eb] at ex
    | some p =>
    obtain ⟨env1, ir1⟩ := p
    simp only [eb] at ex
    have next : (if s1.zf then done else s1.pc + 1) = pc + cc.length + 2 := by
      simp [z1, zero, p1, cc] <;> omega
    rw [next] at r2
    obtain ⟨s3, r3, p3, h3, m3⟩ := ihb (pc + cc.length + 2) (pre ++ cc ++ [.test .rax, .jz done]) ([.jmp pc] ++ post)
      env ir { s1 with pc := pc + cc.length + 2 } env1 ir1 (by rw [code] at layout; simpa using layout)
      (by simp [hpre, cc]; omega) rfl (h1.congr rfl rfl rfl rfl) (by omega) eb
    have lay4 : (c.image.code c.routine).toList = (pre ++ cc ++ [Instr.test .rax, Instr.jz done] ++ inner) ++
        .jmp pc :: post := by rw [code] at layout; simpa using layout
    have at4 : s3.pc = (pre ++ cc ++ [Instr.test .rax, Instr.jz done] ++ inner).length := by
      rw [p3]; simp [hpre, cc, inner]; omega
    have r4 := Reaches.jmp c.image c.routine s3 pc (by rw [at4]; exact fetch_at c.image c.routine _ _ _ lay4)
      h3.running
    -- The loop again, from its start.
    obtain ⟨s5, r5, p5, h5, m5⟩ := ihl pc pre post env1 ir1 { s3 with pc := pc } env' ir' layout hpre rfl
      (h3.congr rfl rfl rfl rfl) room ex
    exact ⟨s5, r1.trans (r2.trans (r3.trans (r4.trans r5))), p5, h5, fun a lo hi => by
      rw [m5 a lo hi]; simp only; rw [m3 a lo hi]; exact m1 a lo⟩

/-- A store evaluates the address and the value, then writes the value's bytes. -/
theorem store_ok (m : Module) (c : Site) (fits : c.Fits) (fuel : Nat) (w : Width) (a v : Expr)
    (ha : a.varsBelow c.vars) (hv : v.varsBelow c.vars) : StmtOk m c fuel (.store w a v) := by
  intro pc pre post env ir s env' ir' layout hpre hpc holds room ex
  cases fuel with
  | zero => simp [exec] at ex
  | succ n =>
  simp only [exec, bind, Option.bind] at ex
  cases ea : eval c.w env ir a with
  | none => simp [ea] at ex
  | some x =>
  cases eb : eval c.w env ir v with
  | none => simp [ea, eb] at ex
  | some y =>
  simp only [ea, eb] at ex
  split at ex
  · rename_i ok
    simp only [pure, Option.some.injEq, Prod.mk.injEq] at ex
    obtain ⟨rfl, rfl⟩ := ex
    let ca := compileExpr c.vars pc a 0
    let cv := compileExpr c.vars (pc + ca.length + 1) v 1
    have code : compileStmt c.vars pc (.store w a v) =
        joinOperands c.vars 0 ca cv [] ++ [.store w ⟨.rax, 0⟩ .rcx] := by
      simp [compileStmt, joinOperands, ca, cv, Nat.add_assoc]
    rw [code] at layout
    obtain ⟨s4, r4, p4, rax4, rcx4, h4, m4⟩ := operands_ok c fits a v (expr_ok c fits a ha) (expr_ok c fits v hv)
      env ir 0 pc pre ([.store w ⟨.rax, 0⟩ .rcx] ++ post) s x y (by simpa using layout) hpre hpc holds
      (by simpa [Stmt.temps] using room) ea eb
    have lay5 : (c.image.code c.routine).toList = (pre ++ joinOperands c.vars 0 ca cv []) ++
        [.store w ⟨.rax, 0⟩ .rcx] ++ post := by simpa using layout
    have r5 := Reaches.one c.image c.routine _ _ _ lay5 (by simp [Instr.straight]) s4
      (by rw [p4]; simp [joinOperands, hpre, ca, cv]; omega) h4.running
    simp only [World.access, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at ok
    have addr : s4.addr ⟨.rax, 0⟩ = x.toNat := by simp [State.addr, rax4]
    refine ⟨_, r4.trans r5, by rw [code]; simp [joinOperands, hpre, ca, cv]; omega, ?_, fun b lo hi => ?_⟩
    · refine ⟨by simp [exec1]; exact h4.rsp, fun z hz => ?_, fun b hb => ?_, by simp [exec1]; exact h4.cpu,
        by simp [exec1]; exact h4.running, by simp [exec1]; exact h4.kept⟩
      · simp only [exec1, addr, rcx4]
        rw [← h4.vars z hz]
        apply readLE_congr
        intro k hk
        simp only [store]
        rw [ite_eq_right (by have := fits.low; have := fits.high; have := fits.vars; omega)]
      · simp only [exec1, addr, rcx4, store]
        split
        · rfl
        · exact h4.heap b hb
    · simp only [exec1, addr, store]
      have := fits.low
      rw [ite_eq_right (by omega)]
      exact m4 b (Or.inr lo)
  · simp at ex

/-- The arguments' slots reach at least the position after the last argument. -/
theorem argsTemps_ge : ∀ (args : List Expr) (i : Nat), i + args.length ≤ argsTemps args i
  | [], i => by simp [argsTemps]
  | a :: rest, i => by
    have := argsTemps_ge rest (i + 1)
    simp only [argsTemps, List.length_cons]
    omega

/-- Arguments evaluated in order, argument j parked in the slot j places above a first one. -/
theorem args_ok (c : Site) (fits : c.Fits) (env : Env) (ir : Memory) :
    ∀ (args : List Expr) (i pc : Nat) (pre rest : List Instr) (s : State) (values : List UInt64),
      args.all (·.varsBelow c.vars) →
      (c.image.code c.routine).toList = pre ++ compileArgs c.vars pc args i ++ rest → pre.length = pc → s.pc = pc →
      c.Holds env ir s → c.vars + argsTemps args i ≤ c.frame →
      args.mapM (eval c.w env ir) = some values →
      ∃ s', Reaches c.image c.routine s s' ∧ s'.pc = pc + (compileArgs c.vars pc args i).length ∧ c.Holds env ir s' ∧
        values.length = args.length ∧
        (∀ j < values.length, readLE s'.mem (c.base + 8 * (c.vars + i + j)) 8 = values.getD j 0) ∧
        ∀ a, (a < c.base + 8 * (c.vars + i) ∨ c.base + 8 * c.frame ≤ a) → s'.mem a = s.mem a
  | [], i, pc, pre, rest, s, values, _, _, _, hpc, holds, _, ev => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at ev; subst ev
    exact ⟨s, Reaches.refl _ _ _, by simp [compileArgs, hpc], holds, rfl, by simp, fun _ _ => rfl⟩
  | a :: more, i, pc, pre, rest, s, values, wf, layout, hpre, hpc, holds, room, ev => by
    simp only [List.all_cons, Bool.and_eq_true] at wf
    simp only [List.mapM_cons, bind, Option.bind] at ev
    cases ea : eval c.w env ir a with
    | none => simp [ea] at ev
    | some v =>
    cases em : more.mapM (eval c.w env ir) with
    | none => simp [ea, em] at ev
    | some vs =>
    simp only [ea, em, pure, Option.some.injEq] at ev; subst ev
    simp only [argsTemps] at room
    have above := argsTemps_ge more (i + 1)
    let here := compileExpr c.vars pc a i ++ [.store .b8 (slot (c.vars + i)) .rax]
    -- This argument, into its slot.
    obtain ⟨s1, r1, p1, rax1, h1, m1⟩ := expr_ok c fits a wf.1 i pc pre
      ([.store .b8 (slot (c.vars + i)) .rax] ++ compileArgs c.vars (pc + here.length) more (i + 1) ++ rest) env ir s v
      (by simpa [compileArgs, here] using layout) hpre hpc holds (by omega) ea
    have lay2 : (c.image.code c.routine).toList = (pre ++ compileExpr c.vars pc a i) ++
        [.store .b8 (slot (c.vars + i)) .rax] ++ (compileArgs c.vars (pc + here.length) more (i + 1) ++ rest) := by
      simpa [compileArgs, here] using layout
    have r2 := Reaches.one c.image c.routine _ _ _ lay2 (by simp [Instr.straight]) s1 (by simp [p1, hpre]) h1.running
    let s2 := { exec1 (.store .b8 (slot (c.vars + i)) .rax) s1 with
      pc := (pre ++ compileExpr c.vars pc a i).length + 1 }
    have mem2 : s2.mem = store s1.mem (c.base + 8 * (c.vars + i)) 8 (qwordByte v) := by
      simp [s2, exec1, slot_addr c fits s1 h1.rsp, rax1, Width.bytes]
    have h2 : c.Holds env ir s2 :=
      (h1.setSlot fits (c.vars + i) (by omega) (by omega) v).congr (by simp [s2, exec1]) mem2 (by simp [s2, exec1])
        (by simp [s2, exec1])
    -- The rest, above it.
    obtain ⟨s3, r3, p3, h3, len3, vals3, m3⟩ := args_ok c fits env ir more (i + 1) (pc + here.length)
      (pre ++ here) rest s2 vs wf.2 (by simpa [compileArgs, here] using layout) (by simp [hpre, here])
      (by simp [s2, hpre, here]; omega) h2 (by omega) em
    refine ⟨s3, r1.trans (r2.trans r3), by rw [p3]; simp [compileArgs, here]; omega, h3, by simp [len3], ?_,
      fun b hb => ?_⟩
    · intro j hj
      cases j with
      | zero =>
        simp only [Nat.add_zero, List.getD_cons_zero]
        rw [readLE_congr s3.mem s2.mem _ 8 (fun k hk => m3 _ (by omega)), mem2, readLE_store8]
      | succ j =>
        have := vals3 j (by simp at hj; omega)
        simp only [List.getD_cons_succ]
        rw [← this, show c.vars + i + (j + 1) = c.vars + (i + 1) + j by omega]
    · rw [m3 b (by omega)]
      have e2 : s2.mem b = s1.mem b := by
        rw [mem2]; simp only [store]; rw [ite_eq_right (by omega)]
      rw [e2, m1 b (by omega)]

/-- The six argument registers are distinct. -/
theorem argReg_inj (i j : Nat) (hi : i < 6) (hj : j < 6) (h : argReg i = argReg j) : i = j := by
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [argReg]

/-- An argument register is a scratch register. -/
theorem argReg_scratch (i : Nat) : argReg i ∈ [Gpr.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11] := by
  unfold argReg; split <;> simp

/-- Loading parked arguments puts each in its register, and keeps the correspondence and memory. -/
theorem loads_ok (c : Site) (fits : c.Fits) (env : Env) (ir : Memory) :
    ∀ (n : Nat) (s : State), n ≤ 6 → c.Holds env ir s →
      c.Holds env ir (Asm.exec (argLoads c.vars n) s) ∧
      (∀ i < n, (Asm.exec (argLoads c.vars n) s).gpr (argReg i) = readLE s.mem (c.base + 8 * (c.vars + i)) 8) ∧
      (Asm.exec (argLoads c.vars n) s).mem = s.mem
  | 0, s, _, holds => ⟨holds, by simp, by simp [argLoads]⟩
  | n + 1, s, hn, holds => by
    obtain ⟨h1, regs1, m1⟩ := loads_ok c fits env ir n s (by omega) holds
    have split : argLoads c.vars (n + 1) = argLoads c.vars n ++ [.load .b8 (argReg n) (slot (c.vars + n))] := by
      simp [argLoads, List.range_succ]
    rw [split, exec_append]
    let s1 := Asm.exec (argLoads c.vars n) s
    have addr : s1.addr (slot (c.vars + n)) = c.base + 8 * (c.vars + n) := slot_addr c fits s1 h1.rsp _
    refine ⟨?_, fun i hi => ?_, by simp [Asm.exec, exec1, m1]⟩
    · exact h1.update (argReg n) (argReg_scratch n) (readLE s1.mem (s1.addr (slot (c.vars + n))) 8)
        (by simp [Asm.exec, exec1, s1, Width.bytes]) (by simp [Asm.exec, exec1])
        (by simp [Asm.exec, exec1]) (by simp [Asm.exec, exec1])
    · simp only [Asm.exec, exec1, assign]
      split
      · rename_i same
        have := argReg_inj i n (by omega) (by omega) same
        subst this
        simp [addr, m1, s1, Width.bytes]
      · rename_i other
        exact regs1 i (by
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact h
          · subst h; exact absurd rfl other)

/-- A call parks its arguments, moves them into registers, calls, and stores the result. -/
theorem call_ok (m : Module) (c : Site) (fits : c.Fits) (fuel : Nat) (f : String) (args : List Expr) (dst : Nat)
    (wf : (Stmt.call f args dst).wf c.vars) (calls : CallOk c.image c.w f (callSpec m c.w fuel f)) :
    StmtOk m c (fuel + 1) (.call f args dst) := by
  intro pc pre post env ir s env' ir' layout hpre hpc holds room ex
  simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at wf
  obtain ⟨⟨few, hdst⟩, hargs⟩ := wf
  rw [exec_call] at ex
  simp only [bind, Option.bind] at ex
  cases ev : args.mapM (eval c.w env ir) with
  | none => simp [ev] at ex
  | some values =>
  simp only [ev] at ex
  cases ec : callSpec m c.w fuel f c.base values ir with
  | none => simp [ec] at ex
  | some p =>
  obtain ⟨res, ir1⟩ := p
  simp only [ec, pure, Option.some.injEq, Prod.mk.injEq] at ex
  obtain ⟨rfl, rfl⟩ := ex
  simp only [Stmt.temps] at room
  let parked := compileArgs c.vars pc args 0
  let loads := argLoads c.vars args.length
  have code : compileStmt c.vars pc (.call f args dst) = parked ++ loads ++ [.call f, .store .b8 (slot dst) .rax] :=
    rfl
  rw [code] at layout
  -- The arguments, parked.
  obtain ⟨s1, r1, p1, h1, len1, vals1, m1⟩ := args_ok c fits env ir args 0 pc pre
    (loads ++ [.call f, .store .b8 (slot dst) .rax] ++ post) s values hargs (by simpa using layout) hpre hpc holds
    (by omega) ev
  -- Into their registers.
  have lay2 : (c.image.code c.routine).toList = (pre ++ parked) ++ loads ++ ([.call f, .store .b8 (slot dst) .rax] ++
      post) := by simpa using layout
  have r2 := Reaches.block c.image c.routine _ _ _ lay2 (by simp [loads, argLoads, Instr.straight]) s1
    (by simp [p1, hpre, parked]) h1.running
  let s2 := { Asm.exec loads s1 with pc := (pre ++ parked).length + loads.length }
  obtain ⟨hl, regs, ml⟩ := loads_ok c fits env ir args.length s1 few h1
  have h2 : c.Holds env ir s2 := hl.congr rfl rfl rfl rfl
  -- The call.
  have lay3 : (c.image.code c.routine).toList = (pre ++ parked ++ loads) ++ .call f ::
      (.store .b8 (slot dst) .rax :: post) := by simpa using layout
  have fetch3 : (c.image.code c.routine)[s2.pc]? = some (.call f) := by
    rw [show s2.pc = (pre ++ parked ++ loads).length by simp [s2]; omega]; exact fetch_at c.image c.routine _ _ _ lay3
  have bound3 : s2.pc + 1 < 2 ^ 32 := by
    have size := congrArg List.length lay3
    simp only [Array.length_toList, List.length_append, List.length_cons] at size
    have := fits.code
    simp [s2] at size ⊢; omega
  obtain ⟨s3, r3, p3, rax3, rsp3, kept3, heap3, stack3, cpu3, run3⟩ := calls c.routine s2 c.base values ir ir1 res
    fetch3 h2.running h2.cpu fits.routine.1 fits.routine.2 bound3 h2.rsp (by have := fits.high; omega) fits.bound
    (by omega) (fun i hi => by
      rw [show s2.gpr (argReg i) = (Asm.exec loads s1).gpr (argReg i) from rfl, regs i (by omega)]
      exact vals1 i hi) (fun a ha => by rw [show s2.mem = s1.mem from ml]; exact h1.heap a ha) ec
  have h3 : c.Holds env ir1 s3 := by
    refine ⟨rsp3, fun x hx => ?_, heap3, by rw [cpu3]; exact h2.cpu, run3, fun g hg => by rw [kept3 g hg]; exact h2.kept g hg⟩
    rw [← h2.vars x hx]
    apply readLE_congr
    intro k hk
    have := fits.low; have := fits.high; have := fits.vars
    exact stack3 _ (by omega) (by omega)
  -- The result, into its variable.
  have lay4 : (c.image.code c.routine).toList = (pre ++ parked ++ loads ++ [.call f]) ++
      [.store .b8 (slot dst) .rax] ++ post := by simpa using layout
  have r4 := Reaches.one c.image c.routine _ _ _ lay4 (by simp [Instr.straight]) s3 (by simp [p3, s2]; omega) run3
  refine ⟨_, r1.trans (r2.trans (r3.trans r4)), by rw [code]; simp [hpre]; omega, ?_, fun a lo hi => ?_⟩
  · refine (h3.setVar fits dst hdst res).congr (by simp [exec1]) ?_ (by simp [exec1]) (by simp [exec1])
    simp [exec1, slot_addr c fits s3 h3.rsp, rax3, Width.bytes]
  · simp only [exec1, slot_addr c fits s3 h3.rsp, store, Width.bytes]
    have := fits.vars
    rw [ite_eq_right (by omega), stack3 a (by omega) hi, show s2.mem = s1.mem from ml, m1 a (Or.inr lo)]

/-- With no fuel, no statement has a meaning, so its code owes nothing. -/
theorem zero_ok (m : Module) (c : Site) (stmt : Stmt) : StmtOk m c 0 stmt := by
  intro pc pre post env ir s env' ir' layout hpre hpc holds room ex
  simp [exec] at ex

/--
Every statement's code computes its meaning, given that every call computes its meaning with less fuel.

The fuel bounds the calls the statement may make.
-/
theorem stmt_ok (m : Module) (c : Site) (fits : c.Fits) (bound : Nat)
    (calls : ∀ j < bound, ∀ name, CallOk c.image c.w name (callSpec m c.w j name)) :
    ∀ fuel ≤ bound, ∀ stmt : Stmt, stmt.wf c.vars → StmtOk m c fuel stmt := by
  intro fuel
  induction fuel with
  | zero => intro _ stmt _; exact zero_ok m c stmt
  | succ k ih =>
    intro hk stmt wf
    have ih' := ih (by omega)
    cases stmt with
    | skip => exact skip_ok m c _
    | set x e =>
      simp only [Stmt.wf, Bool.and_eq_true, decide_eq_true_eq] at wf
      exact set_ok m c fits _ x e wf.1 wf.2
    | store w a v =>
      simp only [Stmt.wf, Bool.and_eq_true] at wf
      exact store_ok m c fits _ w a v wf.1 wf.2
    | seq a b =>
      simp only [Stmt.wf, Bool.and_eq_true] at wf
      exact seq_ok m c k a b (ih' a wf.1) (ih' b wf.2)
    | ite cond t e =>
      simp only [Stmt.wf, Bool.and_eq_true] at wf
      exact ite_ok m c fits k cond t e wf.1.1 (ih' t wf.1.2) (ih' e wf.2)
    | loop cond body =>
      have whole := wf
      simp only [Stmt.wf, Bool.and_eq_true] at wf
      exact loop_ok m c fits k cond body wf.1 (ih' body wf.2) (ih' _ whole)
    | call f args dst => exact call_ok m c fits k f args dst wf (calls k (by omega) f)

end EthLib.Consensus.Ssz.Native.Ir
