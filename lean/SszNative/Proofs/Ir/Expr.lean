import SszNative.Proofs.Ir.Frame

/-!
The code of every expression computes its value.

It leaves the value in rax, keeps the frame matching the variables, and writes only the temporaries above its depth.
-/

namespace Ssz.Native.Ir

open Ssz.Native.Asm

/-- One straight instruction at a layout position. -/
theorem Reaches.one (image : Image) (r : Nat) (pre post : List Instr) (i : Instr)
    (layout : (image.code r).toList = pre ++ [i] ++ post) (straight : i.straight)
    (s : State) (at_ : s.pc = pre.length) (running : s.status = .running) :
    Reaches image r s { exec1 i s with pc := pre.length + 1 } := by
  have := Reaches.block image r pre [i] post layout (by simpa using straight) s at_ running
  simpa [exec] using this

/-- What an expression's code guarantees, from a state matching its variables. -/
def ExprOk (c : Site) (e : Expr) : Prop :=
  ∀ (d pc : Nat) (pre post : List Instr) (env : Env) (ir : Memory) (s : State) (v : UInt64),
    (c.image.code c.routine).toList = pre ++ compileExpr c.vars pc e d ++ post →
    pre.length = pc → s.pc = pc → c.Holds env ir s → c.vars + d + e.temps ≤ c.frame →
    eval c.w env ir e = some v →
    ∃ s', Reaches c.image c.routine s s' ∧ s'.pc = pc + (compileExpr c.vars pc e d).length ∧
      s'.gpr .rax = v ∧ c.Holds env ir s' ∧
      ∀ a, (a < c.base + 8 * (c.vars + d) ∨ c.base + 8 * c.frame ≤ a) → s'.mem a = s.mem a

/-- A constant is one move into rax. -/
theorem lit_ok (c : Site) (n : UInt64) : ExprOk c (.lit n) := by
  intro d pc pre post env ir s v layout hpre hpc holds room ev
  simp only [eval, Option.some.injEq] at ev
  subst ev
  refine ⟨_, Reaches.one c.image c.routine pre post _ layout (by simp [Instr.straight]) s (by omega) holds.running,
    by simp [compileExpr, hpre], by simp [exec1, assign], ?_, fun a _ => rfl⟩
  have := holds.setGpr .rax (by simp) n
  exact ⟨this.rsp, this.vars, this.heap, this.cpu, this.running, this.kept⟩

/-- A variable is one load from its slot. -/
theorem var_ok (c : Site) (fits : c.Fits) (x : Nat) (hx : x < c.vars) : ExprOk c (.var x) := by
  intro d pc pre post env ir s v layout hpre hpc holds room ev
  simp only [eval, Option.some.injEq] at ev
  subst ev
  refine ⟨_, Reaches.one c.image c.routine pre post _ layout (by simp [Instr.straight]) s (by omega) holds.running,
    by simp [compileExpr, hpre], ?_, ?_, fun a _ => rfl⟩
  · simp [exec1, assign, slot_addr c fits s holds.rsp, Width.bytes, holds.vars x hx]
  · have := holds.setGpr .rax (by simp) (readLE s.mem (s.addr (slot x)) 8)
    exact ⟨this.rsp, this.vars, this.heap, this.cpu, this.running, this.kept⟩

/-- A left shift writes only its register, by its count's low six bits. -/
theorem exec1_shlImm (r : Gpr) (k : Nat) (s : State) :
    (exec1 (.shlImm r k) s).gpr = assign s.gpr r (s.gpr r <<< (k % 64).toUInt64) ∧
      (exec1 (.shlImm r k) s).mem = s.mem ∧ (exec1 (.shlImm r k) s).cpu = s.cpu ∧
      (exec1 (.shlImm r k) s).status = s.status := by
  simp only [exec1]
  split
  · rename_i h; refine ⟨funext fun g => ?_, rfl, rfl, rfl⟩
    simp only [assign, h]; split <;> simp_all
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- A right shift writes only its register, by its count's low six bits. -/
theorem exec1_shrImm (r : Gpr) (k : Nat) (s : State) :
    (exec1 (.shrImm r k) s).gpr = assign s.gpr r (s.gpr r >>> (k % 64).toUInt64) ∧
      (exec1 (.shrImm r k) s).mem = s.mem ∧ (exec1 (.shrImm r k) s).cpu = s.cpu ∧
      (exec1 (.shrImm r k) s).status = s.status := by
  simp only [exec1]
  split
  · rename_i h; refine ⟨funext fun g => ?_, rfl, rfl, rfl⟩
    simp only [assign, h]; split <;> simp_all
  · exact ⟨rfl, rfl, rfl, rfl⟩

/--
The code of an operand, then one instruction writing rax from rax alone.

The instruction's effect is given by its new rax value, with memory, processor and status untouched.
-/
theorem unary_ok (c : Site) (a : Expr) (ih : ExprOk c a) (i : Instr) (straight : i.straight)
    (f : UInt64 → Option UInt64) (env : Env) (ir : Memory)
    (effect : ∀ s : State, c.Holds env ir s → ∀ x y, s.gpr .rax = x → f x = some y →
      (exec1 i s).gpr = assign s.gpr .rax y ∧ (exec1 i s).mem = s.mem ∧ (exec1 i s).cpu = s.cpu ∧
        (exec1 i s).status = s.status)
    (d pc : Nat) (pre post : List Instr) (s : State) (v : UInt64)
    (layout : (c.image.code c.routine).toList = pre ++ (compileExpr c.vars pc a d ++ [i]) ++ post)
    (hpre : pre.length = pc) (hpc : s.pc = pc) (holds : c.Holds env ir s) (room : c.vars + d + a.temps ≤ c.frame)
    (ev : (eval c.w env ir a).bind f = some v) :
    ∃ s', Reaches c.image c.routine s s' ∧ s'.pc = pc + (compileExpr c.vars pc a d ++ [i]).length ∧
      s'.gpr .rax = v ∧ c.Holds env ir s' ∧
      ∀ a, (a < c.base + 8 * (c.vars + d) ∨ c.base + 8 * c.frame ≤ a) → s'.mem a = s.mem a := by
  cases ea : eval c.w env ir a with
  | none => simp [ea] at ev
  | some x =>
    simp only [ea, Option.bind_some] at ev
    have lay : (c.image.code c.routine).toList = pre ++ compileExpr c.vars pc a d ++ ([i] ++ post) := by
      simpa using layout
    obtain ⟨s1, r1, p1, rax1, h1, m1⟩ := ih d pc pre _ env ir s x lay hpre hpc holds room ea
    have lay2 : (c.image.code c.routine).toList = (pre ++ compileExpr c.vars pc a d) ++ [i] ++ post := by
      simpa using lay
    obtain ⟨g, m, cpu, st⟩ := effect s1 h1 x v rax1 ev
    refine ⟨_, r1.trans (Reaches.one c.image c.routine _ post _ lay2 straight s1 (by simp [p1, hpre]) h1.running),
      by simp only [List.length_append, List.length_singleton, hpre]; omega, by simp [g, assign],
      h1.update .rax (by simp) v (by simp [g]) (by simp [m]) (by simp [cpu]) (by simp), fun a ha => by simp [m, m1 a ha]⟩

/-- A left shift is its operand, then one shift of rax. -/
theorem shl_ok (c : Site) (a : Expr) (k : Nat) (ih : ExprOk c a) : ExprOk c (.shl a k) := by
  intro d pc pre post env ir s v layout hpre hpc holds room ev
  have := unary_ok c a ih (.shlImm .rax k) (by simp [Instr.straight])
    (fun x => if k < 64 then some (x <<< k.toUInt64) else none)
    env ir (fun s _ x y hx hy => by
      split at hy
      · simp only [Option.some.injEq] at hy; subst hy
        rename_i hk; have e := exec1_shlImm .rax k s; rw [Nat.mod_eq_of_lt hk, hx] at e; exact e
      · simp at hy)
    d pc pre post s v (by simpa [compileExpr] using layout) hpre hpc holds (by simpa [Expr.temps] using room)
    (by simpa [eval, bind, Option.bind] using ev)
  simpa [compileExpr] using this

/-- A right shift is its operand, then one shift of rax. -/
theorem shr_ok (c : Site) (a : Expr) (k : Nat) (ih : ExprOk c a) : ExprOk c (.shr a k) := by
  intro d pc pre post env ir s v layout hpre hpc holds room ev
  have := unary_ok c a ih (.shrImm .rax k) (by simp [Instr.straight])
    (fun x => if k < 64 then some (x >>> k.toUInt64) else none)
    env ir (fun s _ x y hx hy => by
      split at hy
      · simp only [Option.some.injEq] at hy; subst hy
        rename_i hk; have e := exec1_shrImm .rax k s; rw [Nat.mod_eq_of_lt hk, hx] at e; exact e
      · simp at hy)
    d pc pre post s v (by simpa [compileExpr] using layout) hpre hpc holds (by simpa [Expr.temps] using room)
    (by simpa [eval, bind, Option.bind] using ev)
  simpa [compileExpr] using this

/-- A load is its address, then one load through rax, which reads the program's memory off the stack. -/
theorem load_ok (c : Site) (a : Expr) (w : Width) (ih : ExprOk c a) : ExprOk c (.load w a) := by
  intro d pc pre post env ir s v layout hpre hpc holds room ev
  have := unary_ok c a ih (.load w .rax ⟨.rax, 0⟩) (by simp [Instr.straight])
    (fun x => if c.w.access x.toNat w.bytes then some (readLE ir x.toNat w.bytes) else none)
    env ir (fun s hs x y hx hy => by
      split at hy
      · simp only [Option.some.injEq] at hy; subst hy
        rename_i ok
        refine ⟨?_, rfl, rfl, rfl⟩
        simp only [exec1, State.addr, hx, Nat.add_zero]
        congr 1
        apply readLE_congr
        intro k hk
        apply hs.heap
        simp only [World.access, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at ok
        omega
      · simp at hy)
    d pc pre post s v (by simpa [compileExpr] using layout) hpre hpc holds (by simpa [Expr.temps] using room)
    (by simpa [eval, bind, Option.bind] using ev)
  simpa [compileExpr] using this

/-- A division with a divisor above the high half of the dividend steps on, as the instruction alone does. -/
theorem Reaches.div (image : Image) (r : Nat) (s : State) (g : Gpr) (fetch : (image.code r)[s.pc]? = some (.div g))
    (nonzero : s.gpr g ≠ 0) (fits : (s.gpr .rdx).toNat < (s.gpr g).toNat) (running : s.status = .running) :
    Reaches image r s { exec1 (.div g) s with pc := s.pc + 1 } := by
  refine ⟨1, ?_⟩
  simp only [Image.run, image_step_plain image r s _ fetch (by simp) (by simp)]
  simp [step, running, fetch, nonzero, Nat.not_le.mpr fits]

/-- A conditional branch goes to its target when the flags satisfy it, and on otherwise. -/
theorem Reaches.jcc (image : Image) (r : Nat) (s : State) (c : Cond) (t : Nat)
    (fetch : (image.code r)[s.pc]? = some (.jcc c t)) (running : s.status = .running) :
    Reaches image r s { s with pc := if c.holds s.zf s.cf then t else s.pc + 1 } := by
  refine ⟨1, ?_⟩
  simp only [Image.run, image_step_plain image r s _ fetch (by simp) (by simp)]
  simp [step, running, fetch]

/-- What the instructions combining two operands in rax and rcx guarantee. -/
def FinishOk (c : Site) (env : Env) (ir : Memory) (finish : Nat → List Instr)
    (g : UInt64 → UInt64 → Option UInt64) : Prop :=
  ∀ (pre post : List Instr) (s : State) (x y z : UInt64),
    (c.image.code c.routine).toList = pre ++ finish pre.length ++ post → s.pc = pre.length → c.Holds env ir s →
    s.gpr .rax = x → s.gpr .rcx = y → g x y = some z →
    ∃ s', Reaches c.image c.routine s s' ∧ s'.pc = pre.length + (finish pre.length).length ∧ s'.gpr .rax = z ∧
      c.Holds env ir s' ∧ s'.mem = s.mem

/-- Joined operands are the code before the finish. -/
theorem joinOperands_append (vars d : Nat) (first second finish : List Instr) :
    joinOperands vars d first second finish = joinOperands vars d first second [] ++ finish := by
  simp [joinOperands]

/-- Two operands evaluated: the first in rax and the second in rcx, the frame's correspondence kept. -/
theorem operands_ok (c : Site) (fits : c.Fits) (a b : Expr) (iha : ExprOk c a) (ihb : ExprOk c b)
    (env : Env) (ir : Memory) (d pc : Nat) (pre rest : List Instr) (s : State) (x y : UInt64)
    (layout : (c.image.code c.routine).toList = pre ++ joinOperands c.vars d (compileExpr c.vars pc a d)
      (compileExpr c.vars (pc + (compileExpr c.vars pc a d).length + 1) b (d + 1)) [] ++ rest)
    (hpre : pre.length = pc) (hpc : s.pc = pc) (holds : c.Holds env ir s)
    (room : c.vars + d + max a.temps (b.temps + 1) ≤ c.frame)
    (ea : eval c.w env ir a = some x) (eb : eval c.w env ir b = some y) :
    ∃ s', Reaches c.image c.routine s s' ∧
      s'.pc = pc + (compileExpr c.vars pc a d).length + 1 +
        (compileExpr c.vars (pc + (compileExpr c.vars pc a d).length + 1) b (d + 1)).length + 2 ∧
      s'.gpr .rax = x ∧ s'.gpr .rcx = y ∧ c.Holds env ir s' ∧
      ∀ a, (a < c.base + 8 * (c.vars + d) ∨ c.base + 8 * c.frame ≤ a) → s'.mem a = s.mem a := by
  -- The pieces of the code, and their positions.
  let ca := compileExpr c.vars pc a d
  let cb := compileExpr c.vars (pc + ca.length + 1) b (d + 1)
  let park : Instr := .store .b8 (slot (c.vars + d)) .rax
  let fetchBack : List Instr := [.movReg .rcx .rax, .load .b8 .rax (slot (c.vars + d))]
  -- The first operand.
  obtain ⟨s1, r1, p1, rax1, h1, m1⟩ := iha d pc pre ([park] ++ cb ++ fetchBack ++ rest) env ir s x
    (by simpa [joinOperands, ca, cb, park, fetchBack] using layout) hpre hpc holds (by omega) ea
  -- It waits in its slot.
  have lay2 : (c.image.code c.routine).toList = (pre ++ ca) ++ [park] ++ (cb ++ fetchBack ++ rest) := by
    simpa [joinOperands, ca, cb, park, fetchBack] using layout
  have r2 := Reaches.one c.image c.routine _ _ _ lay2 (by simp [park, Instr.straight]) s1 (by simp [p1, hpre, ca])
    h1.running
  let s2 := { exec1 park s1 with pc := (pre ++ ca).length + 1 }
  have slotAddr : s1.addr (slot (c.vars + d)) = c.base + 8 * (c.vars + d) := slot_addr c fits s1 h1.rsp _
  have mem2 : s2.mem = store s1.mem (c.base + 8 * (c.vars + d)) 8 (qwordByte x) := by
    simp [s2, park, exec1, slotAddr, rax1, Width.bytes]
  have h2 : c.Holds env ir s2 := by
    have := h1.setSlot fits (c.vars + d) (by omega) (by omega) x
    exact this.congr (by simp [s2, park, exec1]) mem2 (by simp [s2, park, exec1]) (by simp [s2])
  -- The second operand, above the slot.
  obtain ⟨s3, r3, p3, rax3, h3, m3⟩ := ihb (d + 1) (pc + ca.length + 1) (pre ++ ca ++ [park])
    (fetchBack ++ rest) env ir s2 y (by simpa [joinOperands, ca, cb, park, fetchBack] using layout)
    (by simp [hpre, ca] <;> omega) (by simp [s2, hpre, ca] <;> omega) h2 (by omega) eb
  -- Both into rax and rcx.
  have lay4 : (c.image.code c.routine).toList = (pre ++ ca ++ [park] ++ cb) ++ fetchBack ++ rest := by
    simpa [joinOperands, ca, cb, park, fetchBack] using layout
  have r4 := Reaches.block c.image c.routine _ _ _ lay4 (by simp [fetchBack, Instr.straight]) s3
    (by simp [p3, hpre, ca, cb] <;> omega) h3.running
  let s4 := { Asm.exec fetchBack s3 with pc := (pre ++ ca ++ [park] ++ cb).length + fetchBack.length }
  have slot3 : s3.addr (slot (c.vars + d)) = c.base + 8 * (c.vars + d) := slot_addr c fits s3 h3.rsp _
  have back : readLE s3.mem (c.base + 8 * (c.vars + d)) 8 = x := by
    rw [readLE_congr s3.mem s2.mem _ 8 (fun k hk => m3 _ (by omega)), mem2, readLE_store8]
  have g4 : s4.gpr = assign (assign s3.gpr .rcx y) .rax x := by
    simp only [s4, fetchBack, Asm.exec, exec1]
    rw [slot_addr c fits _ (by simp [assign, h3.rsp])]
    funext r
    simp [assign, Width.bytes, back, rax3]
  have rax4 : s4.gpr .rax = x := by simp [g4, assign]
  have rcx4 : s4.gpr .rcx = y := by simp [g4, assign]
  have h4 : c.Holds env ir s4 := by
    have := (h3.setGpr .rcx (by simp) y).setGpr .rax (by simp) x
    exact this.congr g4 (by simp [s4, fetchBack, Asm.exec, exec1]) (by simp [s4, fetchBack, Asm.exec, exec1])
      (by simp [s4, fetchBack, Asm.exec, exec1])
  refine ⟨s4, r1.trans (r2.trans (r3.trans r4)), ?_, rax4, rcx4, h4, fun a ha => ?_⟩
  · simp [s4, fetchBack, hpre, ca, cb]; omega
  · have e4 : s4.mem = s3.mem := by simp [s4, fetchBack, Asm.exec, exec1]
    rw [e4, m3 a (by omega)]
    have e2 : s2.mem a = s1.mem a := by
      rw [mem2]; simp only [store]; rw [if_neg (by omega)]
    rw [e2, m1 a ha]

/-- Two operands, then a finish that combines rax and rcx into the value. -/
theorem binary_ok (c : Site) (fits : c.Fits) (a b : Expr) (iha : ExprOk c a) (ihb : ExprOk c b)
    (finish : Nat → List Instr) (g : UInt64 → UInt64 → Option UInt64) (env : Env) (ir : Memory)
    (fin : FinishOk c env ir finish g)
    (d pc : Nat) (pre post : List Instr) (s : State) (v : UInt64)
    (layout : (c.image.code c.routine).toList = pre ++ joinOperands c.vars d (compileExpr c.vars pc a d)
      (compileExpr c.vars (pc + (compileExpr c.vars pc a d).length + 1) b (d + 1))
      (finish (pc + (compileExpr c.vars pc a d).length + 1 +
        (compileExpr c.vars (pc + (compileExpr c.vars pc a d).length + 1) b (d + 1)).length + 2)) ++ post)
    (hpre : pre.length = pc) (hpc : s.pc = pc) (holds : c.Holds env ir s)
    (room : c.vars + d + max a.temps (b.temps + 1) ≤ c.frame)
    (ev : (do let x ← eval c.w env ir a; let y ← eval c.w env ir b; g x y) = some v) :
    ∃ s', Reaches c.image c.routine s s' ∧
      s'.pc = pc + (joinOperands c.vars d (compileExpr c.vars pc a d)
        (compileExpr c.vars (pc + (compileExpr c.vars pc a d).length + 1) b (d + 1))
        (finish (pc + (compileExpr c.vars pc a d).length + 1 +
          (compileExpr c.vars (pc + (compileExpr c.vars pc a d).length + 1) b (d + 1)).length + 2))).length ∧
      s'.gpr .rax = v ∧ c.Holds env ir s' ∧
      ∀ a, (a < c.base + 8 * (c.vars + d) ∨ c.base + 8 * c.frame ≤ a) → s'.mem a = s.mem a := by
  cases ea : eval c.w env ir a with
  | none => simp [ea] at ev
  | some x =>
  cases eb : eval c.w env ir b with
  | none => simp [ea, eb] at ev
  | some y =>
  simp only [ea, eb, Option.bind_eq_bind, Option.bind_some] at ev
  let ca := compileExpr c.vars pc a d
  let cb := compileExpr c.vars (pc + ca.length + 1) b (d + 1)
  let fc := finish (pc + ca.length + 1 + cb.length + 2)
  -- The operands, then the finish.
  rw [joinOperands_append] at layout
  obtain ⟨s4, r4, p4, rax4, rcx4, h4, m4⟩ := operands_ok c fits a b iha ihb env ir d pc pre (fc ++ post) s x y
    (by simpa using layout) hpre hpc holds room ea eb
  have hlen : (pre ++ joinOperands c.vars d ca cb []).length = pc + ca.length + 1 + cb.length + 2 := by
    simp [joinOperands, hpre]; omega
  have lay5 : (c.image.code c.routine).toList =
      (pre ++ joinOperands c.vars d ca cb []) ++ finish (pre ++ joinOperands c.vars d ca cb []).length ++ post := by
    rw [hlen]; simpa using layout
  obtain ⟨s5, r5, p5, rax5, h5, m5⟩ := fin _ post s4 x y v lay5 (by rw [hlen, p4]) h4 rax4 rcx4 ev
  refine ⟨s5, r4.trans r5, ?_, rax5, h5, fun a ha => by rw [m5, m4 a ha]⟩
  rw [p5, hlen, joinOperands_append (finish := finish _)]
  show pc + ca.length + 1 + cb.length + 2 + fc.length = pc + (joinOperands c.vars d ca cb [] ++ fc).length
  simp only [joinOperands, List.length_append, List.length_cons, List.length_nil]; omega

/-- An integer operation combines rax and rcx into rax. -/
theorem finish_alu (c : Site) (env : Env) (ir : Memory) (o : Alu) :
    FinishOk c env ir (fun _ => [.alu o .rax .rcx]) (fun x y => some (aluResult o x y).1) := by
  intro pre post s x y z layout at_ holds hx hy hz
  simp only at layout ⊢
  simp only [Option.some.injEq] at hz; subst hz
  refine ⟨_, Reaches.one c.image c.routine pre post _ layout (by simp [Instr.straight]) s at_ holds.running,
    rfl, ?_, ?_, by simp [exec1]⟩
  · simp [exec1, assign, hx, hy]
  · exact holds.update .rax (by simp) (aluResult o x y).1 (by simp [exec1, hx, hy]) (by simp [exec1]) (by simp [exec1])
      (by simp [exec1])

/-- Clearing rdx and dividing by rcx leaves the quotient in rax and the remainder in rdx. -/
theorem divide_ok (c : Site) (env : Env) (ir : Memory) (pre post : List Instr) (s : State) (x y : UInt64)
    (layout : (c.image.code c.routine).toList = pre ++ [.zeroReg .rdx, .div .rcx] ++ post) (at_ : s.pc = pre.length)
    (holds : c.Holds env ir s) (hx : s.gpr .rax = x) (hy : s.gpr .rcx = y) (nz : y ≠ 0) :
    ∃ s', Reaches c.image c.routine s s' ∧ s'.pc = pre.length + 2 ∧ s'.gpr .rax = x / y ∧ s'.gpr .rdx = x % y ∧
      c.Holds env ir s' ∧ s'.mem = s.mem := by
  -- Clear the high half.
  have lay1 : (c.image.code c.routine).toList = pre ++ [.zeroReg .rdx] ++ (.div .rcx :: post) := by simpa using layout
  have r1 := Reaches.one c.image c.routine pre _ _ lay1 (by simp [Instr.straight]) s at_ holds.running
  let s1 := { exec1 (.zeroReg .rdx) s with pc := pre.length + 1 }
  have h1 : c.Holds env ir s1 :=
    holds.update .rdx (by simp) 0 (by simp [s1, exec1]) (by simp [s1, exec1]) (by simp [s1, exec1])
      (by simp [s1, exec1])
  -- Divide: the high half is zero, below any nonzero divisor.
  have lay2 : (c.image.code c.routine).toList = (pre ++ [.zeroReg .rdx]) ++ .div .rcx :: post := by simpa using layout
  have f2 := fetch_at c.image c.routine _ _ _ lay2
  have pos : 0 < y.toNat := Nat.pos_of_ne_zero fun h => nz (UInt64.toNat_inj.mp (by simpa using h))
  have r2 := Reaches.div c.image c.routine s1 .rcx (by simpa [s1] using f2)
    (by simp [s1, exec1, assign, hy, nz]) (by simp [s1, exec1, assign, hy, pos]) h1.running
  let s2 := { exec1 (.div .rcx) s1 with pc := s1.pc + 1 }
  have g2 : s2.gpr = assign (assign s.gpr .rax (x / y)) .rdx (x % y) := by
    funext r
    simp only [s2, s1, exec1, assign]
    split <;> split <;> simp_all <;> apply UInt64.toNat_inj.mp <;> simp <;>
      first
      | exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) x.toNat_lt
      | exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) x.toNat_lt
  have h2 : c.Holds env ir s2 :=
    ((holds.setGpr .rax (by simp) (x / y)).setGpr .rdx (by simp) (x % y)).congr g2 (by simp [s2, s1, exec1])
      (by simp [s2, s1, exec1]) (by simp [s2, s1, exec1])
  exact ⟨s2, r1.trans r2, by simp [s2, s1], by simp [g2, assign], by simp [g2, assign], h2, by simp [s2, s1, exec1]⟩

/-- A division leaves the quotient of rax by rcx in rax. -/
theorem finish_div (c : Site) (env : Env) (ir : Memory) :
    FinishOk c env ir (fun _ => [.zeroReg .rdx, .div .rcx]) (fun x y => if y == 0 then none else some (x / y)) := by
  intro pre post s x y z layout at_ holds hx hy hz
  simp only at layout ⊢
  by_cases nz : y = 0
  · simp [nz] at hz
  simp only [beq_iff_eq, nz, if_false, Option.some.injEq] at hz; subst hz
  obtain ⟨s', r, p, q, _, h, m⟩ := divide_ok c env ir pre post s x y (by simpa using layout) at_ holds hx hy nz
  exact ⟨s', r, by simp [p], q, h, m⟩

/-- A remainder moves what the division leaves in rdx into rax. -/
theorem finish_mod (c : Site) (env : Env) (ir : Memory) :
    FinishOk c env ir (fun _ => [.zeroReg .rdx, .div .rcx, .movReg .rax .rdx])
      (fun x y => if y == 0 then none else some (x % y)) := by
  intro pre post s x y z layout at_ holds hx hy hz
  simp only at layout ⊢
  by_cases nz : y = 0
  · simp [nz] at hz
  simp only [beq_iff_eq, nz, if_false, Option.some.injEq] at hz; subst hz
  obtain ⟨s2, r2, p2, _, rest, h2, m2⟩ :=
    divide_ok c env ir pre (.movReg .rax .rdx :: post) s x y (by simpa using layout) at_ holds hx hy nz
  have lay3 : (c.image.code c.routine).toList = (pre ++ [.zeroReg .rdx, .div .rcx]) ++ [.movReg .rax .rdx] ++ post := by
    simpa using layout
  have r3 := Reaches.one c.image c.routine _ _ _ lay3 (by simp [Instr.straight]) s2 (by simp [p2]) h2.running
  refine ⟨_, r2.trans r3, by simp, by simp [exec1, assign, rest], ?_, by simp [exec1, m2]⟩
  exact h2.update .rax (by simp) (x % y) (by simp [exec1, rest]) (by simp [exec1]) (by simp [exec1]) (by simp [exec1])

/-- The code a comparison ends with, placed at an index: compare, assume true, and clear when the condition fails. -/
def cmpFinish (c : Cond) (p : Nat) : List Instr :=
  [.cmp .rax .rcx, .movImm .rax 1, .jcc c (p + 4), .movImm .rax 0]

/-- A comparison leaves one in rax when its condition holds, and zero otherwise. -/
theorem finish_cmp (site : Site) (env : Env) (ir : Memory) (c : Cond) :
    FinishOk site env ir (cmpFinish c) (fun x y => some (if c.holds (x == y) (x < y) then 1 else 0)) := by
  intro pre post s x y z layout at_ holds hx hy hz
  simp only [Option.some.injEq] at hz; subst hz
  -- Compare, then assume the condition holds.
  have lay1 : (site.image.code site.routine).toList = pre ++ [.cmp .rax .rcx, .movImm .rax 1] ++
      ([.jcc c (pre.length + 4), .movImm .rax 0] ++ post) := by simpa [cmpFinish] using layout
  have r1 := Reaches.block site.image site.routine _ _ _ lay1 (by simp [Instr.straight]) s at_ holds.running
  let s1 := { Asm.exec [.cmp .rax .rcx, .movImm .rax 1] s with pc := pre.length + 2 }
  have g1 : s1.gpr = assign s.gpr .rax 1 := by simp [s1, Asm.exec, exec1]
  have h1 : site.Holds env ir s1 :=
    holds.update .rax (by simp) 1 g1 (by simp [s1, Asm.exec, exec1]) (by simp [s1, Asm.exec, exec1])
      (by simp [s1, Asm.exec, exec1])
  have flags : s1.zf = (x == y) ∧ s1.cf = decide (x < y) := by simp [s1, Asm.exec, exec1, hx, hy]
  -- The branch.
  have lay2 : (site.image.code site.routine).toList = (pre ++ [.cmp .rax .rcx, .movImm .rax 1]) ++
      .jcc c (pre.length + 4) :: ([.movImm .rax 0] ++ post) := by simpa [cmpFinish] using layout
  have r2 := Reaches.jcc site.image site.routine s1 c (pre.length + 4)
    (by simpa [s1] using fetch_at site.image site.routine _ _ _ lay2) h1.running
  by_cases holdsC : c.holds (x == y) (x < y) = true
  · -- Taken: one stays in rax.
    refine ⟨_, r1.trans r2, by simp [flags, holdsC, cmpFinish], ?_, ?_, ?_⟩
    · simp [g1, assign, holdsC]
    · exact h1.congr (by simp) (by simp) (by simp) (by simp)
    · simp [s1, Asm.exec, exec1]
  · -- Not taken: zero replaces it.
    have lay3 : (site.image.code site.routine).toList =
        (pre ++ [.cmp .rax .rcx, .movImm .rax 1, .jcc c (pre.length + 4)]) ++ [.movImm .rax 0] ++ post := by
      simpa [cmpFinish] using layout
    let s2 := { s1 with pc := pre.length + 3 }
    have r2' : Reaches site.image site.routine s1 s2 := by
      have : (if c.holds s1.zf s1.cf then pre.length + 4 else s1.pc + 1) = pre.length + 3 := by
        rw [flags.1, flags.2, if_neg holdsC]
      rw [this] at r2
      exact r2
    have h2 : site.Holds env ir s2 := h1.congr rfl rfl rfl rfl
    have r3 := Reaches.one site.image site.routine _ _ _ lay3 (by simp [Instr.straight]) s2 (by simp [s2])
      h2.running
    refine ⟨_, r1.trans (r2'.trans r3), by simp [cmpFinish], by simp [exec1, assign, holdsC], ?_, ?_⟩
    · exact h2.update .rax (by simp) 0 (by simp [exec1]) (by simp [exec1]) (by simp [exec1]) (by simp [exec1])
    · simp [exec1, s2, s1, Asm.exec]

/-- An expression's code computes its value, for every expression reading only the function's variables. -/
theorem expr_ok (c : Site) (fits : c.Fits) : ∀ e : Expr, e.varsBelow c.vars → ExprOk c e
  | .lit n, _ => lit_ok c n
  | .var x, h => var_ok c fits x (by simpa [Expr.varsBelow] using h)
  | .shl a k, h => shl_ok c a k (expr_ok c fits a (by simpa [Expr.varsBelow] using h))
  | .shr a k, h => shr_ok c a k (expr_ok c fits a (by simpa [Expr.varsBelow] using h))
  | .load w a, h => load_ok c a w (expr_ok c fits a (by simpa [Expr.varsBelow] using h))
  | .op o a b, h => by
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    intro d pc pre post env ir s v layout hpre hpc holds room ev
    exact binary_ok c fits a b (expr_ok c fits a h.1) (expr_ok c fits b h.2) _ _ env ir (finish_alu c env ir o)
      d pc pre post s v (by simpa [compileExpr] using layout) hpre hpc holds (by simpa [Expr.temps] using room)
      (by simpa [eval] using ev)
  | .div a b, h => by
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    intro d pc pre post env ir s v layout hpre hpc holds room ev
    exact binary_ok c fits a b (expr_ok c fits a h.1) (expr_ok c fits b h.2) _ _ env ir (finish_div c env ir)
      d pc pre post s v (by simpa [compileExpr] using layout) hpre hpc holds (by simpa [Expr.temps] using room)
      (by simpa [eval] using ev)
  | .mod a b, h => by
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    intro d pc pre post env ir s v layout hpre hpc holds room ev
    exact binary_ok c fits a b (expr_ok c fits a h.1) (expr_ok c fits b h.2) _ _ env ir (finish_mod c env ir)
      d pc pre post s v (by simpa [compileExpr] using layout) hpre hpc holds (by simpa [Expr.temps] using room)
      (by simpa [eval] using ev)
  | .cmp cc a b, h => by
    simp only [Expr.varsBelow, Bool.and_eq_true] at h
    intro d pc pre post env ir s v layout hpre hpc holds room ev
    have code : compileExpr c.vars pc (.cmp cc a b) d = joinOperands c.vars d (compileExpr c.vars pc a d)
        (compileExpr c.vars (pc + (compileExpr c.vars pc a d).length + 1) b (d + 1))
        (cmpFinish cc (pc + (compileExpr c.vars pc a d).length + 1 +
          (compileExpr c.vars (pc + (compileExpr c.vars pc a d).length + 1) b (d + 1)).length + 2)) := by
      simp only [compileExpr, joinOperands, cmpFinish]
      simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append, List.length_cons,
        List.length_nil, List.append_cancel_left_eq, List.cons.injEq, Instr.jcc.injEq, true_and, and_true]
      omega
    rw [code] at layout ⊢
    exact binary_ok c fits a b (expr_ok c fits a h.1) (expr_ok c fits b h.2) _ _ env ir (finish_cmp c env ir cc)
      d pc pre post s v layout hpre hpc holds (by simpa [Expr.temps] using room) (by simpa [eval] using ev)

end Ssz.Native.Ir
