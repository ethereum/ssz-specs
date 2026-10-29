import SszNative.Proofs.Ir.Stmt

/-!
A compiled function keeps the call contract, and so does every function of a module, at any depth of calls.

The entry builds the frame, the body and the result follow, and the exit releases the frame and pops the return.
-/

namespace Ssz.Native.Ir

open Ssz.Native.Asm

/-- Storing registers to consecutive slots: each slot holds its register, and nothing else in memory changes. -/
theorem slotStores_exec (base k : Nat) (hbase : base < 2 ^ 64) (reg : Nat → Gpr) (noRsp : ∀ i, reg i ≠ .rsp) :
    ∀ (n : Nat) (s : State), s.gpr .rsp = base.toUInt64 →
      (Asm.exec (slotStores k n reg) s).gpr = s.gpr ∧
      (∀ i < n, readLE (Asm.exec (slotStores k n reg) s).mem (base + 8 * (k + i)) 8 = s.gpr (reg i)) ∧
      (∀ a, (a < base + 8 * k ∨ base + 8 * (k + n) ≤ a) → (Asm.exec (slotStores k n reg) s).mem a = s.mem a) ∧
      (Asm.exec (slotStores k n reg) s).cpu = s.cpu ∧ (Asm.exec (slotStores k n reg) s).status = s.status
  | 0, s, _ => by simp [slotStores]
  | n + 1, s, rsp => by
    obtain ⟨g, vals, rest, cpu, st⟩ := slotStores_exec base k hbase reg noRsp n s rsp
    have split : slotStores k (n + 1) reg = slotStores k n reg ++ [.store .b8 (slot (k + n)) (reg n)] := by
      simp [slotStores, List.range_succ]
    rw [split, exec_append]
    generalize Asm.exec (slotStores k n reg) s = s1 at g vals rest cpu st ⊢
    have addr : s1.addr (slot (k + n)) = base + 8 * (k + n) := by
      simp [State.addr, slot, g, rsp, Nat.mod_eq_of_lt hbase]
    refine ⟨by simp [Asm.exec, exec1, g], fun i hi => ?_, fun a ha => ?_, by simp [Asm.exec, exec1, cpu],
      by simp [Asm.exec, exec1, st]⟩
    · simp only [Asm.exec, exec1, addr, Width.bytes]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
      · rw [← vals i h]
        apply readLE_congr
        intro j hj
        simp only [store]
        rw [if_neg (by omega)]
      · subst h; rw [readLE_store8, g]
    · simp only [Asm.exec, exec1, addr, store, Width.bytes]
      rw [if_neg (by omega), rest a (by omega)]

/-- Whether an instruction needs no instruction set extension. -/
def Instr.baseline (i : Instr) : Bool := i.features.isEmpty

/-- The compiled code of an expression needs no instruction set extension. -/
theorem compileExpr_baseline (vars : Nat) : ∀ (e : Expr) (pc d : Nat), (compileExpr vars pc e d).all Instr.baseline
  | .lit _, _, _ | .var _, _, _ => by simp [compileExpr, Instr.baseline, Instr.features]
  | .shl a _, pc, d | .shr a _, pc, d | .load _ a, pc, d => by
    simp [compileExpr, Instr.baseline, Instr.features, compileExpr_baseline vars a pc d]
  | .op _ a b, pc, d | .div a b, pc, d | .mod a b, pc, d | .cmp _ a b, pc, d => by
    simp [compileExpr, joinOperands, Instr.baseline, Instr.features, compileExpr_baseline vars a pc d,
      compileExpr_baseline vars b _ (d + 1)]

/-- The compiled code of call arguments needs no instruction set extension. -/
theorem compileArgs_baseline (vars : Nat) : ∀ (args : List Expr) (pc i : Nat),
    (compileArgs vars pc args i).all Instr.baseline
  | [], _, _ => by simp [compileArgs]
  | a :: rest, pc, i => by
    simp [compileArgs, Instr.baseline, Instr.features, compileExpr_baseline vars a pc i,
      compileArgs_baseline vars rest _ (i + 1)]

/-- The compiled code of a statement needs no instruction set extension. -/
theorem compileStmt_baseline (vars : Nat) : ∀ (stmt : Stmt) (pc : Nat), (compileStmt vars pc stmt).all Instr.baseline
  | .skip, _ => by simp [compileStmt]
  | .set _ e, pc => by simp [compileStmt, Instr.baseline, Instr.features, compileExpr_baseline vars e pc 0]
  | .store _ a v, pc => by
    simp [compileStmt, Instr.baseline, Instr.features, compileExpr_baseline vars a pc 0,
      compileExpr_baseline vars v _ 1]
  | .seq a b, pc => by simp [compileStmt, compileStmt_baseline vars a pc, compileStmt_baseline vars b _]
  | .ite c t e, pc => by
    simp [compileStmt, Instr.baseline, Instr.features, compileExpr_baseline vars c pc 0, compileStmt_baseline vars t _,
      compileStmt_baseline vars e _]
  | .loop c body, pc => by
    simp [compileStmt, Instr.baseline, Instr.features, compileExpr_baseline vars c pc 0,
      compileStmt_baseline vars body _]
  | .call _ args _, pc => by
    simp [compileStmt, argLoads, Instr.baseline, Instr.features, compileArgs_baseline vars args pc 0]

/-- Code needing no extension runs on every processor. -/
theorem runs_of_baseline (cpu : Cpu) (code : List Instr) (h : code.all Instr.baseline) :
    code.all (fun i => i.features.all cpu.has) := by
  simp only [List.all_eq_true, Instr.baseline, List.isEmpty_iff] at h ⊢
  intro i hi; simp [h i hi]

/-- A compiled function runs on every processor. -/
theorem compileFn_runs (cpu : Cpu) (f : Fn) : cpu.runs (compileFn f) := by
  have pro : (prologue f).all Instr.baseline := by simp [prologue, slotStores, Instr.baseline, Instr.features]
  have body := compileStmt_baseline f.vars f.body (prologue f).length
  have result := compileExpr_baseline f.vars f.result
    ((prologue f).length + (compileStmt f.vars (prologue f).length f.body).length) 0
  simp only [Cpu.runs, compileFn, List.toList_toArray, List.all_append, runs_of_baseline cpu _ pro,
    runs_of_baseline cpu _ body, runs_of_baseline cpu _ result, Bool.true_and]
  simp [Instr.features]

/-- A subtraction of words that does not go below zero. -/
theorem toUInt64_sub (a b : Nat) (hb : b ≤ a) : a.toUInt64 - b.toUInt64 = (a - b).toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_sub]
  omega

/-- An addition of words that does not wrap. -/
theorem toUInt64_add (a b : Nat) (h : a + b < 2 ^ 64) : a.toUInt64 + b.toUInt64 = (a + b).toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_add, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)]

/-- A return address reads back as its routine and its instruction. -/
theorem codeAddress_toNat (r i : Nat) (hr : r < 2 ^ 31) (hi : i < 2 ^ 32) :
    (codeAddress r i).toNat = r * 2 ^ 32 + i := by
  simp [codeAddress]
  omega

/-- A call to a routine of the image pushes the return address and enters the routine. -/
theorem image_step_call (image : Image) (r : Nat) (s : State) (name : String) (t : Nat)
    (fetch : (image.code r)[s.pc]? = some (.call name)) (running : s.status = .running)
    (find : image.find name = some t) (runs : s.cpu.runs (image.code t)) :
    image.step ⟨r, s⟩ = ⟨t, { s with
      gpr := assign s.gpr .rsp (s.gpr .rsp - 8)
      mem := store s.mem (s.gpr .rsp - 8).toNat 8 (qwordByte (codeAddress r (s.pc + 1)))
      pc := 0 }⟩ := by
  simp [Image.step, running, fetch, find, runs]

/-- A return pops the address the call pushed and resumes the caller. -/
theorem image_step_ret (image : Image) (t : Nat) (s : State) (fetch : (image.code t)[s.pc]? = some .ret)
    (running : s.status = .running) (back : Nat) (hback : (readLE s.mem (s.gpr .rsp).toNat 8).toNat = back)
    (inside : back / 2 ^ 32 < image.size) :
    image.step ⟨t, s⟩ = ⟨back / 2 ^ 32, { s with gpr := assign s.gpr .rsp (s.gpr .rsp + 8), pc := back % 2 ^ 32 }⟩ := by
  simp [Image.step, running, fetch, hback, inside]

/-- A frame holds the variables and every temporary the body and result need. -/
theorem frame_room (f : Fn) : f.vars + max f.body.temps f.result.temps ≤ f.frame := by
  simp only [Fn.frame]; split <;> omega

/--
A compiled function computes its meaning: the call contract holds for it, with some fuel.

The calls its body makes must hold their contracts with less fuel.
-/
theorem fn_ok (m : Module) (image : Image) (w : World) (name : String) (f : Fn) (t fuel : Nat)
    (lookup : m.fns.lookup name = some f) (find : image.find name = some t) (code : image.code t = compileFn f)
    (tIn : t < image.size) (tSmall : t < 2 ^ 31) (size : (compileFn f).size < 2 ^ 32) (wf : f.wf)
    (calls : ∀ j < fuel, ∀ name, CallOk image w name (callSpec m w j name)) :
    CallOk image w name (callSpec m w fuel name) := by
  intro r s sp args ir ir' res fetch running cpu rIn rSmall pcSmall rsp spHi hiBound few argRegs heap spec
  simp only [Fn.wf, Bool.and_eq_true, decide_eq_true_eq] at wf
  obtain ⟨⟨⟨p6, pv⟩, wfBody⟩, wfRes⟩ := wf
  -- What the call means.
  simp only [callSpec, lookup, bind, Option.bind] at spec
  split at spec
  rotate_left
  · simp at spec
  rename_i room
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at room
  obtain ⟨room, nparams⟩ := room
  cases eb : exec m w fuel (sp - 8 - 8 * f.frame) (entryEnv args) ir f.body with
  | none => simp [eb] at spec
  | some p =>
  obtain ⟨env', mem'⟩ := p
  simp only [eb] at spec
  cases er : eval w env' mem' f.result with
  | none => simp [er] at spec
  | some v =>
  simp only [er, pure, Option.some.injEq, Prod.mk.injEq] at spec
  obtain ⟨rfl, rfl⟩ := spec
  have spBound : sp ≤ 2 ^ 63 := by simp [addressBound] at hiBound; omega
  obtain ⟨base, hbase⟩ : ∃ b, b = sp - 8 - 8 * f.frame := ⟨_, rfl⟩
  let back := codeAddress r (s.pc + 1)
  -- The call: the return address below the caller's stack pointer.
  have runs := compileFn_runs s.cpu f
  rw [← code] at runs
  have step0 := image_step_call image r s name t fetch running find runs
  have top : s.gpr .rsp - 8 = (sp - 8).toUInt64 := by
    rw [rsp, show (8 : UInt64) = (8 : Nat).toUInt64 from rfl, toUInt64_sub _ _ (by omega)]
  have topNat : (sp - 8).toUInt64.toNat = sp - 8 := by simp; omega
  rw [top, topNat] at step0
  let s0 : State := { s with
    gpr := assign s.gpr .rsp (sp - 8).toUInt64
    mem := store s.mem (sp - 8) 8 (qwordByte back)
    pc := 0 }
  -- The callee's site.
  let c : Site := ⟨image, t, w, base, f.vars, f.frame, s.gpr⟩
  have cbase : c.base = base := rfl
  have cvars : c.vars = f.vars := rfl
  have cframe : c.frame = f.frame := rfl
  have cw : c.w = w := rfl
  have fits : c.Fits := ⟨show w.stackLo ≤ base by omega, show base + 8 * f.frame ≤ w.stackHi by omega, hiBound,
    show f.vars ≤ f.frame by have := frame_room f; omega, ⟨tIn, tSmall⟩,
    show (image.code t).size < 2 ^ 32 by rw [code]; exact size⟩
  have baseBound : base < 2 ^ 64 := by omega
  -- The prologue.
  have layoutP : (image.code t).toList = [] ++ prologue f ++
      (compileStmt f.vars (prologue f).length f.body ++ compileExpr f.vars ((prologue f).length +
        (compileStmt f.vars (prologue f).length f.body).length) f.result 0 ++
        [Instr.addImm .rsp (8 * f.frame), Instr.ret]) := by
    rw [code]; simp [compileFn]
  have straightP : ∀ i ∈ prologue f, i.straight := by
    rw [← List.all_eq_true]
    simp [prologue, slotStores, List.all_map, Function.comp_def, Instr.straight]
  have rP := Reaches.block image t [] (prologue f) _ layoutP straightP s0 rfl (by simp [s0, running])
  -- Its four parts, one after the other.
  have splitP : Asm.exec (prologue f) s0 = Asm.exec (slotStores f.params (f.vars - f.params) (fun _ => .rax))
      (Asm.exec [.zeroReg .rax] (Asm.exec (slotStores 0 f.params argReg) (Asm.exec [.subImm .rsp (8 * f.frame)] s0))) := by
    simp only [prologue, exec_append]
  generalize hA : Asm.exec [.subImm .rsp (8 * f.frame)] s0 = sA at splitP
  have rspA : sA.gpr .rsp = base.toUInt64 := by
    rw [← hA]; simp only [Asm.exec, exec1, assign, if_true, s0]
    rw [show ((8 * f.frame : Nat)).toUInt64 = (8 * f.frame).toUInt64 from rfl, toUInt64_sub _ _ (by omega), hbase,
      Nat.sub_sub]
  have gprA : ∀ g, g ≠ .rsp → sA.gpr g = s.gpr g := by
    intro g hg; rw [← hA]; simp [Asm.exec, exec1, assign, s0, hg]
  have memA : sA.mem = s0.mem := by rw [← hA]; simp [Asm.exec, exec1]
  have restA : sA.cpu = s.cpu ∧ sA.status = s.status := by rw [← hA]; simp [Asm.exec, exec1, s0]
  obtain ⟨gB, valsB, restB, cpuB, stB⟩ := slotStores_exec base 0 baseBound argReg (by
    intro i h; have := argReg_scratch i; rw [h] at this; simp at this) f.params sA rspA
  generalize hB : Asm.exec (slotStores 0 f.params argReg) sA = sB at splitP gB valsB restB cpuB stB
  generalize hC : Asm.exec [.zeroReg .rax] sB = sC at splitP
  have gC : sC.gpr = assign sB.gpr .rax 0 := by rw [← hC]; simp [Asm.exec, exec1]
  have memC : sC.mem = sB.mem := by rw [← hC]; simp [Asm.exec, exec1]
  have restC : sC.cpu = sB.cpu ∧ sC.status = sB.status := by rw [← hC]; simp [Asm.exec, exec1]
  have rspC : sC.gpr .rsp = base.toUInt64 := by simp [gC, assign, gB, rspA]
  obtain ⟨gD, valsD, restD, cpuD, stD⟩ := slotStores_exec base f.params baseBound (fun _ => .rax) (by simp)
    (f.vars - f.params) sC rspC
  rw [splitP] at rP
  generalize Asm.exec (slotStores f.params (f.vars - f.params) (fun _ => .rax)) sC = sD at gD valsD restD cpuD stD rP
  let s1 : State := { sD with pc := ([] : List Instr).length + (prologue f).length }
  have h1 : c.Holds (entryEnv args) ir s1 := by
    refine ⟨by simp [s1, gD, rspC, cbase], fun x hx => ?_, fun a ha => ?_, ?_, ?_, fun g hg => ?_⟩
    · rw [cvars] at hx
      show readLE sD.mem (base + 8 * x) 8 = args.getD x 0
      by_cases below : x < f.params
      · rw [readLE_congr sD.mem sB.mem (base + 8 * x) 8 (fun k hk => by rw [restD _ (by omega), memC])]
        rw [show base + 8 * x = base + 8 * (0 + x) by simp, valsB x below, gprA _ (by
          intro h; have := argReg_scratch x; rw [h] at this; simp at this)]
        exact argRegs x (by omega)
      · have := valsD (x - f.params) (by omega)
        rw [show f.params + (x - f.params) = x by omega] at this
        have long : args.length ≤ x := by omega
        rw [this, gC]
        simp [assign, List.getElem?_eq_none long]
    · show sD.mem a = ir a
      rw [cw] at ha
      have := frame_room f
      rw [restD a (by omega), memC, restB a (by omega), memA]
      simp only [s0, store]
      rw [if_neg (by omega)]
      exact heap a ha
    · simp [s1, cpuD, restC, cpuB, restA, cpu, c]
    · simp [s1, stD, restC, stB, restA, running]
    · simp only [s1, gD, gC, gB, c]
      simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hg
      rw [assign, if_neg (by rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp),
        gprA g (by rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)]
  -- What the prologue left below the return address and off the stack.
  have frameRoom := frame_room f
  have stack1 : ∀ a, base + 8 * f.frame ≤ a → s1.mem a = s0.mem a := by
    intro a ha
    show sD.mem a = s0.mem a
    rw [restD a (by omega), memC, restB a (by omega), memA]
  -- The body.
  let pro := prologue f
  let bodyCode := compileStmt f.vars pro.length f.body
  let resCode := compileExpr f.vars (pro.length + bodyCode.length) f.result 0
  have layoutB : (image.code t).toList = pro ++ bodyCode ++ (resCode ++ [Instr.addImm .rsp (8 * f.frame), Instr.ret]) := by
    rw [code]; simp [compileFn, pro, bodyCode, resCode]
  have bodyOk := stmt_ok m c fits fuel (fun j hj name => calls j hj name) fuel (Nat.le_refl _) f.body wfBody
  obtain ⟨s2, rB, pB, h2, m2⟩ := bodyOk pro.length pro _ (entryEnv args) ir s1 env' mem' layoutB rfl
    (by simp [s1, pro]) h1 (by rw [cvars, cframe]; omega) (by rw [cw, cbase, hbase]; exact eb)
  -- The result.
  have layoutR : (image.code t).toList = (pro ++ bodyCode) ++ resCode ++ [Instr.addImm .rsp (8 * f.frame), Instr.ret] := by
    simpa using layoutB
  obtain ⟨s3, rE, pE, rax3, h3, m3⟩ := expr_ok c fits f.result (by rw [cvars]; exact wfRes) 0
    (pro.length + bodyCode.length) (pro ++ bodyCode) _ env' mem' s2 v layoutR (by simp) (by rw [pB])
    h2 (by rw [cvars, cframe]; omega) (by rw [cw]; exact er)
  -- The frame released.
  have layoutA : (image.code t).toList = (pro ++ bodyCode ++ resCode) ++ [Instr.addImm .rsp (8 * f.frame)] ++
      [Instr.ret] := by simpa using layoutR
  have rA := Reaches.one image t _ _ _ layoutA (by simp [Instr.straight]) s3
    (by rw [pE, cvars]; simp [resCode]; omega) h3.running
  let s4 := { exec1 (.addImm .rsp (8 * f.frame)) s3 with pc := (pro ++ bodyCode ++ resCode).length + 1 }
  have rsp4 : s4.gpr .rsp = (sp - 8).toUInt64 := by
    simp only [s4, exec1, assign, if_true]
    rw [h3.rsp, cbase, toUInt64_add _ _ (by omega)]
    congr 1; omega
  have gpr4 : ∀ g, g ≠ .rsp → s4.gpr g = s3.gpr g := by intro g hg; simp [s4, exec1, assign, hg]
  have mem4 : s4.mem = s3.mem := by simp [s4, exec1]
  -- The return address, untouched since the call.
  have backNat : (back).toNat = r * 2 ^ 32 + (s.pc + 1) := codeAddress_toNat r (s.pc + 1) rSmall pcSmall
  have readBack : (readLE s4.mem (s4.gpr .rsp).toNat 8).toNat = r * 2 ^ 32 + (s.pc + 1) := by
    rw [rsp4, topNat, mem4]
    rw [readLE_congr s3.mem s0.mem (sp - 8) 8 (fun k hk => by
      rw [m3 _ (Or.inr (by rw [cbase, cframe]; omega)), m2 _ (by rw [cbase, cframe]; omega) (by rw [cw]; omega),
        stack1 _ (by omega)])]
    simp only [s0, readLE_store8, backNat]
  have fetchRet : (image.code t)[s4.pc]? = some .ret := by
    have := fetch_at image t (pro ++ bodyCode ++ resCode ++ [Instr.addImm .rsp (8 * f.frame)]) [] .ret
      (by simpa using layoutA)
    have at4 : s4.pc = (pro ++ bodyCode ++ resCode ++ [Instr.addImm .rsp (8 * f.frame)]).length := by
      simp [s4]; omega
    rw [at4]; exact this
  have stepRet := image_step_ret image t s4 fetchRet (by simp [s4, h3.running]) _ readBack
    (by rw [show (r * 2 ^ 32 + (s.pc + 1)) / 2 ^ 32 = r by omega]; exact rIn)
  rw [show (r * 2 ^ 32 + (s.pc + 1)) / 2 ^ 32 = r by omega,
    show (r * 2 ^ 32 + (s.pc + 1)) % 2 ^ 32 = s.pc + 1 by omega] at stepRet
  -- The whole run: the call, the callee's code, and the return.
  obtain ⟨k, hk⟩ := rP.trans (rB.trans (rE.trans rA))
  refine ⟨{ s4 with gpr := assign s4.gpr .rsp (s4.gpr .rsp + 8), pc := s.pc + 1 }, ⟨1 + k + 1, ?_⟩, rfl, ?_, ?_,
    fun g hg => ?_, fun a ha => ?_, fun a lo hi => ?_, ?_, ?_⟩
  · rw [Image.run_add, Image.run_add]
    simp only [Image.run]
    rw [step0]
    exact (congrArg (fun m => image.step m) hk).trans stepRet
  · simp [assign, gpr4 .rax (by simp), rax3]
  · simp only [assign, if_true]
    rw [rsp4, show (8 : UInt64) = (8 : Nat).toUInt64 from rfl, toUInt64_add _ _ (by omega)]
    congr 1; omega
  · have ne : g ≠ .rsp := by
      simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    simp only [assign, if_neg ne]; rw [gpr4 g ne, h3.kept g hg]
  · simp only; rw [mem4]; exact h3.heap a (by rw [cw]; exact ha)
  · simp only; rw [mem4, m3 a (Or.inr (by rw [cbase, cframe]; omega)), m2 a (by rw [cbase, cframe]; omega) (by rw [cw]; exact hi),
      stack1 a (by omega)]
    simp only [s0, store]; rw [if_neg (by omega)]
  · simp [s4, exec1, h3.cpu, cw, cpu]
  · simp [s4, exec1, h3.running]

end Ssz.Native.Ir

namespace Ssz.Native.Ir

open Ssz.Native.Asm

/-- What a routine outside the language must guarantee: its call contract, for its meaning. -/
def ExternOk (image : Image) (w : World) (name : String) (e : Extern) : Prop :=
  CallOk image w name fun sp args mem => if w.stackLo + 8 ≤ sp then e.run w sp args mem else none

/-- Where each function of a module sits in an image, compiled, and ready for the proof. -/
def Placed (m : Module) (image : Image) : Prop :=
  ∀ name f, m.fns.lookup name = some f → ∃ t, image.find name = some t ∧ image.code t = compileFn f ∧
    t < image.size ∧ t < 2 ^ 31 ∧ (compileFn f).size < 2 ^ 32 ∧ f.wf

/--
Every call to a module compiled into an image computes its meaning, with any fuel.

The routines outside the language must keep their own contracts.
-/
theorem module_ok (m : Module) (image : Image) (w : World) (placed : Placed m image)
    (externs : ∀ name e, m.fns.lookup name = none → m.ext.lookup name = some e → ExternOk image w name e) :
    ∀ fuel name, CallOk image w name (callSpec m w fuel name) := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel ih =>
    intro name
    cases hf : m.fns.lookup name with
    | some f =>
      obtain ⟨t, find, code, tIn, tSmall, size, wf⟩ := placed name f hf
      exact fn_ok m image w name f t fuel hf find code tIn tSmall size wf (fun j hj => ih j hj)
    | none =>
      cases he : m.ext.lookup name with
      | some e =>
        have := externs name e hf he
        intro r s sp args ir ir' res fetch running cpu rIn rSmall pcSmall rsp spHi hiBound few argRegs heap spec
        exact this r s sp args ir ir' res fetch running cpu rIn rSmall pcSmall rsp spHi hiBound few argRegs heap
          (by simpa [callSpec, hf, he] using spec)
      | none =>
        intro r s sp args ir ir' res _ _ _ _ _ _ _ _ _ _ _ _ spec
        simp [callSpec, hf, he] at spec

end Ssz.Native.Ir
