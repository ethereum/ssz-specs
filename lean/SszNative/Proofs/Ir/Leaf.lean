import SszNative.Proofs.Ir.Fn

/-!
Routines written by hand, proved run alone, keep the call contract inside the image.

Such a routine calls nothing, so it runs inside the image as it runs alone, up to the return that pops its caller's address.
-/

namespace EthLib.Consensus.Ssz.Native.Ir

open EthLib.Consensus.Ssz.Native.Asm

/--
What a routine that calls nothing must guarantee when run alone, from its first instruction, for an extern meaning.

It returns with the result in rax, the stack pointer and kept registers as on entry, memory off the stack as the
meaning says, and the stack from the return address up untouched.
The meaning is only ever given on processors that run the routine.
-/
def LeafOk (w : World) (code : Array Instr) (e : Extern) : Prop :=
  ∀ (s : State) (sp : Nat) (args : List UInt64) (ir ir' : Memory) (res : UInt64),
    s.pc = 0 → s.status = .running → s.cpu = w.cpu →
    s.gpr .rsp = (sp - 8).toUInt64 → w.stackLo + 8 ≤ sp → sp ≤ w.stackHi → w.stackHi ≤ addressBound →
    args.length ≤ 6 → (∀ i < args.length, s.gpr (argReg i) = args.getD i 0) →
    (∀ a, a < w.stackLo ∨ w.stackHi ≤ a → s.mem a = ir a) →
    e.run w sp args ir = some (res, ir') →
    w.cpu.runs code ∧ ∃ n, (run code n s).status = .returned ∧ (run code n s).gpr .rax = res ∧
      (run code n s).gpr .rsp = s.gpr .rsp ∧ (∀ g ∈ keptRegs, (run code n s).gpr g = s.gpr g) ∧
      (∀ a, a < w.stackLo ∨ w.stackHi ≤ a → (run code n s).mem a = ir' a) ∧
      (∀ a, sp - 8 ≤ a → a < w.stackHi → (run code n s).mem a = s.mem a) ∧ (run code n s).cpu = s.cpu

/-- A routine that calls nothing and keeps its alone guarantee keeps its call contract inside the image. -/
theorem extern_of_leaf (image : Image) (w : World) (name : String) (t : Nat) (e : Extern)
    (find : image.find name = some t) (leaf : Leaf (image.code t)) (ok : LeafOk w (image.code t) e) :
    ExternOk image w name e := by
  intro r s sp args ir ir' res fetch running cpu rIn rSmall pcSmall rsp spHi hiBound few argRegs heap spec
  by_cases room : w.stackLo + 8 ≤ sp
  rotate_left
  · simp [room] at spec
  simp only [room, ite_true] at spec
  have spBound : sp ≤ 2 ^ 63 := by simp [addressBound] at hiBound; omega
  let back := codeAddress r (s.pc + 1)
  -- The call: the return address below the caller's stack pointer.
  have top : s.gpr .rsp - 8 = (sp - 8).toUInt64 := by
    rw [rsp, show (8 : UInt64) = (8 : Nat).toUInt64 from rfl, toUInt64_sub _ _ (by omega)]
  have topNat : (sp - 8).toUInt64.toNat = sp - 8 := by simp; omega
  let s0 : State := { s with
    gpr := assign s.gpr .rsp (sp - 8).toUInt64
    mem := store s.mem (sp - 8) 8 (qwordByte back)
    pc := 0 }
  obtain ⟨runs, n, ret, rax, rspN, kept, heapN, stackN, cpuN⟩ := ok s0 sp args ir ir' res rfl (by simp [s0, running])
    (by simp [s0, cpu]) (by simp [s0, assign]) room spHi hiBound few
    (fun i hi => by
      have ne : argReg i ≠ .rsp := by intro h; have := argReg_scratch i; rw [h] at this; simp at this
      simp [s0, assign, ne, argRegs i hi])
    (fun a ha => by simp only [s0, store]; rw [ite_eq_right (by omega)]; exact heap a ha) spec
  have step0 := image_step_call image r s name t fetch running find (by rw [cpu]; exact runs)
  rw [top, topNat] at step0
  -- The routine alone, lifted into the image up to its return.
  obtain ⟨k, reach, atRet⟩ := lift_return image t leaf n s0 (by simp [s0, running]) ret
  generalize hf : run (image.code t) n s0 = f at reach atRet rax rspN kept heapN stackN cpuN
  -- The return pops the address the call pushed.
  have backNat : back.toNat = r * 2 ^ 32 + (s.pc + 1) := codeAddress_toNat r (s.pc + 1) rSmall pcSmall
  have readBack : (readLE ({ f with status := .running } : State).mem
      (({ f with status := .running } : State).gpr .rsp).toNat 8).toNat = r * 2 ^ 32 + (s.pc + 1) := by
    simp only
    rw [rspN, show s0.gpr .rsp = (sp - 8).toUInt64 by simp [s0, assign], topNat]
    rw [readLE_congr f.mem s0.mem (sp - 8) 8 (fun k hk => stackN _ (by omega) (by omega))]
    simp only [s0, readLE_store8, backNat]
  have stepRet := image_step_ret image t { f with status := .running } atRet rfl _ readBack
    (by rw [show (r * 2 ^ 32 + (s.pc + 1)) / 2 ^ 32 = r by omega]; exact rIn)
  rw [show (r * 2 ^ 32 + (s.pc + 1)) / 2 ^ 32 = r by omega,
    show (r * 2 ^ 32 + (s.pc + 1)) % 2 ^ 32 = s.pc + 1 by omega] at stepRet
  have rspF : f.gpr .rsp = (sp - 8).toUInt64 := by rw [rspN]; simp [s0, assign]
  refine ⟨{ f with status := .running, gpr := assign f.gpr .rsp (f.gpr .rsp + 8), pc := s.pc + 1 }, ⟨1 + k + 1, ?_⟩,
    rfl, ?_, ?_, fun g hg => ?_, fun a ha => ?_, fun a lo hi => ?_, ?_, rfl⟩
  · rw [Image.run_add, Image.run_add]
    simp only [Image.run]
    rw [step0]
    exact (congrArg (fun m => image.step m) reach).trans stepRet
  · have ne : Gpr.rax ≠ .rsp := by simp
    simp [assign, ne, rax]
  · simp only [assign, ite_true]
    rw [rspF, show (8 : UInt64) = (8 : Nat).toUInt64 from rfl, toUInt64_add _ _ (by omega)]
    congr 1; omega
  · have ne : g ≠ .rsp := by
      simp only [keptRegs, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    simp only [assign, ite_eq_right ne]; rw [kept g hg]; simp [s0, assign, ne]
  · exact heapN a ha
  · simp only; rw [stackN a (by omega) hi]; simp only [s0, store]; rw [ite_eq_right (by omega)]
  · simp [cpuN, s0]

end EthLib.Consensus.Ssz.Native.Ir
