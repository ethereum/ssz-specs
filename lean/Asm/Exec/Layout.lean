import Asm.Flow
import Asm.Exec.Code
import Asm.Sha256.Length
import Asm.Merkle.Layout

/-! Where each piece of the executor sits, so that a branch target names the code it lands on. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Exec

open Ssz.Asm.Sha256 (pairCode)

theorem entryCode_length : entryCode.length = 18 := rfl
theorem stepHeadCode_length (x y : Nat) : (stepHeadCode x y).length = 15 := rfl
theorem chunkStartCode_length : chunkStartCode.length = 1 := rfl
theorem chunkByteCode_length (x y z : Nat) : (chunkByteCode x y z).length = 10 := rfl
theorem hashCode_length : hashCode.length = 5092 := by
  simp [hashCode, Sha256.pairCode_length]
theorem nextCode_length (x : Nat) : (nextCode x).length = 4 := rfl
theorem finishCode_length : finishCode.length = 15 := rfl

/-- The program as one list, the pieces in order. -/
def programList : List Instr :=
  entryCode ++ (stepHeadCode finish hashStart ++ (chunkStartCode ++ (chunkByteCode next store chunkLoop ++
    (hashCode ++ (nextCode stepHead ++ finishCode)))))

theorem program_eq : program = programList.toArray := by
  simp only [program, programList, List.append_assoc]

theorem fetch {before code after : List Instr} {start k : Nat} (at_start : before.length = start)
    (whole : programList = before ++ (code ++ after)) (within : k < code.length) :
    program[start + k]? = some code[k] := by
  rw [program_eq, whole, ← at_start, ← List.append_assoc]
  exact here_of_append within

theorem length_before_stepHead : (entryCode).length = stepHead := by
  rw [entryCode_length]
  rfl

theorem split_at_stepHead : programList = (entryCode) ++ (stepHeadCode finish hashStart ++ (chunkStartCode ++ (chunkByteCode next store chunkLoop ++ (hashCode ++ (nextCode stepHead ++ (finishCode)))))) := by
  simp only [programList, List.append_assoc, List.append_nil]

theorem fetch_stepHead {k : Nat} (within : k < (stepHeadCode finish hashStart).length) :
    program[stepHead + k]? = some (stepHeadCode finish hashStart)[k] :=
  fetch length_before_stepHead split_at_stepHead within

theorem length_before_chunkStart : ((entryCode) ++ stepHeadCode finish hashStart).length = chunkStart := by
  rw [List.length_append, length_before_stepHead, stepHeadCode_length]
  rfl

theorem split_at_chunkStart : programList = ((entryCode) ++ stepHeadCode finish hashStart) ++ (chunkStartCode ++ (chunkByteCode next store chunkLoop ++ (hashCode ++ (nextCode stepHead ++ (finishCode))))) := by
  simp only [programList, List.append_assoc, List.append_nil]

theorem fetch_chunkStart {k : Nat} (within : k < (chunkStartCode).length) :
    program[chunkStart + k]? = some (chunkStartCode)[k] :=
  fetch length_before_chunkStart split_at_chunkStart within

theorem length_before_chunkLoop : (((entryCode) ++ stepHeadCode finish hashStart) ++ chunkStartCode).length = chunkLoop := by
  rw [List.length_append, length_before_chunkStart, chunkStartCode_length]
  rfl

theorem split_at_chunkLoop : programList = (((entryCode) ++ stepHeadCode finish hashStart) ++ chunkStartCode) ++ (chunkByteCode next store chunkLoop ++ (hashCode ++ (nextCode stepHead ++ (finishCode)))) := by
  simp only [programList, List.append_assoc, List.append_nil]

theorem fetch_chunkLoop {k : Nat} (within : k < (chunkByteCode next store chunkLoop).length) :
    program[chunkLoop + k]? = some (chunkByteCode next store chunkLoop)[k] :=
  fetch length_before_chunkLoop split_at_chunkLoop within

theorem length_before_hashStart : ((((entryCode) ++ stepHeadCode finish hashStart) ++ chunkStartCode) ++ chunkByteCode next store chunkLoop).length = hashStart := by
  rw [List.length_append, length_before_chunkLoop, chunkByteCode_length]
  rfl

theorem split_at_hashStart : programList = ((((entryCode) ++ stepHeadCode finish hashStart) ++ chunkStartCode) ++ chunkByteCode next store chunkLoop) ++ (hashCode ++ (nextCode stepHead ++ (finishCode))) := by
  simp only [programList, List.append_assoc, List.append_nil]

theorem fetch_hashStart {k : Nat} (within : k < (hashCode).length) :
    program[hashStart + k]? = some (hashCode)[k] :=
  fetch length_before_hashStart split_at_hashStart within

theorem length_before_next : (((((entryCode) ++ stepHeadCode finish hashStart) ++ chunkStartCode) ++ chunkByteCode next store chunkLoop) ++ hashCode).length = next := by
  rw [List.length_append, length_before_hashStart, hashCode_length]
  rfl

theorem split_at_next : programList = (((((entryCode) ++ stepHeadCode finish hashStart) ++ chunkStartCode) ++ chunkByteCode next store chunkLoop) ++ hashCode) ++ (nextCode stepHead ++ (finishCode)) := by
  simp only [programList, List.append_assoc, List.append_nil]

theorem fetch_next {k : Nat} (within : k < (nextCode stepHead).length) :
    program[next + k]? = some (nextCode stepHead)[k] :=
  fetch length_before_next split_at_next within

theorem length_before_finish : ((((((entryCode) ++ stepHeadCode finish hashStart) ++ chunkStartCode) ++ chunkByteCode next store chunkLoop) ++ hashCode) ++ nextCode stepHead).length = finish := by
  rw [List.length_append, length_before_next, nextCode_length]
  rfl

theorem split_at_finish : programList = ((((((entryCode) ++ stepHeadCode finish hashStart) ++ chunkStartCode) ++ chunkByteCode next store chunkLoop) ++ hashCode) ++ nextCode stepHead) ++ (finishCode ++ ([])) := by
  simp only [programList, List.append_assoc, List.append_nil]

theorem fetch_finish {k : Nat} (within : k < (finishCode).length) :
    program[finish + k]? = some (finishCode)[k] :=
  fetch length_before_finish split_at_finish within

theorem fetch_entry {k : Nat} (within : k < entryCode.length) : program[0 + k]? = some entryCode[k] :=
  fetch (before := []) (after := stepHeadCode finish hashStart ++ (chunkStartCode ++
      (chunkByteCode next store chunkLoop ++ (hashCode ++ (nextCode stepHead ++ finishCode)))))
    rfl (by simp only [programList, List.nil_append]) within

/-- A run of instructions taken from inside a piece. -/
theorem fetch_slice {start : Nat} {code : List Instr}
    (whole : ∀ k (within : k < code.length), program[start + k]? = some code[k])
    (off : Nat) (sub : List Instr) (slice : (code.drop off).take sub.length = sub)
    (fits : off + sub.length ≤ code.length) :
    ∀ k (within : k < sub.length), program[start + off + k]? = some sub[k] := by
  intro k within
  rw [Nat.add_assoc, whole (off + k) (by omega)]
  congr 1
  have lookup := congrArg (fun l : List Instr => l[k]?) slice
  simp only [List.getElem?_take, List.getElem?_drop, within, if_true] at lookup
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem within] at lookup
  exact Option.some.inj lookup

/-- A single instruction taken from inside a piece. -/
theorem fetch_one {start : Nat} {code : List Instr}
    (whole : ∀ k (within : k < code.length), program[start + k]? = some code[k])
    (off : Nat) (within : off < code.length) : program[start + off]? = some code[off] :=
  whole off within

end Ssz.Asm.Exec
