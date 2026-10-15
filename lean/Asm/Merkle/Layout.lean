import Asm.Flow
import Asm.Merkle.Code
import Asm.Sha256.Length

/-! Where each piece of the routine sits, so that a branch target names the code it lands on. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Merkle

open Ssz.Asm.Sha256 (pairCode)

theorem levelHeadCode_length (x : Nat) : (levelHeadCode x).length = 6 := rfl
theorem pairHeadCode_length (x y : Nat) : (pairHeadCode x y).length = 12 := rfl
theorem pairBodyCode_length (x : Nat) : (pairBodyCode x).length = (pairCode outSlot).length + 4 := by
  simp [pairBodyCode, pairStepCode]
theorem levelEndCode_length (x : Nat) : (levelEndCode x).length = 8 := rfl
theorem doneCode_length (x : Nat) : (doneCode x).length = 2 := rfl
theorem entryCode_length : entryCode.length = 19 := rfl
theorem oddCode_length : oddCode.length = 4 := rfl
theorem normalCode_length : normalCode.length = 3 := rfl
theorem emptyCode_length : emptyCode.length = 13 := rfl
theorem finishCode_length : finishCode.length = 15 := rfl

/-- The program as one list, the pieces in order. -/
def programList : List Instr :=
  entryCode ++ (levelHeadCode done ++ (pairHeadCode levelEnd normal ++ (oddCode ++ (normalCode ++
    (pairBodyCode pairHead ++ (levelEndCode levelHead ++ (doneCode finish ++ (emptyCode ++
    finishCode))))))))

theorem program_eq : program = programList.toArray := by
  simp only [program, programList, List.append_assoc]

/-- An instruction inside a piece is found at the piece's start plus its offset. -/
theorem fetch {before code after : List Instr} {start k : Nat} (at_start : before.length = start)
    (whole : programList = before ++ (code ++ after)) (within : k < code.length) :
    program[start + k]? = some code[k] := by
  rw [program_eq, whole, ← at_start, ← List.append_assoc]
  exact here_of_append within

theorem length_before_levelHead : (entryCode).length = levelHead := by
  rw [entryCode_length]
  rfl


theorem split_at_levelHead : programList = (entryCode) ++ (levelHeadCode done ++ (pairHeadCode levelEnd normal ++ (oddCode ++ (normalCode ++ (pairBodyCode pairHead ++ (levelEndCode levelHead ++ (doneCode finish ++ (emptyCode ++ (finishCode))))))))) := by
  simp only [programList, List.append_assoc, List.append_nil]

theorem fetch_levelHead {k : Nat} (within : k < (levelHeadCode done).length) :
    program[levelHead + k]? = some (levelHeadCode done)[k] :=
  fetch length_before_levelHead split_at_levelHead within

theorem length_before_pairHead : ((entryCode) ++ levelHeadCode done).length = pairHead := by
  rw [List.length_append, length_before_levelHead, levelHeadCode_length]
  rfl

theorem split_at_pairHead : programList = ((entryCode) ++ levelHeadCode done) ++ (pairHeadCode levelEnd normal ++ (oddCode ++ (normalCode ++ (pairBodyCode pairHead ++ (levelEndCode levelHead ++ (doneCode finish ++ (emptyCode ++ (finishCode)))))))) := by
  simp only [programList, List.append_assoc, List.append_nil]

theorem fetch_pairHead {k : Nat} (within : k < (pairHeadCode levelEnd normal).length) :
    program[pairHead + k]? = some (pairHeadCode levelEnd normal)[k] :=
  fetch length_before_pairHead split_at_pairHead within

theorem length_before_oddStart : (((entryCode) ++ levelHeadCode done) ++ pairHeadCode levelEnd normal).length = oddStart := by
  rw [List.length_append, length_before_pairHead, pairHeadCode_length]
  rfl

theorem split_at_oddStart : programList = (((entryCode) ++ levelHeadCode done) ++ pairHeadCode levelEnd normal) ++ (oddCode ++ (normalCode ++ (pairBodyCode pairHead ++ (levelEndCode levelHead ++ (doneCode finish ++ (emptyCode ++ (finishCode))))))) := by
  simp only [programList, List.append_assoc, List.append_nil]

theorem fetch_oddStart {k : Nat} (within : k < (oddCode).length) :
    program[oddStart + k]? = some (oddCode)[k] :=
  fetch length_before_oddStart split_at_oddStart within

theorem length_before_normal : ((((entryCode) ++ levelHeadCode done) ++ pairHeadCode levelEnd normal) ++ oddCode).length = normal := by
  rw [List.length_append, length_before_oddStart, oddCode_length]
  rfl

theorem split_at_normal : programList = ((((entryCode) ++ levelHeadCode done) ++ pairHeadCode levelEnd normal) ++ oddCode) ++ (normalCode ++ (pairBodyCode pairHead ++ (levelEndCode levelHead ++ (doneCode finish ++ (emptyCode ++ (finishCode)))))) := by
  simp only [programList, List.append_assoc, List.append_nil]

theorem fetch_normal {k : Nat} (within : k < (normalCode).length) :
    program[normal + k]? = some (normalCode)[k] :=
  fetch length_before_normal split_at_normal within

theorem length_before_pairBody : (((((entryCode) ++ levelHeadCode done) ++ pairHeadCode levelEnd normal) ++ oddCode) ++ normalCode).length = pairBody := by
  rw [List.length_append, length_before_normal, normalCode_length]
  rfl

theorem split_at_pairBody : programList = (((((entryCode) ++ levelHeadCode done) ++ pairHeadCode levelEnd normal) ++ oddCode) ++ normalCode) ++ (pairBodyCode pairHead ++ (levelEndCode levelHead ++ (doneCode finish ++ (emptyCode ++ (finishCode))))) := by
  simp only [programList, List.append_assoc, List.append_nil]

theorem fetch_pairBody {k : Nat} (within : k < (pairBodyCode pairHead).length) :
    program[pairBody + k]? = some (pairBodyCode pairHead)[k] :=
  fetch length_before_pairBody split_at_pairBody within

theorem length_before_levelEnd : ((((((entryCode) ++ levelHeadCode done) ++ pairHeadCode levelEnd normal) ++ oddCode) ++ normalCode) ++ pairBodyCode pairHead).length = levelEnd := by
  rw [List.length_append, length_before_pairBody, pairBodyCode_length, Sha256.pairCode_length]
  rfl

theorem split_at_levelEnd : programList = ((((((entryCode) ++ levelHeadCode done) ++ pairHeadCode levelEnd normal) ++ oddCode) ++ normalCode) ++ pairBodyCode pairHead) ++ (levelEndCode levelHead ++ (doneCode finish ++ (emptyCode ++ (finishCode)))) := by
  simp only [programList, List.append_assoc, List.append_nil]

theorem fetch_levelEnd {k : Nat} (within : k < (levelEndCode levelHead).length) :
    program[levelEnd + k]? = some (levelEndCode levelHead)[k] :=
  fetch length_before_levelEnd split_at_levelEnd within

theorem length_before_done : (((((((entryCode) ++ levelHeadCode done) ++ pairHeadCode levelEnd normal) ++ oddCode) ++ normalCode) ++ pairBodyCode pairHead) ++ levelEndCode levelHead).length = done := by
  rw [List.length_append, length_before_levelEnd, levelEndCode_length]
  rfl

theorem split_at_done : programList = (((((((entryCode) ++ levelHeadCode done) ++ pairHeadCode levelEnd normal) ++ oddCode) ++ normalCode) ++ pairBodyCode pairHead) ++ levelEndCode levelHead) ++ (doneCode finish ++ (emptyCode ++ (finishCode))) := by
  simp only [programList, List.append_assoc, List.append_nil]

theorem fetch_done {k : Nat} (within : k < (doneCode finish).length) :
    program[done + k]? = some (doneCode finish)[k] :=
  fetch length_before_done split_at_done within

theorem length_before_emptyStart : ((((((((entryCode) ++ levelHeadCode done) ++ pairHeadCode levelEnd normal) ++ oddCode) ++ normalCode) ++ pairBodyCode pairHead) ++ levelEndCode levelHead) ++ doneCode finish).length = emptyStart := by
  rw [List.length_append, length_before_done, doneCode_length]
  rfl

theorem split_at_emptyStart : programList = ((((((((entryCode) ++ levelHeadCode done) ++ pairHeadCode levelEnd normal) ++ oddCode) ++ normalCode) ++ pairBodyCode pairHead) ++ levelEndCode levelHead) ++ doneCode finish) ++ (emptyCode ++ (finishCode)) := by
  simp only [programList, List.append_assoc, List.append_nil]

theorem fetch_emptyStart {k : Nat} (within : k < (emptyCode).length) :
    program[emptyStart + k]? = some (emptyCode)[k] :=
  fetch length_before_emptyStart split_at_emptyStart within

theorem length_before_finish : (((((((((entryCode) ++ levelHeadCode done) ++ pairHeadCode levelEnd normal) ++ oddCode) ++ normalCode) ++ pairBodyCode pairHead) ++ levelEndCode levelHead) ++ doneCode finish) ++ emptyCode).length = finish := by
  rw [List.length_append, length_before_emptyStart, emptyCode_length]
  rfl

theorem split_at_finish : programList = (((((((((entryCode) ++ levelHeadCode done) ++ pairHeadCode levelEnd normal) ++ oddCode) ++ normalCode) ++ pairBodyCode pairHead) ++ levelEndCode levelHead) ++ doneCode finish) ++ emptyCode) ++ (finishCode ++ ([])) := by
  simp only [programList, List.append_assoc, List.append_nil]

theorem fetch_finish {k : Nat} (within : k < (finishCode).length) :
    program[finish + k]? = some (finishCode)[k] :=
  fetch length_before_finish split_at_finish within

theorem fetch_entry {k : Nat} (within : k < entryCode.length) :
    program[0 + k]? = some entryCode[k] :=
  fetch (before := []) (after := levelHeadCode done ++ (pairHeadCode levelEnd normal ++ (oddCode ++
      (normalCode ++ (pairBodyCode pairHead ++ (levelEndCode levelHead ++ (doneCode finish ++
      (emptyCode ++ finishCode))))))))
    rfl (by simp only [programList, List.nil_append]) within

/-- A run of instructions taken from inside a piece is found at the piece's start plus its offset. -/
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

end Ssz.Asm.Merkle
