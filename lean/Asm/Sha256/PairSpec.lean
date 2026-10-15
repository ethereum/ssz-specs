import Asm.Sha256.Pair
import Asm.Sha256.Rounds
import Ssz.Merkle.Tree

/-! SHA-256 of a 64-byte message, as two compressions with a fixed second block. -/

namespace Ssz.Asm.Sha256

open Ssz.Sha256 (Spec.messageWord Spec.small0 Spec.small1 Spec.inputWord Spec.inputWords
  Spec.compression Spec.initial Spec.digest Spec.padded Spec.blocks Spec.zeroCount Spec.hash)

theorem messageWord_early {input : Vector (BitVec 32) 16} {t : Nat} (early : t < 16) :
    Spec.messageWord input t = input[t] := by
  rw [Spec.messageWord, dif_pos early]

/-- The padding block's schedule is the table, word for word. -/
theorem padSchedule_spec : ∀ t (within : t < 64), Spec.messageWord padWords t = padSchedule[t] := by
  -- The table starts with the block and then obeys the schedule recurrence, both checked by evaluation.
  have early : ∀ t (within : t < 16), padWords[t] = padSchedule[t]'(by omega) := by decide
  have late : ∀ t (within : t < 64), 16 ≤ t →
      padSchedule[t] = padSchedule[t - 16] + Spec.small0 padSchedule[t - 15] + padSchedule[t - 7] +
        Spec.small1 padSchedule[t - 2] := by decide
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro within
    by_cases low : t < 16
    · rw [messageWord_early low, early t low]
    · rw [messageWord_late padWords (by omega), late t within (by omega),
        ih (t - 16) (by omega) (by omega), ih (t - 15) (by omega) (by omega),
        ih (t - 7) (by omega) (by omega), ih (t - 2) (by omega) (by omega)]

/-- Reading a byte from a concatenation reads from whichever part holds that position. -/
theorem get!_append {a b : Array UInt8} {i : Nat} :
    (ByteArray.mk (a ++ b)).get! i = if i < a.size then (ByteArray.mk a).get! i
      else (ByteArray.mk b).get! (i - a.size) := by
  simp only [ByteArray.get!]
  split
  · rename_i inside
    simp [getElem!_def, Array.getElem?_append_left inside, inside]
  · rename_i outside
    simp [getElem!_def, Array.getElem?_append_right (Nat.le_of_not_lt outside)]

/-- A message word read at matching positions of two byte strings agrees. -/
theorem inputWord_shift {a b : ByteArray} {s q : Nat}
    (same : ∀ k, k < 4 → a.get! (s + (q + k)) = b.get! (q + k)) :
    Spec.inputWord a (s + q) = Spec.inputWord b q := by
  have b0 := same 0 (by omega)
  have b1 := same 1 (by omega)
  have b2 := same 2 (by omega)
  have b3 := same 3 (by omega)
  simp only [Nat.add_zero, ← Nat.add_assoc] at b0 b1 b2 b3
  unfold Spec.inputWord
  rw [b0, b1, b2, b3]

/-- Message words read at matching positions of two byte strings agree. -/
theorem inputWords_shift {a b : ByteArray} {s : Nat}
    (same : ∀ k, k < 64 → a.get! (s + k) = b.get! k) : Spec.inputWords a s = Spec.inputWords b 0 := by
  apply Vector.ext
  intro p within
  rw [Spec.inputWords, Spec.inputWords, Vector.getElem_ofFn, Vector.getElem_ofFn, Nat.zero_add]
  exact inputWord_shift fun k below => same _ (by omega)

/-- The bytes padding adds after a 64-byte message. -/
def padTail : ByteArray :=
  ⟨#[0x80] ++ Array.replicate 55 0 ++ Array.ofFn fun i : Fin 8 =>
    UInt8.ofNat ((64 * 8 / 2 ^ (56 - 8 * i.val)) % 256)⟩

theorem padded_eq {message : ByteArray} (size : message.size = 64) :
    Spec.padded message = ⟨message.data ++ padTail.data⟩ := by
  -- The delimiter, the zeros, and the length all depend on the size alone.
  simp only [Spec.padded, padTail, Spec.zeroCount, size, Array.append_assoc]

theorem padTail_words : Spec.inputWords padTail 0 = padWords := by
  decide

/--
SHA-256 of 64 bytes is two compressions, the second over the fixed padding block.

    hash(message) = digest(compress(padding, compress(message, initial)))
-/
theorem hash_sixtyFour {message : ByteArray} (size : message.size = 64) :
    Spec.hash message = Spec.digest
      (Spec.compression padWords (Spec.compression (Spec.inputWords message 0) Spec.initial)) := by
  have dataSize : message.data.size = 64 := size
  have total : (Spec.padded message).size / 64 = 2 := by
    rw [padded_eq size]
    simp [ByteArray.size, padTail, dataSize]
  have low : Spec.inputWords (Spec.padded message) 0 = Spec.inputWords message 0 := by
    apply inputWords_shift
    intro k within
    rw [padded_eq size, Nat.zero_add, get!_append, if_pos (by omega)]
  have high : Spec.inputWords (Spec.padded message) 64 = padWords := by
    rw [← padTail_words]
    apply inputWords_shift
    intro k within
    rw [padded_eq size, get!_append, if_neg (by omega), dataSize, Nat.add_sub_cancel_left]
  simp only [Spec.hash, total, Spec.blocks, Nat.mul_zero, Nat.mul_one, low, high]

end Ssz.Asm.Sha256
