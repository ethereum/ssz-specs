import SszNative.Kernel.Constants
import SszNative.Asm.Semantics
import EthLib.Cryptography.Proofs.Hash.Sha256

/-! What the kernels compute, in the specification's terms: two compressions per pair, and constants from the table. -/

namespace EthLib.Consensus.Ssz.Native.Kernel

open EthLib.Cryptography.Hash.Sha256 hiding K IV
open EthLib.Consensus.Ssz.Native.Asm

/-- The padding block, byte by byte: the closing bit, zeros, then the length 512 in bits. -/
private theorem paddingBlock_data :
    paddingBlock.data = #[0x80] ++ Array.replicate 55 0 ++ (lengthBytes 64).data := by
  -- A literal array, checked by evaluation.
  decide

/-- A 64-byte message pads to itself followed by the fixed padding block. -/
theorem pad_pair (message : ByteArray) (size : message.size = 64) : pad message = message ++ paddingBlock := by
  -- The closing bit, the zeros, and the length are exactly the padding block's bytes.
  unfold pad
  rw [size]
  apply ByteArray.ext
  simp only [ByteArray.data_append, ByteArray.push, paddingBlock_data, Array.append_assoc, Array.push_eq_append]
  rfl

/-- A byte inside an array, read with a default. -/
theorem get!_eq (a : ByteArray) (i : Nat) (h : i < a.size) : a.get! i = a[i] := by
  -- A byte array's byte is its data's.
  cases a with
  | mk bs => exact getElem!_pos bs i h

/-- A byte past an array's end, read with a default. -/
theorem get!_out (a : ByteArray) (i : Nat) (h : ¬ i < a.size) : a.get! i = default := by
  -- A byte array's byte is its data's.
  cases a with
  | mk bs => exact getElem!_neg bs i h

/-- A byte inside the first of two joined arrays comes from the first. -/
theorem get!_append_left (a b : ByteArray) (i : Nat) (within : i < a.size) :
    (a ++ b).get! i = a.get! i := by
  -- The index falls inside the first array.
  rw [get!_eq _ _ (by rw [ByteArray.size_append]; omega), get!_eq _ _ within, ByteArray.getElem_append_left within]

/-- A byte past the first of two joined arrays comes from the second. -/
theorem get!_append_right (a b : ByteArray) (i : Nat) :
    (a ++ b).get! (a.size + i) = b.get! i := by
  -- Inside the second array, or past it on both sides.
  by_cases inside : i < b.size
  · rw [get!_eq _ _ (by rw [ByteArray.size_append]; omega), get!_eq _ _ inside,
      ByteArray.getElem_append_right (by omega)]
    simp
  · rw [get!_out _ _ (by rw [ByteArray.size_append]; omega), get!_out _ _ inside]

/-- Byte i of the table is byte i mod 4 of its word i / 4. -/
theorem table_get (i : Nat) (within : i < tableSize) :
    table.get! i = (tableWord (i / 4) >>> (8 * (i % 4)).toUInt32).toUInt8 := by
  -- The table is built byte by byte from its words.
  rw [get!_eq _ _ (by simp [table, ByteArray.size]; exact within)]
  simp [table, ByteArray.getElem_eq_getElem_data]

/-- Reading a byte with `[i]!` is reading it with `get!`. -/
theorem getElem!_eq_get! (a : ByteArray) (i : Nat) : a[i]! = a.get! i := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h, get!_eq a i h]
  · rw [getElem!_neg a i h, get!_out a i h]

/-- The digest of a 64-byte message: the message compressed, then the padding block. -/
theorem hash_pair (message : ByteArray) (size : message.size = 64) :
    Cryptography.Hash.Sha256.hash message = digest (compress (compress Cryptography.Hash.Sha256.IV message 0) paddingBlock 0) := by
  -- A 64-byte message pads to two blocks.
  have padded : (pad message).size = 128 := by
    rw [pad_pair message size, ByteArray.size_append, size]
    rfl
  simp only [Cryptography.Hash.Sha256.hash, padded]
  -- Two blocks: the message's bytes, then the padding block's.
  simp only [show List.range (128 / 64) = [0, 1] by rfl, List.foldl_cons, List.foldl_nil]
  rw [pad_pair message size]
  apply congrArg digest
  rw [compress_congr _ (message ++ paddingBlock) paddingBlock (64 * 1) 0 fun i _ => by
    rw [getElem!_eq_get!, getElem!_eq_get!, Nat.zero_add, show 64 * 1 + i = message.size + i by omega,
      get!_append_right]]
  apply congrArg (compress · paddingBlock 0)
  exact compress_congr _ _ _ _ _ fun i within => by
    rw [getElem!_eq_get!, getElem!_eq_get!]
    simpa using get!_append_left message paddingBlock i (by omega)

/-- Whether memory holds the constant table from an address. -/
def TableAt (mem : Nat → UInt8) (base : Nat) : Prop :=
  ∀ i < tableSize, mem (base + i) = table.get! i

/-- The four bytes of a word, put back in place, give the word. -/
private theorem recombine (w : UInt32) :
    (w >>> 0).toUInt8.toUInt32 ||| (w >>> 8).toUInt8.toUInt32 <<< 8 |||
      (w >>> 16).toUInt8.toUInt32 <<< 16 ||| (w >>> 24).toUInt8.toUInt32 <<< 24 = w := by
  -- Bit by bit, each of the four bytes lands back in place.
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  simp only [Nat.forall_lt_succ_right, Nat.not_lt_zero, false_imp_iff, implies_true, true_and]
  simp [-UInt32.toUInt32_toUInt8]

/-- A word read from the table is the table's word. -/
theorem readWord_table (mem : Nat → UInt8) (base : Nat) (holds : TableAt mem base) (w : Nat)
    (within : w < tableSize / 4) : readWord mem (base + 4 * w) = tableWord w := by
  -- Each of the four bytes in memory is the table's byte of word w.
  have byte : ∀ k < 4, mem (base + 4 * w + k) = (tableWord w >>> (8 * k).toUInt32).toUInt8 := by
    intro k small
    rw [Nat.add_assoc, holds (4 * w + k) (by simp only [tableSize] at *; omega), table_get _ (by
      simp only [tableSize] at *; omega)]
    rw [show (4 * w + k) / 4 = w by omega, show (4 * w + k) % 4 = k by omega]
  -- The four bytes recombine into the word.
  simp only [readWord]
  rw [show base + 4 * w = base + 4 * w + 0 from rfl, byte 0 (by omega), byte 1 (by omega), byte 2 (by omega),
    byte 3 (by omega)]
  exact recombine _

end EthLib.Consensus.Ssz.Native.Kernel
