import SszNative.Proofs.Root.Variable.Facts
import Ssz.Proofs.Codec.RoundTripScalar

/-! The nodes of a bit list: its bytes without the closing bit, as the specification packs its bits. -/

namespace Ssz.Native.RootProof

open Ssz Ssz.Native

set_option maxRecDepth 100000 in
/-- Clearing one bit of a byte clears that bit and leaves every other bit as it was. -/
theorem clear_bit (x : UInt8) (m o : Fin 8) :
    (((x &&& ~~~((1 : UInt8) <<< UInt8.ofNat m.val)) >>> UInt8.ofNat o.val) &&& 1 == 1) =
      (o != m && ((x >>> UInt8.ofNat o.val) &&& 1 == 1)) := by
  -- Eight positions of 256 bytes, for every cleared position: a finite check.
  cases x with
  | ofBitVec x =>
    cases x with
    | ofFin x =>
      revert x m o
      decide

set_option maxRecDepth 100000 in
/-- No bit of a byte is set above its highest set bit. -/
theorem above_highest (x : UInt8) (o : Fin 8) (above : highestBit x < o.val) :
    ((x >>> UInt8.ofNat o.val) &&& 1 == 1) = false := by
  -- Every byte and position, checked by evaluation.
  cases x with
  | ofBitVec x =>
    cases x with
    | ofFin x =>
      revert x o
      decide

set_option maxRecDepth 100000 in
/-- The highest set bit of a byte is one of its eight positions. -/
theorem highest_lt (x : UInt8) : highestBit x < 8 := by
  -- Every byte, checked by evaluation.
  cases x with
  | ofBitVec x =>
    cases x with
    | ofFin x =>
      revert x
      decide

set_option maxRecDepth 100000 in
/-- Shifting a byte and masking its lowest bit reads one bit of it. -/
theorem byte_bit (byte : UInt8) (offset : Fin 8) :
    ((byte >>> UInt8.ofNat offset.val) &&& 1 == 1) = byte.toBitVec.getLsbD offset.val := by
  -- Every byte and position, checked by evaluation.
  cases byte with
  | ofBitVec byte =>
    cases byte with
    | ofFin byte =>
      revert byte offset
      decide

/-- Two bytes agreeing at all eight bit positions are equal. -/
theorem byte_eq_of_bits {left right : UInt8}
    (same : ∀ offset, offset < 8 →
      ((left >>> UInt8.ofNat offset) &&& 1 == 1) = ((right >>> UInt8.ofNat offset) &&& 1 == 1)) :
    left = right := by
  -- Compare the bytes bit by bit.
  apply UInt8.eq_iff_toBitVec_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro offset small
  simpa only [byte_bit left ⟨offset, small⟩, byte_bit right ⟨offset, small⟩] using same offset small

/-- What decoding a delimited encoding establishes: a nonzero last byte, and the bits below its highest bit. -/
theorem unpackDelimited_ok {limit : Option Nat} {data : Bytes} {bits : Array Bool}
    (read : unpackDelimited limit data = .ok bits) :
    data.size ≠ 0 ∧ data[data.size - 1]! ≠ 0 ∧
      bits = unpackBits data (8 * (data.size - 1) + highestBit data[data.size - 1]!) := by
  -- Decoding refuses an empty encoding and a zero last byte, and then counts the bits below the closing one.
  simp only [unpackDelimited, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure,
    Except.pure] at read
  split at read
  · cases read
  rename_i nonempty
  split at read
  · split at read <;> cases read
  rename_i nonzero
  refine ⟨by simpa using nonempty, by simpa using nonzero, ?_⟩
  split at read
  · split at read
    · cases read
    · cases read; rfl
  · cases read; rfl

/-- One byte of a packed bit list: the data byte, with the closing bit cleared where it shares the byte. -/
theorem packByte_delimited (data : Bytes) (j : Nat)
    (within : j < (8 * (data.size - 1) + highestBit data[data.size - 1]! + 7) / 8) :
    packByte (unpackBits data (8 * (data.size - 1) + highestBit data[data.size - 1]!)) j =
      if (8 * (data.size - 1) + highestBit data[data.size - 1]!) % 8 != 0 ∧
          j = (8 * (data.size - 1) + highestBit data[data.size - 1]!) / 8 then
        data[j]! &&& ~~~((1 : UInt8) <<< UInt8.ofNat ((8 * (data.size - 1) + highestBit data[data.size - 1]!) % 8))
      else data[j]! := by
  -- Name the last byte and its highest set bit.
  generalize hf : data[data.size - 1]! = final at *
  have hlt := highest_lt final
  generalize hh : highestBit final = h at *
  apply byte_eq_of_bits
  intro o small
  rw [packByte_bit _ _ _ small]
  -- Bit o of byte j is a decoded bit while it lies below the count.
  have bitAt : (unpackBits data (8 * (data.size - 1) + h))[j * 8 + o]?.getD false =
      if j * 8 + o < 8 * (data.size - 1) + h then ((data[j]! >>> UInt8.ofNat o) &&& 1 == 1) else false := by
    split
    · rename_i below
      rw [Array.getElem?_eq_getElem (by simpa [unpackBits] using below), Option.getD_some]
      simp only [unpackBits, Array.getElem_map, Array.getElem_range]
      rw [show (j * 8 + o) / 8 = j by omega, show (j * 8 + o) % 8 = o by omega]
    · rename_i above
      rw [Array.getElem?_eq_none (by simp [unpackBits]; omega)]
      rfl
  rw [bitAt]
  by_cases shared : ((8 * (data.size - 1) + h) % 8 != 0) = true ∧ j = (8 * (data.size - 1) + h) / 8
  · -- The byte holding the closing bit: the cleared bit and those above it read as zero.
    rw [if_pos shared]
    obtain ⟨notWhole, hj⟩ := shared
    have m : (8 * (data.size - 1) + h) % 8 = h := by omega
    have last : (8 * (data.size - 1) + h) / 8 = data.size - 1 := by omega
    rw [last] at hj
    subst hj
    rw [m, clear_bit _ ⟨h, hlt⟩ ⟨o, small⟩, hf]
    have positive : h ≠ 0 := by simp at notWhole; omega
    by_cases below : o < h
    · rw [if_pos (by omega)]
      simp [show o ≠ h by omega]
    · rw [if_neg (by omega)]
      by_cases tableEntry : o = h
      · subst tableEntry; simp
      · rw [above_highest final ⟨o, small⟩ (by rw [hh]; simp; omega)]
        simp
  · -- Any other byte holds eight decoded bits.
    rw [if_neg shared, if_pos (by
      by_cases ending : (8 * (data.size - 1) + h) % 8 = 0
      · omega
      · have : j ≠ (8 * (data.size - 1) + h) / 8 := fun e => shared ⟨by simpa using ending, e⟩
        omega)]

/-- The nodes of a decoded bit list: its count, and its bits packed as the specification packs them. -/
theorem bitNodes_data (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (small : stop - start + 64 < USize.size) (limit : Option Nat) (bits : Array Bool)
    (read : unpackDelimited limit (slice b start stop) = .ok bits) :
    bitCount b start stop = bits.size ∧
      (bitNodes b start bits.size).data = packBits bits ((bits.size + 7) / 8) ++
        Array.replicate (32 * nodesFor ((bits.size + 7) / 8) + 32 - (bits.size + 7) / 8) 0 := by
  -- A decoded bit list has a nonzero last byte, and its bits are those below the closing bit.
  obtain ⟨nonempty, _, decoded⟩ := unpackDelimited_ok read
  generalize hd : slice b start stop = data at *
  have size : data.size = stop - start := by rw [← hd]; exact slice_size b start stop inside
  subst decoded
  have counted : (unpackBits data (8 * (data.size - 1) + highestBit data[data.size - 1]!)).size =
      8 * (data.size - 1) + highestBit data[data.size - 1]! := by simp [unpackBits]
  rw [counted]
  have last : data[data.size - 1]! = b.get! (stop - 1) := by
    have e := slice_getElem! b start stop (stop - start - 1) inside (by omega)
    rw [hd] at e
    rw [show data.size - 1 = stop - start - 1 by omega, e]
    congr 1
    omega
  have hlt := highest_lt data[data.size - 1]!
  refine ⟨by simp only [bitCount]; rw [← last, size], ?_⟩
  have byte := packByte_delimited data
  generalize hc : 8 * (data.size - 1) + highestBit data[data.size - 1]! = count at *
  -- The packed range holds the slice's first bytes, then zeros.
  have nb : (count + 7) / 8 ≤ data.size := by omega
  have packed := packRange_data b start (start + (count + 7) / 8) (by omega) (by omega) (by omega)
  rw [show start + (count + 7) / 8 - start = (count + 7) / 8 by omega] at packed
  -- The packed range is the slice's first bytes, then zeros.
  have front : b.data.extract start (start + (count + 7) / 8) = data.extract 0 ((count + 7) / 8) := by
    rw [← hd, slice, Array.extract_extract]
    congr 1 <;> omega
  rw [front] at packed
  -- The first bytes, as packed bits wherever the closing bit does not share a byte with them.
  have lane : ∀ k (hk : k < (count + 7) / 8), (data.extract 0 ((count + 7) / 8))[k]'(by simp; omega) = data[k]! := by
    intro k hk
    simp only [Array.getElem_extract, Nat.zero_add]
    rw [getElem!_pos data k (by omega)]
  have packedSize : (packBits (unpackBits data count) ((count + 7) / 8)).size = (count + 7) / 8 := by
    simp [packBits]
  -- When the count is a whole number of bytes, the closing bit has a byte of its own.
  simp only [bitNodes]
  split
  · rename_i whole
    rw [packed]
    congr 1
    apply Array.ext (by simp [packedSize]; omega)
    intro k hk _
    simp only [Array.size_extract] at hk
    rw [lane k (by omega)]
    simp only [packBits, Array.getElem_ofFn]
    rw [byte k (by omega), if_neg (by simp at whole; omega)]
  -- Otherwise the closing bit is cleared from the last counted byte.
  · rename_i shared
    have tableEntry : count / 8 < (count + 7) / 8 := by simp at shared; omega
    simp only [ByteArray.set!, ByteArray.get!, packed, Array.set!_eq_setIfInBounds]
    rw [Array.setIfInBounds_append_left (by simp; omega)]
    congr 1
    apply Array.ext (by simp [packedSize]; omega)
    intro k hk _
    simp only [Array.size_setIfInBounds, Array.size_extract] at hk
    simp only [packBits, Array.getElem_ofFn]
    rw [byte k (by omega), Array.getElem_setIfInBounds (by simp; omega)]
    by_cases same : count / 8 = k
    · subst same
      rw [if_pos rfl, if_pos ⟨by simpa using shared, rfl⟩, getElem!_pos _ (count / 8) (by simp; omega),
        Array.getElem_append_left (by simp; omega), lane _ tableEntry]
    · rw [if_neg same, if_neg (fun h => same h.2.symm), lane k (by omega)]

/-- The nodes of a decoded bit list are, node by node, the specification's packed bits. -/
theorem bitNodes_nodes (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (small : stop - start + 64 < USize.size) (limit : Option Nat) (bits : Array Bool)
    (read : unpackDelimited limit (slice b start stop) = .ok bits) :
    bitCount b start stop = bits.size ∧
      nodesFrom (bitNodes b start bits.size) 0 (nodesFor ((bits.size + 7) / 8)) = packedBits bits ∧
      -- The node buffer is the packed bits followed by zeros.
      (bitNodes b start bits.size).size = 32 * nodesFor ((bits.size + 7) / 8) + 32 := by
  obtain ⟨counted, data⟩ := bitNodes_data b start stop ordered inside small limit bits read
  have sized : (packBits bits ((bits.size + 7) / 8)).size = (bits.size + 7) / 8 := by simp [packBits]
  refine ⟨counted, ?_, ?_⟩
  · have : bitNodes b start bits.size = ⟨packBits bits ((bits.size + 7) / 8) ++
        Array.replicate (32 * nodesFor ((bits.size + 7) / 8) + 32 - (bits.size + 7) / 8) 0⟩ := ByteArray.ext data
    rw [this, packedBits, show nodesFor ((bits.size + 7) / 8) = chunksForBytes
      (packBits bits ((bits.size + 7) / 8)).size by simp [sized, nodesFor, chunksForBytes]]
    apply nodes_padded
    simp [chunksForBytes, sized]
    -- The packed bits and the zeros fill the whole nodes and the spare one.
    omega
  · rw [← ByteArray.size_data, data]
    simp [sized, nodesFor]
    omega

end Ssz.Native.RootProof
