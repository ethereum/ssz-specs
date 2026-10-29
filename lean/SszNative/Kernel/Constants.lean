import Ssz.Hash.Sha256

/-!
The constants the SHA-256 kernels read, laid out as one table.

Every entry comes from the specification's own constants, so the kernels and the specification share them.
-/

namespace Ssz.Native.Kernel

open Ssz.Sha256 (roundConstants initialState schedule)

/--
The second block of every 64-byte message: a set bit, zeros, then the bit length 512.

Its schedule never changes, so its words plus round constants are precomputed.
-/
def paddingBlock : ByteArray :=
  ⟨(Array.replicate 64 (0 : UInt8)).set! 0 0x80 |>.set! 62 0x02⟩

/-- Round t's constant plus the padding block's schedule word t. -/
def paddingWK (t : Nat) : UInt32 :=
  roundConstants[t % 64]! + (schedule paddingBlock 0)[t % 64]!

/-- Byte offset of round t's constant, repeated in all sixteen lanes. -/
def kAvx512 (t : Nat) : Nat := 64 * t

/-- Byte offset of the padding block's word plus constant for round t, in all sixteen lanes. -/
def padAvx512 (t : Nat) : Nat := 4096 + 64 * t

/-- Byte offset of initial state word j, in all sixteen lanes. -/
def ivAvx512 (j : Nat) : Nat := 8192 + 64 * j

/-- Byte offset of the mask that reverses the bytes of every 32-bit lane. -/
def bswapAvx512 : Nat := 8704

/-- Byte offsets of the four lane-index masks the transposes use. -/
def transposeMask (k : Nat) : Nat := 8768 + 64 * k

/-- Byte offset of rounds 4r to 4r + 3's constants, as four lanes. -/
def kShaNi (r : Nat) : Nat := 9024 + 16 * r

/-- Byte offset of the padding block's words plus constants for rounds 4r to 4r + 3. -/
def padShaNi (r : Nat) : Nat := 9280 + 16 * r

/-- Byte offset of the initial state's words A, B, E, F, in the lane order the SHA instructions use. -/
def ivAbef : Nat := 9536

/-- Byte offset of the initial state's words C, D, G, H, in the lane order the SHA instructions use. -/
def ivCdgh : Nat := 9552

/-- Byte offset of the mask that reverses the bytes of four 32-bit lanes. -/
def bswapShaNi : Nat := 9568

/-- Bytes in the table. -/
def tableSize : Nat := 9584

/-- The byte-reversal shuffle's lane l: within each 16-byte block, byte 4m + k reads byte 4m + 3 - k. -/
def reverseLane (l : Nat) : UInt32 :=
  let m := (4 * (l % 4)).toUInt32
  (m + 3) ||| (m + 2) <<< (8 : UInt32) ||| (m + 1) <<< (16 : UInt32) ||| m <<< (24 : UInt32)

/-- Lane indices of the first transpose's 64-bit masks: the low half of each 64-bit lane, the high half zero. -/
def quadMask (k l : Nat) : UInt32 :=
  let picks := if k == 0 then #[0, 1, 8, 9, 4, 5, 12, 13] else #[2, 3, 10, 11, 6, 7, 14, 15]
  if l % 2 == 0 then picks[l / 2 % 8]! else 0

/-- Lane indices of the second transpose's 32-bit masks. -/
def laneMask (k l : Nat) : UInt32 :=
  let picks := if k == 0 then #[0, 2, 16, 18, 1, 3, 17, 19, 4, 6, 20, 22, 5, 7, 21, 23]
    else #[8, 10, 24, 26, 9, 11, 25, 27, 12, 14, 28, 30, 13, 15, 29, 31]
  picks[l % 16]!

/-- The table's 32-bit word w, at byte offset 4w. -/
def tableWord (w : Nat) : UInt32 :=
  let iv := fun j => initialState[j % 8]!
  -- Sixteen-lane constants: one 64-byte row per entry.
  if w < 1024 then roundConstants[w / 16 % 64]!
  else if w < 2048 then paddingWK ((w - 1024) / 16)
  else if w < 2176 then iv ((w - 2048) / 16)
  else if w < 2192 then reverseLane (w - 2176)
  else if w < 2224 then quadMask ((w - 2192) / 16) (w - 2192)
  else if w < 2256 then laneMask ((w - 2224) / 16) (w - 2224)
  -- Four-lane constants for the SHA instructions.
  else if w < 2320 then roundConstants[(w - 2256) % 64]!
  else if w < 2384 then paddingWK (w - 2320)
  -- ABEF and CDGH hold A, B, E, F and C, D, G, H from the highest lane down.
  else if w < 2388 then iv (#[5, 4, 1, 0][(w - 2384) % 4]!)
  else if w < 2392 then iv (#[7, 6, 3, 2][(w - 2388) % 4]!)
  else reverseLane (w - 2392)

/-- The table's bytes: each word little-endian, in offset order. -/
def table : ByteArray :=
  ⟨Array.ofFn (n := tableSize) fun i => (tableWord (i / 4) >>> (8 * (i.val % 4)).toUInt32).toUInt8⟩

end Ssz.Native.Kernel
