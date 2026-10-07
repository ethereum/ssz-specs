/-!
SHA-256 for byte-aligned messages, following [FIPS 180-4](https://csrc.nist.gov/files/pubs/fips/180-4/final/docs/fips180-4.pdf).
-/

namespace Ssz.Sha256

/--
The sixty-four round constants.

Each is the first thirty-two bits of a cube root's fractional part.

The roots are those of the first sixty-four primes.
-/
def roundConstants : Vector UInt32 64 :=
  #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
  0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
  0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
  0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
  0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
  0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
  0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
  0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
  0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/--
The eight starting words of the state.

Each is the first thirty-two bits of a square root's fractional part.

The roots are those of the first eight primes.
-/
def initialState : Vector UInt32 8 :=
  #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- A word rotated right, with the bits leaving the bottom re-entering at the top. -/
@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- The message-schedule mixing applied to the word fifteen places back. -/
@[inline] def sigma0 (x : UInt32) : UInt32 :=
  rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)

/-- The message-schedule mixing applied to the word two places back. -/
@[inline] def sigma1 (x : UInt32) : UInt32 :=
  rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

/-- The round mixing applied to the first working word. -/
@[inline] def bigSigma0 (x : UInt32) : UInt32 :=
  rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

/-- The round mixing applied to the fifth working word. -/
@[inline] def bigSigma1 (x : UInt32) : UInt32 :=
  rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- Bit by bit, the second word where the first is set and the third where it is not. -/
@[inline] def choose (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ ((~~~x) &&& z)

/-- Bit by bit, whichever value at least two of the three words agree on. -/
@[inline] def majority (x y z : UInt32) : UInt32 :=
  (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Reading four bytes of a block as one big-endian word. -/
@[inline] def wordAt (block : ByteArray) (start : Nat) : UInt32 :=
  (block.get! start).toUInt32 <<< 24 |||
  (block.get! (start + 1)).toUInt32 <<< 16 |||
  (block.get! (start + 2)).toUInt32 <<< 8 |||
  (block.get! (start + 3)).toUInt32

/-- The first words of the schedule, with every earlier reference proved in bounds. -/
def schedulePrefix (block : ByteArray) (start : Nat) : (count : Nat) → Vector UInt32 count
  | 0 => .emptyWithCapacity 64
  | count + 1 =>
    let previous := schedulePrefix block start count
    -- FIPS 180-4, section 6.2.2: sixteen input words precede the four-term recurrence.
    let next := if first : count < 16 then wordAt block (start + 4 * count)
      else previous[count - 16]'(by omega) + sigma0 (previous[count - 15]'(by omega)) +
        previous[count - 7]'(by omega) + sigma1 (previous[count - 2]'(by omega))
    previous.push next

/-- Expand the schedule in one tail-recursive pass with a uniquely owned array. -/
private def schedulePrefixTR (block : ByteArray) (start count : Nat) : Vector UInt32 count :=
  -- Dependent folding retains the same proved bounds as the recursive specification.
  Nat.dfold count (α := fun i _ => Vector UInt32 i) (fun i _ previous =>
    let next := if first : i < 16 then wordAt block (start + 4 * i)
      else previous[i - 16]'(by omega) + sigma0 (previous[i - 15]'(by omega)) +
        previous[i - 7]'(by omega) + sigma1 (previous[i - 2]'(by omega))
    previous.push next) (.emptyWithCapacity 64)

@[csimp] private theorem schedulePrefix_eq_tail : schedulePrefix = schedulePrefixTR := by
  -- Induction checks the same input words and recurrence at every prefix length.
  funext block start count
  induction count with
  | zero => simp [schedulePrefix, schedulePrefixTR, Nat.dfold_zero]
  | succ count ih =>
    simp only [schedulePrefixTR, Nat.dfold_succ] at *
    simp only [schedulePrefix, ih]

/-- The sixty-four schedule words consumed by one block's rounds. -/
def schedule (block : ByteArray) (start : Nat) : Vector UInt32 64 :=
  schedulePrefix block start 64

private theorem backIndex (i back : Nat) (within : i < 64) (earlier : back ≤ i) :
    (USize.ofNat i - USize.ofNat back).toNat = i - back := by
  -- Schedule indices fit even on 32-bit platforms, and backward references never underflow.
  have hi := USize.toNat_ofNat_of_lt_32 (n := i) (by omega)
  have hb := USize.toNat_ofNat_of_lt_32 (n := back) (by omega)
  rw [USize.toNat_sub_of_le]
  · rw [hi, hb]
  · apply USize.le_iff_toNat_le.mpr
    rwa [hi, hb]

/-- Read an earlier schedule word through a proved machine-sized index. -/
@[inline] private def wordBack {i : Nat} (previous : Vector UInt32 i) (back : Nat)
    (within : i < 64) (positive : 0 < back) (earlier : back ≤ i) : UInt32 :=
  -- Machine subtraction avoids arbitrary-precision index arithmetic in the hot loop.
  previous.toArray.uget (USize.ofNat i - USize.ofNat back) (by
    rw [backIndex i back within earlier, Vector.size_toArray]
    omega)

/-- Expand one block with machine-sized backward indices and a uniquely owned array. -/
private def scheduleFast (block : ByteArray) (start : Nat) : Vector UInt32 64 :=
  -- Every prefix is indexed by its exact length, so all four reads remain proved in bounds.
  Nat.dfold 64 (α := fun i _ => Vector UInt32 i) (fun i within previous =>
    let next := if first : i < 16 then wordAt block (start + 4 * i)
      else wordBack previous 16 within (by omega) (by omega) +
        sigma0 (wordBack previous 15 within (by omega) (by omega)) +
        wordBack previous 7 within (by omega) (by omega) +
        sigma1 (wordBack previous 2 within (by omega) (by omega))
    previous.push next) (.emptyWithCapacity 64)

@[csimp] private theorem schedule_eq_fast : schedule = scheduleFast := by
  -- Replacing natural indices with equal machine indices preserves every expanded word.
  funext block start
  rw [schedule, schedulePrefix_eq_tail]
  unfold schedulePrefixTR scheduleFast
  congr 1
  funext i within previous
  split
  · rfl
  · simp only [wordBack, Array.uget]
    simp only [backIndex i 16 within (by omega), backIndex i 15 within (by omega),
      backIndex i 7 within (by omega), backIndex i 2 within (by omega)]
    rfl

/-- One SHA-256 round, preserving the eight working words. -/
@[inline] def round (state : Vector UInt32 8) (constant word : UInt32) : Vector UInt32 8 :=
  -- FIPS 180-4, section 6.2.2, names the eight working words in order.
  let a := state[0]
  let b := state[1]
  let c := state[2]
  let d := state[3]
  let e := state[4]
  let f := state[5]
  let g := state[6]
  let h := state[7]
  let t1 := h + bigSigma1 e + choose e f g + constant + word
  let t2 := bigSigma0 a + majority a b c
  #v[t1 + t2, a, b, c, d + t1, e, f, g]

/-- The state after absorbing one sixty-four-byte block. -/
def compress (state : Vector UInt32 8) (block : ByteArray) (start : Nat) : Vector UInt32 8 :=
  let words := schedule block start
  let working := (List.finRange 64).foldl
    (fun current i => round current roundConstants[i] words[i]) state
  state.zipWith (· + ·) working

/-- Run the rounds with eight scalar accumulators instead of allocating a vector per round. -/
private def roundsScalar (initial : Vector UInt32 8) (words : Vector UInt32 64) : List (Fin 64) →
    UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → Vector UInt32 8
  | [], a, b, c, d, e, f, g, h =>
    -- Feed forward directly into the result, avoiding a second eight-word vector.
    #v[initial[0] + a, initial[1] + b, initial[2] + c, initial[3] + d,
      initial[4] + e, initial[5] + f, initial[6] + g, initial[7] + h]
  | i :: rest, a, b, c, d, e, f, g, h =>
    -- Keep the working words in machine registers throughout the compression loop.
    let t1 := h + bigSigma1 e + choose e f g + roundConstants[i] + words[i]
    let t2 := bigSigma0 a + majority a b c
    roundsScalar initial words rest (t1 + t2) a b c (d + t1) e f g

private theorem roundsScalar_eq (initial : Vector UInt32 8) (words : Vector UInt32 64)
    (indices : List (Fin 64))
    (a b c d e f g h : UInt32) :
    roundsScalar initial words indices a b c d e f g h =
      initial.zipWith (· + ·) (indices.foldl (fun current i => round current roundConstants[i] words[i])
        #v[a, b, c, d, e, f, g, h]) := by
  -- Each scalar transition is exactly the eight-word FIPS round.
  induction indices generalizing a b c d e f g h with
  | nil =>
    apply Vector.ext
    intro i bound
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => simp [roundsScalar]
    | n + 8 => omega
  | cons i rest ih =>
    simpa [roundsScalar, List.foldl_cons, round] using
      ih (h + bigSigma1 e + choose e f g + roundConstants[i] + words[i] +
        (bigSigma0 a + majority a b c)) a b c
        (d + (h + bigSigma1 e + choose e f g + roundConstants[i] + words[i])) e f g

/-- Absorb one block using scalar round accumulators. -/
private def compressScalar (state : Vector UInt32 8) (block : ByteArray) (start : Nat) :
    Vector UInt32 8 :=
  -- Allocate the schedule once and write the working vector only after the final round.
  let words := schedule block start
  roundsScalar state words (List.finRange 64)
    state[0] state[1] state[2] state[3] state[4] state[5] state[6] state[7]

@[csimp] private theorem compress_eq_scalar : compress = compressScalar := by
  -- Compiler substitution preserves the existing specification and its refinement proofs.
  funext state block start
  simp only [compress, compressScalar, roundsScalar_eq]
  congr 1

/-- The number of whole zero bytes between the closing bit and the length. -/
def paddingZeros (size : Nat) : Nat :=
  -- Reserve one delimiter byte and eight length bytes before rounding up to a 64-byte block.
  (64 - (size + 9) % 64) % 64

/-- The message length in bits, encoded as eight big-endian bytes. -/
def lengthBytes (size : Nat) : ByteArray :=
  -- FIPS 180-4 admits fewer than 2^64 bits, so an admitted length fits this word.
  let bits : UInt64 := (UInt64.ofNat size) * 8
  ⟨Array.ofFn fun i : Fin 8 => (bits >>> (56 - 8 * UInt64.ofNat i.val)).toUInt8⟩

/--
The message followed by a one bit, zeros, and its own length in bits.

FIPS 180-4, section 5.1.1, places the length in the last eight bytes of a full block.

The standard admits messages of fewer than 2^61 bytes.
-/
def pad (message : ByteArray) : ByteArray :=
  message.push 0x80 ++ ⟨Array.replicate (paddingZeros message.size) 0⟩ ++
    lengthBytes message.size

/-- The final state written as thirty-two bytes, most significant byte first in each word. -/
def digest (state : Vector UInt32 8) : ByteArray :=
  ⟨Array.ofFn fun i : Fin 32 =>
    (state[i.val / 4]'(by omega) >>> (24 - 8 * UInt32.ofNat (i.val % 4))).toUInt8⟩

/-- Write the eight words directly into a 32-byte output buffer. -/
private def digestFast (state : Vector UInt32 8) : ByteArray :=
  -- Fixed byte positions avoid a closure call and division for every output byte.
  ⟨#[
    (state[0] >>> 24).toUInt8, (state[0] >>> 16).toUInt8, (state[0] >>> 8).toUInt8, state[0].toUInt8,
    (state[1] >>> 24).toUInt8, (state[1] >>> 16).toUInt8, (state[1] >>> 8).toUInt8, state[1].toUInt8,
    (state[2] >>> 24).toUInt8, (state[2] >>> 16).toUInt8, (state[2] >>> 8).toUInt8, state[2].toUInt8,
    (state[3] >>> 24).toUInt8, (state[3] >>> 16).toUInt8, (state[3] >>> 8).toUInt8, state[3].toUInt8,
    (state[4] >>> 24).toUInt8, (state[4] >>> 16).toUInt8, (state[4] >>> 8).toUInt8, state[4].toUInt8,
    (state[5] >>> 24).toUInt8, (state[5] >>> 16).toUInt8, (state[5] >>> 8).toUInt8, state[5].toUInt8,
    (state[6] >>> 24).toUInt8, (state[6] >>> 16).toUInt8, (state[6] >>> 8).toUInt8, state[6].toUInt8,
    (state[7] >>> 24).toUInt8, (state[7] >>> 16).toUInt8, (state[7] >>> 8).toUInt8, state[7].toUInt8]⟩

@[csimp] private theorem digest_eq_fast : digest = digestFast := by
  -- Compare the fixed big-endian byte positions against the indexed specification.
  funext state
  apply ByteArray.ext
  apply Array.ext
  · simp [digest, digestFast]
  · intro i left right
    have bound : i < 32 := by simpa [digest] using left
    match i with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15
      | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 =>
      simp [digest, digestFast]
    | n + 32 => omega

/-- The thirty-two byte digest of a message. -/
def hash (message : ByteArray) : ByteArray :=
  let padded := pad message
  let state := (List.range (padded.size / 64)).foldl
    (fun current block => compress current padded (64 * block)) initialState
  digest state

/-- Hash using a counted block loop without allocating a list of block indices. -/
private def hashTR (message : ByteArray) : ByteArray :=
  -- The standard tail-recursive fold keeps only the current chaining state alive.
  let padded := pad message
  digest (Nat.fold (padded.size / 64)
    (fun block _ current => compress current padded (64 * block)) initialState)

private theorem fold_range (count : Nat) (step : Nat → Vector UInt32 8 → Vector UInt32 8)
    (state : Vector UInt32 8) :
    Nat.fold count (fun i _ current => step i current) state =
      (List.range count).foldl (fun current i => step i current) state := by
  -- Increasing counted indices visit exactly the same blocks as the list specification.
  induction count with
  | zero => rfl
  | succ count ih => simp [Nat.fold, List.range_succ, List.foldl_append, ih]

@[csimp] private theorem hash_eq_tail : hash = hashTR := by
  -- Only the iteration representation changes, leaving padding and digest output identical.
  funext message
  simp only [hash, hashTR, fold_range]

end Ssz.Sha256
