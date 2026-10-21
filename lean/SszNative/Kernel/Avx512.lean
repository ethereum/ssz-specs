import SszNative.Asm.Instr
import SszNative.Kernel.Constants

/-!
Sixteen pairs of nodes hashed at once with AVX-512: lane j of every vector belongs to pair j.

Each pair is a 64-byte message, so its hash is two compressions.
The first compression reads the pair, and the second reads the constant padding block.

Registers 0 to 7 hold the working words A to H.
They are renamed rather than moved each round.
Registers 8 to 23 hold the sixteen most recent schedule words.
Registers 24 to 31 are temporaries.

The schedule follows Prysm's hashtree.
Each round adds its constant to H before E is ready, so four operations separate one E from the next.
-/

namespace Ssz.Native.Kernel.Avx512

open Ssz.Native.Asm

/-- The output address, the first argument. -/
abbrev out : Gpr := .rdi

/-- The address of the first left node, the second argument. -/
abbrev left : Gpr := .rsi

/-- The address of the first right node, the third argument. -/
abbrev right : Gpr := .rdx

/-- The number of batches of sixteen pairs, the fourth argument. -/
abbrev count : Gpr := .rcx

/-- The constant table's address, the fifth argument. -/
abbrev tbl : Gpr := .r8

/-- The home register of working word j. -/
def home (j : Nat) : Vreg := ⟨j % 8, by omega⟩

/-- The register holding schedule word t, in a ring of sixteen. -/
def ring (t : Nat) : Vreg := ⟨8 + t % 16, by omega⟩

/-- The round's running sum. -/
def t1 : Vreg := 24

/-- Temporary k, for k below 7. -/
def tmp (k : Nat) : Vreg := ⟨25 + k % 7, by omega⟩

/-- A table entry. -/
def tableEntry (offset : Nat) : Mem := ⟨tbl, offset⟩

/-- The register holding working word j at round t: every round shifts each word one place along. -/
def role (t j : Nat) : Vreg := home (j + 8 - t % 8)

/--
One round, with the next T1 seeded from H and the round's word plus constant.

The word plus constant is a register for the first block and a table entry for the padding block.
-/
def roundCode (t : Nat) (seed : Instr) : List Instr :=
  let a := role t 0
  let b := role t 1
  let c := role t 2
  let d := role t 3
  let e := role t 4
  let f := role t 5
  let g := role t 6
  let h := role t 7
  [seed,
    .vmov (tmp 0) e,
    .vror (tmp 1) e 6, .vror (tmp 2) e 11, .vror (tmp 3) e 25,
    -- Choice takes f where e is set and g elsewhere.
    .vternlog (tmp 0) f g 0xCA,
    .vternlog (tmp 1) (tmp 2) (tmp 3) 0x96,
    .vadd t1 t1 (tmp 0), .vadd t1 t1 (tmp 1),
    .vadd d d t1,
    .vror h a 2, .vror (tmp 2) a 13, .vror (tmp 3) a 22,
    .vmov (tmp 0) a,
    -- Majority is the bitwise vote of a, b, and c.
    .vternlog (tmp 0) b c 0xE8,
    .vternlog h (tmp 2) (tmp 3) 0x96,
    .vadd h h (tmp 0), .vadd h h t1]

/-- A first-block round: T1 starts as H plus the round constant, then the schedule word joins it. -/
def firstRound (t : Nat) : List Instr :=
  match roundCode t (.vaddMem t1 (role t 7) (tableEntry (kAvx512 t))) with
  | seed :: rest => seed :: .vadd t1 t1 (ring t) :: rest
  | [] => []

/-- A padding-block round: T1 starts as H plus the precomputed word and constant. -/
def paddingRound (t : Nat) : List Instr :=
  roundCode t (.vaddMem t1 (role t 7) (tableEntry (padAvx512 t)))

/-- Schedule word t + 16, written over word t once round t has used it. -/
def scheduleCode (t : Nat) : List Instr :=
  let w := ring t
  [.vror (tmp 4) (ring (t + 14)) 17, .vror (tmp 5) (ring (t + 14)) 19, .vshr (tmp 6) (ring (t + 14)) 10,
    .vternlog (tmp 4) (tmp 5) (tmp 6) 0x96,
    .vadd w w (tmp 4), .vadd w w (ring (t + 9)),
    .vror (tmp 4) (ring (t + 1)) 7, .vror (tmp 5) (ring (t + 1)) 18, .vshr (tmp 6) (ring (t + 1)) 3,
    .vternlog (tmp 4) (tmp 5) (tmp 6) 0x96,
    .vadd w w (tmp 4)]

/--
Load sixteen messages and transpose them, so that word t of message j lands in lane j of register t.

Message j is the left node at left + ls * j followed by the right node at right + rs * j.
Register i holds the left nodes of messages i and 8 + i, and register 8 + i their right nodes.
-/
def loadCode (ls rs : Nat) : List Instr :=
  (List.range 8).flatMap (fun i =>
    [.vloadHalf (ring i) ⟨left, ls * i⟩, .vloadHalf (ring (8 + i)) ⟨right, rs * i⟩]) ++
  (List.range 8).flatMap (fun i =>
    [.vinsertHigh (ring i) (ring i) ⟨left, ls * (8 + i)⟩,
      .vinsertHigh (ring (8 + i)) (ring (8 + i)) ⟨right, rs * (8 + i)⟩])

/-- The sixteen-by-sixteen transpose of 32-bit lanes, in four rows at a time and then across halves. -/
def transposeIn : List Instr :=
  let r := ring
  let t0 := tmp 0
  let t1' := tmp 1
  let m0 := tmp 4
  let m1 := tmp 5
  -- Within each group of four rows: pairs of lanes, then single lanes.
  [.vshufps t0 (r 0) (r 1) 0x44, .vshufps (r 0) (r 0) (r 1) 0xEE,
    .vshufps t1' (r 2) (r 3) 0x44, .vshufps (r 2) (r 2) (r 3) 0xEE,
    .vshufps (r 3) t0 t1' 0xDD, .vshufps (r 1) (r 0) (r 2) 0x88,
    .vshufps (r 0) (r 0) (r 2) 0xDD, .vshufps t0 t0 t1' 0x88,
    .vload m0 (tableEntry (transposeMask 0)), .vload m1 (tableEntry (transposeMask 1)),
    .vshufps (r 2) (r 4) (r 5) 0x44, .vshufps (r 4) (r 4) (r 5) 0xEE,
    .vshufps t1' (r 6) (r 7) 0x44, .vshufps (r 6) (r 6) (r 7) 0xEE,
    .vshufps (r 7) (r 2) t1' 0xDD, .vshufps (r 5) (r 4) (r 6) 0x88,
    .vshufps (r 4) (r 4) (r 6) 0xDD, .vshufps (r 2) (r 2) t1' 0x88,
    .vshufps (r 6) (r 8) (r 9) 0x44, .vshufps (r 8) (r 8) (r 9) 0xEE,
    .vshufps t1' (r 10) (r 11) 0x44, .vshufps (r 10) (r 10) (r 11) 0xEE,
    .vshufps (r 11) (r 6) t1' 0xDD, .vshufps (r 9) (r 8) (r 10) 0x88,
    .vshufps (r 8) (r 8) (r 10) 0xDD, .vshufps (r 6) (r 6) t1' 0x88,
    .vshufps (r 10) (r 12) (r 13) 0x44, .vshufps (r 12) (r 12) (r 13) 0xEE,
    .vshufps t1' (r 14) (r 15) 0x44, .vshufps (r 14) (r 14) (r 15) 0xEE,
    .vshufps (r 15) (r 10) t1' 0xDD, .vshufps (r 13) (r 12) (r 14) 0x88,
    .vshufps (r 12) (r 12) (r 14) 0xDD, .vshufps (r 10) (r 10) t1' 0x88,
    -- Across halves: each output row takes two 64-bit lanes from each of two rows.
    .vmov t1' m0, .vpermi2q t1' (r 9) (r 13), .vmov (r 14) m1, .vpermi2q (r 14) (r 9) (r 13),
    .vmov (r 9) m0, .vpermi2q (r 9) (r 11) (r 15), .vmov (r 13) m1, .vpermi2q (r 13) (r 11) (r 15),
    .vmov (r 11) m0, .vpermi2q (r 11) (r 8) (r 12), .vmov (r 15) m1, .vpermi2q (r 15) (r 8) (r 12),
    .vmov (r 8) m0, .vpermi2q (r 8) (r 6) (r 10), .vmov (r 12) m1, .vpermi2q (r 12) (r 6) (r 10),
    .vmov (r 10) t1',
    .vmov t1' m0, .vpermi2q t1' (r 1) (r 5), .vmov (r 6) m1, .vpermi2q (r 6) (r 1) (r 5),
    .vmov (r 1) m0, .vpermi2q (r 1) (r 3) (r 7), .vmov (r 5) m1, .vpermi2q (r 5) (r 3) (r 7),
    .vmov (r 3) m0, .vpermi2q (r 3) (r 0) (r 4), .vmov (r 7) m1, .vpermi2q (r 7) (r 0) (r 4),
    .vmov (r 0) m0, .vpermi2q (r 0) t0 (r 2), .vmov (r 4) m1, .vpermi2q (r 4) t0 (r 2),
    .vmov (r 2) t1']

/-- Reverse the bytes of every lane, from the little-endian loads to the big-endian words SHA-256 reads. -/
def swapIn : List Instr :=
  .vload (tmp 2) (tableEntry bswapAvx512) :: (List.range 16).map fun t => .vshufb (ring t) (ring t) (tmp 2)

/--
Transpose the eight digest words back, so that each register holds two whole 32-byte digests.

Register k ends with digest 2k in its low half and digest 2k + 1 in its high half.
-/
def transposeOut : List Instr :=
  let h := home
  let t := tmp
  let m0 := tmp 5
  let m1 := tmp 6
  [.vload m0 (tableEntry (transposeMask 2)), .vload m1 (tableEntry (transposeMask 3)),
    .vmov (t 0) m0, .vmov (t 1) m0, .vpermi2d (t 0) (h 0) (h 4), .vpermi2d (t 1) (h 1) (h 5),
    .vmov (t 2) m1, .vmov (t 3) m1, .vpermi2d (t 2) (h 0) (h 4), .vpermi2d (t 3) (h 1) (h 5),
    .vmov (h 0) m0, .vmov (h 1) m0, .vpermi2d (h 0) (h 2) (h 6), .vpermi2d (h 1) (h 3) (h 7),
    .vmov (h 4) m1, .vmov (h 5) m1, .vpermi2d (h 4) (h 2) (h 6), .vpermi2d (h 5) (h 3) (h 7),
    .vshufps (h 6) (t 0) (t 1) 0x88, .vshufps (h 7) (t 0) (t 1) 0xDD,
    .vshufps (t 1) (t 2) (t 3) 0x88, .vshufps (t 0) (t 2) (t 3) 0xDD,
    .vshufps (t 2) (h 4) (h 5) 0x88, .vshufps (t 3) (h 4) (h 5) 0xDD,
    .vshufps (h 4) (h 0) (h 1) 0x88, .vshufps (h 5) (h 0) (h 1) 0xDD,
    .vmov (h 0) m0, .vmov (h 1) m0, .vpermi2d (h 0) (h 6) (h 4), .vpermi2d (h 1) (h 7) (h 5),
    .vmov (h 2) m1, .vmov (h 3) m1, .vpermi2d (h 2) (h 6) (h 4), .vpermi2d (h 3) (h 7) (h 5),
    .vmov (h 4) m0, .vmov (h 5) m0, .vpermi2d (h 4) (t 1) (t 2), .vpermi2d (h 5) (t 0) (t 3),
    .vmov (h 6) m1, .vmov (h 7) m1, .vpermi2d (h 6) (t 1) (t 2), .vpermi2d (h 7) (t 0) (t 3)]

/-- Byte-swap the digests and store them, sixty-four bytes per register. -/
def storeCode : List Instr :=
  .vload (tmp 2) (tableEntry bswapAvx512) ::
  (List.range 8).flatMap fun k => [.vshufb (home k) (home k) (tmp 2), .vstore ⟨out, 64 * k⟩ (home k)]

/-- The body of one batch: sixteen pairs in, sixteen digests out. -/
def batchCode (ls rs : Nat) : List Instr :=
  loadCode ls rs ++ transposeIn ++ swapIn ++
  -- The initial state in every lane.
  (List.range 8).map (fun j => .vload (home j) (tableEntry (ivAvx512 j))) ++
  (List.range 64).flatMap (fun t => firstRound t ++ (if t < 48 then scheduleCode t else [])) ++
  -- Feed the initial state forward, and keep the result for the second feed-forward.
  (List.range 8).flatMap (fun j => [.vaddMem (home j) (home j) (tableEntry (ivAvx512 j)), .vmov (ring j) (home j)]) ++
  (List.range 64).flatMap paddingRound ++
  (List.range 8).map (fun j => .vadd (home j) (home j) (ring j)) ++
  transposeOut ++ storeCode

/-- Instruction index of the batch loop's head, after the empty-count check. -/
def loopHead : Nat := 2

/--
The routine: sixteen digests per batch, for a count of batches.

On entry: rdi the output, rsi the left nodes, rdx the right nodes, rcx the batch count, r8 the constant table.

Consecutive left nodes sit ls bytes apart, and consecutive right nodes rs bytes apart:

- 64 and 64 for adjacent nodes of one level;
- 32 and 32 for two separate columns;
- 32 and 0 for a column against one fixed node.
-/
def program (ls rs : Nat) : Array Instr :=
  let tail := [.addImm left (16 * ls), .addImm right (16 * rs), .addImm out 512, .subImm count 1,
    .jnz loopHead]
  let finish := loopHead + (batchCode ls rs).length + tail.length
  (([.test count, .jz finish] ++ batchCode ls rs ++ tail ++ [.vzeroupper, .ret]) : List Instr).toArray

end Ssz.Native.Kernel.Avx512
