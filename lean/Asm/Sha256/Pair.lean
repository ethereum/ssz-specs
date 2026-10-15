import Asm.Sha256.Code

/-!
SHA-256 of two 32-byte nodes, the hash every Merkle tree level is built from.

A 64-byte message pads to exactly two blocks, and the second block never changes:

```text
    block 1:  left node (32 bytes) | right node (32 bytes)
    block 2:  0x80, 55 zero bytes, then the bit length 512 as 8 big-endian bytes
```

The second block's whole schedule is therefore a constant.
Each round adds its schedule word to its round constant ahead of time, so that block costs no schedule step and one fewer addition per round.
-/

namespace Ssz.Asm.Sha256

/-- The sixteen words of the padding block of a 64-byte message. -/
def padWords : Vector (BitVec 32) 16 :=
  #v[0x80000000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x200]

/-- The schedule of the padding block, all sixty-four words of it. -/
def padSchedule : Vector (BitVec 32) 64 :=
  #v[0x80000000, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x200,
    0x80000000, 0x1400000, 0x205000, 0x5088, 0x22000800, 0x22550014, 0x5089742, 0xa0000020,
    0x5a880000, 0x5c9400, 0x16d49d, 0xfa801f00, 0xd33225d0, 0x11675959, 0xf6e6bfda, 0xb30c1549,
    0x8b2b050, 0x9d7c4c27, 0xce2a393, 0x88e6e1ea, 0xa52b4335, 0x67a16f49, 0xd732016f, 0x4eeb2e91,
    0x5dbf55e5, 0x8eee2335, 0xe2bc5ec2, 0xa83f4394, 0x45ad78f7, 0x36f3d0cd, 0xd99c05e8, 0xb0511dc7,
    0x69bc7ac4, 0xbd11375b, 0xe3ba71e5, 0x3b209ff2, 0x18feee17, 0xe25ad9e7, 0x13375046, 0x515089d,
    0x4f0d0f04, 0x2627484e, 0x310128d2, 0xc668b434, 0x420841cc, 0x62d311b8, 0xe59ba771, 0x85a7a484]

/-- Round t's constant with the padding block's schedule word already added. -/
def fusedConstant (t : Nat) : BitVec 32 :=
  (Ssz.Sha256.roundConstants[t % 64]'(Nat.mod_lt _ (by decide))).toBitVec +
    padSchedule[t % 64]'(Nat.mod_lt _ (by decide))

/-- Initial word j of SHA-256. -/
def ivWord (j : Nat) : BitVec 32 :=
  (Ssz.Sha256.initialState[j % 8]'(Nat.mod_lt _ (by decide))).toBitVec

/-- The home of working word j at round zero, which is also its home after sixty-four rounds. -/
def stateHome (j : Nat) : Reg :=
  stateRegs[j % 8]'(Nat.mod_lt _ (by decide))

/-- The third argument register, holding the right node's address on entry. -/
abbrev a2 : Reg := 12

/-- Message word k of the pair: words 0 to 7 from the left node, 8 to 15 from the right node. -/
def loadPairWord (k : Nat) : List Instr :=
  if k < 8 then loadWordFrom k a1 (4 * k) else loadWordFrom k a2 (4 * (k - 8))

/-- Sixteen message words: eight from the left node, then eight from the right node. -/
def loadPairCode : List Instr :=
  (List.range 16).flatMap loadPairWord

/-- Initial word j, built from immediates in its home. -/
def ivWordCode (j : Nat) : List Instr :=
  [.lui (stateHome j) (upper (ivWord j)), .addiw (stateHome j) (stateHome j) (lower (ivWord j))]

/-- The initial state, built from immediates into the eight homes. -/
def ivCode : List Instr :=
  (List.range 8).flatMap ivWordCode

/-- Initial word j, rebuilt from immediates and added to its working word. -/
def ivForwardWord (j : Nat) : List Instr :=
  [.lui t0 (upper (ivWord j)), .addiw t0 t0 (lower (ivWord j)), .addw (stateHome j) (stateHome j) t0]

/-- The first feed-forward, adding the initial state rebuilt from immediates. -/
def ivForwardCode : List Instr :=
  (List.range 8).flatMap ivForwardWord

/-- Chaining word j, copied into ring slot j. -/
def keepWord (j : Nat) : Instr :=
  .addi (ringSlot j) (stateHome j) 0

/-- The chaining state after the first block, kept in the first eight ring slots. -/
def keepCode : List Instr :=
  -- The ring is free for the rest of the hash, since the second schedule is folded into constants.
  (List.range 8).map keepWord

/-- One round whose schedule word is folded into its constant, in 30 instructions. -/
def roundFusedCodeWith (a b d e f g h q p : Reg) (k : BitVec 32) : List Instr :=
  rotations3Code t0 t1 e 14 5 6 ++
  [.addw h h t0,
    .xor t0 f g, .and t0 t0 e, .xor t0 t0 g, .addw h h t0,
    .lui t0 (upper k), .addiw t0 t0 (lower k), .addw h h t0,
    .addw d d h] ++
  rotations3Code t0 t1 a 9 11 2 ++
  [.addw h h t0,
    .xor p a b, .and q q p, .xor q q b, .addw h h q]

/-- Round i of the padding block. -/
def roundFusedCode (i : Nat) : List Instr :=
  roundFusedCodeWith (wordHome i 0) (wordHome i 1) (wordHome i 3) (wordHome i 4) (wordHome i 5)
    (wordHome i 6) (wordHome i 7) (carry i) (carry (i + 1)) (fusedConstant i)

/-- The padding block's rounds below a given count. -/
def fusedRoundsCode : Nat → List Instr
  | 0 => []
  | i + 1 => fusedRoundsCode i ++ roundFusedCode i

/-- Kept chaining word j, added to its working word. -/
def keptForwardWord (j : Nat) : Instr :=
  .addw (stateHome j) (stateHome j) (ringSlot j)

/-- The second feed-forward, adding the kept chaining state. -/
def keptForwardCode : List Instr :=
  (List.range 8).map keptForwardWord

/-- Digest word j, written big-endian at offset 4j from the address in t1. -/
def digestWord (j : Nat) : List Instr :=
  let s := stateHome j
  let off := fun (b : Nat) => BitVec.ofNat 12 (4 * j + b)
  -- Most significant byte first, as SHA-256 prints a word.
  [.srliw t0 s 24, .sb t0 t1 (off 0), .srliw t0 s 16, .sb t0 t1 (off 1),
    .srliw t0 s 8, .sb t0 t1 (off 2), .sb s t1 (off 3)]

/-- The digest written big-endian to the address in a frame slot. -/
def digestCode (outSlot : Nat) : List Instr :=
  .ld t1 sp (BitVec.ofNat 12 outSlot) :: (List.range 8).flatMap digestWord

/--
SHA-256 of the 32 bytes at a1 followed by the 32 bytes at a2, written to the address in a frame slot.

Every register the routine may use is clobbered except the stack pointer.
-/
def pairCode (outSlot : Nat) : List Instr :=
  loadPairCode ++ ivCode ++ [.xor (carry 0) (wordHome 0 1) (wordHome 0 2)] ++ roundsCode 64 ++
    ivForwardCode ++ keepCode ++ [.xor (carry 0) (wordHome 0 1) (wordHome 0 2)] ++
    fusedRoundsCode 64 ++ keptForwardCode ++ digestCode outSlot

end Ssz.Asm.Sha256
