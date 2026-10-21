import SszNative.Asm.Instr
import Ssz.Hash.Sha256

/-!
What each instruction does, following the Intel Software Developer's Manual.

The model is trusted: the proofs show that the programs compute the specification on it.

Memory is a function from addresses to bytes, and an access never wraps past the top of the address space.
User-space addresses on x86-64 sit far below that top, so no real access wraps either.

The model leaves out what the callers rule out instead:

- faults on unmapped memory, since the bindings only pass ranges inside live arrays;
- faults on missing instructions, since the bindings check the processor first;
- faults on misaligned legacy SSE memory operands, since those only read the table, which is aligned to 64 bytes;
- the direction flag, which the calling convention keeps clear;
- the stack, which no routine touches, and the return address, which only the final return uses.
-/

namespace Ssz.Native.Asm

open Ssz.Sha256 (rotr sigma0 sigma1 bigSigma0 bigSigma1 choose majority)

/-- A vector register's sixteen 32-bit lanes: lanes 0 to 3 are its xmm part, and lanes 0 to 7 its ymm part. -/
abbrev Lanes := Fin 16 → UInt32

/-- Whether the routine is still running, returned to its caller, or reached an address holding no instruction. -/
inductive Status where
  | running
  | returned
  | faulted
  deriving Repr, DecidableEq, Inhabited

/-- The machine: registers, the zero flag, memory, and where execution is. -/
structure State where
  /-- The general-purpose registers. -/
  gpr : Gpr → UInt64
  /-- The vector registers. -/
  vec : Vreg → Lanes
  /-- The zero flag, the only flag the programs branch on. -/
  zf : Bool
  /-- Memory, one byte per address. -/
  mem : Nat → UInt8
  /-- The index of the next instruction. -/
  pc : Nat
  /-- Whether execution goes on. -/
  status : Status

/-- A function with one argument's value replaced. -/
def assign {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-- The address a memory operand names. -/
def State.addr (s : State) (m : Mem) : Nat :=
  (s.gpr m.base).toNat + m.disp

/-- Four bytes from an address, read as a little-endian word. -/
def readWord (mem : Nat → UInt8) (a : Nat) : UInt32 :=
  (mem a).toUInt32 ||| (mem (a + 1)).toUInt32 <<< 8 ||| (mem (a + 2)).toUInt32 <<< 16 |||
    (mem (a + 3)).toUInt32 <<< 24

/-- Byte k of a word, the least significant first. -/
def wordByte (w : UInt32) (k : Nat) : UInt8 :=
  (w >>> (8 * (k % 4)).toUInt32).toUInt8

/-- The lane holding byte k of a register's 64 bytes. -/
def laneOf (k : Nat) : Fin 16 :=
  ⟨k / 4 % 16, by omega⟩

/-- Byte k of a register, the lowest lane's least significant byte first. -/
def laneByte (v : Lanes) (k : Nat) : UInt8 :=
  wordByte (v (laneOf k)) k

/-- Lanes built from a function giving each byte of the register. -/
def ofBytes (byte : Nat → UInt8) : Lanes :=
  fun l => (byte (4 * l)).toUInt32 ||| (byte (4 * l + 1)).toUInt32 <<< 8 |||
    (byte (4 * l + 2)).toUInt32 <<< 16 ||| (byte (4 * l + 3)).toUInt32 <<< 24

/-- Memory after writing a count of bytes from an address. -/
def store (mem : Nat → UInt8) (a count : Nat) (byte : Nat → UInt8) : Nat → UInt8 :=
  fun x => if a ≤ x ∧ x < a + count then byte (x - a) else mem x

/-- Memory after copying a count of bytes forward, one at a time, so an overlapping copy repeats its source. -/
def copyForward (mem : Nat → UInt8) (dst src : Nat) : (count : Nat) → Nat → UInt8
  | 0 => mem
  | count + 1 => copyForward (assign mem dst (mem src)) (dst + 1) (src + 1) count

/-- Any bitwise function of three words, given as its truth table: bit 4a + 2b + c is the output for inputs a, b, c. -/
def ternlog (table : UInt8) (a b c : UInt32) : UInt32 :=
  -- Each set bit of the table contributes the bits where the inputs take its pattern.
  let term (k : UInt8) (x : UInt32) : UInt32 := if (table >>> k) &&& 1 == 1 then x else 0
  term 0 (~~~a &&& ~~~b &&& ~~~c) ||| term 1 (~~~a &&& ~~~b &&& c) ||| term 2 (~~~a &&& b &&& ~~~c) |||
    term 3 (~~~a &&& b &&& c) ||| term 4 (a &&& ~~~b &&& ~~~c) ||| term 5 (a &&& ~~~b &&& c) |||
    term 6 (a &&& b &&& ~~~c) ||| term 7 (a &&& b &&& c)

/-- Lanes chosen by a function of their index, keeping the destination's lanes from 4 up. -/
def low (keep : Lanes) (f : Fin 16 → UInt32) : Lanes :=
  fun l => if l.val < 4 then f l else keep l

/-- A byte shuffle within each 16-byte block: an index byte with its top bit set gives zero. -/
def shuffleBytes (src mask : Lanes) (k : Nat) : UInt8 :=
  let index := laneByte mask k
  if index &&& 0x80 != 0 then 0 else laneByte src (16 * (k / 16) + (index &&& 0x0F).toNat)

/-- Two SHA-256 rounds: the state as ABEF in one register and CDGH in the other, the two words plus constants given. -/
def rounds2 (cdgh abef : Lanes) (wk0 wk1 : UInt32) : Lanes :=
  let round (s : UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32 × UInt32) (wk : UInt32) :=
    let (a, b, c, d, e, f, g, h) := s
    let t1 := choose e f g + bigSigma1 e + wk + h
    (t1 + majority a b c + bigSigma0 a, a, b, c, t1 + d, e, f, g)
  let s0 := (abef 3, abef 2, cdgh 3, cdgh 2, abef 1, abef 0, cdgh 1, cdgh 0)
  let s1 := round s0 wk0
  let s2 := round s1 wk1
  -- The new A and E words, oldest first from the bottom.
  fun l => match l.val with
    | 0 => s1.2.2.2.2.1
    | 1 => s2.2.2.2.2.1
    | 2 => s1.1
    | 3 => s2.1
    | _ => cdgh l

/-- One instruction, apart from where it sends control. -/
def exec1 (i : Instr) (s : State) : State :=
  let vec := s.vec
  let set (d : Vreg) (v : Lanes) : State := { s with vec := assign vec d v }
  match i with
  | .addImm r imm =>
    let v := s.gpr r + imm.toUInt64
    { s with gpr := assign s.gpr r v, zf := v == 0 }
  | .subImm r imm =>
    let v := s.gpr r - imm.toUInt64
    { s with gpr := assign s.gpr r v, zf := v == 0 }
  | .test r => { s with zf := s.gpr r == 0 }
  | .jz _ | .jnz _ | .ret => s
  -- Leaving the vector unit clears the upper parts of the first sixteen registers.
  | .vzeroupper => { s with vec := fun r l => if r.val < 16 ∧ 4 ≤ l.val then 0 else vec r l }
  | .movReg d r => { s with gpr := assign s.gpr d (s.gpr r) }
  | .zeroReg r => { s with gpr := assign s.gpr r 0, zf := true }
  | .addReg d r =>
    let v := s.gpr d + s.gpr r
    { s with gpr := assign s.gpr d v, zf := v == 0 }
  | .repMovsb =>
    let n := s.gpr .rcx
    { s with
      mem := copyForward s.mem (s.gpr .rdi).toNat (s.gpr .rsi).toNat n.toNat
      gpr := assign (assign (assign s.gpr .rdi (s.gpr .rdi + n))
        .rsi (s.gpr .rsi + n)) .rcx 0 }
  | .repStosb =>
    let n := s.gpr .rcx
    { s with
      mem := store s.mem (s.gpr .rdi).toNat n.toNat fun _ => (s.gpr .rax).toUInt8
      gpr := assign (assign s.gpr .rdi (s.gpr .rdi + n)) .rcx 0 }
  -- The narrow loads zero-extend into the whole register.
  | .loadByte d m => { s with gpr := assign s.gpr d (s.mem (s.addr m)).toUInt64 }
  | .loadWord d m =>
    { s with gpr := assign s.gpr d ((s.mem (s.addr m)).toUInt64 ||| (s.mem (s.addr m + 1)).toUInt64 <<< 8) }
  | .vfromGpr d r => set d fun l => if l.val == 0 then (s.gpr r).toUInt32 else 0
  | .vload4 d m => set d fun l => if l.val < 1 then readWord s.mem (s.addr m + 4 * l.val) else 0
  | .vload8 d m => set d fun l => if l.val < 2 then readWord s.mem (s.addr m + 4 * l.val) else 0
  | .vload16 d m => set d fun l => if l.val < 4 then readWord s.mem (s.addr m + 4 * l.val) else 0
  | .vstoreHalf m r => { s with mem := store s.mem (s.addr m) 32 (laneByte (vec r)) }
  | .vload d m => set d fun l => readWord s.mem (s.addr m + 4 * l.val)
  | .vstore m r => { s with mem := store s.mem (s.addr m) 64 (laneByte (vec r)) }
  -- The 256-bit load clears every bit above it.
  | .vloadHalf d m => set d fun l => if l.val < 8 then readWord s.mem (s.addr m + 4 * l.val) else 0
  | .vinsertHigh d r m =>
    set d fun l => if l.val < 8 then vec r l else readWord s.mem (s.addr m + 4 * (l.val - 8))
  | .vmov d r => set d (vec r)
  | .vadd d a b => set d fun l => vec a l + vec b l
  | .vaddMem d a m => set d fun l => vec a l + readWord s.mem (s.addr m + 4 * l.val)
  | .vror d a k => set d fun l => rotr (vec a l) k.toUInt32
  | .vshr d a k => set d fun l => if k < 32 then vec a l >>> k.toUInt32 else 0
  | .vternlog d a b t => set d fun l => ternlog t.toNat.toUInt8 (vec d l) (vec a l) (vec b l)
  | .vshufb d a b => set d (ofBytes (shuffleBytes (vec a) (vec b)))
  | .vshufps d a b imm =>
    -- Within each 128-bit block, two lanes of the first source and then two of the second.
    set d fun l =>
      let base := 4 * (l.val / 4)
      let field := (imm.toNat >>> (2 * (l.val % 4))) % 4
      let src := if l.val % 4 < 2 then vec a else vec b
      src ⟨base + field, by omega⟩
  | .vpermi2q d a b =>
    -- Each 64-bit index: three bits pick a 64-bit lane, and the fourth picks the source.
    set d fun l =>
      let index := (vec d ⟨2 * (l.val / 2), by omega⟩).toNat
      let src := if index / 8 % 2 == 0 then vec a else vec b
      src ⟨2 * (index % 8) + l.val % 2, by omega⟩
  | .vpermi2d d a b =>
    -- Each index: four bits pick a lane, and the fifth picks the source.
    set d fun l =>
      let index := (vec d l).toNat
      let src := if index / 16 % 2 == 0 then vec a else vec b
      src ⟨index % 16, by omega⟩
  -- The legacy SSE instructions below write the low 128 bits and keep the rest.
  | .movdqu d m => set d (low (vec d) fun l => readWord s.mem (s.addr m + 4 * l.val))
  | .movdquStore m r => { s with mem := store s.mem (s.addr m) 16 (laneByte (vec r)) }
  | .movdqa d r => set d (low (vec d) (vec r))
  | .paddd d r => set d (low (vec d) fun l => vec d l + vec r l)
  | .padddMem d m => set d (low (vec d) fun l => vec d l + readWord s.mem (s.addr m + 4 * l.val))
  | .pshufb d r => set d (low (vec d) (ofBytes (shuffleBytes (vec d) (vec r))))
  | .pshufd d r imm => set d (low (vec d) fun l => vec r ⟨(imm.toNat >>> (2 * l.val)) % 4, by omega⟩)
  | .palignr d r k =>
    -- The destination above the source, as 32 bytes, shifted right and cut to its low 16.
    let joined (j : Nat) : UInt8 :=
      if j < 16 then laneByte (vec r) j else if j < 32 then laneByte (vec d) (j - 16) else 0
    set d (low (vec d) (ofBytes fun j => joined (j + k)))
  | .pblendw d r imm =>
    -- Each set bit of the immediate takes one 16-bit half-lane from the source.
    let half (v : Lanes) (w : Nat) : UInt32 := (v ⟨w / 2 % 16, by omega⟩ >>> (16 * (w % 2)).toUInt32) &&& 0xFFFF
    let pick (w : Nat) : UInt32 := if (imm.toNat >>> w) % 2 == 1 then half (vec r) w else half (vec d) w
    set d (low (vec d) fun l => pick (2 * l.val) ||| pick (2 * l.val + 1) <<< 16)
  | .sha256rnds2 d r => set d (rounds2 (vec d) (vec r) (vec 0 0) (vec 0 1))
  | .sha256msg1 d r =>
    let w (k : Nat) : UInt32 := if h : k < 4 then vec d ⟨k, by omega⟩ else vec r 0
    set d fun l => if l.val < 4 then w l.val + sigma0 (w (l.val + 1)) else vec d l
  | .sha256msg2 d r =>
    let w16 := vec d 0 + sigma1 (vec r 2)
    let w17 := vec d 1 + sigma1 (vec r 3)
    let w18 := vec d 2 + sigma1 w16
    let w19 := vec d 3 + sigma1 w17
    set d fun l => match l.val with
      | 0 => w16
      | 1 => w17
      | 2 => w18
      | 3 => w19
      | _ => vec d l

/-- One step of a program: the instruction at the current index, then on to the next or to a branch target. -/
def step (program : Array Instr) (s : State) : State :=
  if s.status != .running then s
  else match program[s.pc]? with
    | none => { s with status := .faulted }
    | some .ret => { s with status := .returned }
    | some (.jz t) => { s with pc := if s.zf then t else s.pc + 1 }
    | some (.jnz t) => { s with pc := if s.zf then s.pc + 1 else t }
    | some i => { exec1 i s with pc := s.pc + 1 }

/-- A number of steps of a program. -/
def run (program : Array Instr) : (steps : Nat) → State → State
  | 0, s => s
  | steps + 1, s => run program steps (step program s)

/-- A list of instructions run in order, with no branch among them. -/
def exec : List Instr → State → State
  | [], s => s
  | i :: rest, s => exec rest (exec1 i s)

end Ssz.Native.Asm
