import SszNative.Driver.Hash

/-!
Gathering a field out of fixed-width records, on the fastest routine its width has.

The shape is three words in memory: the field's width, the bytes from one field's end to the next field, and the zero
bytes after each copy.
A field of 1, 2, 4, 8, 16 or 32 bytes into a 32-byte slot, and a 48-byte key into a 64-byte slot, have routines
with one load and one store per record, which need AVX.
Every other shape takes the general byte copy.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt

namespace GatherVars
/-- The output address. -/
abbrev out : Var := ⟨0⟩
/-- The first field's address. -/
abbrev src : Var := ⟨1⟩
/-- How many records. -/
abbrev count : Var := ⟨2⟩
/-- The address of the shape words. -/
abbrev shape : Var := ⟨3⟩
/-- The context the caller filled. -/
abbrev ctx : Var := ⟨4⟩
/-- The field's width. -/
abbrev width : Var := ⟨5⟩
/-- The bytes from one field's end to the next. -/
abbrev skip : Var := ⟨6⟩
/-- The zero bytes after each copy. -/
abbrev pad : Var := ⟨7⟩
/-- Which routine ran: zero for the general copy, one for an AVX routine. -/
abbrev path : Var := ⟨8⟩
/-- The sink for the routines' zero results. -/
abbrev sink : Var := ⟨9⟩
/-- Whether AVX is usable. -/
abbrev avx : Var := ⟨10⟩

/-- A call to one gather routine with the record arguments. -/
def gatherCall (name : String) : Stmt :=
  callInto sink name [out, src, count, width, skip, pad]

/--
Gather a field of each record: arguments out, src, count, shape, ctx.

Returns which routine ran: zero for the general copy, one for an AVX routine.
-/
def _root_.EthLib.Consensus.Ssz.Native.Driver.gatherField : Fn :=
  -- The AVX routines by width, each for a 32-byte slot.
  let narrow : List Stmt := [1, 2, 4, 8, 16, 32].map fun w =>
    when (eq width (w : Nat)) [gatherCall s!"ssz_gather_{w}", path ::= 1]
  { params := 5, vars := 11, result := path,
    body := .block [width ::= ld shape, skip ::= ld (shape + 8), pad ::= ld (shape + 16), path ::= 0,
      avx ::= ne (ld ctx &&& 4) 0,
      when avx [when (eq (width + pad) 32) narrow,
        when (eq width 48 &&& eq pad 16) [gatherCall "ssz_gather_key", path ::= 1]],
      when (eq path 0) [gatherCall "ssz_gather"]] }
end GatherVars

end EthLib.Consensus.Ssz.Native.Driver
