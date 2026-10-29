import SszNative.Proofs.Driver.Root.ByteList
import SszNative.Proofs.Driver.Root.Progressive

/-!
The bit list driver writes the Lean root of a bit list, bounded or progressive.

It finds the closing bit as the last byte's highest set bit, gathers the bytes the bits fill, and clears the closing bit
when it shares a byte with them.
The nodes are then rooted at the limit's depth, or on a progressive spine, and the bit count is mixed in.
-/

namespace Ssz.Native.Driver

open Ssz Ssz.Native.Ir Ssz.Native.Ir.Expr Ssz.Native.Ir.Stmt Ssz.Native.Asm

/-! ### Bytes and bits -/

/-- A byte with one bit cleared, as the driver computes it on a word. -/
theorem clearBit_table : ∀ n : Fin 256, ∀ h : Fin 8,
    (((UInt8.ofNat n.val).toUInt64 &&& (255 ^^^ (UInt64.ofNat (2 ^ h.val)))).toUInt8) =
      (UInt8.ofNat n.val) &&& ~~~((1 : UInt8) <<< UInt8.ofNat h.val) := by
  decide +kernel

/-- A byte whose quotient by a power of two is one has that power's bit as its highest. -/
theorem highestBit_table : ∀ n : Fin 256, ∀ h : Fin 8, n.val / 2 ^ h.val = 1 → highestBit (UInt8.ofNat n.val) = h.val := by
  decide +kernel

/-- Halving a byte above one keeps it at least one, below its eighth halving. -/
theorem halve_table : ∀ n : Fin 256, ∀ h : Fin 8, 1 < n.val / 2 ^ h.val → h.val + 1 < 8 ∧ 1 ≤ n.val / 2 ^ (h.val + 1) := by
  decide +kernel

/-- A byte is the byte of its value. -/
theorem uint8_ofNat_toNat (x : UInt8) : UInt8.ofNat x.toNat = x := UInt8.ofNat_toNat

/-- One byte read as a word is the byte's value. -/
theorem readLE_byte (mem : Memory) (a : Nat) : readLE mem a 1 = UInt64.ofNat (mem a).toNat := by
  apply UInt64.toNat_inj.mp
  simp [readLE]

/-- A store of one byte changes only that byte. -/
theorem store_one (mem : Memory) (a : Nat) (f : Nat → UInt8) (x : Nat) :
    store mem a 1 f x = if x = a then f 0 else mem x := by
  simp only [Asm.store]
  by_cases h : x = a
  · subst h; rw [if_pos ⟨Nat.le_refl _, by omega⟩, if_pos rfl, Nat.sub_self]
  · rw [if_neg (by omega), if_neg h]

/-- Setting a byte of a buffer, then reading it back. -/
theorem get!_set!_self (x : ByteArray) (i : Nat) (v : UInt8) (h : i < x.size) : (x.set! i v).get! i = v := by
  simp only [ByteArray.set!, ByteArray.get!]
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ _ (by simpa using h), Array.getElem_setIfInBounds_self]

/-- Setting a byte of a buffer leaves the others. -/
theorem get!_set!_ne (x : ByteArray) (i j : Nat) (v : UInt8) (h : j ≠ i) : (x.set! i v).get! j = x.get! j := by
  simp only [ByteArray.set!, ByteArray.get!]
  rw [Array.set!_eq_setIfInBounds]
  by_cases hj : j < x.data.size
  · rw [getElem!_pos (x.data.setIfInBounds i v) j (by simpa using hj), getElem!_pos x.data j hj,
      Array.getElem_setIfInBounds_ne hj (Ne.symm h)]
  · rw [getElem!_neg (x.data.setIfInBounds i v) j (by simpa using hj), getElem!_neg x.data j hj]

/-- Setting a byte keeps a buffer's size. -/
theorem size_set! (x : ByteArray) (i : Nat) (v : UInt8) : (x.set! i v).size = x.size := by
  show (x.data.set! i v).size = x.data.size
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- The exclusive or of two values. -/
theorem eval_xor {w : World} {env : Env} {mem : Memory} {a b : Expr} {x y : UInt64} (ha : eval w env mem a = some x)
    (hb : eval w env mem b = some y) : eval w env mem (a ^^^ b) = some (x ^^^ y) := by
  show eval w env mem (.op .xor a b) = _
  simp only [eval, ha, hb, aluResult, Option.bind_eq_bind, Option.bind]
  rfl

/-- What decoding a bit list establishes: a last byte other than zero, and the bit count its highest bit gives. -/
theorem bits_decoded {lim : Option Nat} {b : ByteArray} {start stop : Nat} {bits : Array Bool}
    (inside : stop ≤ b.size) (read : unpackDelimited lim (slice b start stop) = .ok bits) :
    start < stop ∧ b.get! (stop - 1) ≠ 0 := by
  obtain ⟨nonempty, nz, -⟩ := Ssz.unpackDelimited_ok read
  rw [slice_size b start stop inside] at nonempty nz
  refine ⟨by omega, ?_⟩
  rw [slice_getElem! b start stop _ inside (by omega), show start + (stop - start - 1) = stop - 1 by omega] at nz
  exact nz

/-! ### Finding the bits -/

/-- The driver's statements up to the tree: the closing bit, the counts, the gather, and the cleared bit. -/
abbrev bitsHead : List Stmt :=
  [RootBits.v ::= ld1 (RootBits.src + RootBits.size - 1), RootBits.hb ::= 0, RootBits.pw ::= 1,
    while_ (lt 1 RootBits.v) [RootBits.v ::= RootBits.v / 2, RootBits.hb ::= RootBits.hb + 1,
      RootBits.pw ::= RootBits.pw + RootBits.pw],
    RootBits.count ::= 8 * (RootBits.size - 1) + RootBits.hb, RootBits.bytes ::= (RootBits.count + 7) / 8,
    RootBits.nodes ::= ceilDiv RootBits.bytes 32, RootBits.buf ::= RootBits.scratch + 64,
    callInto RootBits.sink "ssz_gather"
      [RootBits.buf, RootBits.src, 1, RootBits.bytes, 0, 32 * RootBits.nodes + 32 - RootBits.bytes],
    when (ne (RootBits.count % 8) 0) [st1 (RootBits.buf + RootBits.count / 8)
      (ld1 (RootBits.buf + RootBits.count / 8) &&& (255 ^^^ RootBits.pw))]]

set_option maxHeartbeats 2000000 in
/--
The statements before the tree leave the bit list's nodes at a buffer a node past the scratch's first two.

The range is not empty and its last byte is not zero, as decoding requires.
Memory changes only in the buffer.
-/
theorem bitsHead_runs {m : Module} {w : World} (gmod : GatherModule m) {sp : Nat} (room : w.stackLo + 8 ≤ sp)
    {mem : Memory} {base start stop out scratch ctx p : Nat} {b : ByteArray} (holds : Holds mem base b)
    (bAcc : w.access base b.size = true) (inside : stop ≤ b.size) (small : 64 * b.size + 128 < 2 ^ 64)
    (usize : USize.size = 2 ^ 64) (nonempty : start < stop) (nz : b.get! (stop - 1) ≠ 0)
    (bufAcc : w.access (scratch + 64) (32 * nodesFor (stop - start) + 32) = true)
    (bufApart : Apart (scratch + 64, 32 * nodesFor (stop - start) + 32) (base, b.size))
    {env : Env} (ev : RangeEnv env p (base + start) (stop - start) out scratch ctx) :
    ∃ env' mem', Runs m w sp env mem (.block bitsHead) env' mem' ∧
      RangeEnv env' p (base + start) (stop - start) out scratch ctx ∧
      env' 9 = UInt64.ofNat (bitCount b start stop) ∧
      env' 11 = UInt64.ofNat (nodesFor ((bitCount b start stop + 7) / 8)) ∧
      env' 12 = UInt64.ofNat (scratch + 64) ∧
      Holds mem' (scratch + 64) (bitNodes b start (bitCount b start stop)) ∧
      ∀ a, ¬ (scratch + 64 ≤ a ∧ a < scratch + 64 + (32 * nodesFor (stop - start) + 32)) → mem' a = mem a := by
  have ab := access_bound bAcc
  have abuf := access_bound bufAcc
  -- The last byte.
  generalize hx : b.get! (stop - 1) = x at nz
  have xs := x.toNat_lt
  have xnz : x.toNat ≠ 0 := fun h => nz (by rw [← uint8_ofNat_toNat x, h]; rfl)
  have last : mem (base + start + (stop - start) - 1) = x := by
    rw [show base + start + (stop - start) - 1 = base + (stop - 1) by omega, holds _ (by omega), hx]
  have e1 : eval w env mem (ld1 (RootBits.src + RootBits.size - 1)) = some (UInt64.ofNat x.toNat) := by
    rw [eval_ld1_of (eval_sub (eval_add (eval_var ev.src) (eval_var ev.size)) (eval_lit 1) (by omega))
      (access_sub bAcc (by omega) (by omega)), readLE_byte, last]
  have s1 := Runs.set' (m := m) (w := w) (sp := sp) (x := 6) e1
  have s2 := Runs.set' (m := m) (w := w) (sp := sp) (env := Asm.assign env 6 (UInt64.ofNat x.toNat)) (mem := mem)
    (x := 7) (eval_lit 0)
  have s3 := Runs.set' (m := m) (w := w) (sp := sp)
    (env := Asm.assign (Asm.assign env 6 (UInt64.ofNat x.toNat)) 7 (UInt64.ofNat 0)) (mem := mem) (x := 8)
    (eval_lit 1)
  -- The highest bit, by halving the byte down to one.
  let inv : Env → Memory → Prop := fun e mm => mm = mem ∧ RangeEnv e p (base + start) (stop - start) out scratch ctx ∧
    ∃ h, h < 8 ∧ e 6 = UInt64.ofNat (x.toNat / 2 ^ h) ∧ e 7 = UInt64.ofNat h ∧ e 8 = UInt64.ofNat (2 ^ h) ∧
      1 ≤ x.toNat / 2 ^ h
  have start0 : inv (Asm.assign (Asm.assign (Asm.assign env 6 (UInt64.ofNat x.toNat)) 7 (UInt64.ofNat 0)) 8
      (UInt64.ofNat 1)) mem :=
    ⟨rfl, ((ev.write _ (by decide)).write _ (by decide)).write _ (by decide), 0, by decide,
      by simp [Asm.assign], by simp [Asm.assign], by simp [Asm.assign], by simp; omega⟩
  obtain ⟨e4, mm4, run4, ⟨same4, ev4, h, h8, hv, hh, hp, one⟩, exit⟩ := Ends.loop (m := m) (w := w) (sp := sp)
    (c := lt 1 RootBits.v) (body := .block [RootBits.v ::= RootBits.v / 2, RootBits.hb ::= RootBits.hb + 1,
      RootBits.pw ::= RootBits.pw + RootBits.pw]) inv (fun e _ => (e 6).toNat) start0
    (fun e mm ⟨_, _, h, h8, hv, _⟩ => ⟨_, eval_lt (eval_lit 1) (eval_var hv) (by decide)
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))⟩)
    (by
      rintro e mm v ⟨same, ev', h, h8, hv, hh, hp, one⟩ hc nz'
      have q := Nat.lt_of_le_of_lt (Nat.div_le_self x.toNat (2 ^ h)) xs
      have c := eval_lt (w := w) (env := e) (mem := mm) (eval_lit 1) (eval_var hv) (by decide) (by omega)
      rw [hc] at c
      have big : 1 < x.toNat / 2 ^ h := by
        by_cases g : 1 < x.toNat / 2 ^ h
        · exact g
        · rw [if_neg g] at c; cases c; exact absurd rfl nz'
      obtain ⟨h8', one'⟩ := halve_table ⟨x.toNat, xs⟩ ⟨h, h8⟩ big
      have half : x.toNat / 2 ^ h / 2 = x.toNat / 2 ^ (h + 1) := by rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
      have pw : 2 ^ h + 2 ^ h = 2 ^ (h + 1) := by rw [Nat.pow_succ]; omega
      have pws : 2 ^ (h + 1) < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
      have r1 := Runs.set' (m := m) (w := w) (sp := sp) (env := e) (mem := mm) (x := 6)
        (eval_div (eval_var hv) (eval_lit 2) (by omega) (by decide) (by decide))
      have r2 := Runs.set' (m := m) (w := w) (sp := sp) (env := Asm.assign e 6 (UInt64.ofNat (x.toNat / 2 ^ h / 2)))
        (mem := mm) (x := 7)
        (eval_add (eval_var (show Asm.assign e 6 _ 7 = _ by rw [assign_ne (by decide)]; exact hh)) (eval_lit 1))
      have r3 := Runs.set' (m := m) (w := w) (sp := sp)
        (env := Asm.assign (Asm.assign e 6 (UInt64.ofNat (x.toNat / 2 ^ h / 2))) 7 (UInt64.ofNat (h + 1)))
        (mem := mm) (x := 8)
        (eval_add (eval_var (show Asm.assign (Asm.assign e 6 _) 7 _ 8 = _ by
            rw [assign_ne (by decide), assign_ne (by decide)]; exact hp))
          (eval_var (show Asm.assign (Asm.assign e 6 _) 7 _ 8 = _ by
            rw [assign_ne (by decide), assign_ne (by decide)]; exact hp)))
      refine ⟨_, mm, Runs.block_cons r1 (Runs.block_cons r2 (Runs.block_cons r3 (Runs.block_nil _ _ _ _ _))),
        ⟨same, ((ev'.write _ (by decide)).write _ (by decide)).write _ (by decide), h + 1, h8', ?_, ?_, ?_, one'⟩, ?_⟩
      · rw [assign_ne (by decide), assign_ne (by decide), assign_eq, half]
      · rw [assign_ne (by decide), assign_eq]
      · rw [assign_eq, pw]
      · show (Asm.assign (Asm.assign (Asm.assign e 6 _) 7 _) 8 _ 6).toNat < (e 6).toNat
        rw [assign_ne (by decide), assign_ne (by decide), assign_eq, hv, ofNat_toNat (by omega),
          ofNat_toNat (by omega)]
        omega)
  rw [same4] at run4
  -- The loop stops at one: the highest bit.
  have q := Nat.lt_of_le_of_lt (Nat.div_le_self x.toNat (2 ^ h)) xs
  rw [eval_lt (eval_lit 1) (eval_var hv) (by decide) (by omega)] at exit
  have isOne : x.toNat / 2 ^ h = 1 := by
    by_cases g : 1 < x.toNat / 2 ^ h
    · rw [if_pos g] at exit; cases exit
    · omega
  have top : highestBit x = h := by
    have := highestBit_table ⟨x.toNat, xs⟩ ⟨h, h8⟩ isOne
    rwa [uint8_ofNat_toNat] at this
  have counted : bitCount b start stop = 8 * (stop - start - 1) + h := by
    simp only [bitCount]; rw [hx, top]
  rw [counted]
  -- The counts.
  generalize hc : 8 * (stop - start - 1) + h = count
  have cb : count ≤ 8 * (stop - start) := by omega
  have e5 : eval w e4 mem (8 * (RootBits.size - 1) + RootBits.hb) = some (UInt64.ofNat count) := by
    rw [← hc]
    exact eval_add (eval_mul (eval_lit 8) (eval_sub (eval_var ev4.size) (eval_lit 1) (by omega))) (eval_var hh)
  have s5 := Runs.set' (m := m) (w := w) (sp := sp) (x := 9) e5
  have c5 : Asm.assign e4 9 (UInt64.ofNat count) 9 = UInt64.ofNat count := assign_eq
  have ev5 := ev4.write (x := 9) (UInt64.ofNat count) (by decide)
  have p5 : Asm.assign e4 9 (UInt64.ofNat count) 8 = UInt64.ofNat (2 ^ h) := by rw [assign_ne (by decide)]; exact hp
  generalize Asm.assign e4 9 (UInt64.ofNat count) = E5 at s5 c5 ev5 p5
  have s6 := Runs.set' (m := m) (w := w) (sp := sp) (env := E5) (mem := mem) (x := 10)
    (eval_div (eval_add (eval_var c5) (eval_lit 7)) (eval_lit 8) (by omega) (by decide) (by decide))
  generalize hy : (count + 7) / 8 = bytes at s6
  have yb : bytes ≤ stop - start := by omega
  have c6 : Asm.assign E5 10 (UInt64.ofNat bytes) 9 = UInt64.ofNat count := by rw [assign_ne (by decide)]; exact c5
  have y6 : Asm.assign E5 10 (UInt64.ofNat bytes) 10 = UInt64.ofNat bytes := assign_eq
  have ev6 := ev5.write (x := 10) (UInt64.ofNat bytes) (by decide)
  have p6 : Asm.assign E5 10 (UInt64.ofNat bytes) 8 = UInt64.ofNat (2 ^ h) := by
    rw [assign_ne (by decide)]; exact p5
  generalize Asm.assign E5 10 (UInt64.ofNat bytes) = E6 at s6 c6 y6 ev6 p6
  have e7 : eval w E6 mem (ceilDiv RootBits.bytes 32) = some (UInt64.ofNat (nodesFor bytes)) := by
    rw [eval_ceilDiv (eval_var y6) 32 (by omega), ofNat_toNat (by omega)]
    rfl
  have s7 := Runs.set' (m := m) (w := w) (sp := sp) (x := 11) e7
  have nb : nodesFor bytes ≤ nodesFor (stop - start) := Nat.div_le_div_right (by omega)
  generalize hn : nodesFor bytes = n at s7 nb
  have hn' : n = (bytes + 31) / 32 := by rw [← hn]; rfl
  have c7 : Asm.assign E6 11 (UInt64.ofNat n) 9 = UInt64.ofNat count := by rw [assign_ne (by decide)]; exact c6
  have y7 : Asm.assign E6 11 (UInt64.ofNat n) 10 = UInt64.ofNat bytes := by rw [assign_ne (by decide)]; exact y6
  have n7 : Asm.assign E6 11 (UInt64.ofNat n) 11 = UInt64.ofNat n := assign_eq
  have ev7 := ev6.write (x := 11) (UInt64.ofNat n) (by decide)
  have p7 : Asm.assign E6 11 (UInt64.ofNat n) 8 = UInt64.ofNat (2 ^ h) := by rw [assign_ne (by decide)]; exact p6
  generalize Asm.assign E6 11 (UInt64.ofNat n) = E7 at s7 c7 y7 n7 ev7 p7
  have s8 := Runs.set' (m := m) (w := w) (sp := sp) (env := E7) (mem := mem) (x := 12)
    (eval_add (eval_var ev7.scratch) (eval_lit 64))
  have c8 : Asm.assign E7 12 (UInt64.ofNat (scratch + 64)) 9 = UInt64.ofNat count := by
    rw [assign_ne (by decide)]; exact c7
  have y8 : Asm.assign E7 12 (UInt64.ofNat (scratch + 64)) 10 = UInt64.ofNat bytes := by
    rw [assign_ne (by decide)]; exact y7
  have n8 : Asm.assign E7 12 (UInt64.ofNat (scratch + 64)) 11 = UInt64.ofNat n := by
    rw [assign_ne (by decide)]; exact n7
  have b8 : Asm.assign E7 12 (UInt64.ofNat (scratch + 64)) 12 = UInt64.ofNat (scratch + 64) := assign_eq
  have ev8 := ev7.write (x := 12) (UInt64.ofNat (scratch + 64)) (by decide)
  have p8 : Asm.assign E7 12 (UInt64.ofNat (scratch + 64)) 8 = UInt64.ofNat (2 ^ h) := by
    rw [assign_ne (by decide)]; exact p7
  generalize Asm.assign E7 12 (UInt64.ofNat (scratch + 64)) = E8 at s8 c8 y8 n8 b8 ev8 p8
  -- The gather of the bytes the bits fill.
  have nEq : nodesFor (start + bytes - start) = n := by rw [show start + bytes - start = bytes by omega, hn]
  obtain ⟨mem1, g1, held1, keep1⟩ := packGather_runs (m := m) (w := w) gmod (sp := sp) room (env := E8)
    (mem := mem) (dst := 14) (args := [RootBits.buf, RootBits.src, 1, RootBits.bytes, 0,
      32 * RootBits.nodes + 32 - RootBits.bytes]) (buf := scratch + 64) (start := start) (stop := start + bytes) holds bAcc (by omega)
    (by omega) (by rw [usize]; omega) usize (by rw [nEq]; exact access_sub bufAcc (by omega) (by omega))
    (by rw [nEq]; exact apart_sub bufApart (by omega) (by omega))
    (by
      rw [nEq, show start + bytes - start = bytes by omega]
      simp only [List.mapM_cons, List.mapM_nil, eval_var b8, eval_var ev8.src, eval_var y8,
        eval_sub (eval_add (eval_mul (eval_lit 32) (eval_var n8)) (eval_lit 32)) (eval_var y8)
          (show bytes ≤ 32 * n + 32 by rw [← hn]; simp only [nodesFor]; omega)]
      rfl)
  rw [nEq] at keep1
  have packedSize : (packRange b start (start + bytes)).size = 32 * n + 32 := by
    have := (RootProof.packRange_nodes b start (start + bytes) (by omega) (by omega) (by rw [usize]; omega)).2
    rwa [show start + bytes - start = bytes by omega, hn] at this
  have c9 : Asm.assign E8 14 0 9 = UInt64.ofNat count := by rw [assign_ne (by decide)]; exact c8
  have b9 : Asm.assign E8 14 0 12 = UInt64.ofNat (scratch + 64) := by rw [assign_ne (by decide)]; exact b8
  have n9 : Asm.assign E8 14 0 11 = UInt64.ofNat n := by rw [assign_ne (by decide)]; exact n8
  have p9 : Asm.assign E8 14 0 8 = UInt64.ofNat (2 ^ h) := by rw [assign_ne (by decide)]; exact p8
  have ev9 := ev8.write (x := 14) 0 (by decide)
  generalize Asm.assign E8 14 0 = E9 at g1 c9 b9 n9 p9 ev9
  have lead : ∀ {e' : Env} {mm' : Memory},
      Runs m w sp E9 mem1 (.block [when (ne (RootBits.count % 8) 0) [st1 (RootBits.buf + RootBits.count / 8)
        (ld1 (RootBits.buf + RootBits.count / 8) &&& (255 ^^^ RootBits.pw))]]) e' mm' →
      Runs m w sp env mem (.block bitsHead) e' mm' := fun r =>
    Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons s3 (Runs.block_cons run4 (Runs.block_cons s5
      (Runs.block_cons s6 (Runs.block_cons s7 (Runs.block_cons s8 (Runs.block_cons g1 r))))))))
  have cm := eval_ne (w := w) (env := E9) (mem := mem1) (a := RootBits.count % 8) (b := 0)
    (eval_mod (eval_var c9) (eval_lit 8) (by omega) (by decide) (by decide)) (eval_lit 0)
  have hmod : count % 8 = h := by omega
  by_cases whole : count % 8 = 0
  · -- The closing bit has a byte of its own.
    rw [if_pos (by rw [whole])] at cm
    refine ⟨E9, mem1, lead (Runs.block_cons (Runs.when_false cm) (Runs.block_nil _ _ _ _ _)), ev9, c9, ?_, b9,
      ?_, fun a o => keep1 a (fun h => o ⟨h.1, by omega⟩)⟩
    · rw [n9, ← hn, ← hy]
    · have code : bitNodes b start count = packRange b start (start + (count + 7) / 8) := by
        simp only [bitNodes]; rw [if_pos (by simpa using whole)]
      rw [code, hy]; exact held1
  · -- The closing bit is cleared from the last byte the bits fill.
    rw [if_neg (fun e => whole ((ofNat_inj (by omega) (by decide)).mp e))] at cm
    have j8 : count / 8 < bytes := by omega
    have aj : w.access (scratch + 64 + count / 8) 1 = true :=
      access_sub bufAcc (by omega) (by omega)
    have ea : ∀ mm, eval w E9 mm (RootBits.buf + RootBits.count / 8) = some (UInt64.ofNat (scratch + 64 + count / 8)) :=
      fun mm => eval_add (eval_var b9) (eval_div (eval_var c9) (eval_lit 8) (by omega) (by decide) (by decide))
    let old := (packRange b start (start + bytes)).get! (count / 8)
    have oldAt : mem1 (scratch + 64 + count / 8) = old := held1 _ (by omega)
    have ev' : eval w E9 mem1 (ld1 (RootBits.buf + RootBits.count / 8) &&& (255 ^^^ RootBits.pw)) =
        some (UInt64.ofNat old.toNat &&& (255 ^^^ UInt64.ofNat (2 ^ h))) := by
      rw [eval_and (eval_ld1_of (ea mem1) aj) (eval_xor (eval_lit 255) (eval_var p9)), readLE_byte, oldAt]
      rfl
    have st := Runs.store m w sp E9 mem1 .b1 _ _ _ _ (ea mem1) ev' (by rw [ofNat_toNat (by omega)]; exact aj)
    rw [ofNat_toNat (by omega)] at st
    replace st : Runs m w sp E9 mem1 _ E9 (store mem1 (scratch + 64 + count / 8) 1
        (qwordByte (UInt64.ofNat old.toNat &&& (255 ^^^ UInt64.ofNat (2 ^ h))))) := st
    refine ⟨E9, _, lead (Runs.block_cons (Runs.when_true 1 cm (by decide) (Runs.block_cons st
      (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _)), ev9, c9, ?_, b9, ?_, fun a o => ?_⟩
    · rw [n9, ← hn, ← hy]
    · -- The cleared byte is the Lean one.
      have newByte : qwordByte (UInt64.ofNat old.toNat &&& (255 ^^^ UInt64.ofNat (2 ^ h))) 0 =
          old &&& ~~~((1 : UInt8) <<< UInt8.ofNat (count % 8)) := by
        rw [hmod]
        have := clearBit_table ⟨old.toNat, old.toNat_lt⟩ ⟨h, by omega⟩
        rw [uint8_ofNat_toNat] at this
        rw [← this]
        simp [qwordByte]
      have code : bitNodes b start count = (packRange b start (start + bytes)).set! (count / 8)
          (old &&& ~~~((1 : UInt8) <<< UInt8.ofNat (count % 8))) := by
        simp only [bitNodes, old]; rw [if_neg (by simpa using whole), hy]
      rw [code]
      intro i hi
      rw [size_set!] at hi
      rw [store_one]
      by_cases at_ : i = count / 8
      · subst at_
        rw [if_pos rfl, newByte, get!_set!_self _ _ _ hi]
      · rw [if_neg (by omega), held1 i hi, get!_set!_ne _ _ _ _ at_]
    · rw [store_one, if_neg (by omega)]
      exact keep1 a (fun h => o ⟨h.1, by omega⟩)


/-! ### The drivers -/

/-- What a bit list's range gives the driver: a closing bit, a count it bounds, and the scratch's size. -/
theorem bits_facts {lim : Option Nat} {b : ByteArray} {start stop : Nat} {bits : Array Bool} (ordered : start ≤ stop)
    (inside : stop ≤ b.size) (small : stop - start + 64 < USize.size)
    (read : unpackDelimited lim (slice b start stop) = .ok bits) :
    start < stop ∧ b.get! (stop - 1) ≠ 0 ∧ bitCount b start stop = bits.size ∧
      bitCount b start stop ≤ 8 * (stop - start) ∧
      (bitNodes b start (bitCount b start stop)).size = 32 * nodesFor ((bitCount b start stop + 7) / 8) + 32 := by
  obtain ⟨nonempty, nz⟩ := bits_decoded inside read
  obtain ⟨counted, -, sized⟩ := RootProof.bitNodes_nodes b start stop ordered inside small _ bits read
  refine ⟨nonempty, nz, counted, ?_, by rw [counted]; exact sized⟩
  simp only [bitCount]
  have := RootProof.highest_lt (b.get! (stop - 1))
  omega

/-- The bit list driver's body, from its statements: the head, the tree, then the count mixed in. -/
theorem rootBits_body_eq : RootBits.fn.body = .block (bitsHead ++
    (ifElse (eq (ld RootBits.p) 5)
      [callInto RootBits.d "ssz_depth_for" [ceilDiv (ld (RootBits.p + 8)) 256],
        callInto RootBits.sink "ssz_merkleize" [RootBits.buf, RootBits.nodes, RootBits.d, RootBits.scratch,
          RootBits.buf + 32 * RootBits.nodes + 32, RootBits.ctx]]
      [callInto RootBits.sink "ssz_root_progressive" [RootBits.buf, RootBits.nodes, RootBits.scratch,
        RootBits.buf + 32 * RootBits.nodes + 32, RootBits.ctx]] ::
      (lengthNodeAt (Expr.var 4 + 32) (Expr.var 9) ++
        [.call "ssz_hash_pairs" [Expr.var 3, Expr.var 4, Expr.var 4 + 32, 1, Expr.var 5] 14]))) := rfl

set_option maxHeartbeats 4000000 in
/-- The bit list driver writes the Lean root of a bit list's range, bounded or progressive. -/
theorem rootBits_body {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RangeFns m)
    {d : Desc} (shape : (∃ limit, d = .bitList limit) ∨ (∃ lim, d = .progressiveBitList lim))
    {sp : Nat} {mem : Memory} {p base start stop out scratch ctx table zeros pad : Nat} {mask : UInt64}
    {b : ByteArray} (room : w.stackLo + 12288 ≤ sp)
    (pre : RangePre w mem d p base start stop out scratch ctx table zeros pad mask b)
    {env : Env} (ev : RangeEnv env p (base + start) (stop - start) out scratch ctx) :
    ∃ env' mem', Runs m w sp env mem RootBits.fn.body env' mem' ∧
      RangePost w mem mem' out scratch (varNeed d (stop - start)) ctx table zeros pad mask (rootOf d b start stop) := by
  have usize := pre.usize
  have small := pre.small
  unfold RootProof.Small at small
  rw [usize] at small
  have ordered := pre.ordered
  have inside := pre.inside
  have bound : addressBound = 2 ^ 63 := rfl
  have zh : zeroHeights = 64 := rfl
  -- What decoding gives.
  obtain ⟨v, read⟩ := pre.accepted
  obtain ⟨lim, bits, decoded, capped⟩ : ∃ lim bits, unpackDelimited lim (slice b start stop) = .ok bits ∧
      ∀ limit, d = .bitList limit → bits.size ≤ limit := by
    rcases shape with ⟨limit, rfl⟩ | ⟨lim, rfl⟩
    · simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
      split at read
      · cases read
      rename_i bits decoded
      exact ⟨some limit, bits, decoded, fun l e => by cases e; exact unpackDelimited_bound decoded⟩
    · simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
      split at read
      · cases read
      rename_i bits decoded
      exact ⟨lim, bits, decoded, fun l e => by cases e⟩
  obtain ⟨nonempty, nz, counted, cb, sized⟩ := bits_facts ordered inside (by rw [usize]; omega) decoded
  -- The scratch.
  have need : varNeed d (stop - start) = 96 + 32 * nodesFor (stop - start) + (2560 + 2048 + 32 * nodesFor (stop - start)) := by
    have := pre.below
    rcases shape with ⟨limit, rfl⟩ | ⟨lim, rfl⟩ <;> simp only [varNeed] at this ⊢ <;> exact listNeed_eq this
  have sAcc := pre.sAcc
  have sB := pre.sB
  have sPad := pre.sPad
  have sCtx := pre.sCtx
  have sTable := pre.sTable
  have sZeros := pre.sZeros
  have sOut := pre.sOut
  have sPlan := pre.sPlan
  rw [need] at sAcc sB sPad sCtx sTable sZeros sOut sPlan
  have as := access_bound sAcc
  have hN : nodesFor (stop - start) = (stop - start + 31) / 32 := rfl
  -- The head: the count, and the bits' nodes.
  obtain ⟨E1, mem1, run1, ev1, c1, n1, b1, held1, keep1⟩ := bitsHead_runs gmod (sp := sp) (by omega) pre.holds
    pre.bAcc inside small usize nonempty nz (access_sub sAcc (by omega) (by omega)) (apart_sub sB (by omega) (by omega))
    ev
  generalize hc : bitCount b start stop = count at c1 n1 held1 counted cb sized
  generalize hn : nodesFor ((count + 7) / 8) = n at n1 sized
  have hn' : n = ((count + 7) / 8 + 31) / 32 := by rw [← hn]; rfl
  have nN : n ≤ nodesFor (stop - start) := by rw [hN]; omega
  -- The plan's tag.
  have planOk : WordsAt w mem1 p (Plan.words d) := by
    refine planAt_congr pre.plan fun a lo hi => keep1 a ?_
    have := sPlan
    simp only [Apart] at this
    omega
  have tagEval := eval_tag (env := E1) (e := RootBits.p) planOk (eval_var ev1.p)
  have tagWord : Plan.tag d = 5 ∨ Plan.tag d = 6 := by
    rcases shape with ⟨limit, rfl⟩ | ⟨lim, rfl⟩ <;> simp [Plan.tag]
  have cTag := eval_eq (w := w) (env := E1) (mem := mem1) (a := ld RootBits.p) (b := 5) tagEval (eval_lit 5)
    (by rcases tagWord with h | h <;> rw [h] <;> decide) (by decide)
  -- The tree over the nodes, at the limit's depth or on a spine, into the scratch's first node.
  obtain ⟨E2, mem2, run2, ev2, c2, root2, keep2⟩ : ∃ E2 mem2,
      Runs m w sp E1 mem1 (ifElse (eq (ld RootBits.p) 5)
        [callInto RootBits.d "ssz_depth_for" [ceilDiv (ld (RootBits.p + 8)) 256],
          callInto RootBits.sink "ssz_merkleize" [RootBits.buf, RootBits.nodes, RootBits.d, RootBits.scratch,
            RootBits.buf + 32 * RootBits.nodes + 32, RootBits.ctx]]
        [callInto RootBits.sink "ssz_root_progressive" [RootBits.buf, RootBits.nodes, RootBits.scratch,
          RootBits.buf + 32 * RootBits.nodes + 32, RootBits.ctx]]) E2 mem2 ∧
      RangeEnv E2 p (base + start) (stop - start) out scratch ctx ∧ E2 9 = UInt64.ofNat count ∧
      nodeAt mem2 scratch = (match d with
        | .bitList limit => merkleizeCapacity (bitNodes b start count) n ((limit + 255) / 256)
        | _ => merkleizeProgressive (bitNodes b start count) n).data ∧
      ∀ a, ¬ (scratch ≤ a ∧ a < scratch + (96 + 32 * nodesFor (stop - start) +
        (2560 + 2048 + 32 * nodesFor (stop - start)))) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem2 a = mem1 a := by
    have ready1 := pre.ready.within (o := scratch + 64) (n := 32 * nodesFor (stop - start) + 32)
      (apart_sub sCtx (by omega) (by omega)) (apart_sub sTable (by omega) (by omega))
      (apart_sub sZeros (by omega) (by omega)) fun a o _ => keep1 a o
    rcases shape with ⟨limit, rfl⟩ | ⟨lim, rfl⟩
    · -- A bounded list: the tree at the limit's depth.
      rw [if_pos (by simp [Plan.tag])] at cTag
      have limitSmall : limit < 2 ^ 64 := pre.fits limit (by simp [Plan.words])
      have few : count ≤ limit := by rw [counted]; exact capped limit rfl
      have lw : eval w E1 mem1 (ld (RootBits.p + 8)) = some (UInt64.ofNat limit) :=
        eval_word planOk 1 (by simp [Plan.words]) (e := RootBits.p + 8) (eval_add (eval_var ev1.p) (eval_lit 8))
      have dframe : DepthFor.fn.frame = 5 := by decide
      have dcall := depthFor_calls (m := m) (w := w) fns.roots.plan.depth (sp := sp) (by rw [dframe]; omega)
        (UInt64.ofNat ((limit + 255) / 256)) mem1
      rw [ofNat_toNat (by omega)] at dcall
      have r1 := Runs.call (m := m) (sp := sp) (env := E1) (mem := mem1) (dst := 13)
        (args := [ceilDiv (ld (RootBits.p + 8)) 256])
        (by
          simp only [List.mapM_cons, List.mapM_nil]
          rw [eval_ceilDiv lw 256 (by omega), ofNat_toNat limitSmall]
          rfl) dcall
      generalize hd : depthFor ((limit + 255) / 256) = depth at r1
      have deep : depth ≤ 64 := by rw [← hd]; exact depthFor_le_of_le_two_pow (by omega)
      have fitsTree : n ≤ 2 ^ depth := by
        rw [← hd]; exact Nat.le_trans (by rw [hn']; omega) (le_two_pow_depthFor _)
      have tpre : TreePre w mem1 (scratch + 64) n depth scratch (scratch + 64 + 32 * n + 32) ctx table zeros pad
          mask :=
        { ctxAccess := ready1.ctxAccess, maskAt := ready1.maskAt, tableAt := ready1.tableAt,
          zerosAt := ready1.zerosAt, padAt := ready1.padAt, tableBytes := ready1.tableHeld,
          tableAccess := ready1.tableAccess, zeroRoots := ready1.zeroRoots, zerosAccess := ready1.zerosAccess,
          deep := by rw [zh]; omega, fits := fitsTree, nodesAccess := access_sub sAcc (by omega) (by omega),
          outAccess := access_sub sAcc (by omega) (by omega),
          scratchAccess := access_sub sAcc (by omega) (by omega), padAccess := ready1.padAccess,
          scratchNodes := by simp only [Apart]; omega, scratchOut := by simp only [Apart]; omega,
          scratchCtx := apart_sub sCtx (by omega) (by omega), scratchTable := apart_sub sTable (by omega) (by omega),
          scratchZeros := apart_sub sZeros (by omega) (by omega), scratchPad := apart_sub sPad (by omega) (by omega),
          padNodes := apart_comm (apart_sub sPad (by omega) (by omega)), padCtx := ready1.padCtx,
          padTable := ready1.padTable, padZeros := ready1.padZeros, nodesReach := by omega,
          outNodes := by simp only [Apart]; omega, outZeros := apart_sub sZeros (by omega) (by omega) }
      obtain ⟨mem2, call2, root2, keep2⟩ := treeCalls_native hash.merkleize (sp := sp) tpre ready1.kernels (by
        simp only [treeStack, hashStack]; omega) (by rw [usize]; omega)
      have ev' := ev1.write (x := 13) depth.toUInt64 (by decide)
      have r2 := Runs.call (m := m) (sp := sp) (env := Asm.assign E1 13 depth.toUInt64) (mem := mem1) (dst := 14)
        (args := [RootBits.buf, RootBits.nodes, RootBits.d, RootBits.scratch,
          RootBits.buf + 32 * RootBits.nodes + 32, RootBits.ctx])
        (by
          have b' : Asm.assign E1 13 depth.toUInt64 12 = UInt64.ofNat (scratch + 64) := by
            rw [assign_ne (by decide)]; exact b1
          have n' : Asm.assign E1 13 depth.toUInt64 11 = UInt64.ofNat n := by rw [assign_ne (by decide)]; exact n1
          simp only [List.mapM_cons, List.mapM_nil, eval_var b', eval_var n',
            eval_var (show Asm.assign E1 13 depth.toUInt64 13 = UInt64.ofNat depth from assign_eq),
            eval_var ev'.scratch, eval_add (eval_add (eval_var b') (eval_mul (eval_lit 32) (eval_var n')))
              (eval_lit 32), eval_var ev'.ctx]
          rfl) call2
      refine ⟨_, mem2, Runs.ifElse_true 1 cTag (by decide) (Runs.block_cons r1 (Runs.block_cons r2
        (Runs.block_nil _ _ _ _ _))), ev'.write 0 (by decide), ?_, ?_, fun a o pd => ?_⟩
      · rw [assign_ne (by decide), assign_ne (by decide)]; exact c1
      · show nodeAt mem2 scratch = (merkleizeCapacity (bitNodes b start count) n ((limit + 255) / 256)).data
        rw [root2, merkleizeDepth_of_holds held1 (by rw [sized]; omega) fitsTree (by rw [sized, usize]; omega),
          merkleizeCapacity, hd]
      · exact keep2 a (fun h => o ⟨by omega, by omega⟩) pd (fun h => o ⟨h.1, by omega⟩)
    · -- A progressive list: the spine.
      rw [if_neg (by simp [Plan.tag])] at cTag
      have pspan : progressiveSpan n = 4608 + 32 * n := rfl
      have ppre : ProgPre w mem1 (scratch + 64) n scratch (scratch + 64 + 32 * n + 32) ctx table zeros pad mask
          (bitNodes b start count) :=
        { ready := ready1, held := held1, inside := by rw [sized]; omega, small := by rw [sized, usize]; omega,
          few := by omega, nAcc := access_sub sAcc (by omega) (by omega), nReach := by omega,
          oAcc := access_sub sAcc (by omega) (by omega), sAcc := access_sub sAcc (by omega) (by omega),
          sN := by rw [sized]; simp only [Apart]; omega, sO := by simp only [Apart]; omega,
          sPad := apart_sub sPad (by omega) (by omega), sCtx := apart_sub sCtx (by omega) (by omega),
          sTable := apart_sub sTable (by omega) (by omega), sZeros := apart_sub sZeros (by omega) (by omega),
          oPad := apart_sub sPad (by omega) (by omega), oCtx := apart_sub sCtx (by omega) (by omega),
          oTable := apart_sub sTable (by omega) (by omega), oZeros := apart_sub sZeros (by omega) (by omega),
          nPad := by rw [sized]; exact apart_sub sPad (by omega) (by omega) }
      obtain ⟨mem2, call2, root2, -, keep2⟩ := rootProgressive_calls hash fns.progressive (sp := sp)
        (by simp only [treeStack, hashStack]; omega) ppre
      have r1 := Runs.call (m := m) (sp := sp) (env := E1) (mem := mem1) (dst := 14)
        (args := [RootBits.buf, RootBits.nodes, RootBits.scratch, RootBits.buf + 32 * RootBits.nodes + 32,
          RootBits.ctx])
        (by
          simp only [List.mapM_cons, List.mapM_nil, eval_var b1, eval_var n1, eval_var ev1.scratch,
            eval_add (eval_add (eval_var b1) (eval_mul (eval_lit 32) (eval_var n1))) (eval_lit 32), eval_var ev1.ctx]
          rfl) call2
      refine ⟨_, mem2, Runs.ifElse_false cTag (Runs.block_cons r1 (Runs.block_nil _ _ _ _ _)),
        ev1.write 0 (by decide), by rw [assign_ne (by decide)]; exact c1, root2, fun a o pd => ?_⟩
      exact keep2 a (fun h => o ⟨by omega, by omega⟩) (fun h => o ⟨by omega, by omega⟩) pd
  -- The count mixed in.
  have keep12 : ∀ a, ¬ (scratch ≤ a ∧ a < scratch + (96 + 32 * nodesFor (stop - start) +
      (2560 + 2048 + 32 * nodesFor (stop - start)))) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem2 a = mem a :=
    fun a o pd => by rw [keep2 a o pd, keep1 a (fun h => o ⟨by omega, by omega⟩)]
  have ready2 := pre.ready.within (o := scratch) (n := 96 + 32 * nodesFor (stop - start) +
    (2560 + 2048 + 32 * nodesFor (stop - start))) sCtx sTable sZeros keep12
  obtain ⟨E3, mem3, run3, root3, ready3, keep3⟩ := mixin_ends hash (sp := sp) (by simp only [hashStack]; omega)
    ready2 ev2.scratch ev2.out ev2.ctx (cnt := Expr.var 9) (n := count) (fun _ => eval_var c2) (by omega)
    (access_sub sAcc (by omega) (by omega)) (by omega) pre.oAcc (apart_sub sOut (by omega) (by omega))
    (apart_sub sPad (by omega) (by omega)) (apart_sub sCtx (by omega) (by omega))
    (apart_sub sTable (by omega) (by omega)) (apart_sub sZeros (by omega) (by omega)) pre.oPad pre.oCtx pre.oTable
    pre.oZeros 14
  refine ⟨E3, mem3, by rw [rootBits_body_eq]; exact Runs.block_append run1 (Runs.block_cons run2 run3), ?_,
    ready3, fun a o s pd => ?_⟩
  · -- The root: the tree over the bits' nodes, with the count mixed in.
    rw [root3, root2]
    rcases shape with ⟨limit, rfl⟩ | ⟨lim, rfl⟩
    · have treeSize := (merkleizeCapacity_spec (bitNodes b start count) n ((limit + 255) / 256)
        (by rw [hn']; have := capped limit rfl; omega) (by rw [sized]; omega) (by rw [sized, usize]; omega)).1
      have code : rootOf (.bitList limit) b start stop =
          hashPair (merkleizeCapacity (bitNodes b start count) n ((limit + 255) / 256)) (lengthNode count) := by
        rw [rootOf, hc, hn]
      rw [code, RootProof.hashPair_data _ _ treeSize (by simp [lengthNode, ByteArray.size])]
    · have treeSize := (merkleizeProgressive_spec (bitNodes b start count) n (by rw [sized]; omega)
        (by rw [sized, usize]; omega)).1
      have code : rootOf (.progressiveBitList lim) b start stop =
          hashPair (merkleizeProgressive (bitNodes b start count) n) (lengthNode count) := by
        rw [rootOf, hc, hn]
      rw [code, RootProof.hashPair_data _ _ treeSize (by simp [lengthNode, ByteArray.size])]
  · rw [need] at s
    rw [keep3 a (fun h => s ⟨by omega, by omega⟩) o pd]
    exact keep12 a s pd

/-- The bit list driver writes the Lean root of a bounded bit list's range. -/
theorem rootBits_ok {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RangeFns m)
    (limit : Nat) : RangeOk m w "ssz_root_bits" (.bitList limit) := by
  intro sp mem p base start stop out scratch ctx table zeros pad mask b room pre
  have frame : RootBits.fn.frame = 21 := by decide
  have stack : rootStack (.bitList limit) = 12288 + 1024 := rfl
  obtain ⟨env', mem', run, post⟩ := rootBits_body hash gmod fns (.inl ⟨limit, rfl⟩)
    (sp := sp - 8 - 8 * RootBits.fn.frame) (by rw [frame]; omega) pre (rangeEnv_entry _ _ _ _ _ _)
  exact ⟨mem', Calls.fn fns.bits (by rw [frame]; omega) rfl run rfl, post⟩

/-- The bit list driver writes the Lean root of a progressive bit list's range. -/
theorem rootBitsProgressive_ok {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m)
    (fns : RangeFns m) (lim : Option Nat) : RangeOk m w "ssz_root_bits" (.progressiveBitList lim) := by
  intro sp mem p base start stop out scratch ctx table zeros pad mask b room pre
  have frame : RootBits.fn.frame = 21 := by decide
  have stack : rootStack (.progressiveBitList lim) = 12288 + 1024 := rfl
  obtain ⟨env', mem', run, post⟩ := rootBits_body hash gmod fns (.inr ⟨lim, rfl⟩)
    (sp := sp - 8 - 8 * RootBits.fn.frame) (by rw [frame]; omega) pre (rangeEnv_entry _ _ _ _ _ _)
  exact ⟨mem', Calls.fn fns.bits (by rw [frame]; omega) rfl run rfl, post⟩

end Ssz.Native.Driver
