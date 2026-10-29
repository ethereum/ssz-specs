import SszNative.Proofs.Driver.Root.Sequence
import SszNative.Proofs.Driver.Fields
import SszNative.Proofs.Driver.Validate.PlanCheck
import SszNative.Proofs.Branch.Nested

/-!
The fields driver writes, node by node, the Lean roots of a struct's fields.

The driver reads the fixed part into a table of ranges, closes each body at the start of the next one, then roots
each field from its range.
Each field is rooted by the dispatcher on the field's type, a hypothesis of the induction on the type.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Asm

/-! ### The field ranges -/

/-- The range of field j of a struct, as the Lean root reads it. -/
abbrev fieldRg (fields : List Desc) (b : ByteArray) (start stop j : Nat) : Nat × Nat :=
  (rangesOf start (stop - start) (placesFrom fields b start 0)).getD j (0, 0)

/-- Where the first body after some fields starts, from the struct's start, or the struct's end when none does. -/
abbrev nextBody (fields : List Desc) (b : ByteArray) (start stop j : Nat) : Nat :=
  (placeStarts ((placesFrom fields b start 0).drop j)).headD (stop - start)

/-- Field ranges a struct accepts are the ranges of its places, and its fixed part lies inside it. -/
theorem fieldRanges_ok {fields : List Desc} {b : ByteArray} {start stop : Nat} {rs : List (Nat × Nat)}
    (h : fieldRanges fields b start stop = .ok rs) :
    rs = rangesOf start (stop - start) (placesFrom fields b start 0) ∧ Desc.leadingWidth fields ≤ stop - start := by
  have small : ¬ offsetBound ≤ stop - start := by
    intro big
    simp [fieldRanges, fieldPlaces, big, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
  by_cases acc : budgetOk fields (stop - start) ∧
      tableOk (placeStarts (placesFrom fields b start 0)) (Desc.leadingWidth fields) (stop - start)
  · rw [fieldRanges_accepted fields b start stop small acc.1 acc.2] at h
    refine ⟨(Except.ok.inj h).symm, ?_⟩
    have budget := acc.1
    simp only [budgetOk] at budget
    cases fixed : Desc.fieldsFixedSize fields with
    | none => simp [fixed] at budget; omega
    | some width => simp [fixed] at budget; rw [leadingWidth_fixed fields width fixed]; omega
  · exact absurd h (fieldRanges_refused fields b start stop small acc rs)

/--
What decoding a struct gives its root: the ranges of its places, a fixed part inside it, and for each field a range
inside the struct that decodes.
-/
theorem struct_decoded {fields : List Desc} {b : ByteArray} {start stop : Nat} (ordered : start ≤ stop)
    (inside : stop ≤ b.size) {values : List Value}
    (read : deserializeStruct fields (slice b start stop) = .ok values) :
    fieldRanges fields b start stop = .ok (rangesOf start (stop - start) (placesFrom fields b start 0)) ∧
      Desc.leadingWidth fields ≤ stop - start ∧
      ∀ j (_ : j < fields.length), start ≤ (fieldRg fields b start stop j).1 ∧
        (fieldRg fields b start stop j).1 ≤ (fieldRg fields b start stop j).2 ∧
        (fieldRg fields b start stop j).2 ≤ stop ∧
        ∃ v, deserialize fields[j] (slice b (fieldRg fields b start stop j).1 (fieldRg fields b start stop j).2) =
          .ok v := by
  obtain ⟨slices, cut, decoded⟩ := deserializeStruct_ok read
  have agree := fieldRanges_cut fields b start stop ordered inside
  rw [cut] at agree
  cases ranged : fieldRanges fields b start stop with
  | error e => simp [ranged, CutAgree] at agree
  | ok rs =>
    simp only [ranged, CutAgree, Cuts] at agree
    obtain ⟨sliced, within⟩ := agree
    obtain ⟨same, lead⟩ := fieldRanges_ok ranged
    subst same
    obtain ⟨fl, vl, each⟩ := BranchProof.deserializeFields_get fields slices values decoded
    have lens : (rangesOf start (stop - start) (placesFrom fields b start 0)).length = fields.length := by
      rw [rangesOf_length, placesFrom_length]
    refine ⟨rfl, lead, fun j hj => ?_⟩
    have hr : j < (rangesOf start (stop - start) (placesFrom fields b start 0)).length := by omega
    have at_ : fieldRg fields b start stop j = (rangesOf start (stop - start) (placesFrom fields b start 0))[j] := by
      simp only [fieldRg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
    rw [at_]
    obtain ⟨a, c, d⟩ := within _ (List.getElem_mem hr)
    refine ⟨a, c, d, values[j]'(by omega), ?_⟩
    have := each j hj (by omega) (by omega)
    have sj : slices[j]'(by omega) = slice b (rangesOf start (stop - start) (placesFrom fields b start 0))[j].1
        (rangesOf start (stop - start) (placesFrom fields b start 0))[j].2 := by
      subst sliced; simp
    rw [sj] at this
    exact this

/-- A field's place, read at its position in the fixed part. -/
theorem placesFrom_getElem (fields : List Desc) (b : ByteArray) (start j : Nat) (hj : j < fields.length) :
    (placesFrom fields b start 0)[j]'(by rw [placesFrom_length]; exact hj) =
      if hasWidth fields[j] then Place.inline (start + Desc.leadingWidth (fields.take j))
        (start + Desc.leadingWidth (fields.take j) + fixedWidth fields[j])
      else Place.body (offsetAt b (start + Desc.leadingWidth (fields.take j))) := by
  rw [placesFrom_get b start fields 0 j hj, fixedSize_eq]
  by_cases h : hasWidth fields[j] <;> simp [h]

/-- A fixed field's range is its own bytes in the fixed part. -/
theorem fieldRg_fixed {fields : List Desc} {b : ByteArray} {start stop j : Nat} (hj : j < fields.length)
    (fx : hasWidth fields[j] = true) :
    fieldRg fields b start stop j = (start + Desc.leadingWidth (fields.take j),
      start + Desc.leadingWidth (fields.take j) + fixedWidth fields[j]) := by
  have hp : j < (placesFrom fields b start 0).length := by rw [placesFrom_length]; exact hj
  have hr : j < (rangesOf start (stop - start) (placesFrom fields b start 0)).length := by
    rw [rangesOf_length]; exact hp
  simp only [fieldRg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
  rw [rangesOf_get start _ _ j hp, placesFrom_getElem fields b start j hj, ite_eq_left fx]

/-- A variable field's range runs from its offset to the next body's start, or to the end. -/
theorem fieldRg_body {fields : List Desc} {b : ByteArray} {start stop j : Nat} (hj : j < fields.length)
    (fx : hasWidth fields[j] = false) :
    fieldRg fields b start stop j = (start + offsetAt b (start + Desc.leadingWidth (fields.take j)),
      start + nextBody fields b start stop (j + 1)) := by
  have hp : j < (placesFrom fields b start 0).length := by rw [placesFrom_length]; exact hj
  have hr : j < (rangesOf start (stop - start) (placesFrom fields b start 0)).length := by
    rw [rangesOf_length]; exact hp
  simp only [fieldRg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some]
  rw [rangesOf_get start _ _ j hp, placesFrom_getElem fields b start j hj, ite_eq_right (by simp [fx])]

/-- The next body after a field: its own when it has one, or the next body after it. -/
theorem nextBody_step {fields : List Desc} {b : ByteArray} {start stop j : Nat} (hj : j < fields.length) :
    nextBody fields b start stop j = if hasWidth fields[j] then nextBody fields b start stop (j + 1)
      else offsetAt b (start + Desc.leadingWidth (fields.take j)) := by
  have hp : j < (placesFrom fields b start 0).length := by rw [placesFrom_length]; exact hj
  simp only [nextBody]
  rw [List.drop_eq_getElem_cons hp, placesFrom_getElem fields b start j hj]
  by_cases fx : hasWidth fields[j] <;> simp [fx, placeStarts]

/-- Past the last field, the next body is the struct's end. -/
theorem nextBody_end (fields : List Desc) (b : ByteArray) (start stop : Nat) :
    nextBody fields b start stop fields.length = stop - start := by
  simp only [nextBody]
  rw [List.drop_eq_nil_of_le (by rw [placesFrom_length]; exact Nat.le_refl _)]
  rfl

/-! ### The fields' plans -/

/-- The plan of field j: past the plans of the fields before it. -/
abbrev fieldPlan (fa : Nat) (fields : List Desc) (j : Nat) : Nat :=
  fa + 8 * (Plan.wordsAll (fields.take j)).length

/-- The words of a field's plan are among the fields' words. -/
theorem fieldWords_mem (fields : List Desc) (j : Nat) (hj : j < fields.length) :
    ∀ x ∈ Plan.words fields[j], x ∈ Plan.wordsAll fields := by
  intro x hx
  have e : Plan.wordsAll fields =
      Plan.wordsAll (fields.take j) ++ (Plan.words fields[j] ++ Plan.wordsAll (fields.drop (j + 1))) := by
    have split : Plan.words fields[j] ++ Plan.wordsAll (fields.drop (j + 1)) = Plan.wordsAll (fields.drop j) := by
      rw [List.drop_eq_getElem_cons hj]; rfl
    rw [split, ← Validate.wordsAll_append, List.take_append_drop]
  rw [e]
  simp [hx]

/-! ### The table of ranges -/

/--
The fields table holds, for each of the first fields, its start, whether it is fixed, and its end when it is fixed or
already closed.
-/
def RangeTable (mem : Memory) (t base : Nat) (fields : List Desc) (b : ByteArray) (start stop upto ended : Nat) : Prop :=
  ∀ k (hk : k < fields.length), k < upto →
    readLE mem (t + 24 * k) 8 = UInt64.ofNat (base + (fieldRg fields b start stop k).1) ∧
    readLE mem (t + 24 * k + 16) 8 = bitOf (hasWidth fields[k]) ∧
    (ended ≤ k ∨ hasWidth fields[k] = true →
      readLE mem (t + 24 * k + 8) 8 = UInt64.ofNat (base + (fieldRg fields b start stop k).2))

/-- The table stays as it was where memory does. -/
theorem RangeTable.congr {mem mem' : Memory} {t base : Nat} {fields : List Desc} {b : ByteArray}
    {start stop upto ended : Nat} (h : RangeTable mem t base fields b start stop upto ended)
    (same : ∀ a, t ≤ a → a < t + 24 * fields.length → mem' a = mem a) :
    RangeTable mem' t base fields b start stop upto ended := by
  intro k hk lt
  have rd : ∀ c, c + 8 ≤ 24 → readLE mem' (t + 24 * k + c) 8 = readLE mem (t + 24 * k + c) 8 := fun c hc =>
    readLE_congr _ _ _ 8 fun i hi => same _ (by omega) (by omega)
  obtain ⟨a0, a2, a1⟩ := h k hk lt
  refine ⟨?_, ?_, fun c => ?_⟩
  · have := rd 0 (by omega); simp only [Nat.add_zero] at this; rw [this, a0]
  · rw [rd 16 (by omega), a2]
  · rw [rd 8 (by omega), a1 c]

/-- A word stored apart from eight bytes keeps them. -/
theorem readLE_store_word (mem : Memory) (a x : Nat) (v : UInt64) (h : a + 8 ≤ x ∨ x + 8 ≤ a) :
    readLE (store mem x 8 (qwordByte v)) a 8 = readLE mem a 8 :=
  readLE_store_apart mem a x 8 _ h

/-- A store of eight bytes at an address a program may use. -/
theorem Runs.st8 {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {a v : Expr} {x : Nat}
    {y : UInt64} (ha : eval w env mem a = some (UInt64.ofNat x)) (hv : eval w env mem v = some y)
    (acc : w.access x 8 = true) : Runs m w sp env mem (st a v) env (store mem x 8 (qwordByte y)) := by
  have bx : x < 2 ^ 64 := by have := access_bound acc; omega
  have := Runs.store m w sp env mem .b8 a v _ y ha hv (by rw [ofNat_toNat bx]; exact acc)
  rw [ofNat_toNat bx] at this
  exact this

/-! ### The driver's needs -/

/-- The fields driver's frame holds twenty-one words. -/
theorem fieldsFrame : RootFields.fn.frame = 21 := by decide

/--
What the fields driver needs: the fields' plans, the encoding, each field's range decoding, and a region apart.

The region holds the roots, the table of ranges, then the most a field's scratch needs.
-/
structure FieldsPre (w : World) (mem : Memory) (fields : List Desc)
    (fa base start stop out span ctx table zeros pad : Nat) (mask : UInt64) (b : ByteArray) : Prop where
  /-- The context is filled. -/
  ready : RootReady w ctx table zeros pad mask mem
  /-- The fields' plans are in memory. -/
  plan : WordsAt w mem fa (Plan.wordsAll fields)
  /-- Their words fit machine words. -/
  fits : Fits (Plan.wordsAll fields)
  /-- The encoding is in memory. -/
  holds : Holds mem base b
  /-- The encoding is usable. -/
  bAcc : w.access base b.size = true
  /-- The struct's range runs forward. -/
  ordered : start ≤ stop
  /-- It lies inside the encoding. -/
  inside : stop ≤ b.size
  /-- Every buffer the root builds has machine-sized offsets. -/
  small : RootProof.Small b
  /-- Twice the encoding's size past its address stays below the address bound. -/
  spread : base + 2 * b.size ≤ addressBound
  /-- Every field type is legal. -/
  sound : ∀ f ∈ fields, f.wellFormed = .ok ()
  /-- Every field type's fixed-size parts are narrow. -/
  thin : ∀ f ∈ fields, narrow f = true
  /-- The fixed part lies inside the struct. -/
  lead : Desc.leadingWidth fields ≤ stop - start
  /-- Each field's range lies inside the struct's and decodes. -/
  ranges : ∀ j (_ : j < fields.length), start ≤ (fieldRg fields b start stop j).1 ∧
    (fieldRg fields b start stop j).1 ≤ (fieldRg fields b start stop j).2 ∧
    (fieldRg fields b start stop j).2 ≤ stop ∧
    ∃ v, deserialize fields[j] (slice b (fieldRg fields b start stop j).1 (fieldRg fields b start stop j).2) = .ok v
  /-- The region holds the roots and the table, then the most a field's scratch needs. -/
  room : 56 * fields.length + fieldsVarNeed fields (stop - start) 0 ≤ span
  /-- That most is below the cap. -/
  below : fieldsVarNeed fields (stop - start) 0 < scratchCap
  /-- The region is usable. -/
  rAcc : w.access out span = true
  /-- The region ends a node short of the address bound. -/
  rSlack : out + span + 32 ≤ addressBound
  /-- The region misses the encoding. -/
  rB : Apart (out, span) (base, b.size)
  /-- It misses the padding area. -/
  rPad : Apart (out, span) (pad, 1536)
  /-- It misses the context. -/
  rCtx : Apart (out, span) (ctx, 32)
  /-- It misses the table. -/
  rTable : Apart (out, span) (table, Kernel.tableSize)
  /-- It misses the zero roots. -/
  rZeros : Apart (out, span) (zeros, 32 * (zeroHeights + 1))
  /-- It misses the fields' plans. -/
  rPlan : Apart (out, span) (fa, 8 * (Plan.wordsAll fields).length)
  /-- The encoding misses the padding area. -/
  bPad : Apart (base, b.size) (pad, 1536)
  /-- The fields' plans miss the padding area. -/
  planPad : Apart (fa, 8 * (Plan.wordsAll fields).length) (pad, 1536)
  /-- A machine word holds a full 64-bit size. -/
  usize : USize.size = 2 ^ 64

/-- The fields driver's variables that stay: the arguments and the table's address. -/
structure FieldsEnv (env : Env) (fa n src size out ctx : Nat) : Prop where
  /-- The first field's plan. -/
  fV : env 0 = UInt64.ofNat fa
  /-- The field count. -/
  nV : env 1 = UInt64.ofNat n
  /-- The struct's address. -/
  srcV : env 2 = UInt64.ofNat src
  /-- Its size. -/
  sizeV : env 3 = UInt64.ofNat size
  /-- The output. -/
  outV : env 4 = UInt64.ofNat out
  /-- The context. -/
  ctxV : env 5 = UInt64.ofNat ctx
  /-- The table, after the roots. -/
  tV : env 6 = UInt64.ofNat (out + 32 * n)

/-- Writing a working variable keeps the variables that stay. -/
theorem FieldsEnv.write {env : Env} {fa n src size out ctx : Nat} (h : FieldsEnv env fa n src size out ctx) {x : Nat}
    (v : UInt64) (hx : 7 ≤ x) : FieldsEnv (Asm.assign env x v) fa n src size out ctx :=
  ⟨by rw [assign_ne (by omega), h.fV], by rw [assign_ne (by omega), h.nV], by rw [assign_ne (by omega), h.srcV],
    by rw [assign_ne (by omega), h.sizeV], by rw [assign_ne (by omega), h.outV], by rw [assign_ne (by omega), h.ctxV],
    by rw [assign_ne (by omega), h.tV]⟩

/-- Memory that kept the fields' plans holds each field's plan. -/
theorem FieldsPre.planAt {w : World} {mem mm : Memory} {fields : List Desc}
    {fa base start stop out span ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : FieldsPre w mem fields fa base start stop out span ctx table zeros pad mask b)
    (frame : ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm a = mem a)
    (j : Nat) (hj : j < fields.length) :
    WordsAt w mm (fieldPlan fa fields j) (Plan.words fields[j]) ∧
      fieldPlan fa fields j + 8 * (Plan.words fields[j]).length ≤ fa + 8 * (Plan.wordsAll fields).length := by
  have planM : WordsAt w mm fa (Plan.wordsAll fields) := planAt_congr pre.plan fun a lo hi =>
    frame a (outside_of_apart pre.rPlan lo hi) (outside_of_apart' pre.planPad lo hi)
  obtain ⟨at_, le⟩ := fieldPlan_at fields fa j hj planM
  exact ⟨at_, by simp only [fieldPlan]; omega⟩

/-! ### The forward pass -/

/-- The fields driver's forward pass: each field's start, end when fixed, and kind, into the table. -/
abbrev fwdLoop : Stmt :=
  while_ (lt RootFields.j RootFields.n) [RootFields.ent ::= RootFields.t + 24 * RootFields.j,
    callInto RootFields.fx "ssz_plan_fixed" [RootFields.q], st (RootFields.ent + 16) RootFields.fx,
    ifElse RootFields.fx [callInto RootFields.w "ssz_plan_fixed_width" [RootFields.q],
        st RootFields.ent (RootFields.src + RootFields.pos),
        st (RootFields.ent + 8) (RootFields.src + RootFields.pos + RootFields.w),
        RootFields.pos ::= RootFields.pos + RootFields.w]
      [st RootFields.ent (RootFields.src + ld4 (RootFields.src + RootFields.pos)),
        RootFields.pos ::= RootFields.pos + 4],
    callInto RootFields.q "ssz_plan_next" [RootFields.q], RootFields.j ::= RootFields.j + 1]

/-- What the forward pass keeps: the variables, the first entries of the table, and memory outside the table. -/
def FwdAt (mem0 : Memory) (fields : List Desc) (fa base start stop out ctx : Nat) (b : ByteArray) (e : Env)
    (mm : Memory) (j : Nat) : Prop :=
  j ≤ fields.length ∧ FieldsEnv e fa fields.length (base + start) (stop - start) out ctx ∧
    e 7 = UInt64.ofNat (Desc.leadingWidth (fields.take j)) ∧ e 8 = UInt64.ofNat j ∧
    e 14 = UInt64.ofNat (fieldPlan fa fields j) ∧
    RangeTable mm (out + 32 * fields.length) base fields b start stop j fields.length ∧
    ∀ a, ¬ (out + 32 * fields.length ≤ a ∧ a < out + 32 * fields.length + 24 * fields.length) → mm a = mem0 a

set_option maxHeartbeats 8000000 in
/-- One pass of the forward loop writes the next field's entry. -/
theorem fwdBody_ends {m : Module} {w : World} (fns : RangeFns m) {fields : List Desc} {sp : Nat}
    (room : ∀ f ∈ fields, w.stackLo + rootStack f + 256 ≤ sp) {mem0 : Memory}
    {fa base start stop out span ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : FieldsPre w mem0 fields fa base start stop out span ctx table zeros pad mask b)
    {e : Env} {mm : Memory} {j : Nat} (at_ : FwdAt mem0 fields fa base start stop out ctx b e mm j)
    (hlt : j < fields.length) :
    Ends m w sp e mm (.block [RootFields.ent ::= RootFields.t + 24 * RootFields.j,
      callInto RootFields.fx "ssz_plan_fixed" [RootFields.q], st (RootFields.ent + 16) RootFields.fx,
      ifElse RootFields.fx [callInto RootFields.w "ssz_plan_fixed_width" [RootFields.q],
          st RootFields.ent (RootFields.src + RootFields.pos),
          st (RootFields.ent + 8) (RootFields.src + RootFields.pos + RootFields.w),
          RootFields.pos ::= RootFields.pos + RootFields.w]
        [st RootFields.ent (RootFields.src + ld4 (RootFields.src + RootFields.pos)),
          RootFields.pos ::= RootFields.pos + 4],
      callInto RootFields.q "ssz_plan_next" [RootFields.q], RootFields.j ::= RootFields.j + 1])
      fun e' mm' => FwdAt mem0 fields fa base start stop out ctx b e' mm' (j + 1) := by
  obtain ⟨-, ev, hpos, hj8, hq, tab, frame⟩ := at_
  have ab := access_bound pre.bAcc
  have ar := access_bound pre.rAcc
  have roomR := pre.room
  have rs := pre.rSlack
  have bound : addressBound = 2 ^ 63 := rfl
  have lead := pre.lead
  have inside := pre.inside
  have ordered := pre.ordered
  have rB := pre.rB
  simp only [Apart] at rB
  have mf : fields[j] ∈ fields := List.getElem_mem hlt
  have soundJ := pre.sound _ mf
  have thinJ := pre.thin _ mf
  have stackJ : w.stackLo + 112 * fields[j].nesting ≤ sp := by
    have := room _ mf; simp only [rootStack] at this; omega
  have walkJ : w.stackLo + walkLevel * fields[j].nesting ≤ sp := by rw [walkLevel_eq]; exact stackJ
  have lwLe := leadingWidth_take_le fields (j + 1)
  have lwStep := leadingWidth_take_succ fields j hlt
  -- Memory outside the table is as at the start, so it holds the plans and the encoding.
  have planOf : ∀ mm' : Memory, (∀ a, ¬ (out + 32 * fields.length ≤ a ∧
      a < out + 32 * fields.length + 24 * fields.length) → mm' a = mem0 a) →
      WordsAt w mm' (fieldPlan fa fields j) (Plan.words fields[j]) := fun mm' fr =>
    (pre.planAt (fun a o _ => fr a fun h => o ⟨by omega, by omega⟩) j hlt).1
  have acc : ∀ c, c + 8 ≤ 24 → w.access (out + 32 * fields.length + 24 * j + c) 8 = true := fun c hc =>
    access_sub pre.rAcc (by omega) (by omega)
  have acc0 : w.access (out + 32 * fields.length + 24 * j) 8 = true := by simpa using acc 0 (by omega)
  -- The entry's address, and whether the field is fixed.
  have r1 := Runs.set' (m := m) (w := w) (sp := sp) (env := e) (mem := mm) (x := 12)
    (eval_add (eval_var ev.tV) (eval_mul (eval_lit 24) (eval_var hj8)))
  have ev1 := ev.write (x := 12) (UInt64.ofNat (out + 32 * fields.length + 24 * j)) (by decide)
  have q1 : Asm.assign e 12 (UInt64.ofNat (out + 32 * fields.length + 24 * j)) 14 =
      UInt64.ofNat (fieldPlan fa fields j) := by rw [assign_ne (by decide)]; exact hq
  have ent1 : Asm.assign e 12 (UInt64.ofNat (out + 32 * fields.length + 24 * j)) 12 =
      UInt64.ofNat (out + 32 * fields.length + 24 * j) := assign_eq
  have pos1 : Asm.assign e 12 (UInt64.ofNat (out + 32 * fields.length + 24 * j)) 7 =
      UInt64.ofNat (Desc.leadingWidth (fields.take j)) := by rw [assign_ne (by decide)]; exact hpos
  have j1 : Asm.assign e 12 (UInt64.ofNat (out + 32 * fields.length + 24 * j)) 8 = UInt64.ofNat j := by
    rw [assign_ne (by decide)]; exact hj8
  generalize Asm.assign e 12 (UInt64.ofNat (out + 32 * fields.length + 24 * j)) = E1 at r1 ev1 q1 ent1 pos1 j1
  have fixedC := planFixed_calls fns.roots.plan fields[j] (fieldPlan fa fields j) sp mm (planOf mm frame) soundJ
    stackJ
  have r2 := Runs.call (m := m) (sp := sp) (env := E1) (mem := mm) (dst := 9) (args := [RootFields.q])
    (by simp only [List.mapM_cons, List.mapM_nil, eval_var q1]; rfl) fixedC
  have ev2 := ev1.write (x := 9) (bitOf (hasWidth fields[j])) (by decide)
  have q2 : Asm.assign E1 9 (bitOf (hasWidth fields[j])) 14 = UInt64.ofNat (fieldPlan fa fields j) := by
    rw [assign_ne (by decide)]; exact q1
  have ent2 : Asm.assign E1 9 (bitOf (hasWidth fields[j])) 12 = UInt64.ofNat (out + 32 * fields.length + 24 * j) := by
    rw [assign_ne (by decide)]; exact ent1
  have pos2 : Asm.assign E1 9 (bitOf (hasWidth fields[j])) 7 = UInt64.ofNat (Desc.leadingWidth (fields.take j)) := by
    rw [assign_ne (by decide)]; exact pos1
  have j2 : Asm.assign E1 9 (bitOf (hasWidth fields[j])) 8 = UInt64.ofNat j := by
    rw [assign_ne (by decide)]; exact j1
  have fx2 : Asm.assign E1 9 (bitOf (hasWidth fields[j])) 9 = bitOf (hasWidth fields[j]) := assign_eq
  generalize Asm.assign E1 9 (bitOf (hasWidth fields[j])) = E2 at r2 ev2 q2 ent2 pos2 j2 fx2
  have r3 := Runs.st8 (m := m) (sp := sp) (env := E2) (mem := mm) (eval_add (eval_var ent2) (eval_lit 16))
    (eval_var fx2) (acc 16 (by omega))
  have frame1 : ∀ a, ¬ (out + 32 * fields.length ≤ a ∧ a < out + 32 * fields.length + 24 * fields.length) →
      store mm (out + 32 * fields.length + 24 * j + 16) 8 (qwordByte (bitOf (hasWidth fields[j]))) a = mem0 a :=
    fun a o => by rw [store_outside (by omega)]; exact frame a o
  generalize hM1 : store mm (out + 32 * fields.length + 24 * j + 16) 8 (qwordByte (bitOf (hasWidth fields[j]))) = M1
    at r3 frame1
  -- The entry's start, its end when fixed, and the position after the field.
  obtain ⟨E3, M, run4, ev3, pos3, j3, q3, tab3, frame3⟩ : ∃ E3 M, Runs m w sp E2 M1
      (ifElse RootFields.fx [callInto RootFields.w "ssz_plan_fixed_width" [RootFields.q],
          st RootFields.ent (RootFields.src + RootFields.pos),
          st (RootFields.ent + 8) (RootFields.src + RootFields.pos + RootFields.w),
          RootFields.pos ::= RootFields.pos + RootFields.w]
        [st RootFields.ent (RootFields.src + ld4 (RootFields.src + RootFields.pos)),
          RootFields.pos ::= RootFields.pos + 4]) E3 M ∧
      FieldsEnv E3 fa fields.length (base + start) (stop - start) out ctx ∧
      E3 7 = UInt64.ofNat (Desc.leadingWidth (fields.take (j + 1))) ∧ E3 8 = UInt64.ofNat j ∧
      E3 14 = UInt64.ofNat (fieldPlan fa fields j) ∧
      RangeTable M (out + 32 * fields.length) base fields b start stop (j + 1) fields.length ∧
      ∀ a, ¬ (out + 32 * fields.length ≤ a ∧ a < out + 32 * fields.length + 24 * fields.length) → M a = mem0 a := by
    -- Entries before this one are kept by the stores into this one.
    have old : ∀ (M' : Memory), (∀ k < j, ∀ c, c + 8 ≤ 24 →
        readLE M' (out + 32 * fields.length + 24 * k + c) 8 = readLE mm (out + 32 * fields.length + 24 * k + c) 8) →
        ∀ k (hk : k < fields.length), k < j →
          readLE M' (out + 32 * fields.length + 24 * k) 8 = UInt64.ofNat (base + (fieldRg fields b start stop k).1) ∧
          readLE M' (out + 32 * fields.length + 24 * k + 16) 8 = bitOf (hasWidth fields[k]) ∧
          (fields.length ≤ k ∨ hasWidth fields[k] = true → readLE M' (out + 32 * fields.length + 24 * k + 8) 8 =
            UInt64.ofNat (base + (fieldRg fields b start stop k).2)) := by
      intro M' same k hk lt
      obtain ⟨a0, a2, a1⟩ := tab k hk lt
      have s0 := same k lt 0 (by omega)
      simp only [Nat.add_zero] at s0
      exact ⟨by rw [s0, a0], by rw [same k lt 16 (by omega), a2], fun c => by rw [same k lt 8 (by omega), a1 c]⟩
    by_cases fx : hasWidth fields[j] = true
    · have fxv : E2 9 = 1 := by rw [fx2, fx]; rfl
      have rg := fieldRg_fixed (start := start) (stop := stop) (b := b) hlt fx
      have lw1 : Desc.leadingWidth (fields.take (j + 1)) = Desc.leadingWidth (fields.take j) + fixedWidth fields[j] := by
        rw [lwStep, fixedSize_eq, ite_eq_left fx]; rfl
      have widthC := planWidth_calls fns.roots.plan fields[j] (fieldPlan fa fields j) sp M1 (planOf M1 frame1) soundJ
        thinJ stackJ
      have s1 := Runs.call (m := m) (sp := sp) (env := E2) (mem := M1) (dst := 10) (args := [RootFields.q])
        (by simp only [List.mapM_cons, List.mapM_nil, eval_var q2]; rfl) widthC
      have w3 : Asm.assign E2 10 (fixedWidth fields[j]).toUInt64 10 = UInt64.ofNat (fixedWidth fields[j]) := assign_eq
      have src3 : Asm.assign E2 10 (fixedWidth fields[j]).toUInt64 2 = UInt64.ofNat (base + start) :=
        (ev2.write _ (by decide)).srcV
      have p3 : Asm.assign E2 10 (fixedWidth fields[j]).toUInt64 7 = UInt64.ofNat (Desc.leadingWidth (fields.take j)) := by
        rw [assign_ne (by decide)]; exact pos2
      have e3 : Asm.assign E2 10 (fixedWidth fields[j]).toUInt64 12 =
          UInt64.ofNat (out + 32 * fields.length + 24 * j) := by
        rw [assign_ne (by decide)]; exact ent2
      have s2 := Runs.st8 (m := m) (sp := sp) (env := Asm.assign E2 10 (fixedWidth fields[j]).toUInt64) (mem := M1)
        (eval_var e3) (eval_add (eval_var src3) (eval_var p3)) acc0
      have s3 := Runs.st8 (m := m) (sp := sp) (env := Asm.assign E2 10 (fixedWidth fields[j]).toUInt64)
        (mem := store M1 (out + 32 * fields.length + 24 * j) 8
          (qwordByte (UInt64.ofNat (base + start + Desc.leadingWidth (fields.take j)))))
        (eval_add (eval_var e3) (eval_lit 8)) (eval_add (eval_add (eval_var src3) (eval_var p3)) (eval_var w3))
        (acc 8 (by omega))
      have s4 := Runs.set' (m := m) (w := w) (sp := sp) (env := Asm.assign E2 10 (fixedWidth fields[j]).toUInt64)
        (mem := store (store M1 (out + 32 * fields.length + 24 * j) 8
          (qwordByte (UInt64.ofNat (base + start + Desc.leadingWidth (fields.take j)))))
          (out + 32 * fields.length + 24 * j + 8) 8
          (qwordByte (UInt64.ofNat (base + start + Desc.leadingWidth (fields.take j) + fixedWidth fields[j]))))
        (x := 7) (eval_add (eval_var p3) (eval_var w3))
      refine ⟨_, _, Runs.ifElse_true 1 (eval_var fxv) (by decide) (Runs.block_cons s1 (Runs.block_cons s2
        (Runs.block_cons s3 (Runs.block_cons s4 (Runs.block_nil _ _ _ _ _))))),
        (ev2.write _ (by decide)).write _ (by decide), by rw [assign_eq, lw1], ?_, ?_, ?_, ?_⟩
      · rw [assign_ne (by decide), assign_ne (by decide)]; exact j2
      · rw [assign_ne (by decide), assign_ne (by decide)]; exact q2
      · intro k hk lt
        by_cases kj : k < j
        · refine old _ (fun k' lt' c hc => ?_) k hk kj
          rw [readLE_store_word _ _ _ _ (by omega), readLE_store_word _ _ _ _ (by omega), ← hM1,
            readLE_store_word _ _ _ _ (by omega)]
        · obtain rfl : k = j := by omega
          refine ⟨?_, ?_, fun _ => ?_⟩
          · rw [readLE_store_word _ _ _ _ (by omega), readLE_store8, rg, Nat.add_assoc]
          · rw [readLE_store_word _ _ _ _ (by omega), readLE_store_word _ _ _ _ (by omega), ← hM1, readLE_store8]
          · rw [readLE_store8, rg]; congr 1; omega
      · intro a o
        rw [store_outside (by omega), store_outside (by omega)]
        exact frame1 a o
    · have fxf : hasWidth fields[j] = false := by simpa using fx
      have fxv : E2 9 = 0 := by rw [fx2, fxf]; rfl
      have rg := fieldRg_body (start := start) (stop := stop) (b := b) hlt fxf
      have lw1 : Desc.leadingWidth (fields.take (j + 1)) = Desc.leadingWidth (fields.take j) + 4 := by
        rw [lwStep, fixedSize_eq, ite_eq_right fx]; rfl
      have offIn : start + Desc.leadingWidth (fields.take j) + 4 ≤ b.size := by omega
      have ld : eval w E2 M1 (ld4 (RootFields.src + RootFields.pos)) =
          some (UInt64.ofNat (offsetAt b (start + Desc.leadingWidth (fields.take j)))) := by
        have mm0 : ∀ q < 4, M1 (base + (start + Desc.leadingWidth (fields.take j)) + q) =
            mem0 (base + (start + Desc.leadingWidth (fields.take j)) + q) := fun q hq =>
          frame1 _ (by omega)
        rw [eval_ld4_of (eval_add (eval_var ev2.srcV) (eval_var pos2)) (access_sub pre.bAcc (by omega) (by omega)),
          Nat.add_assoc, readLE_congr M1 mem0 _ 4 mm0, readLE_offsetAt pre.holds pre.bAcc _ (by omega)]
      have s1 := Runs.st8 (m := m) (sp := sp) (env := E2) (mem := M1) (eval_var ent2)
        (eval_add (eval_var ev2.srcV) ld) acc0
      have s2 := Runs.set' (m := m) (w := w) (sp := sp) (env := E2)
        (mem := store M1 (out + 32 * fields.length + 24 * j) 8
          (qwordByte (UInt64.ofNat (base + start + offsetAt b (start + Desc.leadingWidth (fields.take j))))))
        (x := 7) (eval_add (eval_var pos2) (eval_lit 4))
      refine ⟨_, _, Runs.ifElse_false (eval_var fxv) (Runs.block_cons s1 (Runs.block_cons s2
        (Runs.block_nil _ _ _ _ _))), ev2.write _ (by decide), by rw [assign_eq, lw1], ?_, ?_, ?_, ?_⟩
      · rw [assign_ne (by decide)]; exact j2
      · rw [assign_ne (by decide)]; exact q2
      · intro k hk lt
        by_cases kj : k < j
        · refine old _ (fun k' lt' c hc => ?_) k hk kj
          rw [readLE_store_word _ _ _ _ (by omega), ← hM1, readLE_store_word _ _ _ _ (by omega)]
        · obtain rfl : k = j := by omega
          refine ⟨?_, ?_, fun h => ?_⟩
          · rw [readLE_store8, rg, Nat.add_assoc]
          · rw [readLE_store_word _ _ _ _ (by omega), ← hM1, readLE_store8]
          · rcases h with h | h
            · omega
            · rw [fxf] at h; cases h
      · intro a o
        rw [store_outside (by omega)]
        exact frame1 a o
  -- The next field's plan, and the next field.
  have nextC := next_ok m w fns.roots.plan.codec fields[j] soundJ sp M (fieldPlan fa fields j) (planOf M frame3) walkJ
  have r5 := Runs.call (m := m) (sp := sp) (env := E3) (mem := M) (dst := 14) (args := [RootFields.q])
    (by simp only [List.mapM_cons, List.mapM_nil, eval_var q3]; rfl) nextC
  have r6 := Runs.set' (m := m) (w := w) (sp := sp)
    (env := Asm.assign E3 14 (fieldPlan fa fields j + 8 * (Plan.words fields[j]).length).toUInt64) (mem := M) (x := 8)
    (eval_add (eval_var (show Asm.assign E3 14 _ 8 = UInt64.ofNat j by rw [assign_ne (by decide)]; exact j3))
      (eval_lit 1))
  refine ⟨_, M, Runs.block_cons r1 (Runs.block_cons r2 (Runs.block_cons r3 (Runs.block_cons run4
    (Runs.block_cons r5 (Runs.block_cons r6 (Runs.block_nil _ _ _ _ _)))))),
    by omega, (ev3.write _ (by decide)).write _ (by decide), ?_, assign_eq, ?_, tab3, frame3⟩
  · rw [assign_ne (by decide), assign_ne (by decide)]; exact pos3
  · rw [assign_ne (by decide), assign_eq, toUInt64_ofNat]
    congr 1
    simp only [fieldPlan]
    rw [wordsAll_take_succ fields j hlt]
    omega

/-- The forward pass writes every field's start and kind, and the end of every fixed field. -/
theorem fwdLoop_ends {m : Module} {w : World} (fns : RangeFns m) {fields : List Desc} {sp : Nat}
    (room : ∀ f ∈ fields, w.stackLo + rootStack f + 256 ≤ sp) {mem0 : Memory}
    {fa base start stop out span ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : FieldsPre w mem0 fields fa base start stop out span ctx table zeros pad mask b) {env : Env}
    (at0 : FwdAt mem0 fields fa base start stop out ctx b env mem0 0) :
    Ends m w sp env mem0 fwdLoop fun e mm => FwdAt mem0 fields fa base start stop out ctx b e mm fields.length := by
  have nSmall : fields.length < 2 ^ 64 := by
    have := pre.room; have := pre.rSlack; have : addressBound = 2 ^ 63 := rfl; omega
  refine (Ends.loop (fun e mm => ∃ j, FwdAt mem0 fields fa base start stop out ctx b e mm j)
    (fun e _ => fields.length - (e 8).toNat) ⟨0, at0⟩ ?_ ?_).mono ?_
  · rintro e mm ⟨j, hj, ev, -, hj8, -⟩
    exact ⟨_, eval_lt (eval_var hj8) (eval_var ev.nV) (by omega) nSmall⟩
  · rintro e mm v ⟨j, at_⟩ hv nz
    obtain ⟨hj, ev, -, hj8, -⟩ := id at_
    have c := eval_lt (w := w) (env := e) (mem := mm) (eval_var hj8) (eval_var ev.nV) (by omega) nSmall
    rw [hv] at c
    have hlt : j < fields.length := by
      by_cases h : j < fields.length
      · exact h
      · rw [ite_eq_right h] at c; cases c; exact absurd rfl nz
    refine (fwdBody_ends fns room pre at_ hlt).mono fun e' mm' at' => ⟨⟨j + 1, at'⟩, ?_⟩
    rw [at'.2.2.2.1, hj8, ofNat_toNat (by omega), ofNat_toNat (by omega)]
    omega
  · rintro e mm ⟨⟨j, at_⟩, exit⟩
    obtain ⟨hj, ev, -, hj8, -⟩ := id at_
    rw [eval_lt (eval_var hj8) (eval_var ev.nV) (by omega) nSmall] at exit
    have : j = fields.length := by
      by_cases h : j < fields.length
      · rw [ite_eq_left h] at exit; cases exit
      · omega
    rw [this] at at_
    exact at_

/-! ### The backward pass -/

/-- The fields driver's backward pass: each body closes where the next one starts, the last at the end. -/
abbrev bwdLoop : Stmt :=
  while_ (lt 0 RootFields.j) [RootFields.j ::= RootFields.j - 1, RootFields.ent ::= RootFields.t + 24 * RootFields.j,
    when (eq (ld (RootFields.ent + 16)) 0) [st (RootFields.ent + 8) RootFields.nextStart,
      RootFields.nextStart ::= ld RootFields.ent]]

/-- What the backward pass keeps: the variables, the next body's start, the table closed from a field on. -/
def BwdAt (mem0 : Memory) (fields : List Desc) (fa base start stop out ctx : Nat) (b : ByteArray) (e : Env)
    (mm : Memory) (j : Nat) : Prop :=
  j ≤ fields.length ∧ FieldsEnv e fa fields.length (base + start) (stop - start) out ctx ∧ e 8 = UInt64.ofNat j ∧
    e 11 = UInt64.ofNat (base + start + nextBody fields b start stop j) ∧
    RangeTable mm (out + 32 * fields.length) base fields b start stop fields.length j ∧
    ∀ a, ¬ (out + 32 * fields.length ≤ a ∧ a < out + 32 * fields.length + 24 * fields.length) → mm a = mem0 a

set_option maxHeartbeats 4000000 in
/-- One pass of the backward loop closes the body before the ones already closed. -/
theorem bwdBody_ends {m : Module} {w : World} {fields : List Desc} {sp : Nat} {mem0 : Memory}
    {fa base start stop out span ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : FieldsPre w mem0 fields fa base start stop out span ctx table zeros pad mask b)
    {e : Env} {mm : Memory} {j : Nat} (at_ : BwdAt mem0 fields fa base start stop out ctx b e mm (j + 1)) :
    Ends m w sp e mm (.block [RootFields.j ::= RootFields.j - 1, RootFields.ent ::= RootFields.t + 24 * RootFields.j,
      when (eq (ld (RootFields.ent + 16)) 0) [st (RootFields.ent + 8) RootFields.nextStart,
        RootFields.nextStart ::= ld RootFields.ent]])
      fun e' mm' => BwdAt mem0 fields fa base start stop out ctx b e' mm' j := by
  obtain ⟨hj, ev, hj8, hnext, tab, frame⟩ := at_
  have hlt : j < fields.length := by omega
  have ar := access_bound pre.rAcc
  have roomR := pre.room
  have acc : ∀ c, c + 8 ≤ 24 → w.access (out + 32 * fields.length + 24 * j + c) 8 = true := fun c hc =>
    access_sub pre.rAcc (by omega) (by omega)
  have acc0 : w.access (out + 32 * fields.length + 24 * j) 8 = true := by simpa using acc 0 (by omega)
  have r1 := Runs.set' (m := m) (w := w) (sp := sp) (env := e) (mem := mm) (x := 8)
    (eval_sub (eval_var hj8) (eval_lit 1) (by omega))
  have j1 : Asm.assign e 8 (UInt64.ofNat (j + 1 - 1)) 8 = UInt64.ofNat j := by rw [assign_eq]; congr 1
  have r2 := Runs.set' (m := m) (w := w) (sp := sp) (env := Asm.assign e 8 (UInt64.ofNat (j + 1 - 1))) (mem := mm)
    (x := 12) (eval_add (eval_var (ev.write _ (by decide)).tV) (eval_mul (eval_lit 24) (eval_var j1)))
  have ev2 := (ev.write (x := 8) (UInt64.ofNat (j + 1 - 1)) (by decide)).write (x := 12)
    (UInt64.ofNat (out + 32 * fields.length + 24 * j)) (by decide)
  have j2 : Asm.assign (Asm.assign e 8 (UInt64.ofNat (j + 1 - 1))) 12
      (UInt64.ofNat (out + 32 * fields.length + 24 * j)) 8 = UInt64.ofNat j := by
    rw [assign_ne (by decide)]; exact j1
  have ent2 : Asm.assign (Asm.assign e 8 (UInt64.ofNat (j + 1 - 1))) 12
      (UInt64.ofNat (out + 32 * fields.length + 24 * j)) 12 = UInt64.ofNat (out + 32 * fields.length + 24 * j) :=
    assign_eq
  have n2 : Asm.assign (Asm.assign e 8 (UInt64.ofNat (j + 1 - 1))) 12
      (UInt64.ofNat (out + 32 * fields.length + 24 * j)) 11 =
      UInt64.ofNat (base + start + nextBody fields b start stop (j + 1)) := by
    rw [assign_ne (by decide), assign_ne (by decide)]; exact hnext
  generalize Asm.assign (Asm.assign e 8 (UInt64.ofNat (j + 1 - 1))) 12
    (UInt64.ofNat (out + 32 * fields.length + 24 * j)) = E2 at r2 ev2 j2 ent2 n2
  obtain ⟨a0, a2, -⟩ := tab j hlt (by omega)
  have kind := eval_ld (w := w) (env := E2) (mem := mm) (eval_add (eval_var ent2) (eval_lit 16)) (acc 16 (by omega))
  rw [a2] at kind
  have step := nextBody_step (b := b) (start := start) (stop := stop) hlt
  by_cases fx : hasWidth fields[j] = true
  · -- A fixed field has its end already, and leaves the next body's start alone.
    have kind' : eval w E2 mm (ld (RootFields.ent + 16)) = some (UInt64.ofNat 1) := by rw [kind, fx]; rfl
    have c := eval_eq (w := w) (env := E2) (mem := mm) (b := 0) kind' (eval_lit 0) (by decide) (by decide)
    rw [ite_eq_right (by decide)] at c
    refine ⟨_, mm, Runs.block_cons r1 (Runs.block_cons r2 (Runs.block_cons (Runs.when_false c)
      (Runs.block_nil _ _ _ _ _))), by omega, ev2, j2, by rw [n2, step, ite_eq_left fx], fun k hk lt => ?_, frame⟩
    obtain ⟨b0, b2, b1⟩ := tab k hk lt
    refine ⟨b0, b2, fun h => b1 ?_⟩
    rcases h with h | h
    · by_cases kj : k = j
      · subst kj; exact Or.inr fx
      · exact Or.inl (by omega)
    · exact Or.inr h
  · -- A body closes at the next body's start, and its own start becomes the next.
    have fxf : hasWidth fields[j] = false := by simpa using fx
    have rg := fieldRg_body (b := b) (start := start) (stop := stop) hlt fxf
    have kind' : eval w E2 mm (ld (RootFields.ent + 16)) = some (UInt64.ofNat 0) := by rw [kind, fxf]; rfl
    have c := eval_eq (w := w) (env := E2) (mem := mm) (b := 0) kind' (eval_lit 0) (by decide) (by decide)
    rw [ite_eq_left rfl] at c
    have s1 := Runs.st8 (m := m) (sp := sp) (env := E2) (mem := mm) (eval_add (eval_var ent2) (eval_lit 8))
      (eval_var n2) (acc 8 (by omega))
    have ld0 := eval_ld (w := w) (env := E2)
      (mem := store mm (out + 32 * fields.length + 24 * j + 8) 8
        (qwordByte (UInt64.ofNat (base + start + nextBody fields b start stop (j + 1)))))
      (eval_var ent2) acc0
    rw [readLE_store_word _ _ _ _ (by omega), a0, rg] at ld0
    have s2 := Runs.set' (m := m) (w := w) (sp := sp) (x := 11) ld0
    refine ⟨_, _, Runs.block_cons r1 (Runs.block_cons r2 (Runs.block_cons
      (Runs.when_true 1 c (by decide) (Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_nil _ _ _ _ _))))
      (Runs.block_nil _ _ _ _ _))), by omega, ev2.write _ (by decide), ?_, ?_, fun k hk lt => ?_, fun a o => ?_⟩
    · rw [assign_ne (by decide)]; exact j2
    · rw [assign_eq, step, ite_eq_right fx, Nat.add_assoc]
    · obtain ⟨b0, b2, b1⟩ := tab k hk lt
      by_cases kj : k = j
      · subst kj
        refine ⟨by rw [readLE_store_word _ _ _ _ (by omega), b0], by rw [readLE_store_word _ _ _ _ (by omega), b2],
          fun _ => ?_⟩
        rw [readLE_store8, rg, Nat.add_assoc]
      · refine ⟨by rw [readLE_store_word _ _ _ _ (by omega), b0], by rw [readLE_store_word _ _ _ _ (by omega), b2],
          fun h => ?_⟩
        rw [readLE_store_word _ _ _ _ (by omega)]
        refine b1 ?_
        rcases h with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h
    · rw [store_outside (by omega)]; exact frame a o

/-- The backward pass closes every body. -/
theorem bwdLoop_ends {m : Module} {w : World} {fields : List Desc} {sp : Nat} {mem0 : Memory}
    {fa base start stop out span ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : FieldsPre w mem0 fields fa base start stop out span ctx table zeros pad mask b) {env : Env} {mem : Memory}
    (at0 : BwdAt mem0 fields fa base start stop out ctx b env mem fields.length) :
    Ends m w sp env mem bwdLoop fun e mm => BwdAt mem0 fields fa base start stop out ctx b e mm 0 := by
  have nSmall : fields.length < 2 ^ 64 := by
    have := pre.room; have := pre.rSlack; have : addressBound = 2 ^ 63 := rfl; omega
  refine (Ends.loop (fun e mm => ∃ j, BwdAt mem0 fields fa base start stop out ctx b e mm j)
    (fun e _ => (e 8).toNat) ⟨_, at0⟩ ?_ ?_).mono ?_
  · rintro e mm ⟨j, hj, -, hj8, -⟩
    exact ⟨_, eval_lt (eval_lit 0) (eval_var hj8) (by decide) (by omega)⟩
  · rintro e mm v ⟨j, at_⟩ hv nz
    obtain ⟨hj, -, hj8, -⟩ := id at_
    have c := eval_lt (w := w) (env := e) (mem := mm) (eval_lit 0) (eval_var hj8) (by decide) (by omega)
    rw [hv] at c
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := by
      by_cases h : 0 < j
      · exact ⟨j - 1, by omega⟩
      · rw [ite_eq_right h] at c; cases c; exact absurd rfl nz
    refine (bwdBody_ends pre at_).mono fun e' mm' at' => ⟨⟨i, at'⟩, ?_⟩
    rw [at'.2.2.1, hj8, ofNat_toNat (by omega), ofNat_toNat (by omega)]
    omega
  · rintro e mm ⟨⟨j, at_⟩, exit⟩
    obtain ⟨hj, -, hj8, -⟩ := id at_
    rw [eval_lt (eval_lit 0) (eval_var hj8) (by decide) (by omega)] at exit
    have : j = 0 := by
      by_cases h : 0 < j
      · rw [ite_eq_left h] at exit; cases exit
      · omega
    rw [this] at at_
    exact at_

/-! ### The roots -/

/-- The fields driver's last pass: each field rooted from its range into its node. -/
abbrev finLoop : Stmt :=
  while_ (lt RootFields.j RootFields.n) [RootFields.ent ::= RootFields.t + 24 * RootFields.j,
    callInto RootFields.sink "ssz_root_of" [RootFields.q, ld RootFields.ent, ld (RootFields.ent + 8) - ld RootFields.ent,
      RootFields.out + 32 * RootFields.j, RootFields.t + 24 * RootFields.n, RootFields.ctx],
    callInto RootFields.q "ssz_plan_next" [RootFields.q], RootFields.j ::= RootFields.j + 1]

/-- What the last pass keeps: the variables, the table, the roots so far, and memory outside the region. -/
def FinAt (mem0 : Memory) (fields : List Desc) (fa base start stop out span ctx pad : Nat) (b : ByteArray) (e : Env)
    (mm : Memory) (j : Nat) : Prop :=
  j ≤ fields.length ∧ FieldsEnv e fa fields.length (base + start) (stop - start) out ctx ∧ e 8 = UInt64.ofNat j ∧
    e 14 = UInt64.ofNat (fieldPlan fa fields j) ∧
    RangeTable mm (out + 32 * fields.length) base fields b start stop fields.length 0 ∧
    (∀ k (hk : k < fields.length), k < j → nodeAt mm (out + 32 * k) =
      (rootOf fields[k] b (fieldRg fields b start stop k).1 (fieldRg fields b start stop k).2).data) ∧
    ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm a = mem0 a

set_option maxHeartbeats 8000000 in
/-- One pass of the last loop roots the next field into its node. -/
theorem finBody_ends {m : Module} {w : World} (fns : RangeFns m) {fields : List Desc}
    (ih : ∀ f ∈ fields, RootOfOk m w f) {sp : Nat} (room : ∀ f ∈ fields, w.stackLo + rootStack f + 256 ≤ sp)
    {mem0 : Memory} {fa base start stop out span ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : FieldsPre w mem0 fields fa base start stop out span ctx table zeros pad mask b)
    {e : Env} {mm : Memory} {j : Nat} (at_ : FinAt mem0 fields fa base start stop out span ctx pad b e mm j)
    (hlt : j < fields.length) :
    Ends m w sp e mm (.block [RootFields.ent ::= RootFields.t + 24 * RootFields.j,
      callInto RootFields.sink "ssz_root_of" [RootFields.q, ld RootFields.ent,
        ld (RootFields.ent + 8) - ld RootFields.ent, RootFields.out + 32 * RootFields.j,
        RootFields.t + 24 * RootFields.n, RootFields.ctx],
      callInto RootFields.q "ssz_plan_next" [RootFields.q], RootFields.j ::= RootFields.j + 1])
      fun e' mm' => FinAt mem0 fields fa base start stop out span ctx pad b e' mm' (j + 1) := by
  obtain ⟨-, ev, hj8, hq, tab, roots, frame⟩ := at_
  have ar := access_bound pre.rAcc
  have roomR := pre.room
  have rs := pre.rSlack
  have bound : addressBound = 2 ^ 63 := rfl
  have rPad := pre.rPad
  simp only [Apart] at rPad
  have mf : fields[j] ∈ fields := List.getElem_mem hlt
  have soundJ := pre.sound _ mf
  have walkJ : w.stackLo + walkLevel * fields[j].nesting ≤ sp := by
    have := room _ mf; rw [walkLevel_eq]; simp only [rootStack] at this; omega
  obtain ⟨lo, ord, hiStop, accepted⟩ := pre.ranges j hlt
  obtain ⟨a0, -, a1⟩ := tab j hlt hlt
  have a1' := a1 (Or.inl (Nat.zero_le _))
  generalize hr : fieldRg fields b start stop j = r at lo ord hiStop accepted a0 a1'
  have acc : ∀ c, c + 8 ≤ 24 → w.access (out + 32 * fields.length + 24 * j + c) 8 = true := fun c hc =>
    access_sub pre.rAcc (by omega) (by omega)
  have acc0 : w.access (out + 32 * fields.length + 24 * j) 8 = true := by simpa using acc 0 (by omega)
  have r1 := Runs.set' (m := m) (w := w) (sp := sp) (env := e) (mem := mm) (x := 12)
    (eval_add (eval_var ev.tV) (eval_mul (eval_lit 24) (eval_var hj8)))
  have ev1 := ev.write (x := 12) (UInt64.ofNat (out + 32 * fields.length + 24 * j)) (by decide)
  have q1 : Asm.assign e 12 (UInt64.ofNat (out + 32 * fields.length + 24 * j)) 14 =
      UInt64.ofNat (fieldPlan fa fields j) := by rw [assign_ne (by decide)]; exact hq
  have ent1 : Asm.assign e 12 (UInt64.ofNat (out + 32 * fields.length + 24 * j)) 12 =
      UInt64.ofNat (out + 32 * fields.length + 24 * j) := assign_eq
  have j1 : Asm.assign e 12 (UInt64.ofNat (out + 32 * fields.length + 24 * j)) 8 = UInt64.ofNat j := by
    rw [assign_ne (by decide)]; exact hj8
  generalize Asm.assign e 12 (UInt64.ofNat (out + 32 * fields.length + 24 * j)) = E1 at r1 ev1 q1 ent1 j1
  -- The field's range, from the table, and its root by the dispatcher on the field's type.
  have grow := varNeed_mono fields[j] (show r.2 - r.1 ≤ stop - start by omega)
  have most := fieldsVarNeed_mem fields (stop - start) 0 fields[j] mf
  have frameP : ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm a = mem0 a := frame
  have childPre : RangePre w mm fields[j] (fieldPlan fa fields j) base r.1 r.2 (out + 32 * j)
      (out + 32 * fields.length + 24 * fields.length) ctx table zeros pad mask b := by
    obtain ⟨planJ, planIn⟩ := pre.planAt frameP j hlt
    exact rangePre_of (pre.ready.within (o := out) (n := span) pre.rCtx pre.rTable pre.rZeros frameP) planJ
      (fun x hx => pre.fits x (fieldWords_mem fields j hlt x hx))
      (pre.holds.congr fun i hi => frameP _ (outside_of_apart pre.rB (by omega) (by omega))
        (outside_of_apart' pre.bPad (by omega) (by omega)))
      pre.bAcc ord (by have := pre.inside; omega) pre.small pre.spread soundJ (pre.thin _ mf) accepted
      (by have := pre.below; omega) pre.rAcc pre.rSlack pre.rB pre.rPad pre.rCtx pre.rTable pre.rZeros
      (apart_sub' pre.rPlan (by simp only [fieldPlan]; omega) planIn) pre.bPad
      (apart_comm (apart_sub' (apart_comm pre.planPad) (by simp only [fieldPlan]; omega) planIn))
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by simp only [Apart]; omega) pre.usize
  obtain ⟨mm', call, root, -, keep⟩ := ih _ mf sp mm (fieldPlan fa fields j) base r.1 r.2 (out + 32 * j)
    (out + 32 * fields.length + 24 * fields.length) ctx table zeros pad mask b (room _ mf) childPre
  have startW := eval_ld (w := w) (env := E1) (mem := mm) (eval_var ent1) acc0
  rw [a0] at startW
  have endW := eval_ld (w := w) (env := E1) (mem := mm) (eval_add (eval_var ent1) (eval_lit 8)) (acc 8 (by omega))
  rw [a1'] at endW
  have r2 := Runs.call (m := m) (sp := sp) (env := E1) (mem := mm) (dst := 13)
    (args := [RootFields.q, ld RootFields.ent, ld (RootFields.ent + 8) - ld RootFields.ent,
      RootFields.out + 32 * RootFields.j, RootFields.t + 24 * RootFields.n, RootFields.ctx])
    (by
      have len := eval_sub endW startW (by omega)
      rw [show base + r.2 - (base + r.1) = r.2 - r.1 by omega] at len
      simp only [List.mapM_cons, List.mapM_nil, eval_var q1, startW, len,
        eval_add (eval_var ev1.outV) (eval_mul (eval_lit 32) (eval_var j1)),
        eval_add (eval_var ev1.tV) (eval_mul (eval_lit 24) (eval_var ev1.nV)), eval_var ev1.ctxV]
      rfl) call
  -- Memory after the root: the table and the earlier roots are kept.
  have frame2 : ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm' a = mem0 a :=
    fun a o pd => by
      rw [keep a (fun h => o ⟨by omega, by omega⟩) (fun h => o ⟨by omega, by omega⟩) pd]; exact frame a o pd
  have planJ' := (pre.planAt frame2 j hlt).1
  have nextC := next_ok m w fns.roots.plan.codec fields[j] soundJ sp mm' (fieldPlan fa fields j) planJ' walkJ
  have r3 := Runs.call (m := m) (sp := sp) (env := Asm.assign E1 13 0) (mem := mm') (dst := 14)
    (args := [RootFields.q])
    (by simp only [List.mapM_cons, List.mapM_nil, eval_var (show Asm.assign E1 13 0 14 =
      UInt64.ofNat (fieldPlan fa fields j) by rw [assign_ne (by decide)]; exact q1)]; rfl) nextC
  have r4 := Runs.set' (m := m) (w := w) (sp := sp)
    (env := Asm.assign (Asm.assign E1 13 0) 14 (fieldPlan fa fields j + 8 * (Plan.words fields[j]).length).toUInt64)
    (mem := mm') (x := 8)
    (eval_add (eval_var (show Asm.assign (Asm.assign E1 13 0) 14 _ 8 = UInt64.ofNat j by
      rw [assign_ne (by decide), assign_ne (by decide)]; exact j1)) (eval_lit 1))
  refine ⟨_, mm', Runs.block_cons r1 (Runs.block_cons r2 (Runs.block_cons r3 (Runs.block_cons r4
    (Runs.block_nil _ _ _ _ _)))), by omega, ((ev1.write _ (by decide)).write _ (by decide)).write _ (by decide),
    assign_eq, ?_, tab.congr fun a lo hi => keep a (by omega) (by omega) (by omega), fun k hk lt => ?_, frame2⟩
  · rw [assign_ne (by decide), assign_eq, toUInt64_ofNat]
    congr 1
    simp only [fieldPlan]
    rw [wordsAll_take_succ fields j hlt]
    omega
  · by_cases kj : k = j
    · subst kj; rw [hr]; exact root
    · rw [nodeAt_congr (m₂ := mm) fun q hq => keep _ (by omega) (by omega) (by omega)]
      exact roots k hk (by omega)

/-- The last pass roots every field into its node. -/
theorem finLoop_ends {m : Module} {w : World} (fns : RangeFns m) {fields : List Desc}
    (ih : ∀ f ∈ fields, RootOfOk m w f) {sp : Nat} (room : ∀ f ∈ fields, w.stackLo + rootStack f + 256 ≤ sp)
    {mem0 : Memory} {fa base start stop out span ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : FieldsPre w mem0 fields fa base start stop out span ctx table zeros pad mask b) {env : Env} {mem : Memory}
    (at0 : FinAt mem0 fields fa base start stop out span ctx pad b env mem 0) :
    Ends m w sp env mem finLoop fun e mm =>
      FinAt mem0 fields fa base start stop out span ctx pad b e mm fields.length := by
  have nSmall : fields.length < 2 ^ 64 := by
    have := pre.room; have := pre.rSlack; have : addressBound = 2 ^ 63 := rfl; omega
  refine (Ends.loop (fun e mm => ∃ j, FinAt mem0 fields fa base start stop out span ctx pad b e mm j)
    (fun e _ => fields.length - (e 8).toNat) ⟨0, at0⟩ ?_ ?_).mono ?_
  · rintro e mm ⟨j, hj, ev, hj8, -⟩
    exact ⟨_, eval_lt (eval_var hj8) (eval_var ev.nV) (by omega) nSmall⟩
  · rintro e mm v ⟨j, at_⟩ hv nz
    obtain ⟨hj, ev, hj8, -⟩ := id at_
    have c := eval_lt (w := w) (env := e) (mem := mm) (eval_var hj8) (eval_var ev.nV) (by omega) nSmall
    rw [hv] at c
    have hlt : j < fields.length := by
      by_cases h : j < fields.length
      · exact h
      · rw [ite_eq_right h] at c; cases c; exact absurd rfl nz
    refine (finBody_ends fns ih room pre at_ hlt).mono fun e' mm' at' => ⟨⟨j + 1, at'⟩, ?_⟩
    rw [at'.2.2.1, hj8, ofNat_toNat (by omega), ofNat_toNat (by omega)]
    omega
  · rintro e mm ⟨⟨j, at_⟩, exit⟩
    obtain ⟨hj, ev, hj8, -⟩ := id at_
    rw [eval_lt (eval_var hj8) (eval_var ev.nV) (by omega) nSmall] at exit
    have : j = fields.length := by
      by_cases h : j < fields.length
      · rw [ite_eq_left h] at exit; cases exit
      · omega
    rw [this] at at_
    exact at_

/-! ### The fields driver -/

/-- The fields driver's body, in its passes. -/
theorem rootFields_body_eq : RootFields.fn.body = .block [RootFields.t ::= RootFields.out + 32 * RootFields.n,
    RootFields.pos ::= 0, RootFields.j ::= 0, RootFields.q ::= RootFields.f, fwdLoop,
    RootFields.nextStart ::= RootFields.src + RootFields.size, bwdLoop, RootFields.q ::= RootFields.f, finLoop] := rfl

set_option maxHeartbeats 4000000 in
/--
The fields driver writes, at node j of its output, the Lean root of field j from its range.

What a call of the dispatcher on each field's type does is a hypothesis.
Memory changes only in the output region and the padding area.
-/
theorem rootFields_calls {m : Module} {w : World} (fns : RangeFns m) {fields : List Desc}
    (ih : ∀ f ∈ fields, RootOfOk m w f) {sp : Nat} (roomF : w.stackLo + 176 ≤ sp)
    (room : ∀ f ∈ fields, w.stackLo + 176 + rootStack f + 256 ≤ sp)
    {mem : Memory} {fa base start stop out span ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : FieldsPre w mem fields fa base start stop out span ctx table zeros pad mask b) :
    ∃ mem', Calls m w "ssz_root_fields" sp [UInt64.ofNat fa, UInt64.ofNat fields.length, UInt64.ofNat (base + start),
        UInt64.ofNat (stop - start), UInt64.ofNat out, UInt64.ofNat ctx] mem 0 mem' ∧
      (∀ k (hk : k < fields.length), nodeAt mem' (out + 32 * k) =
        (rootOf fields[k] b (fieldRg fields b start stop k).1 (fieldRg fields b start stop k).2).data) ∧
      RootReady w ctx table zeros pad mask mem' ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a := by
  have roomR := pre.room
  let sp' := sp - 8 - 8 * RootFields.fn.frame
  have room' : ∀ f ∈ fields, w.stackLo + rootStack f + 256 ≤ sp' := fun f mf => by
    have := room f mf; simp only [sp', fieldsFrame]; omega
  let E0 := entryEnv [UInt64.ofNat fa, UInt64.ofNat fields.length, UInt64.ofNat (base + start),
    UInt64.ofNat (stop - start), UInt64.ofNat out, UInt64.ofNat ctx]
  have s1 := Runs.set' (m := m) (w := w) (sp := sp') (env := E0) (mem := mem) (x := 6)
    (eval_add (eval_var (show E0 4 = UInt64.ofNat out from rfl))
      (eval_mul (eval_lit 32) (eval_var (show E0 1 = UInt64.ofNat fields.length from rfl))))
  let E1 := Asm.assign E0 6 (UInt64.ofNat (out + 32 * fields.length))
  have s2 := Runs.set' (m := m) (w := w) (sp := sp') (env := E1) (mem := mem) (x := 7) (eval_lit 0)
  have s3 := Runs.set' (m := m) (w := w) (sp := sp') (env := Asm.assign E1 7 (UInt64.ofNat 0)) (mem := mem) (x := 8)
    (eval_lit 0)
  have s4 := Runs.set' (m := m) (w := w) (sp := sp')
    (env := Asm.assign (Asm.assign E1 7 (UInt64.ofNat 0)) 8 (UInt64.ofNat 0)) (mem := mem) (x := 14)
    (eval_var (show Asm.assign (Asm.assign E1 7 (UInt64.ofNat 0)) 8 (UInt64.ofNat 0) 0 = UInt64.ofNat fa from rfl))
  have at0 : FwdAt mem fields fa base start stop out ctx b
      (Asm.assign (Asm.assign (Asm.assign E1 7 (UInt64.ofNat 0)) 8 (UInt64.ofNat 0)) 14 (UInt64.ofNat fa)) mem 0 :=
    ⟨Nat.zero_le _, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, by simp [Asm.assign, Desc.leadingWidth], rfl,
      by simp [Asm.assign, fieldPlan, Plan.wordsAll], fun k _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  obtain ⟨E5, M5, run5, -, ev5, -, j5, -, tab5, frame5⟩ := fwdLoop_ends fns room' pre at0
  have s6 := Runs.set' (m := m) (w := w) (sp := sp') (env := E5) (mem := M5) (x := 11)
    (eval_add (eval_var ev5.srcV) (eval_var ev5.sizeV))
  have bat : BwdAt mem fields fa base start stop out ctx b
      (Asm.assign E5 11 (UInt64.ofNat (base + start + (stop - start)))) M5 fields.length :=
    ⟨Nat.le_refl _, ev5.write _ (by decide), by rw [assign_ne (by decide)]; exact j5,
      by rw [assign_eq, nextBody_end], tab5, frame5⟩
  obtain ⟨E6, M6, run6, -, ev6, j6, -, tab6, frame6⟩ := bwdLoop_ends (sp := sp') pre bat
  have s7 := Runs.set' (m := m) (w := w) (sp := sp') (env := E6) (mem := M6) (x := 14) (eval_var ev6.fV)
  have fat : FinAt mem fields fa base start stop out span ctx pad b (Asm.assign E6 14 (UInt64.ofNat fa)) M6 0 := by
    have ar := access_bound pre.rAcc
    refine ⟨Nat.zero_le _, ev6.write _ (by decide), by rw [assign_ne (by decide)]; exact j6,
      by simp [Asm.assign, fieldPlan, Plan.wordsAll], tab6, fun k _ h => absurd h (Nat.not_lt_zero _),
      fun a o _ => frame6 a fun h => o ⟨by omega, by omega⟩⟩
  obtain ⟨E8, M8, run8, -, -, -, -, -, roots8, frame8⟩ := finLoop_ends (sp := sp') fns ih room' pre fat
  have body : Runs m w sp' E0 mem RootFields.fn.body E8 M8 := by
    rw [rootFields_body_eq]
    exact Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons s3 (Runs.block_cons s4 (Runs.block_cons run5
      (Runs.block_cons s6 (Runs.block_cons run6 (Runs.block_cons s7 (Runs.block_cons run8
        (Runs.block_nil _ _ _ _ _)))))))))
  exact ⟨M8, Calls.fn fns.fields (by rw [fieldsFrame]; exact roomF) rfl body rfl, fun k hk => roots8 k hk hk,
    pre.ready.within (o := out) (n := span) pre.rCtx pre.rTable pre.rZeros frame8, frame8⟩

end EthLib.Consensus.Ssz.Native.Driver
