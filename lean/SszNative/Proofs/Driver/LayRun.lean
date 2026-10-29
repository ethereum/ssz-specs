import SszNative.Proofs.Driver.Lay
import Ssz.Proofs.Codec.Table

/-!
The layout driver `ssz_lay_out` answers what `layOut` answers.

The parts' types are read one after the other along the plan: the one element type of a sequence again and again,
or a struct's fields in order.
The checking loop runs first and the writing loop only once every check passed, so each loop is proved on its own.
-/

namespace Ssz.Native.Driver

open Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Plan

/--
The types the parts are paired with, as the driver walks them along the plan.

Type i's node sits at a position, and the next position is the same for a sequence, or past the node for a struct.
Every type is real and narrow, and nests no deeper than a bound.
-/
structure LayTypes (w : World) (mem : Memory) (same : Bool) (ts : List Desc) (pos : Nat → Nat) (nest : Nat) :
    Prop where
  /-- Each type's node is in memory at its position. -/
  plan : ∀ i (h : i < ts.length), PlanAt w mem (pos i) (words ts[i])
  /-- The walk from one type to the next. -/
  next : ∀ i (h : i < ts.length), pos (i + 1) = if same then pos i else pos i + 8 * (words ts[i]).length
  /-- Each type is real. -/
  sound : ∀ i (h : i < ts.length), ts[i].wellFormed = .ok ()
  /-- Each type is narrow. -/
  thin : ∀ i (h : i < ts.length), narrow ts[i] = true
  /-- Each type nests no deeper than the bound. -/
  deep : ∀ i (h : i < ts.length), ts[i].nesting ≤ nest

/-- The fixed part of the first parts' slots. -/
def layHead (ts : List Desc) (ps : List ByteArray) (i : Nat) : Nat := headWidth ((laySlots ts ps).take i)

/-- The bodies of the first parts' slots. -/
def layBody (ts : List Desc) (ps : List ByteArray) (i : Nat) : Nat := bodyWidth ((laySlots ts ps).take i)

/-- One more fixed part grows the fixed part by its size, and leaves the bodies. -/
theorem layHead_fixed (ts : List Desc) (ps : List ByteArray) (i : Nat) (ht : i < ts.length) (hp : i < ps.length)
    (fixed : ts[i].isFixed = true) :
    layHead ts ps (i + 1) = layHead ts ps i + ps[i].size ∧ layBody ts ps (i + 1) = layBody ts ps i := by
  simp only [layHead, layBody, laySlots_take_succ ts ps i ht hp, lay_headWidth_append, lay_bodyWidth_append, fixed]
  exact ⟨rfl, rfl⟩

/-- One more variable part grows the fixed part by an offset, and the bodies by its size. -/
theorem layHead_body (ts : List Desc) (ps : List ByteArray) (i : Nat) (ht : i < ts.length) (hp : i < ps.length)
    (varies : ts[i].isFixed = false) :
    layHead ts ps (i + 1) = layHead ts ps i + 4 ∧ layBody ts ps (i + 1) = layBody ts ps i + ps[i].size := by
  simp only [layHead, layBody, laySlots_take_succ ts ps i ht hp, lay_headWidth_append, lay_bodyWidth_append, varies]
  exact ⟨rfl, rfl⟩

/-- A part a fixed-size type fits is as big as the type. -/
theorem lay_partFits_fixed (d : Desc) (part : ByteArray) (width : Nat) (fixed : d.fixedSize = some width) :
    partFits d part = if part.size = width then .ok () else .error (.count width part.size) := by
  by_cases h : part.size = width <;> simp [partFits, fixed, h]

/-- Any part fits a variable-size type. -/
theorem lay_partFits_none (d : Desc) (part : ByteArray) (varies : d.fixedSize = none) : partFits d part = .ok () := by
  simp [partFits, varies]

/-- What the checking loop holds after some parts: still going with the sizes so far, or stopped at a refusal. -/
def layChecked (ts : List Desc) (ps : List ByteArray) (env : Env) (i : Nat) : Prop :=
  (env 6 = 0 ∧ checkParts (ts.take i) (ps.take i) = .ok () ∧ env 11 = (layHead ts ps i).toUInt64 ∧
      env 12 = (layHead ts ps i + layBody ts ps i).toUInt64 ∧
      layWrapped (env 13) (layHead ts ps i + layBody ts ps i)) ∨
    (env 6 = (codePart : Nat).toUInt64 ∧ ∃ e, checkParts (ts.take i) (ps.take i) = .error e ∧ errCode e = codePart)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 2000000 in
/-- One pass of the checking loop: the part's width and size, its check, and the step to the next type. -/
theorem lay_check_pass (m : Module) (w : World) (linked : HasCodec m) (inner : Nat) (mem : Memory) (same : Bool)
    (ts : List Desc) (ps : List ByteArray) (ptrs : List Nat) (pos : Nat → Nat) (nest parts : Nat)
    (types : LayTypes w mem same ts pos nest) (paired : ts.length = ps.length) (at_ : PartsAt w mem parts ps ptrs)
    (room : w.stackLo + (widthLevel + walkLevel) * nest ≤ inner) (env : Env) (i : Nat) (more : i < ps.length)
    (e1 : env 1 = if same then 1 else 0) (e2 : env 2 = parts.toUInt64) (e7 : env 7 = i.toUInt64)
    (e8 : env 8 = (pos i).toUInt64) (e6 : env 6 = 0) (checked : checkParts (ts.take i) (ps.take i) = .ok ())
    (e11 : env 11 = (layHead ts ps i).toUInt64) (e12 : env 12 = (layHead ts ps i + layBody ts ps i).toUInt64)
    (e13 : layWrapped (env 13) (layHead ts ps i + layBody ts ps i)) :
    ∃ env', Runs m w inner env mem (.block layCheckBody) env' mem ∧ (∀ k, k < 6 → env' k = env k) ∧
      env' 7 = (i + 1).toUInt64 ∧ env' 8 = (pos (i + 1)).toUInt64 ∧ layChecked ts ps env' (i + 1) := by
  have ht : i < ts.length := by omega
  let t := ts[i]
  have plan := types.plan i ht
  have deeper : (widthLevel + walkLevel) * t.nesting ≤ (widthLevel + walkLevel) * nest :=
    Nat.mul_le_mul_left _ (types.deep i ht)
  have tableBound : parts + 16 * ps.length ≤ 2 ^ 63 := by
    have := at_.table
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have sizeBound : ps[i].size ≤ 2 ^ 63 := by
    have := at_.readable i more
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have measured := lay_width_call m w linked t (types.sound i ht) (types.thin i ht) inner mem (pos i) env e8 plan
    (by omega)
  let env₁ := assign env 9 (widthWord t)
  obtain ⟨readSize, -⟩ := lay_read at_ env₁ mem i more (by simp [env₁, assign, e2]) (by simp [env₁, assign, e7])
    (fun _ _ _ => rfl)
  let env₂ := assign env₁ 10 ps[i].size.toUInt64
  have sized : Runs m w inner env₁ mem (.set 10 (Expr.ld (Expr.var 2 + 16 * Expr.var 7 + 8))) env₂ mem :=
    Runs.set _ _ _ _ _ 10 _ _ readSize
  -- The rest of the pass, once the check has run to some variables that keep the type's position.
  have rest : ∀ env₃, Runs m w inner env₂ mem layCheckStep env₃ mem → env₃ 1 = env 1 → env₃ 8 = env 8 →
      (∀ k, k < 6 → env₃ k = env k) → env₃ 7 = env 7 → layChecked ts ps env₃ (i + 1) →
      ∃ env', Runs m w inner env mem (.block layCheckBody) env' mem ∧ (∀ k, k < 6 → env' k = env k) ∧
        env' 7 = (i + 1).toUInt64 ∧ env' 8 = (pos (i + 1)).toUInt64 ∧ layChecked ts ps env' (i + 1) := by
    intro env₃ ran f1 f8 keep f7 after
    have advanced := lay_advance m w linked t (types.sound i ht) inner mem (pos i) same env₃ (by rw [f1, e1])
      (by rw [f8, e8]) plan (by omega)
    rw [← types.next i ht] at advanced
    let env₄ := assign env₃ 8 (pos (i + 1)).toUInt64
    refine ⟨assign env₄ 7 (i + 1).toUInt64, ?_, fun k hk => ?_, by simp [assign], by simp [env₄, assign], ?_⟩
    · exact Runs.block_cons measured (Runs.block_cons sized (Runs.block_cons ran (Runs.block_cons advanced
        (Runs.set _ _ _ _ _ 7 _ _ (by simp [eval, env₄, assign, f7, e7, aluResult])))))
    · simp [env₄, assign, show k ≠ 7 by omega, show k ≠ 8 by omega, keep k hk]
    · -- Only the type's position and the index changed, and neither is part of what the check holds.
      simp only [layChecked] at after ⊢
      simpa [env₄, assign] using after
  have lenWord : ps[i].size < 2 ^ 64 := by omega
  have next := lay_checkParts_succ ts ps i ht more
  rw [checked] at next
  cases fixed : t.fixedSize with
  | some width =>
    have small := narrow_width t (types.thin i ht) width fixed
    have isFixed : ts[i].isFixed = true := by simp [Desc.isFixed, show ts[i].fixedSize = some width from fixed]
    have notNone : eval w env₂ mem (Expr.ne (.var 9) (.lit (none64 : Nat).toUInt64)) = some 1 := by
      have := widthWord_none t width fixed small
      evaluate [env₂, env₁]
      exact this
    have word : widthWord t = width.toUInt64 := by simp [widthWord, fixed]
    by_cases fits : ps[i].size = width
    · -- The part has its type's width: the sizes grow by it.
      obtain ⟨headStep, bodyStep⟩ := layHead_fixed ts ps i ht more isFixed
      have same₁ : eval w env₂ mem (Expr.ne (.var 10) (.var 9)) = some 0 := by
        evaluate [env₂, env₁, word, fits]
      let env₃ := assign env₂ 11 (layHead ts ps (i + 1)).toUInt64
      have headSet : Runs m w inner env₂ mem (.set 11 (Expr.var 11 + .var 9)) env₃ mem :=
        Runs.set _ _ _ _ _ 11 _ _ (by
          simp only [show (Expr.var 11 + .var 9) = .op .add (.var 11) (.var 9) from rfl, eval]
          simp [env₂, env₁, assign, e11, word, headStep, ← fits, aluResult, UInt64.ofNat_add])
      obtain ⟨env₄, keep₄, f12, f13, grown⟩ := lay_grow m w inner env₃ mem (.var 10) ps[i].size
        (layHead ts ps i + layBody ts ps i) lenWord (by simp [eval, env₃, env₂, assign])
        (by simp [env₃, env₂, env₁, assign, e12]) (by simpa [env₃, env₂, env₁, assign] using e13)
      have ran := grown [] env₄ mem (Runs.block_nil _ _ _ _ _)
      rw [List.append_nil] at ran
      refine rest env₄ (Runs.ite_true 1 notNone (by decide) (Runs.ite_false same₁
        (Runs.block_cons headSet ran))) ?_ ?_ ?_ ?_ (Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩)
      · rw [keep₄ 1 (by decide) (by decide) (by decide)]; simp [env₃, env₂, env₁, assign]
      · rw [keep₄ 8 (by decide) (by decide) (by decide)]; simp [env₃, env₂, env₁, assign]
      · intro k hk
        rw [keep₄ k (by omega) (by omega) (by omega)]
        simp [env₃, env₂, env₁, assign, show k ≠ 9 by omega, show k ≠ 10 by omega, show k ≠ 11 by omega]
      · rw [keep₄ 7 (by decide) (by decide) (by decide)]; simp [env₃, env₂, env₁, assign]
      · rw [keep₄ 6 (by decide) (by decide) (by decide)]; simp [env₃, env₂, env₁, assign, e6]
      · rw [next, lay_partFits_fixed _ _ width fixed, if_pos fits]; rfl
      · rw [keep₄ 11 (by decide) (by decide) (by decide)]; simp [env₃, assign]
      · rw [f12, headStep, bodyStep]; congr 1; omega
      · rw [headStep, bodyStep, show layHead ts ps i + ps[i].size + layBody ts ps i =
          layHead ts ps i + layBody ts ps i + ps[i].size by omega]
        exact f13
    · -- A part of the wrong size is refused.
      have differ : eval w env₂ mem (Expr.ne (.var 10) (.var 9)) = some 1 := by
        have ne : ps[i].size.toUInt64 ≠ width.toUInt64 := fun h =>
          fits ((ofNat_eq_ofNat _ _ lenWord (by omega)).mp h)
        evaluate [env₂, env₁, word, ne]
      refine rest (assign env₂ 6 (codePart : Nat).toUInt64) (Runs.ite_true 1 notNone (by decide)
        (Runs.ite_true 1 differ (by decide) (Runs.set _ _ _ _ _ 6 _ _ rfl))) ?_ ?_ ?_ ?_
        (Or.inr ⟨by simp [assign], .count width ps[i].size, ?_, rfl⟩)
      · simp [env₂, env₁, assign]
      · simp [env₂, env₁, assign]
      · intro k hk
        simp [env₂, env₁, assign, show k ≠ 6 by omega, show k ≠ 9 by omega, show k ≠ 10 by omega]
      · simp [env₂, env₁, assign]
      · rw [next, lay_partFits_fixed _ _ width fixed, if_neg fits]; rfl
  | none =>
    -- A variable part takes an offset in the fixed part, and its bytes among the bodies.
    have isBody : ts[i].isFixed = false := by simp [Desc.isFixed, show ts[i].fixedSize = none from fixed]
    obtain ⟨headStep, bodyStep⟩ := layHead_body ts ps i ht more isBody
    have word : widthWord t = (none64 : Nat).toUInt64 := by simp [widthWord, fixed]
    have isNone : eval w env₂ mem (Expr.ne (.var 9) (.lit (none64 : Nat).toUInt64)) = some 0 := by
      evaluate [env₂, env₁, word]
    let env₃ := assign env₂ 11 (layHead ts ps (i + 1)).toUInt64
    have headSet : Runs m w inner env₂ mem (.set 11 (Expr.var 11 + 4)) env₃ mem :=
      Runs.set _ _ _ _ _ 11 _ _ (by
        simp only [show (Expr.var 11 + 4) = .op .add (.var 11) 4 from rfl, eval]
        simp [env₂, env₁, assign, e11, headStep, aluResult])
    obtain ⟨env₄, keep₄, f12, f13, grown⟩ := lay_grow m w inner env₃ mem 4 4
      (layHead ts ps i + layBody ts ps i) (by decide) rfl
      (by simp [env₃, env₂, env₁, assign, e12]) (by simpa [env₃, env₂, env₁, assign] using e13)
    obtain ⟨env₅, keep₅, g12, g13, grown'⟩ := lay_grow m w inner env₄ mem (.var 10) ps[i].size
      (layHead ts ps i + layBody ts ps i + 4) lenWord
      (by rw [show eval w env₄ mem (.var 10) = some (env₄ 10) from rfl, keep₄ 10 (by decide) (by decide) (by decide)]
          simp [env₃, env₂, assign]) f12 f13
    have ran := grown _ env₅ mem (by
      have := grown' [] env₅ mem (Runs.block_nil _ _ _ _ _)
      rwa [List.append_nil] at this)
    have keep : ∀ k, k ≠ 12 → k ≠ 13 → k ≠ 14 → env₅ k = env₃ k := fun k a b c => by
      rw [keep₅ k a b c, keep₄ k a b c]
    refine rest env₅ (Runs.ite_false isNone (Runs.block_cons headSet ran)) ?_ ?_ ?_ ?_ (Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩)
    · rw [keep 1 (by decide) (by decide) (by decide)]; simp [env₃, env₂, env₁, assign]
    · rw [keep 8 (by decide) (by decide) (by decide)]; simp [env₃, env₂, env₁, assign]
    · intro k hk
      rw [keep k (by omega) (by omega) (by omega)]
      simp [env₃, env₂, env₁, assign, show k ≠ 9 by omega, show k ≠ 10 by omega, show k ≠ 11 by omega]
    · rw [keep 7 (by decide) (by decide) (by decide)]; simp [env₃, env₂, env₁, assign]
    · rw [keep 6 (by decide) (by decide) (by decide)]; simp [env₃, env₂, env₁, assign, e6]
    · rw [next, lay_partFits_none _ _ fixed]; rfl
    · rw [keep 11 (by decide) (by decide) (by decide)]; simp [env₃, assign]
    · rw [g12, headStep, bodyStep]; congr 1; omega
    · rw [headStep, bodyStep, show layHead ts ps i + 4 + (layBody ts ps i + ps[i].size) =
        layHead ts ps i + layBody ts ps i + 4 + ps[i].size by omega]
      exact g13

/-! ## The writing loop -/

/-- Memory that differs from another only inside the output. -/
def layAway (mem : Memory) (out cap : Nat) (cur : Memory) : Prop := ∀ x, x < out ∨ out + cap ≤ x → cur x = mem x

/-- A store inside the output keeps memory away from the output as it was. -/
theorem lay_away_store {mem cur : Memory} {out cap : Nat} (away : layAway mem out cap cur) (a n : Nat)
    (g : Nat → UInt8) (lo : out ≤ a) (hi : a + n ≤ out + cap) : layAway mem out cap (store cur a n g) := by
  intro x far
  simp only [store]
  rw [if_neg (by omega)]
  exact away x far

/-- A plan away from the output still reads as itself. -/
theorem lay_plan_kept {w : World} {mem cur : Memory} {out cap p : Nat} {ws : List Nat} (plan : PlanAt w mem p ws)
    (away : layAway mem out cap cur) (apart : p + 8 * ws.length ≤ out ∨ out + cap ≤ p) : PlanAt w cur p ws := by
  refine ⟨plan.1, fun k small => ⟨(plan.2 k small).1, ?_⟩⟩
  rw [← (plan.2 k small).2]
  exact readLE_congr _ _ _ _ (fun j hj => away _ (by omega))

/-- The fixed part of the first slots is no wider than the whole fixed part. -/
theorem lay_head_le (l : List (Bool × Bytes)) (i : Nat) : headWidth (l.take i) ≤ headWidth l := by
  have := lay_headWidth_append (l.take i) (l.drop i)
  rw [List.take_append_drop] at this
  omega

/-- The bodies of the first slots are no wider than all the bodies. -/
theorem lay_body_le (l : List (Bool × Bytes)) (i : Nat) : bodyWidth (l.take i) ≤ bodyWidth l := by
  have := lay_bodyWidth_append (l.take i) (l.drop i)
  rw [List.take_append_drop] at this
  omega

/-- The output after the first parts are written: their fixed part from the start, their bodies past the fixed part. -/
def layWritten (mem : Memory) (out : Nat) (ts : List Desc) (ps : List ByteArray) (i : Nat) : Memory :=
  placed (placed mem out ⟨headOf (headWidth (laySlots ts ps)) ((laySlots ts ps).take i)⟩)
    (out + headWidth (laySlots ts ps)) ⟨bodiesOf ((laySlots ts ps).take i)⟩

/-- The written output lies inside the output. -/
theorem lay_away_written (mem : Memory) (out cap : Nat) (ts : List Desc) (ps : List ByteArray) (i : Nat)
    (fits : headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps) ≤ cap) :
    layAway mem out cap (layWritten mem out ts ps i) := by
  intro x far
  have h := lay_head_le (laySlots ts ps) i
  have b := lay_body_le (laySlots ts ps) i
  have hs : (⟨headOf (headWidth (laySlots ts ps)) ((laySlots ts ps).take i)⟩ : ByteArray).size =
      headWidth ((laySlots ts ps).take i) := headOf_size _ _
  have bs : (⟨bodiesOf ((laySlots ts ps).take i)⟩ : ByteArray).size = bodyWidth ((laySlots ts ps).take i) :=
    bodiesOf_size _
  simp only [layWritten]
  rw [lay_placed_outside _ _ _ _ (by rw [bs]; omega), lay_placed_outside _ _ _ _ (by rw [hs]; omega)]

/-- One more fixed part extends the fixed part with its bytes, and leaves the bodies. -/
theorem lay_written_fixed (ts : List Desc) (ps : List ByteArray) (i : Nat) (ht : i < ts.length)
    (hp : i < ps.length) (fixed : ts[i].isFixed = true) (s : Nat) :
    (⟨headOf s ((laySlots ts ps).take (i + 1))⟩ : ByteArray) = ⟨headOf s ((laySlots ts ps).take i)⟩ ++ ps[i] ∧
      (⟨bodiesOf ((laySlots ts ps).take (i + 1))⟩ : ByteArray) = ⟨bodiesOf ((laySlots ts ps).take i)⟩ := by
  rw [laySlots_take_succ ts ps i ht hp, lay_headOf_append, lay_bodiesOf_append, fixed]
  refine ⟨?_, ?_⟩
  · rw [lay_mk_append]; simp [headOf]
  · simp [bodiesOf]

/-- One more variable part extends the fixed part with its offset, and the bodies with its bytes. -/
theorem lay_written_body (ts : List Desc) (ps : List ByteArray) (i : Nat) (ht : i < ts.length)
    (hp : i < ps.length) (varies : ts[i].isFixed = false) (s : Nat) :
    (⟨headOf s ((laySlots ts ps).take (i + 1))⟩ : ByteArray) =
        ⟨headOf s ((laySlots ts ps).take i)⟩ ++ ⟨uintBytes 4 (s + bodyWidth ((laySlots ts ps).take i))⟩ ∧
      (⟨bodiesOf ((laySlots ts ps).take (i + 1))⟩ : ByteArray) = ⟨bodiesOf ((laySlots ts ps).take i)⟩ ++ ps[i] := by
  rw [laySlots_take_succ ts ps i ht hp, lay_headOf_append, lay_bodiesOf_append, varies]
  refine ⟨?_, ?_⟩
  · rw [lay_mk_append]; simp [headOf]
  · rw [lay_mk_append]; simp [bodiesOf]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/-- One pass of the writing loop: the part's width and size, its bytes or its offset and body, then the next type. -/
theorem lay_write_pass (m : Module) (w : World) (linked : HasCodec m) (inner : Nat) (mem : Memory) (same : Bool)
    (ts : List Desc) (ps : List ByteArray) (ptrs : List Nat) (pos : Nat → Nat) (nest parts out cap : Nat)
    (types : LayTypes w mem same ts pos nest) (paired : ts.length = ps.length) (at_ : PartsAt w mem parts ps ptrs)
    (to : OutAt w parts ps ptrs out cap)
    (planApart : ∀ i (h : i < ts.length), pos i + 8 * (words ts[i]).length ≤ out ∨ out + cap ≤ pos i)
    (fits : headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps) ≤ cap)
    (room : w.stackLo + (widthLevel + walkLevel) * nest + (8 + 8 * copyBytes.frame) ≤ inner)
    (env : Env) (i : Nat) (more : i < ps.length)
    (e1 : env 1 = if same then 1 else 0) (e2 : env 2 = parts.toUInt64) (e4 : env 4 = out.toUInt64)
    (e7 : env 7 = i.toUInt64) (e8 : env 8 = (pos i).toUInt64) (e12 : env 12 = (layHead ts ps i).toUInt64)
    (e15 : env 15 = (headWidth (laySlots ts ps) + layBody ts ps i).toUInt64) :
    ∃ env', Runs m w inner env (layWritten mem out ts ps i) (.block layWriteBody) env'
        (layWritten mem out ts ps (i + 1)) ∧ (∀ k, k < 6 → env' k = env k) ∧
      env' 7 = (i + 1).toUInt64 ∧ env' 8 = (pos (i + 1)).toUInt64 ∧ env' 12 = (layHead ts ps (i + 1)).toUInt64 ∧
      env' 15 = (headWidth (laySlots ts ps) + layBody ts ps (i + 1)).toUInt64 := by
  have ht : i < ts.length := by omega
  let t := ts[i]
  let H := headWidth (laySlots ts ps)
  let B := bodyWidth (laySlots ts ps)
  have hH : H = headWidth (laySlots ts ps) := rfl
  have hB : B = bodyWidth (laySlots ts ps) := rfl
  let cur := layWritten mem out ts ps i
  have away : layAway mem out cap cur := lay_away_written mem out cap ts ps i fits
  have plan := lay_plan_kept (types.plan i ht) away (planApart i ht)
  have deeper : (widthLevel + walkLevel) * t.nesting ≤ (widthLevel + walkLevel) * nest :=
    Nat.mul_le_mul_left _ (types.deep i ht)
  have outBound : out + cap ≤ 2 ^ 63 := by
    have := to.writable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have ptrLen : i < ptrs.length := by rw [at_.count]; exact more
  have ptrBound : ptrs[i] + ps[i].size ≤ 2 ^ 63 := by
    have := at_.readable i more
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have apartPart := to.apartParts i ptrLen more
  have bytes : BytesAt mem ptrs[i] ps[i] := at_.bytes i more
  -- The table lies away from the output, so it reads as before in any memory that only changed the output.
  have keptOf : ∀ c, layAway mem out cap c → ∀ x, parts ≤ x → x < parts + 16 * ps.length → c x = mem x :=
    fun c a x lo hi => a x (by have := to.apartTable; omega)
  have headLe : layHead ts ps (i + 1) ≤ H := lay_head_le _ _
  have bodyLe : layBody ts ps i ≤ B := lay_body_le _ _
  have bodyLe' : layBody ts ps (i + 1) ≤ B := lay_body_le _ _
  have headSize : (⟨headOf H ((laySlots ts ps).take i)⟩ : ByteArray).size = layHead ts ps i := headOf_size _ _
  have bodySize : (⟨bodiesOf ((laySlots ts ps).take i)⟩ : ByteArray).size = layBody ts ps i := bodiesOf_size _
  have measured := lay_width_call m w linked t (types.sound i ht) (types.thin i ht) inner cur (pos i) env e8 plan
    (by omega)
  let env₁ := assign env 9 (widthWord t)
  obtain ⟨readSize, -⟩ := lay_read at_ env₁ cur i more (by simp [env₁, assign, e2]) (by simp [env₁, assign, e7])
    (keptOf cur away)
  let env₂ := assign env₁ 10 ps[i].size.toUInt64
  have sized : Runs m w inner env₁ cur (.set 10 (Expr.ld (Expr.var 2 + 16 * Expr.var 7 + 8))) env₂ cur :=
    Runs.set _ _ _ _ _ 10 _ _ readSize
  -- The rest of the pass, once the write has run to some variables that keep the type's position.
  have rest : ∀ env₃, Runs m w inner env₂ cur layWriteStep env₃ (layWritten mem out ts ps (i + 1)) →
      env₃ 1 = env 1 → env₃ 8 = env 8 → (∀ k, k < 6 → env₃ k = env k) → env₃ 7 = env 7 →
      env₃ 12 = (layHead ts ps (i + 1)).toUInt64 → env₃ 15 = (H + layBody ts ps (i + 1)).toUInt64 →
      ∃ env', Runs m w inner env cur (.block layWriteBody) env' (layWritten mem out ts ps (i + 1)) ∧
        (∀ k, k < 6 → env' k = env k) ∧ env' 7 = (i + 1).toUInt64 ∧ env' 8 = (pos (i + 1)).toUInt64 ∧
        env' 12 = (layHead ts ps (i + 1)).toUInt64 ∧ env' 15 = (H + layBody ts ps (i + 1)).toUInt64 := by
    intro env₃ ran f1 f8 keep f7 f12 f15
    have plan' := lay_plan_kept (types.plan i ht) (lay_away_written mem out cap ts ps (i + 1) fits) (planApart i ht)
    have advanced := lay_advance m w linked t (types.sound i ht) inner _ (pos i) same env₃ (by rw [f1, e1])
      (by rw [f8, e8]) plan' (by omega)
    rw [← types.next i ht] at advanced
    let env₄ := assign env₃ 8 (pos (i + 1)).toUInt64
    refine ⟨assign env₄ 7 (i + 1).toUInt64, ?_, fun k hk => ?_, by simp [assign], by simp [env₄, assign], ?_, ?_⟩
    · exact Runs.block_cons measured (Runs.block_cons sized (Runs.block_cons ran (Runs.block_cons advanced
        (Runs.set _ _ _ _ _ 7 _ _ (by simp [eval, env₄, assign, f7, e7, aluResult])))))
    · simp [env₄, assign, show k ≠ 7 by omega, show k ≠ 8 by omega, keep k hk]
    · simp [env₄, assign, f12]
    · simp [env₄, assign, f15]
  have outWord : ∀ x, x ≤ cap → (UInt64.ofNat out + UInt64.ofNat x) = (out + x).toUInt64 := by
    intro x _; simp [UInt64.ofNat_add]
  cases fixed : t.fixedSize with
  | some width =>
    -- A fixed part is copied in place, after the fixed part written so far.
    have small := narrow_width t (types.thin i ht) width fixed
    have isFixed : ts[i].isFixed = true := by simp [Desc.isFixed, show ts[i].fixedSize = some width from fixed]
    obtain ⟨headStep, -⟩ := layHead_fixed ts ps i ht more isFixed
    have written := lay_written_fixed ts ps i ht more isFixed H
    have notNone : eval w env₂ cur (Expr.ne (.var 9) (.lit (none64 : Nat).toUInt64)) = some 1 := by
      have := widthWord_none t width fixed small
      evaluate [env₂, env₁]
      exact this
    obtain ⟨-, readStart⟩ := lay_read at_ env₂ cur i more (by simp [env₂, env₁, assign, e2])
      (by simp [env₂, env₁, assign, e7]) (keptOf cur away)
    have copiedNow := copy_correct m w linked inner cur (out + layHead ts ps i).toUInt64 (ptrs[i]).toUInt64
      ps[i].size.toUInt64 (by omega)
      (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]; exact at_.readable i more)
      (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]
          exact access_sub to.writable (by omega) (by omega))
      (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]; omega)
    have memEq : copied cur (out + layHead ts ps i) ptrs[i] ps[i].size = layWritten mem out ts ps (i + 1) := by
      have step := lay_step_inline mem out (out + H) ptrs[i] _ _ ps[i] bytes (by rw [headSize]; omega)
        (by rw [bodySize]; omega)
      rw [headSize] at step
      simp only [layWritten]
      rw [written.1, written.2]
      exact step
    rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), memEq] at copiedNow
    refine rest _ (Runs.ite_true 1 notNone (by decide) (Runs.block_cons (Runs.call (values :=
      [(out + layHead ts ps i).toUInt64, (ptrs[i]).toUInt64, ps[i].size.toUInt64]) ?_ copiedNow)
        (Runs.set _ _ _ _ _ 12 _ (layHead ts ps (i + 1)).toUInt64 ?_))) ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [List.mapM_cons, List.mapM_nil, readStart]
      simp [eval, env₂, env₁, assign, e4, e12, aluResult, outWord, H]
    · simp only [show (Expr.var 12 + .var 10) = .op .add (.var 12) (.var 10) from rfl, eval]
      simp [assign, env₂, env₁, e12, headStep, aluResult, UInt64.ofNat_add]
    · simp [assign, env₂, env₁]
    · simp [assign, env₂, env₁]
    · intro k hk
      simp [assign, env₂, env₁, show k ≠ 9 by omega, show k ≠ 10 by omega, show k ≠ 12 by omega,
        show k ≠ 16 by omega]
    · simp [assign, env₂, env₁]
    · simp [assign]
    · simp [assign, env₂, env₁, e15, layHead_fixed ts ps i ht more isFixed, H]
  | none =>
    -- A variable part leaves its body's offset in place, and its bytes after the bodies written so far.
    have isBody : ts[i].isFixed = false := by simp [Desc.isFixed, show ts[i].fixedSize = none from fixed]
    obtain ⟨headStep, bodyStep⟩ := layHead_body ts ps i ht more isBody
    have written := lay_written_body ts ps i ht more isBody H
    have isNone : eval w env₂ cur (Expr.ne (.var 9) (.lit (none64 : Nat).toUInt64)) = some 0 := by
      have word : widthWord t = (none64 : Nat).toUInt64 := by simp [widthWord, fixed]
      evaluate [env₂, env₁, word]
    let stored := store cur (out + layHead ts ps i) 4 (qwordByte (H + layBody ts ps i).toUInt64)
    have storeRun : Runs m w inner env₂ cur (.store .b4 (Expr.var 4 + Expr.var 12) (.var 15)) env₂ stored := by
      have := Runs.store m w inner env₂ cur .b4 (Expr.var 4 + Expr.var 12) (.var 15)
        (out + layHead ts ps i).toUInt64 (H + layBody ts ps i).toUInt64
        (by simp [eval, env₂, env₁, assign, e4, e12, aluResult, outWord])
        (by simp [eval, env₂, env₁, assign, e15, H])
        (by rw [toNat_toUInt64 _ (by omega)]; exact access_sub to.writable (by omega) (by simp only [Width.bytes]; omega))
      rwa [toNat_toUInt64 _ (by omega)] at this
    have away' : layAway mem out cap stored := lay_away_store away _ 4 _ (by omega) (by omega)
    obtain ⟨-, readStart⟩ := lay_read at_ env₂ stored i more (by simp [env₂, env₁, assign, e2])
      (by simp [env₂, env₁, assign, e7]) (keptOf stored away')
    have copiedNow := copy_correct m w linked inner stored (out + (H + layBody ts ps i)).toUInt64 (ptrs[i]).toUInt64
      ps[i].size.toUInt64 (by omega)
      (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]; exact at_.readable i more)
      (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]
          exact access_sub to.writable (by omega) (by omega))
      (by rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]; omega)
    have memEq : copied stored (out + (H + layBody ts ps i)) ptrs[i] ps[i].size =
        layWritten mem out ts ps (i + 1) := by
      have step := lay_step_body mem out (out + H) ptrs[i] (H + layBody ts ps i) (by omega) _ _ ps[i] bytes
        (by rw [headSize]; omega) (by rw [bodySize]; omega)
      rw [headSize, bodySize, Nat.add_assoc] at step
      simp only [layWritten]
      rw [written.1, written.2]
      exact step
    rw [toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega), memEq] at copiedNow
    refine rest _ (Runs.ite_false isNone (Runs.block_cons storeRun (Runs.block_cons (Runs.call (values :=
      [(out + (H + layBody ts ps i)).toUInt64, (ptrs[i]).toUInt64, ps[i].size.toUInt64]) ?_ copiedNow)
        (Runs.block_cons (Runs.set _ _ _ _ _ 15 _ (H + layBody ts ps (i + 1)).toUInt64 ?_)
          (Runs.set _ _ _ _ _ 12 _ (layHead ts ps (i + 1)).toUInt64 ?_))))) ?_ ?_ ?_ ?_ ?_ ?_
    · simp only [List.mapM_cons, List.mapM_nil, readStart]
      simp [eval, env₂, env₁, assign, e4, e15, aluResult, outWord, H]
    · simp only [show (Expr.var 15 + .var 10) = .op .add (.var 15) (.var 10) from rfl, eval]
      simp [assign, env₂, env₁, e15, bodyStep, aluResult, UInt64.ofNat_add, ← Nat.add_assoc, H]
    · simp only [show (Expr.var 12 + 4) = .op .add (.var 12) 4 from rfl, eval]
      simp [assign, env₂, env₁, e12, headStep, aluResult, UInt64.ofNat_add]
    · simp [assign, env₂, env₁]
    · simp [assign, env₂, env₁]
    · intro k hk
      simp [assign, env₂, env₁, show k ≠ 9 by omega, show k ≠ 10 by omega, show k ≠ 12 by omega,
        show k ≠ 15 by omega, show k ≠ 16 by omega]
    · simp [assign, env₂, env₁]
    · simp [assign]
    · simp [assign]

/-! ## The whole driver -/

/-- The first slots of all the parts are all the slots. -/
theorem laySlots_take_all (ts : List Desc) (ps : List ByteArray) :
    (laySlots ts ps).take ps.length = laySlots ts ps :=
  List.take_of_length_le (by simp [laySlots, Nat.min_le_right])

/-- The stack the layout driver needs below its own frame: the walk along the plan, and a copy. -/
def layRoom (nest : Nat) : Nat := (widthLevel + walkLevel) * nest + (8 + 8 * copyBytes.frame)

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/--
The layout driver: parts checked against their types and laid out, or refused, as `layOut` does.

The types are walked along the plan from the first node's position, and the plan lies away from the output.
-/
theorem lay_ok (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory) (q parts out cap nest : Nat)
    (same : Bool) (ts : List Desc) (ps : List ByteArray) (ptrs : List Nat) (pos : Nat → Nat)
    (types : LayTypes w mem same ts pos nest) (start : pos 0 = q) (paired : ts.length = ps.length)
    (planApart : ∀ i (h : i < ts.length), pos i + 8 * (words ts[i]).length ≤ out ∨ out + cap ≤ pos i)
    (at_ : PartsAt w mem parts ps ptrs) (to : OutAt w parts ps ptrs out cap)
    (room : w.stackLo + 8 + 8 * layParts.frame + layRoom nest ≤ sp) :
    Calls m w "ssz_lay_out" sp
      [q.toUInt64, if same then 1 else 0, parts.toUInt64, ps.length.toUInt64, out.toUInt64, cap.toUInt64] mem
      (assembleOutcome out cap mem (layOut ts ps)).1 (assembleOutcome out cap mem (layOut ts ps)).2 := by
  have found : m.fns.lookup "ssz_lay_out" = some layParts := linked ("ssz_lay_out", layParts) (by simp [codecFns])
  have tableBound : parts + 16 * ps.length ≤ 2 ^ 63 := by
    have := at_.table
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have outBound : out + cap ≤ 2 ^ 63 := by
    have := to.writable
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  have lr : layRoom nest = (widthLevel + walkLevel) * nest + (8 + 8 * copyBytes.frame) := rfl
  let N := ps.length
  let inner := sp - 8 - 8 * layParts.frame
  let args : List UInt64 := [q.toUInt64, if same then 1 else 0, parts.toUInt64, N.toUInt64, out.toUInt64,
    cap.toUInt64]
  have finish : ∀ env' mem' (r : UInt64), Runs m w inner (entryEnv args) mem layParts.body env' mem' →
      env' 6 = r → Calls m w "ssz_lay_out" sp args mem r mem' := by
    intro env' mem' r main answer
    exact Calls.fn (env' := env') found (by omega) rfl main (by simp [layParts, Lay.r, eval, answer])
  have a1 : (entryEnv args) 1 = if same then 1 else 0 := by simp [entryEnv, args]
  have a2 : (entryEnv args) 2 = parts.toUInt64 := by simp [entryEnv, args]
  have a3 : (entryEnv args) 3 = N.toUInt64 := by simp [entryEnv, args]
  have a4 : (entryEnv args) 4 = out.toUInt64 := by simp [entryEnv, args]
  have a5 : (entryEnv args) 5 = cap.toUInt64 := by simp [entryEnv, args]
  have a0 : (entryEnv args) 0 = q.toUInt64 := by simp [entryEnv, args]
  -- The checking loop: after i parts, still going with the sizes so far, or stopped at a refusal.
  let inv₁ : Env → Memory → Prop := fun env cur => cur = mem ∧ (∀ k, k < 6 → env k = entryEnv args k) ∧
    ∃ i, i ≤ N ∧ env 7 = i.toUInt64 ∧ env 8 = (pos i).toUInt64 ∧ layChecked ts ps env i
  have loop₁ := Runs.loop_inv (m := m) (w := w) (sp := inner) (c := layCheckCond) (body := .block layCheckBody)
    inv₁ (fun env _ => N - (env 7).toNat)
    (fun env cur ⟨_, keep, i, within, e7, _, _⟩ =>
      ⟨_, lay_cond_eval w env cur i N (env 6) (by omega) (by omega) e7 (by rw [keep 3 (by decide), a3]) rfl⟩)
    (by
      rintro env cur v ⟨rfl, keep, i, within, e7, e8, checked⟩ cond nonzero
      rw [lay_cond_eval w env cur i N (env 6) (by omega) (by omega) e7 (by rw [keep 3 (by decide), a3]) rfl] at cond
      have going : i < N ∧ env 6 = 0 := by
        by_cases g : i < N ∧ env 6 = 0
        · exact g
        · simp [g] at cond; exact absurd cond.symm nonzero
      rcases checked with ⟨e6, sofar, e11, e12, e13⟩ | ⟨e6, -⟩
      case inr => exact absurd (e6 ▸ going.2) (by decide)
      obtain ⟨env', ran, keep', f7, f8, after⟩ := lay_check_pass m w linked inner cur same ts ps ptrs pos nest parts
        types paired at_ (by rw [lr] at room; omega) env i going.1 (by rw [keep 1 (by decide), a1])
        (by rw [keep 2 (by decide), a2]) e7 e8 e6 sofar e11 e12 e13
      refine ⟨env', cur, ran, ⟨rfl, fun k hk => by rw [keep' k hk, keep k hk], i + 1, going.1, f7, f8, after⟩, ?_⟩
      rw [f7, e7, toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]
      omega)
  -- Before the checking loop, everything starts at zero and the type at the first node.
  let env₀ := assign (assign (assign (assign (assign (assign (entryEnv args) 6 0) 7 0) 8 q.toUInt64) 11 0) 12 0) 13 0
  have slots0 : (laySlots ts ps).take 0 = [] := rfl
  obtain ⟨env₁, mem₁, ran₁, ⟨hm, keep₁, i, within, e7, -, checked⟩, exit₁⟩ := loop₁ env₀ mem
    ⟨rfl, fun k hk => by simp [env₀, assign, show k ≠ 6 by omega, show k ≠ 7 by omega, show k ≠ 8 by omega,
      show k ≠ 11 by omega, show k ≠ 12 by omega, show k ≠ 13 by omega], 0, Nat.zero_le _, by simp [env₀, assign],
      by simp [env₀, assign, start],
      Or.inl ⟨by simp [env₀, assign], rfl, by simp [env₀, assign, layHead, slots0, headWidth],
        by simp [env₀, assign, layHead, layBody, slots0, headWidth, bodyWidth],
        Or.inl ⟨by simp [env₀, assign], by simp [layHead, layBody, slots0, headWidth, bodyWidth]⟩⟩⟩
  subst mem₁
  -- The body up to the tail, whatever the tail does.
  have head : ∀ env' mem' r, Runs m w inner env₁ mem layTail env' mem' → env' 6 = r →
      Calls m w "ssz_lay_out" sp args mem r mem' := by
    intro env' mem' r tail answer
    refine finish env' mem' r ?_ answer
    rw [layParts_body]
    exact Runs.block_cons (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.block_cons (Runs.set _ _ _ _ _ 7 _ _ rfl)
      (Runs.block_cons (Runs.set _ _ _ _ _ 8 _ _ (by simp [eval, assign, a0])) (Runs.block_cons
        (Runs.set _ _ _ _ _ 11 _ _ rfl) (Runs.block_cons (Runs.set _ _ _ _ _ 12 _ _ rfl) (Runs.block_cons
          (Runs.set _ _ _ _ _ 13 _ _ rfl) (Runs.block_cons ran₁ tail))))))
  have g6 := lay_cond_eval w env₁ mem i N (env₁ 6) (by omega) (by omega) e7 (by rw [keep₁ 3 (by decide), a3]) rfl
  rw [g6] at exit₁
  rcases checked with ⟨e6, sofar, e11, e12, e13⟩ | ⟨e6, e, refusedAt, code⟩
  case inr =>
    -- A part refused: nothing is written, and the code stays.
    have whole := lay_checkParts_refused ts ps i (by omega) paired e refusedAt
    have refused : layOut ts ps = .error e := by simp [layOut, whole, Bind.bind, Except.bind]
    rw [refused]
    refine head env₁ mem _ (Runs.ite_false ?_ (Runs.skip _ _ _ _ _)) (by simp [assembleOutcome, code, e6])
    simp [Expr.eq, eval, e6, Cond.holds]
    decide
  have done : i = N := by
    by_cases g : i < N
    · simp [g, e6] at exit₁
    · omega
  subst done
  have takeTs : ts.take ps.length = ts := List.take_of_length_le (by omega)
  have takePs : ps.take ps.length = ps := List.take_of_length_le (by omega)
  rw [takeTs, takePs] at sofar
  rw [layOut_checked ts ps sofar]
  have hN : layHead ts ps ps.length = headWidth (laySlots ts ps) := by simp only [layHead, laySlots_take_all]
  have bN : layBody ts ps ps.length = bodyWidth (laySlots ts ps) := by simp only [layBody, laySlots_take_all]
  rw [hN, bN] at e12 e13
  rw [hN] at e11
  have limitSmall : (offsetLimit : Nat) < 2 ^ 64 := by decide
  let env₂ := assign env₁ 6 (codeOverflow : Nat).toUInt64
  have small : eval w env₂ mem (.op .and (Expr.eq (.var 13) 0) (Expr.lt (.var 12) (.lit (offsetLimit : Nat).toUInt64)))
      = some (if headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps) < 2 ^ 32 then 1 else 0) := by
    rcases e13 with ⟨w0, fitsWord⟩ | ⟨w1, wraps⟩
    · have ltIff : (headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps)).toUInt64 < (offsetLimit : Nat).toUInt64 ↔
          headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps) < 2 ^ 32 := ofNat_lt_ofNat _ _ fitsWord limitSmall
      rw [eval_alu (eval_cmp_eq (x := 0) (y := 0) (by simp [eval, env₂, assign, w0]) rfl)
        (eval_cmp_lt (x := (headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps)).toUInt64)
          (by simp [eval, env₂, assign, e12]) rfl)]
      simp only [ltIff]
      by_cases lt : headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps) < 2 ^ 32 <;> simp [lt, aluResult]
    · rw [eval_alu (eval_cmp_eq (x := 1) (y := 0) (by simp [eval, env₂, assign, w1]) rfl)
        (eval_cmp_lt (x := env₁ 12) (by simp [eval, env₂, assign]) rfl)]
      simp [aluResult, show ¬ headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps) < 2 ^ 32 by omega]
  have taken : eval w env₁ mem (Expr.eq (.var 6) 0) = some 1 := by simp [Expr.eq, eval, e6, Cond.holds]
  by_cases big : headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps) ≥ 2 ^ 32
  · -- Past what a four-byte offset names.
    rw [if_pos big]
    refine head _ mem _ (Runs.ite_true 1 taken (by decide)
      (Runs.block_cons (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_false ?_ (Runs.skip _ _ _ _ _))))
      (by simp [assign, assembleOutcome, errCode])
    rw [small, if_neg (by omega)]
  rw [if_neg big]
  have fitsWord : headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps) < 2 ^ 64 := by omega
  have sizeOut :
      (⟨headOf (headWidth (laySlots ts ps)) (laySlots ts ps) ++ bodiesOf (laySlots ts ps)⟩ : ByteArray).size =
      headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps) := by
    simp [ByteArray.size, headOf_size, bodiesOf_size]
  let env₃ := assign env₂ 6 (codeCapacity : Nat).toUInt64
  have capSmall : cap < 2 ^ 64 := by omega
  have capCheck : eval w env₃ mem (Expr.le (.var 12) (.var 5)) =
      some (if headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps) ≤ cap then 1 else 0) := by
    rw [eval_cmp_le (x := (headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps)).toUInt64) (y := cap.toUInt64)
      (by simp [eval, env₃, env₂, assign, e12]) (by simp [eval, env₃, env₂, assign, keep₁ 5 (by decide), a5])]
    have leIff : (headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps)).toUInt64 ≤ cap.toUInt64 ↔
        headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps) ≤ cap :=
      ofNat_le_iff _ _ fitsWord capSmall
    simp only [leIff]
  have within : eval w env₂ mem (.op .and (Expr.eq (.var 13) 0) (Expr.lt (.var 12) (.lit (offsetLimit : Nat).toUInt64)))
      = some 1 := by rw [small, if_pos (by omega)]
  by_cases room' : headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps) ≤ cap
  case neg =>
    -- Too big for the output.
    simp only [assembleOutcome, sizeOut, if_neg room']
    refine head _ mem _ (Runs.ite_true 1 taken (by decide)
      (Runs.block_cons (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_true 1 within (by decide)
        (Runs.block_cons (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_false ?_ (Runs.skip _ _ _ _ _))))))
      (by simp [assign])
    rw [capCheck, if_neg room']
  simp only [assembleOutcome, sizeOut, if_pos room']
  -- The writing loop: after i parts, their fixed part and their bodies are written.
  let inv₂ : Env → Memory → Prop := fun env cur => (∀ k, k < 6 → env k = entryEnv args k) ∧
    ∃ i, i ≤ N ∧ env 7 = i.toUInt64 ∧ env 8 = (pos i).toUInt64 ∧ env 12 = (layHead ts ps i).toUInt64 ∧
      env 15 = (headWidth (laySlots ts ps) + layBody ts ps i).toUInt64 ∧ cur = layWritten mem out ts ps i
  have loop₂ := Runs.loop_inv (m := m) (w := w) (sp := inner) (c := Expr.lt (.var 7) (.var 3))
    (body := .block layWriteBody) inv₂ (fun env _ => N - (env 7).toNat) (fun env cur _ => ⟨_, rfl⟩)
    (by
      rintro env cur v ⟨keep, i, within, e7, e8, f12, f15, rfl⟩ cond nonzero
      have more : i < N := by
        by_cases g : i < N
        · exact g
        · simp [Expr.lt, eval, e7, keep 3 (by decide), a3, Cond.holds, ofNat_lt_ofNat i N (by omega) (by omega),
            g] at cond
          exact absurd cond.symm nonzero
      obtain ⟨env', ran, keep', f7', f8', f12', f15'⟩ := lay_write_pass m w linked inner mem same ts ps ptrs pos nest
        parts out cap types paired at_ to planApart room' (by rw [lr] at room; omega) env i more
        (by rw [keep 1 (by decide), a1]) (by rw [keep 2 (by decide), a2]) (by rw [keep 4 (by decide), a4]) e7 e8 f12
        f15
      refine ⟨env', _, ran, ⟨fun k hk => by rw [keep' k hk, keep k hk], i + 1, more, f7', f8', f12', f15', rfl⟩, ?_⟩
      rw [f7', e7, toNat_toUInt64 _ (by omega), toNat_toUInt64 _ (by omega)]
      omega)
  have start₂ : layWritten mem out ts ps 0 = mem := by
    simp only [layWritten, slots0, headOf, bodiesOf]
    rw [show (⟨#[]⟩ : ByteArray) = .empty from rfl, placed_empty, placed_empty]
  let env₄ := assign (assign (assign (assign env₃ 7 0) 8 q.toUInt64) 12 0) 15
    (headWidth (laySlots ts ps)).toUInt64
  obtain ⟨env₅, mem₅, ran₂, ⟨keep₅, j, within₂, g7, -, -, g15, rfl⟩, exit₂⟩ := loop₂ env₄ mem
    ⟨fun k hk => by simp [env₄, env₃, env₂, assign, show k ≠ 6 by omega, show k ≠ 7 by omega,
      show k ≠ 8 by omega, show k ≠ 12 by omega, show k ≠ 15 by omega, keep₁ k hk], 0, Nat.zero_le _,
      by simp [env₄, assign],
      by simp [env₄, assign, start], by simp [env₄, assign, layHead, slots0, headWidth],
      by simp [env₄, assign, layBody, slots0, bodyWidth], start₂.symm⟩
  have reached : j = N := by
    have small : j < 2 ^ 64 := by omega
    simp only [Expr.lt, eval, g7, keep₅ 3 (by decide), a3, Cond.holds] at exit₂
    simp [ofNat_lt_ofNat j N small (by omega)] at exit₂
    omega
  subst reached
  have joined := lay_placed_join mem out ⟨headOf (headWidth (laySlots ts ps)) (laySlots ts ps)⟩
    ⟨bodiesOf (laySlots ts ps)⟩
  rw [show (⟨headOf (headWidth (laySlots ts ps)) (laySlots ts ps)⟩ : ByteArray).size = headWidth (laySlots ts ps) from
    headOf_size _ _] at joined
  have final : layWritten mem out ts ps ps.length =
      placed mem out ⟨headOf (headWidth (laySlots ts ps)) (laySlots ts ps) ++ bodiesOf (laySlots ts ps)⟩ := by
    simp only [layWritten, laySlots_take_all]
    rw [lay_mk_append, ← joined]
  rw [← final]
  refine head _ _ _ (Runs.ite_true 1 taken (by decide)
    (Runs.block_cons (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_true 1 within (by decide)
      (Runs.block_cons (Runs.set _ _ _ _ _ 6 _ _ rfl) (Runs.ite_true 1 (by rw [capCheck, if_pos room']) (by decide)
        (Runs.block_cons (Runs.set _ _ _ _ _ 7 _ _ rfl) (Runs.block_cons (Runs.set _ _ _ _ _ 8 _ _ ?_)
          (Runs.block_cons (Runs.set _ _ _ _ _ 12 _ _ rfl) (Runs.block_cons (Runs.set _ _ _ _ _ 15 _ _ ?_)
            (Runs.block_cons ran₂ (Runs.set _ _ _ _ _ 6 _ _ rfl))))))))))) ?_
  · simp [eval, env₃, env₂, assign, keep₁ 0 (by decide), a0]
  · simp [eval, env₃, env₂, assign, e11]
  · simp [assign, g15, N, bN]

/-! ## Sequences and structs -/

/-- A sequence's parts: one element type for every part, its node read again and again. -/
theorem lay_seq (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory) (e : Desc)
    (q parts out cap : Nat) (ps : List ByteArray) (ptrs : List Nat) (sound : e.wellFormed = .ok ())
    (thin : narrow e = true) (plan : PlanAt w mem q (words e))
    (planApart : q + 8 * (words e).length ≤ out ∨ out + cap ≤ q)
    (at_ : PartsAt w mem parts ps ptrs) (to : OutAt w parts ps ptrs out cap)
    (room : w.stackLo + 8 + 8 * layParts.frame + layRoom e.nesting ≤ sp) :
    Calls m w "ssz_lay_out" sp [q.toUInt64, 1, parts.toUInt64, ps.length.toUInt64, out.toUInt64, cap.toUInt64] mem
      (assembleOutcome out cap mem (layOut (List.replicate ps.length e) ps)).1
      (assembleOutcome out cap mem (layOut (List.replicate ps.length e) ps)).2 :=
  lay_ok m w linked sp mem q parts out cap e.nesting true (List.replicate ps.length e) ps ptrs (fun _ => q)
    ⟨fun i _ => by simpa using plan, fun _ _ => by simp, fun i _ => by simpa using sound,
      fun i _ => by simpa using thin, fun i _ => by simp⟩
    rfl (by simp) (fun i _ => by simpa using planApart) at_ to room

/-- The position of a struct's field node: past the nodes of the fields before it. -/
def fieldPos (q : Nat) (fields : List Desc) (i : Nat) : Nat := q + 8 * (wordsAll (fields.take i)).length

/-- A struct's parts: one per field, the fields' nodes read in order. -/
theorem lay_fields (m : Module) (w : World) (linked : HasCodec m) (sp : Nat) (mem : Memory) (fields : List Desc)
    (q parts out cap : Nat) (ps : List ByteArray) (ptrs : List Nat) (sound : ∀ f ∈ fields, f.wellFormed = .ok ())
    (thin : ∀ f ∈ fields, narrow f = true) (plan : PlanAt w mem q (wordsAll fields))
    (planApart : q + 8 * (wordsAll fields).length ≤ out ∨ out + cap ≤ q) (paired : fields.length = ps.length)
    (at_ : PartsAt w mem parts ps ptrs) (to : OutAt w parts ps ptrs out cap)
    (room : w.stackLo + 8 + 8 * layParts.frame + layRoom (Desc.deepestNesting fields) ≤ sp) :
    Calls m w "ssz_lay_out" sp [q.toUInt64, 0, parts.toUInt64, ps.length.toUInt64, out.toUInt64, cap.toUInt64] mem
      (assembleOutcome out cap mem (layOut fields ps)).1 (assembleOutcome out cap mem (layOut fields ps)).2 := by
  -- The fields before a field, that field, and the fields after it.
  have split : ∀ i (h : i < fields.length), fields = fields.take i ++ fields[i] :: fields.drop (i + 1) := by simp
  have step : ∀ i (h : i < fields.length),
      fieldPos q fields (i + 1) = fieldPos q fields i + 8 * (words fields[i]).length := by
    intro i h
    simp only [fieldPos, List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, wordsAll_append,
      wordsAll, List.append_nil, List.length_append]
    omega
  have within : ∀ i (h : i < fields.length),
      fieldPos q fields i + 8 * (words fields[i]).length ≤ q + 8 * (wordsAll fields).length := by
    intro i h
    rw [← step i h]
    have whole := congrArg (fun l => (wordsAll l).length) (List.take_append_drop (i + 1) fields)
    simp only [wordsAll_append, List.length_append] at whole
    simp only [fieldPos]
    omega
  refine lay_ok m w linked sp mem q parts out cap (Desc.deepestNesting fields) false fields ps ptrs (fieldPos q fields)
    ⟨fun i h => ?_, fun i h => by simp [step i h], fun i h => sound _ (List.getElem_mem h),
      fun i h => thin _ (List.getElem_mem h), fun i h => nesting_le_deepest fields _ (List.getElem_mem h)⟩
    (by simp [fieldPos, wordsAll]) paired
    (fun i h => by have := within i h; simp only [fieldPos] at this ⊢; omega) at_ to room
  have all := plan
  rw [split i h, wordsAll_append, wordsAll] at all
  exact all.right.left

end Ssz.Native.Driver
