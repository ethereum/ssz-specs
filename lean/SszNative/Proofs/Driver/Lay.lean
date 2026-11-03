import SszNative.Proofs.Driver.Assemble

/-!
The layout driver writes what `layOut` computes.

Parts sit in memory as a table of pairs, each paired with a type: one element type for a sequence, or the fields of a
struct, walked along the plan.
The driver checks every part against its type and sums the encoding's size, then writes fixed parts in place and
variable parts as an offset, with their bytes after the fixed part.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Plan

/-- The step to the next part's type: the same type, or the next field's. -/
def layAdvance : Stmt := .ite (Expr.eq (.var 1) 0) (.call "ssz_plan_next" [.var 8] 8) .skip

/-- The size grown by a step, noting when it passes what a word holds. -/
def layGrow (step : Expr) : List Stmt :=
  [.set 14 (Expr.var 12 + step), .ite (Expr.lt (.var 14) (.var 12)) (.set 13 1) .skip, .set 12 (.var 14)]

/-- The checking step: a fixed part must have its width, and the sizes grow by what the part takes. -/
def layCheckStep : Stmt :=
  .ite (Expr.ne (.var 9) (.lit (none64 : Nat).toUInt64))
    (.ite (Expr.ne (.var 10) (.var 9)) (.set 6 (.lit (codePart : Nat).toUInt64))
      (.block (.set 11 (Expr.var 11 + .var 9) :: layGrow (.var 10))))
    (.block (.set 11 (Expr.var 11 + 4) :: (layGrow 4 ++ layGrow (.var 10))))

/-- The checking loop's body: the part's width and size, the check, then the next type. -/
def layCheckBody : List Stmt :=
  [.call "ssz_plan_width" [.var 8] 9, .set 10 (Expr.ld (Expr.var 2 + 16 * Expr.var 7 + 8)), layCheckStep,
    layAdvance, .set 7 (Expr.var 7 + 1)]

/-- The checking loop runs while parts are left and none was refused. -/
def layCheckCond : Expr := .op .and (Expr.lt (.var 7) (.var 3)) (Expr.eq (.var 6) 0)

/-- The writing step: a fixed part copied in place, or a variable part's offset in place and its bytes after. -/
def layWriteStep : Stmt :=
  .ite (Expr.ne (.var 9) (.lit (none64 : Nat).toUInt64))
    (.block [.call "ssz_copy" [Expr.var 4 + Expr.var 12, Expr.ld (Expr.var 2 + 16 * Expr.var 7), .var 10] 16,
      .set 12 (Expr.var 12 + .var 10)])
    (.block [.store .b4 (Expr.var 4 + Expr.var 12) (.var 15),
      .call "ssz_copy" [Expr.var 4 + Expr.var 15, Expr.ld (Expr.var 2 + 16 * Expr.var 7), .var 10] 16,
      .set 15 (Expr.var 15 + .var 10), .set 12 (Expr.var 12 + 4)])

/-- The writing loop's body: the part's width and size, the write, then the next type. -/
def layWriteBody : List Stmt :=
  [.call "ssz_plan_width" [.var 8] 9, .set 10 (Expr.ld (Expr.var 2 + 16 * Expr.var 7 + 8)), layWriteStep,
    layAdvance, .set 7 (Expr.var 7 + 1)]

/-- What follows the checking loop: the size checks, then the writing loop. -/
def layTail : Stmt :=
  .ite (Expr.eq (.var 6) 0)
    (.block [.set 6 (.lit (codeOverflow : Nat).toUInt64),
      .ite (.op .and (Expr.eq (.var 13) 0) (Expr.lt (.var 12) (.lit (offsetLimit : Nat).toUInt64)))
        (.block [.set 6 (.lit (codeCapacity : Nat).toUInt64),
          .ite (Expr.le (.var 12) (.var 5))
            (.block [.set 7 0, .set 8 (.var 0), .set 12 0, .set 15 (.var 11),
              .loop (Expr.lt (.var 7) (.var 3)) (.block layWriteBody), .set 6 (.var 15)]) .skip]) .skip]) .skip

/-- The layout driver: everything starts at zero, the parts are checked and summed, then written. -/
theorem layParts_body : layParts.body =
    .block [.set 6 0, .set 7 0, .set 8 (.var 0), .set 11 0, .set 12 0, .set 13 0,
      .loop layCheckCond (.block layCheckBody), layTail] := rfl

/-! ## The reference, part by part -/

/-- The slots the reference lays out: whether each part sits in place, and its bytes. -/
def laySlots (ts : List Desc) (ps : List ByteArray) : List (Bool × Bytes) :=
  (ts.map Desc.isFixed).zip (ps.map ByteArray.data)

/-- The fixed part of slots one after the other is the first's, then the second's. -/
theorem lay_headWidth_append : ∀ (a b : List (Bool × Bytes)), headWidth (a ++ b) = headWidth a + headWidth b
  | [], b => by simp [headWidth]
  | (x, p) :: a, b => by simp [headWidth, lay_headWidth_append a b]; omega

/-- The bodies of slots one after the other are the first's, then the second's. -/
theorem lay_bodyWidth_append : ∀ (a b : List (Bool × Bytes)), bodyWidth (a ++ b) = bodyWidth a + bodyWidth b
  | [], b => by simp [bodyWidth]
  | (x, p) :: a, b => by cases x <;> simp [bodyWidth, lay_bodyWidth_append a b]; omega

/-- The fixed part of slots one after the other: the second's offsets start past the first's bodies. -/
theorem lay_headOf_append : ∀ (s : Nat) (a b : List (Bool × Bytes)),
    headOf s (a ++ b) = headOf s a ++ headOf (s + bodyWidth a) b
  | s, [], b => by simp [headOf, bodyWidth]
  | s, (true, p) :: a, b => by simp [headOf, bodyWidth, lay_headOf_append s a b, Array.append_assoc]
  | s, (false, p) :: a, b => by
    simp [headOf, bodyWidth, lay_headOf_append (s + p.size) a b, Array.append_assoc, Nat.add_assoc]

/-- The bodies of slots one after the other. -/
theorem lay_bodiesOf_append : ∀ (a b : List (Bool × Bytes)), bodiesOf (a ++ b) = bodiesOf a ++ bodiesOf b
  | [], b => by simp [bodiesOf]
  | (true, p) :: a, b => by simp [bodiesOf, lay_bodiesOf_append a b]
  | (false, p) :: a, b => by simp [bodiesOf, lay_bodiesOf_append a b, Array.append_assoc]

/-- The first slots and one more. -/
theorem laySlots_take_succ (ts : List Desc) (ps : List ByteArray) (i : Nat) (ht : i < ts.length)
    (hp : i < ps.length) :
    (laySlots ts ps).take (i + 1) = (laySlots ts ps).take i ++ [(ts[i].isFixed, ps[i].data)] := by
  rw [List.take_add_one]
  congr
  rw [List.getElem?_eq_getElem (by simp [laySlots]; omega)]
  simp [laySlots]

/-- Checking parts one after the other checks the first, then the rest. -/
theorem lay_checkParts_append : ∀ (a c : List Desc) (b d : List ByteArray), a.length = b.length →
    checkParts (a ++ c) (b ++ d) = (checkParts a b >>= fun _ => checkParts c d)
  | [], c, [], d, _ => by simp [checkParts, Bind.bind, Except.bind]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | t :: a, c, p :: b, d, h => by
    simp only [List.cons_append, checkParts]
    rw [lay_checkParts_append a c b d (by simpa using h)]
    cases partFits t p <;> cases checkParts a b <;> rfl

/-- Checking the first parts and one more checks the first, then that one. -/
theorem lay_checkParts_succ (ts : List Desc) (ps : List ByteArray) (i : Nat) (ht : i < ts.length)
    (hp : i < ps.length) :
    checkParts (ts.take (i + 1)) (ps.take (i + 1)) =
      (checkParts (ts.take i) (ps.take i) >>= fun _ => partFits ts[i] ps[i]) := by
  rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem ht, List.getElem?_eq_getElem hp,
    Option.toList_some, Option.toList_some, lay_checkParts_append _ _ _ _ (by simp; omega)]
  simp only [checkParts]
  cases partFits ts[i] ps[i] <;> rfl

/-- A refusal of the first parts is the refusal of all the parts. -/
theorem lay_checkParts_refused (ts : List Desc) (ps : List ByteArray) (i : Nat) (hi : i ≤ ts.length)
    (same : ts.length = ps.length) (e : Err) (refused : checkParts (ts.take i) (ps.take i) = .error e) :
    checkParts ts ps = .error e := by
  have whole := lay_checkParts_append (ts.take i) (ts.drop i) (ps.take i) (ps.drop i) (by simp; omega)
  rw [List.take_append_drop, List.take_append_drop, refused] at whole
  rw [whole]; rfl

/-- The reference, once the parts pass their checks: the size check, then the fixed part and the bodies. -/
theorem layOut_checked (ts : List Desc) (ps : List ByteArray) (passed : checkParts ts ps = .ok ()) :
    layOut ts ps =
      if headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps) ≥ 2 ^ 32 then
        .error (.offsetOverflow (headWidth (laySlots ts ps) + bodyWidth (laySlots ts ps)))
      else .ok ⟨headOf (headWidth (laySlots ts ps)) (laySlots ts ps) ++ bodiesOf (laySlots ts ps)⟩ := by
  simp only [layOut, passed, Ssz.assemble, laySlots]
  split <;> simp_all [Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] <;> omega

/-! ## Memory as the parts are written -/

/-- Placed bytes leave memory outside them alone. -/
theorem lay_placed_outside (mem : Memory) (a : Nat) (A : ByteArray) (x : Nat) (far : x < a ∨ a + A.size ≤ x) :
    placed mem a A x = mem x := by
  simp only [placed, store]
  rw [ite_eq_right (by omega)]

/-- Bytes placed apart from each other may be placed in either order. -/
theorem lay_placed_swap (mem : Memory) (a b : Nat) (A B : ByteArray) (apart : a + A.size ≤ b ∨ b + B.size ≤ a) :
    placed (placed mem a A) b B = placed (placed mem b B) a A := by
  funext x
  simp only [placed, store]
  by_cases ha : a ≤ x ∧ x < a + A.size
  · simp only [ite_eq_right (show ¬ (b ≤ x ∧ x < b + B.size) by omega), ite_eq_left ha]
  · simp only [ite_eq_right ha]

/-- Bytes placed right after placed bytes extend them. -/
theorem lay_placed_join (mem : Memory) (a : Nat) (A B : ByteArray) :
    placed (placed mem a A) (a + A.size) B = placed mem a (A ++ B) := by
  funext x
  simp only [placed, store, ByteArray.size_append]
  by_cases hb : a + A.size ≤ x ∧ x < a + A.size + B.size
  · rw [ite_eq_left hb, ite_eq_left (by omega), show x - a = A.size + (x - (a + A.size)) by omega, Kernel.get!_append_right]
  · rw [ite_eq_right hb]
    by_cases ha : a ≤ x ∧ x < a + A.size
    · rw [ite_eq_left ha, ite_eq_left (by omega), Kernel.get!_append_left _ _ _ (by omega)]
    · rw [ite_eq_right ha, ite_eq_right (by omega)]

/-- A store of bytes is placing them. -/
theorem lay_store_placed (mem : Memory) (a n : Nat) (g : Nat → UInt8) (B : ByteArray) (size : B.size = n)
    (each : ∀ k, k < n → B.get! k = g k) : store mem a n g = placed mem a B := by
  funext x
  simp only [placed, store, size]
  by_cases inside : a ≤ x ∧ x < a + n
  · rw [ite_eq_left inside, ite_eq_left inside, each _ (by omega)]
  · rw [ite_eq_right inside, ite_eq_right inside]

/-- Bytes in memory stay there when bytes are placed apart from them. -/
theorem lay_bytes_placed {mem : Memory} {p : Nat} {b : ByteArray} (bytes : BytesAt mem p b) (a : Nat) (A : ByteArray)
    (apart : p + b.size ≤ a ∨ a + A.size ≤ p) : BytesAt (placed mem a A) p b := by
  intro k hk
  rw [lay_placed_outside _ _ _ _ (by omega)]
  exact bytes k hk

/-- A little-endian integer takes its width in bytes. -/
theorem lay_uintBytes_size : ∀ (width value : Nat), (uintBytes width value).size = width
  | 0, _ => rfl
  | width + 1, value => by simp [uintBytes, lay_uintBytes_size width (value / 256)]; omega

/-- Byte k of a little-endian integer is its k-th base-256 digit. -/
theorem lay_uintBytes_toNat : ∀ (width value k : Nat) (h : k < width),
    ((uintBytes width value)[k]'(by rw [lay_uintBytes_size]; exact h)).toNat = value / 256 ^ k % 256
  | 0, _, _, h => absurd h (by omega)
  | width + 1, value, 0, _ => by simp [uintBytes]
  | width + 1, value, k + 1, h => by
    simp only [uintBytes]
    rw [Array.getElem_append_right (by simp)]
    simp only [Array.size_singleton, Nat.add_sub_cancel]
    rw [lay_uintBytes_toNat width (value / 256) k (by omega), Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

/-- A four-byte store of a number is placing its four-byte offset. -/
theorem lay_store_offset (mem : Memory) (a v : Nat) (small : v < 2 ^ 64) :
    store mem a 4 (qwordByte v.toUInt64) = placed mem a ⟨uintBytes 4 v⟩ := by
  refine lay_store_placed mem a 4 _ _ (by simp [ByteArray.size, lay_uintBytes_size]) (fun k hk => ?_)
  apply UInt8.toNat_inj.mp
  rw [Kernel.get!_eq _ _ (by simp [ByteArray.size, lay_uintBytes_size]; omega), qwordByte_toNat _ k (by omega),
    toNat_toUInt64 v small]
  simp only [ByteArray.getElem_eq_getElem_data]
  exact lay_uintBytes_toNat 4 v k hk

/-- Array bytes joined are the byte arrays joined. -/
theorem lay_mk_append (a b : Array UInt8) : (⟨a ++ b⟩ : ByteArray) = ⟨a⟩ ++ ⟨b⟩ := by
  apply ByteArray.ext
  simp [ByteArray.data_append]

/-- A fixed part copied right after the fixed part written so far, with the bodies further on. -/
theorem lay_step_inline (mem : Memory) (out X p : Nat) (H B part : ByteArray) (bytes : BytesAt mem p part)
    (fit : out + H.size + part.size ≤ X) (apart : p + part.size ≤ out ∨ X + B.size ≤ p) :
    copied (placed (placed mem out H) X B) (out + H.size) p part.size = placed (placed mem out (H ++ part)) X B := by
  rw [lay_placed_swap mem out X H B (Or.inl (by omega)),
    copied_placed (placed mem X B) out H part p (lay_bytes_placed bytes X B (by omega)) (by omega),
    lay_placed_swap mem X out B (H ++ part) (Or.inr (by rw [ByteArray.size_append]; omega))]

/-- A variable part's offset stored after the fixed part written so far, and its bytes copied after the bodies. -/
theorem lay_step_body (mem : Memory) (out X p v : Nat) (small : v < 2 ^ 64) (H B part : ByteArray)
    (bytes : BytesAt mem p part) (fit : out + H.size + 4 ≤ X) (apart : p + part.size ≤ out ∨ X + B.size + part.size ≤ p) :
    copied (store (placed (placed mem out H) X B) (out + H.size) 4 (qwordByte v.toUInt64)) (X + B.size) p part.size =
      placed (placed mem out (H ++ ⟨uintBytes 4 v⟩)) X (B ++ part) := by
  have sizeU : (⟨uintBytes 4 v⟩ : ByteArray).size = 4 := by simp [ByteArray.size, lay_uintBytes_size]
  rw [lay_placed_swap mem out X H B (Or.inl (by omega)), lay_store_offset _ _ _ small, lay_placed_join,
    lay_placed_swap mem X out B (H ++ ⟨uintBytes 4 v⟩) (Or.inr (by rw [ByteArray.size_append, sizeU]; omega))]
  exact copied_placed _ X B part p
    (lay_bytes_placed bytes out _ (by rw [ByteArray.size_append, sizeU]; omega)) (by omega)

/-- A part's pair of words, read from the table the driver's third argument names. -/
theorem lay_read {w : World} {mem : Memory} {parts : Nat} {ps : List ByteArray} {ptrs : List Nat}
    (at_ : PartsAt w mem parts ps ptrs) (env : Env) (cur : Memory) (i : Nat) (hi : i < ps.length)
    (e2 : env 2 = parts.toUInt64) (e7 : env 7 = i.toUInt64)
    (kept : ∀ x, parts ≤ x → x < parts + 16 * ps.length → cur x = mem x) :
    eval w env cur (Expr.ld (Expr.var 2 + 16 * Expr.var 7 + 8)) = some ps[i].size.toUInt64 ∧
      eval w env cur (Expr.ld (Expr.var 2 + 16 * Expr.var 7)) =
        some (ptrs[i]'(by rw [at_.count]; exact hi)).toUInt64 := by
  have bound : parts + 16 * ps.length ≤ 2 ^ 63 := by
    have := at_.table
    simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; simp [addressBound] at this; omega
  obtain ⟨a0, a8⟩ := table_addr parts i (by omega)
  have same : ∀ c, c + 8 ≤ 16 → readLE cur (parts + 16 * i + c) 8 = readLE mem (parts + 16 * i + c) 8 :=
    fun c hc => readLE_congr _ _ _ _ (fun k hk => kept _ (by omega) (by omega))
  have acc : ∀ c, c + 8 ≤ 16 → w.access (parts + 16 * i + c) 8 :=
    fun c hc => access_sub at_.table (by omega) (by omega)
  have s8 := same 8 (by omega)
  have s0 := same 0 (by omega)
  have c8 := acc 8 (by omega)
  have c0 := acc 0 (by omega)
  simp only [Nat.add_zero] at s0 c0
  constructor
  · evaluate [e2, e7, a8, s8, c8, at_.size i hi]
  · evaluate [e2, e7, a0, s0, c0, at_.start i hi]

/-- The width of the current part's type, from its plan node. -/
theorem lay_width_call (m : Module) (w : World) (linked : HasCodec m) (d : Desc) (sound : d.wellFormed = .ok ())
    (thin : narrow d = true) (inner : Nat) (cur : Memory) (p : Nat) (env : Env) (e8 : env 8 = p.toUInt64)
    (plan : PlanAt w cur p (words d)) (room : w.stackLo + (widthLevel + walkLevel) * d.nesting ≤ inner) :
    Runs m w inner env cur (.call "ssz_plan_width" [.var 8] 9) (assign env 9 (widthWord d)) cur :=
  Runs.call (values := [p.toUInt64]) (by simp [eval, e8]) (width_ok m w linked d sound thin inner cur p plan room)

/-- The step to the next part's type: the same node for a sequence, past the node for a struct. -/
theorem lay_advance (m : Module) (w : World) (linked : HasCodec m) (d : Desc) (sound : d.wellFormed = .ok ())
    (inner : Nat) (cur : Memory) (p : Nat) (same : Bool) (env : Env) (e1 : env 1 = if same then 1 else 0)
    (e8 : env 8 = p.toUInt64) (plan : PlanAt w cur p (words d))
    (room : w.stackLo + (widthLevel + walkLevel) * d.nesting ≤ inner) :
    Runs m w inner env cur layAdvance (assign env 8 (if same then p else p + 8 * (words d).length).toUInt64) cur := by
  cases same
  · have walked := next_ok m w linked d sound inner cur p plan (by
      have : walkLevel * d.nesting ≤ (widthLevel + walkLevel) * d.nesting :=
        Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
      omega)
    exact Runs.ite_true 1 (by simp [eval, Expr.eq, e1, Cond.holds]) (by decide)
      (Runs.call (values := [p.toUInt64]) (by simp [eval, e8]) walked)
  · have unchanged : assign env 8 p.toUInt64 = env := by
      funext x; by_cases h : x = 8 <;> simp [assign, h, e8]
    simp only [ite_true]
    rw [unchanged]
    exact Runs.ite_false (by simp [eval, Expr.eq, e1, Cond.holds]) (Runs.skip _ _ _ _ _)

/-- A size kept as a word, with a flag that is one exactly when the size passed what a word holds. -/
def layWrapped (v : UInt64) (T : Nat) : Prop := (v = 0 ∧ T < 2 ^ 64) ∨ (v = 1 ∧ 2 ^ 64 ≤ T)

set_option linter.unusedSimpArgs false in
/-- Growing the size by a step keeps the flag right. -/
theorem lay_grow (m : Module) (w : World) (inner : Nat) (env : Env) (cur : Memory) (step : Expr) (s T : Nat)
    (small : s < 2 ^ 64) (hs : eval w env cur step = some s.toUInt64) (e12 : env 12 = T.toUInt64)
    (e13 : layWrapped (env 13) T) :
    ∃ env', (∀ k, k ≠ 12 → k ≠ 13 → k ≠ 14 → env' k = env k) ∧ env' 12 = (T + s).toUInt64 ∧
      layWrapped (env' 13) (T + s) ∧
      ∀ rest env'' cur', Runs m w inner env' cur (.block rest) env'' cur' →
        Runs m w inner env cur (.block (layGrow step ++ rest)) env'' cur' := by
  have sumWord : (T + s).toUInt64 = T.toUInt64 + s.toUInt64 := by
    simp only [Nat.toUInt64_eq]; rw [UInt64.ofNat_add]
  -- The sum wraps exactly when the old sum, cut to a word, and the step pass what a word holds.
  have sumNat : ((T.toUInt64 + s.toUInt64 : UInt64)).toNat = (T % 2 ^ 64 + s) % 2 ^ 64 := by
    rw [UInt64.toNat_add]; simp
  have carry : (T.toUInt64 + s.toUInt64 < T.toUInt64) ↔ 2 ^ 64 ≤ T % 2 ^ 64 + s := by
    rw [UInt64.lt_iff_toNat_lt, sumNat]; simp [UInt64.toNat_ofNat]; omega
  let env₁ := assign env 14 (T.toUInt64 + s.toUInt64)
  let wrap' : UInt64 := if 2 ^ 64 ≤ T % 2 ^ 64 + s then 1 else env 13
  have test : Runs m w inner env₁ cur (.ite (Expr.lt (.var 14) (.var 12)) (.set 13 1) .skip)
      (assign env₁ 13 wrap') cur := by
    by_cases over : 2 ^ 64 ≤ T % 2 ^ 64 + s
    · have one : wrap' = 1 := by simp [wrap', over]
      rw [one]
      refine Runs.ite_true 1 ?_ (by decide) (Runs.set m w inner env₁ cur 13 1 1 rfl)
      simp [Expr.lt, eval, env₁, assign, e12, Cond.holds, carry.mpr over]
    · have unchanged : assign env₁ 13 wrap' = env₁ := by
        funext x; by_cases h : x = 13 <;> simp [assign, wrap', over, h, env₁]
      rw [unchanged]
      refine Runs.ite_false ?_ (Runs.skip _ _ _ _ _)
      simp [Expr.lt, eval, env₁, assign, e12, Cond.holds, show ¬ (T.toUInt64 + s.toUInt64 < T.toUInt64) from
        fun h => over (carry.mp h)]
  refine ⟨assign (assign env₁ 13 wrap') 12 (T.toUInt64 + s.toUInt64), fun k h12 h13 h14 => ?_, ?_, ?_, ?_⟩
  · simp [assign, env₁, h12, h13, h14]
  · simp [assign, sumWord]
  · simp only [assign, ite_eq_right (show (13 : Nat) ≠ 12 by decide), ite_eq_left rfl, wrap']
    rcases e13 with ⟨w0, lo⟩ | ⟨w1, hi⟩
    · by_cases over : 2 ^ 64 ≤ T % 2 ^ 64 + s
      · right; exact ⟨by simp [over], by omega⟩
      · left; exact ⟨by simp [over, w0], by omega⟩
    · right
      refine ⟨?_, by omega⟩
      by_cases o : 2 ^ 64 ≤ T % 2 ^ 64 + s <;> simp [o, w1]
  · intro rest env'' cur' ran
    exact Runs.block_cons (Runs.set _ _ _ _ _ 14 _ _ (by
        simp only [show (Expr.var 12 + step) = .op .add (.var 12) step from rfl, eval, hs, e12]; rfl))
      (Runs.block_cons test (Runs.block_cons (Runs.set _ _ _ _ _ 12 _ _ (by simp [eval, assign, env₁])) ran))

/-- The checking loop's condition: parts are left and none was refused. -/
theorem lay_cond_eval (w : World) (env : Env) (cur : Memory) (i N : Nat) (r : UInt64) (hi : i < 2 ^ 64)
    (hN : N < 2 ^ 64) (e7 : env 7 = i.toUInt64) (e3 : env 3 = N.toUInt64) (e6 : env 6 = r) :
    eval w env cur layCheckCond = some (if i < N ∧ r = 0 then 1 else 0) := by
  by_cases lt : i < N <;> by_cases z : r = 0 <;>
    simp [layCheckCond, eval, Expr.lt, Expr.eq, e7, e3, e6, Cond.holds, aluResult, lt, z,
      ofNat_lt_ofNat i N hi hN]

end EthLib.Consensus.Ssz.Native.Driver
