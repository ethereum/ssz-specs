import SszNative.Proofs.Driver.Root.Size

/-!
Several records of a vector or a container are rooted one column at a time.

Each element or field gets a column: its roots across every record, one node per record.
The columns lie one after the other right after the output's first nodes, and each is a call of the driver on itself.
The column tree then roots across the columns, and its root column lands at the output.

What one call on an element or field type does is a hypothesis, so these proofs serve the induction on the type.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Asm

/-! ### Exact bounds -/

/-- A saturated sum below the cap leaves its plain sum below the cap. -/
theorem sadd_lt {a b : Nat} (h : sadd a b < scratchCap) : a + b < scratchCap := by
  rw [← sadd_of_lt h]; exact h

/-- A saturated product below the cap leaves its plain product below the cap. -/
theorem smul_lt {a b : Nat} (h : smul a b < scratchCap) : a * b < scratchCap := by
  rw [← smul_of_lt h]; exact h

/-- A column that ends before a later one starts: one more step of a product stays below a larger one. -/
theorem step_le {c j k : Nat} (h : j < k) : c * j + c ≤ c * k := by
  have := Nat.mul_le_mul_left c (show j + 1 ≤ k by omega)
  rw [Nat.mul_succ] at this
  exact this

/--
Below the cap, the bound for several records rooted a column at a time is exact.

It is a node per record, a column per element or field, and the larger of a column's needs and the tree's room.
-/
theorem columnsNeed_eq {most len count : Nat} (lpos : 1 ≤ len) (pos : 1 ≤ count)
    (below : sadd (sadd (smul 32 count) (smul (smul 32 count) (sat len)))
      (max most (smul (smul 64 count) (sat len))) < scratchCap) :
    sadd (sadd (smul 32 count) (smul (smul 32 count) (sat len))) (max most (smul (smul 64 count) (sat len))) =
      32 * count + 32 * (count * len) + max most (64 * (count * len)) := by
  have capv := cap_eq
  -- Peel the outer sum, then each of its parts.
  have t := sadd_lt below
  have t1 := sadd_lt (show sadd (smul 32 count) (smul (smul 32 count) (sat len)) < scratchCap by omega)
  have a32 : smul 32 count = 32 * count := smul_of_lt (by omega)
  rw [a32] at t1
  have t2 := smul_lt (show smul (32 * count) (sat len) < scratchCap by omega)
  -- The length is below the cap, as a record's column count times a positive count of nodes.
  have lsat : sat len = len := by
    have : sat len ≤ 32 * count * sat len := Nat.le_mul_of_pos_left _ (by omega)
    exact sat_of_lt (by omega)
  rw [lsat] at t t1 t2
  have b32 : smul (32 * count) len = 32 * count * len := smul_of_lt (by omega)
  -- The tree's room is below the cap too, so its parts are exact.
  have m64 : smul (smul 64 count) len < scratchCap := by omega
  have a64 : smul 64 count = 64 * count := by
    have big : smul 64 count ≤ smul (smul 64 count) len := by
      simp only [smul, sat]
      have : min (64 * count) scratchCap ≤ min (64 * count) scratchCap * len := Nat.le_mul_of_pos_right _ lpos
      omega
    exact smul_of_lt (by omega)
  rw [a64] at m64 ⊢
  have b64 : smul (64 * count) len = 64 * count * len := smul_of_lt m64
  simp only [a32, a64, lsat, b32, b64, Nat.mul_assoc 32, Nat.mul_assoc 64] at below ⊢
  simp only [sadd, sat] at below ⊢
  omega

/-- Below the cap, the bound for several records of a vector of composite elements is exact. -/
theorem vectorNeed_eq {e : Desc} {len count : Nat} (basic : e.isBasic = false) (many : count ≠ 1) (pos : 1 ≤ count)
    (lpos : 1 ≤ len) (below : rootsNeed (.vector e len) count < scratchCap) :
    rootsNeed (.vector e len) count =
      32 * count + 32 * (count * len) + max (rootsNeed e count) (64 * (count * len)) := by
  have hN : rootsNeed (.vector e len) count = sadd (sadd (smul 32 count) (smul (smul 32 count) (sat len)))
      (max (rootsNeed e count) (smul (smul 64 count) (sat len))) := by
    simp only [rootsNeed, basic, Bool.false_eq_true, ite_false, ite_eq_right many]
  rw [hN] at below ⊢
  exact columnsNeed_eq lpos pos below

/-- Below the cap, the bound for several records of a container is exact. -/
theorem containerNeed_eq {names : List String} {fields : List Desc} {count : Nat} (many : count ≠ 1)
    (pos : 1 ≤ count) (lpos : 1 ≤ fields.length) (below : rootsNeed (.container names fields) count < scratchCap) :
    rootsNeed (.container names fields) count = 32 * count + 32 * (count * fields.length) +
      max (fieldsRootsNeed fields count 0) (64 * (count * fields.length)) := by
  have hN : rootsNeed (.container names fields) count =
      sadd (sadd (smul 32 count) (smul (smul 32 count) (sat fields.length)))
        (max (fieldsRootsNeed fields count 0) (smul (smul 64 count) (sat fields.length))) := by
    simp only [rootsNeed, ite_eq_right many]
  rw [hN] at below ⊢
  exact columnsNeed_eq lpos pos below

/-! ### Memory changed only in the output -/

/-- The context stays filled in memory that changed only inside a call's output region and the padding area. -/
theorem RootsPre.readyAfter {w : World} {mem mem₂ : Memory} {d : Desc}
    {p base start stride count out ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : RootsPre w mem d p base start stride count out ctx table zeros pad mask b)
    (agree : ∀ a, ¬ (out ≤ a ∧ a < out + rootsNeed d count) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem₂ a = mem a) :
    RootReady w ctx table zeros pad mask mem₂ := by
  refine pre.ready.frame fun a held => ?_
  simp only [RootReady.Held] at held
  rcases held with h | h | h
  · exact agree a (outside_of_apart pre.oCtx h.1 h.2) (outside_of_apart' (apart_comm pre.ready.padCtx) h.1 h.2)
  · exact agree a (outside_of_apart pre.oTable h.1 h.2) (outside_of_apart' (apart_comm pre.ready.padTable) h.1 h.2)
  · exact agree a (outside_of_apart pre.oZeros h.1 h.2) (outside_of_apart' (apart_comm pre.ready.padZeros) h.1 h.2)

/-! ### A vector's columns -/

/-- The statements that root several records of a vector: a column per element, then the tree across them. -/
abbrev vectorColumns : List Stmt :=
  [RootsOf.c ::= RootsOf.out + 32 * RootsOf.count, RootsOf.i ::= 0,
    while_ (lt RootsOf.i RootsOf.len) [
      callInto RootsOf.sink "ssz_roots_of" [RootsOf.e, RootsOf.src + RootsOf.w * RootsOf.i, RootsOf.stride,
        RootsOf.count, RootsOf.c + 32 * RootsOf.count * RootsOf.i, RootsOf.ctx],
      RootsOf.i ::= RootsOf.i + 1],
    callInto RootsOf.d "ssz_depth_for" [RootsOf.len],
    callInto RootsOf.sink "ssz_root_columns" [RootsOf.c, RootsOf.len, RootsOf.count, RootsOf.d, RootsOf.ctx]]

/--
Several records of a vector of composite elements are rooted one column per element, then the tree across them.

Column i holds element i's roots across the records, a node per record, and is a call of the driver on the element.
What that call does is a hypothesis, the step of an induction on the type.
-/
theorem vectorColumns_runs {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RootsFns m)
    {sp : Nat} {mem : Memory} {element : Desc} {length : Nat} {p base start stride count out ctx table zeros pad : Nat}
    {mask : UInt64} {b : ByteArray}
    (pre : RootsPre w mem (.vector element length) p base start stride count out ctx table zeros pad mask b)
    (ok : Rootable (.vector element length)) (basic : element.isBasic = false) (many : count ≠ 1)
    (ih : RootsOfOk m w element) (room : w.stackLo + rootsStack element ≤ sp) (colRoom : w.stackLo + columnsStack ≤ sp)
    {env : Env} (ev : RootsEnv env p (base + start) stride count out ctx)
    (elen : env 7 = UInt64.ofNat length) (ee : env 8 = UInt64.ofNat (p + 16))
    (ew : env 9 = UInt64.ofNat (fixedWidth element)) :
    ∃ env' mem', Runs m w sp env mem (.block vectorColumns) env' mem' ∧
      RootsPost w mem mem' out (rootsNeed (.vector element length) count) ctx table zeros pad mask
        (rootsOf (.vector element length) b start stride count) := by
  obtain ⟨pl, wf, thin⟩ := ok
  have capv := cap_eq
  have plE : plain element = true := by simpa only [plain] using pl
  have spread := pre.spread
  have wpos := width_pos element plE (wellFormed_vector wf)
  have wide := width_narrow _ pl thin
  simp only [fixedWidth] at wide spread
  -- A well-formed vector has elements, so its width bounds its length.
  have lpos : 1 ≤ length := by
    have := width_pos _ pl wf
    simp only [fixedWidth] at this
    rcases Nat.eq_zero_or_pos length with z | z
    · rw [z, Nat.mul_zero] at this; omega
    · exact z
  have lw : length ≤ fixedWidth element * length := Nat.le_mul_of_pos_left _ wpos
  have cpos := pre.pos
  -- The bound, exactly: a node per record, a column per element, then an element's needs or the tree's room.
  have needEq := vectorNeed_eq basic many cpos lpos pre.below
  have below := pre.below
  rw [needEq] at below
  have big : count ≤ count * length := Nat.le_mul_of_pos_right _ lpos
  have maxR := Nat.le_max_left (rootsNeed element count) (64 * (count * length))
  have maxT := Nat.le_max_right (rootsNeed element count) (64 * (count * length))
  -- An element's roots take a node per record.
  have thinE : narrow element = true := by simp only [narrow, Bool.and_eq_true] at thin; exact thin.2
  have sized : ∀ s, (rootsOf element b s stride count).size = 32 * count := fun s =>
    rootsOf_size element ⟨plE, wellFormed_vector wf, thinE⟩ pre.usize b s stride count cpos (by omega)
  have lenSmall : length < 2 ^ 64 := by omega
  have countSmall : count < 2 ^ 64 := by omega
  have pv := pre.plan
  simp only [Plan.words] at pv
  have planE : WordsAt w mem (p + 16) (Plan.words element) := (wordsAt_split pv).2
  have planIn : p ≤ p + 16 ∧ p + 16 + 8 * (Plan.words element).length ≤
      p + 8 * (Plan.words (.vector element length)).length := by
    simp only [Plan.words, List.length_append]; constructor <;> simp <;> omega
  have dframe : DepthFor.fn.frame = 5 := by decide
  have cstack : columnsStack = 10600 := rfl
  have hstack : hashStack = 10392 := rfl
  -- The first column right after the output's nodes, and no element rooted yet.
  let E0 := Asm.assign (Asm.assign env 13 (UInt64.ofNat (out + 32 * count))) 14 (UInt64.ofNat 0)
  have r0 : Runs m w sp env mem (.block [RootsOf.c ::= RootsOf.out + 32 * RootsOf.count, RootsOf.i ::= 0]) E0 mem :=
    Runs.block_cons (Runs.set' (eval_add (eval_var ev.out) (eval_mul (eval_lit 32) (eval_var ev.count))))
      (Runs.block_cons (Runs.set' (eval_lit 0)) (Runs.block_nil _ _ _ _ _))
  -- The columns rooted so far are held in order, and memory is as at the start outside the output and the padding.
  let inv : Env → Memory → Prop := fun e mm => ∃ k, k ≤ length ∧ e 14 = UInt64.ofNat k ∧
    RootsEnv e p (base + start) stride count out ctx ∧ e 7 = UInt64.ofNat length ∧ e 8 = UInt64.ofNat (p + 16) ∧
    e 9 = UInt64.ofNat (fixedWidth element) ∧ e 13 = UInt64.ofNat (out + 32 * count) ∧
    (∀ j < k, Holds mm (out + 32 * count + 32 * count * j)
      (rootsOf element b (start + fixedWidth element * j) stride count)) ∧
    ∀ a, ¬ (out ≤ a ∧ a < out + rootsNeed (.vector element length) count) → ¬ (pad ≤ a ∧ a < pad + 1536) →
      mm a = mem a
  have start0 : inv E0 mem := by
    refine ⟨0, Nat.zero_le _, assign_eq, (ev.write _ (by decide)).write _ (by decide), ?_, ?_, ?_, ?_,
      fun j hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl⟩
    · simp only [E0]; rw [assign_ne (by decide), assign_ne (by decide), elen]
    · simp only [E0]; rw [assign_ne (by decide), assign_ne (by decide), ee]
    · simp only [E0]; rw [assign_ne (by decide), assign_ne (by decide), ew]
    · simp only [E0]; rw [assign_ne (by decide), assign_eq]
  obtain ⟨E1, M1, loop, ⟨k, hk, e14, ev1, e7, e8, e9, e13, cols, agree⟩, exit⟩ := Runs.loop_inv (m := m) (w := w)
    (sp := sp) (c := lt RootsOf.i RootsOf.len)
    (body := .block [callInto RootsOf.sink "ssz_roots_of" [RootsOf.e, RootsOf.src + RootsOf.w * RootsOf.i,
        RootsOf.stride, RootsOf.count, RootsOf.c + 32 * RootsOf.count * RootsOf.i, RootsOf.ctx],
      RootsOf.i ::= RootsOf.i + 1])
    inv (fun e _ => length - (e 14).toNat)
    (fun e mm (h : inv e mm) => by
      obtain ⟨k, hk, e14, _, e7, _⟩ := h
      exact ⟨_, eval_lt (eval_var e14) (eval_var e7) (by omega) lenSmall⟩)
    (fun e mm v (h : inv e mm) hv nz => by
      obtain ⟨k, hk, e14, evk, e7, e8, e9, e13, cols, agree⟩ := h
      rw [eval_lt (eval_var e14) (eval_var e7) (by omega) lenSmall] at hv
      have more : k < length := by
        by_cases h : k < length
        · exact h
        · rw [ite_eq_right h] at hv; cases hv; exact absurd rfl nz
      -- Column k lies inside the output region, after the columns before it.
      have step := step_le (c := 32 * count) more
      rw [Nat.mul_assoc 32 count length] at step
      have outIn : out ≤ out + 32 * count + 32 * count * k ∧
          out + 32 * count + 32 * count * k + rootsNeed element count ≤
            out + rootsNeed (.vector element length) count := by
        rw [needEq]; omega
      have wk := step_le (c := fixedWidth element) more
      have child := RootsPre.child pre agree planE planIn (Nat.le_trans (Nat.le_mul_of_pos_right _ lpos) pre.gap)
        pre.strideSmall cpos (start₂ := start + fixedWidth element * k)
        (fun j hj => by have := pre.inside j hj; simp only [fixedWidth] at this; omega)
        (by omega) (by omega) outIn
      obtain ⟨mem', call, held, ready, keep⟩ := ih sp mm _ _ _ _ _ _ _ _ _ _ _ _ room child
      rw [← Nat.add_assoc] at call
      have r1 := Runs.call (m := m) (sp := sp) (env := e) (mem := mm) (dst := RootsOf.sink.idx)
        (args := [RootsOf.e, RootsOf.src + RootsOf.w * RootsOf.i, RootsOf.stride, RootsOf.count,
          RootsOf.c + 32 * RootsOf.count * RootsOf.i, RootsOf.ctx])
        (by
          simp only [List.mapM_cons, List.mapM_nil, eval_var e8,
            eval_add (eval_var evk.src) (eval_mul (eval_var e9) (eval_var e14)), eval_var evk.stride,
            eval_var evk.count, eval_add (eval_var e13) (eval_mul (eval_mul (eval_lit 32) (eval_var evk.count))
              (eval_var e14)), eval_var evk.ctx]
          rfl) call
      have r2 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem') (x := 14) (env := Asm.assign e 10 0)
        (e := RootsOf.i + 1) (eval_add (eval_var (show Asm.assign e 10 0 14 = UInt64.ofNat k by
          rw [assign_ne (by decide)]; exact e14)) (eval_lit 1))
      refine ⟨_, mem', Runs.block_cons r1 (Runs.block_cons r2 (Runs.block_nil _ _ _ _ _)),
        ⟨k + 1, more, assign_eq, (evk.write _ (by decide)).write _ (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [assign_ne (by decide), assign_ne (by decide), e7]
      · rw [assign_ne (by decide), assign_ne (by decide), e8]
      · rw [assign_ne (by decide), assign_ne (by decide), e9]
      · rw [assign_ne (by decide), assign_ne (by decide), e13]
      · -- The new column lands after the others, which the call left alone.
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with lt | eq
        · have sj := step_le (c := 32 * count) lt
          refine (cols j lt).congr fun i hi => keep _ (by rw [sized] at hi; omega) ?_
          rw [sized] at hi
          exact outside_of_apart' pre.oPad (a := out + 32 * count + 32 * count * j + i) (by omega) (by
            rw [needEq]; omega)
        · subst eq; exact held
      · intro a o pd
        rw [keep a (fun h => o ⟨by omega, by omega⟩) pd, agree a o pd]
      · show length - (UInt64.ofNat (k + 1)).toNat < length - (e 14).toNat
        rw [e14, ofNat_toNat (by omega), ofNat_toNat (by omega)]
        omega)
    E0 mem start0
  -- The loop stops once every element has its column.
  rw [eval_lt (eval_var e14) (eval_var e7) (by omega) lenSmall] at exit
  have last : k = length := by
    by_cases h : k < length
    · rw [ite_eq_left h] at exit; cases exit
    · omega
  subst last
  have rd := pre.readyAfter agree
  -- The depth for the elements.
  have depth := depthFor_calls fns.plan.depth (w := w) (sp := sp) (by rw [dframe]; omega) (UInt64.ofNat k) M1
  rw [ofNat_toNat lenSmall] at depth
  have r3 := Runs.call (m := m) (sp := sp) (env := E1) (mem := M1) (dst := RootsOf.d.idx) (args := [RootsOf.len])
    (by simp only [List.mapM_cons, List.mapM_nil, eval_var e7]; rfl) depth
  -- The tree across the columns.
  obtain ⟨len, get⟩ := elementColumns_get element b start stride count (fixedWidth element) k
  have hz : depthFor k ≤ zeroHeights := by
    have h := depthFor_word (UInt64.ofNat k)
    rw [ofNat_toNat lenSmall] at h
    exact h
  have tree := rootColumns_calls hash gmod fns.plan.depth fns.columns colRoom rd
    (out := out) (count := count) (depth := depthFor k) (span := rootsNeed (.vector element k) count)
    (elementColumns element b start stride count (fixedWidth element) k)
    (fun c hc => by rw [get c hc, sized])
    (fun c hc => by rw [get c hc, Nat.mul_comm c]; exact cols c (by omega))
    (by omega) (by omega) (by rw [len]; exact Nat.le_refl _) hz
    (by rw [pre.usize]; omega)
    (by rw [len, Nat.sub_self, Nat.add_zero, needEq, Nat.mul_assoc 3 k, Nat.mul_left_comm k 32 count,
      Nat.mul_comm k count]; omega)
    pre.acc pre.oPad pre.oCtx pre.oTable pre.oZeros
  rw [len] at tree
  obtain ⟨mem', call, held, ready, keep⟩ := tree
  have r4 := Runs.call (m := m) (sp := sp) (env := Asm.assign E1 12 (depthFor k).toUInt64) (mem := M1)
    (dst := RootsOf.sink.idx) (args := [RootsOf.c, RootsOf.len, RootsOf.count, RootsOf.d, RootsOf.ctx])
    (by
      simp only [List.mapM_cons, List.mapM_nil,
        eval_var (show Asm.assign E1 12 (depthFor k).toUInt64 13 = UInt64.ofNat (out + 32 * count) by
          rw [assign_ne (by decide)]; exact e13),
        eval_var (show Asm.assign E1 12 (depthFor k).toUInt64 7 = UInt64.ofNat k by
          rw [assign_ne (by decide)]; exact e7),
        eval_var (show Asm.assign E1 12 (depthFor k).toUInt64 3 = UInt64.ofNat count by
          rw [assign_ne (by decide)]; exact ev1.count),
        eval_var (show Asm.assign E1 12 (depthFor k).toUInt64 12 = UInt64.ofNat (depthFor k) from assign_eq),
        eval_var (show Asm.assign E1 12 (depthFor k).toUInt64 5 = UInt64.ofNat ctx by
          rw [assign_ne (by decide)]; exact ev1.ctx)]
      rfl) call
  have code : rootsOf (.vector element k) b start stride count =
      columnTreeTo (elementColumns element b start stride count (fixedWidth element) k) count (depthFor k) := by
    simp [rootsOf, basic, many]
  refine ⟨_, mem', Runs.block_append r0 (Runs.block_cons loop (Runs.block_cons r3 (Runs.block_cons r4
    (Runs.block_nil _ _ _ _ _)))), by rw [code]; exact held, ready, fun a o pd => ?_⟩
  rw [keep a o pd, agree a o pd]

/-! ### A container's columns -/

/-- The next field starts where this one ends. -/
theorem offsetOf_succ : ∀ (fields : List Desc) (k : Nat) (h : k < fields.length),
    offsetOf fields (k + 1) = offsetOf fields k + fixedWidth fields[k]
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | f :: rest, 0, _ => by simp [offsetOf, fieldsWidth]
  | f :: rest, k + 1, h => by
    -- Past the first field, both offsets carry its width.
    have := offsetOf_succ rest k (by simpa using h)
    simp only [offsetOf, List.take_succ_cons, fieldsWidth, List.getElem_cons_succ] at this ⊢
    omega

/-- The next field's plan starts where this one's ends. -/
theorem wordsAll_take_succ : ∀ (fields : List Desc) (k : Nat) (h : k < fields.length),
    (Plan.wordsAll (fields.take (k + 1))).length =
      (Plan.wordsAll (fields.take k)).length + (Plan.words fields[k]).length
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | f :: rest, 0, _ => by simp [Plan.wordsAll]
  | f :: rest, k + 1, h => by
    -- Past the first field, both lengths carry its plan's.
    have := wordsAll_take_succ rest k (by simpa using h)
    simp only [List.take_succ_cons, Plan.wordsAll, List.length_append, List.getElem_cons_succ] at this ⊢
    omega

/-- Each field's plan lies in memory after the plans of the fields before it, inside the fields' plans. -/
theorem fieldPlan_at {w : World} {mem : Memory} : ∀ (fields : List Desc) (a k : Nat) (h : k < fields.length),
    WordsAt w mem a (Plan.wordsAll fields) →
    WordsAt w mem (a + 8 * (Plan.wordsAll (fields.take k)).length) (Plan.words fields[k]) ∧
      (Plan.wordsAll (fields.take k)).length + (Plan.words fields[k]).length ≤ (Plan.wordsAll fields).length
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | f :: rest, a, 0, _, hw => by
    simp only [Plan.wordsAll] at hw
    simp only [List.take_zero, Plan.wordsAll, List.length_nil, Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero,
      List.length_append, Nat.zero_add]
    exact ⟨(wordsAt_split hw).1, Nat.le_add_right _ _⟩
  | f :: rest, a, k + 1, h, hw => by
    -- Past the first field, its plan comes first.
    simp only [Plan.wordsAll] at hw
    have := fieldPlan_at rest (a + 8 * (Plan.words f).length) k (by simpa using h) (wordsAt_split hw).2
    simp only [List.take_succ_cons, Plan.wordsAll, List.length_append, List.getElem_cons_succ]
    rw [show a + 8 * ((Plan.words f).length + (Plan.wordsAll (rest.take k)).length) =
      a + 8 * (Plan.words f).length + 8 * (Plan.wordsAll (rest.take k)).length by omega]
    exact ⟨this.1, by omega⟩

/-- The statements that root several records of a container: a column per field, then the tree across them. -/
abbrev containerColumns : List Stmt :=
  [RootsOf.c ::= RootsOf.out + 32 * RootsOf.count,
    while_ (lt RootsOf.i RootsOf.len) [
      callInto RootsOf.sink "ssz_roots_of" [RootsOf.e, RootsOf.src + RootsOf.off, RootsOf.stride, RootsOf.count,
        RootsOf.c + 32 * RootsOf.count * RootsOf.i, RootsOf.ctx],
      callInto RootsOf.w "ssz_plan_fixed_width" [RootsOf.e], RootsOf.off ::= RootsOf.off + RootsOf.w,
      callInto RootsOf.e "ssz_plan_next" [RootsOf.e], RootsOf.i ::= RootsOf.i + 1],
    callInto RootsOf.d "ssz_depth_for" [RootsOf.len],
    callInto RootsOf.sink "ssz_root_columns" [RootsOf.c, RootsOf.len, RootsOf.count, RootsOf.d, RootsOf.ctx]]

/--
Several records of a container are rooted one column per field, then the tree across them.

Column i holds field i's roots across the records, a node per record, and is a call of the driver on the field.
What that call does is a hypothesis for every field, the step of an induction on the type.
-/
theorem containerColumns_runs {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m)
    (fns : RootsFns m) {sp : Nat} {mem : Memory} {names : List String} {fields : List Desc}
    {p base start stride count out ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : RootsPre w mem (.container names fields) p base start stride count out ctx table zeros pad mask b)
    (ok : Rootable (.container names fields)) (many : count ≠ 1) (ih : ∀ f ∈ fields, RootsOfOk m w f)
    (room : ∀ f ∈ fields, w.stackLo + rootsStack f ≤ sp)
    (planRoom : w.stackLo + 112 * Desc.deepestNesting fields ≤ sp) (colRoom : w.stackLo + columnsStack ≤ sp)
    {env : Env} (ev : RootsEnv env p (base + start) stride count out ctx)
    (elen : env 7 = UInt64.ofNat fields.length) (ee : env 8 = UInt64.ofNat (p + 16))
    (eo : env 15 = UInt64.ofNat 0) (ei : env 14 = UInt64.ofNat 0) :
    ∃ env' mem', Runs m w sp env mem (.block containerColumns) env' mem' ∧
      RootsPost w mem mem' out (rootsNeed (.container names fields) count) ctx table zeros pad mask
        (rootsOf (.container names fields) b start stride count) := by
  obtain ⟨pl, wf, thin⟩ := ok
  have capv := cap_eq
  have plF : plainAll fields = true := by simpa only [plain] using pl
  have wfF := allWellFormed_mem fields (wellFormed_container wf)
  have thinF : narrowAll fields = true := by
    simp only [narrow, Bool.and_eq_true] at thin
    exact thin.2
  have spread := pre.spread
  simp only [fixedWidth] at spread
  -- A well-formed container has fields.
  have nonempty : 1 ≤ fields.length := by
    rcases fields with _ | ⟨f, rest⟩
    · simp [Desc.wellFormed, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at wf
    · simp
  have cpos := pre.pos
  -- The bound, exactly: a node per record, a column per field, then a field's needs or the tree's room.
  have needEq := containerNeed_eq many cpos nonempty pre.below
  have below := pre.below
  rw [needEq] at below
  have big : count ≤ count * fields.length := Nat.le_mul_of_pos_right _ nonempty
  have big' : fields.length ≤ count * fields.length := Nat.le_mul_of_pos_left _ cpos
  have maxR := Nat.le_max_left (fieldsRootsNeed fields count 0) (64 * (count * fields.length))
  have maxT := Nat.le_max_right (fieldsRootsNeed fields count 0) (64 * (count * fields.length))
  -- A field's roots take a node per record.
  have sized : ∀ f ∈ fields, ∀ s, (rootsOf f b s stride count).size = 32 * count := fun f fm s =>
    rootsOf_size f ⟨plainAll_mem fields plF f fm, wfF f fm, narrow_mem fields thinF f fm⟩ pre.usize b s stride count
      cpos (by have := fieldsRootsNeed_mem fields count 0 f fm; omega)
  have lenSmall : fields.length < 2 ^ 64 := by omega
  have countSmall : count < 2 ^ 64 := by omega
  have pv := pre.plan
  simp only [Plan.words] at pv
  have planF : WordsAt w mem (p + 16) (Plan.wordsAll fields) := (wordsAt_split pv).2
  have planLen : 8 * (Plan.words (.container names fields)).length = 16 + 8 * (Plan.wordsAll fields).length := by
    simp only [Plan.words, List.length_append, List.length_cons, List.length_nil]
    omega
  have dframe : DepthFor.fn.frame = 5 := by decide
  have cstack : columnsStack = 10600 := rfl
  have hstack : hashStack = 10392 := rfl
  have walk : walkLevel = 112 := walkLevel_eq
  -- Where field k's plan starts.
  let pos : Nat → Nat := fun k => p + 16 + 8 * (Plan.wordsAll (fields.take k)).length
  -- The first column right after the output's nodes.
  let E0 := Asm.assign env 13 (UInt64.ofNat (out + 32 * count))
  have r0 : Runs m w sp env mem (RootsOf.c ::= RootsOf.out + 32 * RootsOf.count) E0 mem :=
    Runs.set' (eval_add (eval_var ev.out) (eval_mul (eval_lit 32) (eval_var ev.count)))
  -- The columns rooted so far are held in order, and memory is as at the start outside the output and the padding.
  let inv : Env → Memory → Prop := fun e mm => ∃ k, k ≤ fields.length ∧ e 14 = UInt64.ofNat k ∧
    RootsEnv e p (base + start) stride count out ctx ∧ e 7 = UInt64.ofNat fields.length ∧
    e 8 = UInt64.ofNat (pos k) ∧ e 15 = UInt64.ofNat (offsetOf fields k) ∧ e 13 = UInt64.ofNat (out + 32 * count) ∧
    (∀ j (hj : j < fields.length), j < k →
      Holds mm (out + 32 * count + 32 * count * j) (rootsOf fields[j] b (start + offsetOf fields j) stride count)) ∧
    ∀ a, ¬ (out ≤ a ∧ a < out + rootsNeed (.container names fields) count) → ¬ (pad ≤ a ∧ a < pad + 1536) →
      mm a = mem a
  have start0 : inv E0 mem := by
    refine ⟨0, Nat.zero_le _, ?_, ev.write _ (by decide), ?_, ?_, ?_, assign_eq,
      fun j _ hj => absurd hj (Nat.not_lt_zero _), fun _ _ _ => rfl⟩
    · simp only [E0]; rw [assign_ne (by decide), ei]
    · simp only [E0]; rw [assign_ne (by decide), elen]
    · simp only [E0, pos, List.take_zero, Plan.wordsAll, List.length_nil, Nat.mul_zero, Nat.add_zero]
      rw [assign_ne (by decide), ee]
    · simp only [E0, offsetOf, List.take_zero, fieldsWidth]
      rw [assign_ne (by decide), eo]
  obtain ⟨E1, M1, loop, ⟨k, hk, e14, ev1, e7, e8, e15, e13, cols, agree⟩, exit⟩ := Runs.loop_inv (m := m)
    (w := w) (sp := sp) (c := lt RootsOf.i RootsOf.len)
    (body := .block [callInto RootsOf.sink "ssz_roots_of" [RootsOf.e, RootsOf.src + RootsOf.off, RootsOf.stride,
        RootsOf.count, RootsOf.c + 32 * RootsOf.count * RootsOf.i, RootsOf.ctx],
      callInto RootsOf.w "ssz_plan_fixed_width" [RootsOf.e], RootsOf.off ::= RootsOf.off + RootsOf.w,
      callInto RootsOf.e "ssz_plan_next" [RootsOf.e], RootsOf.i ::= RootsOf.i + 1])
    inv (fun e _ => fields.length - (e 14).toNat)
    (fun e mm (h : inv e mm) => by
      obtain ⟨k, hk, e14, _, e7, _⟩ := h
      exact ⟨_, eval_lt (eval_var e14) (eval_var e7) (by omega) lenSmall⟩)
    (fun e mm v (h : inv e mm) hv nz => by
      obtain ⟨k, hk, e14, evk, e7, e8, e15, e13, cols, agree⟩ := h
      rw [eval_lt (eval_var e14) (eval_var e7) (by omega) lenSmall] at hv
      have more : k < fields.length := by
        by_cases h : k < fields.length
        · exact h
        · rw [ite_eq_right h] at hv; cases hv; exact absurd rfl nz
      have member : fields[k] ∈ fields := List.getElem_mem more
      -- Field k's plan, inside the container's.
      have fp := fieldPlan_at fields (p + 16) k more planF
      have planIn : p ≤ pos k ∧ pos k + 8 * (Plan.words fields[k]).length ≤
          p + 8 * (Plan.words (.container names fields)).length := by
        rw [planLen]; simp only [pos]; omega
      -- Field k sits inside the record, at its offset.
      have offLe := offsetOf_le fields k more
      have gap := pre.gap
      simp only [fixedWidth] at gap
      have fieldNeed := fieldsRootsNeed_mem fields count 0 fields[k] member
      -- Column k lies inside the output region, after the columns before it.
      have step := step_le (c := 32 * count) more
      rw [Nat.mul_assoc 32 count fields.length] at step
      have outIn : out ≤ out + 32 * count + 32 * count * k ∧
          out + 32 * count + 32 * count * k + rootsNeed fields[k] count ≤
            out + rootsNeed (.container names fields) count := by
        rw [needEq]; omega
      have child := RootsPre.child pre agree fp.1 planIn (by omega) pre.strideSmall cpos
        (start₂ := start + offsetOf fields k)
        (fun j hj => by have := pre.inside j hj; simp only [fixedWidth] at this; omega)
        (by omega) (by omega) outIn
      obtain ⟨mem', call, held, ready, keep⟩ := ih fields[k] member sp mm _ _ _ _ _ _ _ _ _ _ _ _
        (room fields[k] member) child
      rw [← Nat.add_assoc] at call
      have r1 := Runs.call (m := m) (sp := sp) (env := e) (mem := mm) (dst := RootsOf.sink.idx)
        (args := [RootsOf.e, RootsOf.src + RootsOf.off, RootsOf.stride, RootsOf.count,
          RootsOf.c + 32 * RootsOf.count * RootsOf.i, RootsOf.ctx])
        (by
          simp only [List.mapM_cons, List.mapM_nil, eval_var e8, eval_add (eval_var evk.src) (eval_var e15),
            eval_var evk.stride, eval_var evk.count, eval_add (eval_var e13)
              (eval_mul (eval_mul (eval_lit 32) (eval_var evk.count)) (eval_var e14)), eval_var evk.ctx]
          rfl) call
      -- The plan is outside the output region and the padding area, so the call left it alone.
      have plan' : WordsAt w mem' (pos k) (Plan.words fields[k]) := planAt_congr fp.1 fun a lo hi => by
        have o := outside_of_apart pre.oPlan (a := a) (by omega) (by omega)
        have pd := outside_of_apart' pre.planPad (a := a) (by omega) (by omega)
        rw [keep a (fun h => o ⟨by omega, by omega⟩) pd, agree a o pd]
      have wfk := wfF fields[k] member
      have deep := nesting_le_deepest fields fields[k] member
      have deeper := Nat.mul_le_mul_left 112 deep
      -- The field's width, then the offset past it.
      have width := planWidth_calls fns.plan fields[k] (pos k) sp mem' plan' wfk (narrow_mem fields thinF _ member)
        (by omega)
      let A1 := Asm.assign e 10 0
      have r2 := Runs.call (m := m) (sp := sp) (env := A1) (mem := mem') (dst := RootsOf.w.idx)
        (args := [RootsOf.e])
        (by
          simp only [List.mapM_cons, List.mapM_nil,
            eval_var (show A1 8 = UInt64.ofNat (pos k) by simp only [A1]; rw [assign_ne (by decide)]; exact e8)]
          rfl) width
      let A2 := Asm.assign A1 9 (fixedWidth fields[k]).toUInt64
      have r3 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem') (x := 15) (env := A2)
        (e := RootsOf.off + RootsOf.w)
        (eval_add (eval_var (show A2 15 = UInt64.ofNat (offsetOf fields k) by
            simp only [A2, A1]; rw [assign_ne (by decide), assign_ne (by decide)]; exact e15))
          (eval_var (show A2 9 = UInt64.ofNat (fixedWidth fields[k]) from assign_eq)))
      let A3 := Asm.assign A2 15 (UInt64.ofNat (offsetOf fields k + fixedWidth fields[k]))
      -- The next field's plan.
      have next := next_ok m w fns.plan.codec fields[k] wfk sp mem' (pos k) plan' (by rw [walk]; omega)
      have r4 := Runs.call (m := m) (sp := sp) (env := A3) (mem := mem') (dst := RootsOf.e.idx)
        (args := [RootsOf.e])
        (by
          simp only [List.mapM_cons, List.mapM_nil,
            eval_var (show A3 8 = UInt64.ofNat (pos k) by
              simp only [A3, A2, A1]; rw [assign_ne (by decide), assign_ne (by decide), assign_ne (by decide)]
              exact e8)]
          rfl) next
      let A4 := Asm.assign A3 8 (pos k + 8 * (Plan.words fields[k]).length).toUInt64
      have r5 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem') (x := 14) (env := A4)
        (e := RootsOf.i + 1) (eval_add (eval_var (show A4 14 = UInt64.ofNat k by
          simp only [A4, A3, A2, A1]
          rw [assign_ne (by decide), assign_ne (by decide), assign_ne (by decide), assign_ne (by decide)]
          exact e14)) (eval_lit 1))
      refine ⟨_, mem', Runs.block_cons r1 (Runs.block_cons r2 (Runs.block_cons r3 (Runs.block_cons r4
        (Runs.block_cons r5 (Runs.block_nil _ _ _ _ _))))),
        ⟨k + 1, more, assign_eq, ((((evk.write _ (by decide)).write _ (by decide)).write _ (by decide)).write _
          (by decide)).write _ (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · simp only [A4, A3, A2, A1]
        rw [assign_ne (by decide), assign_ne (by decide), assign_ne (by decide), assign_ne (by decide),
          assign_ne (by decide), e7]
      · simp only [A4, A3, A2, A1]
        rw [assign_ne (by decide), assign_eq]
        simp only [pos]
        rw [wordsAll_take_succ fields k more, Nat.mul_add, Nat.add_assoc]
      · simp only [A4, A3, A2, A1]
        rw [assign_ne (by decide), assign_ne (by decide), assign_eq, offsetOf_succ fields k more]
      · simp only [A4, A3, A2, A1]
        rw [assign_ne (by decide), assign_ne (by decide), assign_ne (by decide), assign_ne (by decide),
          assign_ne (by decide), e13]
      · -- The new column lands after the others, which the call left alone.
        intro j hj hjk
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with lt | eq
        · have sj := step_le (c := 32 * count) lt
          have sz := sized fields[j] (List.getElem_mem hj) (start + offsetOf fields j)
          refine (cols j hj lt).congr fun i hi => keep _ (by rw [sz] at hi; omega) ?_
          rw [sz] at hi
          exact outside_of_apart' pre.oPad (a := out + 32 * count + 32 * count * j + i) (by omega) (by
            rw [needEq]; omega)
        · subst eq; exact held
      · intro a o pd
        rw [keep a (fun h => o ⟨by omega, by omega⟩) pd, agree a o pd]
      · show fields.length - (UInt64.ofNat (k + 1)).toNat < fields.length - (e 14).toNat
        rw [e14, ofNat_toNat (by omega), ofNat_toNat (by omega)]
        omega)
    E0 mem start0
  -- The loop stops once every field has its column.
  rw [eval_lt (eval_var e14) (eval_var e7) (by omega) lenSmall] at exit
  have last : k = fields.length := by
    by_cases h : k < fields.length
    · rw [ite_eq_left h] at exit; cases exit
    · omega
  have rd := pre.readyAfter agree
  -- The depth for the fields.
  have depth := depthFor_calls fns.plan.depth (w := w) (sp := sp) (by rw [dframe]; omega)
    (UInt64.ofNat fields.length) M1
  rw [ofNat_toNat lenSmall] at depth
  have r3 := Runs.call (m := m) (sp := sp) (env := E1) (mem := M1) (dst := RootsOf.d.idx) (args := [RootsOf.len])
    (by simp only [List.mapM_cons, List.mapM_nil, eval_var e7]; rfl) depth
  -- The tree across the columns.
  obtain ⟨len, get⟩ := fieldColumns_get b start stride count fields 0
  have hz : depthFor fields.length ≤ zeroHeights := by
    have h := depthFor_word (UInt64.ofNat fields.length)
    rw [ofNat_toNat lenSmall] at h
    exact h
  have tree := rootColumns_calls hash gmod fns.plan.depth fns.columns colRoom rd
    (out := out) (count := count) (depth := depthFor fields.length)
    (span := rootsNeed (.container names fields) count) (fieldColumns fields b start stride count 0)
    (fun c hc => by
      rw [get c (by omega) hc]
      exact sized _ (List.getElem_mem _) _)
    (fun c hc => by
      rw [get c (by omega) hc, Nat.zero_add, Nat.mul_comm c]
      exact cols c (by omega) (by omega))
    (by omega) (by omega) (by rw [len]; exact Nat.le_refl _) hz
    (by rw [pre.usize]; omega)
    (by rw [len, Nat.sub_self, Nat.add_zero, needEq, Nat.mul_assoc 3 fields.length,
      Nat.mul_left_comm fields.length 32 count, Nat.mul_comm fields.length count]; omega)
    pre.acc pre.oPad pre.oCtx pre.oTable pre.oZeros
  rw [len] at tree
  obtain ⟨mem', call, held, ready, keep⟩ := tree
  have r4 := Runs.call (m := m) (sp := sp) (env := Asm.assign E1 12 (depthFor fields.length).toUInt64) (mem := M1)
    (dst := RootsOf.sink.idx) (args := [RootsOf.c, RootsOf.len, RootsOf.count, RootsOf.d, RootsOf.ctx])
    (by
      simp only [List.mapM_cons, List.mapM_nil,
        eval_var (show Asm.assign E1 12 (depthFor fields.length).toUInt64 13 = UInt64.ofNat (out + 32 * count) by
          rw [assign_ne (by decide)]; exact e13),
        eval_var (show Asm.assign E1 12 (depthFor fields.length).toUInt64 7 = UInt64.ofNat fields.length by
          rw [assign_ne (by decide)]; exact e7),
        eval_var (show Asm.assign E1 12 (depthFor fields.length).toUInt64 3 = UInt64.ofNat count by
          rw [assign_ne (by decide)]; exact ev1.count),
        eval_var (show Asm.assign E1 12 (depthFor fields.length).toUInt64 12 =
          UInt64.ofNat (depthFor fields.length) from assign_eq),
        eval_var (show Asm.assign E1 12 (depthFor fields.length).toUInt64 5 = UInt64.ofNat ctx by
          rw [assign_ne (by decide)]; exact ev1.ctx)]
      rfl) call
  have code : rootsOf (.container names fields) b start stride count =
      columnTreeTo (fieldColumns fields b start stride count 0) count (depthFor fields.length) := by
    rw [rootsOf]; simp [many]
  refine ⟨_, mem', Runs.block_cons r0 (Runs.block_cons loop (Runs.block_cons r3 (Runs.block_cons r4
    (Runs.block_nil _ _ _ _ _)))), by rw [code]; exact held, ready, fun a o pd => ?_⟩
  rw [keep a o pd, agree a o pd]

end EthLib.Consensus.Ssz.Native.Driver
