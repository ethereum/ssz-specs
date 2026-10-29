import SszNative.Proofs.Driver.Root.ColumnPaths
import SszNative.Proofs.Driver.Root.VectorOne
import SszNative.Proofs.Driver.Root.ContainerOne

/-!
The fixed-size roots driver meets its contract for every type it serves.

The driver reads the type's tag and takes one of five paths, each proved on its own.
A vector or a container calls the driver on its element or field types.
So the proof is an induction on the type, with the contract on the inner types as the hypothesis.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Asm

/-! ### The body -/

/-- The driver's body, with its five paths named. -/
theorem rootsOf_body : RootsOf.fn.body = .block [RootsOf.tag ::= ld RootsOf.p,
    ifElse (eq RootsOf.tag 7) [RootsOf.len ::= ld (RootsOf.p + 8), RootsOf.e ::= RootsOf.p + 16,
      ifElse (le (ld RootsOf.e) 1) (packedPath RootsOf.p) [callInto RootsOf.w "ssz_plan_fixed_width" [RootsOf.e],
        ifElse (eq RootsOf.count 1) vectorOnePath vectorColumns]]
    [ifElse (eq RootsOf.tag 10) [RootsOf.len ::= ld (RootsOf.p + 8), RootsOf.e ::= RootsOf.p + 16,
      RootsOf.off ::= 0, RootsOf.i ::= 0, ifElse (eq RootsOf.count 1) containerOnePath containerColumns]
      (packedPath RootsOf.p)]] := rfl

/-- A call of the driver does what its body does a frame below, from any variables holding its arguments. -/
theorem rootsOf_of_runs {m : Module} {w : World} (fns : RootsFns m) {d : Desc} {sp : Nat} {mem : Memory}
    {p base start stride count out ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (room : w.stackLo + 224 ≤ sp)
    (run : ∀ env, RootsEnv env p (base + start) stride count out ctx → ∃ env' mem',
      Runs m w (sp - 224) env mem RootsOf.fn.body env' mem' ∧
      RootsPost w mem mem' out (rootsNeed d count) ctx table zeros pad mask (rootsOf d b start stride count)) :
    ∃ mem', Calls m w "ssz_roots_of" sp [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat stride,
        UInt64.ofNat count, UInt64.ofNat out, UInt64.ofNat ctx] mem 0 mem' ∧
      RootsPost w mem mem' out (rootsNeed d count) ctx table zeros pad mask (rootsOf d b start stride count) := by
  obtain ⟨env', mem', body, post⟩ := run (entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat stride,
    UInt64.ofNat count, UInt64.ofNat out, UInt64.ofNat ctx]) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨mem', Calls.fn (env' := env') fns.roots (by rw [rootsFrame]; omega) rfl ?_ rfl, post⟩
  rw [rootsFrame, show sp - 8 - 8 * 27 = sp - 224 by omega]
  exact body

/-- A call's count is below the word size, since its roots fit below the cap. -/
theorem RootsPre.countSmall {w : World} {mem : Memory} {d : Desc}
    {p base start stride count out ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : RootsPre w mem d p base start stride count out ctx table zeros pad mask b) : count < 2 ^ 62 := by
  have roots := rootsNeed_roots d count
  simp only [sat] at roots
  have := pre.below
  have capv := cap_eq
  omega

/-! ### Each kind of type -/

/-- A type that is neither a vector nor a container takes the last path, and packs. -/
theorem rootsOf_other_ok {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RootsFns m)
    {d : Desc} (ok : Rootable d) (t7 : Plan.tag d ≠ 7) (t10 : Plan.tag d ≠ 10)
    (packs : ∀ b start stride count, rootsOf d b start stride count =
      packedRoots (fixedWidth d) (nodesFor (fixedWidth d)) b start stride count)
    (need : ∀ count, rootsNeed d count = packedNeed (satWidth d) count) : RootsOfOk m w d := by
  intro sp mem p base start stride count out ctx table zeros pad mask b stack pre
  have one := nesting_pos d
  have rs : rootsStack d = 10600 + 352 * d.nesting := rfl
  have ps : packedStack = 10568 := rfl
  have tl := tag_lt d
  refine rootsOf_of_runs fns (by omega) fun env ev => ?_
  -- The tag, which is neither a vector's nor a container's.
  have s0 := Runs.set' (m := m) (sp := sp - 224) (x := RootsOf.tag.idx) (eval_tag pre.plan (eval_var ev.p))
  have ev1 := ev.write (Plan.tag d).toUInt64 (x := 6) (by decide)
  have c7 : eval w (Asm.assign env 6 (Plan.tag d).toUInt64) mem (eq RootsOf.tag 7) = some 0 := by
    rw [eval_eq (eval_var assign_eq) (eval_lit 7) (by omega) (by decide), ite_eq_right t7]
  have c10 : eval w (Asm.assign env 6 (Plan.tag d).toUInt64) mem (eq RootsOf.tag 10) = some 0 := by
    rw [eval_eq (eval_var assign_eq) (eval_lit 10) (by omega) (by decide), ite_eq_right t10]
  obtain ⟨env', mem', run, post⟩ := packedPath_runs hash gmod fns (sp := sp - 224) pre ok (by omega) (by omega) ev1
    (x := RootsOf.p) (eval_var ev1.p) (packs b start stride count) (need count)
  refine ⟨env', mem', ?_, post⟩
  rw [rootsOf_body]
  exact Runs.block_cons s0 (Runs.block_cons (Runs.ifElse_false c7 (Runs.block_cons (Runs.ifElse_false c10 run)
    (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))

/-- A vector takes the first path: basic elements pack, and composite ones root alone or a column each. -/
theorem rootsOf_vector_ok {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RootsFns m)
    {element : Desc} {length : Nat} (ok : Rootable (.vector element length))
    (ih : element.isBasic = false → RootsOfOk m w element) : RootsOfOk m w (.vector element length) := by
  intro sp mem p base start stride count out ctx table zeros pad mask b stack pre
  obtain ⟨pl, wf, thin⟩ := ok
  have pe : plain element = true := by simpa [plain] using pl
  have se := wellFormed_vector wf
  have ne : narrow element = true := by simp only [narrow, Bool.and_eq_true] at thin; exact thin.2
  have rs : rootsStack (.vector element length) = 10600 + 352 * (element.nesting + 1) := rfl
  have rse : rootsStack element = 10600 + 352 * element.nesting := rfl
  have one := nesting_pos element
  have ps : packedStack = 10568 := rfl
  have ts : treeStack = 10552 := rfl
  have cs : columnsStack = 10600 := rfl
  have cf : RootsChunked.fn.frame = 15 := chunkedFrame
  have small := pre.countSmall
  have nest : (Desc.vector element length).nesting = element.nesting + 1 := rfl
  refine rootsOf_of_runs fns (by omega) fun env ev => ?_
  -- The tag of a vector.
  have s0 := Runs.set' (m := m) (sp := sp - 224) (x := 6) (eval_tag pre.plan (eval_var ev.p))
  let E1 := Asm.assign env 6 (Plan.tag (.vector element length)).toUInt64
  have c7 : eval w E1 mem (eq RootsOf.tag 7) = some 1 := by
    rw [eval_eq (eval_var assign_eq) (eval_lit 7) (by simp [Plan.tag]) (by decide)]; rfl
  -- The length, and the element's node right after the vector's two words.
  have pv := pre.plan
  simp only [Plan.words] at pv
  have planE : WordsAt w mem (p + 16) (Plan.words element) := (wordsAt_split pv).2
  have lenR : eval w E1 mem (ld (RootsOf.p + 8)) = some (UInt64.ofNat length) :=
    eval_word (wordsAt_split pv).1 1 (by simp) (eval_add (eval_var ((ev.write _ (by decide)).p)) (eval_lit 8))
  have s1 := Runs.set' (m := m) (sp := sp - 224) (x := 7) lenR
  let E2 := Asm.assign E1 7 (UInt64.ofNat length)
  have s2 := Runs.set' (m := m) (w := w) (sp := sp - 224) (mem := mem) (env := E2) (x := 8)
    (eval_add (eval_var (((ev.write _ (by decide)).write _ (by decide)).p)) (eval_lit 16))
  let E3 := Asm.assign E2 8 (UInt64.ofNat (p + 16))
  have ev3 : RootsEnv E3 p (base + start) stride count out ctx :=
    ((ev.write _ (by decide)).write _ (by decide)).write _ (by decide)
  have e37 : E3 7 = UInt64.ofNat length := by simp only [E3, E2]; rw [assign_ne (by decide), assign_eq]
  have e38 : E3 8 = UInt64.ofNat (p + 16) := assign_eq
  have c1 : eval w E3 mem (le (ld RootsOf.e) 1) = some (if element.isBasic then 1 else 0) :=
    eval_le_tag (eval_tag planE (eval_var e38))
  by_cases basic : element.isBasic = true
  · -- Basic elements pack, read at the vector's node.
    rw [ite_eq_left basic] at c1
    obtain ⟨env', mem', run, post⟩ := packedPath_runs hash gmod fns (sp := sp - 224) pre ⟨pl, wf, thin⟩ (by omega)
      (by omega) ev3 (x := RootsOf.p) (eval_var ev3.p) (by simp [rootsOf, basic]) (by simp [rootsNeed, basic, satWidth])
    refine ⟨env', mem', ?_, post⟩
    rw [rootsOf_body]
    exact Runs.block_cons s0 (Runs.block_cons (Runs.ifElse_true 1 c7 (by decide) (Runs.block_cons s1
      (Runs.block_cons s2 (Runs.block_cons (Runs.ifElse_true 1 c1 (by decide) run) (Runs.block_nil _ _ _ _ _)))))
      (Runs.block_nil _ _ _ _ _))
  have nb : element.isBasic = false := by simpa using basic
  rw [ite_eq_right basic] at c1
  -- The element's width.
  have width := planWidth_calls fns.plan element (p + 16) (sp - 224) mem planE se ne (by omega)
  have s3 := Runs.call (m := m) (sp := sp - 224) (env := E3) (mem := mem) (dst := 9) (args := [RootsOf.e])
    (by simp only [List.mapM_cons, List.mapM_nil, eval_var e38]; rfl) width
  let E4 := Asm.assign E3 9 (fixedWidth element).toUInt64
  have ev4 : RootsEnv E4 p (base + start) stride count out ctx := ev3.write _ (by decide)
  have e47 : E4 7 = UInt64.ofNat length := by simp only [E4]; rw [assign_ne (by decide), e37]
  have e48 : E4 8 = UInt64.ofNat (p + 16) := by simp only [E4]; rw [assign_ne (by decide), e38]
  have e49 : E4 9 = UInt64.ofNat (fixedWidth element) := assign_eq
  have cc : eval w E4 mem (eq RootsOf.count 1) = some (if count = 1 then 1 else 0) :=
    eval_eq (eval_var ev4.count) (eval_lit 1) (by omega) (by decide)
  by_cases single : count = 1
  · -- One vector: its elements' roots side by side, then their tree.
    subst single
    obtain ⟨env', mem', run, post⟩ := vectorOne_runs hash fns (ih nb) (sp := sp - 224) pre ⟨pl, wf, thin⟩ nb
      (by omega) (by omega) ev4 e47 e48 e49
    refine ⟨env', mem', ?_, post⟩
    rw [rootsOf_body]
    exact Runs.block_cons s0 (Runs.block_cons (Runs.ifElse_true 1 c7 (by decide) (Runs.block_cons s1
      (Runs.block_cons s2 (Runs.block_cons (Runs.ifElse_false c1 (Runs.block_cons s3 (Runs.block_cons
        (Runs.ifElse_true 1 cc (by decide) run) (Runs.block_nil _ _ _ _ _)))) (Runs.block_nil _ _ _ _ _)))))
      (Runs.block_nil _ _ _ _ _))
  · -- Several vectors: a column per element, then the tree across them.
    rw [ite_eq_right single] at cc
    obtain ⟨env', mem', run, post⟩ := vectorColumns_runs hash gmod fns (sp := sp - 224) pre ⟨pl, wf, thin⟩ nb single
      (ih nb) (by omega) (by omega) ev4 e47 e48 e49
    refine ⟨env', mem', ?_, post⟩
    rw [rootsOf_body]
    exact Runs.block_cons s0 (Runs.block_cons (Runs.ifElse_true 1 c7 (by decide) (Runs.block_cons s1
      (Runs.block_cons s2 (Runs.block_cons (Runs.ifElse_false c1 (Runs.block_cons s3 (Runs.block_cons
        (Runs.ifElse_false cc run) (Runs.block_nil _ _ _ _ _)))) (Runs.block_nil _ _ _ _ _)))))
      (Runs.block_nil _ _ _ _ _))

/-- A container takes the second path: one record roots its field nodes, several root a column per field. -/
theorem rootsOf_container_ok {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m)
    (fns : RootsFns m) {names : List String} {fields : List Desc} (ok : Rootable (.container names fields))
    (ih : ∀ f ∈ fields, RootsOfOk m w f) : RootsOfOk m w (.container names fields) := by
  intro sp mem p base start stride count out ctx table zeros pad mask b stack pre
  have rs : rootsStack (.container names fields) = 10600 + 352 * (Desc.deepestNesting fields + 1) := rfl
  have ts : treeStack = 10552 := rfl
  have cs : columnsStack = 10600 := rfl
  have small := pre.countSmall
  -- Each field's call, and each field's plan walk, fits the stack below the driver's frame.
  have room : ∀ f ∈ fields, w.stackLo + rootsStack f ≤ sp - 224 := fun f fm => by
    have nest := Ssz.Native.Driver.nesting_le_deepest fields f fm
    have rf : rootsStack f = 10600 + 352 * f.nesting := rfl
    omega
  refine rootsOf_of_runs fns (by omega) fun env ev => ?_
  -- The tag of a container.
  have s0 := Runs.set' (m := m) (sp := sp - 224) (x := 6) (eval_tag pre.plan (eval_var ev.p))
  let E1 := Asm.assign env 6 (Plan.tag (.container names fields)).toUInt64
  have c7 : eval w E1 mem (eq RootsOf.tag 7) = some 0 := by
    rw [eval_eq (eval_var assign_eq) (eval_lit 7) (by simp [Plan.tag]) (by decide)]; rfl
  have c10 : eval w E1 mem (eq RootsOf.tag 10) = some 1 := by
    rw [eval_eq (eval_var assign_eq) (eval_lit 10) (by simp [Plan.tag]) (by decide)]; rfl
  -- The field count, the first field's node, and a zero offset and index.
  have pv := pre.plan
  simp only [Plan.words] at pv
  have lenR : eval w E1 mem (ld (RootsOf.p + 8)) = some (UInt64.ofNat fields.length) :=
    eval_word (wordsAt_split pv).1 1 (by simp) (eval_add (eval_var ((ev.write _ (by decide)).p)) (eval_lit 8))
  have s1 := Runs.set' (m := m) (sp := sp - 224) (x := 7) lenR
  let E2 := Asm.assign E1 7 (UInt64.ofNat fields.length)
  have s2 := Runs.set' (m := m) (w := w) (sp := sp - 224) (mem := mem) (env := E2) (x := 8)
    (eval_add (eval_var (((ev.write _ (by decide)).write _ (by decide)).p)) (eval_lit 16))
  let E3 := Asm.assign E2 8 (UInt64.ofNat (p + 16))
  have s3 := Runs.set' (m := m) (w := w) (sp := sp - 224) (mem := mem) (env := E3) (x := 15) (eval_lit 0)
  let E4 := Asm.assign E3 15 (UInt64.ofNat 0)
  have s4 := Runs.set' (m := m) (w := w) (sp := sp - 224) (mem := mem) (env := E4) (x := 14) (eval_lit 0)
  let E5 := Asm.assign E4 14 (UInt64.ofNat 0)
  have ev5 : RootsEnv E5 p (base + start) stride count out ctx :=
    ((((ev.write _ (by decide)).write _ (by decide)).write _ (by decide)).write _ (by decide)).write _ (by decide)
  have e57 : E5 7 = UInt64.ofNat fields.length := by
    simp only [E5, E4, E3, E2]
    rw [assign_ne (by decide), assign_ne (by decide), assign_ne (by decide), assign_eq]
  have e58 : E5 8 = UInt64.ofNat (p + 16) := by
    simp only [E5, E4, E3]; rw [assign_ne (by decide), assign_ne (by decide), assign_eq]
  have e515 : E5 15 = UInt64.ofNat 0 := by simp only [E5, E4]; rw [assign_ne (by decide), assign_eq]
  have e514 : E5 14 = UInt64.ofNat 0 := assign_eq
  have cc : eval w E5 mem (eq RootsOf.count 1) = some (if count = 1 then 1 else 0) :=
    eval_eq (eval_var ev5.count) (eval_lit 1) (by omega) (by decide)
  by_cases single : count = 1
  · -- One record: its field nodes, then their tree.
    subst single
    obtain ⟨env', mem', run, post⟩ := containerOne_runs hash fns (sp := sp - 224) pre ok ih room (by omega)
      (by omega) ev5 e57 e58 e514 e515
    refine ⟨env', mem', ?_, post⟩
    rw [rootsOf_body]
    exact Runs.block_cons s0 (Runs.block_cons (Runs.ifElse_false c7 (Runs.block_cons (Runs.ifElse_true 1 c10
      (by decide) (Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons s3 (Runs.block_cons s4 (Runs.block_cons
        (Runs.ifElse_true 1 cc (by decide) run) (Runs.block_nil _ _ _ _ _)))))))
      (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))
  · -- Several records: a column per field, then the tree across them.
    rw [ite_eq_right single] at cc
    obtain ⟨env', mem', run, post⟩ := containerColumns_runs hash gmod fns (sp := sp - 224) pre ok single ih room
      (by omega) (by omega) ev5 e57 e58 e515 e514
    refine ⟨env', mem', ?_, post⟩
    rw [rootsOf_body]
    exact Runs.block_cons s0 (Runs.block_cons (Runs.ifElse_false c7 (Runs.block_cons (Runs.ifElse_true 1 c10
      (by decide) (Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons s3 (Runs.block_cons s4 (Runs.block_cons
        (Runs.ifElse_false cc run) (Runs.block_nil _ _ _ _ _)))))))
      (Runs.block_nil _ _ _ _ _))) (Runs.block_nil _ _ _ _ _))

/-! ### Every type it serves -/

/--
The fixed-size roots driver computes the Lean roots of values of every type it serves.

The proof is an induction on the type, with the contract on the element or field types as the hypothesis.
-/
theorem rootsOf_ok {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RootsFns m) :
    ∀ d, Rootable d → RootsOfOk m w d := by
  intro d
  -- Types and their field lists are handled together, by mutual induction.
  induction d using Desc.rec (motive_2 := fun fields => ∀ f ∈ fields, Rootable f → RootsOfOk m w f) with
  -- Scalars and byte or bit vectors are packed values.
  | bool | uint | byteVector | bitVector =>
    intro ok
    exact rootsOf_other_ok hash gmod fns ok (by simp [Plan.tag]) (by simp [Plan.tag])
      (fun _ _ _ _ => by rw [rootsOf] <;> simp) (fun _ => by rw [rootsNeed] <;> simp)
  -- Every other type is never plain.
  | byteList | bitList | progressiveBitList | list | progressiveList | progressiveContainer | compatibleUnion =>
    intro ok; simp [Rootable, plain] at ok
  | vector element length ih =>
    intro ok
    obtain ⟨pl, wf, thin⟩ := ok
    have pe : plain element = true := by simpa [plain] using pl
    have ne : narrow element = true := by simp only [narrow, Bool.and_eq_true] at thin; exact thin.2
    exact rootsOf_vector_ok hash gmod fns ⟨pl, wf, thin⟩ fun _ => ih ⟨pe, wellFormed_vector wf, ne⟩
  | container names fields ih =>
    intro ok
    exact rootsOf_container_ok hash gmod fns ok fun f fm => ih f fm (rootable_fields ok f fm)
  -- An empty field list has no members.
  | nil => rename_i member _; simp at member
  | cons field fields ihHead ihTail =>
    -- A member field is the head or in the tail.
    rename_i f member ok
    rcases List.mem_cons.mp member with here | later
    · subst here; exact ihHead ok
    · exact ihTail f later ok

end EthLib.Consensus.Ssz.Native.Driver
