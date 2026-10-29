import Ssz.Proofs.Type.CompatibilityBudget
import Ssz.Proofs.Type.Legality
import SszNative.Proofs.Driver.Validate.PlanCheck
import SszNative.Proofs.Plan.RoundTrip
import Ssz.Proofs.Type.Equality
import Std.Data.String.ToNat

/-!
What the native compatibility check relies on, about types alone.

A type whose fields are named as a plan names them is its own renaming, so two such types are equal exactly when their
words are.
Compatibility answers the same at every budget past the left type's nesting, so the native check, which has none,
computes it.
Two layouts named by position agree exactly when every position both set holds compatible fields.
-/

namespace Ssz.Native.Driver.Validate

open Ssz Ssz.Native

mutual

/-- A type named as a plan names it is its own renaming. -/
theorem rename_of_named : ∀ d : Desc, named d = true → Plan.rename d = d
  | .bool, _ | .uint _, _ | .byteVector _, _ | .byteList _, _ | .bitVector _, _ | .bitList _, _
  | .progressiveBitList _, _ => by simp [Plan.rename]
  | .vector e _, h | .list e _, h | .progressiveList e _, h => by
    simp [Plan.rename, rename_of_named e (by simpa [named] using h)]
  | .container names fs, h | .progressiveContainer _ names fs, h => by
    simp only [named, Bool.and_eq_true, beq_iff_eq] at h
    simp [Plan.rename, renameAll_of_namedAll fs h.2, h.1]
  | .compatibleUnion _ fs, h => by
    simp [Plan.rename, renameAll_of_namedAll fs (by simpa [named] using h)]

/-- Types named as a plan names them are their own renamings. -/
theorem renameAll_of_namedAll : ∀ ds : List Desc, namedAll ds = true → Plan.renameAll ds = ds
  | [], _ => rfl
  | d :: rest, h => by
    simp only [namedAll, Bool.and_eq_true] at h
    simp [Plan.renameAll, rename_of_named d h.1, renameAll_of_namedAll rest h.2]

end

mutual

/-- A type that fits the native check pairs each union's selectors with its options. -/
theorem paired_of_fits : ∀ d : Desc, fitsNative d = true → Plan.paired d = true
  | .bool, _ | .uint _, _ | .byteVector _, _ | .byteList _, _ | .bitVector _, _ | .bitList _, _
  | .progressiveBitList _, _ => rfl
  | .vector e _, h | .list e _, h | .progressiveList e _, h => by
    simp only [fitsNative, Bool.and_eq_true] at h
    simp only [Plan.paired]
    first | exact paired_of_fits e h.1.1 | exact paired_of_fits e h.1
  | .container _ fs, h | .progressiveContainer _ _ fs, h => by
    simp only [fitsNative, Bool.and_eq_true] at h
    exact pairedAll_of_fits fs h.1.1
  | .compatibleUnion _ fs, h => by
    simp only [fitsNative, Bool.and_eq_true] at h
    simp only [Plan.paired, Bool.and_eq_true]
    exact ⟨h.1.2, pairedAll_of_fits fs h.1.1.1⟩

/-- Types that fit the native check pair each union's selectors with its options. -/
theorem pairedAll_of_fits : ∀ ds : List Desc, allFitNative ds = true → Plan.pairedAll ds = true
  | [], _ => rfl
  | d :: rest, h => by
    simp only [allFitNative, Bool.and_eq_true] at h
    simp [Plan.pairedAll, paired_of_fits d h.1, pairedAll_of_fits rest h.2]

end

/-- Two types named as a plan names them, and fitting the native check, are equal exactly when their words are. -/
theorem eq_of_words {a b : Desc} (na : named a = true) (nb : named b = true) (fa : fitsNative a = true)
    (fb : fitsNative b = true) (same : Plan.words a = Plan.words b) : a = b := by
  have ha := Plan.readNode_words a (paired_of_fits a fa) (Plan.words a).length [] (Nat.le_refl _)
  have hb := Plan.readNode_words b (paired_of_fits b fb) (Plan.words b).length [] (Nat.le_refl _)
  -- Reading the same words back gives the same type, which is each type renamed, which is each type.
  rw [← same, ha] at hb
  simp only [Option.some.injEq, Prod.mk.injEq, and_true] at hb
  rw [← rename_of_named a na, ← rename_of_named b nb, hb]

/-! What legal structs declare. -/

/-- Field lists compatible pair by pair are as long as each other. -/
theorem fieldsCompatible_length {budget : Nat} : ∀ l r : List Desc, fieldsCompatible budget l r = true →
    l.length = r.length
  | [], [], _ => rfl
  | _ :: l, _ :: r, h => by
    simp only [fieldsCompatible, Bool.and_eq_true] at h
    simp [fieldsCompatible_length l r h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [fieldsCompatible] at h

/-! Every word of a legal type's plan fits a word. -/

/-- Every word of a list of plans is below a bound each plan meets. -/
theorem wordsAll_lt (fs : List Desc) (h : ∀ f ∈ fs, ∀ x ∈ Plan.words f, x < 2 ^ 64) :
    ∀ x ∈ Plan.wordsAll fs, x < 2 ^ 64 := by
  induction fs with
  | nil => simp [Plan.wordsAll]
  | cons f fs ih =>
    intro x hx
    simp only [Plan.wordsAll, List.mem_append] at hx
    rcases hx with hx | hx
    · exact h f (by simp) x hx
    · exact ih (fun g hg => h g (by simp [hg])) x hx

/-- Every word of a legal type's plan that fits the native check fits a word. -/
theorem words_lt (d : Desc) : d.wellFormed = .ok () → fitsNative d = true → ∀ x ∈ Plan.words d, x < 2 ^ 64 := by
  induction d using Desc.rec
    (motive_2 := fun fs => ∀ f ∈ fs, f.wellFormed = .ok () → fitsNative f = true → ∀ x ∈ Plan.words f, x < 2 ^ 64)
  with
  | nil => rename_i h _ _ _ _; simp at h
  | cons f fs ihf ihfs =>
    rename_i g h wg fg x hx
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ihf wg fg x hx
    · exact ihfs g h wg fg x hx
  | bool => intro _ _ x hx; simp [Plan.words] at hx; omega
  | uint _ | byteVector _ | byteList _ | bitVector _ | bitList _ =>
    intro _ fit x hx; simp [Plan.words] at hx; simp [fitsNative] at fit; omega
  | progressiveBitList l =>
    intro _ fit x hx
    cases l with
    | none => simp [Plan.words, Plan.bound] at hx; omega
    | some v => simp [Plan.words, Plan.bound] at hx; simp [fitsNative] at fit; omega
  | vector e n ih | list e n ih =>
    intro wf fit x hx
    simp [Plan.words] at hx
    simp [fitsNative] at fit
    simp [Desc.wellFormed, ite_ok, throw_ok, bind_unit_ok] at wf
    rcases hx with hx | hx | hx
    · omega
    · first | omega | (have := fit.1.2; omega) | (have := fit.2; omega)
    · first | exact ih (wf.2 wf.1) fit.1.1 x hx | exact ih wf fit.1 x hx
  | progressiveList e l ih =>
    intro wf fit x hx
    simp [Plan.words] at hx
    simp only [fitsNative, Bool.and_eq_true] at fit
    simp [Desc.wellFormed] at wf
    rcases hx with hx | hx | hx
    · omega
    · cases l with
      | none => simp [Plan.bound] at hx; omega
      | some v => simp [Plan.bound] at hx fit; omega
    · exact ih wf fit.1 x hx
  | container names fs ih =>
    intro wf fit x hx
    simp [Plan.words] at hx
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
    simp [Desc.wellFormed, ite_ok, throw_ok, bind_unit_ok] at wf
    have wfs : Desc.allWellFormed fs = .ok () := (wf.2 wf.1).1 (wf.2 wf.1).2 |>.2 ((wf.2 wf.1).1 (wf.2 wf.1).2).1
    rcases hx with hx | hx | hx
    · omega
    · omega
    · exact wordsAll_lt fs (fun f hf => ih f hf (allWellFormed_mem fs wfs f hf) (allFitNative_mem fs fit.1.1 f hf))
        x hx
  | progressiveContainer active names fs ih =>
    intro wf fit x hx
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq] at fit
    simp [Desc.wellFormed, ite_ok, throw_ok, bind_unit_ok, maxActiveFields] at wf
    obtain ⟨ane, wf⟩ := wf
    obtain ⟨last, wf⟩ := wf ane
    obtain ⟨a256, wf⟩ := wf last
    obtain ⟨fne, wf⟩ := wf a256
    obtain ⟨wf, cnt⟩ := wf fne
    obtain ⟨wf, nlen⟩ := wf cnt
    have wfs : Desc.allWellFormed fs = .ok () := (wf nlen).2 (wf nlen).1
    simp [Plan.words] at hx
    rcases hx with hx | hx | hx | hx | hx
    · omega
    · omega
    · rcases hx with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
    · omega
    · exact wordsAll_lt fs (fun f hf => ih f hf (allWellFormed_mem fs wfs f hf) (allFitNative_mem fs fit.1.1 f hf))
        x hx
  | compatibleUnion sels opts ih =>
    intro wf fit x hx
    obtain ⟨sne, lens, dup, rng, wfs, comp⟩ := wf_union sels opts wf
    simp only [fitsNative, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at fit
    simp [Plan.words] at hx
    rcases hx with hx | hx | hx | hx
    · omega
    · omega
    · exact fit.2 x hx
    · exact wordsAll_lt opts (fun f hf => ih f hf (allWellFormed_mem opts wfs f hf)
        (allFitNative_mem opts fit.1.1.1 f hf)) x hx

/-! Compatibility at any budget past the left type's nesting. -/

/-- A union's options are compatible two by two when the first fits every later one and the later ones are. -/
theorem optionsCompatible_cons (sels : List Nat) (o : Desc) (rest : List Desc) :
    Desc.optionsCompatible sels (o :: rest) = .ok () ↔
      (∀ slot < rest.length, isCompatible o rest[slot]! = true) ∧
        Desc.optionsCompatible (sels.drop 1) rest = .ok () := by
  simp only [Desc.optionsCompatible]
  split
  · rename_i slot found
    have bad := List.find?_some found
    have inside := List.mem_range.mp (List.mem_of_find?_eq_some found)
    simp only [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, reduceCtorEq, false_iff, not_and]
    intro all
    -- The slot found is one the first option does not fit.
    have good := all slot inside
    simp only [Bool.not_eq_true', good] at bad
    cases bad
  · rename_i none_
    have all := List.find?_eq_none.mp none_
    constructor
    · intro h
      exact ⟨fun slot hs => by simpa using all slot (List.mem_range.mpr hs), h⟩
    · exact fun h => h.2

/-- Whether every option of a union is compatible, at its own nesting, with every later one. -/
def allPairs : List Desc → Bool
  | [] => true
  | o :: rest => rest.all (compatibleAt o.nesting o) && allPairs rest

/-- A union's options are compatible two by two exactly when each is with every later one, at its own nesting. -/
theorem optionsCompatible_iff : ∀ (sels : List Nat) (opts : List Desc),
    Desc.optionsCompatible sels opts = .ok () ↔ allPairs opts = true
  | _, [] => by simp [Desc.optionsCompatible, allPairs]
  | sels, o :: rest => by
    rw [optionsCompatible_cons, optionsCompatible_iff, allPairs, Bool.and_eq_true, List.all_eq_true]
    -- The budget of the sum of two nestings answers as the first nesting does.
    have same : ∀ x, isCompatible o x = compatibleAt o.nesting o x := fun x =>
      compatibleAt_stable _ _ _ _ (by omega) (Nat.le_refl _)
    constructor
    · rintro ⟨all, tail⟩
      refine ⟨fun x hx => ?_, tail⟩
      obtain ⟨slot, hs, rfl⟩ := List.getElem_of_mem hx
      have := all slot hs
      rwa [getElem!_pos rest slot hs, same] at this
    · rintro ⟨all, tail⟩
      refine ⟨fun slot hs => ?_, tail⟩
      rw [getElem!_pos rest slot hs, same]
      exact all _ (List.getElem_mem hs)

/-! Byte-array spellings, as the native check codes them. -/

/-- The code of a type's byte-array spelling: zero for none, one for a fixed count, two for a bounded count. -/
def byteCode (d : Desc) : Nat :=
  match d.byteSequence with
  | none => 0
  | some (.asVector _) => 1
  | some (.asList _) => 2

/-- The size a byte-array spelling declares. -/
def shapeSize : ByteShape → Nat
  | .asVector n | .asList n => n

/-- A type spelling a byte array keeps its size in its second word. -/
theorem words_one_of_byteSequence {d : Desc} {s : ByteShape} (h : d.byteSequence = some s) :
    (Plan.words d)[1]? = some (shapeSize s) := by
  cases d with
  | byteVector n | byteList n => simp [Desc.byteSequence] at h; subst h; simp [Plan.words, shapeSize]
  | vector e n | list e n =>
    cases e with
    | uint w =>
      by_cases one : w = 1
      · subst one; simp [Desc.byteSequence] at h; subst h; simp [Plan.words, shapeSize]
      · simp [Desc.byteSequence, one] at h
    | _ => simp [Desc.byteSequence] at h
  | _ => simp [Desc.byteSequence] at h

/-- Two spellings, one of them a byte array, agree exactly when their codes and second words do. -/
theorem byteSequence_beq {a b : Desc} (some_ : byteCode a ≠ 0 ∨ byteCode b ≠ 0) :
    (a.byteSequence == b.byteSequence) =
      (byteCode a == byteCode b && (Plan.words a)[1]? == (Plan.words b)[1]?) := by
  unfold byteCode at some_ ⊢
  cases ha : a.byteSequence with
  | none =>
    cases hb : b.byteSequence with
    | none => simp [ha, hb] at some_
    | some t => cases t <;> simp
  | some s =>
    have wa := words_one_of_byteSequence ha
    cases hb : b.byteSequence with
    | none => cases s <;> simp
    | some t =>
      have wb := words_one_of_byteSequence hb
      rw [wa, wb]
      cases s <;> cases t <;> simp only [shapeSize] <;> (apply Bool.eq_iff_iff.mpr; simp)

/-! Layouts named by position. -/

/-- The set bits of a layout before a position. -/
def setBefore (active : List Bool) (k : Nat) : Nat :=
  (active.take k).countP (· == true)

/-- A layout's positions, its first bit apart from the rest. -/
theorem layoutPositions_cons (b : Bool) (rest : List Bool) :
    Plan.layoutPositions (b :: rest) = (if b then [0] else []) ++ (Plan.layoutPositions rest).map (· + 1) := by
  simp only [Plan.layoutPositions, List.zipIdx_cons, List.zipIdx_succ]
  cases b <;> simp [List.map_filterMap, Function.comp_def] <;> (congr 1; funext x; split <;> simp)

/-- The k-th position a layout sets is a set position with k set bits before it. -/
theorem layoutPositions_getElem? : ∀ (active : List Bool) (o k : Nat),
    (Plan.layoutPositions active)[o]? = some k ↔ active[k]? = some true ∧ setBefore active k = o
  | [], o, k => by simp [Plan.layoutPositions]
  | b :: rest, o, k => by
    have ih := layoutPositions_getElem? rest
    rw [layoutPositions_cons]
    cases b <;> cases o <;> cases k <;> simp [setBefore, ih, List.take_succ_cons] at * <;> omega

/-- An entry of a layout named by position: a set position, its name, and the set bits before it. -/
theorem mem_placedOrdinals_named (active : List Bool) (x : Nat × String × Nat) :
    x ∈ placedOrdinals active (Plan.layoutNames active) ↔
      active[x.1]? = some true ∧ x.2.1 = toString x.1 ∧ x.2.2 = setBefore active x.1 := by
  rcases x with ⟨p, n, o⟩
  simp only [placedOrdinals, List.mem_map, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨⟨p', n'⟩, o'⟩, h, e⟩
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    have h' := List.getElem?_zip_eq_some.mp h
    simp only [Plan.layoutNames, List.getElem?_map] at h'
    obtain ⟨hp, hn⟩ := h'
    have hp : (Plan.layoutPositions active)[o']? = some p' := hp
    rw [hp] at hn
    have := (layoutPositions_getElem? active o' p').mp hp
    simp only [Option.map_some, Option.some.injEq] at hn
    exact ⟨this.1, hn.symm, this.2.symm⟩
  · rintro ⟨hb, rfl, rfl⟩
    have hp := (layoutPositions_getElem? active (setBefore active p) p).mpr ⟨hb, rfl⟩
    refine ⟨((p, toString p), setBefore active p), List.getElem?_zip_eq_some.mpr ⟨hp, ?_⟩, rfl⟩
    simp [Plan.layoutNames, List.getElem?_map, hp]

/-- What two layouts named by position check at a position both set: compatible fields there. -/
def sharedAgree (budget : Nat) (la lb : List Bool) (fa fb : List Desc) (k : Nat) : Bool :=
  match fa[setBefore la k]?, fb[setBefore lb k]? with
  | some f, some g => compatibleAt budget f g
  | _, _ => false

/-- Two layouts named by position agree exactly when every position both set holds compatible fields. -/
theorem layoutsAgree_named (budget : Nat) (la lb : List Bool) (fa fb : List Desc) :
    layoutsAgree budget la (Plan.layoutNames la) fa lb (Plan.layoutNames lb) fb = true ↔
      ∀ k, la[k]? = some true → lb[k]? = some true → sharedAgree budget la lb fa fb k = true := by
  rw [layoutsAgree.eq_def]
  simp only [List.all_eq_true]
  constructor
  · intro all k ha hb
    have pair := all (k, toString k, setBefore la k) ((mem_placedOrdinals_named la _).mpr ⟨ha, rfl, rfl⟩)
      (k, toString k, setBefore lb k) ((mem_placedOrdinals_named lb _).mpr ⟨hb, rfl, rfl⟩)
    rw [layoutPairAgree.eq_def] at pair
    simp only [beq_self_eq_true, if_true, Bool.true_and] at pair
    unfold sharedAgree
    revert pair
    cases fa[setBefore la k]? <;> cases fb[setBefore lb k]? <;> simp
  · rintro all ⟨p, n, o⟩ hx ⟨p', n', o'⟩ hy
    obtain ⟨ha, hn, ho⟩ := (mem_placedOrdinals_named la _).mp hx
    obtain ⟨hb, hn', ho'⟩ := (mem_placedOrdinals_named lb _).mp hy
    simp only at ha hb hn ho hn' ho'
    subst hn ho hn' ho'
    rw [layoutPairAgree.eq_def]
    by_cases same : p = p'
    · subst same
      have := all p ha hb
      unfold sharedAgree at this
      revert this
      simp only [beq_self_eq_true, if_true, Bool.true_and]
      cases fa[setBefore la p]? <;> cases fb[setBefore lb p]? <;> simp
    · -- Two positions are named by two different numbers.
      simp only [beq_iff_eq, same, if_false, bne_iff_ne, ne_eq]
      exact fun e => same (Nat.repr_inj.mp e)

end Ssz.Native.Driver.Validate
