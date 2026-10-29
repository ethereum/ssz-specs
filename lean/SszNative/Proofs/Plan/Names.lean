import SszNative.Proofs.Plan.RoundTrip
import SszNative.Proofs.Driver.Validate.Compat
import Std.Data.String.ToNat
import Ssz.Proofs.Type.Equality

/-!
What naming fields by position keeps.

A plan read back names a struct's fields by ordinal and a progressive container's by layout position.
The native check judges that renamed type, and the words never change.
Names stay unique, and inside a union two progressive containers name a shared position alike, so every legal type
stays legal renamed.
-/

namespace Ssz.Native.Plan

open Ssz Ssz.Native.Driver.Validate

mutual

/-- Renaming a type leaves its words alone. -/
theorem words_rename : ∀ d : Desc, words (rename d) = words d
  | .bool | .uint _ | .byteVector _ | .byteList _ | .bitVector _ | .bitList _ | .progressiveBitList _ => by
    simp [rename]
  | .vector e _ | .list e _ | .progressiveList e _ => by simp [rename, words, words_rename e]
  | .container _ fs | .progressiveContainer _ _ fs | .compatibleUnion _ fs => by
    simp [rename, words, wordsAll_rename fs, length_renameAll fs]

/-- Renaming types leaves their words alone. -/
theorem wordsAll_rename : ∀ ds : List Desc, wordsAll (renameAll ds) = wordsAll ds
  | [] => rfl
  | d :: rest => by simp [renameAll, wordsAll, words_rename d, wordsAll_rename rest]

/-- Renaming types keeps their count. -/
theorem length_renameAll : ∀ ds : List Desc, (renameAll ds).length = ds.length
  | [] => rfl
  | _ :: rest => by simp [renameAll, length_renameAll rest]

end

mutual

/-- A renamed type names its fields by position, as the native check asks. -/
theorem named_rename : ∀ d : Desc, named (rename d) = true
  | .bool | .uint _ | .byteVector _ | .byteList _ | .bitVector _ | .bitList _ | .progressiveBitList _ => by
    simp [rename, named]
  | .vector e _ | .list e _ | .progressiveList e _ => by simp [rename, named, named_rename e]
  | .container _ fs | .progressiveContainer _ _ fs | .compatibleUnion _ fs => by
    simp [rename, named, namedAll_rename fs, length_renameAll fs]

/-- Renamed types name their fields by position. -/
theorem namedAll_rename : ∀ ds : List Desc, namedAll (renameAll ds) = true
  | [] => rfl
  | d :: rest => by simp [renameAll, namedAll, named_rename d, namedAll_rename rest]

end

/-- Names by position are all different. -/
theorem positionNames_nodup (n : Nat) : (positionNames n).Nodup := by
  -- Two numbers written in decimal are the same text only when they are the same number.
  exact List.Pairwise.map _ (fun a b differ same => differ (Nat.repr_inj.mp same)) List.nodup_range

/-- Renaming types renames each one. -/
theorem renameAll_eq_map : ∀ ds : List Desc, renameAll ds = ds.map rename
  | [] => rfl
  | d :: rest => by simp [renameAll, renameAll_eq_map rest]

mutual

/-- Renaming a type keeps its nesting. -/
theorem nesting_rename : ∀ d : Desc, (rename d).nesting = d.nesting
  | .bool | .uint _ | .byteVector _ | .byteList _ | .bitVector _ | .bitList _ | .progressiveBitList _ => by
    simp [rename]
  | .vector e _ | .list e _ | .progressiveList e _ => by simp [rename, Desc.nesting, nesting_rename e]
  | .container _ fs | .progressiveContainer _ _ fs | .compatibleUnion _ fs => by
    simp [rename, Desc.nesting, deepestNesting_renameAll fs]

/-- Renaming types keeps their deepest nesting. -/
theorem deepestNesting_renameAll : ∀ ds : List Desc, Desc.deepestNesting (renameAll ds) = Desc.deepestNesting ds
  | [] => rfl
  | d :: rest => by simp [renameAll, Desc.deepestNesting, nesting_rename d, deepestNesting_renameAll rest]

end

/-- Renaming a type keeps the byte array it spells, if any. -/
theorem byteSequence_rename (d : Desc) : (rename d).byteSequence = d.byteSequence := by
  cases d with
  | vector e n | list e n => cases e <;> simp [rename, Desc.byteSequence]
  | _ => simp [rename, Desc.byteSequence]

/-- The positions a layout sets, counted from an offset: one per set bit, increasing, none below the offset. -/
theorem positions_from (active : List Bool) : ∀ k,
    (active.zipIdx k |>.filterMap fun (present, position) => if present then some position else none).length =
      active.countP (· == true) ∧
    (active.zipIdx k |>.filterMap fun (present, position) => if present then some position else none).Pairwise
      (· < ·) ∧
    ∀ x ∈ (active.zipIdx k |>.filterMap fun (present, position) => if present then some position else none), k ≤ x := by
  induction active with
  | nil => intro k; simp
  | cons b rest ih =>
    intro k
    obtain ⟨l, s, g⟩ := ih (k + 1)
    -- A set bit puts its position first, below every later one.
    cases b
    · simp only [List.zipIdx_cons]
      simp [l, s]
      intro x hx; have := g x (by simpa using hx); omega
    · simp only [List.zipIdx_cons]
      simp [l, s]
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · have := g x (by simpa using hx); omega
      · have := g x (by simpa using hx); omega

/-- A layout sets as many positions as it has set bits. -/
theorem length_layoutPositions (active : List Bool) :
    (layoutPositions active).length = active.countP (· == true) :=
  (positions_from active 0).1

/-- Names by layout position are all different. -/
theorem layoutNames_nodup (active : List Bool) : (layoutNames active).Nodup := by
  -- Positions increase, and two numbers written in decimal are the same text only when they are the same number.
  exact List.Pairwise.map _ (fun a b differ same => differ (Nat.repr_inj.mp same))
    ((positions_from active 0).2.1.imp Nat.ne_of_lt)

/-- An entry of a layout's placed fields: the position, the name and the ordinal agree on one index. -/
theorem mem_placedOrdinals (active : List Bool) (names : List String) (x : Nat × String × Nat) :
    x ∈ placedOrdinals active names ↔
      (layoutPositions active)[x.2.2]? = some x.1 ∧ names[x.2.2]? = some x.2.1 := by
  rcases x with ⟨p, n, o⟩
  simp only [placedOrdinals, List.mem_map, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨⟨p', n'⟩, o'⟩, h, e⟩
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact List.getElem?_zip_eq_some.mp h
  · intro h
    exact ⟨((p, n), o), List.getElem?_zip_eq_some.mpr h, rfl⟩

/-- What renaming keeps of compatibility at one budget, for legal types. -/
def RenameKeeps (budget : Nat) : Prop :=
  ∀ a b : Desc, a.wellFormed = .ok () → b.wellFormed = .ok () → compatibleAt budget a b = true →
    compatibleAt budget (rename a) (rename b) = true

/-- Field lists compatible pair by pair stay so renamed. -/
theorem fieldsCompatible_rename {budget : Nat} (inner : RenameKeeps budget) : ∀ l r : List Desc,
    Desc.allWellFormed l = .ok () → Desc.allWellFormed r = .ok () → fieldsCompatible budget l r = true →
      fieldsCompatible budget (renameAll l) (renameAll r) = true
  | [], [], _, _, _ => by simp [renameAll, fieldsCompatible]
  | x :: l, y :: r, wl, wr, h => by
    rw [Desc.allWellFormed, bind_unit_ok] at wl wr
    simp only [fieldsCompatible, Bool.and_eq_true] at h
    simp only [renameAll, fieldsCompatible, Bool.and_eq_true]
    exact ⟨inner x y wl.1 wr.1 h.1, fieldsCompatible_rename inner l r wl.2 wr.2 h.2⟩
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp [fieldsCompatible] at h

/-- Union options agreeing stay so renamed. -/
theorem unionOptionsAgree_rename {budget : Nat} (inner : RenameKeeps budget) (l r : List Desc)
    (wl : Desc.allWellFormed l = .ok ()) (wr : Desc.allWellFormed r = .ok ())
    (h : unionOptionsAgree budget l r = true) : unionOptionsAgree budget (renameAll l) (renameAll r) = true := by
  rw [unionOptionsAgree_iff] at h ⊢
  simp only [renameAll_eq_map, List.mem_map]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact inner x y (allWellFormed_mem l wl x hx) (allWellFormed_mem r wr y hy) (h x hx y hy)

/-- A renamed layout's entry: its name is its position written out, and the original layout has an entry there. -/
theorem placed_renamed (active : List Bool) (names : List String) (x : Nat × String × Nat)
    (enough : (layoutPositions active).length ≤ names.length) (hx : x ∈ placedOrdinals active (layoutNames active)) :
    x.2.1 = toString x.1 ∧ ∃ name, (x.1, name, x.2.2) ∈ placedOrdinals active names := by
  rw [mem_placedOrdinals] at hx
  obtain ⟨hp, hn⟩ := hx
  have lt := (List.getElem?_eq_some_iff.mp hp).1
  simp only [layoutNames, List.getElem?_map, hp, Option.map_some, Option.some.injEq] at hn
  refine ⟨hn.symm, names[x.2.2]'(by omega), (mem_placedOrdinals _ _ _).mpr ⟨hp, ?_⟩⟩
  simp [List.getElem?_eq_getElem (show x.2.2 < names.length by omega)]

/-- Two layouts agreeing stay so renamed: names by position match exactly where positions do. -/
theorem layoutsAgree_rename {budget : Nat} (inner : RenameKeeps budget) (la lb : List Bool) (na nb : List String)
    (fa fb : List Desc) (wa : Desc.allWellFormed fa = .ok ()) (wb : Desc.allWellFormed fb = .ok ())
    (ea : (layoutPositions la).length ≤ na.length) (eb : (layoutPositions lb).length ≤ nb.length)
    (h : layoutsAgree budget la na fa lb nb fb = true) :
    layoutsAgree budget la (layoutNames la) (renameAll fa) lb (layoutNames lb) (renameAll fb) = true := by
  rw [layoutsAgree.eq_def] at h ⊢
  simp only [List.all_eq_true] at h ⊢
  intro x hx y hy
  obtain ⟨xn, m, hm⟩ := placed_renamed la na x ea hx
  obtain ⟨yn, m', hm'⟩ := placed_renamed lb nb y eb hy
  have orig := h _ hm _ hm'
  rw [layoutPairAgree.eq_def] at orig ⊢
  rcases x with ⟨p, n, o⟩
  rcases y with ⟨p', n', o'⟩
  dsimp only at xn yn orig ⊢
  subst xn yn
  by_cases same : p = p'
  · subst same
    simp only [beq_self_eq_true, if_true, Bool.true_and, Bool.and_eq_true] at orig ⊢
    simp only [renameAll_eq_map, List.getElem?_map]
    -- The original fields at the shared position are compatible, so their renamings are.
    cases ga : fa[o]? <;> cases gb : fb[o']? <;> simp only [ga, gb] at orig ⊢ <;> try (simp at orig; done)
    exact inner _ _ (allWellFormed_mem fa wa _ (List.mem_of_getElem? ga))
      (allWellFormed_mem fb wb _ (List.mem_of_getElem? gb)) orig.2
  · -- Two positions are named by two different numbers.
    simp only [beq_iff_eq, same, if_false, bne_iff_ne, ne_eq]
    exact fun e => same (Nat.repr_inj.mp e)

/-- A legal progressive container has a name for every position its layout sets. -/
theorem names_enough {active : List Bool} {names : List String} {fs : List Desc}
    (h : (Desc.progressiveContainer active names fs).wellFormed = .ok ()) :
    (layoutPositions active).length ≤ names.length := by
  obtain ⟨_, _, _, _, count, len, _⟩ := (wellFormed_progressiveContainer_iff active names fs).mp h
  rw [length_layoutPositions]
  omega

/-- Compatible legal types stay compatible renamed, at every budget. -/
theorem compatibleAt_rename (budget : Nat) : RenameKeeps budget := by
  induction budget with
  | zero => intro a b _ _ h; simp [compatibleAt.eq_def] at h
  | succ budget ih =>
    intro a b wa wb h
    by_cases same : rename a = rename b
    · rw [same]; exact compatibleAt_self budget _
    have orig : a ≠ b := fun e => same (by rw [e])
    rw [compatibleAt.eq_def] at h ⊢
    simp only [show (a == b) = false by simp [orig], show (rename a == rename b) = false by simp [same],
      Bool.false_eq_true, if_false, byteSequence_rename] at h ⊢
    -- A byte-array spelling compares the same way renamed, since renaming keeps it.
    cases ha : a.byteSequence <;> cases hb : b.byteSequence <;> simp only [ha, hb] at h ⊢ <;> try exact h
    cases a <;> cases b <;> simp only [rename, Bool.false_eq_true] at h ⊢ <;> try exact h
    case vector.vector e n e' n' =>
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨h.1, ih _ _ (wellFormed_vector_element wa) (wellFormed_vector_element wb) h.2⟩
    case list.list e n e' n' =>
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨h.1, ih _ _ (by simpa [Desc.wellFormed] using wa) (by simpa [Desc.wellFormed] using wb) h.2⟩
    case progressiveList.progressiveList =>
      exact ih _ _ (by simpa [Desc.wellFormed] using wa) (by simpa [Desc.wellFormed] using wb) h
    case container.container names fs names' fs' =>
      simp only [Bool.and_eq_true] at h ⊢
      -- Names by ordinal match whenever the field counts do.
      refine ⟨by simp [fieldsCompatible_length fs fs' h.2], fieldsCompatible_rename ih fs fs'
        ((wellFormed_container_iff names fs).mp wa).2.2.2 ((wellFormed_container_iff names' fs').mp wb).2.2.2 h.2⟩
    case progressiveContainer.progressiveContainer la na fa lb nb fb =>
      exact layoutsAgree_rename ih la lb na nb fa fb ((wellFormed_progressiveContainer_iff la na fa).mp wa).2.2.2.2.2.2.2
        ((wellFormed_progressiveContainer_iff lb nb fb).mp wb).2.2.2.2.2.2.2 (names_enough wa) (names_enough wb) h
    case compatibleUnion.compatibleUnion sa oa sb ob =>
      exact unionOptionsAgree_rename ih oa ob ((wellFormed_compatibleUnion_iff sa oa).mp wa).2.2.2.2.2.1
        ((wellFormed_compatibleUnion_iff sb ob).mp wb).2.2.2.2.2.1 h

/-- Legal options compatible two by two stay so renamed. -/
theorem optionsCompatible_rename : ∀ (sels : List Nat) (opts : List Desc), Desc.allWellFormed opts = .ok () →
    Desc.optionsCompatible sels opts = .ok () → Desc.optionsCompatible sels (renameAll opts) = .ok ()
  | _, [], _, _ => rfl
  | sels, o :: rest, w, h => by
    rw [optionsCompatible_cons] at h
    rw [renameAll, optionsCompatible_cons]
    have wr : Desc.allWellFormed rest = .ok () := ((bind_unit_ok _ _).mp w).2
    refine ⟨fun slot hs => ?_, optionsCompatible_rename _ rest wr h.2⟩
    rw [length_renameAll] at hs
    have c := h.1 slot hs
    rw [renameAll_eq_map, getElem!_pos (rest.map rename) slot (by simpa using hs), List.getElem_map]
    rw [getElem!_pos rest slot hs] at c
    -- Renaming keeps nesting, so the budget is the same.
    simp only [isCompatible, nesting_rename] at c ⊢
    exact compatibleAt_rename _ _ _ ((bind_unit_ok _ _).mp w).1
      (allWellFormed_mem rest wr _ (List.getElem_mem hs)) c

mutual

/-- A legal type stays legal with its fields named by position: by ordinal in a struct, by layout position in a
progressive container. -/
theorem wellFormed_rename : ∀ d : Desc, d.wellFormed = .ok () → (rename d).wellFormed = .ok ()
  | .bool, h | .uint _, h | .byteVector _, h | .byteList _, h | .bitVector _, h
  | .bitList _, h | .progressiveBitList _, h => by simpa [rename] using h
  | .vector e n, h => by
    have inner := wellFormed_rename e (wellFormed_vector_element h)
    by_cases z : n = 0
    · simp [Desc.wellFormed, z, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at h
    · simpa [rename, Desc.wellFormed, z] using inner
  | .list e _, h | .progressiveList e _, h => by
    simp only [Desc.wellFormed] at h
    simpa [rename, Desc.wellFormed] using wellFormed_rename e h
  | .container names fs, h => by
    obtain ⟨empty, _, _, sound⟩ := (wellFormed_container_iff names fs).mp h
    -- The new names are as many as the fields, and all different.
    refine (wellFormed_container_iff _ _).mpr ⟨?_, by simp [positionNames, length_renameAll],
      firstDuplicate_of_nodup _ (positionNames_nodup _), allWellFormed_rename fs sound⟩
    cases fs <;> simp_all [renameAll]
  | .progressiveContainer active names fs, h => by
    obtain ⟨empty, gap, wide, none_, count, _, _, sound⟩ := (wellFormed_progressiveContainer_iff active names fs).mp h
    -- One name per set position, all different.
    refine (wellFormed_progressiveContainer_iff _ _ _).mpr ⟨empty, gap, wide, ?_, by rw [length_renameAll]; exact count,
      by simp [layoutNames, length_layoutPositions, length_renameAll]; simpa using count,
      firstDuplicate_of_nodup _ (layoutNames_nodup _), allWellFormed_rename fs sound⟩
    cases fs <;> simp_all [renameAll]
  | .compatibleUnion sels opts, h => by
    obtain ⟨sne, one, len, dup, range, sound, comp⟩ := (wellFormed_compatibleUnion_iff sels opts).mp h
    -- Selectors stay as they are; the options stay legal and compatible.
    refine (wellFormed_compatibleUnion_iff _ _).mpr ⟨sne, ?_, by rw [length_renameAll]; exact len, dup, range,
      allWellFormed_rename opts sound, optionsCompatible_rename sels opts sound comp⟩
    cases opts <;> simp_all [renameAll]

/-- Legal types stay legal renamed. -/
theorem allWellFormed_rename : ∀ ds : List Desc, Desc.allWellFormed ds = .ok () →
    Desc.allWellFormed (renameAll ds) = .ok ()
  | [], _ => rfl
  | d :: rest, h => by
    rw [Desc.allWellFormed, bind_unit_ok] at h
    rw [renameAll, Desc.allWellFormed, bind_unit_ok]
    exact ⟨wellFormed_rename d h.1, allWellFormed_rename rest h.2⟩

end

/--
A legal union that naming by ordinal would make illegal stays legal.

Its first option sets three positions and its second only the last, under one name in both.
By ordinal that shared position would be named two in one option and zero in the other; by position it is two in both.
-/
theorem wellFormed_rename_union :
    (rename (.compatibleUnion [1, 2]
      [.progressiveContainer [true, true, true] ["a", "b", "c"] [.bool, .bool, .bool],
        .progressiveContainer [false, false, true] ["c"] [.bool]])).wellFormed = .ok () :=
  wellFormed_rename _ (by
    simp (config := {decide := true}) [Desc.wellFormed, Desc.allWellFormed, Desc.optionsCompatible, isCompatible,
      compatibleAt, layoutsAgree, layoutPairAgree, placedOrdinals, placedFields, firstDuplicate, Desc.nesting,
      Desc.deepestNesting, Desc.byteSequence, Bind.bind, Except.bind])

end Ssz.Native.Plan
