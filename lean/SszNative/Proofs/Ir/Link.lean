import SszNative.Ir.Link
import SszNative.Proofs.Ir.Leaf

/-!
Linking compiled functions and routines into one image, checked once, places every function where calls find it.
-/

namespace Ssz.Native.Ir

open Ssz.Native.Asm

/-- In a list whose names are distinct, the first entry under an entry's name is that entry. -/
theorem findIdx_of_nodup {α : Type} (l : List (String × α)) (nodup : (l.map (·.1)).Nodup) (i : Nat)
    (hi : i < l.length) : l.findIdx? (·.1 == l[i].1) = some i := by
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hi, by simp, fun j hj => ?_⟩
  -- An earlier entry carries a different name.
  have := List.pairwise_iff_getElem.mp nodup j i (by simp; omega) (by simpa using hi) hj
  simpa using this

/-- A name found in a list of pairs sits at some position, paired with what was found. -/
theorem lookup_getElem {α : Type} : ∀ (l : List (String × α)) (name : String) (a : α), l.lookup name = some a →
    ∃ i, ∃ h : i < l.length, l[i] = (name, a)
  | [], _, _, found => by simp at found
  | (k, b) :: rest, name, a, found => by
    by_cases same : name = k
    · -- The head matches.
      subst same
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at found
      exact ⟨0, by simp, by simp [found]⟩
    · -- The name is further on.
      have miss : (name == k) = false := by simpa using same
      simp only [List.lookup, miss] at found
      obtain ⟨i, h, hi⟩ := lookup_getElem rest name a found
      exact ⟨i + 1, by simp; omega, by simpa using hi⟩

/-- The routines of a linked image, as a list. -/
theorem link_toList (fns : List (String × Fn)) (externs : Image) :
    (Module.link fns externs).toList = fns.map (fun p => (p.1, compileFn p.2)) ++ externs.toList := by
  simp [Module.link]

/-- A linked image holds the functions and the outside routines. -/
theorem link_size (fns : List (String × Fn)) (externs : Image) :
    (Module.link fns externs).size = fns.length + externs.size := by
  simp [Module.link]

/-- In a checked image, each routine's name finds that routine. -/
theorem link_find (fns : List (String × Fn)) (externs : Image) (check : linkCheck fns externs = true) (i : Nat)
    (hi : i < (Module.link fns externs).size) :
    (Module.link fns externs).find (Module.link fns externs)[i].1 = some i := by
  simp only [linkCheck, Bool.and_eq_true, decide_eq_true_eq] at check
  have nodup := check.1.1
  -- The image is a list underneath.
  generalize Module.link fns externs = a at hi nodup ⊢
  rcases a with ⟨l⟩
  simp only [Image.find, List.findIdx?_toArray]
  simpa using findIdx_of_nodup l (by simpa using nodup) i (by simpa using hi)

/-- The code of a routine inside an image is its instructions. -/
theorem code_of_lt (image : Image) (i : Nat) (hi : i < image.size) : image.code i = image[i].2 := by
  simp [Image.code, hi]

/-- A checked image places every function of the module, whatever its outside routines. -/
theorem placed_of_linkCheck (fns : List (String × Fn)) (externs : Image) (ext : List (String × Extern))
    (check : linkCheck fns externs = true) : Placed ⟨fns, ext⟩ (Module.link fns externs) := by
  intro name f found
  obtain ⟨i, hi, at_i⟩ := lookup_getElem fns name f found
  have checked := check
  simp only [linkCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at checked
  obtain ⟨⟨_, each⟩, small⟩ := checked
  -- The function's own checks.
  have own := each fns[i] (List.getElem_mem hi)
  rw [at_i] at own
  have iIn : i < (Module.link fns externs).size := by rw [link_size]; omega
  -- The routine at the function's position.
  have entry : (Module.link fns externs)[i] = (name, compileFn f) := by
    simp only [Module.link, List.getElem_toArray]
    rw [List.getElem_append_left (by simpa using hi)]
    simp [at_i]
  refine ⟨i, ?_, ?_, iIn, by omega, own.2, own.1⟩
  · have := link_find fns externs check i iIn
    rwa [entry] at this
  · rw [code_of_lt _ _ iIn, entry]

/-- In a checked image, each outside routine sits after the functions, and its name finds it there. -/
theorem extern_found (fns : List (String × Fn)) (externs : Image) (check : linkCheck fns externs = true) (j : Nat)
    (hj : j < externs.size) :
    (Module.link fns externs).find externs[j].1 = some (fns.length + j) ∧
      (Module.link fns externs).code (fns.length + j) = externs[j].2 ∧
      fns.length + j < (Module.link fns externs).size ∧ (Module.link fns externs).size < 2 ^ 31 := by
  have small : (Module.link fns externs).size < 2 ^ 31 := by
    simp only [linkCheck, Bool.and_eq_true, decide_eq_true_eq] at check
    exact check.2
  have jIn : fns.length + j < (Module.link fns externs).size := by rw [link_size]; omega
  -- The routine at the outside routine's position.
  have entry : (Module.link fns externs)[fns.length + j] = externs[j] := by
    simp [Module.link, List.getElem_append_right]
  refine ⟨?_, ?_, jIn, small⟩
  · have := link_find fns externs check (fns.length + j) jIn
    rwa [entry] at this
  · rw [code_of_lt _ _ jIn, entry]

/-- A small module links and checks by evaluation: two functions, one calling the other, and one outside routine. -/
example : linkCheck
    [("one", ⟨0, 0, .skip, .lit 1⟩), ("two", ⟨1, 2, .call "one" [] 1, .op .add (.var 0) (.var 1)⟩)]
    #[("leaf", #[.ret])] = true := by
  decide +kernel

end Ssz.Native.Ir
