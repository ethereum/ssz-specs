import Ssz.Proofs.Codec.JsonLaws
import Ssz.Proofs.Codec.Admits

/-! A JSON document written for a value reads back as that value, at every shape. -/

namespace Ssz

open Lean

/-- Whether the mapping reads back every value of a shape that it writes. -/
def Rewrites (shape : Desc) : Prop :=
  ∀ (spelling : Spelling) (value : Value) (document : Json),
    Fits shape value → jsonOf shape spelling value = .ok document →
    valueOf shape spelling document = .ok value

/-- One byte on the front of a run gives one value on the front of the elements. -/
theorem byteElements_cons (byte : UInt8) (data : Bytes) :
    byteElements (#[byte] ++ data) = .uint byte.toNat :: byteElements data := by
  simp [byteElements]

/-- A run of one-byte values is recovered from the bytes it wrote. -/
theorem byteElements_byteRun : ∀ (values : List Value) (data : Bytes),
    byteRun values = .ok data → byteElements data = values
  | [], data, wrote => by
    simp only [byteRun, Except.ok.injEq] at wrote
    subst wrote
    simp [byteElements]
  | .uint n :: rest, data, wrote => by
    rw [byteRun] at wrote
    by_cases wide : 256 ≤ n
    · simp [wide, Bind.bind, Except.bind] at wrote
    · rw [if_neg wide] at wrote
      cases run : byteRun rest with
      | error _ => simp [run, Bind.bind, Except.bind] at wrote
      | ok tail =>
        simp only [run, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at wrote
        subst wrote
        have byte : (UInt8.ofNat n).toNat = n := by
          simpa [UInt8.toNat_ofNat] using Nat.mod_eq_of_lt (Nat.not_le.mp wide)
        rw [byteElements_cons, byte, byteElements_byteRun rest tail run]
  | .bool _ :: _, _, wrote => by simp [byteRun] at wrote
  | .bytes _ :: _, _, wrote => by simp [byteRun] at wrote
  | .bits _ :: _, _, wrote => by simp [byteRun] at wrote
  | .seq _ :: _, _, wrote => by simp [byteRun] at wrote
  | .union _ _ :: _, _, wrote => by simp [byteRun] at wrote

/-- Each entry of a sequence document reads back as the element it was written from. -/
theorem valueOfEntries_jsonOfEach (element : Desc) (spelling : Spelling)
    (back : ∀ (value : Value) (document : Json), Fits element value →
      jsonOf element spelling value = .ok document →
        valueOf element spelling document = .ok value) :
    ∀ (values : List Value) (documents : List Json),
      (∀ value ∈ values, Fits element value) →
      jsonOfEach element spelling values = .ok documents →
      valueOfEntries element spelling documents = .ok values
  | [], documents, _, wrote => by
    rw [jsonOfEach] at wrote
    simp only [Except.ok.injEq] at wrote
    subst wrote
    rw [valueOfEntries]
  | value :: rest, documents, fitted, wrote => by
    rw [jsonOfEach] at wrote
    cases head : jsonOf element spelling value with
    | error _ => simp [head, Bind.bind, Except.bind] at wrote
    | ok first =>
      cases tail : jsonOfEach element spelling rest with
      | error _ => simp [head, tail, Bind.bind, Except.bind] at wrote
      | ok others =>
        simp only [head, tail, Bind.bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at wrote
        subst wrote
        rw [valueOfEntries, back value first (fitted value (by simp)) head,
          valueOfEntries_jsonOfEach element spelling back rest others
            (fun v member => fitted v (by simp [member])) tail]
        simp [Bind.bind, Except.bind, pure, Except.pure]

/-- Two lists that hold an entry at one position hold their pair there once zipped. -/
theorem zip_getElem? {α β : Type} :
    ∀ (left : List α) (right : List β) (offset : Nat) (a : α) (b : β),
      left[offset]? = some a → right[offset]? = some b →
      (left.zip right)[offset]? = some (a, b)
  | [], _, _, _, _, held, _ => by simp at held
  | _ :: _, [], _, _, _, _, held => by simp at held
  | _ :: _, _ :: _, 0, _, _, first, second => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at first second
    simp [first, second]
  | _ :: left, _ :: right, offset + 1, a, b, first, second => by
    simp only [List.getElem?_cons_succ] at first second
    simpa using zip_getElem? left right offset a b first second

/-- Distinct names stay distinct once paired with what they hold. -/
theorem zip_pairwise {α β : Type} (right : List β) :
    ∀ (left : List α), left.Nodup → (left.zip right).Pairwise fun x y => x.1 ≠ y.1
  | [], _ => by simp
  | a :: rest, distinct => by
    cases right with
    | nil => simp
    | cons b others =>
      rw [List.nodup_cons] at distinct
      refine List.Pairwise.cons ?_ (zip_pairwise others rest distinct.2)
      intro pair member same
      have inside : pair.1 ∈ rest := (List.of_mem_zip member).1
      apply distinct.1
      rw [show a = pair.1 from same]
      exact inside

/-- A declaration that reported no repeated name has none. -/
theorem nodup_of_firstDuplicate {α : Type} [BEq α] [LawfulBEq α] :
    ∀ (items : List α), firstDuplicate items = none → items.Nodup
  | [], _ => by simp
  | item :: rest, none? => by
    rw [firstDuplicate] at none?
    by_cases repeated? : rest.contains item = true
    · rw [if_pos repeated?] at none?
      exact absurd none? (by simp)
    · rw [if_neg repeated?] at none?
      refine List.nodup_cons.mpr ⟨?_, nodup_of_firstDuplicate rest none?⟩
      simpa using repeated?

/-- The part written under one name is read back under that name. -/
theorem getObjVal?_zip {names : List String} {parts : List Json} (distinct : names.Nodup)
    {offset : Nat} {name : String} {part : Json}
    (named : names[offset]? = some name) (held : parts[offset]? = some part) :
    (Json.mkObj (names.zip parts)).getObjVal? name = .ok part :=
  getObjVal?_mkObj (zip_pairwise parts names distinct)
    (List.mem_of_getElem? (zip_getElem? names parts offset name part named held))

/--
Each field of a struct reads back as the value it was written from.

What the object yields at each position is a hypothesis, so only the recursion over the
fields is proved here.
-/
theorem valueOfFields_jsonOfFields (names : List String) (document : Json) (spelling : Spelling) :
    ∀ (fields : List Desc) (values : List Value) (documents : List Json) (position : Nat),
      (∀ pair ∈ fields.zip values, Rewrites pair.1) →
      (∀ pair ∈ fields.zip values, Fits pair.1 pair.2) →
      jsonOfFields fields spelling position values = .ok documents →
      (∀ (offset : Nat) (part : Json), documents[offset]? = some part →
        document.getObjVal? (names.getD (position + offset) "") = .ok part) →
      valueOfFields fields names spelling position document = .ok values
  | [], [], documents, _, _, _, wrote, _ => by
    rw [jsonOfFields] at wrote
    simp only [Except.ok.injEq] at wrote
    subst wrote
    rw [valueOfFields]
  | [], _ :: _, _, _, _, _, wrote, _ => by simp [jsonOfFields] at wrote
  | _ :: _, [], _, _, _, _, wrote, _ => by simp [jsonOfFields] at wrote
  | field :: fields, value :: values, documents, position, rewrites, fitted, wrote, reads => by
    rw [jsonOfFields] at wrote
    cases head : jsonOf field (spelling.part position) value with
    | error _ => simp [head, Bind.bind, Except.bind] at wrote
    | ok first =>
      cases tail : jsonOfFields fields spelling (position + 1) values with
      | error _ => simp [head, tail, Bind.bind, Except.bind] at wrote
      | ok others =>
        simp only [head, tail, Bind.bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at wrote
        subst wrote
        have here : document.getObjVal? (names.getD position "") = .ok first := by
          simpa using reads 0 first (by simp)
        have inner : valueOf field (spelling.part position) first = .ok value :=
          rewrites (field, value) (by simp) (spelling.part position) value first
            (fitted (field, value) (by simp)) head
        have shorter : valueOfFields fields names spelling (position + 1) document
            = .ok values :=
          valueOfFields_jsonOfFields names document spelling fields values others (position + 1)
            (fun pair member => rewrites pair (by simp [member]))
            (fun pair member => fitted pair (by simp [member])) tail
            (fun offset part held => by
              have := reads (offset + 1) part (by simpa using held)
              simpa [Nat.add_assoc, Nat.add_comm 1 offset] using this)
        rw [valueOfFields, here]
        simp only [Except.toOption, Bind.bind, Except.bind, pure, Except.pure, inner, shorter]

/-- The option a selector names is the one the reader walks to. -/
theorem valueOfOption_found (spelling : Spelling) (payload : Json) (option : Desc)
    (value : Value) :
    ∀ (selectors : List Nat) (options : List Desc) (start selector slot : Nat),
      selectors.findIdx? (· == selector) = some slot →
      lookupOption selectors options selector = .ok option →
      valueOf option (spelling.part (start + slot)) payload = .ok value →
      valueOfOption selectors options spelling start selector payload
        = .ok (.union selector value)
  | [], _, _, _, _, found, _, _ => by simp at found
  | _ :: _, [], _, _, _, _, named, _ => by simp [lookupOption] at named
  | chosen :: selectors, first :: options, start, selector, slot, found, named, inner => by
    rw [lookupOption] at named
    by_cases here : chosen == selector
    · rw [if_pos here] at named
      simp only [Except.ok.injEq] at named
      subst named
      have zero : slot = 0 := by
        rw [List.findIdx?_cons, if_pos (by simpa using here)] at found
        simpa using found.symm
      rw [valueOfOption, if_pos here]
      simp only [Bind.bind, Except.bind, pure, Except.pure]
      rw [show start + slot = start from by omega] at inner
      rw [inner]
    · rw [if_neg here] at named
      obtain ⟨earlier, place, split⟩ : ∃ earlier, selectors.findIdx? (· == selector) = some earlier
          ∧ slot = earlier + 1 := by
        rw [List.findIdx?_cons, if_neg (by simpa using here)] at found
        obtain ⟨earlier, place, plus⟩ := Option.map_eq_some_iff.mp found
        exact ⟨earlier, place, by omega⟩
      rw [valueOfOption, if_neg here]
      refine valueOfOption_found spelling payload option value selectors options
        (start + 1) selector earlier place named ?_
      rw [show start + 1 + earlier = start + slot from by omega]
      exact inner

/-- A sequence document reads back as the elements it was written from. -/
theorem valueOfSequence_jsonOfSequence (element : Desc) (spelling : Spelling)
    (back : Rewrites element) (elements : List Value) (document : Json)
    (fitted : ∀ value ∈ elements, Fits element value)
    (wrote : jsonOfSequence element spelling elements = .ok document) :
    valueOfSequence element spelling document = .ok elements := by
  rw [jsonOfSequence] at wrote
  by_cases alias? : spelling.isByte = true
  · rw [if_pos alias?] at wrote
    cases run : byteRun elements with
    | error _ => simp [run, Bind.bind, Except.bind] at wrote
    | ok data =>
      simp only [run, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at wrote
      subst wrote
      rw [valueOfSequence, if_pos alias?]
      simp [collectionHex, ofHex_toHex, byteElements_byteRun elements data run,
        Bind.bind, Except.bind, pure, Except.pure]
      simp
  · rw [if_neg alias?] at wrote
    cases each : jsonOfEach element spelling elements with
    | error _ => simp [each, Bind.bind, Except.bind] at wrote
    | ok documents =>
      simp only [each, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at wrote
      subst wrote
      rw [valueOfSequence, if_neg alias?]
      simpa using valueOfEntries_jsonOfEach element spelling (fun v d => back spelling v d)
        elements documents fitted each

/-- A struct writes one document per value it holds. -/
theorem jsonOfFields_length (spelling : Spelling) :
    ∀ (fields : List Desc) (values : List Value) (position : Nat) (documents : List Json),
      jsonOfFields fields spelling position values = .ok documents →
      documents.length = values.length
  | [], [], _, documents, wrote => by
    simp only [jsonOfFields, Except.ok.injEq] at wrote
    simp [← wrote]
  | [], _ :: _, _, _, wrote => by simp [jsonOfFields] at wrote
  | _ :: _, [], _, _, wrote => by simp [jsonOfFields] at wrote
  | field :: fields, value :: values, position, documents, wrote => by
    rw [jsonOfFields] at wrote
    cases head : jsonOf field (spelling.part position) value with
    | error _ => simp [head, Bind.bind, Except.bind] at wrote
    | ok first =>
      cases tail : jsonOfFields fields spelling (position + 1) values with
      | error _ => simp [head, tail, Bind.bind, Except.bind] at wrote
      | ok others =>
        simp only [head, tail, Bind.bind, Except.bind, pure, Except.pure,
          Except.ok.injEq] at wrote
        subst wrote
        simp [jsonOfFields_length spelling fields values (position + 1) others tail]

/-- A written struct carries no name it did not declare. -/
theorem find?_undeclared (names : List String) (documents : List Json) :
    (objectNames (Json.mkObj (names.zip documents))).find?
      (fun name => !names.contains name) = none := by
  rw [List.find?_eq_none]
  intro name member declared
  obtain ⟨pair, member, named⟩ := List.mem_map.mp (objectNames_mkObj member)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.contains_eq_mem,
    decide_eq_false_iff_not] at declared
  exact declared (named ▸ (List.of_mem_zip member).1)

/-- A struct object reads back as the values it was written from. -/
theorem valueOfFields_object {names : List String} {fields : List Desc} {values : List Value}
    {spelling : Spelling} {documents : List Json}
    (distinct : names.Nodup) (counted : names.length = fields.length)
    (paired : fields.length = values.length)
    (rewrites : ∀ pair ∈ fields.zip values, Rewrites pair.1)
    (fitted : ∀ pair ∈ fields.zip values, Fits pair.1 pair.2)
    (wrote : jsonOfFields fields spelling 0 values = .ok documents) :
    valueOfFields fields names spelling 0 (Json.mkObj (names.zip documents)) = .ok values := by
  refine valueOfFields_jsonOfFields names _ spelling fields values documents 0
    rewrites fitted wrote ?_
  intro offset part held
  have inside : offset < names.length := by
    have := (List.getElem?_eq_some_iff.mp held).1
    have := jsonOfFields_length spelling fields values 0 documents wrote
    omega
  have named : names[offset]? = some (names.getD offset "") := by
    simp [List.getElem?_eq_getElem inside, List.getD]
  simpa using getObjVal?_zip distinct named held

/-- A selector that names an option is found at a position among the selectors. -/
theorem findIdx?_of_lookupOption {selectors : List Nat} {options : List Desc} {selector : Nat}
    {option : Desc} (named : lookupOption selectors options selector = .ok option) :
    ∃ slot, selectors.findIdx? (· == selector) = some slot := by
  cases place : selectors.findIdx? (· == selector) with
  | some slot => exact ⟨slot, rfl⟩
  | none =>
    rw [List.findIdx?_eq_none_iff] at place
    exact absurd (place selector (lookupOption_selector _ _ _ _ named)) (by simp)

/-- A union object reads back as the value it was written from, under its own selector. -/
theorem valueOf_union {selectors : List Nat} {options : List Desc} {spelling : Spelling}
    {selector : Nat} {option : Desc} {data : Value} {payload : Json}
    (named : lookupOption selectors options selector = .ok option) (back : Rewrites option)
    (fitted : Fits option data)
    (wrote : jsonOf option (spelling.part ((selectors.findIdx? (· == selector)).getD 0)) data
      = .ok payload) :
    valueOf (.compatibleUnion selectors options) spelling
        (Json.mkObj [("selector", decimal selector), ("data", payload)])
      = .ok (.union selector data) := by
  obtain ⟨slot, place⟩ := findIdx?_of_lookupOption named
  rw [place] at wrote
  have names : objectNames (Json.mkObj [("selector", decimal selector), ("data", payload)])
      = ["data", "selector"] := by rfl
  have carried : (Json.mkObj [("selector", decimal selector), ("data", payload)]).getObjVal? "data"
      = .ok payload := getObjVal?_mkObj (by simp) (by simp)
  have tagged :
      (Json.mkObj [("selector", decimal selector), ("data", payload)]).getObjVal? "selector"
      = .ok (decimal selector) := getObjVal?_mkObj (by simp) (by simp)
  have inner : valueOf option (spelling.part (0 + slot)) payload = .ok data :=
    back _ data payload fitted (by simpa using wrote)
  rw [Json.mkObj, valueOf]
  simp only [Json.mkObj] at names tagged carried
  simp only [names, List.isEmpty_cons, Bool.false_eq_true, if_false, tagged, carried,
    Except.toOption, Bind.bind, Except.bind, readNat_decimal]
  exact valueOfOption_found spelling payload option data selectors options 0 selector slot
    place named inner

/-- What the reader checks and reads on a struct object, shared by both struct shapes. -/
theorem valueOf_struct {names : List String} {fields : List Desc} {values : List Value}
    {spelling : Spelling} {documents : List Json}
    (rewrites : ∀ field ∈ fields, Rewrites field)
    (distinct : names.Nodup) (counted : names.length = fields.length)
    (paired : fields.length = values.length)
    (fitted : ∀ pair ∈ fields.zip values, Fits pair.1 pair.2)
    (wrote : jsonOfFields fields spelling 0 values = .ok documents) :
    (objectNames (Json.mkObj (names.zip documents))).find?
        (fun name => !names.contains name) = none
      ∧ valueOfFields fields names spelling 0 (Json.mkObj (names.zip documents)) = .ok values :=
  ⟨find?_undeclared names documents,
    valueOfFields_object distinct counted paired
      (fun pair member => rewrites pair.1 (List.of_mem_zip member).1) fitted wrote⟩

/--
A document the mapping wrote for a value of a real type reads back as that value.

Every shape of the universe is covered, with nothing left to check first.
-/
theorem valueOf_jsonOf : ∀ (shape : Desc), shape.wellFormed = .ok () → Rewrites shape := by
  intro shape
  induction shape using Desc.rec
    (motive_2 := fun fields => Desc.allWellFormed fields = .ok () →
      ∀ field ∈ fields, Rewrites field) with
  | bool =>
    intro _ _ _ _ fitted wrote
    cases fitted
    exact valueOf_jsonOf_bool wrote
  | uint width =>
    intro _ _ _ _ fitted wrote
    cases fitted with
    | uint bound => exact valueOf_jsonOf_uint bound wrote
  | byteVector length =>
    intro _ _ _ _ fitted wrote
    cases fitted with
    | byteVector exact => exact valueOf_jsonOf_byteVector exact wrote
  | byteList limit =>
    intro _ _ _ _ fitted wrote
    cases fitted with
    | byteList within => exact valueOf_jsonOf_byteList within wrote
  | bitVector length =>
    intro sound _ _ _ fitted wrote
    cases fitted with
    | bitVector exact =>
      subst exact
      exact valueOf_jsonOf_bitVector sound (.bitVector rfl) wrote
  | bitList limit =>
    intro sound _ _ _ fitted wrote
    cases fitted with
    | bitList within => exact valueOf_jsonOf_bitList within sound (.bitList within) wrote
  | progressiveBitList limit =>
    intro sound _ _ _ fitted wrote
    cases fitted with
    | progressiveBitList within =>
      exact valueOf_jsonOf_progressiveBitList within sound (.progressiveBitList within) wrote
  | vector element length ih =>
    intro sound spelling _ document fitted wrote
    cases fitted with
    | vector count each =>
      rw [jsonOf] at wrote
      rw [valueOf, valueOfSequence_jsonOfSequence element _ (ih (wellFormed_vector sound)) _
        document each wrote]
      simp [count, Bind.bind, Except.bind]
      rfl
  | list element limit ih =>
    intro sound spelling _ document fitted wrote
    cases fitted with
    | list within each =>
      rw [jsonOf] at wrote
      rw [valueOf, valueOfSequence_jsonOfSequence element _ (ih (wellFormed_list sound)) _
        document each wrote]
      simp [Nat.not_lt.mpr within, Bind.bind, Except.bind]
      rfl
  | progressiveList element limit ih =>
    intro sound spelling _ document fitted wrote
    cases fitted with
    | progressiveList within each =>
      rw [jsonOf] at wrote
      rw [valueOf, valueOfSequence_jsonOfSequence element _ (ih (wellFormed_progressiveList sound))
        _ document each wrote]
      cases limit with
      | none => simp [Bind.bind, Except.bind]; rfl
      | some bound =>
        simp only [withinBound, decide_eq_true_eq] at within
        simp [Nat.not_lt.mpr within, Bind.bind, Except.bind]
        rfl
  | container names fields ih =>
    intro sound spelling value document fitted wrote
    cases fitted with
    | @container _ _ values paired each =>
      obtain ⟨counted, once⟩ := wellFormed_container_names sound
      rw [jsonOf] at wrote
      cases parts : jsonOfFields fields spelling 0 values with
      | error _ => simp [parts, Bind.bind, Except.bind] at wrote
      | ok written =>
        simp only [parts, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at wrote
        subst wrote
        obtain ⟨undeclared, read⟩ := valueOf_struct (ih (wellFormed_container sound))
          (nodup_of_firstDuplicate names once) counted paired each parts
        rw [Json.mkObj, valueOf]
        simp only [Json.mkObj] at undeclared read
        simp only [undeclared, read, Bind.bind, Except.bind]
        rfl
  | progressiveContainer active names fields ih =>
    intro sound spelling value document fitted wrote
    cases fitted with
    | @progressiveContainer _ _ _ values paired each =>
      obtain ⟨counted, once⟩ := wellFormed_progressiveContainer_names sound
      rw [jsonOf] at wrote
      cases parts : jsonOfFields fields spelling 0 values with
      | error _ => simp [parts, Bind.bind, Except.bind] at wrote
      | ok written =>
        simp only [parts, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at wrote
        subst wrote
        obtain ⟨undeclared, read⟩ := valueOf_struct (ih (wellFormed_progressiveContainer sound))
          (nodup_of_firstDuplicate names once) counted paired each parts
        rw [Json.mkObj, valueOf]
        simp only [Json.mkObj] at undeclared read
        simp only [undeclared, read, Bind.bind, Except.bind]
        rfl
  | compatibleUnion selectors options ih =>
    intro sound spelling value document fitted wrote
    cases fitted with
    | @compatibleUnion _ _ selector option data bounded named inner =>
      rw [jsonOf, named] at wrote
      cases payload : jsonOf option
          (spelling.part ((selectors.findIdx? (· == selector)).getD 0)) data with
      | error _ => simp [payload, Bind.bind, Except.bind] at wrote
      | ok written =>
        simp only [payload, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at wrote
        subst wrote
        exact valueOf_union named (ih (wellFormed_union sound) _ (lookupOption_mem _ _ _ _ named))
          inner payload
  | nil =>
    rename_i _ field member
    simp at member
  | cons field fields ih ihRest =>
    rename_i sound target member
    rcases List.mem_cons.mp member with here | later
    · subst target
      exact ih (allWellFormed_mem _ sound field List.mem_cons_self)
    · exact ihRest (allWellFormed_tail sound) target later

end Ssz
