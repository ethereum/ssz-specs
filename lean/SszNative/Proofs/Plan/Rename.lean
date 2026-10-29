import SszNative.Proofs.Plan.Names
import SszNative.Branch
import SszNative.Codec
import SszNative.Proofs.Validate.Main
import SszNative.Proofs.Root.Main
import SszNative.Proofs.Driver.Validate.Main

/-!
What naming fields by position leaves alone.

Checking an encoding, rooting it, proving its nodes, and cutting or laying out its parts never read a field's name.
Each gives the same answer on a type and on that type renamed.
A plan read back names its fields by position, so what the native code computes on the plan it reads is what the
specification computes on the type it was written from.
-/

namespace Ssz.Native.Plan

open Ssz Ssz.Native

/-! Facts about one level of a type. -/

/-- Renaming keeps whether a type is basic. -/
@[simp] theorem isBasic_rename (d : Desc) : (rename d).isBasic = d.isBasic := by
  cases d <;> simp [rename, Desc.isBasic]

/-- Renaming keeps the bytes one element takes in a node. -/
@[simp] theorem itemLength_rename (d : Desc) : (rename d).itemLength = d.itemLength := by
  cases d <;> simp [rename, Desc.itemLength]

/-- Renaming keeps whether deserializing first bounds the size. -/
@[simp] theorem composite_rename (d : Desc) : composite (rename d) = composite d := by
  cases d <;> simp [rename, composite]

/-- Renaming keeps whether a value is its own node. -/
@[simp] theorem packsIntoNode_rename (d : Desc) : packsIntoNode (rename d) = packsIntoNode d := by
  cases d <;> simp [rename, packsIntoNode]

/-- Renaming types renames each one. -/
@[simp] theorem renameAll_map (ds : List Desc) : renameAll ds = ds.map rename := renameAll_eq_map ds

/-- Renaming keeps a type's nesting. -/
@[simp] theorem nesting_rename' (d : Desc) : (rename d).nesting = d.nesting := nesting_rename d

mutual

/-- Renaming keeps a type's encoded width. -/
@[simp] theorem fixedSize_rename : ∀ d : Desc, (rename d).fixedSize = d.fixedSize
  | .bool | .uint _ | .byteVector _ | .byteList _ | .bitVector _ | .bitList _ | .progressiveBitList _
  | .list _ _ | .progressiveList _ _ | .compatibleUnion _ _ => by simp [rename, Desc.fixedSize]
  | .vector e _ => by simp [rename, Desc.fixedSize, fixedSize_rename e]
  | .container _ fs | .progressiveContainer _ _ fs => by
    simp only [rename, Desc.fixedSize]; exact fieldsFixedSize_rename fs

/-- Renaming keeps the total width of fields. -/
theorem fieldsFixedSize_rename : ∀ ds : List Desc, Desc.fieldsFixedSize (renameAll ds) = Desc.fieldsFixedSize ds
  | [] => rfl
  | d :: rest => by simp only [renameAll, Desc.fieldsFixedSize, fixedSize_rename d, fieldsFixedSize_rename rest]

end

/-- Renaming keeps the total width of fields, as a map. -/
@[simp] theorem fieldsFixedSize_map (ds : List Desc) :
    Desc.fieldsFixedSize (ds.map rename) = Desc.fieldsFixedSize ds := by
  rw [← renameAll_eq_map]; exact fieldsFixedSize_rename ds

/-- Renaming keeps whether a type is fixed. -/
@[simp] theorem isFixed_rename (d : Desc) : (rename d).isFixed = d.isFixed := by simp [Desc.isFixed]

/-- Renaming keeps the width of a struct's fixed part. -/
@[simp] theorem leadingWidth_map : ∀ ds : List Desc, Desc.leadingWidth (ds.map rename) = Desc.leadingWidth ds
  | [] => rfl
  | d :: rest => by simp [Desc.leadingWidth, leadingWidth_map rest]

mutual

/-- Renaming keeps whether a type has a width. -/
@[simp] theorem hasWidth_rename : ∀ d : Desc, hasWidth (rename d) = hasWidth d
  | .bool | .uint _ | .byteVector _ | .byteList _ | .bitVector _ | .bitList _ | .progressiveBitList _
  | .list _ _ | .progressiveList _ _ | .compatibleUnion _ _ => by simp [rename, hasWidth]
  | .vector e _ => by simp [rename, hasWidth, hasWidth_rename e]
  | .container _ fs | .progressiveContainer _ _ fs => by
    simp only [rename, hasWidth]; exact allHaveWidth_rename fs

/-- Renaming keeps whether types have widths. -/
theorem allHaveWidth_rename : ∀ ds : List Desc, allHaveWidth (renameAll ds) = allHaveWidth ds
  | [] => rfl
  | d :: rest => by simp only [renameAll, allHaveWidth, hasWidth_rename d, allHaveWidth_rename rest]

end

mutual

/-- Renaming keeps a type's width. -/
@[simp] theorem fixedWidth_rename : ∀ d : Desc, fixedWidth (rename d) = fixedWidth d
  | .bool | .uint _ | .byteVector _ | .byteList _ | .bitVector _ | .bitList _ | .progressiveBitList _
  | .list _ _ | .progressiveList _ _ | .compatibleUnion _ _ => by simp [rename, fixedWidth]
  | .vector e _ => by simp [rename, fixedWidth, fixedWidth_rename e]
  | .container _ fs | .progressiveContainer _ _ fs => by
    simp only [rename, fixedWidth]; exact fieldsWidth_rename fs

/-- Renaming keeps the total width of types. -/
theorem fieldsWidth_rename : ∀ ds : List Desc, fieldsWidth (renameAll ds) = fieldsWidth ds
  | [] => rfl
  | d :: rest => by simp only [renameAll, fieldsWidth, fixedWidth_rename d, fieldsWidth_rename rest]

end

mutual

/-- Renaming keeps a type's probes. -/
@[simp] theorem plan_rename : ∀ d : Desc, Native.plan (rename d) = Native.plan d
  | .bool | .uint _ | .byteVector _ | .byteList _ | .bitVector _ | .bitList _ | .progressiveBitList _
  | .list _ _ | .progressiveList _ _ | .compatibleUnion _ _ => by simp [rename, Native.plan]
  | .vector e _ => by simp [rename, Native.plan, plan_rename e]
  | .container _ fs | .progressiveContainer _ _ fs => by
    simp only [rename, Native.plan]; exact fieldsPlan_rename fs 0

/-- Renaming keeps fields' probes. -/
theorem fieldsPlan_rename : ∀ (ds : List Desc) (offset : Nat), fieldsPlan (renameAll ds) offset = fieldsPlan ds offset
  | [], _ => rfl
  | d :: rest, offset => by
    simp only [renameAll, fieldsPlan, plan_rename d, fixedWidth_rename d, fieldsPlan_rename rest]

end

mutual

/-- Renaming keeps a type's probe runs. -/
@[simp] theorem runs_rename : ∀ d : Desc, runs (rename d) = runs d
  | .bool | .uint _ | .byteVector _ | .byteList _ | .bitVector _ | .bitList _ | .progressiveBitList _
  | .list _ _ | .progressiveList _ _ | .compatibleUnion _ _ => by simp [rename, runs, Native.plan]
  | .vector e _ => by simp [rename, runs]
  | .container _ fs | .progressiveContainer _ _ fs => by
    simp only [rename, runs]; exact fieldsRuns_rename fs 0

/-- Renaming keeps fields' probe runs. -/
theorem fieldsRuns_rename : ∀ (ds : List Desc) (offset : Nat), fieldsRuns (renameAll ds) offset = fieldsRuns ds offset
  | [], _ => rfl
  | d :: rest, offset => by
    simp only [renameAll, fieldsRuns, runs_rename d, fixedWidth_rename d, fieldsRuns_rename rest]

end

mutual

/-- Renaming keeps whether a type is plain. -/
@[simp] theorem plain_rename : ∀ d : Desc, plain (rename d) = plain d
  | .bool | .uint _ | .byteVector _ | .byteList _ | .bitVector _ | .bitList _ | .progressiveBitList _
  | .list _ _ | .progressiveList _ _ | .compatibleUnion _ _ | .progressiveContainer _ _ _ => by simp [rename, plain]
  | .vector e _ => by simp [rename, plain, plain_rename e]
  | .container _ fs => by simp only [rename, plain]; exact plainAll_rename fs

/-- Renaming keeps whether types are plain. -/
theorem plainAll_rename : ∀ ds : List Desc, plainAll (renameAll ds) = plainAll ds
  | [] => rfl
  | d :: rest => by simp only [renameAll, plainAll, plain_rename d, plainAll_rename rest]

end

/-- Renaming keeps whether types have widths, as a map. -/
@[simp] theorem allHaveWidth_map (ds : List Desc) : allHaveWidth (ds.map rename) = allHaveWidth ds := by
  rw [← renameAll_eq_map]; exact allHaveWidth_rename ds

/-- Renaming keeps the total width of types, as a map. -/
@[simp] theorem fieldsWidth_map (ds : List Desc) : fieldsWidth (ds.map rename) = fieldsWidth ds := by
  rw [← renameAll_eq_map]; exact fieldsWidth_rename ds

/-- Renaming keeps fields' probes, as a map. -/
@[simp] theorem fieldsPlan_map (ds : List Desc) (offset : Nat) :
    fieldsPlan (ds.map rename) offset = fieldsPlan ds offset := by
  rw [← renameAll_eq_map]; exact fieldsPlan_rename ds offset

/-- Renaming keeps fields' probe runs, as a map. -/
@[simp] theorem fieldsRuns_map (ds : List Desc) (offset : Nat) :
    fieldsRuns (ds.map rename) offset = fieldsRuns ds offset := by
  rw [← renameAll_eq_map]; exact fieldsRuns_rename ds offset

/-- Renaming keeps whether types are plain, as a map. -/
@[simp] theorem plainAll_map (ds : List Desc) : plainAll (ds.map rename) = plainAll ds := by
  rw [← renameAll_eq_map]; exact plainAll_rename ds

/-! Where the parts of an encoding sit. -/

/-- Renaming keeps a struct's budget. -/
@[simp] theorem structBudget_map (ds : List Desc) (scope : Nat) :
    structBudget (ds.map rename) scope = structBudget ds scope := by
  simp [structBudget]

/-- Renaming keeps the places of a struct's fields. -/
@[simp] theorem readPlaces_map : ∀ (ds : List Desc) (b : ByteArray) (start size position : Nat),
    readPlaces (ds.map rename) b start size position = readPlaces ds b start size position
  | [], _, _, _, _ => rfl
  | d :: rest, b, start, size, position => by
    simp only [List.map_cons, readPlaces, fixedSize_rename, readPlaces_map rest]

/-- Renaming keeps the places of a struct's fixed part. -/
@[simp] theorem fieldPlaces_map (ds : List Desc) (b : ByteArray) (start stop : Nat) :
    fieldPlaces (ds.map rename) b start stop = fieldPlaces ds b start stop := by
  simp [fieldPlaces]

/-- Renaming keeps the ranges of a struct's fields. -/
@[simp] theorem fieldRanges_map (ds : List Desc) (b : ByteArray) (start stop : Nat) :
    fieldRanges (ds.map rename) b start stop = fieldRanges ds b start stop := by
  simp [fieldRanges]

/-- Renaming keeps where a vector's elements sit. -/
@[simp] theorem vectorRanges_rename (e : Desc) (length : Nat) (b : ByteArray) (start stop : Nat) :
    vectorRanges (rename e) length b start stop = vectorRanges e length b start stop := by
  simp [vectorRanges]

/-- Renaming keeps where a list's elements sit. -/
@[simp] theorem listRanges_rename (e : Desc) (limit : Option Nat) (b : ByteArray) (start stop : Nat) :
    listRanges (rename e) limit b start stop = listRanges e limit b start stop := by
  simp [listRanges]

/-- Renaming keeps the element ranges of a valid sequence. -/
@[simp] theorem elementRanges_rename (e : Desc) (b : ByteArray) (start stop count : Nat) :
    elementRanges (rename e) b start stop count = elementRanges e b start stop count := by
  simp [elementRanges]

/-- Renaming keeps the element count of a valid sequence. -/
@[simp] theorem elementCount_rename (e : Desc) (b : ByteArray) (start stop : Nat) :
    elementCount (rename e) b start stop = elementCount e b start stop := by
  simp [elementCount]

/-- The option a selector names among renamed options is that option renamed. -/
theorem lookupOption_map : ∀ (sels : List Nat) (opts : List Desc) (selector : Nat),
    lookupOption sels (opts.map rename) selector = (lookupOption sels opts selector).map rename
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | chosen :: sels, o :: opts, selector => by
    simp only [List.map_cons, lookupOption]
    split
    · rfl
    · exact lookupOption_map sels opts selector

/-- Renaming keeps the ranges of a composite's parts. -/
theorem viewRanges_rename (d : Desc) (b : ByteArray) (start stop : Nat) :
    viewRanges (rename d) b start stop = viewRanges d b start stop := by
  cases d <;> simp [rename, viewRanges]

/-- Renaming keeps whether a part fits its type. -/
@[simp] theorem partFits_rename (d : Desc) (part : ByteArray) : partFits (rename d) part = partFits d part := by
  simp [partFits]

/-- Renaming keeps which parts fit their types. -/
@[simp] theorem checkParts_map : ∀ (ds : List Desc) (parts : List ByteArray),
    checkParts (ds.map rename) parts = checkParts ds parts
  | [], _ => rfl
  | _ :: _, [] => rfl
  | d :: rest, part :: parts => by simp [checkParts, checkParts_map rest parts]

/-- Renaming keeps how parts are laid out. -/
@[simp] theorem layOut_map (ds : List Desc) (parts : List ByteArray) :
    layOut (ds.map rename) parts = layOut ds parts := by
  simp [layOut, Function.comp_def]

/-- Renaming keeps the encoding assembled from parts. -/
theorem assemble_rename (d : Desc) (parts : List ByteArray) : assemble (rename d) parts = assemble d parts := by
  cases d with
  | vector e n | list e n | progressiveList e n =>
    simp only [rename, assemble]
    rw [← List.map_replicate, layOut_map]
  | compatibleUnion sels opts =>
    simp only [rename, assemble, renameAll_map]
    split
    · simp only [lookupOption_map]
      cases lookupOption sels opts _ <;> simp [Except.map, bind, Except.bind]
    · rfl
  | _ => simp [rename, assemble]

/-! Checking an encoding. -/

section Validate

/-- What checking a range against one type keeps under renaming. -/
def RangeKept (d : Desc) : Prop :=
  ∀ (b : ByteArray) (start stop : Nat), validateRange (rename d) b start stop = validateRange d b start stop

/-- Checking listed ranges against a renamed element is checking them against the element. -/
theorem validateEach_rename {e : Desc} (h : RangeKept e) (b : ByteArray) :
    ∀ ranges, validateEach (rename e) b ranges = validateEach e b ranges
  | [] => by simp [validateEach]
  | (s, t) :: rest => by simp [validateEach, h b s t, validateEach_rename h b rest]

/-- Checking element ranges against a renamed element is checking them against the element. -/
theorem validateRanges_rename {e : Desc} (h : RangeKept e) (b : ByteArray) (r : Ranges) :
    validateRanges (rename e) b r = validateRanges e b r := by
  cases r <;> simp [validateRanges, validateEach_rename h]

/-- Checking fixed fields in place keeps renaming. -/
theorem validateInline_rename : ∀ (fs : List Desc), (∀ f ∈ fs, RangeKept f) → ∀ (b : ByteArray) (places : List Place),
    validateInline (fs.map rename) b places = validateInline fs b places
  | [], _, _, _ => by simp [validateInline]
  | _ :: _, _, _, [] => by simp [validateInline]
  | f :: fs, h, b, .inline s t :: places => by
    simp [validateInline, h f (by simp) b s t, validateInline_rename fs (fun g hg => h g (by simp [hg])) b places]
  | f :: fs, h, b, .body _ :: places => by
    simp [validateInline, validateInline_rename fs (fun g hg => h g (by simp [hg])) b places]

/-- Checking fields against their ranges keeps renaming. -/
theorem validateFields_rename : ∀ (fs : List Desc), (∀ f ∈ fs, RangeKept f) →
    ∀ (b : ByteArray) (ranges : List (Nat × Nat)), validateFields (fs.map rename) b ranges = validateFields fs b ranges
  | [], _, _, [] => by simp [validateFields]
  | [], _, _, _ :: _ => by simp [validateFields]
  | _ :: _, _, _, [] => by simp [validateFields]
  | f :: fs, h, b, (s, t) :: ranges => by
    simp [validateFields, h f (by simp) b s t, validateFields_rename fs (fun g hg => h g (by simp [hg])) b ranges]

/-- Checking a struct keeps renaming. -/
theorem validateStruct_rename (fs : List Desc) (h : ∀ f ∈ fs, RangeKept f) (b : ByteArray) (start stop : Nat) :
    validateStruct (fs.map rename) b start stop = validateStruct fs b start stop := by
  simp [validateStruct, validateInline_rename fs h, validateFields_rename fs h]

/-- Checking the option a selector names keeps renaming. -/
theorem validateOption_rename : ∀ (sels : List Nat) (opts : List Desc), (∀ o ∈ opts, RangeKept o) →
    ∀ (selector : Nat) (b : ByteArray) (start stop : Nat),
      validateOption sels (opts.map rename) selector b start stop = validateOption sels opts selector b start stop
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, _ => by simp only [List.map_cons]; rw [validateOption, validateOption] <;> simp
  | _ :: _, [], _, _, _, _, _ => rfl
  | c :: sels, o :: opts, h, selector, b, start, stop => by
    simp only [List.map_cons, validateOption, h o (by simp) b start stop,
      validateOption_rename sels opts (fun g hg => h g (by simp [hg])) selector b start stop]

/-- Renaming keeps the check of a fixed-size range. -/
@[simp] theorem validateFixed_rename (d : Desc) (width : Nat) (b : ByteArray) (start stop : Nat) :
    validateFixed (rename d) width b start stop = validateFixed d width b start stop := by
  simp [validateFixed]

/-- A type whose variable-size check keeps renaming keeps its whole check. -/
theorem rangeKept_of {d : Desc}
    (h : ∀ b start stop, validateVariable (rename d) b start stop = validateVariable d b start stop) : RangeKept d := by
  intro b start stop
  rw [validateRange, validateRange, hasWidth_rename, fixedWidth_rename, validateFixed_rename, h]

/-- Checking a range against a renamed type is checking it against the type. -/
theorem validateRange_rename (d : Desc) : RangeKept d := by
  induction d using Desc.rec (motive_2 := fun fs => ∀ f ∈ fs, RangeKept f) with
  | nil => rename_i h; simp at h
  | cons f fs ihf ihfs =>
    rename_i g h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ihf
    · exact ihfs g h
  | vector e n ih | list e n ih | progressiveList e n ih =>
    refine rangeKept_of fun b start stop => ?_
    simp [validateVariable, rename, validateRanges_rename ih]
  | container names fs ih | progressiveContainer active names fs ih =>
    refine rangeKept_of fun b start stop => ?_
    simp [validateVariable, rename, validateStruct_rename fs ih]
  | compatibleUnion sels opts ih =>
    refine rangeKept_of fun b start stop => ?_
    simp [validateVariable, rename, validateOption_rename sels opts ih]
  | _ => exact rangeKept_of fun b start stop => by simp [rename]

/-- Checking an encoding against a renamed type is checking it against the type. -/
theorem validate_rename (d : Desc) (b : ByteArray) : validate (rename d) b = validate d b :=
  validateRange_rename d b 0 b.size

end Validate

/-! Rooting an encoding. -/

section Root

/-- What rooting values of one fixed-size type keeps under renaming. -/
def RootsKept (d : Desc) : Prop :=
  ∀ (b : ByteArray) (start stride count : Nat), rootsOf (rename d) b start stride count = rootsOf d b start stride count

/-- What rooting a range of one type keeps under renaming. -/
def RootKept (d : Desc) : Prop :=
  ∀ (b : ByteArray) (start stop : Nat), rootOf (rename d) b start stop = rootOf d b start stop

/-- Rooting values of a type that keeps renaming, as an equation. -/
theorem RootsKept.eq {d : Desc} (h : RootsKept d) (b : ByteArray) (start stride count : Nat) :
    rootsOf (rename d) b start stride count = rootsOf d b start stride count := h b start stride count

/-- Rooting a range of a type that keeps renaming, as an equation. -/
theorem RootKept.eq {d : Desc} (h : RootKept d) (b : ByteArray) (start stop : Nat) :
    rootOf (rename d) b start stop = rootOf d b start stop := h b start stop

/-- Rooting a long run of values keeps renaming. -/
theorem chunkedRoots_rename {d : Desc} (h : RootsKept d) (b : ByteArray) (start stride count : Nat) :
    chunkedRoots (rename d) b start stride count = chunkedRoots d b start stride count := by
  rw [chunkedRoots, chunkedRoots]
  simp only [h.eq]

/-- The columns of a sequence's elements keep renaming. -/
theorem elementColumns_rename {e : Desc} (h : RootsKept e) (b : ByteArray) (start stride count width length : Nat) :
    elementColumns (rename e) b start stride count width length = elementColumns e b start stride count width length := by
  rw [elementColumns, elementColumns]
  simp only [h.eq]

/-- The columns of fields keep renaming. -/
theorem fieldColumns_rename : ∀ (fs : List Desc), (∀ f ∈ fs, RootsKept f) →
    ∀ (b : ByteArray) (start stride count offset : Nat),
      fieldColumns (fs.map rename) b start stride count offset = fieldColumns fs b start stride count offset
  | [], _, _, _, _, _, _ => by simp [fieldColumns]
  | f :: fs, h, b, start, stride, count, offset => by
    simp [fieldColumns, (h f (by simp)).eq, fieldColumns_rename fs (fun g hg => h g (by simp [hg]))]

/-- One record's field roots keep renaming. -/
theorem fieldLeaves_rename : ∀ (fs : List Desc), (∀ f ∈ fs, RootsKept f) →
    ∀ (b : ByteArray) (start offset : Nat) (leaves : ByteArray) (node : Nat),
      fieldLeaves (fs.map rename) b start offset leaves node = fieldLeaves fs b start offset leaves node
  | [], _, _, _, _, _, _ => by simp [fieldLeaves]
  | f :: fs, h, b, start, offset, leaves, node => by
    simp [fieldLeaves, (h f (by simp)).eq, fieldLeaves_rename fs (fun g hg => h g (by simp [hg]))]

/-- Rooting values of a renamed fixed-size type is rooting them against the type. -/
theorem rootsOf_rename (d : Desc) : RootsKept d := by
  induction d using Desc.rec (motive_2 := fun fs => ∀ f ∈ fs, RootsKept f) with
  | nil => rename_i h; simp at h
  | cons f fs ihf ihfs =>
    rename_i g h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ihf
    · exact ihfs g h
  | vector e n ih =>
    intro b start stride count
    have hw := fixedWidth_rename (.vector e n)
    simp only [rename] at hw
    simp only [rootsOf.eq_def, rename, hw, isBasic_rename, fixedWidth_rename, chunkedRoots_rename ih,
      elementColumns_rename ih]
  | container names fs ih =>
    intro b start stride count
    simp only [rootsOf.eq_def, rename, renameAll_map, List.length_map, fieldLeaves_rename fs ih,
      fieldColumns_rename fs ih]
  | _ =>
    intro b start stride count
    simp [rootsOf.eq_def, rename, fixedWidth]

/-- The roots of variable-size values keep renaming. -/
theorem variableRoots_rename {e : Desc} (h : RootKept e) (b : ByteArray) :
    ∀ ranges, variableRoots (rename e) b ranges = variableRoots e b ranges
  | [] => by simp [variableRoots]
  | (s, t) :: rest => by simp [variableRoots, h.eq, variableRoots_rename h b rest]

/-- The nodes under a counted sequence keep renaming. -/
theorem sequenceNodes_rename {e : Desc} (h : RootKept e) (b : ByteArray) (start stop limit : Nat) :
    sequenceNodes (rename e) b start stop limit = sequenceNodes e b start stop limit := by
  rw [sequenceNodes, sequenceNodes]
  simp only [isBasic_rename, itemLength_rename, elementCount_rename, plain_rename, fixedWidth_rename,
    chunkedRoots_rename (rootsOf_rename e), elementRanges_rename, variableRoots_rename h]

/-- The root of the option a selector names keeps renaming. -/
theorem optionRoot_rename : ∀ (sels : List Nat) (opts : List Desc), (∀ o ∈ opts, RootKept o) →
    ∀ (selector : Nat) (b : ByteArray) (start stop : Nat),
      optionRoot sels (opts.map rename) selector b start stop = optionRoot sels opts selector b start stop
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, _, _, _, _, _ => by simp only [List.map_cons]; rw [optionRoot, optionRoot] <;> simp
  | _ :: _, [], _, _, _, _, _ => rfl
  | c :: sels, o :: opts, h, selector, b, start, stop => by
    simp only [List.map_cons, optionRoot, (h o (by simp)).eq,
      optionRoot_rename sels opts (fun g hg => h g (by simp [hg])) selector b start stop]

/-- The roots of fields keep renaming. -/
theorem fieldRoots_rename : ∀ (fs : List Desc), (∀ f ∈ fs, RootKept f) →
    ∀ (b : ByteArray) (ranges : List (Nat × Nat)), fieldRoots (fs.map rename) b ranges = fieldRoots fs b ranges
  | [], _, _, [] => rfl
  | [], _, _, _ :: _ => rfl
  | _ :: _, _, _, [] => by simp only [List.map_cons]; rw [fieldRoots, fieldRoots] <;> simp
  | f :: fs, h, b, (s, t) :: ranges => by
    simp only [List.map_cons, fieldRoots, (h f (by simp)).eq,
      fieldRoots_rename fs (fun g hg => h g (by simp [hg])) b ranges]

/-- Rooting a range of a renamed type is rooting it against the type. -/
theorem rootOf_rename (d : Desc) : RootKept d := by
  induction d using Desc.rec (motive_2 := fun fs => ∀ f ∈ fs, RootKept f) with
  | nil => rename_i h; simp at h
  | cons f fs ihf ihfs =>
    rename_i g h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ihf
    · exact ihfs g h
  | vector e n ih =>
    intro b start stop
    have hp := plain_rename (.vector e n)
    have hw := fixedWidth_rename (.vector e n)
    have hr := fun b start stride count => (rootsOf_rename (.vector e n)).eq b start stride count
    simp only [rename] at hp hw hr
    simp only [rootOf.eq_def, rename, hp, hw, hr, elementRanges_rename, variableRoots_rename ih]
  | list e n ih | progressiveList e n ih =>
    intro b start stop
    simp only [rootOf.eq_def, rename, sequenceNodes_rename ih, elementCount_rename]
  | container names fs ih =>
    intro b start stop
    have hp := plain_rename (.container names fs)
    have hw := fixedWidth_rename (.container names fs)
    have hr := fun b start stride count => (rootsOf_rename (.container names fs)).eq b start stride count
    simp only [rename, renameAll_map] at hp hw hr
    simp only [rootOf.eq_def, rename, renameAll_map, hp, hw, hr, fieldRanges_map, fieldRoots_rename fs ih,
      List.length_map]
  | progressiveContainer active names fs ih =>
    intro b start stop
    simp only [rootOf.eq_def, rename, renameAll_map, fieldRanges_map, fieldRoots_rename fs ih]
  | compatibleUnion sels opts ih =>
    intro b start stop
    simp only [rootOf.eq_def, rename, renameAll_map, optionRoot_rename sels opts ih]
  | _ => intro b start stop; simp [rename]

/-- The root of an encoding against a renamed type is its root against the type. -/
theorem hashTreeRoot_rename (d : Desc) (b : ByteArray) : hashTreeRoot (rename d) b = hashTreeRoot d b := by
  simp [hashTreeRoot, validate_rename, (rootOf_rename d).eq]

end Root

/-! Proving nodes of an encoding. -/

section Branch

/-- A slot's type renamed, its range kept. -/
def renameSlot : Desc × Nat × Nat → Desc × Nat × Nat
  | (d, s, e) => (rename d, s, e)

/-- Slots with every type renamed. -/
def renameSlots : Slots → Slots
  | .stride element start width count => .stride (rename element) start width count
  | .listed slots => .listed (slots.map (Option.map renameSlot))

/-- Leaves with every type renamed. -/
def renameLeaves : EncodedLeaves → EncodedLeaves
  | .packed nodes count => .packed nodes count
  | .nested slots => .nested (renameSlots slots)

/-- A layout with every type renamed. -/
def renameLayout (layout : EncodedLayout) : EncodedLayout :=
  { layout with leaves := renameLeaves layout.leaves }

/-- Renaming keeps how many leaves a layout holds. -/
@[simp] theorem count_renameLayout (layout : EncodedLayout) : (renameLayout layout).count = layout.count := by
  rcases layout with ⟨leaves, limit, mixin⟩
  cases leaves with
  | packed => rfl
  | nested slots => cases slots <;> simp [renameLayout, renameLeaves, renameSlots, EncodedLayout.count, Slots.count]

/-- Renaming keeps a layout's capacity. -/
@[simp] theorem limit_renameLayout (layout : EncodedLayout) : (renameLayout layout).limit = layout.limit := rfl

/-- Renaming keeps a layout's mixed-in word. -/
@[simp] theorem mixin_renameLayout (layout : EncodedLayout) : (renameLayout layout).mixin = layout.mixin := rfl

/-- The slots of a renamed element are its slots renamed. -/
theorem elementSlots_rename (e : Desc) (b : ByteArray) (start stop count : Nat) :
    elementSlots (rename e) b start stop count = renameSlots (elementSlots e b start stop count) := by
  simp only [elementSlots, fixedSize_rename]
  split <;> simp [renameSlots, renameSlot, Function.comp_def]

/-- The layout of a renamed sequence is its layout renamed. -/
theorem encodedSequence_rename (e : Desc) (b : ByteArray) (start stop count : Nat) (positions : Option Nat)
    (mixin : Option ByteArray) :
    encodedSequence (rename e) b start stop count positions mixin =
      renameLayout (encodedSequence e b start stop count positions mixin) := by
  simp only [encodedSequence, isBasic_rename, itemLength_rename]
  split <;> simp [renameLayout, renameLeaves, elementSlots_rename]

/-- Placing renamed fields is placing the fields, then renaming. -/
theorem placeFields_rename : ∀ (active : List Bool) (fs : List (Desc × Nat × Nat)),
    placeFields active (fs.map renameSlot) = (placeFields active fs).map (Option.map renameSlot)
  | [], _ => rfl
  | false :: active, fs => by simp [placeFields, placeFields_rename active fs]
  | true :: active, [] => by
    have := placeFields_rename active []
    simp only [List.map_nil] at this
    simp only [List.map_nil, placeFields, List.map_cons, Option.map_none, ← this]
  | true :: active, f :: fs => by simp [placeFields, placeFields_rename active fs]

/-- Renamed fields paired with ranges are the pairs renamed. -/
theorem zip_rename (fs : List Desc) (ranges : List (Nat × Nat)) :
    (fs.map rename).zip ranges = (fs.zip ranges).map renameSlot := by
  induction fs generalizing ranges with
  | nil => rfl
  | cons f fs ih => cases ranges <;> simp [ih, renameSlot]

/-- The layout of a renamed type is its layout renamed. -/
theorem layoutOf_rename (d : Desc) (b : ByteArray) (start stop : Nat) :
    layoutOf (rename d) b start stop = (layoutOf d b start stop).map renameLayout := by
  cases d with
  | vector e n | list e n | progressiveList e n =>
    simp [layoutOf, rename, encodedSequence_rename, Except.map]
  | container names fs =>
    simp only [layoutOf, rename, renameAll_map, fieldRanges_map, List.length_map]
    cases fieldRanges fs b start stop <;>
      simp [Except.map, bind, Except.bind, pure, Except.pure, renameLayout, renameLeaves, renameSlots, zip_rename,
        Function.comp_def]
  | progressiveContainer active names fs =>
    simp only [layoutOf, rename, renameAll_map, fieldRanges_map]
    cases fieldRanges fs b start stop <;>
      simp [Except.map, bind, Except.bind, pure, Except.pure, renameLayout, renameLeaves, renameSlots, zip_rename,
        placeFields_rename]
  | compatibleUnion sels opts =>
    simp only [layoutOf, rename, renameAll_map, lookupOption_map]
    cases lookupOption sels opts _ <;>
      simp [Except.map, bind, Except.bind, pure, Except.pure, renameLayout, renameLeaves, renameSlots, renameSlot]
  | _ => simp [layoutOf, rename, Except.map, renameLayout, renameLeaves]

/-- The root of one renamed listed position is its root. -/
theorem listedRoot_rename (b : ByteArray) (slot : Option (Desc × Nat × Nat)) :
    listedRoot b (slot.map renameSlot) = listedRoot b slot := by
  rcases slot with _ | ⟨d, s, e⟩
  · rfl
  · simp [listedRoot, renameSlot, (rootOf_rename d).eq]

/-- The leaves of a renamed layout are its leaves. -/
theorem leavesIn_rename (b : ByteArray) (layout : EncodedLayout) (first last : Nat) :
    leavesIn b (renameLayout layout) first last = leavesIn b layout first last := by
  rcases layout with ⟨leaves, limit, mixin⟩
  cases leaves with
  | packed => rfl
  | nested slots =>
    cases slots with
    | stride e start width count =>
      simp [leavesIn, renameLayout, renameLeaves, renameSlots, EncodedLayout.count, Slots.count,
        chunkedRoots_rename (rootsOf_rename e), (rootOf_rename e).eq]
    | listed slots =>
      simp [leavesIn, renameLayout, renameLeaves, renameSlots, EncodedLayout.count, Slots.count, ← List.map_drop,
        ← List.map_take, Function.comp_def, listedRoot_rename]

/-- The slot at a position of renamed slots is the slot renamed. -/
theorem at_renameSlots (slots : Slots) (position : Nat) :
    (renameSlots slots).at position = (slots.at position).map (Option.map renameSlot) := by
  cases slots with
  | stride => simp only [renameSlots, Slots.at]; split <;> simp [renameSlot]
  | listed => simp [renameSlots, Slots.at]

/-- Proving nodes from a renamed type is proving them from the type, at every budget. -/
theorem nodeRootAt_rename : ∀ (budget : Nat) (d : Desc) (b : ByteArray) (start stop index : Nat),
    nodeRootAt budget (rename d) b start stop index = nodeRootAt budget d b start stop index := by
  intro budget
  induction budget with
  | zero => intro d b start stop index; simp [nodeRootAt]
  | succ budget ih =>
    -- A walk inside a leaf goes one level down, where the budget is one smaller.
    have bounded : ∀ (layout : EncodedLayout) (index depth leavesFrom capacity : Nat) (b : ByteArray),
        boundedNode budget b (renameLayout layout) index depth leavesFrom capacity =
          boundedNode budget b layout index depth leavesFrom capacity := by
      intro layout index depth leavesFrom capacity b
      rw [boundedNode, boundedNode]
      simp only [leavesIn_rename]
      rcases layout with ⟨leaves, limit, mixin⟩
      cases leaves with
      | packed => rfl
      | nested slots =>
        simp only [renameLayout, renameLeaves, at_renameSlots]
        split
        · rfl
        · generalize slots.at _ = o
          rcases o with _ | _ | ⟨d, s, e⟩ <;> simp [renameSlot, ih]
    have progressive : ∀ (layout : EncodedLayout) (index depth start capacity : Nat) (b : ByteArray),
        progressiveNode budget b (renameLayout layout) index depth start capacity =
          progressiveNode budget b layout index depth start capacity := by
      intro layout index depth start capacity b
      rw [progressiveNode, progressiveNode]
      simp only [count_renameLayout, bounded, leavesIn_rename]
    intro d b start stop index
    rw [nodeRootAt, nodeRootAt]
    simp only [(rootOf_rename d).eq, layoutOf_rename]
    cases layoutOf d b start stop with
    | error e => rfl
    | ok l =>
      simp only [Except.map, bind, Except.bind, mixin_renameLayout, limit_renameLayout, bounded, progressive]
      rfl

/-- The node at a generalized index of a renamed type's value is the type's. -/
theorem nodeRoot_rename (d : Desc) (b : ByteArray) (index : Nat) :
    nodeRoot (rename d) b index = nodeRoot d b index := by
  simp [nodeRoot, validate_rename, nodeRootAt_rename]

/-- The branch for a generalized index of a renamed type's value is the type's. -/
theorem buildProof_rename (d : Desc) (b : ByteArray) (index : Nat) :
    buildProof (rename d) b index = buildProof d b index := by
  simp [buildProof, validate_rename, nodeRootAt_rename]

/-- The multiproof for generalized indices of a renamed type's value is the type's. -/
theorem buildMultiproof_rename (d : Desc) (b : ByteArray) (indices : List Nat) :
    buildMultiproof (rename d) b indices = buildMultiproof d b indices := by
  simp [buildMultiproof, validate_rename, nodeRootAt_rename]

end Branch

/-! The decoded plan against the type it was written from. -/

section Decoded

/-- A type's plan is its renamed type's plan. -/
theorem encode_rename (d : Desc) : encode (rename d) = encode d := by
  simp [encode, words_rename]

/--
Checking an encoding against the type a plan reads back as is deserializing it against the type the plan was
written from.

The plan must hold numbers that fit a word, and every union must pair its selectors with its options.
-/
theorem validate_decoded (d : Desc) (ok : paired d = true) (fits : Fits d) (b : ByteArray) :
    (decode (encode d)).map (fun read => validate read b) = some ((deserialize d b.data).map fun _ => ()) := by
  rw [decode_encode d ok fits, Option.map_some, validate_rename, validate_eq]

/--
The root of an encoding against the type a plan reads back as is the specification's root of the value it holds,
against the type the plan was written from.

The type must be well formed, and the encoding small enough for machine-sized offsets.
-/
theorem hashTreeRoot_decoded (d : Desc) (ok : paired d = true) (fits : Fits d) (sound : d.wellFormed = .ok ())
    (b : ByteArray) (small : 64 * b.size + 128 < USize.size) :
    (decode (encode d)).map (fun read => (hashTreeRoot read b).map ByteArray.data) =
      some (do let v ← deserialize d b.data; Ssz.hashTreeRoot d v) := by
  rw [decode_encode d ok fits, Option.map_some, hashTreeRoot_rename, hashTreeRoot_eq d sound b small]

mutual

/-- Renaming keeps whether a type fits the native check. -/
theorem fitsNative_rename : ∀ d : Desc, fitsNative (rename d) = fitsNative d
  | .bool | .uint _ | .byteVector _ | .byteList _ | .bitVector _ | .bitList _ | .progressiveBitList _ => by
    simp [rename]
  | .vector e _ | .list e _ | .progressiveList e _ => by simp [rename, fitsNative, fitsNative_rename e]
  | .container _ fs | .progressiveContainer _ _ fs | .compatibleUnion _ fs => by
    simp only [rename, fitsNative, allFitNative_rename fs, length_renameAll] <;> simp

/-- Renaming keeps whether types fit the native check. -/
theorem allFitNative_rename : ∀ ds : List Desc, allFitNative (renameAll ds) = allFitNative ds
  | [] => rfl
  | d :: rest => by simp only [renameAll, allFitNative, fitsNative_rename d, allFitNative_rename rest]

end

open Ssz.Native.Ir Ssz.Native.Driver.Validate in
/--
The native decoding check, for a type whose fields carry any names, against that type's plan.

The check reads the plan back with its fields named by position, and still returns what the Lean check gives on the
type itself: zero and memory untouched when it accepts, one and the refusal's words written when it refuses.
-/
theorem validate_calls_named {m : Module} {w : World} (hm : Loaded m) (d : Desc)
    (wf : d.wellFormed = .ok ()) (fit : fitsNative d = true) (deep : d.nesting ≤ maxNesting)
    (plan data err sp : Nat) (mem : Memory) (b : ByteArray)
    (hplan : PlanBytes w mem plan d) (hd : DataAt w mem data b)
    (cp : Clear err plan (encode d).size) (cd : Clear err data b.size) (ok : w.access err 32 = true)
    (small : b.size < 2 ^ 60) (room : Room w sp (2 * d.nesting) 5) :
    Calls m w "ssz_validate" sp [UInt64.ofNat plan, UInt64.ofNat (encode d).size, UInt64.ofNat data,
      UInt64.ofNat b.size, UInt64.ofNat err] mem (res (validate d b)) (after mem err (validate d b)) := by
  have hplan' : PlanBytes w mem plan (rename d) := by simpa only [PlanBytes, encode_rename] using hplan
  have := validate_calls hm (rename d) (wellFormed_rename d wf) (by rw [fitsNative_rename]; exact fit)
    (named_rename d) (by rw [nesting_rename]; exact deep) plan data err sp mem b hplan' hd
    (by rw [encode_rename]; exact cp) cd ok small (by rw [nesting_rename]; exact room)
  rwa [encode_rename, validate_rename] at this

end Decoded

end Ssz.Native.Plan
