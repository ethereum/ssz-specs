import Asm.Root.Lemmas

/-! The root of a plain value is the root of its encoding. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Root

open Ssz

/-- The root a nested slot contributes. -/
def slotRoot (budget : Nat) : Option (Desc × Value) → Except Err Bytes
  | none => pure zeroChunk
  | some (shape, value) => hashTreeRootAt budget shape value

theorem layoutChunksAt_nested {budget : Nat} {slots : List (Option (Desc × Value))} {limit : Option Nat}
    {mixin : Option Bytes} :
    layoutChunksAt budget ⟨.nested slots, limit, mixin⟩ =
      (slots.mapM (slotRoot budget)).bind fun roots => .ok roots.toArray := by
  simp only [layoutChunksAt, Leaves.count, Option.getD_none, List.drop_zero, Nat.sub_zero,
    List.take_length]
  rfl

theorem layoutChunksAt_packed {budget : Nat} {chunks : Array Bytes} {limit : Option Nat}
    {mixin : Option Bytes} : layoutChunksAt budget ⟨.packed chunks, limit, mixin⟩ = .ok chunks := by
  simp only [layoutChunksAt, Leaves.count, Option.getD_none, Array.extract_size]
  rfl

/-- A bounded layout with nothing mixed in roots to the tree of its capacity. -/
theorem hashTreeRootAt_bounded {budget : Nat} {shape : Desc} {value : Value} {layout : MerkleLayout}
    {chunks : Array Bytes} {capacity : Nat} (laid : merkleLayout shape value = .ok layout)
    (got : layoutChunksAt budget layout = .ok chunks) (limit : layout.limit = some capacity)
    (fits : chunks.size ≤ capacity) (noMix : layout.mixin = none) :
    hashTreeRootAt (budget + 1) shape value = .ok (subtreeAt chunks (depthFor capacity) 0) := by
  simp [hashTreeRootAt, laid, got, limit, noMix, merkleizeBounded, Nat.not_lt.mpr fits, bind,
    Except.bind, pure, Except.pure]

/-- A leaf of fixed width: its encoding packed into chunks, as many as it fills. -/
theorem root_fixedLeaf {budget : Nat} {shape : Desc} {value : Value} {bytes : Bytes}
    (leaf : merkleLayout shape value = fixedLeaf shape value) (encoded : serialize shape value = .ok bytes) :
    hashTreeRootAt (budget + 1) shape value = .ok (packedRoot bytes) := by
  have laid : merkleLayout shape value = .ok (.packing (packBytes bytes) (some (packBytes bytes).size)) := by
    simp [leaf, fixedLeaf, encoded, bind, Except.bind, pure, Except.pure]
  exact hashTreeRootAt_bounded laid layoutChunksAt_packed
    rfl (by simp) rfl

theorem serializeFields_values : ∀ (fields : List Desc) (values : List Value) (parts : List Bytes),
    serializeFields fields values = .ok parts → fields.length = values.length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h | _ :: _, [], _, h => by simp [serializeFields] at h
  | field :: fields, value :: values, parts, h => by
    simp only [serializeFields, bind, Except.bind] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i tail tailOk
        simp [serializeFields_values fields values tail tailOk]

theorem rootsOf_length_le : ∀ (fields : List Desc) (parts : List Bytes),
    (rootsOf fields parts).length ≤ fields.length
  | [], _ => by simp [rootsOf]
  | _ :: _, [] => by simp [rootsOf]
  | field :: fields, part :: parts => by
    simp [rootsOf, rootsOf_length_le fields parts]

/-- Elements each rooted from their own encoding. -/
theorem each_root {budget : Nat} {element : Desc}
    (rooted : ∀ v part, serialize element v = .ok part → hashTreeRootAt budget element v = .ok (rootOf element part)) :
    ∀ (elements : List Value) (parts : List Bytes), serializeEach element elements = .ok parts →
      (elements.map fun v => some (element, v)).mapM (slotRoot budget) = .ok (parts.map (rootOf element))
  | [], parts, h => by simp [serializeEach] at h; subst h; rfl
  | v :: vs, parts, h => by
    simp only [serializeEach, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i head headOk
      split at h
      · simp at h
      · rename_i tail tailOk
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [List.mapM_cons, slotRoot, rooted v head headOk, each_root rooted vs tail tailOk, bind,
          Except.bind, pure, Except.pure]

mutual

theorem root_plain : (d : Desc) → plain d = true → ∀ budget, d.nesting ≤ budget + 1 →
    ∀ value bytes, serialize d value = .ok bytes → hashTreeRootAt (budget + 1) d value = .ok (rootOf d bytes)
  | .bool, _, budget, _, value, bytes, h => root_fixedLeaf rfl h
  | .uint _, _, budget, _, value, bytes, h => root_fixedLeaf rfl h
  | .byteVector _, _, budget, _, value, bytes, h => root_fixedLeaf rfl h
  | .bitVector n, _, budget, _, value, bytes, h => by
    cases value with
    | bits data =>
      simp only [serialize] at h
      split at h
      · rename_i size
        simp only [beq_iff_eq] at size
        simp only [Except.ok.injEq] at h
        subst h
        have laid : merkleLayout (.bitVector n) (.bits data) =
            .ok (.packing (packBytes (packBits data ((n + 7) / 8))) (some (chunksForBits n))) := by
          simp [merkleLayout, size, packedBits, MerkleLayout.packing, pure, Except.pure]
        have same : (packBytes (packBits data ((n + 7) / 8))).size = chunksForBits n := by
          simp [packBits, chunksForBits, bytesPerChunk]
          omega
        rw [hashTreeRootAt_bounded laid layoutChunksAt_packed
          rfl (Nat.le_of_eq same) rfl, ← same]
        rfl
      · simp at h
    | _ => simp [serialize] at h
  | .vector element n, p, budget, deep, value, bytes, h => by
    simp only [plain] at p
    cases value with
    | seq elements =>
    simp only [serialize] at h
    split at h
    case isFalse => simp at h
    rename_i count
    simp only [beq_iff_eq] at count
    simp only [serializeSequence, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i parts partsOk
      have joinedEq := assemble_inline (by simp [isFixed_plain element p]) (by simp) h
      subst joinedEq
      have sizes := each_size (serialize_size element p) elements parts partsOk
      have length := serializeEach_length element elements parts partsOk
      by_cases basic : element.isBasic
      · -- Basic elements pack into shared chunks.
        have laid : merkleLayout (.vector element n) (.seq elements) =
            .ok (.packing (packBytes (joined parts)) (some (chunksForBytes (n * element.itemLength)))) := by
          simp [merkleLayout, count, sequenceLayout, basic, partsOk, packElements, foldl_joined,
            MerkleLayout.packing, bind, Except.bind, pure, Except.pure]
        have item : element.itemLength = width element := by
          cases element <;> simp_all [Desc.isBasic, Desc.itemLength, width]
        have same : (packBytes (joined parts)).size = chunksForBytes (n * element.itemLength) := by
          rw [packBytes_size, joined_size, sizes, List.sum_replicate_nat, length, count, item]
          simp [chunksForBytes, Nat.mul_comm]
        rw [hashTreeRootAt_bounded laid layoutChunksAt_packed
          rfl (Nat.le_of_eq same) rfl, ← same]
        simp [rootOf, basic, packedRoot]
      · -- Composite elements each bring a root.
        have deepElement : element.nesting ≤ budget := by simp [Desc.nesting] at deep; omega
        have positive := element.nesting_pos
        obtain ⟨inner, rfl⟩ : ∃ inner, budget = inner + 1 := ⟨budget - 1, by omega⟩
        have roots := each_root (budget := inner + 1)
          (fun v part encoded => root_plain element p inner deepElement v part encoded) elements parts partsOk
        have laid : merkleLayout (.vector element n) (.seq elements) =
            .ok (.nesting (elements.map fun v => some (element, v)) (some n)) := by
          simp [merkleLayout, count, sequenceLayout, basic, MerkleLayout.nesting, pure, Except.pure]
        rw [hashTreeRootAt_bounded laid (by rw [MerkleLayout.nesting, layoutChunksAt_nested, roots]; rfl)
          rfl (by simp [length, count]) rfl]
        simp only [rootOf, basic, if_false, Bool.false_eq_true]
        rw [slices_joined parts _ (by rw [sizes, length, count])]
    | _ => simp [serialize] at h
  | .container names fields, p, budget, deep, value, bytes, h => by
    simp only [plain] at p
    cases value with
    | seq values =>
    simp only [serialize, serializeStruct, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i parts partsOk
      have length := serializeFields_length fields values parts partsOk
      have joinedEq := assemble_inline (isFixed_plainAll fields p) (by simp [length]) h
      subst joinedEq
      have sizes := fields_size fields p values parts partsOk
      have valuesLength : fields.length = values.length :=
        serializeFields_values fields values parts partsOk
      have laid : merkleLayout (.container names fields) (.seq values) =
          .ok (.nesting ((fields.zip values).map some) (some fields.length)) := by
        simp [merkleLayout, valuesLength, MerkleLayout.nesting, pure, Except.pure]
      have roots := fields_root fields p budget (by simp [Desc.nesting] at deep; omega) values parts partsOk
      rw [hashTreeRootAt_bounded laid (by rw [MerkleLayout.nesting, layoutChunksAt_nested, roots]; rfl)
        rfl (by simpa using rootsOf_length_le fields parts) rfl]
      simp only [rootOf]
      rw [slices_joined parts _ sizes]
    | _ => simp [serialize] at h
  | .byteList _, p, _, _, _, _, _ | .bitList _, p, _, _, _, _, _
  | .progressiveBitList _, p, _, _, _, _, _ | .list _ _, p, _, _, _, _, _
  | .progressiveList _ _, p, _, _, _, _, _ | .progressiveContainer _ _ _, p, _, _, _, _, _
  | .compatibleUnion _ _, p, _, _, _, _, _ => by simp [plain] at p

theorem fields_root : (fields : List Desc) → plainAll fields = true → ∀ budget,
    Desc.deepestNesting fields ≤ budget → ∀ values parts, serializeFields fields values = .ok parts →
      ((fields.zip values).map some).mapM (slotRoot budget) = .ok (rootsOf fields parts)
  | [], _, budget, _, values, parts, h => by
    cases values <;> simp [serializeFields] at h
    subst h
    rfl
  | field :: fields, p, budget, deep, values, parts, h => by
    simp only [plainAll, Bool.and_eq_true] at p
    simp only [Desc.deepestNesting, Nat.max_le] at deep
    cases values with
    | nil => simp [serializeFields] at h
    | cons value values =>
      simp only [serializeFields, bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i head headOk
        split at h
        · simp at h
        · rename_i tail tailOk
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          have positive := field.nesting_pos
          obtain ⟨inner, rfl⟩ : ∃ inner, budget = inner + 1 := ⟨budget - 1, by omega⟩
          simp [List.mapM_cons, slotRoot, root_plain field p.1 inner deep.1 value head headOk,
            fields_root fields p.2 (inner + 1) deep.2 values tail tailOk, rootsOf, bind, Except.bind,
            pure, Except.pure]

end

end Ssz.Asm.Root
