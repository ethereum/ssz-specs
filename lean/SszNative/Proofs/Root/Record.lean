import SszNative.Proofs.Validate.Plan
import SszNative.Root
import Ssz.Proofs.Codec.Admits
import Ssz.Codec.Root
import Ssz.Proofs.Codec.Canonicality
import Ssz.Proofs.Codec.CanonicalComposite
import Ssz.Proofs.Codec.DecodeFits
import Ssz.Proofs.Codec.RootLaws
import Ssz.Proofs.Merkle.Tree

/-!
The root of a fixed-size value, read straight from its bytes.

Take a type built from booleans, integers, byte and bit vectors, vectors, and containers.
The specification's root of a value of such a type depends only on the value's encoding.
This file states that function of the bytes and proves it is the specification's root.
-/

namespace Ssz.Native

open Ssz

/-- The root of bytes packed into nodes and merkleized at the capacity their width needs. -/
def packedRoot (data : Bytes) : Bytes :=
  subtreeAt (packBytes data) (depthFor (chunksForBytes data.size)) 0

mutual

/-- The root of a fixed-size value, from its encoding. -/
def recordRoot : Desc → Bytes → Bytes
  | .vector element length, data =>
    if element.isBasic then packedRoot data
    else subtreeAt (Array.ofFn (n := length) fun i =>
      recordRoot element (data.extract (i.val * fixedWidth element) ((i.val + 1) * fixedWidth element)))
      (depthFor length) 0
  | .container _ fields, data => subtreeAt (recordFieldRoots fields data 0).toArray (depthFor fields.length) 0
  | _, data => packedRoot data

/-- The roots of a struct's fixed fields, each read in place from a position on. -/
def recordFieldRoots : List Desc → Bytes → Nat → List Bytes
  | [], _, _ => []
  | field :: fields, data, position =>
    recordRoot field (data.extract position (position + fixedWidth field)) ::
      recordFieldRoots fields data (position + fixedWidth field)

end

/-- A bounded root from a layout that mixes nothing in, its leaves within the capacity. -/
theorem rootAt_of_layout (budget : Nat) (shape : Desc) (value : Value) (leaves : Leaves) (cap : Nat)
    (chunks : Array Bytes) (laid : merkleLayout shape value = .ok ⟨leaves, some cap, none⟩)
    (read : layoutChunksAt budget ⟨leaves, some cap, none⟩ = .ok chunks) (fits : chunks.size ≤ cap) :
    hashTreeRootAt (budget + 1) shape value = .ok (subtreeAt chunks (depthFor cap) 0) := by
  -- The layout's leaves fit its capacity, so the bounded tree is the perfect tree of that depth.
  simp only [hashTreeRootAt, laid, read, merkleizeBounded, if_neg (Nat.not_lt.mpr fits), Bind.bind, Except.bind,
    pure, Except.pure]

/-- Packed leaves are read back whole. -/
theorem layoutChunksAt_packed (budget : Nat) (chunks : Array Bytes) (limit : Option Nat) (mixin : Option Bytes) :
    layoutChunksAt budget ⟨.packed chunks, limit, mixin⟩ = .ok chunks := by
  -- Packed leaves are the chunks themselves.
  simp [layoutChunksAt, Leaves.count, pure, Except.pure]

/-- The roots of decoded elements, each a function of its slice. -/
theorem mapM_roots (element : Desc) (r : Bytes → Bytes) (g : Option (Desc × Value) → Except Err Bytes)
    (each : ∀ s v, deserialize element s = .ok v → g (some (element, v)) = .ok (r s)) :
    ∀ slices values, deserializeEach element slices = .ok values →
      (values.map fun v => some (element, v)).mapM g = .ok (slices.map r)
  -- No slices decode to no values, whose roots are none.
  | [], values, read => by
    simp only [deserializeEach, Except.ok.injEq] at read
    subst read
    rfl
  | slice :: slices, values, read => by
    -- The first slice decodes, and its root is the function's value on it, then the rest follow by induction.
    rw [deserializeEach] at read
    cases head : deserialize element slice with
    | error _ => simp [head, Bind.bind, Except.bind] at read
    | ok first =>
      cases tail : deserializeEach element slices with
      | error _ => simp [head, tail, Bind.bind, Except.bind] at read
      | ok others =>
        simp only [head, tail, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at read
        subst read
        simp only [List.map_cons, List.mapM_cons, each slice first head,
          mapM_roots element r g each slices others tail, Bind.bind, Except.bind, pure, Except.pure]

/-- The roots of decoded fields, each a function of its type and slice. -/
theorem mapM_fieldRoots (r : Desc → Bytes → Bytes) (g : Option (Desc × Value) → Except Err Bytes) :
    ∀ fields slices values, (∀ field ∈ fields, ∀ s v, deserialize field s = .ok v →
        g (some (field, v)) = .ok (r field s)) →
      deserializeFields fields slices = .ok values →
      ((fields.zip values).map some).mapM g = .ok ((fields.zip slices).map fun p => r p.1 p.2)
  -- No fields decode to no values, whose roots are none.
  | [], slices, values, _, read => by
    cases slices <;> simp [deserializeFields] at read
    subst read
    rfl
  -- Fields without slices never decode.
  | field :: fields, [], values, _, read => by simp [deserializeFields] at read
  | field :: fields, slice :: slices, values, each, read => by
    -- The first field decodes, and its root is the function's value on its slice, then the rest follow by induction.
    rw [deserializeFields] at read
    cases head : deserialize field slice with
    | error _ => simp [head, Bind.bind, Except.bind] at read
    | ok first =>
      cases tail : deserializeFields fields slices with
      | error _ => simp [head, tail, Bind.bind, Except.bind] at read
      | ok others =>
        simp only [head, tail, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at read
        subst read
        simp only [List.zip_cons_cons, List.map_cons, List.mapM_cons, each field (by simp) slice first head,
          mapM_fieldRoots r g fields slices others (fun f m => each f (by simp [m])) tail, Bind.bind,
          Except.bind, pure, Except.pure]

/-- Consecutive slices of one width, joined, are the bytes they were cut from. -/
theorem join_slices (data : Bytes) (width : Nat) :
    ∀ count, width * count = data.size →
      ((List.range count).map fun i => data.extract (i * width) ((i + 1) * width)).foldl (· ++ ·) #[] = data := by
  -- Joining the first k slices gives the first k widths of bytes.
  have prefix_ : ∀ k, width * k ≤ data.size →
      ((List.range k).map fun i => data.extract (i * width) ((i + 1) * width)).foldl (· ++ ·) #[] =
        data.extract 0 (width * k) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro fits
      rw [List.range_succ, List.map_append, List.foldl_append, ih (by rw [Nat.mul_succ] at fits; omega)]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      rw [Nat.mul_comm k width, Nat.mul_comm (k + 1) width,
        extract_join data (Nat.zero_le _) (by rw [Nat.mul_succ]; omega) fits]
  intro count whole
  -- The prefix of all the slices is the whole data.
  rw [prefix_ count (by omega), whole, Array.extract_size]

/-- A value whose leaf is its own encoding roots to its packed bytes. -/
theorem leaf_root (budget : Nat) (shape : Desc) (value : Value) (data : Bytes)
    (laid : merkleLayout shape value = fixedLeaf shape value) (encoded : serialize shape value = .ok data) :
    hashTreeRootAt (budget + 1) shape value = .ok (packedRoot data) := by
  -- A fixed leaf packs its own encoding, with nothing mixed in.
  have layout : merkleLayout shape value =
      .ok ⟨.packed (packBytes data), some (packBytes data).size, none⟩ := by
    rw [laid]
    simp [fixedLeaf, encoded, MerkleLayout.packing, Bind.bind, Except.bind, pure, Except.pure]
  rw [rootAt_of_layout budget shape value _ _ _ layout (layoutChunksAt_packed ..) (Nat.le_refl _)]
  simp [packedRoot, chunksForBytes]

mutual

/-- Plain types have a fixed size. -/
theorem plain_hasWidth : ∀ d : Desc, plain d = true → hasWidth d = true
  -- Scalars and byte or bit vectors have fixed sizes.
  | .bool, _ | .uint _, _ | .byteVector _, _ | .bitVector _, _ => rfl
  -- Plain vectors and structs have fixed-size parts.
  | .vector element _, p => by simp only [plain] at p; simp only [hasWidth]; exact plain_hasWidth element p
  | .container _ fields, p => by simp only [plain] at p; simp only [hasWidth]; exact plainAll_allHaveWidth fields p
  -- Every other type is never plain.
  | .byteList _, p | .bitList _, p | .progressiveBitList _, p | .list _ _, p | .progressiveList _ _, p
  | .progressiveContainer _ _ _, p | .compatibleUnion _ _, p => by simp [plain] at p

/-- Plain fields all have a fixed size. -/
theorem plainAll_allHaveWidth : ∀ fields : List Desc, plainAll fields = true → allHaveWidth fields = true
  -- No fields have fixed sizes trivially.
  | [], _ => rfl
  | field :: fields, p => by
    -- Each plain field has a fixed size.
    simp only [plainAll, Bool.and_eq_true] at p
    simp only [allHaveWidth, plain_hasWidth field p.1, plainAll_allHaveWidth fields p.2, Bool.and_self]

end

/-- A decode reads one value per slice. -/
theorem deserializeEach_length (element : Desc) :
    ∀ (slices : List Bytes) (values : List Value),
      deserializeEach element slices = .ok values → values.length = slices.length
  -- No slices decode to no values.
  | [], values, read => by
    simp only [deserializeEach, Except.ok.injEq] at read
    simp [← read]
  | slice :: rest, values, read => by
    -- Each slice decodes to one value, and the rest follow by induction.
    rw [deserializeEach] at read
    cases head : deserialize element slice with
    | error _ => simp [head, Bind.bind, Except.bind] at read
    | ok first =>
      cases tail : deserializeEach element rest with
      | error _ => simp [head, tail, Bind.bind, Except.bind] at read
      | ok others =>
        simp only [head, tail, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at read
        subst read
        simp [deserializeEach_length element rest others tail]

/-- A struct decode reads one value per field. -/
theorem deserializeFields_length :
    ∀ (fields : List Desc) (slices : List Bytes) (values : List Value),
      deserializeFields fields slices = .ok values → values.length = fields.length
  -- No fields read no values.
  | [], slices, values, read => by
    cases slices <;> simp [deserializeFields] at read
    -- Fields without slices never decode.
    simp [← read]
  | _ :: _, [], _, read => by simp [deserializeFields] at read
  | field :: fields, slice :: slices, values, read => by
    -- Each field decodes to one value, and the rest follow by induction.
    rw [deserializeFields] at read
    cases head : deserialize field slice with
    | error _ => simp [head, Bind.bind, Except.bind] at read
    | ok first =>
      cases tail : deserializeFields fields slices with
      | error _ => simp [head, tail, Bind.bind, Except.bind] at read
      | ok others =>
        simp only [head, tail, Bind.bind, Except.bind, pure, Except.pure, Except.ok.injEq] at read
        subst read
        simp [deserializeFields_length fields slices others tail]

/-- The field roots read in place are the roots of the slices the struct decode cuts. -/
theorem recordFieldRoots_slots (data : Bytes) :
    ∀ (fields : List Desc) (position : Nat), recordFieldRoots fields data position =
      (fields.zip ((fixedSlots data fields position).map Slot.held)).map fun p => recordRoot p.1 p.2
  | [], _ => rfl
  | field :: fields, position => by
    -- The first field's root reads its slot, and the rest follow by induction.
    simp [recordFieldRoots, fixedSlots, Slot.held, recordFieldRoots_slots data fields]

/-- Every field of a plain list is plain. -/
theorem plainAll_mem : ∀ (fields : List Desc), plainAll fields = true → ∀ field ∈ fields, plain field = true
  -- An empty list has no members.
  | [], _, _, member => by simp at member
  | f :: rest, p, field, member => by
    -- A member is the head, plain by the first half, or in the tail, by induction.
    simp only [plainAll, Bool.and_eq_true] at p
    rcases List.mem_cons.mp member with here | later
    · exact here ▸ p.1
    · exact plainAll_mem rest p.2 field later

/-- A field is no deeper than the deepest of its struct. -/
theorem nesting_le_deepest : ∀ (fields : List Desc), ∀ field ∈ fields, field.nesting ≤ Desc.deepestNesting fields
  -- An empty list has no members.
  | [], _, member => by simp at member
  | f :: rest, field, member => by
    -- A struct is as deep as its deepest field.
    simp only [Desc.deepestNesting]
    rcases List.mem_cons.mp member with here | later
    · subst here; omega
    · have := nesting_le_deepest rest field later; omega

/-- The specification's root of a decoded fixed-size value is the root read from its bytes. -/
def RootsFromBytes (d : Desc) : Prop :=
  plain d = true → d.wellFormed = .ok () → ∀ data value, deserialize d data = .ok value →
    ∀ budget, d.nesting ≤ budget → hashTreeRootAt budget d value = .ok (recordRoot d data)

/-- The root read from the bytes of a fixed-size value is the specification's root of the value they decode to. -/
theorem recordRoot_spec (d : Desc) : RootsFromBytes d := by
  -- Types and their field lists are handled together, by mutual induction.
  induction d using Desc.rec (motive_2 := fun fields => ∀ field ∈ fields, RootsFromBytes field) with
  | bool | uint | byteVector =>
    -- A scalar or byte vector's leaf is its own encoding, which decoding preserves.
    intro _ sound data value read budget deep
    obtain ⟨b, rfl⟩ : ∃ b, budget = b + 1 := ⟨budget - 1, by simp [Desc.nesting] at deep; omega⟩
    exact leaf_root b _ value data rfl (serialize_of_deserialize _ sound data value read)
  | bitVector length =>
    -- A bit vector's leaf is its encoding, under the capacity its bit length gives.
    intro _ sound data value read budget deep
    obtain ⟨b, rfl⟩ : ∃ b, budget = b + 1 := ⟨budget - 1, by simp [Desc.nesting] at deep; omega⟩
    have encoded := serialize_of_deserialize _ sound data value read
    cases value with
    | bits bits =>
      simp only [serialize] at encoded
      split at encoded
      · rename_i sized
        simp only [beq_iff_eq] at sized
        simp only [Except.ok.injEq] at encoded
        -- The bits pack back into the encoding, whose width fixes the capacity.
        have width : data.size = (length + 7) / 8 := by rw [← encoded]; simp [packBits]
        have layout : merkleLayout (.bitVector length) (.bits bits) =
            .ok ⟨.packed (packBytes data), some (chunksForBits length), none⟩ := by
          simp [merkleLayout, sized, packedBits, encoded, MerkleLayout.packing, pure, Except.pure]
        rw [rootAt_of_layout b _ _ _ _ _ layout (layoutChunksAt_packed ..)
          (by simp [chunksForBits, width, bytesPerChunk]; omega)]
        simp only [recordRoot, packedRoot, chunksForBits, chunksForBytes, width, bytesPerChunk]
        rw [show ((length + 7) / 8 + 32 - 1) / 32 = (length + 8 * 32 - 1) / (8 * 32) by omega]
      · simp at encoded
    | _ => simp [serialize] at encoded
  | byteList | bitList | progressiveBitList | list | progressiveList | progressiveContainer | compatibleUnion =>
    -- Every other type is never plain.
    intro p; simp [plain] at p
  | vector element length ih =>
    -- A vector spends one budget step, and its elements are fixed-size.
    intro p sound data value read budget deep
    simp only [plain] at p
    obtain ⟨b, rfl⟩ : ∃ b, budget = b + 1 := ⟨budget - 1, by simp [Desc.nesting] at deep; omega⟩
    simp only [Desc.nesting] at deep
    have elementSound := wellFormed_vector sound
    have elementSize : element.fixedSize = some (fixedWidth element) := by
      rw [fixedSize_eq, if_pos (plain_hasWidth element p)]
    -- Decoding cuts the encoding into one slice per element.
    let slices := (List.range length).map fun i =>
      data.extract (i * fixedWidth element) ((i + 1) * fixedWidth element)
    have cut : vectorSlices element length data = .ok slices ∧ data.size = fixedWidth element * length := by
      cases hv : vectorSlices element length data with
      | error _ => simp [deserialize, hv, Bind.bind, Except.bind] at read
      | ok sl =>
        simp only [vectorSlices, elementSize, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind,
          pure, Except.pure] at hv
        split at hv
        · simp at hv
        split at hv
        · simp at hv
        rename_i _ same
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at same
        simp only [Except.ok.injEq] at hv
        exact ⟨by rw [← hv], same⟩
    obtain ⟨cut, whole⟩ := cut
    simp only [deserialize, cut, Bind.bind, Except.bind, pure, Except.pure] at read
    -- Each element decodes from its slice, and decoding is canonical.
    cases each : deserializeEach element slices with
    | error _ => simp [slices, each] at read
    | ok elements =>
      simp only [slices, each, Except.ok.injEq] at read
      subst read
      have count : elements.length = length := by
        rw [deserializeEach_length element slices elements each]; simp [slices]
      have canonical := serializeEach_of_deserializeEach (serialize_of_deserialize element elementSound) slices
        elements each
      by_cases basic : element.isBasic = true
      · -- Basic elements pack into shared nodes: the bytes themselves.
        have joined := join_slices data (fixedWidth element) length (by omega)
        have item : element.itemLength = fixedWidth element := by
          cases element <;> simp_all [Desc.isBasic, Desc.itemLength, fixedWidth]
        have layout : merkleLayout (.vector element length) (.seq elements) =
            .ok ⟨.packed (packBytes data), some (chunksForBytes (length * fixedWidth element)), none⟩ := by
          simp only [merkleLayout, count, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, sequenceLayout,
            basic, canonical, packElements, item, MerkleLayout.packing, Bind.bind, Except.bind, pure, Except.pure]
          rw [show slices = (List.range length).map fun i =>
            data.extract (i * fixedWidth element) ((i + 1) * fixedWidth element) from rfl, joined]
          rfl
        rw [rootAt_of_layout b _ _ _ _ _ layout (layoutChunksAt_packed ..)
          (by simp [chunksForBytes, bytesPerChunk]; rw [whole, Nat.mul_comm]; omega)]
        simp only [recordRoot, basic, ↓reduceIte, packedRoot, whole, Nat.mul_comm length]
      · -- Composite elements each bring a root of their own.
        have layout : merkleLayout (.vector element length) (.seq elements) =
            .ok ⟨.nested (elements.map fun v => some (element, v)), some length, none⟩ := by
          simp [merkleLayout, count, sequenceLayout, basic, MerkleLayout.nesting, pure, Except.pure]
        have roots : layoutChunksAt b ⟨.nested (elements.map fun v => some (element, v)), some length, none⟩ =
            .ok (slices.map (recordRoot element)).toArray := by
          simp only [layoutChunksAt, Leaves.count, Option.getD_none, List.drop_zero, Nat.sub_zero,
            List.length_map]
          rw [List.take_of_length_le (by simp), mapM_roots element (recordRoot element) _ (fun s v decoded =>
            ih p elementSound s v decoded b (by omega)) slices elements each]
          rfl
        rw [rootAt_of_layout b _ _ _ _ _ layout roots (by simp [slices])]
        simp only [recordRoot, basic, Bool.false_eq_true, ↓reduceIte]
        congr 2
        apply Array.ext
        · simp [slices]
        · intro i _ _
          simp [slices]
  | container names fields ih =>
    -- A struct spends one budget step, and its fields are fixed-size.
    intro p sound data value read budget deep
    simp only [plain] at p
    obtain ⟨b, rfl⟩ : ∃ b, budget = b + 1 := ⟨budget - 1, by simp [Desc.nesting] at deep; omega⟩
    simp only [Desc.nesting] at deep
    have fieldsSound := allWellFormed_mem fields (wellFormed_container sound)
    have all := plainAll_allHaveWidth fields p
    -- Decoding reads every field in place.
    let slices := (fixedSlots data fields 0).map Slot.held
    have small : ¬ data.size ≥ 2 ^ (8 * bytesPerOffset) := by
      intro big
      rw [deserialize, structSlices_overflow fields data big] at read
      simp [Bind.bind, Except.bind] at read
    have same : data.size = fieldsWidth fields := by
      apply Classical.byContradiction
      intro off
      simp [deserialize, structSlices, small, structBudget, fieldsFixedSize_eq, all, off, Bind.bind,
        Except.bind] at read
    have cut : structSlices fields data = .ok slices := by
      simp [structSlices, structBudget, fieldsFixedSize_eq, all, same,
        readSlots_fixed data fields 0 all (by omega), bodyStarts_fixedSlots, slices, Bind.bind, Except.bind,
        pure, Except.pure]
      omega
    simp only [deserialize, cut, Bind.bind, Except.bind, pure, Except.pure] at read
    -- Each field decodes from its slot, and its root is read from that slot.
    cases each : deserializeFields fields slices with
    | error _ => simp [each] at read
    | ok values =>
      simp only [each, Except.ok.injEq] at read
      subst read
      have count := deserializeFields_length fields slices values each
      have layout : merkleLayout (.container names fields) (.seq values) =
          .ok ⟨.nested ((fields.zip values).map some), some fields.length, none⟩ := by
        simp [merkleLayout, count, MerkleLayout.nesting, pure, Except.pure]
      have roots : layoutChunksAt b ⟨.nested ((fields.zip values).map some), some fields.length, none⟩ =
          .ok ((fields.zip slices).map fun p => recordRoot p.1 p.2).toArray := by
        simp only [layoutChunksAt, Leaves.count, Option.getD_none, List.drop_zero, Nat.sub_zero,
          List.length_map]
        rw [List.take_of_length_le (by simp), mapM_fieldRoots recordRoot _ fields slices values (fun f m s v decoded =>
          ih f m (plainAll_mem fields p f m) (fieldsSound f m) s v decoded b (by have := nesting_le_deepest fields f m; omega)) each]
        rfl
      have sized : ((fields.zip slices).map fun p => recordRoot p.1 p.2).toArray.size ≤ fields.length := by
        simp only [List.size_toArray, List.length_map, List.length_zip]
        omega
      rw [rootAt_of_layout b _ _ _ _ _ layout roots sized]
      simp only [recordRoot, recordFieldRoots_slots]
      rfl
  -- An empty field list has no members.
  | nil => rename_i member; simp at member
  | cons field fields ihHead ihTail =>
    -- A member field is the head or in the tail, by induction.
    rename_i held member
    rcases List.mem_cons.mp member with here | later
    · exact here ▸ ihHead
    · exact ihTail held later

end Ssz.Native
