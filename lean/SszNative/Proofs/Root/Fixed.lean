import SszNative.Proofs.Root.Packed
import SszNative.Proofs.Root.Columns
import SszNative.Proofs.Validate.Main

/-!
Roots of fixed-size values computed many at a time, from bytes, are the specification's roots.

A run of records one stride apart is rooted as columns, one per field or element, then a tree across them.
A single record is rooted as its own row of leaves.
-/

namespace Ssz.Native

open Ssz

/-- A buffer of zeros of the requested size. -/
theorem zeros_spec (size : Nat) (small : size < USize.size) :
    (zeros size).size = size ∧ ∀ x < size, (zeros size).get! x = 0 := by
  -- One and zero fit machine words.
  have one : (1 : Nat) < USize.size := Nat.lt_of_lt_of_le (by decide) USize.le_size
  have hz : ((0 : USize)).toNat = 0 := rfl
  have h1 : ((1 : USize)).toNat = 1 := by rw [show (1 : USize) = (1 : Nat).toUSize from rfl, toUSize_toNat 1 one]
  refine ⟨by simp only [zeros, gather, gatherReference_size, h1, toUSize_toNat _ small, Nat.one_mul], fun x lx => ?_⟩
  -- A gather of an empty field into one slot reads only padding.
  have := gatherReference_get ByteArray.empty 0 0 0 1 size.toUSize 0 x (by rw [h1]; decide)
    (by rw [toUSize_toNat _ small]; exact lx) (by simp [hz]) (by simp [hz])
  simp only [toUSize_toNat _ small, Nat.mul_zero, Nat.zero_add, hz, Nat.not_lt_zero, if_false] at this
  simpa [zeros, gather] using this

/-- A node past the first buffer of two joined ones is a node of the second. -/
theorem nodeOf_append_after (a b : ByteArray) (m j : Nat) (whole : a.size = 32 * m) (_inside : 32 * j + 32 ≤ b.size) :
    nodeOf (a ++ b) 0 (m + j) = nodeOf b 0 j := by
  -- The node starts past the first buffer, at its own place in the second.
  simp only [nodeOf, Nat.zero_add, ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
  have w : a.data.size = 32 * m := whole
  rw [w, Array.extract_eq_empty_of_le (as := a.data) (by rw [w]; omega), Array.empty_append,
    show 32 * (m + j) - 32 * m = 32 * j by omega, show 32 * (m + j) + 32 - 32 * m = 32 * j + 32 by omega]

/-- Runs of nodes appended in order: node i is node i mod the run width of run i / width. -/
theorem concat_runs (f : Nat → ByteArray) (width count : Nat) (positive : 0 < width)
    (sized : ∀ k, width * k < count → (f k).size = 32 * min width (count - width * k)) :
    ∀ p, width * (p - 1) < count ∨ p = 0 →
      ((List.range p).foldl (fun out k => out ++ f k) (ByteArray.emptyWithCapacity (32 * count + 32))).size =
        32 * min count (width * p) ∧
      ∀ i < min count (width * p),
        nodeOf ((List.range p).foldl (fun out k => out ++ f k) (ByteArray.emptyWithCapacity (32 * count + 32))) 0 i =
          nodeOf (f (i / width)) 0 (i % width)
  -- No runs hold no nodes.
  | 0, _ => ⟨by simp; rfl, fun i lt => by simp at lt⟩
  | p + 1, started => by
    -- The run just appended starts below the count.
    have here : width * p < count := by
      rcases started with s | s
      · simpa using s
      · omega
    -- The earlier runs hold their nodes in order, by induction.
    obtain ⟨size, nodes⟩ := concat_runs f width count positive sized p (by
      rcases Nat.eq_zero_or_pos p with z | q
      · right; exact z
      · left; have := Nat.mul_le_mul_left width (show p - 1 ≤ p by omega); omega)
    have before : min count (width * p) = width * p := by omega
    rw [before] at size nodes
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have pieceSize := sized p here
    refine ⟨by rw [ByteArray.size_append, size, pieceSize, Nat.mul_succ]; omega, fun i lt => ?_⟩
    have lt' : i < count ∧ i < width * p + width := by rw [Nat.mul_succ] at lt; omega
    by_cases old : i < width * p
    -- A node of an earlier run is read from the earlier runs.
    · rw [nodeOf_append_left _ _ _ (by rw [size]; omega), nodes i old]
    · -- A node of the run just appended.
      have q : i / width = p := by
        apply Nat.div_eq_of_lt_le
        · rw [Nat.mul_comm]; omega
        · rw [Nat.add_one_mul, Nat.mul_comm p]; omega
      have r : i = width * p + i % width := by
        have := Nat.div_add_mod i width
        rw [q] at this
        omega
      rw [q]
      conv => lhs; rw [r]
      rw [nodeOf_append_after _ _ (width * p) _ size (by rw [pieceSize]; have := Nat.mod_lt i positive; omega)]

/-- Where field k of a struct starts: the widths of the fields before it. -/
def offsetOf (fields : List Desc) (k : Nat) : Nat :=
  fieldsWidth (fields.take k)

/-- A field ends inside its struct. -/
theorem offsetOf_le : ∀ (fields : List Desc) (k : Nat) (h : k < fields.length),
    offsetOf fields k + fixedWidth fields[k] ≤ fieldsWidth fields
  -- An empty struct has no fields.
  | [], _, h => absurd h (by simp)
  -- The first field starts at offset zero.
  | f :: rest, 0, _ => by simp [offsetOf, fieldsWidth]
  | f :: rest, k + 1, h => by
    -- A later field's offset is the first field's width plus its offset among the rest.
    have := offsetOf_le rest k (by simpa using h)
    simp only [offsetOf, List.take_succ_cons, fieldsWidth, List.getElem_cons_succ] at this ⊢
    omega

/-- The columns of a struct's fields, one per field, each from the field's place in every record. -/
theorem fieldColumns_get (b : ByteArray) (start stride count : Nat) :
    ∀ (fields : List Desc) (offset : Nat),
      (fieldColumns fields b start stride count offset).length = fields.length ∧
      ∀ k (h : k < fields.length) (h' : k < (fieldColumns fields b start stride count offset).length),
        (fieldColumns fields b start stride count offset)[k] =
          rootsOf fields[k] b (start + (offset + offsetOf fields k)) stride count
  -- No fields give no columns.
  | [], _ => ⟨by simp [fieldColumns], fun k h => absurd h (by simp)⟩
  | f :: rest, offset => by
    -- The first column is the first field's, and the rest come from the following fields, by induction.
    obtain ⟨len, get⟩ := fieldColumns_get b start stride count rest (offset + fixedWidth f)
    rw [fieldColumns]
    refine ⟨by simp [len], fun k h h' => ?_⟩
    cases k with
    | zero => simp [offsetOf, fieldsWidth]
    | succ k =>
      simp only [List.getElem_cons_succ]
      rw [get k (by simpa using h) (by simpa using h')]
      simp only [offsetOf, List.take_succ_cons, fieldsWidth, Nat.add_assoc]

/-- The roots of a struct's fields read in place, one per field. -/
theorem recordFieldRoots_get (data : Bytes) :
    ∀ (fields : List Desc) (position : Nat),
      (recordFieldRoots fields data position).length = fields.length ∧
      ∀ k (h : k < fields.length) (h' : k < (recordFieldRoots fields data position).length),
        (recordFieldRoots fields data position)[k] = recordRoot fields[k]
          (data.extract (position + offsetOf fields k) (position + offsetOf fields k + fixedWidth fields[k]))
  -- No fields give no roots.
  | [], _ => ⟨rfl, fun k h => absurd h (by simp)⟩
  | f :: rest, position => by
    -- The first root is the first field's, and the rest come from the following fields, by induction.
    obtain ⟨len, get⟩ := recordFieldRoots_get data rest (position + fixedWidth f)
    simp only [recordFieldRoots]
    refine ⟨by simp [len], fun k h h' => ?_⟩
    cases k with
    | zero => simp [offsetOf, fieldsWidth]
    | succ k =>
      simp only [List.getElem_cons_succ]
      rw [get k (by simpa using h) (by simpa using h')]
      simp only [offsetOf, List.take_succ_cons, fieldsWidth, Nat.add_assoc]

/-- The columns of a vector's elements, one per element, each from the element's place in every record. -/
theorem elementColumns_get (element : Desc) (b : ByteArray) (start stride count width : Nat) :
    ∀ length, (elementColumns element b start stride count width length).length = length ∧
      ∀ j (h : j < (elementColumns element b start stride count width length).length),
        (elementColumns element b start stride count width length)[j] =
          rootsOf element b (start + width * j) stride count
  -- No elements give no columns.
  | 0 => ⟨by simp [elementColumns], fun j h => absurd h (by simp [elementColumns])⟩
  | length + 1 => by
    -- The new column is the last, at its element's place.
    obtain ⟨len, get⟩ := elementColumns_get element b start stride count width length
    rw [elementColumns]
    refine ⟨by simp [len], fun j h => ?_⟩
    by_cases old : j < length
    · rw [List.getElem_append_left (by rw [len]; exact old), get j (by rw [len]; exact old)]
    · have : j = length := by simp [len] at h; omega
      subst this
      rw [List.getElem_append_right (by rw [len]; exact Nat.le_refl _)]
      simp [len]

mutual

/-- Every well-formed plain type is at least one byte wide. -/
theorem width_pos : ∀ d : Desc, plain d = true → d.wellFormed = .ok () → 1 ≤ fixedWidth d
  -- A boolean is one byte.
  | .bool, _, _ => by simp [fixedWidth]
  | .uint w, _, sound => by
    -- A well-formed integer has one of the listed widths.
    simp only [Desc.wellFormed] at sound
    split at sound
    · rename_i listed
      simp only [fixedWidth]
      simp at listed
      omega
    · simp at sound
  | .byteVector n, _, sound => by
    -- A well-formed byte vector has a nonzero length.
    simp only [Desc.wellFormed] at sound
    split at sound
    · simp at sound
    · rename_i nz; simp only [fixedWidth]; simp at nz; omega
  | .bitVector n, _, sound => by
    -- A well-formed bit vector has a nonzero length.
    simp only [Desc.wellFormed] at sound
    split at sound
    · simp at sound
    · rename_i nz; simp only [fixedWidth]; simp at nz; omega
  | .vector element n, p, sound => by
    -- A well-formed vector has a nonzero length of positive-width elements.
    simp only [plain] at p
    have := width_pos element p (wellFormed_vector sound)
    have positive : n ≠ 0 := by
      rintro rfl
      simp [Desc.wellFormed, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at sound
    simp only [fixedWidth]
    exact Nat.mul_le_mul this (show 1 ≤ n by omega)
  | .container names fields, p, sound => by
    -- A well-formed struct has at least one field, each of positive width.
    simp only [plain] at p
    simp only [fixedWidth]
    have nonempty : fields ≠ [] := by
      rintro rfl
      simp [Desc.wellFormed, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at sound
    exact fieldsWidth_pos fields p (allWellFormed_mem fields (wellFormed_container sound)) nonempty
  | .byteList _, p, _ | .bitList _, p, _ | .progressiveBitList _, p, _ | .list _ _, p, _
  | .progressiveList _ _, p, _ | .progressiveContainer _ _ _, p, _ | .compatibleUnion _ _, p, _ => by
    -- Every other type is never plain.
    simp [plain] at p

/-- A nonempty list of well-formed plain fields is at least one byte wide. -/
theorem fieldsWidth_pos : ∀ fields : List Desc, plainAll fields = true →
    (∀ field ∈ fields, field.wellFormed = .ok ()) → fields ≠ [] → 1 ≤ fieldsWidth fields
  -- An empty list is excluded.
  | [], _, _, h => absurd rfl h
  | f :: rest, p, sound, _ => by
    -- The first field alone is a byte wide.
    simp only [plainAll, Bool.and_eq_true] at p
    have := width_pos f p.1 (sound f (by simp))
    simp only [fieldsWidth]
    omega

end

/-- A value that fits one node is rooted as its packed bytes, which are that one node. -/
theorem packs_root (d : Desc) (packs : packsIntoNode d = true) (sound : d.wellFormed = .ok ())
    (positive : 1 ≤ fixedWidth d) (data : Bytes) (sized : data.size = fixedWidth d) :
    fixedWidth d ≤ 32 ∧ recordRoot d data = (packBytes data)[0]?.getD zeroChunk := by
  have narrow : fixedWidth d ≤ 32 := by
    -- A value that packs into one node is at most 32 bytes.
    clear sized positive
    cases d with
    | uint w =>
      simp only [Desc.wellFormed] at sound
      split at sound
      · rename_i listed; simp only [fixedWidth]; simp at listed; omega
      · simp at sound
    | _ => simp_all [packsIntoNode, fixedWidth] <;> omega
  refine ⟨narrow, ?_⟩
  -- Its bytes then make one node, the whole tree.
  have one : chunksForBytes data.size = 1 := by
    rw [chunksForBytes, sized]; simp only [bytesPerChunk]; omega
  have root : recordRoot d data = packedRoot data := by
    cases d <;> simp_all [packsIntoNode, recordRoot]
  rw [root, packedRoot, one, show depthFor 1 = 0 by rw [depthFor]; simp, subtreeAt_leaf]

/-- The record's bytes, from a start, one width long. -/
abbrev recordBytes (b : ByteArray) (start width : Nat) : Bytes :=
  Native.slice b start (start + width)

/--
One record's field roots written into a zeroed buffer of nodes, one node per field from a given node on.

Each field that fits a node is copied in, and the zeros after it pad it.
Any other field's root is copied in.
-/
theorem fieldLeaves_spec (b : ByteArray) (start : Nat) (fieldsAll : List Desc)
    (rootOne : ∀ f ∈ fieldsAll, ∀ s', s' + fixedWidth f ≤ b.size →
      (rootsOf f b s' (fixedWidth f) 1).size = 32 ∧
        nodeOf (rootsOf f b s' (fixedWidth f) 1) 0 0 = recordRoot f (recordBytes b s' (fixedWidth f)))
    (positive : ∀ f ∈ fieldsAll, 1 ≤ fixedWidth f) (sound : ∀ f ∈ fieldsAll, f.wellFormed = .ok ()) :
    ∀ (fields : List Desc), (∀ f ∈ fields, f ∈ fieldsAll) → ∀ (offset : Nat) (leaves : ByteArray) (node : Nat),
      start + offset + fieldsWidth fields ≤ b.size → 32 * (node + fields.length) ≤ leaves.size →
      (∀ x, 32 * node ≤ x → x < leaves.size → leaves.get! x = 0) →
      (fieldLeaves fields b start offset leaves node).size = leaves.size ∧
      (∀ k < node, nodeOf (fieldLeaves fields b start offset leaves node) 0 k = nodeOf leaves 0 k) ∧
      ∀ k (h : k < fields.length), nodeOf (fieldLeaves fields b start offset leaves node) 0 (node + k) =
        recordRoot fields[k] (recordBytes b (start + offset + offsetOf fields k) (fixedWidth fields[k]))
  | [], _, offset, leaves, node, _, _, _ => by
    rw [fieldLeaves]
    exact ⟨rfl, fun _ _ => rfl, fun k h => absurd h (by simp)⟩
  | f :: rest, member, offset, leaves, node, inside, room, zero => by
    rw [fieldLeaves]
    simp only [fieldsWidth] at inside
    simp only [List.length_cons] at room
    have fm := member f (by simp)
    have w1 := positive f fm
    -- Write this field's node.
    generalize hnext : (if packsIntoNode f = true then b.copySlice (start + offset) leaves (32 * node) (fixedWidth f)
      else (rootsOf f b (start + offset) (fixedWidth f) 1).copySlice 0 leaves (32 * node) 32) = next
    have one := rootOne f fm (start + offset) (by omega)
    have nextSize : next.size = leaves.size := by
      rw [← hnext]
      split
      · rename_i packs
        have := (packs_root f packs (sound f fm) w1 (recordBytes b (start + offset) (fixedWidth f))
          (by simp [recordBytes]; rw [slice_size b _ _ (by omega)]; omega)).1
        exact copySlice_size _ _ _ _ _ (by omega) (by omega)
      · exact copySlice_size _ _ _ _ _ (by rw [one.1]; omega) (by omega)
    -- Bytes outside the field's node are untouched.
    have outside : ∀ x, x < leaves.size → (x < 32 * node ∨ 32 * node + 32 ≤ x) → next.get! x = leaves.get! x := by
      intro x lx far
      rw [← hnext]
      split
      · rename_i packs
        have := (packs_root f packs (sound f fm) w1 (recordBytes b (start + offset) (fixedWidth f))
          (by simp [recordBytes]; rw [slice_size b _ _ (by omega)]; omega)).1
        rw [copySlice_get _ _ _ _ _ _ (by omega) (by omega) lx, if_neg (by omega)]
      · rw [copySlice_get _ _ _ _ _ _ (by rw [one.1]; omega) (by omega) lx, if_neg (by omega)]
    have here : nodeOf next 0 node = recordRoot f (recordBytes b (start + offset) (fixedWidth f)) := by
      by_cases packs : packsIntoNode f = true
      · have cut : (recordBytes b (start + offset) (fixedWidth f)).size = fixedWidth f := by
          simp only [recordBytes]; rw [slice_size b _ _ (by omega)]; omega
        obtain ⟨narrow, root⟩ := packs_root f packs (sound f fm) w1 _ cut
        rw [root]
        apply nodeOf_of_get _ _ _ _ (by
          by_cases has : 0 < (packBytes (recordBytes b (start + offset) (fixedWidth f))).size
          · rw [Array.getElem?_eq_getElem has, Option.getD_some, packBytes_chunk_size _ _ has]
          · rw [Array.getElem?_eq_none (by omega), Option.getD_none]; simp [zeroChunk]) (by omega)
        intro x lx
        rw [packBytes_node_get _ 0 x lx, cut, Nat.zero_add]
        rw [← hnext]
        simp only [packs, if_true]
        rw [copySlice_get _ _ _ _ _ _ (by omega) (by omega) (by omega)]
        simp only [Nat.mul_zero, Nat.zero_add]
        split
        · rename_i payload
          rw [if_pos (by omega), show 32 * node + x - 32 * node = x by omega, recordBytes,
            slice_getElem! b _ _ _ (by omega) (by omega)]
        · rw [if_neg (by omega), zero _ (by omega) (by omega)]
      · rw [← one.2]
        apply nodeOf_of_get _ _ _ _ (by rw [nodeOf_size _ _ _ (by rw [one.1]; omega)]) (by omega)
        intro x lx
        rw [nodeOf_get _ _ _ _ (by rw [one.1]; omega) lx]
        rw [← hnext]
        simp only [packs, Bool.false_eq_true, if_false]
        rw [copySlice_get _ _ _ _ _ _ (by rw [one.1]; omega) (by omega) (by omega), if_pos (by omega)]
        simp only [Nat.zero_add, Nat.mul_zero]
        congr 1
        omega
    -- The rest of the fields go into the nodes after it.
    obtain ⟨size, before, after⟩ := fieldLeaves_spec b start fieldsAll rootOne positive sound rest
      (fun g m => member g (by simp [m])) (offset + fixedWidth f) next (node + 1) (by omega)
      (by rw [nextSize]; omega)
      (fun x (lo : 32 * (node + 1) ≤ x) (lx : x < next.size) => by
        rw [outside x (by rw [nextSize] at lx; exact lx) (by omega)]
        exact zero x (by omega) (by rw [nextSize] at lx; exact lx))
    refine ⟨by rw [size, nextSize], fun k lk => ?_, fun k h => ?_⟩
    · rw [before k (by omega)]
      apply nodeOf_of_get _ _ _ _ (nodeOf_size _ _ _ (by omega)) (by rw [nextSize]; omega)
      intro x lx
      rw [outside _ (by omega) (by omega), nodeOf_get _ _ _ _ (by omega) lx]
    · cases k with
      | zero =>
        simp only [Nat.add_zero]
        rw [before node (by omega), here]
        simp [offsetOf, fieldsWidth]
      | succ k =>
        rw [show node + (k + 1) = node + 1 + k by omega, after k (by simpa using h)]
        simp only [List.getElem_cons_succ, offsetOf, List.take_succ_cons, fieldsWidth, Nat.add_assoc]

/-- A run of records of one width, one stride apart, inside an addressable buffer. -/
structure Run (b : ByteArray) (width start stride count : Nat) : Prop where
  /-- Every buffer derived from the input stays addressable. -/
  small : 64 * b.size < USize.size
  /-- At least one record. -/
  nonempty : 1 ≤ count
  /-- The stride lies inside the buffer. -/
  strideIn : stride ≤ b.size
  /-- Records do not overlap. -/
  spread : 2 ≤ count → width ≤ stride
  /-- Every record lies inside the buffer. -/
  inside : ∀ i < count, start + stride * i + width ≤ b.size

/-- What a function rooting runs of records must give: one node per record, the record's root. -/
def RootsSpec (d : Desc) (f : ByteArray → Nat → Nat → Nat → ByteArray) : Prop :=
  ∀ b start stride count, Run b (fixedWidth d) start stride count →
    (f b start stride count).size = 32 * count ∧
      ∀ i < count, nodeOf (f b start stride count) 0 i = recordRoot d (recordBytes b (start + stride * i) (fixedWidth d))

/-- The records of a run fill no more than the buffer. -/
theorem Run.fill {b : ByteArray} {width start stride count : Nat} (run : Run b width start stride count)
    (positive : 1 ≤ width) : count * width ≤ b.size ∧ start + width ≤ b.size ∧ count ≤ b.size ∧ b.size < USize.size := by
  -- The last record ends inside the buffer, and the records before it are a stride apart.
  have first := run.inside 0 run.nonempty
  have fill : count * width ≤ b.size := by
    rcases Nat.lt_or_ge count 2 with one | many
    · have : count = 1 := by have := run.nonempty; omega
      subst this; omega
    · have last := run.inside (count - 1) (by omega)
      have := Nat.mul_le_mul_right (count - 1) (run.spread many)
      have split : count * width = width * (count - 1) + width := by
        rw [Nat.mul_comm, ← Nat.mul_succ]; congr 1; omega
      omega
  refine ⟨fill, by omega, Nat.le_trans (Nat.le_mul_of_pos_right count (by omega)) fill, by
    have := run.small; omega⟩

/-- Long runs are rooted a chunk of records at a time, and the chunks joined in order. -/
theorem chunked_of_roots (d : Desc) (roots : RootsSpec d (rootsOf d)) : RootsSpec d (chunkedRoots d) := by
  -- Short runs are one chunk.
  intro b start stride count run
  unfold chunkedRoots
  split
  · exact roots b start stride count run
  · rename_i long
    simp only [recordsPerChunk] at long ⊢
    simp only [List.foldl_map]
    let piece := fun k => rootsOf d b (start + stride * 1024 * k) stride (min 1024 (count - 1024 * k))
    -- Each chunk is a run of its own.
    have chunk : ∀ k, 1024 * k < count → Run b (fixedWidth d) (start + stride * 1024 * k) stride
        (min 1024 (count - 1024 * k)) := fun k lt =>
      ⟨run.small, by omega, run.strideIn, fun many => run.spread (by omega), fun i li => by
        have := run.inside (1024 * k + i) (by omega)
        rw [Nat.mul_add, ← Nat.mul_assoc] at this
        -- The chunks join in order, each node read from its own chunk.
        omega⟩
    have parts := concat_runs piece 1024 count (by decide) (fun k lt => (roots _ _ _ _ (chunk k lt)).1)
      ((count + 1024 - 1) / 1024) (Or.inl (by omega))
    rw [show min count (1024 * ((count + 1024 - 1) / 1024)) = count by omega] at parts
    refine ⟨parts.1, fun i li => ?_⟩
    refine Eq.trans (parts.2 i li) ?_
    simp only [piece]
    rw [(roots _ _ _ _ (chunk (i / 1024) (by omega))).2 (i % 1024) (by omega)]
    congr 2
    rw [Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.div_add_mod]

/-- Values rooted as packed bytes, many at a time. -/
theorem packed_spec (d : Desc) (root : ∀ s, recordRoot d s = packedRoot s)
    (code : ∀ b start stride count, rootsOf d b start stride count =
      packedRoots (fixedWidth d) (nodesFor (fixedWidth d)) b start stride count)
    (positive : 1 ≤ fixedWidth d) : RootsSpec d (rootsOf d) := by
  -- The records fill no more than the buffer.
  intro b start stride count run
  obtain ⟨fill, first, few, addressable⟩ := run.fill positive
  have small := run.small
  -- Each record's block of nodes is under twice its width, so every buffer stays addressable.
  have block : 32 * 2 ^ depthFor (nodesFor (fixedWidth d)) ≤ 64 * fixedWidth d := by
    have := two_pow_depthFor_lt (nodesFor (fixedWidth d)) (by simp only [nodesFor]; omega)
    have : nodesFor (fixedWidth d) ≤ fixedWidth d := by simp only [nodesFor]; omega
    omega
  have blocks : count * (32 * 2 ^ depthFor (nodesFor (fixedWidth d))) ≤ 64 * b.size := by
    have h1 := Nat.mul_le_mul_left count block
    have h2 : count * (64 * fixedWidth d) = 64 * (count * fixedWidth d) := Nat.mul_left_comm _ _ _
    -- Every record's root is its packed bytes' tree.
    omega
  rw [code]
  obtain ⟨size, nodes⟩ := packedRoots_spec b start stride (fixedWidth d) count (by omega) (by have := run.strideIn; omega)
    (by omega) (by omega) (by omega) (by omega) run.inside
  exact ⟨size, fun i li => by rw [nodes i li, root]⟩

/-- Fields at least one byte wide are no more than their total width in number. -/
-- No fields have no width.
theorem length_le_fieldsWidth : ∀ fields : List Desc, (∀ f ∈ fields, 1 ≤ fixedWidth f) → fields.length ≤ fieldsWidth fields
  | [], _ => Nat.le_refl _
  -- Each field adds at least one byte.
  | f :: rest, widths => by
    have := widths f (by simp)
    have := length_le_fieldsWidth rest (fun g m => widths g (by simp [m]))
    simp only [List.length_cons, fieldsWidth]
    omega

/-- Part of a record's bytes is the bytes of that part. -/
theorem recordBytes_extract (b : ByteArray) (start width x y : Nat) (within : y ≤ width) (ordered : x ≤ y) :
    (recordBytes b start width).extract x y = recordBytes b (start + x) (y - x) := by
  -- The part is the slice of the encoding at the shifted range.
  simp only [recordBytes]
  rw [slice_extract b start (start + width) x y (by omega) (by omega)]
  congr 1
  omega

/-- The native roots of fixed-size records are the specification's roots of the values they decode to. -/
theorem rootsOf_spec (d : Desc) : plain d = true → d.wellFormed = .ok () → RootsSpec d (rootsOf d) := by
  -- Types and their field lists are handled together, by mutual induction.
  induction d using Desc.rec (motive_2 := fun fields =>
    ∀ f ∈ fields, plain f = true → f.wellFormed = .ok () → RootsSpec f (rootsOf f)) with
  -- Scalars and byte or bit vectors are packed values.
  | bool | uint | byteVector | bitVector =>
    intro p sound
    exact packed_spec _ (fun _ => by rw [recordRoot] <;> simp) (fun _ _ _ _ => by rw [rootsOf] <;> simp)
      (width_pos _ p sound)
  -- Every other type is never plain.
  | byteList | bitList | progressiveBitList | list | progressiveList | progressiveContainer | compatibleUnion =>
    intro p; simp [plain] at p
  | vector element length ih =>
    -- A plain vector has plain elements, positive widths, and a nonzero length.
    intro p sound
    have pe : plain element = true := by simpa [plain] using p
    have se := wellFormed_vector sound
    have we := width_pos element pe se
    have positive := width_pos _ p sound
    have nz : 1 ≤ length := by
      apply Nat.pos_of_ne_zero
      rintro rfl
      simp [Desc.wellFormed, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at sound
    -- Basic elements pack, so the vector is a packed value.
    by_cases basic : element.isBasic = true
    · exact packed_spec _ (fun s => by simp [recordRoot, basic]) (fun _ _ _ _ => by simp [rootsOf, basic]) positive
    -- Composite elements are rooted by their own type's claim, a chunk at a time.
    · have elementSpec := ih pe se
      have chunked := chunked_of_roots element elementSpec
      intro b start stride count run
      obtain ⟨fill, first, few, addressable⟩ := run.fill positive
      have width : fixedWidth (.vector element length) = fixedWidth element * length := rfl
      rw [width] at first fill
      have wl : fixedWidth element ≤ fixedWidth element * length := Nat.le_mul_of_pos_right _ nz
      have within : ∀ j < length, fixedWidth element * j + fixedWidth element ≤ fixedWidth element * length :=
        fun j lj => by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ lj
      -- The record's elements, as the specification's array of element roots.
      have elements : ∀ s, (Array.ofFn (n := length) fun j => recordRoot element
          ((recordBytes b s (fixedWidth element * length)).extract (j.val * fixedWidth element)
            ((j.val + 1) * fixedWidth element))) =
          Array.ofFn (n := length) fun j => recordRoot element
            (recordBytes b (s + fixedWidth element * j.val) (fixedWidth element)) := by
        intro s
        apply Array.ext
        · simp
        · intro j lj _
          simp only [Array.getElem_ofFn]
          have := within j (by simpa using lj)
          rw [recordBytes_extract b s _ _ _ (by rw [Nat.succ_mul, Nat.mul_comm]; omega) (by rw [Nat.succ_mul]; omega),
            Nat.succ_mul, Nat.add_sub_cancel_left, Nat.mul_comm]
      by_cases single : count = 1
      · subst single
        -- One record: its elements' roots side by side, then their tree.
        have code : rootsOf (.vector element length) b start stride 1 =
            merkleizeDepth (chunkedRoots element b start (fixedWidth element) length) length (depthFor length) := by
          simp [rootsOf, basic]
        rw [code]
        have elementRun : Run b (fixedWidth element) start (fixedWidth element) length :=
          ⟨run.small, nz, by omega, fun _ => Nat.le_refl _, fun j lj => by have := within j lj; omega⟩
        obtain ⟨rs, rn⟩ := chunked b start _ length elementRun
        obtain ⟨ms, md⟩ := merkleizeDepth_spec _ length (depthFor length) (le_two_pow_depthFor _) (by rw [rs]; omega)
          (by
            rw [rs]
            have small := run.small
            have grow := Nat.le_mul_of_pos_left length we
            omega)
        refine ⟨by rw [ms], fun i li => ?_⟩
        have : i = 0 := by omega
        subst this
        rw [nodeOf_single _ ms, md, Nat.mul_zero, Nat.add_zero, width]
        simp only [recordRoot, basic, Bool.false_eq_true, if_false]
        rw [elements]
        congr 1
        apply Array.ext
        · simp
        · intro j lj _
          simp only [nodesFrom, Array.getElem_ofFn]
          rw [rn j (by simpa using lj)]
      · -- Many records: one column per element, then the element tree across them.
        have many : 2 ≤ count := by have := run.nonempty; omega
        have code : rootsOf (.vector element length) b start stride count =
            columnTreeTo (elementColumns element b start stride count (fixedWidth element) length) count
              (depthFor length) := by
          simp [rootsOf, basic, single]
        rw [code]
        obtain ⟨len, get⟩ := elementColumns_get element b start stride count (fixedWidth element) length
        have spread := run.spread many
        rw [width] at spread
        have columnRun : ∀ j < length, Run b (fixedWidth element) (start + fixedWidth element * j) stride count :=
          fun j lj => ⟨run.small, run.nonempty, run.strideIn,
            fun _ => Nat.le_trans (Nat.le_mul_of_pos_right _ nz) spread,
            fun i li => by have := run.inside i li; rw [width] at this; have := within j lj; omega⟩
        let leaves := fun i => Array.ofFn (n := length) fun j => recordRoot element
          (recordBytes b (start + stride * i + fixedWidth element * j.val) (fixedWidth element))
        have tree := columnTreeTo_spec (elementColumns element b start stride count (fixedWidth element) length) count
          (depthFor length) leaves (by have := run.small; omega) (fun i _ => by simp [leaves, len]) (by rw [len]; exact nz)
          ⟨fun c h => by rw [get c h]; exact (elementSpec b _ stride count (columnRun c (by omega))).1,
            fun c h i li => by
              rw [get c h, (elementSpec b _ stride count (columnRun c (by omega))).2 i li, Nat.pow_zero, Nat.mul_one,
                Nat.zero_add, subtreeAt_leaf]
              simp only [leaves, Array.getElem?_ofFn, show c < length by omega]
              congr 2
              omega⟩
          (by rw [len]; exact Nat.le_refl _)
        refine ⟨tree.1, fun i li => ?_⟩
        rw [tree.2 i li, width]
        simp only [recordRoot, basic, Bool.false_eq_true, if_false]
        rw [elements]
  | container names fields ih =>
    -- A plain struct has plain fields of positive width, and at least one of them.
    intro p sound
    have pf : plainAll fields = true := by simpa [plain] using p
    have wfs := allWellFormed_mem fields (wellFormed_container sound)
    have positive := width_pos _ p sound
    have plainEach := plainAll_mem fields pf
    have specs : ∀ f ∈ fields, RootsSpec f (rootsOf f) := fun f m => ih f m (plainEach f m) (wfs f m)
    have widths : ∀ f ∈ fields, 1 ≤ fixedWidth f := fun f m => width_pos f (plainEach f m) (wfs f m)
    have nonempty : 1 ≤ fields.length := by
      cases fields with
      | nil => simp [Desc.wellFormed, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at sound
      | cons _ _ => simp
    have few := length_le_fieldsWidth fields widths
    -- The records fill no more than the buffer.
    intro b start stride count run
    obtain ⟨fill, first, _, addressable⟩ := run.fill positive
    have width : fixedWidth (.container names fields) = fieldsWidth fields := rfl
    rw [width] at first fill
    have small := run.small
    -- The record's fields, as the specification's array of field roots.
    have fieldsArray : ∀ s, (recordFieldRoots fields (recordBytes b s (fieldsWidth fields)) 0).toArray =
        Array.ofFn (n := fields.length) fun k =>
          recordRoot fields[k] (recordBytes b (s + offsetOf fields k) (fixedWidth fields[k])) := by
      intro s
      obtain ⟨len, get⟩ := recordFieldRoots_get (recordBytes b s (fieldsWidth fields)) fields 0
      apply Array.ext
      · simp [len]
      · intro k lk _
        have lk' : k < fields.length := by simpa [len] using lk
        simp only [List.getElem_toArray, Array.getElem_ofFn]
        rw [get k lk' (by simpa using lk), Nat.zero_add,
          recordBytes_extract b s _ _ _ (offsetOf_le fields k lk') (by omega), Nat.add_sub_cancel_left]
        rfl
    by_cases single : count = 1
    · subst single
      -- One record: its field roots in a row of nodes, then their tree.
      have code : rootsOf (.container names fields) b start stride 1 =
          merkleizeDepth (fieldLeaves fields b start 0 (zeros (32 * fields.length + 32)) 0) fields.length
            (depthFor fields.length) := by
        rw [rootsOf]; simp
      rw [code]
      obtain ⟨zs, zb⟩ := zeros_spec (32 * fields.length + 32) (by omega)
      have rootOne : ∀ f ∈ fields, ∀ s', s' + fixedWidth f ≤ b.size →
          (rootsOf f b s' (fixedWidth f) 1).size = 32 ∧
            nodeOf (rootsOf f b s' (fixedWidth f) 1) 0 0 = recordRoot f (recordBytes b s' (fixedWidth f)) := by
        intro f m s' inside
        have := specs f m b s' (fixedWidth f) 1 ⟨small, Nat.le_refl _, by omega, fun two => absurd two (by decide),
          fun i li => by have : i = 0 := by omega
                         subst this; omega⟩
        refine ⟨this.1, ?_⟩
        rw [this.2 0 (by decide), Nat.mul_zero, Nat.add_zero]
      obtain ⟨ls, _, ln⟩ := fieldLeaves_spec b start fields rootOne widths wfs fields (fun f m => m) 0
        (zeros (32 * fields.length + 32)) 0 (by omega) (by rw [zs]; omega) (fun x _ lx => zb x (by rw [zs] at lx; exact lx))
      obtain ⟨ms, md⟩ := merkleizeDepth_spec _ fields.length (depthFor fields.length) (le_two_pow_depthFor _)
        (by rw [ls, zs]; omega) (by rw [ls, zs]; omega)
      refine ⟨by rw [ms], fun i li => ?_⟩
      have : i = 0 := by omega
      subst this
      rw [nodeOf_single _ ms, md, Nat.mul_zero, Nat.add_zero, width]
      simp only [recordRoot]
      rw [fieldsArray]
      congr 1
      apply Array.ext
      · simp
      · intro k lk _
        simp only [nodesFrom, Array.getElem_ofFn]
        have := ln k (by simpa using lk)
        simp only [Nat.zero_add, Nat.add_zero] at this
        rw [this]
        rfl
    · -- Many records: one column per field, then the field tree across them.
      have many : 2 ≤ count := by have := run.nonempty; omega
      have code : rootsOf (.container names fields) b start stride count =
          columnTreeTo (fieldColumns fields b start stride count 0) count (depthFor fields.length) := by
        rw [rootsOf]; simp [single]
      rw [code]
      obtain ⟨len, get⟩ := fieldColumns_get b start stride count fields 0
      have spread := run.spread many
      rw [width] at spread
      have columnRun : ∀ k (h : k < fields.length),
          Run b (fixedWidth fields[k]) (start + offsetOf fields k) stride count :=
        fun k lk => ⟨small, run.nonempty, run.strideIn,
          fun _ => by have := offsetOf_le fields k lk; omega,
          fun i li => by
            have := run.inside i li
            rw [width] at this
            have := offsetOf_le fields k lk
            omega⟩
      let leaves := fun i => Array.ofFn (n := fields.length) fun k =>
        recordRoot fields[k] (recordBytes b (start + stride * i + offsetOf fields k) (fixedWidth fields[k]))
      have tree := columnTreeTo_spec (fieldColumns fields b start stride count 0) count (depthFor fields.length) leaves
        (by omega) (fun i _ => by simp [leaves, len]) (by rw [len]; exact nonempty)
        ⟨fun c h => by
            rw [get c (by omega) h]
            exact (specs _ (List.getElem_mem _) b _ stride count
              (by rw [Nat.zero_add]; exact columnRun c (by omega))).1,
          fun c h i li => by
            have lc : c < fields.length := by omega
            rw [get c lc h, Nat.zero_add,
              (specs _ (List.getElem_mem _) b _ stride count (columnRun c lc)).2 i li,
              Nat.pow_zero, Nat.mul_one, Nat.zero_add, subtreeAt_leaf]
            simp only [leaves, Array.getElem?_ofFn, lc]
            simp only [dite_true, Option.getD_some]
            congr 2
            omega⟩
        (by rw [len]; exact Nat.le_refl _)
      refine ⟨tree.1, fun i li => ?_⟩
      rw [tree.2 i li, width]
      simp only [recordRoot]
      rw [fieldsArray]
  -- An empty field list has no members.
  | nil => rename_i member _ _; simp at member
  | cons field fields ihHead ihTail =>
    -- A member field is the head or in the tail, by induction.
    rename_i held member p sound
    rcases List.mem_cons.mp member with here | later
    · subst here; exact ihHead p sound
    · exact ihTail held later p sound

/-- Long runs of fixed-size records, rooted a chunk at a time, give the same roots. -/
theorem chunkedRoots_spec (d : Desc) (p : plain d = true) (sound : d.wellFormed = .ok ()) :
    RootsSpec d (chunkedRoots d) :=
  chunked_of_roots d (rootsOf_spec d p sound)

/--
Node i of the native roots of a run is the specification's root of record i, when the record decodes.

A record that passes the native decoding check decodes, by the decoding check's own theorem.
-/
theorem rootsOf_hashTreeRoot (d : Desc) (p : plain d = true) (sound : d.wellFormed = .ok ())
    (b : ByteArray) (start stride count : Nat) (run : Run b (fixedWidth d) start stride count) (i : Nat)
    (record : i < count) (valid : validateRange d b (start + stride * i) (start + stride * i + fixedWidth d) = .ok ()) :
    ∃ v, deserialize d (recordBytes b (start + stride * i) (fixedWidth d)) = .ok v ∧
      Ssz.hashTreeRoot d v = .ok (nodeOf (rootsOf d b start stride count) 0 i) ∧
      Ssz.hashTreeRoot d v = .ok (nodeOf (chunkedRoots d b start stride count) 0 i) := by
  -- A record that passes the check decodes, with no refusal.
  have agrees := validate_sound d b (start + stride * i) (start + stride * i + fixedWidth d) (by omega)
    (run.inside i record)
  rw [valid] at agrees
  cases decoded : deserialize d (Native.slice b (start + stride * i) (start + stride * i + fixedWidth d)) with
  | error e => rw [decoded] at agrees; cases agrees
  -- Its root is the root read from its bytes, which is the node the native roots hold.
  | ok v =>
    have root := recordRoot_spec d p sound _ v decoded d.nesting (Nat.le_refl _)
    refine ⟨v, rfl, ?_, ?_⟩
    · rw [← hashTreeRootAt_eq_hashTreeRoot d v d.nesting (Nat.le_refl _), root, (rootsOf_spec d p sound b start stride count run).2 i record]
    · rw [← hashTreeRootAt_eq_hashTreeRoot d v d.nesting (Nat.le_refl _), root, (chunkedRoots_spec d p sound b start stride count run).2 i record]

end Ssz.Native
