import SszNative.Proofs.Root.Variable.Elements

/-! The leaves of a counted sequence, as the root reads them and as the specification lays them out. -/

namespace Ssz.Native.RootProof

open Ssz Ssz.Native

variable (facts : Facts)

/-- The capacity a sequence's tree has, in nodes, for a count of elements. -/
def capacityOf (element : Desc) (count : Nat) : Nat :=
  if element.isBasic then chunksForBytes (count * element.itemLength) else count

/-- A list of well-formed elements spends at least a byte per element. -/
theorem list_count_le {element : Desc} {limit : Option Nat} {data : Bytes} {slices : List Bytes}
    (sound : element.wellFormed = .ok ()) (read : listSlices element limit data = .ok slices) :
    slices.length ≤ data.size := by
  simp only [listSlices, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure,
    Except.pure] at read
  -- An oversized range is refused, and an empty one holds no elements.
  split at read
  · cases read
  split at read
  · cases read; simp
  split at read
  -- Fixed-size elements are counted by a positive width, so at most one per byte.
  · rename_i width fixed
    have positive := fixedSize_pos_of_wellFormed sound fixed
    repeat' (first | (split at read) | (cases read; simp; exact Nat.div_le_self _ _) | (cases read))
  -- Elements found through offsets take four bytes each for their offsets.
  · repeat' (first | (split at read) | (cases read))
    all_goals
      rename_i spans
      have := offsetSpans_length spans
      simp only [List.length_map, List.length_zip, List.length_range, this, Nat.min_self, readOffsets]
      simp_all [bytesPerOffset]
      omega

/-- A type rooted as columns has a fixed size. -/
theorem hasWidth_of_plain (d : Desc) : plain d = true → hasWidth d = true := by
  induction d using Desc.rec (motive_2 := fun fields => plainAll fields = true → allHaveWidth fields = true) with
  -- Types and their field lists are handled together, by mutual induction.
  | nil => rfl
  | cons field fields ihHead ihTail =>
    rename_i both
    simp only [plainAll, Bool.and_eq_true] at both
    simp [allHaveWidth, ihHead both.1, ihTail both.2]
  -- Plain vectors and structs have fixed-size parts, and every other plain type is a scalar or a byte or bit vector.
  | vector element length ih => intro p; simp only [plain] at p; simp [hasWidth, ih p]
  | container names fields ih => intro p; simp only [plain] at p; simp [hasWidth, ih p]
  | _ => intro p; simp_all [plain, hasWidth]

include facts in
/--
The leaves of a decoded counted sequence.

The root reads them as one buffer of nodes, with a count and a capacity.
The specification lays them out as packed bytes or nested roots, under the same capacity.
-/
theorem sequence_leaves (element : Desc) (ih : Agrees element) (sound : element.wellFormed = .ok ())
    (b : ByteArray) (start stop : Nat) (ordered : start ≤ stop) (inside : stop ≤ b.size) (small : Small b)
    (limit : Option Nat) (slices : List Bytes) (values : List Value)
    (cut : listSlices element limit (slice b start stop) = .ok slices)
    (decoded : deserializeEach element slices = .ok values) (cap : Nat) (positions : Option Nat)
    (mixin : Option Bytes) :
    elementCount element b start stop = values.length ∧
      (sequenceNodes element b start stop cap).2.2 = capacityOf element cap ∧
      (sequenceNodes element b start stop cap).2.1 ≤ capacityOf element values.length ∧
      32 * (sequenceNodes element b start stop cap).2.1 ≤ (sequenceNodes element b start stop cap).1.size ∧
      ((sequenceNodes element b start stop cap).2.1 = 0 ∨ (sequenceNodes element b start stop cap).1.size < USize.size) ∧
      ∃ leaves, sequenceLayout element values positions mixin =
          .ok ⟨leaves, positions.map (capacityOf element), mixin⟩ ∧
        leafChunks leaves = .ok (nodesFrom (sequenceNodes element b start stop cap).1 0
          (sequenceNodes element b start stop cap).2.1) := by
  -- The slice has the range's size, and decoding spends a byte per element.
  have size := slice_size b start stop inside
  have few := list_count_le sound cut
  obtain ⟨lengths, each⟩ := deserializeEach_get element slices values decoded
  -- The check accepted ranges cutting the same slices.
  have agree := listRanges_cut element limit b start stop ordered inside
  rw [cut] at agree
  cases ranged : listRanges element limit b start stop with
  | error e => simp [ranged, Except.map, CutAgree] at agree
  | ok r =>
  simp only [ranged, Except.map, CutAgree] at agree
  obtain ⟨sliced, within⟩ := agree
  obtain ⟨counted, rangesEq⟩ := elementRanges_list element limit b start stop r ranged
  -- The count the root reads is the number of decoded elements.
  have countEq : elementCount element b start stop = values.length := by
    rw [counted, lengths, sliced, List.length_map]
  refine ⟨countEq, ?_⟩
  unfold Small at small
  by_cases basic : element.isBasic = true
  · -- Basic elements: the encoding's bytes, packed.
    obtain ⟨wrote, packs, sized⟩ := basic_packing element basic sound _ limit slices values cut decoded
    obtain ⟨nodes, packedSize⟩ := packRange_nodes b start stop ordered inside (by omega)
    rw [sequenceNodes.eq_def]
    simp only [basic, if_true, capacityOf]
    refine ⟨by rw [nodesFor_eq], ?_, ?_, ?_, ?_⟩
    · rw [← size, sized, lengths, nodesFor_eq]; exact Nat.le_refl _
    · rw [packedSize]; omega
    · rw [packedSize]; simp only [nodesFor]; omega
    · refine ⟨.packed (packBytes (slice b start stop)), ?_, ?_⟩
      · simp only [sequenceLayout, basic, if_true, wrote, packs, Bind.bind, Except.bind, pure, Except.pure,
          MerkleLayout.packing]
        congr 3
        funext count
        simp [capacityOf, basic]
      · simp only [leafChunks]
        rw [nodes]
  · -- Other elements bring a root each, so their leaves are those roots.
    have notBasic : element.isBasic = false := by simpa using basic
    have layout : sequenceLayout element values positions mixin =
        .ok ⟨.nested (values.map fun v => some (element, v)), positions.map (capacityOf element), mixin⟩ := by
      simp only [sequenceLayout, notBasic, Bool.false_eq_true, if_false, MerkleLayout.nesting, pure, Except.pure]
      cases positions <;> simp [capacityOf, notBasic]
    rw [sequenceNodes.eq_def]
    simp only [notBasic, Bool.false_eq_true, if_false, capacityOf]
    have sizeLe : values.length ≤ stop - start := by omega
    by_cases isPlain : plain element = true
    · -- Plain elements: rooted as columns, a chunk of records at a time.
      simp only [isPlain, if_true, countEq]
      have fixed : element.fixedSize = some (fixedWidth element) := by
        rw [fixedSize_eq, if_pos (hasWidth_of_plain element isPlain)]
      have unfolded : elementRanges element b start stop values.length = (List.range values.length).map fun i =>
          (start + i * fixedWidth element, start + (i + 1) * fixedWidth element) := by
        unfold elementRanges; rw [fixed]
      have stride : r.toList = (List.range values.length).map fun i =>
          (start + i * fixedWidth element, start + (i + 1) * fixedWidth element) := by
        rw [← unfolded, ← countEq, rangesEq]
      -- Record i is the slice one width past record i - 1.
      have sliceAt : ∀ i (hi : i < slices.length), slices[i] = slice b (start + fixedWidth element * i)
          (start + fixedWidth element * i + fixedWidth element) := by
        intro i hi
        simp only [sliced, stride, List.getElem_map, List.getElem_range]
        rw [Nat.succ_mul, Nat.mul_comm i, Nat.add_assoc]
      have records : RecordsDecode element b start (fixedWidth element) values.length := by
        intro i small'
        have hi : i < slices.length := by omega
        have member : (start + i * fixedWidth element, start + (i + 1) * fixedWidth element) ∈ r.toList := by
          rw [stride]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr small', rfl⟩
        have bounds := (within _ member).2.2
        have e : (i + 1) * fixedWidth element = fixedWidth element * i + fixedWidth element := by
          rw [Nat.succ_mul, Nat.mul_comm]
        refine ⟨by rw [e] at bounds; omega, values[i], ?_⟩
        rw [← sliceAt i hi]
        exact each i hi small'
      by_cases empty : values.length = 0
      · -- No records: no leaves.
        have none : values = [] := List.eq_nil_of_length_eq_zero empty
        refine ⟨by simp, by omega, by omega, Or.inl empty, _, layout, ?_⟩
        subst none
        simp [leafChunks, nodesFrom]
        rfl
      obtain ⟨sized, rooted⟩ := facts.chunkedRoots element isPlain sound b start (fixedWidth element)
        values.length small (by omega) rfl records
      refine ⟨by simp, by omega, by rw [sized]; omega, Or.inr (by rw [sized]; omega), _, layout, ?_⟩
      simp only [leafChunks, Bind.bind, Except.bind, pure, Except.pure]
      rw [indexed_mapM element _ values 0 fun i h => by
        have hi : i < slices.length := by omega
        simp only [Nat.zero_add]
        apply rooted i h values[i]
        rw [← sliceAt i hi]
        exact each i hi h]
    · -- Other elements: one root per element, from its own range.
      simp only [isPlain, Bool.false_eq_true, if_false, countEq]
      rw [show elementRanges element b start stop values.length = r.toList by rw [← countEq, rangesEq]]
      have rooted := variableRoots_spec element ih sound b small r.toList values
        (fun p m => ⟨(within p m).2.1, by have := (within p m).2.2; omega⟩) (by rw [← sliced]; exact decoded)
      have sizedRoots := forall₂_size (fun _ _ h => rooted_size h) rooted
      obtain ⟨nodes, joined⟩ := joinNodes_nodes _ sizedRoots
      have count := Each.length_eq rooted
      refine ⟨by simp, by omega, by rw [joined, ← count]; omega, Or.inr (by rw [joined, ← count]; omega), _, layout,
        ?_⟩
      simp only [leafChunks, elements_mapM element rooted, Bind.bind, Except.bind, pure, Except.pure]
      rw [count, nodes]

-- Packed capacities grow with the count, and others are the count itself.
/-- A larger count never needs a smaller tree. -/
theorem capacityOf_mono (element : Desc) {a b : Nat} (le : a ≤ b) : capacityOf element a ≤ capacityOf element b := by
  unfold capacityOf
  split
  · exact Nat.div_le_div_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ le) _)
  · exact le

/-- The bytes of nodes a root returns, read whole. -/
theorem nodes_whole_size {nodes : ByteArray} {r : Bytes} (same : nodes.data = r) (sized : r.size = 32) :
    nodes.size = 32 := by
  rw [← ByteArray.size_data, same, sized]

/-- Nodes read from inside a buffer are whole nodes. -/
theorem nodesFrom_width (nodes : ByteArray) (offset count : Nat) (inside : offset + 32 * count ≤ nodes.size) :
    ∀ c ∈ nodesFrom nodes offset count, c.size = bytesPerChunk := by
  intro c member
  -- Each node is cut at a whole-node offset inside the buffer.
  obtain ⟨i, within, rfl⟩ := Array.mem_iff_getElem.mp member
  have : i < count := by simpa [nodesFrom] using within
  simp only [nodesFrom, Array.getElem_ofFn, ByteArray.data_extract, Array.size_extract, ByteArray.size_data]
  simp only [bytesPerChunk]
  omega

include facts in
/-- A list's root is the specification's. -/
theorem list_root (element : Desc) (limit : Nat) (ih : Agrees element)
    (sound : (Desc.list element limit).wellFormed = .ok ()) (b : ByteArray) (start stop : Nat) (v : Value)
    (ordered : start ≤ stop) (inside : stop ≤ b.size) (small : Small b)
    (read : deserialize (.list element limit) (slice b start stop) = .ok v) :
    Ssz.hashTreeRoot (.list element limit) v = .ok (rootOf (.list element limit) b start stop).data := by
  -- Decoding cuts the elements' slices, then decodes each.
  simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i slices cut
  split at read
  · cases read
  rename_i values decoded
  cases read
  -- The count stays under the limit, so the tree has room for the leaves.
  have bound := listSlices_bound cut
  have lengths := (deserializeEach_get element slices values decoded).1
  obtain ⟨counted, capacity, fits, inside', small', leaves, layout, chunks⟩ :=
    sequence_leaves facts element ih (wellFormed_list sound) b start stop ordered inside small _ slices values cut
      decoded limit (some limit) (some (lengthWord values.length))
  -- Both sides bound the tree by the limit's capacity, then mix in the count.
  rw [hashTreeRoot_unfold]
  simp only [merkleLayout, show ¬ values.length > limit by omega, if_false, layout, chunks, finishLayout,
    Option.map_some, Bind.bind, Except.bind, pure, Except.pure]
  have room := Nat.le_trans fits (capacityOf_mono element (show values.length ≤ limit by omega))
  rw [← capacity] at room
  have tree := bounded_root facts _ _ _ _ rfl room inside' small'
  rw [← capacity, tree, rootOf]
  simp only [counted]
  rw [hashPair_mixIn rfl (facts.lengthNode _) (bounded_size (nodesFrom_width _ _ _ (by omega)) tree) (by simp)]

include facts in
/-- A progressive list's root is the specification's. -/
theorem progressiveList_root (element : Desc) (limit : Option Nat) (ih : Agrees element)
    (sound : (Desc.progressiveList element limit).wellFormed = .ok ()) (b : ByteArray) (start stop : Nat)
    (v : Value) (ordered : start ≤ stop) (inside : stop ≤ b.size) (small : Small b)
    (read : deserialize (.progressiveList element limit) (slice b start stop) = .ok v) :
    Ssz.hashTreeRoot (.progressiveList element limit) v =
      .ok (rootOf (.progressiveList element limit) b start stop).data := by
  -- Decoding cuts the elements' slices, then decodes each.
  simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i slices cut
  split at read
  · cases read
  rename_i values decoded
  cases read
  obtain ⟨counted, _, _, inside', small', leaves, layout, chunks⟩ :=
    sequence_leaves facts element ih (wellFormed_progressiveList sound) b start stop ordered inside small _ slices
      values cut decoded 0 none (some (lengthWord values.length))
  have within := listSlices_within cut
  have countedValues := (deserializeEach_get element slices values decoded).1
  rw [← countedValues] at within
  have bound := boundCheck_of_withinBound limit values.length within
  -- Both sides build a progressive spine over the leaves, then mix in the count.
  rw [hashTreeRoot_unfold]
  simp only [merkleLayout, bound, layout, chunks, finishLayout, Option.map_none, Bind.bind, Except.bind, pure,
    Except.pure]
  have tree := progressive_root facts _ _ _ rfl inside' small'
  rw [rootOf]
  simp only [counted]
  rw [hashPair_mixIn tree (facts.lengthNode _) (by simp) (by simp)]

end Ssz.Native.RootProof
