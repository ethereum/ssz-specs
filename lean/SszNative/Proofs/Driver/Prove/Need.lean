import SszNative.Proofs.Driver.Prove.Discharge
import SszNative.Proofs.Driver.Prove.Scratch

/-!
The scratch the walk to a node needs, level by level, and why the prover's scratch bound covers it.

At each level the walk writes a layout record, then either roots the leaves under it or hands a child's walk a job and
the scratch past it.
A level's need is twice the most its type needs at once, a node per byte of the encoding, and a fixed amount per level
of nesting.
Each child's need, plus the record and the job, fits its parent's.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.ProveProof

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Plan

set_option maxRecDepth 20000

/-! ### The bound -/

/-- The most a value of a type needs at once over an encoding of a size: its root's scratch, or the path's. -/
def walkMost (d : Desc) (size : Nat) : Nat := max (varNeed d size) (deepNeed d)

/-- The scratch the walk to a node of a type needs past its job, over an encoding of a size. -/
def walkNeed (d : Desc) (size : Nat) : Nat := 2 * walkMost d size + 32 * size + 8192 * d.nesting

/-- A saturated value below the cap is the value. -/
theorem sat_eq {x : Nat} (h : sat x < scratchCap) : sat x = x := by
  simp only [sat] at h ⊢; omega

/-- A type's nesting is at most the deepest of a list holding it. -/
theorem nesting_le_deepest : ∀ (fs : List Desc) (f : Desc), f ∈ fs → f.nesting ≤ Desc.deepestNesting fs
  | [], _, h => by simp at h
  | g :: rest, f, h => by
    simp only [Desc.deepestNesting]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (nesting_le_deepest rest f h) (Nat.le_max_right _ _)

/-- A child type nests less deeply than its parent. -/
theorem IsChild.shallow {c d : Desc} (h : IsChild c d) : c.nesting < d.nesting := by
  cases d <;> simp only [IsChild] at h
  all_goals first
    | (subst h; simp [Desc.nesting])
    | (have := nesting_le_deepest _ _ h; simp only [Desc.nesting]; omega)

/-! ### The path's bound -/

/-- The most several types spend is at least the most so far. -/
theorem deepMost_ge : ∀ (fs : List Desc) (most : Nat), most ≤ deepMost fs most
  | [], _ => Nat.le_refl _
  | f :: rest, most => Nat.le_trans (Nat.le_max_right (deepNeed f) most) (deepMost_ge rest _)

/-- The most several types spend is at least each one's. -/
theorem deepMost_mem : ∀ (fs : List Desc) (most : Nat), ∀ f ∈ fs, deepNeed f ≤ deepMost fs most
  | [], _, _, h => by simp at h
  | g :: rest, most, f, h => by
    simp only [deepMost]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_left _ _) (deepMost_ge rest _)
    · exact deepMost_mem rest _ f h

/-- The path's bound covers the type's own fixed-size root. -/
theorem rootsNeed_le_deep (d : Desc) : rootsNeed d 1 ≤ deepNeed d := by
  have R := rootsNeed_le d 1
  cases d <;> simp only [deepNeed, sadd, smul, sat] <;> omega

/-- A plain type's root needs at most its path's bound. -/
theorem varNeed_le_deep {c : Desc} (pl : plain c = true) (size : Nat) : varNeed c size ≤ deepNeed c := by
  rw [varNeed_plain pl]; exact rootsNeed_le_deep c

/--
A child's path bound, doubled, with its parent's record and a job, fits its parent's doubled with a level to spare.

The parent's bound counts the child's, the parent's own fixed-size root, and a node per child.
-/
theorem deep_child {c d : Desc} (h : IsChild c d) (below : deepNeed d < scratchCap) :
    deepNeed c ≤ deepNeed d ∧ 2 * deepNeed c + recordBytes d + 48 ≤ 2 * deepNeed d + 8192 := by
  have R := rootsNeed_le d 1
  cases d <;> simp only [IsChild] at h
  case vector e l | list e l | progressiveList e l =>
    subst h
    simp only [deepNeed, recordBytes, layoutBytes, sadd, sat] at below ⊢
    omega
  case container names fs | progressiveContainer active names fs | compatibleUnion names fs =>
    have m := deepMost_mem fs 0 c h
    simp only [deepNeed, recordBytes, layoutBytes, sadd, smul, sat] at below ⊢
    omega

/-! ### The root's bound -/

/-- A child of a plain type is plain. -/
theorem IsChild.plain {c d : Desc} (h : IsChild c d) (pl : plain d = true) : plain c = true := by
  cases d with
  | vector e l => simp only [IsChild] at h; subst h; simpa [Ssz.Native.plain] using pl
  | container names fs =>
    simp only [IsChild] at h; simp only [Ssz.Native.plain] at pl; exact plainAll_mem _ pl c h
  | _ => simp only [IsChild] at h <;> simp [Ssz.Native.plain] at pl

/--
A child that is not plain needs, doubled, with its parent's record and a job, at most its parent's need doubled with a
level to spare.
-/
theorem var_child {c d : Desc} (h : IsChild c d) (notPlain : plain c = false) (size : Nat)
    (below : varNeed d size < scratchCap) :
    varNeed c size ≤ varNeed d size ∧ 2 * varNeed c size + recordBytes d + 48 ≤ 2 * varNeed d size + 8192 := by
  have dNot : plain d = false := by
    cases hp : plain d
    · rfl
    · rw [h.plain hp] at notPlain; cases notPlain
  cases d <;> simp only [IsChild] at h
  case vector e l =>
    subst h
    simp only [varNeed, dNot, Bool.false_eq_true, ite_false, recordBytes, layoutBytes, sadd, smul, sat] at below ⊢
    omega
  case list e l | progressiveList e l =>
    subst h
    have nb : c.isBasic = false := by
      cases hb : c.isBasic
      · rfl
      · rw [RootProof.plain_of_basic hb] at notPlain; cases notPlain
    simp only [varNeed, nb, notPlain, Bool.false_eq_true, ite_false, recordBytes, layoutBytes, sadd, smul, sat]
      at below ⊢
    omega
  case container names fs =>
    have m := fieldsVarNeed_mem fs size 0 c h
    simp only [varNeed, dNot, Bool.false_eq_true, ite_false, recordBytes, layoutBytes, sadd, smul, sat] at below ⊢
    omega
  case progressiveContainer active names fs =>
    have m := fieldsVarNeed_mem fs size 0 c h
    simp only [varNeed, recordBytes, layoutBytes, sadd, smul, sat] at below ⊢
    omega
  case compatibleUnion sel fs =>
    have m := fieldsVarNeed_mem fs size 0 c h
    simp only [varNeed, recordBytes, layoutBytes, sadd, sat] at below ⊢
    omega

/-! ### A child's walk -/

/-- A child needs at most what its parent needs at once. -/
theorem walkMost_child {c d : Desc} (h : IsChild c d) (size : Nat) (below : walkMost d size < scratchCap) :
    walkMost c size ≤ walkMost d size := by
  simp only [walkMost] at below ⊢
  have dc := (deep_child h (by omega)).1
  by_cases v : varNeed c size ≤ deepNeed c
  · omega
  · have np : plain c = false := by
      cases hp : plain c
      · rfl
      · exact absurd (varNeed_le_deep hp size) v
    have vc := (var_child h np size (by omega)).1
    omega

/-- A child's walk, with its parent's record and the job before it, fits its parent's walk. -/
theorem walkNeed_child {c d : Desc} (h : IsChild c d) (size : Nat) (below : walkMost d size < scratchCap) :
    walkNeed c size + recordBytes d + 48 ≤ walkNeed d size := by
  have sh := h.shallow
  simp only [walkNeed]
  simp only [walkMost] at below ⊢
  have dc := (deep_child h (by omega)).2
  by_cases v : varNeed c size ≤ deepNeed c
  · have : 8192 * c.nesting + 8192 ≤ 8192 * d.nesting := by omega
    omega
  · have np : plain c = false := by
      cases hp : plain c
      · rfl
      · exact absurd (varNeed_le_deep hp size) v
    have vc := (var_child h np size (by omega)).2
    have : 8192 * c.nesting + 8192 ≤ 8192 * d.nesting := by omega
    omega

/-! ### A level's leaves -/

/-- Values listed under a sequence's tree are at most its count. -/
theorem elementSlots_count (element : Desc) (b : ByteArray) (start stop count : Nat) :
    (elementSlots element b start stop count).count ≤ count := by
  simp only [elementSlots]
  split
  · simp [Slots.count]
  · simp only [Slots.count, List.length_map, bodyRanges, List.length_zip, List.length_append, List.length_drop,
      List.length_range, List.length_cons, List.length_nil]
    omega

/-- A list's values under its tree are at most the node bound over the whole encoding. -/
theorem elementCount_le_nodes {element : Desc} {b : ByteArray} {start stop size : Nat}
    (notBasic : element.isBasic = false) (ordered : start ≤ stop) (inside : stop ≤ size)
    (table : element.fixedSize = none → start + 4 * elementCount element b start stop ≤ stop)
    (small : size < 2 ^ 62) : elementCount element b start stop ≤ nodesBound element size := by
  have cap : scratchCap = 2 ^ 62 := rfl
  simp only [nodesBound, notBasic, Bool.false_eq_true, ite_false]
  by_cases fx : hasWidth element = true
  · have hs : element.fixedSize = some (fixedWidth element) := by rw [fixedSize_eq, ite_eq_left fx]
    simp only [elementCount, hs, ite_eq_left fx]
    have le := satWidth_le_width element
    by_cases z : fixedWidth element = 0
    · simp [z]
    · have nz : satWidth element ≠ 0 := fun h => z (width_zero_of_sat element h)
      simp only [beq_iff_eq, z, ite_false, nz, sat]
      have a1 : (stop - start) / fixedWidth element ≤ size / fixedWidth element :=
        Nat.div_le_div_right (by omega)
      have a2 : size / fixedWidth element ≤ size / satWidth element :=
        Nat.div_le_div_left le (Nat.pos_of_ne_zero nz)
      have a3 : size / satWidth element ≤ size := Nat.div_le_self _ _
      omega
  · have hs : element.fixedSize = none := by rw [fixedSize_eq, ite_eq_right fx]
    have t := table hs
    simp only [elementCount, hs, ite_eq_right fx, sat, bytesPerOffset]
    split
    · omega
    · have : offsetAt b start / 4 = elementCount element b start stop := by
        simp only [elementCount, hs, bytesPerOffset]; split <;> simp_all
      omega

/-- A bit list's bits fill at most one byte past its range. -/
theorem bitCount_le (b : ByteArray) (start stop : Nat) : (bitCount b start stop + 7) / 8 ≤ stop - start + 1 := by
  have hb : highestBit (b.get! (stop - 1)) < 8 := by
    have := highestBit_lt (b.get! (stop - 1)).toNat (b.get! (stop - 1)).toNat_lt
    simpa using this
  simp only [bitCount]
  omega

/-- A vector of composite values has room in its root's bound for a tree over its values. -/
theorem vector_tree (el : Desc) (n size : Nat) (nb : el.isBasic = false)
    (hv : varNeed (.vector el n) size < scratchCap) : 64 * n + 4640 ≤ varNeed (.vector el n) size := by
  simp only [varNeed] at hv ⊢
  split at hv
  · rename_i pl
    rw [ite_eq_left pl]
    simp only [rootsNeed, nb, Bool.false_eq_true, ite_false, ite_true] at hv ⊢
    generalize (if sat n ≤ recordsPerChunk then rootsNeed el (sat n)
      else sadd (smul 32 (sat n)) (rootsNeed el recordsPerChunk)) = chunks at hv ⊢
    simp only [treeNeed, RootProgressive.spineBytes, zeroHeights, sadd, smul, sat] at hv ⊢
    omega
  · rename_i pl
    rw [ite_eq_right pl]
    generalize varNeed el size = v at hv ⊢
    simp only [treeNeed, RootProgressive.spineBytes, zeroHeights, sadd, smul, sat] at hv ⊢
    omega

/-- A struct has room in its root's bound for a tree over its fields. -/
theorem container_tree (names : List String) (fs : List Desc) (size : Nat)
    (hv : varNeed (.container names fs) size < scratchCap) :
    64 * fs.length + 4640 ≤ varNeed (.container names fs) size := by
  simp only [varNeed] at hv ⊢
  split at hv
  · rename_i pl
    rw [ite_eq_left pl]
    simp only [rootsNeed, ite_true] at hv ⊢
    generalize fieldsRootsNeed fs 1 0 = most at hv ⊢
    simp only [treeNeed, RootProgressive.spineBytes, zeroHeights, sadd, smul, sat] at hv ⊢
    omega
  · rename_i pl
    rw [ite_eq_right pl]
    generalize fieldsVarNeed fs size 0 = most at hv ⊢
    simp only [treeNeed, RootProgressive.spineBytes, zeroHeights, sadd, smul, sat] at hv ⊢
    omega

/-- What a level's tree has room for: few leaves, the record and the trees past it, and a node per leaf beside it. -/
theorem count_need {d : Desc} {b : ByteArray} {s e : Nat} {layout : EncodedLayout} (dec : Decoded d b s e layout)
    (small : 64 * b.size + 128 < 2 ^ 64) (below : walkMost d b.size < scratchCap) :
    layout.count < 2 ^ 57 ∧ 64 * layout.count + 4704 + recordBytes d ≤ 2 * walkMost d b.size + 32 * b.size + 8192 ∧
      32 * layout.count + 96 + recordBytes d ≤ walkMost d b.size + 32 * b.size + 8192 := by
  have laid := dec.laid
  have ins := dec.inside
  have ord := dec.ordered
  have V : varNeed d b.size ≤ walkMost d b.size := Nat.le_max_left _ _
  have cap : scratchCap = 2 ^ 62 := rfl
  -- A packed layout holds a node per 32 bytes of at most one byte past the range.
  have packed : ∀ x, x ≤ e - s + 1 → recordBytes d = 144 → layout.count = nodesFor x →
      layout.count < 2 ^ 57 ∧ 64 * layout.count + 4704 + recordBytes d ≤
        2 * walkMost d b.size + 32 * b.size + 8192 ∧
      32 * layout.count + 96 + recordBytes d ≤ walkMost d b.size + 32 * b.size + 8192 := fun x hx rb hc => by
    rw [hc, rb]; simp only [nodesFor]; omega
  generalize walkMost d b.size = W at V below packed ⊢
  cases d with
  | bool | uint _ | byteVector _ | byteList _ | bitVector _ =>
    simp only [layoutOf] at laid; cases laid
    exact packed (e - s) (by omega) rfl rfl
  | bitList _ | progressiveBitList _ =>
    simp only [layoutOf] at laid; cases laid
    exact packed _ (bitCount_le b s e) rfl rfl
  | vector el n =>
    simp only [layoutOf] at laid; cases laid
    simp only [encodedSequence]
    split
    · rename_i hb
      simp only [encodedSequence, hb, ↓reduceIte] at packed
      exact packed (e - s) (by omega) rfl rfl
    · rename_i nb
      simp only [Bool.not_eq_true] at nb
      simp only [EncodedLayout.count]
      -- A vector's count is its length, and its root's bound covers a tree over that many.
      have hc := elementSlots_count el b s e n
      have tree := vector_tree el n b.size nb (by omega)
      simp only [recordBytes, layoutBytes]
      omega
  | list el n | progressiveList el n =>
    simp only [layoutOf] at laid; cases laid
    simp only [encodedSequence]
    split
    · rename_i hb
      simp only [encodedSequence, hb, ↓reduceIte] at packed
      exact packed (e - s) (by omega) rfl rfl
    · rename_i nb
      simp only [Bool.not_eq_true] at nb
      simp only [EncodedLayout.count]
      -- A list's count is at most the node bound, and its root's bound covers a tree over that many.
      have acc := layoutAccepted_of dec.sound ord ins small dec.accepted
      have hc := elementSlots_count el b s e (elementCount el b s e)
      have cnt := elementCount_le_nodes (size := b.size) nb ord ins
        (fun hs => (acc el (elementCount el b s e) rfl).table hs) (by omega)
      have hv := Nat.lt_of_le_of_lt V below
      have tree : 64 * nodesBound el b.size + 4704 ≤ W := by
        simp only [varNeed] at hv V
        simp only [treeNeed, RootProgressive.spineBytes, zeroHeights, sadd, smul, sat] at hv V
        omega
      simp only [recordBytes, layoutBytes]
      omega
  | container names fs =>
    simp only [layoutOf, Bind.bind, Except.bind] at laid
    split at laid
    · cases laid
    · simp only [pure, Except.pure, Except.ok.injEq] at laid
      subst laid
      simp only [EncodedLayout.count, Slots.count, List.length_map, List.length_zip]
      have hv := Nat.lt_of_le_of_lt V below
      have tree := container_tree names fs b.size hv
      simp only [recordBytes, layoutBytes]
      omega
  | progressiveContainer active names fs =>
    simp only [layoutOf, Bind.bind, Except.bind] at laid
    split at laid
    · cases laid
    · simp only [pure, Except.pure, Except.ok.injEq] at laid
      subst laid
      simp only [EncodedLayout.count, Slots.count, placed_length]
      have hv := Nat.lt_of_le_of_lt V below
      have tree : 64 + 32 * fs.length + 64 * active.length + 4608 ≤ varNeed (.progressiveContainer active names fs) b.size := by
        simp only [varNeed] at hv ⊢
        simp only [treeNeed, RootProgressive.spineBytes, zeroHeights, sadd, smul, sat] at hv ⊢
        omega
      simp only [recordBytes, layoutBytes]
      omega
  | compatibleUnion sel opts =>
    simp only [layoutOf, Bind.bind, Except.bind] at laid
    split at laid
    · cases laid
    · simp only [pure, Except.pure, Except.ok.injEq] at laid
      subst laid
      simp only [EncodedLayout.count, Slots.count, List.length_singleton, recordBytes, layoutBytes]
      omega

/-- A run of plain values rooted together needs at most what its sequence needs at once. -/
theorem chunk_need {d : Desc} {b : ByteArray} {s e : Nat} {layout : EncodedLayout} (dec : Decoded d b s e layout)
    (small : 64 * b.size + 128 < 2 ^ 64) (below : walkMost d b.size < scratchCap) {element : Desc}
    {start width count : Nat}
    (nested : layout.leaves = .nested (.stride element start width count)) (pl : plain element = true) :
    chunkNeed element count ≤ walkMost d b.size := by
  have laid := dec.laid
  have cap : scratchCap = 2 ^ 62 := rfl
  -- A run of one value needs the value's own fixed-size root, which the path's bound counts.
  have one : ∀ c, IsChild element c → walkMost c b.size < scratchCap →
      rootsNeed element 1 ≤ walkMost c b.size := fun c h lt => by
    have := (deep_child h (Nat.lt_of_le_of_lt (Nat.le_max_right _ _) lt)).1
    have := rootsNeed_le_deep element
    simp only [walkMost]; omega
  have Vd : varNeed d b.size ≤ walkMost d b.size := Nat.le_max_left _ _
  unfold chunkNeed
  cases d with
  | vector el n =>
    simp only [layoutOf] at laid; cases laid
    simp only [encodedSequence] at nested
    split at nested
    · cases nested
    · rename_i nb
      simp only [Bool.not_eq_true] at nb
      simp only [EncodedLeaves.nested.injEq, elementSlots] at nested
      split at nested
      · simp only [Slots.stride.injEq] at nested
        obtain ⟨rfl, -, -, rfl⟩ := nested
        have r1 := one (.vector el n) rfl below
        have hv : varNeed (.vector el n) b.size < scratchCap :=
          Nat.lt_of_le_of_lt (Nat.le_max_left _ _) below
        have dpl : plain (.vector el n) = true := by simpa [plain] using pl
        have rest : rootsNeed el (min n recordsPerChunk) ≤ varNeed (.vector el n) b.size := by
          simp only [varNeed, dpl, ite_true] at hv ⊢
          simp only [rootsNeed, nb, Bool.false_eq_true, ite_false, ite_true] at hv ⊢
          have chunk : recordsPerChunk = 1024 := rfl
          by_cases hn : n ≤ scratchCap
          · have sn : sat n = n := by simp only [sat]; omega
            rw [sn] at hv ⊢
            by_cases small : n ≤ recordsPerChunk
            · rw [ite_eq_left small] at hv ⊢
              rw [Nat.min_eq_left small]
              generalize rootsNeed el n = r at hv ⊢
              simp only [sadd, sat] at hv ⊢
              omega
            · rw [ite_eq_right small] at hv ⊢
              rw [Nat.min_eq_right (by omega)]
              generalize rootsNeed el recordsPerChunk = r at hv ⊢
              generalize (if n = 0 then 0 else _) = x at hv ⊢
              simp only [treeNeed, sadd, smul, sat] at hv ⊢
              clear one r1 dec below cap
              generalize RootProgressive.spineBytes + 32 * zeroHeights = k at hv ⊢
              generalize scratchCap = C at hv ⊢
              omega
          · exfalso
            have sn : sat n = scratchCap := by simp only [sat]; omega
            rw [sn] at hv
            generalize (if scratchCap ≤ recordsPerChunk then _ else _) = x at hv
            simp only [treeNeed, sadd, smul, sat, cap] at hv
            omega
        have := Nat.le_max_left (varNeed (.vector el n) b.size) (deepNeed (.vector el n))
        simp only [walkMost] at r1 ⊢
        omega
      · cases nested
  | list el n | progressiveList el n =>
    simp only [layoutOf] at laid; cases laid
    simp only [encodedSequence] at nested
    split at nested
    · cases nested
    · rename_i nb
      simp only [Bool.not_eq_true] at nb
      simp only [EncodedLeaves.nested.injEq, elementSlots] at nested
      split at nested
      · simp only [Slots.stride.injEq] at nested
        obtain ⟨rfl, -, -, rfl⟩ := nested
        have acc := layoutAccepted_of dec.sound dec.ordered dec.inside small dec.accepted
        have cnt := elementCount_le_nodes (size := b.size) nb dec.ordered dec.inside
          (fun hs => (acc el (elementCount el b s e) rfl).table hs) (by omega)
        have grow := chunkNeed_mono el cnt
        have hv := Vd
        have lt := Nat.lt_of_le_of_lt hv below
        unfold chunkNeed at grow
        simp only [varNeed, nb, pl, Bool.false_eq_true, ite_false, ite_true] at hv lt
        generalize max (rootsNeed el 1) (rootsNeed el (min (nodesBound el b.size) recordsPerChunk)) = E at hv lt grow
        generalize treeNeed (nodesBound el b.size) = t at hv lt
        generalize smul 32 (nodesBound el b.size) = u at hv lt
        simp only [sadd, sat] at hv lt
        clear one dec below acc cnt
        generalize scratchCap = C at hv lt
        omega
      · cases nested
  | container _ _ | progressiveContainer _ _ _ | compatibleUnion _ _ =>
    simp only [layoutOf, Bind.bind, Except.bind] at laid
    split at laid
    · cases laid
    · simp only [pure, Except.pure, Except.ok.injEq] at laid
      subst laid
      cases nested
  | _ => simp only [layoutOf] at laid; cases laid; cases nested

/--
The prover's scratch bound, when below the cap, holds a walk's job, the walk over a type nesting at most 64 deep, and a
node to spare.
-/
theorem proveScratch_need {d : Desc} {size : Nat} (below : proveScratch d size < scratchCap)
    (deep : d.nesting ≤ 64) : walkMost d size < scratchCap ∧ walkNeed d size + 64 ≤ proveScratch d size := by
  simp only [proveScratch, rootScratch] at below ⊢
  simp only [walkNeed, walkMost]
  generalize max (varNeed d size) (deepNeed d) = M at below ⊢
  simp only [sadd, smul, sat] at below ⊢
  generalize d.nesting = n at deep
  generalize scratchCap = C at below ⊢
  omega

/--
A level's scratch past its record holds the trees the walk builds there, and the leaves under the layout, with a node
to spare.
-/
theorem layout_need {d : Desc} {b : ByteArray} {s e : Nat} {layout : EncodedLayout} (dec : Decoded d b s e layout)
    (small : 64 * b.size + 128 < 2 ^ 64) (usize : USize.size = 2 ^ 64) (below : walkMost d b.size < scratchCap) :
    layout.count < 2 ^ 57 ∧ 64 * layout.count + 4704 + recordBytes d ≤ walkNeed d b.size ∧
      LeavesNeed layout (walkNeed d b.size - recordBytes d - 32) := by
  obtain ⟨cs, qa, qb⟩ := count_need dec small below
  have one := nesting_pos d
  have lvl : 8192 ≤ 8192 * d.nesting := by omega
  have big : 2 * walkMost d b.size + 32 * b.size + 8192 ≤ walkNeed d b.size := by simp only [walkNeed]; omega
  have rs : RootProof.Small b := by simp only [RootProof.Small]; rw [usize]; exact small
  refine ⟨cs, by omega, fun slots nested => ⟨fun _ i c s' e' at_ => ?_, fun element start width count hs pl => ?_⟩⟩
  · -- A value rooted alone needs at most what its parent needs at once.
    have kid := layout_children dec.sound dec.ordered dec.inside rs dec.accepted dec.laid nested at_
    have m1 := varNeed_mono c (show e' - s' ≤ b.size by have := kid.inside; omega)
    have m2 : varNeed c b.size ≤ walkMost c b.size := Nat.le_max_left _ _
    have m3 := walkMost_child kid.child b.size below
    generalize walkNeed d b.size = N at big ⊢
    generalize walkMost d b.size = W at below qa qb big m3
    clear dec kid at_ nested
    generalize scratchCap = C at below ⊢
    omega
  · -- A run rooted together needs at most what its sequence needs at once.
    subst hs
    have ch := chunk_need dec small below nested pl
    have counted : layout.count = count := by simp [EncodedLayout.count, nested, Slots.count]
    rw [counted] at qb
    generalize walkNeed d b.size = N at big ⊢
    generalize walkMost d b.size = W at below qa qb big ch
    clear dec nested
    generalize scratchCap = C at below ⊢
    omega

end EthLib.Consensus.Ssz.Native.Driver.ProveProof
