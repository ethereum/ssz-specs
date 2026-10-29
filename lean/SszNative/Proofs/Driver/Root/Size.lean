import SszNative.Proofs.Driver.Root.RootsOf
import SszNative.Proofs.Root.Fixed

/-!
The Lean roots of fixed-size values take one node per value.

The roots driver writes each child's roots, then reads them back by their size, so the size must be known first.
It follows from the scratch bound: below the cap, no buffer the roots build is too large for a machine word.
Packed roots shrink their blocks one level at a time down to a node each.
A tree over one value's elements or fields is one node.
A tree across columns keeps one node per value at every level.
-/

namespace Ssz.Native.Driver

open Ssz.Native.Ir Ssz.Native.Asm

/-! ### Saturated products -/

/-- A saturated product below the cap, of two factors at least one, has its plain product below the cap. -/
theorem smul_lt_parts {a b : Nat} (h : smul a b < scratchCap) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a * b < scratchCap ∧ a < scratchCap ∧ b < scratchCap := by
  simp only [smul, sat] at h
  have pa := Nat.le_mul_of_pos_right a hb
  have pb := Nat.le_mul_of_pos_left b ha
  omega

/-! ### Packed roots -/

/-- Hashing the pairs of a level, level after level, halves the level each time. -/
theorem levels_size (L0 : ByteArray) (count depth : Nat) (small : L0.size < USize.size)
    (size0 : L0.size = count * (32 * 2 ^ depth)) :
    ∀ k ≤ depth, ((List.range k).foldl (fun level _ => hashPairs level 0 (level.size / 64).toUSize) L0).size =
      count * (32 * 2 ^ (depth - k)) := by
  intro k
  induction k with
  | zero => intro _; simpa using size0
  | succ k ih =>
    -- One more level hashes the pairs of the level below.
    intro le
    have size := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range k).foldl (fun level _ => hashPairs level 0 (level.size / 64).toUSize) L0 = L at size
    obtain ⟨e, he⟩ : ∃ e, depth - k = e + 1 := ⟨depth - k - 1, by omega⟩
    rw [show depth - (k + 1) = e by omega]
    rw [he, Nat.pow_succ] at size
    -- The level holds a pair per node of the next.
    have pairs : L.size / 64 = count * 2 ^ e := by
      rw [size, show count * (32 * (2 ^ e * 2)) = 64 * (count * 2 ^ e) by
        rw [Nat.mul_comm (2 ^ e) 2, ← Nat.mul_assoc 32, Nat.mul_left_comm]]
      omega
    have levelSmall : L.size < USize.size := by
      have : count * (32 * (2 ^ e * 2)) ≤ count * (32 * 2 ^ depth) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_left
        rw [← Nat.pow_succ]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      omega
    rw [usize_zero, pairs, hashPairs_size _ _ _ (by rw [← pairs]; omega), Nat.mul_left_comm]

/-- Packed roots below their scratch bound take one node per value. -/
theorem packedRoots_size (width : Nat) (b : ByteArray) (start stride : Nat) {count : Nat} (pos : 1 ≤ count)
    (usize : USize.size = 2 ^ 64) (below : packedNeed width count < scratchCap) :
    (packedRoots width (nodesFor width) b start stride count).size = 32 * count := by
  have capv := cap_eq
  have one : 1 ≤ 2 ^ depthFor (nodesFor width) := Nat.one_le_two_pow
  -- The gathered blocks are below the cap: one block per value, under twice a value's roots.
  have blocks : count * (32 * 2 ^ depthFor (nodesFor width)) < scratchCap ∧
      32 * 2 ^ depthFor (nodesFor width) < scratchCap := by
    unfold packedNeed at below
    dsimp only at below
    split at below
    · rename_i zero
      rw [zero, Nat.pow_zero] at one ⊢
      simp only [smul, sat] at below
      omega
    · have tail : smul (smul 2 count) (smul 32 (2 ^ depthFor (nodesFor width))) < scratchCap := by
        simp only [sadd, sat] at below; omega
      have outer := smul_lt_parts tail (by simp only [smul, sat]; omega) (by simp only [smul, sat]; omega)
      have left := smul_of_lt outer.2.1
      have right := smul_of_lt outer.2.2
      rw [left, right] at outer
      have := Nat.mul_le_mul_right (32 * 2 ^ depthFor (nodesFor width)) (show count ≤ 2 * count by omega)
      omega
  simp only [packedRoots]
  generalize depthFor (nodesFor width) = depth at blocks one ⊢
  have few := Nat.le_mul_of_pos_right count (show 0 < 32 * 2 ^ depth by omega)
  rw [levels_size _ count _ (by simp only [gather, gatherReference_size]; rw [toUSize_toNat _ (by omega),
      toUSize_toNat _ (by omega)]; omega)
    (by simp only [gather, gatherReference_size]; rw [toUSize_toNat _ (by omega), toUSize_toNat _ (by omega)])
    depth (Nat.le_refl _), Nat.sub_self, Nat.pow_zero, Nat.mul_one, Nat.mul_comm]

/-! ### Trees -/

/-- A tree across columns of one node per value keeps one node per value. -/
theorem columnTreeTo_size (columns : List ByteArray) (count depth : Nat) (small : 32 * count < USize.size)
    (sized : ∀ c (h : c < columns.length), columns[c].size = 32 * count) (nonempty : 1 ≤ columns.length)
    (deep : depthFor columns.length ≤ depth) : (columnTreeTo columns count depth).size = 32 * count :=
  -- Each value's leaves are its nodes across the columns, read back from the columns themselves.
  (columnTreeTo_spec columns count depth (fun i => Array.ofFn (n := columns.length) fun c => nodeOf columns[c] 0 i)
    small (fun _ _ => by simp) nonempty
    ⟨sized, fun c h i _ => by
      rw [Nat.pow_zero, Nat.mul_one, Nat.zero_add, subtreeAt_leaf]
      simp [h]⟩ deep).1

/-- A copy into a buffer, ending inside it, keeps the buffer's size whatever the source holds. -/
theorem copySlice_keeps_size (src dest : ByteArray) (so d len : Nat) (hd : d + len ≤ dest.size) :
    (src.copySlice so dest d len).size = dest.size := by
  change (src.copySlice so dest d len).data.size = dest.data.size
  simp only [ByteArray.copySlice, Array.size_append, Array.size_extract]
  have : src.data.size = src.size := rfl
  have : dest.data.size = dest.size := rfl
  omega

/-- A well-formed value that is its own root is at most one node wide. -/
theorem packsIntoNode_width (d : Desc) (packs : packsIntoNode d = true) (sound : d.wellFormed = .ok ()) :
    fixedWidth d ≤ 32 := by
  -- Integers come in the listed widths, and byte and bit vectors are bounded by the test itself.
  cases d with
  | uint w =>
    simp only [Desc.wellFormed] at sound
    split at sound
    · rename_i listed; simp only [fixedWidth]; simp at listed; omega
    · simp at sound
  | _ => simp_all [packsIntoNode, fixedWidth] <;> omega

/-- Writing a record's field leaves keeps the buffer's size, when every leaf lands inside it. -/
theorem fieldLeaves_size_at (b : ByteArray) (start : Nat) :
    ∀ (fields : List Desc), (∀ f ∈ fields, f.wellFormed = .ok ()) →
      ∀ (offset : Nat) (leaves : ByteArray) (node : Nat), 32 * (node + fields.length) ≤ leaves.size →
        (fieldLeaves fields b start offset leaves node).size = leaves.size
  | [], _, _, leaves, _, _ => by rw [fieldLeaves]
  | f :: rest, sound, offset, leaves, node, room => by
    -- This field's leaf lands inside its node, then the rest follow.
    rw [fieldLeaves]
    simp only [List.length_cons] at room
    have next : (if packsIntoNode f = true then b.copySlice (start + offset) leaves (32 * node) (fixedWidth f)
        else (rootsOf f b (start + offset) (fixedWidth f) 1).copySlice 0 leaves (32 * node) 32).size = leaves.size := by
      split
      · rename_i packs
        have := packsIntoNode_width f packs (sound f (by simp))
        exact copySlice_keeps_size _ _ _ _ _ (by omega)
      · exact copySlice_keeps_size _ _ _ _ _ (by omega)
    rw [fieldLeaves_size_at b start rest (fun g m => sound g (by simp [m])) _ _ _ (by rw [next]; omega), next]

/-! ### Every fixed-size type -/

/-- What the roots of a type give, below its scratch bound: one node per value. -/
def RootsSized (d : Desc) : Prop :=
  ∀ (b : ByteArray) (start stride count : Nat), 1 ≤ count → rootsNeed d count < scratchCap →
    (rootsOf d b start stride count).size = 32 * count

/-- A type rooted as packed values takes one node per value. -/
theorem packed_sized (d : Desc) (ok : Rootable d) (usize : USize.size = 2 ^ 64)
    (code : ∀ b start stride count, rootsOf d b start stride count =
      packedRoots (fixedWidth d) (nodesFor (fixedWidth d)) b start stride count)
    (need : ∀ count, rootsNeed d count = packedNeed (satWidth d) count) : RootsSized d := by
  intro b start stride count pos below
  rw [code]
  rw [need, satWidth_plain d ok.1 (width_narrow d ok.1 ok.2.2)] at below
  exact packedRoots_size _ b start stride pos usize below

/-- A chunked run of values, each chunk below its scratch bound, takes one node per value. -/
theorem chunkedRoots_size (d : Desc) (sized : RootsSized d) (b : ByteArray) (start stride count : Nat)
    (pos : 1 ≤ count) (below : rootsNeed d (min count recordsPerChunk) < scratchCap) :
    (chunkedRoots d b start stride count).size = 32 * count := by
  have chunk : recordsPerChunk = 1024 := rfl
  by_cases few : count ≤ recordsPerChunk
  · -- One chunk: the roots of the whole run.
    rw [chunkedRoots, if_pos few]
    rw [Nat.min_eq_left few] at below
    exact sized b start stride count pos below
  · -- Several chunks: each at most a full chunk, joined in order.
    rw [Nat.min_eq_right (by omega)] at below
    rw [chunkedRoots_join d b start stride count few,
      chunkJoin_size (fun done c lt _ hc => sized b _ stride c (by rw [hc, chunk]; omega)
        (Nat.lt_of_le_of_lt (rootsNeed_chunk d (by rw [hc]; exact Nat.min_le_left _ _)) below)) _
        (by rw [chunk]; omega)]
    rw [chunk]
    omega

/--
The roots of values of a fixed-size type take one node per value, below the type's scratch bound.

The bound keeps every buffer the roots build far below the word size, so no size wraps.
-/
theorem rootsOf_size (d : Desc) : Rootable d → USize.size = 2 ^ 64 → RootsSized d := by
  have capv := cap_eq
  -- Types and their field lists are handled together, by mutual induction.
  induction d using Desc.rec (motive_2 := fun fields =>
    ∀ f ∈ fields, Rootable f → USize.size = 2 ^ 64 → RootsSized f) with
  -- Scalars and byte or bit vectors are packed values.
  | bool | uint | byteVector | bitVector =>
    intro ok usize
    exact packed_sized _ ok usize (fun _ _ _ _ => by rw [rootsOf] <;> simp) (fun _ => by rw [rootsNeed] <;> simp)
  -- Every other type is never plain.
  | byteList | bitList | progressiveBitList | list | progressiveList | progressiveContainer | compatibleUnion =>
    intro ok; simp [Rootable, plain] at ok
  | vector element length ih =>
    intro ok usize
    obtain ⟨pl, wf, thin⟩ := ok
    have pe : plain element = true := by simpa [plain] using pl
    have se := wellFormed_vector wf
    have ne : narrow element = true := by simp only [narrow, Bool.and_eq_true] at thin; exact thin.2
    have sized := ih ⟨pe, se, ne⟩ usize
    have nz : 1 ≤ length := by
      apply Nat.pos_of_ne_zero
      rintro rfl
      simp [Desc.wellFormed, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at wf
    -- Basic elements pack, so the vector is a packed value.
    by_cases basic : element.isBasic = true
    · exact packed_sized _ ⟨pl, wf, thin⟩ usize (fun _ _ _ _ => by simp [rootsOf, basic])
        (fun _ => by simp [rootsNeed, basic, satWidth])
    have nb : element.isBasic = false := by simpa using basic
    intro b start stride count pos below
    simp only [rootsNeed, nb, Bool.false_eq_true, if_false] at below
    by_cases single : count = 1
    · -- One value: the tree over its elements' roots, one node.
      subst single
      rw [if_pos rfl] at below
      have parts : smul 32 (sat length) < scratchCap ∧
          (if sat length ≤ recordsPerChunk then rootsNeed element (sat length)
            else sadd (smul 32 (sat length)) (rootsNeed element recordsPerChunk)) < scratchCap := by
        simp only [sadd, sat] at below ⊢; omega
      have satLen : sat length = length := by
        have := parts.1
        rw [smul_of_lt this] at this
        exact sat_of_lt (by omega)
      rw [satLen] at parts
      have long := smul_of_lt parts.1
      rw [long] at parts
      have code : rootsOf (.vector element length) b start stride 1 =
          merkleizeDepth (chunkedRoots element b start (fixedWidth element) length) length (depthFor length) := by
        simp [rootsOf, nb]
      have roots : (chunkedRoots element b start (fixedWidth element) length).size = 32 * length := by
        apply chunkedRoots_size element sized b start _ length nz
        by_cases few : length ≤ recordsPerChunk
        · rw [Nat.min_eq_left few]; rw [if_pos few] at parts; exact parts.2
        · rw [Nat.min_eq_right (by omega)]; rw [if_neg few] at parts
          have := parts.2
          simp only [sadd, sat] at this; omega
      rw [code, (merkleizeDepth_spec _ length (depthFor length) (le_two_pow_depthFor _)
        (by rw [roots]; exact Nat.le_refl _)
        (by rw [roots]; omega)).1]
    · -- Several values: the tree across one column per element.
      rw [if_neg single] at below
      have parts : smul 32 count < scratchCap ∧ rootsNeed element count < scratchCap := by
        simp only [sadd, sat] at below; omega
      have wide := smul_of_lt parts.1
      rw [wide] at parts
      have code : rootsOf (.vector element length) b start stride count =
          columnTreeTo (elementColumns element b start stride count (fixedWidth element) length) count
            (depthFor length) := by
        simp [rootsOf, nb, single]
      obtain ⟨len, get⟩ := elementColumns_get element b start stride count (fixedWidth element) length
      rw [code]
      exact columnTreeTo_size _ count _ (by omega)
        (fun c h => by rw [get c h]; exact sized b _ stride count pos parts.2) (by rw [len]; exact nz)
        (by rw [len]; exact Nat.le_refl _)
  | container names fields ih =>
    intro ok usize
    obtain ⟨pl, wf, thin⟩ := ok
    have pf : plainAll fields = true := by simpa [plain] using pl
    have wfs := allWellFormed_mem fields (wellFormed_container wf)
    have nf : narrowAll fields = true := by simp only [narrow, Bool.and_eq_true] at thin; exact thin.2
    have sized : ∀ f ∈ fields, RootsSized f := fun f m =>
      ih f m ⟨plainAll_mem fields pf f m, wfs f m, narrow_mem fields nf f m⟩ usize
    have nonempty : 1 ≤ fields.length := by
      cases fields with
      | nil => simp [Desc.wellFormed, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at wf
      | cons _ _ => simp
    intro b start stride count pos below
    simp only [rootsNeed] at below
    by_cases single : count = 1
    · -- One record: the tree over its field leaves, one node.
      subst single
      rw [if_pos rfl] at below
      have parts : smul 32 (sat fields.length) < scratchCap := by simp only [sadd, sat] at below ⊢; omega
      have satLen : sat fields.length = fields.length := by
        have := parts
        rw [smul_of_lt this] at this
        exact sat_of_lt (by omega)
      rw [satLen] at parts
      rw [smul_of_lt parts] at parts
      have code : rootsOf (.container names fields) b start stride 1 =
          merkleizeDepth (fieldLeaves fields b start 0 (zeros (32 * fields.length + 32)) 0) fields.length
            (depthFor fields.length) := by
        rw [rootsOf]; simp
      have zs := (zeros_spec (32 * fields.length + 32) (by omega)).1
      have ls := fieldLeaves_size_at b start fields wfs 0 (zeros (32 * fields.length + 32)) 0 (by rw [zs]; omega)
      rw [code, (merkleizeDepth_spec _ fields.length (depthFor fields.length) (le_two_pow_depthFor _)
        (by rw [ls, zs]; omega) (by rw [ls, zs]; omega)).1]
    · -- Several records: the tree across one column per field.
      rw [if_neg single] at below
      have parts : smul 32 count < scratchCap ∧ fieldsRootsNeed fields count 0 < scratchCap := by
        simp only [sadd, sat] at below; omega
      have wide := smul_of_lt parts.1
      rw [wide] at parts
      have code : rootsOf (.container names fields) b start stride count =
          columnTreeTo (fieldColumns fields b start stride count 0) count (depthFor fields.length) := by
        rw [rootsOf]; simp [single]
      obtain ⟨len, get⟩ := fieldColumns_get b start stride count fields 0
      rw [code]
      exact columnTreeTo_size _ count _ (by omega)
        (fun c h => by
          rw [get c (by omega) h]
          exact sized _ (List.getElem_mem _) b _ stride count pos
            (Nat.lt_of_le_of_lt (fieldsRootsNeed_mem fields count 0 _ (List.getElem_mem _)) parts.2))
        (by rw [len]; exact nonempty) (by rw [len]; exact Nat.le_refl _)
  -- An empty field list has no members.
  | nil => rename_i member _ _; simp at member
  | cons field fields ihHead ihTail =>
    -- A member field is the head or in the tail, by induction.
    rename_i held member ok usize
    rcases List.mem_cons.mp member with here | later
    · subst here; exact ihHead ok usize
    · exact ihTail held later ok usize

/-- The roots a call's needs ask for take one node per value. -/
theorem RootsPre.sized {w : World} {mem : Memory} {d : Desc} {p base start stride count out ctx table zeros pad : Nat}
    {mask : UInt64} {b : ByteArray} (pre : RootsPre w mem d p base start stride count out ctx table zeros pad mask b)
    (ok : Rootable d) : (rootsOf d b start stride count).size = 32 * count :=
  rootsOf_size d ok pre.usize b start stride count pre.pos pre.below

end Ssz.Native.Driver
