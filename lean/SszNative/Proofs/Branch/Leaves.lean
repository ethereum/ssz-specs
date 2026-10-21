import SszNative.Branch
import SszNative.Proofs.Root.Main

/-! The leaves of a span of a tree, read from an encoding, are the specification's leaves of the decoded value. -/

namespace Ssz.Native.BranchProof

open Ssz Ssz.Native

/-- One position, as an encoding holds it and as the decoded value holds it: two gaps, or a range decoding to the value. -/
def SlotAgrees (b : ByteArray) : Option (Desc × Nat × Nat) → Option (Desc × Value) → Prop
  | none, none => True
  | some (d, s, e), some (d', v) =>
    d = d' ∧ d.wellFormed = .ok () ∧ s ≤ e ∧ e ≤ b.size ∧ deserialize d (slice b s e) = .ok v
  | _, _ => False

/-- The leaves of a tree, as an encoding holds them and as the decoded value lays them out. -/
def LeavesAgree (b : ByteArray) : EncodedLeaves → Leaves → Prop
  | .packed nodes count, .packed chunks =>
    RootProof.nodesFrom nodes 0 count = chunks ∧ 32 * count ≤ nodes.size ∧ nodes.size < USize.size
  | .nested slots, .nested values =>
    slots.count = values.length ∧
      (∀ i (h : i < values.length), ∃ x, slots.at i = some x ∧ SlotAgrees b x values[i]) ∧
      ∀ element start width count, slots = .stride element start width count → element.fixedSize = some width
  | _, _ => False

/-- A tree as an encoding lays it out and as the decoded value lays it out. -/
structure Corresponds (b : ByteArray) (E : EncodedLayout) (L : MerkleLayout) : Prop where
  /-- The same leaves. -/
  leaves : LeavesAgree b E.leaves L.leaves
  /-- The same capacity, or the same spine. -/
  limit : E.limit = L.limit
  /-- The same word mixed in. -/
  mixin : E.mixin.map ByteArray.data = L.mixin
  /-- Every buffer of the layout's leaves has machine-sized offsets. -/
  fits : 32 * E.count + 64 < USize.size

/-- Whether every value nested under a layout fits a budget. -/
def Deep (budget : Nat) (L : MerkleLayout) : Prop :=
  ∀ values, L.leaves = .nested values → ∀ d v, some (d, v) ∈ values → d.nesting ≤ budget

/-- The leaves of a layout count the same either way. -/
theorem count_eq {b : ByteArray} {E : EncodedLayout} {L : MerkleLayout} (c : Corresponds b E L) :
    E.count = L.leaves.count := by
  have agree := c.leaves
  unfold EncodedLayout.count
  -- Packed nodes count as many chunks, and nested slots as many values.
  match hE : E.leaves, hL : L.leaves with
  | .packed nodes n, .packed chunks =>
    rw [hE, hL] at agree
    rw [Leaves.count, ← agree.1]
    simp [RootProof.nodesFrom]
  | .nested slots, .nested values =>
    rw [hE, hL] at agree
    exact agree.1
  | .packed _ _, .nested _ => rw [hE, hL] at agree; exact absurd agree id
  | .nested _, .packed _ => rw [hE, hL] at agree; exact absurd agree id

/-- The slots hold no position past their count. -/
theorem Slots.at_none (slots : Slots) (i : Nat) (past : slots.count ≤ i) : slots.at i = none := by
  cases slots with
  | stride element start width count => simp [Slots.at, Slots.count] at *; omega
  | listed slots => simp [Slots.at, Slots.count] at *; exact past

/-- Items whose roots sit, one per node, in a buffer give that buffer's nodes. -/
theorem mapM_nodes {α : Type} (f : α → Except Err Bytes) (buf : ByteArray) :
    ∀ (xs : List α) (offset : Nat), (∀ i (h : i < xs.length),
      f xs[i] = .ok (buf.extract (offset + 32 * i) (offset + 32 * i + 32)).data) →
      xs.mapM f = .ok (RootProof.nodesFrom buf offset xs.length).toList
  | [], _, _ => by simp [RootProof.nodesFrom]; rfl
  | x :: rest, offset, rooted => by
    rw [List.length_cons, RootProof.nodesFrom_succ]
    -- The first item is the first node, and the rest start one node further.
    have head := rooted 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at head
    have tail := mapM_nodes f buf rest (offset + 32) fun i h => by
      have := rooted (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [this]
      congr 3 <;> omega
    simp only [List.mapM_cons, head, tail, Bind.bind, Except.bind, pure, Except.pure]

/-- A root read from a range of an encoding that decodes is a whole node, and the value's root. -/
theorem range_root (b : ByteArray) (small : RootProof.Small b) (d : Desc) (s e : Nat) (v : Value)
    (sound : d.wellFormed = .ok ()) (o : s ≤ e) (i : e ≤ b.size)
    (read : deserialize d (slice b s e) = .ok v) :
    Ssz.hashTreeRoot d v = .ok (rootOf d b s e).data ∧ (rootOf d b s e).size = 32 := by
  have rooted := RootProof.agrees RootProof.facts_hold d sound b s e v o i small read
  exact ⟨rooted, by rw [← ByteArray.size_data]; exact hashTreeRoot_size d v _ rooted⟩

/-- Joined nodes, read back node by node. -/
theorem joinNodes_node (rs : List ByteArray) (sized : ∀ r ∈ rs, r.size = 32) (j : Nat) (h : j < rs.length) :
    ((joinNodes rs).extract (32 * j) (32 * j + 32)).data = rs[j].data := by
  have := congrArg (fun a => a[j]?) (RootProof.joinNodes_nodes rs sized).1
  simp only [RootProof.nodesFrom, Array.getElem?_ofFn, h, ↓reduceDIte, Nat.zero_add, List.getElem?_toArray,
    List.getElem?_map, List.getElem?_eq_getElem h, Option.map_some, Option.some.injEq] at this
  exact this

/-- What the leaves of a span give, as a buffer and a count, and as the specification's chunks. -/
def SpanAgrees (budget : Nat) (L : MerkleLayout) (first last : Nat) (count : Nat) (p : ByteArray × Nat) : Prop :=
  layoutChunksAt budget L first (some last) = .ok (RootProof.nodesFrom p.1 0 p.2) ∧
    p.2 = min last count - first ∧ 32 * p.2 ≤ p.1.size ∧ (p.2 = 0 ∨ p.1.size < USize.size)

/-- Packed leaves of a span are the specification's chunks of that span. -/
theorem packed_span (budget : Nat) (nodes : ByteArray) (n : Nat) (chunks : Array Bytes) (limit : Option Nat)
    (mixin : Option Bytes) (same : RootProof.nodesFrom nodes 0 n = chunks) (inside : 32 * n ≤ nodes.size)
    (small : nodes.size < USize.size) (first last : Nat) :
    SpanAgrees budget ⟨.packed chunks, limit, mixin⟩ first last n
      (nodes.extract (32 * first) (32 * min last n), min last n - first) := by
  have sized : chunks.size = n := by rw [← same]; simp [RootProof.nodesFrom]
  refine ⟨?_, rfl, ?_, Or.inr ?_⟩
  · simp only [layoutChunksAt, Leaves.count, Option.getD_some, pure, Except.pure]
    congr 1
    rw [← same]
    apply Array.ext
    · simp [RootProof.nodesFrom]
    · intro j hl hr
      simp only [RootProof.nodesFrom, Array.getElem_ofFn, Array.getElem_extract, ByteArray.data_extract,
        Nat.zero_add]
      have hl' : j < min last n - first := by simpa [RootProof.nodesFrom] using hl
      -- Node j of the span is node first + j of the buffer.
      -- Node j of the span is node first + j of the buffer.
      rw [Array.extract_extract]
      have hn : 32 * min last n ≤ nodes.data.size := by simp only [ByteArray.size_data]; omega
      congr 1 <;> omega

  · simp only [ByteArray.size_extract]
    omega
  · simp only [ByteArray.size_extract]
    omega

/-- The specification's leaves of a span of nested values, given the buffer holding their roots. -/
theorem nested_chunks (budget : Nat) (values : List (Option (Desc × Value))) (limit : Option Nat)
    (mixin : Option Bytes) (deep : ∀ d v, some (d, v) ∈ values → d.nesting ≤ budget) (first last c : Nat)
    (counted : c = min last values.length - first) (buf : ByteArray)
    (rooted : ∀ i (h : i < c), RootProof.slotRoot (values[first + i]'(by omega)) =
      .ok (buf.extract (32 * i) (32 * i + 32)).data) :
    layoutChunksAt budget ⟨.nested values, limit, mixin⟩ first (some last) = .ok (RootProof.nodesFrom buf 0 c) := by
  simp only [layoutChunksAt, Option.getD_some, Bind.bind, Except.bind, pure, Except.pure]
  have len : ((values.drop first).take (last - first)).length = c := by simp; omega
  -- Position i of the span is position first + i of the layout.
  rw [mapM_nodes _ buf _ 0 (fun i h => by
    have here : ((values.drop first).take (last - first))[i] = values[first + i]'(by simp at h; omega) := by
      simp [List.getElem_take, List.getElem_drop]
    have r := rooted i (by omega)
    have mem : values[first + i]'(by simp at h; omega) ∈ values := List.getElem_mem _
    rw [here]
    simp only [Nat.zero_add]
    -- A gap is the zero node, and a nested value is rooted on the budget that covers it.
    generalize values[first + i]'(by simp at h; omega) = x at r mem
    match x with
    | none => simpa [RootProof.slotRoot] using r
    | some (d, v) =>
      simp only [RootProof.slotRoot] at r
      simp only
      rw [hashTreeRootAt_eq_hashTreeRoot d v budget (deep d v mem), r])]
  rw [len]

/-- Records one width apart, each decoding, have their roots read as columns or one by one. -/
theorem stride_span (b : ByteArray) (small : RootProof.Small b) (budget : Nat) (element : Desc)
    (start width cnt : Nat) (values : List (Option (Desc × Value))) (limit : Option Nat) (mixin : Option Bytes)
    (limit' : Option Nat) (mixin' : Option ByteArray) (counted : cnt = values.length)
    (each : ∀ i (h : i < values.length), ∃ x, (Slots.stride element start width cnt).at i = some x ∧
      SlotAgrees b x values[i])
    (fixed : element.fixedSize = some width)
    (deep : ∀ d v, some (d, v) ∈ values → d.nesting ≤ budget)
    (fits : 32 * cnt + 64 < USize.size) (first last : Nat) :
    SpanAgrees budget ⟨.nested values, limit, mixin⟩ first last cnt
      (leavesIn b ⟨.nested (.stride element start width cnt), limit', mixin'⟩ first last) := by
  -- Record first + i of the span decodes, from its own range.
  have record : ∀ i (h : i < min last cnt - first), element.wellFormed = .ok () ∧
      start + width * (first + i + 1) ≤ b.size ∧ ∃ v, values[first + i]'(by omega) = some (element, v) ∧
      deserialize element (slice b (start + width * (first + i)) (start + width * (first + i + 1))) = .ok v := by
    intro i h
    obtain ⟨x, tableEntry, agrees⟩ := each (first + i) (by omega)
    simp only [Slots.at, show first + i < cnt by omega, if_true, Option.some.injEq] at tableEntry
    subst tableEntry
    revert agrees
    cases values[first + i]'(by omega) with
    | none => simp [SlotAgrees]
    | some pair =>
      obtain ⟨d, v⟩ := pair
      simp only [SlotAgrees]
      rintro ⟨rfl, sound, _, inside, read⟩
      exact ⟨sound, inside, v, rfl, read⟩
  simp only [leavesIn, EncodedLayout.count, Slots.count]
  split
  · -- Plain records are rooted as columns.
    rename_i isPlain
    have width_eq : width = fixedWidth element := by
      rw [fixedSize_eq, if_pos (RootProof.hasWidth_of_plain element isPlain)] at fixed
      exact (Option.some.inj fixed).symm
    by_cases empty : min last cnt - first = 0
    · refine ⟨?_, rfl, by omega, Or.inl empty⟩
      rw [empty]
      exact nested_chunks budget values limit mixin deep first last 0 (by omega) _ (fun i h => by omega)
    obtain ⟨sound, _, _⟩ := record 0 (by omega)
    have records : RootProof.RecordsDecode element b (start + width * first) width (min last cnt - first) := by
      intro i h
      obtain ⟨_, inside, v, _, read⟩ := record i h
      have e1 : start + width * first + width * i = start + width * (first + i) := by rw [Nat.mul_add]; omega
      have e2 : start + width * (first + i) + fixedWidth element = start + width * (first + i + 1) := by
        rw [← width_eq, Nat.mul_succ]; omega
      exact ⟨by rw [e1, e2]; exact inside, v, by rw [e1, e2]; exact read⟩
    obtain ⟨sized, rooted⟩ := RootProof.facts_hold.chunkedRoots element isPlain sound b _ width _ small
      (by omega) width_eq records
    refine ⟨nested_chunks budget values limit mixin deep first last _ (by omega) _ (fun i h => ?_), rfl,
      by dsimp only; rw [sized]; exact Nat.le_refl _, Or.inr (by dsimp only; rw [sized]; omega)⟩
    obtain ⟨_, _, v, eq, read⟩ := record i h
    rw [eq]
    apply rooted i h v
    have e1 : start + width * first + width * i = start + width * (first + i) := by rw [Nat.mul_add]; omega
    have e2 : start + width * (first + i) + fixedWidth element = start + width * (first + i + 1) := by
      rw [← width_eq, Nat.mul_succ]; omega
    rw [e1, e2]
    exact read
  · -- Other records are rooted one by one.
    have roots : ∀ i (h : i < min last cnt - first),
        Ssz.hashTreeRoot element (Classical.choose (record i h).2.2) =
          .ok (rootOf element b (start + width * (first + i)) (start + width * (first + i + 1))).data ∧
        (rootOf element b (start + width * (first + i)) (start + width * (first + i + 1))).size = 32 := by
      intro i h
      obtain ⟨sound, inside, _⟩ := record i h
      have chosen := Classical.choose_spec (record i h).2.2
      exact range_root b small element _ _ _ sound
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _) inside chosen.2
    have sized : ∀ r ∈ (List.range (min last cnt - first)).map (fun i =>
        rootOf element b (start + width * (first + i)) (start + width * (first + i + 1))), r.size = 32 := by
      intro r member
      obtain ⟨i, mem, rfl⟩ := List.mem_map.mp member
      exact (roots i (List.mem_range.mp mem)).2
    have joined := RootProof.joinNodes_nodes _ sized
    simp only [List.length_map, List.length_range] at joined
    refine ⟨nested_chunks budget values limit mixin deep first last _ (by omega) _ (fun i h => ?_), rfl,
      by dsimp only; rw [joined.2]; exact Nat.le_refl _, Or.inr (by dsimp only; rw [joined.2]; omega)⟩
    rw [(Classical.choose_spec (record i h).2.2).1, joinNodes_node _ sized i (by simpa using h)]
    simp only [List.getElem_map, List.getElem_range, RootProof.slotRoot]
    exact (roots i h).1

/-- A listed position that agrees with the decoded value's position has that position's root. -/
theorem listed_root (b : ByteArray) (small : RootProof.Small b) (x : Option (Desc × Nat × Nat))
    (y : Option (Desc × Value)) (agrees : SlotAgrees b x y) :
    RootProof.slotRoot y = .ok (listedRoot b x).data ∧ (listedRoot b x).size = 32 := by
  match x, y, agrees with
  | none, none, _ => exact ⟨rfl, rfl⟩
  | some (d, s, e), some (d', v), ⟨same, sound, o, i, read⟩ =>
    subst same
    exact range_root b small d s e v sound o i read

/-- Positions listed one by one have their roots read one by one. -/
theorem listed_span (b : ByteArray) (small : RootProof.Small b) (budget : Nat)
    (slots : List (Option (Desc × Nat × Nat))) (values : List (Option (Desc × Value))) (limit : Option Nat)
    (mixin : Option Bytes) (limit' : Option Nat) (mixin' : Option ByteArray) (counted : slots.length = values.length)
    (each : ∀ i (h : i < values.length), ∃ x, (Slots.listed slots).at i = some x ∧ SlotAgrees b x values[i])
    (deep : ∀ d v, some (d, v) ∈ values → d.nesting ≤ budget)
    (fits : 32 * slots.length + 64 < USize.size) (first last : Nat) :
    SpanAgrees budget ⟨.nested values, limit, mixin⟩ first last slots.length
      (leavesIn b ⟨.nested (.listed slots), limit', mixin'⟩ first last) := by
  -- Position first + i of the span agrees with the decoded value's.
  have tableEntry : ∀ i (h : i < min last slots.length - first),
      SlotAgrees b (slots[first + i]'(by omega)) (values[first + i]'(by omega)) := by
    intro i h
    obtain ⟨x, found, agrees⟩ := each (first + i) (by omega)
    simp only [Slots.at, List.getElem?_eq_getElem (show first + i < slots.length by omega),
      Option.some.injEq] at found
    rwa [found]
  simp only [leavesIn, EncodedLayout.count, Slots.count]
  have len : (((slots.drop first).take (min last slots.length - first)).map (listedRoot b)).length =
      min last slots.length - first := by simp; omega
  have nth : ∀ i (h : i < min last slots.length - first),
      (((slots.drop first).take (min last slots.length - first)).map (listedRoot b))[i]'(by omega) =
        listedRoot b (slots[first + i]'(by omega)) := by
    intro i h
    simp [List.getElem_take, List.getElem_drop]
  have sized : ∀ r ∈ ((slots.drop first).take (min last slots.length - first)).map (listedRoot b), r.size = 32 := by
    intro r member
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem member
    rw [len] at hj
    rw [nth j hj]
    exact (listed_root b small _ _ (tableEntry j hj)).2
  have joined := RootProof.joinNodes_nodes _ sized
  rw [len] at joined
  refine ⟨nested_chunks budget values limit mixin deep first last _ (by omega) _ (fun i h => ?_), rfl,
    by dsimp only; rw [joined.2]; exact Nat.le_refl _, Or.inr (by dsimp only; rw [joined.2]; omega)⟩
  rw [joinNodes_node _ sized i (by rw [len]; exact h), nth i h]
  exact (listed_root b small _ _ (tableEntry i h)).1

/-- The leaves of any span of a layout are, as a buffer and a count, the specification's leaves of that span. -/
theorem span_agrees (b : ByteArray) (small : RootProof.Small b) (budget : Nat) (E : EncodedLayout)
    (L : MerkleLayout) (c : Corresponds b E L) (deep : Deep budget L) (first last : Nat) :
    SpanAgrees budget L first last E.count (leavesIn b E first last) := by
  obtain ⟨leavesE, limitE, mixinE⟩ := E
  obtain ⟨leavesL, limitL, mixinL⟩ := L
  have agree := c.leaves
  have fits := c.fits
  simp only at agree fits
  match leavesE, leavesL, agree with
  | .packed nodes n, .packed chunks, ⟨same, inside, sm⟩ =>
    have := packed_span budget nodes n chunks limitL mixinL same inside sm first last
    simpa [leavesIn, EncodedLayout.count] using this
  | .nested (.stride element start width cnt), .nested values, ⟨counted, each, fixed⟩ =>
    exact stride_span b small budget element start width cnt values limitL mixinL limitE mixinE counted each
      (fixed element start width cnt rfl) (fun d v m => deep values rfl d v m) fits first last
  | .nested (.listed slots), .nested values, ⟨counted, each, _⟩ =>
    exact listed_span b small budget slots values limitL mixinL limitE mixinE counted each
      (fun d v m => deep values rfl d v m) fits first last

end Ssz.Native.BranchProof
