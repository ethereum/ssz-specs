import SszNative.Proofs.Branch.Leaves

/-! The walk down a generalized index, over an encoding and over the decoded value, step by step. -/

namespace Ssz.Native.BranchProof

open Ssz Ssz.Native

/-- Whether a type's encodings lay out their trees as the values they decode to do. -/
def LaysOut (d : Desc) : Prop :=
  d.wellFormed = .ok () → ∀ (b : ByteArray) (s e : Nat) (v : Value), s ≤ e → e ≤ b.size → RootProof.Small b →
    deserialize d (slice b s e) = .ok v →
      ∃ E L, layoutOf d b s e = .ok E ∧ merkleLayout d v = .ok L ∧ Corresponds b E L

/-- Whether the walk with a budget reads, from every valid range, the node the value's walk reads. -/
def WalkAt (budget : Nat) : Prop :=
  ∀ (d : Desc) (b : ByteArray) (s e : Nat) (v : Value) (index : Nat), d.wellFormed = .ok () →
    d.nesting ≤ budget → s ≤ e → e ≤ b.size → RootProof.Small b → deserialize d (slice b s e) = .ok v →
      (Native.nodeRootAt budget d b s e index).map ByteArray.data = Ssz.nodeRootAt budget d v index

/-- A walk that stops on the spine reaches a capacity that is a power of four. -/
theorem spineWalk_capacity (count index : Nat) :
    ∀ depth start k stop, spineWalk count index depth start (4 ^ k) = .ok stop → ∃ j, stop.capacity = 4 ^ j
  | 0, start, k, stop, walked => by
    simp only [spineWalk, Except.ok.injEq] at walked
    exact ⟨k, by rw [← walked]⟩
  | depth + 1, start, k, stop, walked => by
    simp only [spineWalk, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure] at walked
    split at walked
    · cases walked
    split at walked
    · cases walked; exact ⟨k, rfl⟩
    · rw [show 4 ^ k * 4 = 4 ^ (k + 1) by rw [Nat.pow_succ]] at walked
      exact spineWalk_capacity count index depth _ (k + 1) stop walked

/-- Reading leaves to the end is reading them up to the last leaf. -/
theorem chunks_to_end (budget : Nat) (L : MerkleLayout) (first : Nat) :
    layoutChunksAt budget L first = layoutChunksAt budget L first (some L.leaves.count) := by
  simp [layoutChunksAt]

/-- The leaves of a bounded subtree, rooted, are the specification's bounded root over them. -/
theorem bounded_span (b : ByteArray) (small : RootProof.Small b) (budget : Nat) (E : EncodedLayout)
    (L : MerkleLayout) (c : Corresponds b E L) (deep : Deep budget L) (first span : Nat) :
    (do
      let chunks ← layoutChunksAt budget L first (some (first + span))
      merkleizeBounded chunks (some span)) =
      .ok (merkleizeDepth (leavesIn b E first (first + span)).1 (leavesIn b E first (first + span)).2
        (depthFor span)).data := by
  obtain ⟨chunks, counted, inside, room⟩ := span_agrees b small budget E L c deep first (first + span)
  rw [chunks]
  simp only [Bind.bind, Except.bind]
  -- At most a span of leaves lies in a span.
  have fits : (leavesIn b E first (first + span)).2 ≤ span := by omega
  exact RootProof.bounded_root RootProof.facts_hold _ _ _ _ rfl fits inside room

/-- A step into a bounded subtree, or into one of its leaves, reads the same node either way. -/
theorem bounded_step (budget : Nat) (ih : WalkAt budget) (b : ByteArray) (small : RootProof.Small b)
    (E : EncodedLayout) (L : MerkleLayout) (c : Corresponds b E L) (deep : Deep budget L)
    (index depth leavesFrom capacity : Nat) :
    (Native.boundedNode budget b E index depth leavesFrom capacity).map ByteArray.data =
      Ssz.boundedNode budget L index depth leavesFrom capacity := by
  rw [Native.boundedNode, Ssz.boundedNode]
  split
  · -- Inside the subtree: the root of the span of leaves the node covers.
    rw [bounded_span b small budget E L c deep]
    rfl
  · -- Below the subtree: the walk goes on inside one leaf.
    have agree := c.leaves
    obtain ⟨leavesE, limitE, mixinE⟩ := E
    obtain ⟨leavesL, limitL, mixinL⟩ := L
    simp only at agree ⊢
    match leavesE, leavesL, agree with
    | .packed _ _, .packed _, _ => rfl
    | .nested slots, .nested values, ⟨counted, each, _⟩ =>
      simp only
      generalize leavesFrom + gindexBelow (index >>> (depth - Nat.log2 (nextPow2 capacity)))
        (Nat.log2 (nextPow2 capacity)) = leaf
      by_cases inside : leaf < values.length
      · obtain ⟨x, found, agrees⟩ := each leaf inside
        rw [found, List.getElem?_eq_getElem inside]
        have mem := List.getElem_mem inside
        generalize values[leaf] = y at agrees mem ⊢
        match x, y, agrees with
        | none, none, _ => rfl
        | some (d, s, e), some (d', v), ⟨same, sound, o, i, read⟩ =>
          subst same
          -- The value inside sits within the budget left.
          exact ih d b s e v _ sound (deep values rfl d v mem) o i small read
      · rw [Slots.at_none slots leaf (by omega), List.getElem?_eq_none (by omega)]
        rfl
    | .packed _ _, .nested _, agree => exact absurd agree id
    | .nested _, .packed _, agree => exact absurd agree id

/-- The progressive tree over leaves read to the end is the specification's, from a power-of-four width. -/
theorem progressive_rest (b : ByteArray) (small : RootProof.Small b) (budget : Nat) (E : EncodedLayout)
    (L : MerkleLayout) (c : Corresponds b E L) (deep : Deep budget L) (first k : Nat) :
    (do
      let rest ← layoutChunksAt budget L first
      return merkleizeProgressiveFrom rest (4 ^ k)) =
      (Except.ok (Native.merkleizeProgressive (leavesIn b E first E.count).1 (leavesIn b E first E.count).2 (4 ^ k)).data :
        Except Err Bytes) := by
  obtain ⟨chunks, _, inside, room⟩ := span_agrees b small budget E L c deep first E.count
  rw [chunks_to_end, ← count_eq c, chunks]
  simp only [Bind.bind, Except.bind, pure, Except.pure, merkleizeProgressiveFrom_power, Except.ok.injEq]
  generalize (leavesIn b E first E.count).1 = nodes at inside room ⊢
  generalize (leavesIn b E first E.count).2 = count at inside room ⊢
  rcases room with zero | room
  · -- No leaves: the spine closes at once.
    subst zero
    simp [Native.merkleizeProgressive, spine, RootProof.nodesFrom, Ssz.merkleizeProgressive, zeroNode, zeroChunk]
  · -- Otherwise the spine from that width, over the same nodes.
    have := (spine_spec nodes count inside room (count + 1) 0 k (by omega)).2
    simp only [List.drop_zero] at this
    rw [Native.merkleizeProgressive, this]
    rfl

/-- A step down a progressive spine, or off it into a level, reads the same node either way. -/
theorem progressive_step (budget : Nat) (ih : WalkAt budget) (b : ByteArray) (small : RootProof.Small b)
    (E : EncodedLayout) (L : MerkleLayout) (c : Corresponds b E L) (deep : Deep budget L)
    (index depth start k : Nat) :
    (Native.progressiveNode budget b E index depth start (4 ^ k)).map ByteArray.data =
      Ssz.progressiveNode budget L index depth start (4 ^ k) := by
  rw [Native.progressiveNode, Ssz.progressiveNode, count_eq c]
  cases walked : spineWalk L.leaves.count index depth start (4 ^ k) with
  | error e => rfl
  | ok stop =>
    simp only [Bind.bind, Except.bind]
    split
    · exact bounded_step budget ih b small E L c deep _ _ _ _
    · -- Stopped on the spine: the progressive tree over the rest of the leaves.
      obtain ⟨j, power⟩ := spineWalk_capacity _ index depth start k stop walked
      rw [power, ← count_eq c]
      have := progressive_rest b small budget E L c deep stop.leavesFrom j
      simp only [Bind.bind, Except.bind] at this
      rw [this]
      rfl

/-- The walk reads the same node from an encoding as from the value it decodes to, at every budget. -/
theorem walk (lays : ∀ d, LaysOut d) : ∀ budget, WalkAt budget
  | 0 => by
    intro d b s e v index _ _ _ _ _ _
    rw [Native.nodeRootAt, Ssz.nodeRootAt]
    rfl
  | budget + 1 => by
    intro d b s e v index sound nested o i small read
    have ih := walk lays budget
    rw [Native.nodeRootAt, Ssz.nodeRootAt]
    simp only [throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure, Except.pure]
    split
    · rfl
    split
    · -- The node at the root is the root itself.
      rw [(RootProof.agrees RootProof.facts_hold d sound b s e v o i small read)]
      rfl
    obtain ⟨E, L, laid, layout, c⟩ := lays d sound b s e v o i small read
    -- Every value nested in the layout sits within the budget left.
    have deep : Deep budget L := fun values nested child inner member => by
      have := merkleLayout_child_nesting d v L layout values nested child inner member
      omega
    rw [laid, layout]
    simp only
    cases gindexLength index with
    | error e => rfl
    | ok full =>
      simp only
      have mixin := c.mixin
      have limit := c.limit
      obtain ⟨leavesE, limitE, mixinE⟩ := E
      obtain ⟨leavesL, limitL, mixinL⟩ := L
      simp only at mixin limit ⊢
      subst limit
      -- The word mixed in is the same either way, as the right child of the root.
      cases mixinE with
      | none =>
        subst mixin
        simp only [Option.isSome_none, Bool.false_eq_true, if_false]
        cases limitE with
        | some capacity => exact bounded_step budget ih b small _ _ c deep _ _ _ _
        | none => exact progressive_step budget ih b small _ _ c deep _ _ 0 0
      | some word =>
        subst mixin
        simp only [Option.isSome_some, if_true, Option.map_some]
        split
        · split
          · rfl
          · rfl
        · cases limitE with
          | some capacity => exact bounded_step budget ih b small _ _ c deep _ _ _ _
          | none => exact progressive_step budget ih b small _ _ c deep _ _ 0 0

end Ssz.Native.BranchProof
