import Ssz.Proofs.Codec.RootLaws
import Ssz.Proofs.Codec.LayoutLaws
import Ssz.Proofs.Type.Equality

/-! Replacing a field by its own root leaves the struct's root unchanged. -/

namespace Ssz

/-- A byte string exactly one node wide packs into that one node. -/
private theorem packBytes_chunk {data : Bytes} (width : data.size = bytesPerChunk) :
    packBytes data = #[data] := by
  have size : (packBytes data).size = 1 := by simp [width, bytesPerChunk]
  apply Array.ext
  · simp [size]
  · intro position inside _
    obtain rfl : position = 0 := by omega
    apply Array.ext
    · simp [packBytes_chunk_size _ _ (by omega : 0 < _), width]
    · intro byte inner _
      rw [packBytes_chunk_size _ _ (by omega)] at inner
      simpa using packBytes_get data 0 byte (by omega) inner (by omega)

/-- A complete node held as a fixed byte array is its own root. -/
theorem hashTreeRoot_chunk {data : Bytes} (width : data.size = bytesPerChunk) :
    hashTreeRoot (.byteVector bytesPerChunk) (.bytes data) = .ok data := by
  have flat : depthFor 1 = 0 := depthFor_pow 0
  simp only [hashTreeRoot, Desc.nesting, hashTreeRootAt, merkleLayout, fixedLeaf, serialize,
    width, beq_self_eq_true, if_true, Bind.bind, Except.bind, pure, Except.pure,
    MerkleLayout.packing, packBytes_chunk width, layoutChunksAt, Leaves.count]
  simp only [merkleizeBounded, flat, subtreeAt, padded, Array.size_singleton,
    Bind.bind, Except.bind, pure, Except.pure]
  rfl

/-- Setting one entry of each of two lists sets the one entry of the list they zip to. -/
private theorem zip_set {α β : Type} :
    ∀ (left : List α) (right : List β) (position : Nat) (a : α) (b : β),
      (left.set position a).zip (right.set position b)
        = (left.zip right).set position (a, b)
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, _, _ => by simp
  | _ :: _, _ :: _, 0, _, _ => by simp
  | _ :: leftRest, _ :: rightRest, position + 1, a, b => by
    simp [zip_set leftRest rightRest position a b]

/-- Replacing one entry by another the mapping agrees on leaves the whole mapping unchanged. -/
private theorem mapM_set {α β : Type} (f : α → Except Err β) :
    ∀ (entries : List α) (position : Nat) (replacement original : α),
      entries[position]? = some original → f replacement = f original →
      (entries.set position replacement).mapM f = entries.mapM f
  | [], _, _, _, held, _ => by simp at held
  | _ :: rest, position, _, _, held, agree => by
    cases position <;> simp_all [List.mapM_cons, mapM_set f rest]

/--
A field replaced by its own root gives the same struct root.

This is the summary relation: a party holding only the root of a nested value computes the
same struct root as one holding the value itself.

A proof about anything inside that value therefore verifies against either root, which is
what a light client relies on.

One replacement is enough to state, since several compose.
-/
theorem hashTreeRoot_summary {names : List String} {fields : List Desc} {values : List Value}
    {position : Nat} {nested : Desc} {held : Value} {root : Bytes}
    (paired : fields.length = values.length)
    (declared : fields[position]? = some nested) (carried : values[position]? = some held)
    (rooted : hashTreeRoot nested held = .ok root) (width : root.size = bytesPerChunk) :
    hashTreeRoot (.container names (fields.set position (.byteVector bytesPerChunk)))
        (.seq (values.set position (.bytes root)))
      = hashTreeRoot (.container names fields) (.seq values) := by
  -- One budget serves both shapes, so neither side depends on its own declared nesting.
  obtain ⟨inner, split⟩ :
      ∃ inner, max (Desc.container names (fields.set position (.byteVector bytesPerChunk))).nesting
        (Desc.container names fields).nesting = inner + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le (by simp [Desc.nesting])
      (Nat.le_max_right ..))).symm⟩
  rw [← hashTreeRootAt_eq_hashTreeRoot _ _ _ (split ▸ Nat.le_max_left ..),
    ← hashTreeRootAt_eq_hashTreeRoot _ _ _ (split ▸ Nat.le_max_right ..)]
  -- The replaced leaf has the root the original field had, so the two leaf lists agree.
  have enough : nested.nesting ≤ inner := by
    have bound := nesting_le_deepest nested fields (List.mem_of_getElem? declared)
    have top : (Desc.container names fields).nesting ≤ inner + 1 := split ▸ Nat.le_max_right ..
    simp only [Desc.nesting] at top
    omega
  have shallow : (Desc.byteVector bytesPerChunk).nesting ≤ inner := by
    have := nested.nesting_pos
    simp only [Desc.nesting]
    omega
  have leaf : hashTreeRootAt inner (.byteVector bytesPerChunk) (.bytes root)
      = hashTreeRootAt inner nested held := by
    rw [hashTreeRootAt_eq_hashTreeRoot _ _ _ shallow,
      hashTreeRootAt_eq_hashTreeRoot _ _ _ enough, rooted, hashTreeRoot_chunk width]
  -- The two leaf lists differ at one position, and the leaf read agrees there.
  have chunks : ∀ (limit : Option Nat) (mixin : Option Bytes),
      layoutChunksAt inner ⟨.nested (((fields.zip values).map some).set position
        (some (.byteVector bytesPerChunk, .bytes root))), limit, mixin⟩
      = layoutChunksAt inner ⟨.nested ((fields.zip values).map some), limit, mixin⟩ := by
    intro limit mixin
    simp only [layoutChunksAt, Leaves.count, Option.getD_none, Nat.sub_zero, List.drop_zero,
      List.take_length]
    congr 1
    exact mapM_set _ _ position _ (some (nested, held))
      (by simp [List.getElem?_zip_eq_some, declared, carried]) leaf
  -- Both structs declare the same field count, so both trees have the same capacity.
  simp only [hashTreeRootAt, merkleLayout, List.length_set, paired, bne_self_eq_false,
    Bool.false_eq_true, if_false, Bind.bind, Except.bind, pure, Except.pure,
    zip_set, List.map_set, MerkleLayout.nesting, chunks]

end Ssz
