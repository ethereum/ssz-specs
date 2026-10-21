import SszNative.Proofs.Schema.Validate
import SszNative.Proofs.Schema.Leaves
import SszNative.Proofs.Schema.Fold
import SszNative.Proofs.Root.Main

/-!
A compiled declaration gives the same verdicts and roots as its declaration.

Its roots are therefore the specification's roots of the values the encodings decode to.
-/

namespace Ssz.Native

open Ssz

/-- Copying into a range that ends inside the destination keeps the destination's size. -/
theorem copySlice_size_within (src dest : ByteArray) (so d len : Nat) (hd : d + len ≤ dest.size) :
    (src.copySlice so dest d len).size = dest.size := by
  -- The copy replaces at most a range of the same length, whatever the source holds.
  change (src.copySlice so dest d len).data.size = dest.data.size
  simp only [ByteArray.copySlice, Array.size_append, Array.size_extract]
  have : src.data.size = src.size := rfl
  have : dest.data.size = dest.size := rfl
  omega

/-- A well-formed value that is its own root is at most one node wide. -/
theorem packs_width (d : Desc) (packs : packsIntoNode d = true) (sound : d.wellFormed = .ok ()) :
    fixedWidth d ≤ 32 := by
  -- Integers come in the listed widths, and byte and bit vectors are bounded by the test itself.
  cases d with
  | uint w =>
    simp only [Desc.wellFormed] at sound
    split at sound
    · rename_i listed; simp only [fixedWidth]; simp at listed; omega
    · simp at sound
  | _ => simp_all [packsIntoNode, fixedWidth] <;> omega

/-- Writing a struct's leaves keeps the buffer's size, when every leaf lands inside it. -/
theorem fieldLeaves_size (b : ByteArray) :
    ∀ (fields : List Desc), (∀ f ∈ fields, f.wellFormed = .ok ()) →
      ∀ (offset : Nat) (buffer : ByteArray) (node : Nat), 32 * (node + fields.length) ≤ buffer.size →
        (fieldLeaves fields b 0 offset buffer node).size = buffer.size
  | [], _, _, buffer, _, _ => by rw [fieldLeaves]
  | field :: rest, sound, offset, buffer, node, room => by
    -- The first leaf lands inside its node, then the rest follow.
    rw [fieldLeaves]
    have firstSize : (if packsIntoNode field then b.copySlice (0 + offset) buffer (32 * node) (fixedWidth field)
        else (rootsOf field b (0 + offset) (fixedWidth field) 1).copySlice 0 buffer (32 * node) 32).size =
          buffer.size := by
      split
      · rename_i packs
        have := packs_width field packs (sound field (by simp))
        exact copySlice_size_within _ _ _ _ _ (by simp only [List.length_cons] at room; omega)
      · exact copySlice_size_within _ _ _ _ _ (by simp only [List.length_cons] at room; omega)
    rw [fieldLeaves_size b rest (fun f m => sound f (by simp [m])) _ _ _
      (by rw [firstSize]; simp only [List.length_cons] at room; omega), firstSize]

/-- A struct compiles to one leaf per field. -/
theorem leavesOf_length : ∀ (fields : List Desc) (offset : Nat), (leavesOf fields offset).length = fields.length
  | [], _ => rfl
  | _ :: rest, offset => by simp [leavesOf, leavesOf_length rest]

/-- Leaves read straight from a buffer are the roots of the height-zero subtrees. -/
theorem leaves_height_zero (nodes : ByteArray) (count : Nat) :
    ∀ j < count, nodeOf nodes 0 j = subtreeAt (nodesFrom nodes 0 count) 0 (j * 2 ^ 0) := by
  intro j lt
  rw [Nat.pow_zero, Nat.mul_one, subtreeAt_leaf, nodesFrom_get?, if_pos lt]
  rfl

/-- A compiled struct's root, once its encoding has the struct's width, is the general root. -/
theorem Schema.rootOf_struct (names : List String) (fields : List Desc)
    (p : plain (.container names fields) = true) (sound : (Desc.container names fields).wellFormed = .ok ())
    (b : ByteArray) (sized : b.size = fixedWidth (.container names fields))
    (small : 64 * b.size + 128 < USize.size) :
    foldShort (fillLeaves b (leavesOf fields 0).toArray) (leavesOf fields 0).toArray.size 0 (depthFor fields.length) =
      Native.rootOf (.container names fields) b 0 b.size := by
  -- Every field is well formed and plain, so each is at least a byte wide.
  have fieldsSound := allWellFormed_mem fields (wellFormed_container sound)
  have fieldsPlain : plainAll fields = true := by simpa [plain] using p
  have plainOf : ∀ f ∈ fields, plain f = true := by
    intro f m
    clear sound fieldsSound sized small
    induction fields with
    | nil => simp at m
    | cons g rest ih =>
      simp only [plainAll, Bool.and_eq_true] at fieldsPlain
      rcases List.mem_cons.mp m with rfl | m
      · exact fieldsPlain.1
      · exact ih (by simp [plain, fieldsPlain.2]) fieldsPlain.2 m
  have widths : ∀ f ∈ fields, 1 ≤ fixedWidth f := fun f m => width_pos f (plainOf f m) (fieldsSound f m)
  -- A struct of no fields is not well formed.
  have nonempty : fields ≠ [] := by
    rintro rfl
    simp [Desc.wellFormed, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at sound
  let n := fields.length
  have positive : 1 ≤ n := by cases fields with | nil => exact absurd rfl nonempty | cons _ _ => simp [n]
  -- No more fields than bytes, so the leaf buffer stays addressable.
  have fewer : n ≤ b.size := by
    rw [sized]; exact length_le_fieldsWidth fields widths
  have bufferSmall : 32 * n + 32 < USize.size := by omega
  -- The compiled leaves are the general leaves.
  have count : (leavesOf fields 0).toArray.size = n := by simp [leavesOf_length, n]
  let buffer := fieldLeaves fields b 0 0 (zeros (32 * n + 32)) 0
  have filled : fillLeaves b (leavesOf fields 0).toArray = buffer := by
    rw [fillLeaves_eq, ← Array.foldl_toList, List.toList_toArray, foldl_leavesOf, count, leafBuffer_eq n bufferSmall]
  have bufferSize : buffer.size = 32 * n + 32 := by
    rw [fieldLeaves_size b fields fieldsSound 0 _ 0 (by rw [(zeros_spec _ bufferSmall).1]; omega),
      (zeros_spec _ bufferSmall).1]
  rw [filled, count]
  -- The general root of a single struct is the tree over the same leaves.
  have general : Native.rootOf (.container names fields) b 0 b.size = merkleizeDepth buffer n (depthFor n) := by
    rw [Native.rootOf, if_pos p, rootsOf, if_pos (show (1 == 1) = true from rfl)]
  rw [general]
  -- Both are the specification's tree over the buffer's leaves.
  have spec := merkleizeDepth_spec buffer n (depthFor n) (le_two_pow_depthFor n) (by omega) (by omega)
  have short := foldShort_spec (nodesFrom buffer 0 n) (depthFor n) buffer n 0 (by simp)
    (by simp; omega) (by omega) (by omega) (leaves_height_zero buffer n)
  rw [Nat.zero_add] at short
  apply ByteArray.ext
  rw [short.2, spec.2]

/-- A compiled declaration gives the same root as its declaration, where the encoding is valid. -/
theorem Schema.rootOf_compile (d : Desc) (sound : d.wellFormed = .ok ()) (b : ByteArray)
    (small : 64 * b.size + 128 < USize.size) (valid : Native.validate d b = .ok ()) :
    (Schema.compile d).rootOf b = Native.rootOf d b 0 b.size := by
  unfold Schema.compile
  split
  · rename_i names fields
    split
    · -- A struct of fixed-size fields: its valid encodings have its width.
      rename_i p
      have sized : b.size = fixedWidth (.container names fields) := by
        rw [Native.validate, validateRange, if_pos (plain_hasWidth _ p), validateFixed_whole] at valid
        split at valid
        · simp at valid
        · split at valid
          · simp at valid
          · rename_i wrong; simpa using wrong
      exact Schema.rootOf_struct names fields p sound b sized small
    · rfl
  · rfl

/-- A compiled declaration gives the same root, or the same refusal, as its declaration. -/
theorem Schema.hashTreeRoot_compile (d : Desc) (sound : d.wellFormed = .ok ()) (b : ByteArray)
    (small : 64 * b.size + 128 < USize.size) :
    (Schema.compile d).hashTreeRoot b = Native.hashTreeRoot d b := by
  simp only [Schema.hashTreeRoot, Native.hashTreeRoot, Schema.validate_compile]
  -- A refusal is the same refusal, and an accepted encoding has the same root.
  cases valid : Native.validate d b with
  | error e => rfl
  | ok u =>
    cases u
    simp only [Bind.bind, Except.bind, pure, Except.pure]
    rw [Schema.rootOf_compile d sound b small valid]

/-- A compiled declaration's root of an encoding is the specification's root of the value it decodes to. -/
theorem Schema.hashTreeRoot_eq (d : Desc) (sound : d.wellFormed = .ok ()) (b : ByteArray)
    (small : 64 * b.size + 128 < USize.size) :
    ((Schema.compile d).hashTreeRoot b).map ByteArray.data =
      (do let v ← deserialize d b.data; Ssz.hashTreeRoot d v) := by
  rw [Schema.hashTreeRoot_compile d sound b small]
  exact Native.hashTreeRoot_eq d sound b small

end Ssz.Native
