import SszNative.Hash
import SszNative.Proofs.Asm.Spec
import SszNative.Proofs.Kernel.Sha256

/-!
The Lean references of the native kernels, byte by byte, in the terms the kernels' theorems use.

Each reference appends one fixed-size piece per index, so byte w * i + k of its output is byte k of piece i.
-/

namespace Ssz.Native

open Ssz.Native.Asm Ssz.Native.Kernel

/-- The bytes of pieces of one width, appended in index order. -/
theorem concat_size (f : Nat → ByteArray) (w : Nat) (init : ByteArray) (n : Nat)
    (sized : ∀ i < n, (f i).size = w) :
    ((List.range n).foldl (fun out i => out ++ f i) init).size = init.size + w * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- The new piece adds one width.
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ByteArray.size_append,
      ih (fun i hi => sized i (by omega)), sized n (by omega), Nat.mul_succ, Nat.add_assoc]

/-- Byte k of piece p sits w * p + k bytes past the start. -/
theorem concat_get (f : Nat → ByteArray) (w : Nat) (init : ByteArray) (n : Nat)
    (sized : ∀ i < n, (f i).size = w) (p k : Nat) (piece : p < n) (within : k < w) :
    ((List.range n).foldl (fun out i => out ++ f i) init).get! (init.size + w * p + k) = (f p).get! k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have before := concat_size f w init n (fun i hi => sized i (by omega))
    by_cases last : p = n
    · -- The byte belongs to the piece just appended.
      subst last
      rw [show init.size + w * p + k = (init.size + w * p) + k by rfl, ← before, get!_append_right]
    · -- The byte belongs to an earlier piece, inside what was already there.
      have earlier : w * p + w ≤ w * n := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      rw [get!_append_left _ _ _ (by rw [before]; omega)]
      exact ih (fun i hi => sized i (by omega)) (by omega)

/-- An array with reserved room holds no bytes yet. -/
private theorem size_reserved (n : Nat) : (ByteArray.emptyWithCapacity n).size = 0 := rfl

/-- The loop the references run, unfolded once for all. -/
macro "unfold_loop" : tactic => `(tactic| simp only [Std.Legacy.Range.forIn_eq_forIn_range',
  List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, ← List.range_eq_range', Id.run_pure, bind_pure,
  Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one])

/-- The pairs reference, as a fold appending one digest per pair. -/
private theorem hashPairsReference_fold (src : ByteArray) (offset pairs : USize) :
    hashPairsReference src offset pairs = (List.range pairs.toNat).foldl (fun out i =>
      out ++ Sha256.hash (src.extract (offset.toNat + 64 * i) (offset.toNat + 64 * i + 64)))
      (ByteArray.emptyWithCapacity (32 * pairs.toNat)) := by
  -- The counted loop is a fold over the indices.
  simp only [hashPairsReference]
  unfold_loop

/-- The columns reference, as a fold appending one digest per pair of nodes. -/
private theorem hashColumnsReference_fold (left : ByteArray) (leftOffset : USize) (right : ByteArray)
    (rightOffset count : USize) :
    hashColumnsReference left leftOffset right rightOffset count = (List.range count.toNat).foldl (fun out i =>
      out ++ Sha256.hash (left.extract (leftOffset.toNat + 32 * i) (leftOffset.toNat + 32 * i + 32) ++
        right.extract (rightOffset.toNat + 32 * i) (rightOffset.toNat + 32 * i + 32)))
      (ByteArray.emptyWithCapacity (32 * count.toNat)) := by
  -- The counted loop is a fold over the indices.
  simp only [hashColumnsReference]
  unfold_loop

/-- The fixed-node reference, as a fold appending one digest per node. -/
private theorem hashFixedReference_fold (left : ByteArray) (leftOffset : USize) (node : ByteArray) (count : USize) :
    hashFixedReference left leftOffset node count = (List.range count.toNat).foldl (fun out i =>
      out ++ Sha256.hash (left.extract (leftOffset.toNat + 32 * i) (leftOffset.toNat + 32 * i + 32) ++
        node.extract 0 32))
      (ByteArray.emptyWithCapacity (32 * count.toNat)) := by
  -- The counted loop is a fold over the indices.
  simp only [hashFixedReference]
  unfold_loop

/-- Field i of a gather, cut to its slot. -/
private def field (src : ByteArray) (start stride width slot : USize) (i : Nat) : ByteArray :=
  src.extract (start.toNat + stride.toNat * i) (start.toNat + stride.toNat * i + min width.toNat slot.toNat)

/-- The gather reference, as a fold appending one padded slot per field. -/
private theorem gatherReference_fold (src : ByteArray) (start stride width count slot : USize) :
    gatherReference src start stride width count slot = (List.range count.toNat).foldl (fun out i =>
      out ++ (field src start stride width slot i ++
        ⟨Array.replicate (slot.toNat - (field src start stride width slot i).size) 0⟩))
      (ByteArray.emptyWithCapacity (count.toNat * slot.toNat)) := by
  -- The counted loop is a fold over the indices, each step appending the field and its zeros.
  simp only [gatherReference, field]
  unfold_loop
  simp only [ByteArray.append_assoc]

/-- The parents of adjacent pairs take 32 bytes each. -/
theorem hashPairsReference_size (src : ByteArray) (offset pairs : USize) :
    (hashPairsReference src offset pairs).size = 32 * pairs.toNat := by
  -- Each digest is 32 bytes, appended to an empty array.
  rw [hashPairsReference_fold]
  rw [concat_size _ 32 _ _ fun _ _ => Sha256.hash_size _, size_reserved, Nat.zero_add]

/-- Byte k of parent p is byte k of the digest of the 64 bytes of pair p. -/
theorem hashPairsReference_get (src : ByteArray) (offset pairs : USize) (p k : Nat) (pair : p < pairs.toNat)
    (within : k < 32) :
    (hashPairsReference src offset pairs).get! (32 * p + k) =
      (Sha256.hash (src.extract (offset.toNat + 64 * p) (offset.toNat + 64 * p + 64))).get! k := by
  -- Parent p is the p-th digest appended.
  rw [hashPairsReference_fold]
  have := concat_get (fun i => Sha256.hash (src.extract (offset.toNat + 64 * i) (offset.toNat + 64 * i + 64))) 32
    (ByteArray.emptyWithCapacity (32 * pairs.toNat)) pairs.toNat (fun _ _ => Sha256.hash_size _) p k pair within
  rwa [size_reserved, Nat.zero_add] at this

/-- The parents of two columns take 32 bytes each. -/
theorem hashColumnsReference_size (left : ByteArray) (leftOffset : USize) (right : ByteArray)
    (rightOffset count : USize) :
    (hashColumnsReference left leftOffset right rightOffset count).size = 32 * count.toNat := by
  -- Each digest is 32 bytes, appended to an empty array.
  rw [hashColumnsReference_fold]
  rw [concat_size _ 32 _ _ fun _ _ => Sha256.hash_size _, size_reserved, Nat.zero_add]

/-- Byte k of parent p is byte k of the digest of left node p followed by right node p. -/
theorem hashColumnsReference_get (left : ByteArray) (leftOffset : USize) (right : ByteArray)
    (rightOffset count : USize) (p k : Nat) (pair : p < count.toNat) (within : k < 32) :
    (hashColumnsReference left leftOffset right rightOffset count).get! (32 * p + k) =
      (Sha256.hash (left.extract (leftOffset.toNat + 32 * p) (leftOffset.toNat + 32 * p + 32) ++
        right.extract (rightOffset.toNat + 32 * p) (rightOffset.toNat + 32 * p + 32))).get! k := by
  -- Parent p is the p-th digest appended.
  rw [hashColumnsReference_fold]
  have := concat_get (fun i => Sha256.hash
      (left.extract (leftOffset.toNat + 32 * i) (leftOffset.toNat + 32 * i + 32) ++
        right.extract (rightOffset.toNat + 32 * i) (rightOffset.toNat + 32 * i + 32))) 32
    (ByteArray.emptyWithCapacity (32 * count.toNat)) count.toNat (fun _ _ => Sha256.hash_size _) p k pair within
  rwa [size_reserved, Nat.zero_add] at this

/-- The parents of a column against one node take 32 bytes each. -/
theorem hashFixedReference_size (left : ByteArray) (leftOffset : USize) (node : ByteArray) (count : USize) :
    (hashFixedReference left leftOffset node count).size = 32 * count.toNat := by
  -- Each digest is 32 bytes, appended to an empty array.
  rw [hashFixedReference_fold]
  rw [concat_size _ 32 _ _ fun _ _ => Sha256.hash_size _, size_reserved, Nat.zero_add]

/-- Byte k of parent p is byte k of the digest of left node p followed by the fixed node. -/
theorem hashFixedReference_get (left : ByteArray) (leftOffset : USize) (node : ByteArray) (count : USize)
    (p k : Nat) (pair : p < count.toNat) (within : k < 32) :
    (hashFixedReference left leftOffset node count).get! (32 * p + k) =
      (Sha256.hash (left.extract (leftOffset.toNat + 32 * p) (leftOffset.toNat + 32 * p + 32) ++
        node.extract 0 32)).get! k := by
  -- Parent p is the p-th digest appended.
  rw [hashFixedReference_fold]
  have := concat_get (fun i => Sha256.hash
      (left.extract (leftOffset.toNat + 32 * i) (leftOffset.toNat + 32 * i + 32) ++ node.extract 0 32)) 32
    (ByteArray.emptyWithCapacity (32 * count.toNat)) count.toNat (fun _ _ => Sha256.hash_size _) p k pair within
  rwa [size_reserved, Nat.zero_add] at this

/-- One record's slot: its field, cut to the slot, then zeros up to the slot's size. -/
private theorem slot_size (bytes : ByteArray) (slot : Nat) (fits : bytes.size ≤ slot) :
    (bytes ++ ⟨Array.replicate (slot - bytes.size) 0⟩).size = slot := by
  -- The field and its zeros fill the slot exactly.
  rw [ByteArray.size_append]
  simp only [ByteArray.size, Array.size_replicate] at *
  omega

/-- A field never outgrows its slot. -/
private theorem field_size (src : ByteArray) (start stride width slot : USize) (i : Nat) :
    (field src start stride width slot i).size ≤ slot.toNat := by
  -- A field is cut to at most the slot's size.
  rw [field, ByteArray.size_extract]
  omega

/-- Gathered slots take one slot size each. -/
theorem gatherReference_size (src : ByteArray) (start stride width count slot : USize) :
    (gatherReference src start stride width count slot).size = count.toNat * slot.toNat := by
  -- Each slot is filled to its size, appended to an empty array.
  rw [gatherReference_fold, concat_size _ slot.toNat _ _ fun i _ => slot_size _ _ (field_size ..),
    size_reserved, Nat.zero_add, Nat.mul_comm]

/--
Byte k of slot i is byte k of field i, or a zero past the field.

Every field must lie inside the source and fit its slot, as the native binding checks.
-/
theorem gatherReference_get (src : ByteArray) (start stride width count slot : USize) (i k : Nat)
    (record : i < count.toNat) (within : k < slot.toNat) (fits : width.toNat ≤ slot.toNat)
    (inside : start.toNat + stride.toNat * i + width.toNat ≤ src.size) :
    (gatherReference src start stride width count slot).get! (slot.toNat * i + k) =
      if k < width.toNat then src.get! (start.toNat + stride.toNat * i + k) else 0 := by
  -- Slot i is the i-th piece appended.
  rw [gatherReference_fold]
  have := concat_get _ slot.toNat (ByteArray.emptyWithCapacity (count.toNat * slot.toNat)) count.toNat
    (fun i _ => slot_size _ _ (field_size src start stride width slot i)) i k record within
  rw [size_reserved, Nat.zero_add] at this
  rw [this]
  -- Inside the source, the field is exactly the width.
  have size : (field src start stride width slot i).size = width.toNat := by
    rw [field, ByteArray.size_extract]
    omega
  by_cases early : k < width.toNat
  · -- A field byte, read through the cut.
    rw [if_pos early, get!_append_left _ _ _ (by omega), get!_eq _ _ (by omega), get!_eq _ _ (by omega)]
    simp only [field, ByteArray.getElem_extract]
  · -- A padding byte.
    have zeros : (⟨Array.replicate (slot.toNat - (field src start stride width slot i).size) 0⟩ : ByteArray).size =
        slot.toNat - width.toNat := by
      rw [size]
      exact Array.size_replicate
    have e : k = (field src start stride width slot i).size + (k - width.toNat) := by omega
    rw [if_neg early, e, get!_append_right, get!_eq _ _ (by rw [zeros]; omega), ByteArray.getElem_eq_getElem_data]
    exact Array.getElem_replicate _

/-- Whether memory holds an array's bytes from an address. -/
def Holds (mem : Nat → UInt8) (base : Nat) (bytes : ByteArray) : Prop :=
  ∀ i < bytes.size, mem (base + i) = bytes.get! i

/-- A pair read from memory is a node of the left array followed by a node of the right one. -/
theorem pairMessage_holds (mem : Nat → UInt8) (a b : Nat) (left right : ByteArray) (l r : Nat)
    (holdsLeft : Holds mem a left) (holdsRight : Holds mem b right)
    (leftInside : l + 32 ≤ left.size) (rightInside : r + 32 ≤ right.size) :
    pairMessage mem (a + l) (b + r) = left.extract l (l + 32) ++ right.extract r (r + 32) := by
  -- Each node is 32 bytes inside its array.
  have leftSize : (left.extract l (l + 32)).size = 32 := by rw [ByteArray.size_extract]; omega
  have rightSize : (right.extract r (r + 32)).size = 32 := by rw [ByteArray.size_extract]; omega
  apply ByteArray.ext
  apply Array.ext
  · -- Both are 64 bytes.
    simp only [pairMessage, Array.size_ofFn]
    rw [← ByteArray.size, ByteArray.size_append, leftSize, rightSize]
  · intro i inMessage inNodes
    have bound : i < 64 := by simpa [pairMessage] using inMessage
    simp only [pairMessage, Array.getElem_ofFn]
    rw [← ByteArray.getElem_eq_getElem_data]
    by_cases first : i < 32
    · -- A byte of the left node.
      rw [if_pos first, ByteArray.getElem_append_left (by omega), ByteArray.getElem_extract, Nat.add_assoc,
        holdsLeft _ (by omega), get!_eq _ _ (by omega)]
    · -- A byte of the right node.
      rw [if_neg first, ByteArray.getElem_append_right (by omega), ByteArray.getElem_extract, Nat.add_assoc,
        holdsRight _ (by omega), get!_eq _ _ (by omega)]
      simp only [leftSize]

/-- A pair of adjacent nodes read from memory is the 64 bytes of the array there. -/
theorem pairMessage_adjacent (mem : Nat → UInt8) (a : Nat) (src : ByteArray) (o : Nat)
    (holds : Holds mem a src) (inside : o + 64 ≤ src.size) :
    pairMessage mem (a + o) (a + o + 32) = src.extract o (o + 64) := by
  -- Adjacent nodes of one array join into its 64 bytes there.
  rw [Nat.add_assoc a o 32, pairMessage_holds mem a a src src o (o + 32) holds holds (by omega) (by omega),
    ByteArray.extract_append_extract]
  congr 1 <;> omega

/-- A node read from memory, followed by one fixed node. -/
theorem pairMessage_fixed (mem : Nat → UInt8) (a b : Nat) (left node : ByteArray) (l : Nat)
    (holdsLeft : Holds mem a left) (holdsNode : Holds mem b node)
    (leftInside : l + 32 ≤ left.size) (nodeInside : 32 ≤ node.size) :
    pairMessage mem (a + l) b = left.extract l (l + 32) ++ node.extract 0 32 := by
  -- The fixed node is the first 32 bytes of its array.
  simpa using pairMessage_holds mem a b left node l 0 holdsLeft holdsNode leftInside (by omega)

end Ssz.Native
