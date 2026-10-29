import SszNative.Proofs.Root.Variable.Vector
import Ssz.Proofs.Codec.BindingPacking
import Ssz.Proofs.Codec.CanonicalTable
import Ssz.Proofs.Codec.CanonicalComposite
import Ssz.Proofs.Codec.Canonicality

/-! The leaves of a counted sequence, three ways: packed bytes, columns of fixed-size roots, or one root per element. -/

namespace Ssz.Native.RootProof

open Ssz Ssz.Native

/-- The nodes of a buffer from an offset: the first, then the rest from one node further. -/
theorem nodesFrom_succ (buf : ByteArray) (offset count : Nat) :
    (nodesFrom buf offset (count + 1)).toList =
      (buf.extract offset (offset + 32)).data :: (nodesFrom buf (offset + 32) count).toList := by
  -- Node i + 1 from an offset is node i from one node further on.
  simp only [nodesFrom, Array.toList_ofFn, List.ofFn_succ]
  congr 2
  funext i
  congr 2 <;> simp [Nat.mul_succ] <;> omega

/-- Decoded elements whose roots sit, one per node, in a buffer have those nodes as leaves. -/
theorem indexed_mapM (element : Desc) (buf : ByteArray) :
    ∀ (values : List Value) (offset : Nat),
      (∀ i (h : i < values.length), Ssz.hashTreeRoot element values[i] =
        .ok (buf.extract (offset + 32 * i) (offset + 32 * i + 32)).data) →
      (values.map fun v => some (element, v)).mapM slotRoot = .ok (nodesFrom buf offset values.length).toList
  -- No elements give no leaves.
  | [], _, _ => by simp [nodesFrom]; rfl
  | v :: rest, offset, rooted => by
    -- The first element's root is the first node, and the rest follow from one node further on.
    rw [List.length_cons, nodesFrom_succ]
    have head := rooted 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.mul_zero, Nat.add_zero] at head
    have tail := indexed_mapM element buf rest (offset + 32) fun i h => by
      have := rooted (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [this]
      congr 3 <;> omega
    simp only [List.map_cons, List.mapM_cons, slotRoot, head, tail, Bind.bind, Except.bind, pure, Except.pure]

/-- Each element of a successful decoding decodes from its own slice. -/
theorem deserializeEach_get (element : Desc) :
    ∀ (slices : List Bytes) (values : List Value), deserializeEach element slices = .ok values →
      values.length = slices.length ∧ ∀ i (h : i < slices.length) (h' : i < values.length),
        deserialize element slices[i] = .ok values[i]
  -- No slices decode to no values.
  | [], values, read => by
    simp only [deserializeEach] at read
    cases read
    simp
  | slice :: rest, values, read => by
    -- A successful run decodes the first slice, then the rest.
    simp only [deserializeEach, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    rename_i head decoded
    split at read
    · cases read
    rename_i tail decodedRest
    cases read
    -- The rest decode element by element, by induction, and the first is decoded directly.
    obtain ⟨lengths, each⟩ := deserializeEach_get element rest tail decodedRest
    refine ⟨by simp [lengths], ?_⟩
    intro i h h'
    cases i with
    | zero => simpa using decoded
    | succ i => simpa using each i (by simpa using h) (by simpa using h')

/-- A basic element's fixed size is its item length. -/
theorem basic_fixedSize {element : Desc} (basic : element.isBasic = true) :
    element.fixedSize = some element.itemLength := by
  -- Only booleans and integers are basic, and each has its item length as fixed size.
  cases element <;> simp_all [Desc.isBasic, Desc.fixedSize, Desc.itemLength]

/-- Slices one width apart cover the whole encoding, so they pack back into it. -/
theorem fixed_slices_pack (data : Bytes) (width : Nat) (whole : data.size % width = 0) :
    packElements ((List.range (data.size / width)).map fun i => data.extract (i * width) ((i + 1) * width)) =
      packBytes data ∧
      data.size = ((List.range (data.size / width)).map fun i =>
        data.extract (i * width) ((i + 1) * width)).length * width := by
  -- The slices cover the data exactly, since the width divides its size.
  have covers : data.size / width * width = data.size := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero whole)
  refine ⟨?_, by simp [covers]⟩
  simp only [packElements, fold_parts_eq_concat, Array.empty_append]
  rw [concat_fixed_slices data width _ (by rw [Nat.mul_comm, covers]; exact Nat.le_refl _), covers,
    Array.extract_eq_self_of_le (Nat.le_refl _)]

/-- The elements of a basic list re-encode to the slices they came from, which pack back into the encoding. -/
theorem basic_packing (element : Desc) (basic : element.isBasic = true) (sound : element.wellFormed = .ok ())
    (data : Bytes) (limit : Option Nat) (slices : List Bytes) (values : List Value)
    (cut : listSlices element limit data = .ok slices) (decoded : deserializeEach element slices = .ok values) :
    serializeEach element values = .ok slices ∧ packElements slices = packBytes data ∧
      data.size = slices.length * element.itemLength := by
  -- Decoded basic elements re-encode to their own slices, as deserialization is canonical.
  refine ⟨serializeEach_of_deserializeEach (serialize_of_deserialize element sound) slices values decoded, ?_⟩
  -- A basic element is fixed-size, so the list is cut one width apart.
  have fixed := basic_fixedSize basic
  simp only [listSlices, fixed, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, pure,
    Except.pure] at cut
  split at cut
  · cases cut
  split at cut
  -- An empty list packs to no nodes.
  · rename_i empty
    cases cut
    simp at empty
    subst empty
    simp [packElements]
  -- A nonempty list's slices cover it exactly, whether or not it declares a cap.
  · repeat' (first | (split at cut) | (cases cut))
    · rename_i _ _ _ md _ _ _
      exact fixed_slices_pack data _ (by simpa using md)
    · rename_i _ _ _ md _ _
      exact fixed_slices_pack data _ (by simpa using md)

end Ssz.Native.RootProof
