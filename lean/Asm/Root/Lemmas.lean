import Asm.Root.Spec
import Ssz.Proofs.Codec.Table
import Ssz.Proofs.Codec.RoundTripComposite

/-! What the encoding of a plain type looks like: its parts back to back, each of its type's width. -/

namespace Ssz.Asm.Root

open Ssz

theorem joined_size : ∀ parts : List Bytes, (joined parts).size = (parts.map Array.size).sum
  | [] => rfl
  | part :: parts => by simp [joined, joined_size parts]

theorem foldl_joined : ∀ (parts : List Bytes) (acc : Bytes),
    parts.foldl (fun total part => total ++ part) acc = acc ++ joined parts
  | [], acc => by simp [joined]
  | part :: parts, acc => by
    simp only [List.foldl_cons, joined, foldl_joined parts, Array.append_assoc]

/-- Splitting a concatenation at its parts' widths gives back the parts. -/
theorem slices_joined : ∀ (parts : List Bytes) (ws : List Nat), parts.map Array.size = ws →
    slices ws (joined parts) = parts
  | [], [], _ => rfl
  | part :: parts, w :: ws, sizes => by
    simp only [List.map_cons, List.cons.injEq] at sizes
    obtain ⟨first, rest⟩ := sizes
    subst first
    simp only [slices, joined]
    congr 1
    · simp
    · have tail : (part ++ joined parts).extract part.size (part ++ joined parts).size = joined parts := by
        apply Array.ext
        · simp
        · intro i _ _
          simp
      rw [tail]
      exact slices_joined parts ws rest
  | [], _ :: _, sizes => by simp at sizes
  | _ :: _, [], sizes => by simp at sizes

/-- With every part fixed, the encoding is the parts back to back, with no offsets. -/
theorem assemble_inline {inline : List Bool} {parts : List Bytes} {bytes : Bytes}
    (allInline : ∀ b ∈ inline, b = true) (sameLength : inline.length = parts.length)
    (assembled : assemble inline parts = .ok bytes) : bytes = joined parts := by
  have head : ∀ (inline : List Bool) (parts : List Bytes) (start : Nat), (∀ b ∈ inline, b = true) →
      inline.length = parts.length → headOf start (inline.zip parts) = joined parts ∧
        bodiesOf (inline.zip parts) = #[] := by
    intro inline
    induction inline with
    | nil => intro parts start _ same; cases parts <;> simp_all [headOf, bodiesOf, joined]
    | cons b inline ih =>
      intro parts start all same
      cases parts with
      | nil => simp at same
      | cons part parts =>
        have isTrue : b = true := all b (by simp)
        subst isTrue
        obtain ⟨h1, h2⟩ := ih parts start (fun b mem => all b (by simp [mem])) (by simpa using same)
        simp [headOf, bodiesOf, joined, h1, h2]
  obtain ⟨h1, h2⟩ := head inline parts (headWidth (inline.zip parts)) allInline sameLength
  simp only [assemble, h1, h2, Array.append_empty, bind, Except.bind, pure, Except.pure] at assembled
  split at assembled
  · simp at assembled
  · simp only [Except.ok.injEq] at assembled
    exact assembled.symm

end Ssz.Asm.Root

namespace Ssz.Asm.Root

open Ssz

mutual

theorem fixedSize_plain : (d : Desc) → plain d = true → d.fixedSize = some (width d)
  | .bool, _ | .uint _, _ | .byteVector _, _ | .bitVector _, _ => rfl
  | .vector element n, p => by
    simp only [plain] at p
    simp [Desc.fixedSize, fixedSize_plain element p, width]
  | .container _ fields, p => by
    simp only [plain] at p
    simp [Desc.fixedSize, fieldsFixedSize_plain fields p, width]
  | .byteList _, p | .bitList _, p | .progressiveBitList _, p | .list _ _, p
  | .progressiveList _ _, p | .progressiveContainer _ _ _, p | .compatibleUnion _ _, p => by
    simp [plain] at p

theorem fieldsFixedSize_plain : (fields : List Desc) → plainAll fields = true →
    Desc.fieldsFixedSize fields = some (widths fields).sum
  | [], _ => rfl
  | field :: fields, p => by
    simp only [plainAll, Bool.and_eq_true] at p
    simp [Desc.fieldsFixedSize, fixedSize_plain field p.1, fieldsFixedSize_plain fields p.2, widths]

end

theorem isFixed_plain (d : Desc) (p : plain d = true) : d.isFixed = true := by
  simp [Desc.isFixed, fixedSize_plain d p]

theorem isFixed_plainAll : (fields : List Desc) → plainAll fields = true →
    ∀ b ∈ fields.map Desc.isFixed, b = true
  | [], _ => by simp
  | field :: fields, p => by
    simp only [plainAll, Bool.and_eq_true] at p
    intro b mem
    simp only [List.map_cons, List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact isFixed_plain field p.1
    · exact isFixed_plainAll fields p.2 b mem

/-- Every element of a sequence encodes to the element type's width. -/
theorem each_size {element : Desc} {w : Nat}
    (sized : ∀ v bytes, serialize element v = .ok bytes → bytes.size = w) :
    ∀ (elements : List Value) (parts : List Bytes), serializeEach element elements = .ok parts →
      parts.map Array.size = List.replicate parts.length w
  | [], parts, h => by simp [serializeEach] at h; subst h; rfl
  | v :: vs, parts, h => by
    simp only [serializeEach, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i head headOk
      split at h
      · simp at h
      · rename_i tail tailOk
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp [sized v head headOk, each_size sized vs tail tailOk, List.replicate_succ]

mutual

theorem serialize_size : (d : Desc) → plain d = true → ∀ v bytes, serialize d v = .ok bytes →
    bytes.size = width d
  | .bool, _, v, bytes, h => by
    cases v <;> simp [serialize] at h
    subst h
    rfl
  | .uint w, _, v, bytes, h => by
    cases v with
    | uint n =>
      simp only [serialize] at h
      split at h
      · simp only [Except.ok.injEq] at h
        subst h
        exact uintBytes_size _ _
      · simp at h
    | _ => simp [serialize] at h
  | .byteVector n, _, v, bytes, h => by
    cases v with
    | bytes data =>
      simp only [serialize] at h
      split at h
      · rename_i size
        simp only [Except.ok.injEq] at h
        subst h
        simpa [width] using size
      · simp at h
    | _ => simp [serialize] at h
  | .bitVector n, _, v, bytes, h => by
    cases v with
    | bits data =>
      simp only [serialize] at h
      split at h
      · simp only [Except.ok.injEq] at h
        subst h
        simp [packBits, width]
      · simp at h
    | _ => simp [serialize] at h
  | .vector element n, p, v, bytes, h => by
    simp only [plain] at p
    cases v with
    | seq elements =>
    simp only [serialize] at h
    split at h
    case isFalse => simp at h
    rename_i count
    simp only [beq_iff_eq] at count
    simp only [serializeSequence, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i parts partsOk
      have sizes := each_size (serialize_size element p) elements parts partsOk
      have length := serializeEach_length element elements parts partsOk
      have fixed : element.isFixed = true := isFixed_plain element p
      rw [assemble_inline (by simp [fixed]) (by simp) h, joined_size, sizes, width,
        List.sum_replicate_nat, length, count, Nat.mul_comm]
    | _ => simp [serialize] at h
  | .container names fields, p, v, bytes, h => by
    simp only [plain] at p
    cases v with
    | seq values =>
    simp only [serialize, serializeStruct, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i parts partsOk
      have sizes := fields_size fields p values parts partsOk
      have length := serializeFields_length fields values parts partsOk
      have fixed : ∀ b ∈ fields.map Desc.isFixed, b = true := isFixed_plainAll fields p
      rw [assemble_inline fixed (by simp [length]) h, joined_size, sizes]
      rfl
    | _ => simp [serialize] at h
  | .byteList _, p, _, _, _ | .bitList _, p, _, _, _ | .progressiveBitList _, p, _, _, _
  | .list _ _, p, _, _, _ | .progressiveList _ _, p, _, _, _
  | .progressiveContainer _ _ _, p, _, _, _ | .compatibleUnion _ _, p, _, _, _ => by
    simp [plain] at p

theorem fields_size : (fields : List Desc) → plainAll fields = true → ∀ values parts,
    serializeFields fields values = .ok parts → parts.map Array.size = widths fields
  | [], _, values, parts, h => by
    cases values <;> simp [serializeFields] at h
    subst h
    rfl
  | field :: fields, p, values, parts, h => by
    simp only [plainAll, Bool.and_eq_true] at p
    cases values with
    | nil => simp [serializeFields] at h
    | cons value values =>
      simp only [serializeFields, bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i head headOk
        split at h
        · simp at h
        · rename_i tail tailOk
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp [widths, serialize_size field p.1 value head headOk, fields_size fields p.2 values tail tailOk]

end

end Ssz.Asm.Root
