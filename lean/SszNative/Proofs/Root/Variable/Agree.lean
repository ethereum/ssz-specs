import SszNative.Proofs.Root.Variable.Plain
import SszNative.Proofs.Root.Variable.Packed

/-! Every type's root, by induction on the type, from the cases proved one by one. -/

namespace Ssz.Native.RootProof

open Ssz Ssz.Native

variable (facts : Facts)

include facts in
/-- The root of every valid range of an encoding is the specification's root of the value it holds. -/
theorem agrees (d : Desc) : Agrees d := by
  -- Types and their field lists are handled together, by mutual induction.
  induction d using Desc.rec (motive_2 := fun fields => ∀ field ∈ fields, Agrees field) with
  -- Every field of a list agrees, the head directly and the tail by induction.
  | nil => rename_i member; simp at member
  | cons field fields ihHead ihTail =>
    rename_i f member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ihHead
    · exact ihTail f member
  -- Scalars and byte or bit vectors are plain, rooted as fixed-size records.
  | bool => intro sound b s e v o i small read; exact plain_root facts _ rfl sound b s e v o i small read
  | uint => intro sound b s e v o i small read; exact plain_root facts _ rfl sound b s e v o i small read
  | byteVector => intro sound b s e v o i small read; exact plain_root facts _ rfl sound b s e v o i small read
  | bitVector => intro sound b s e v o i small read; exact plain_root facts _ rfl sound b s e v o i small read
  -- Byte and bit lists pack their data and mix in their count.
  | byteList limit => intro _ b s e v o i small read; exact byteList_root facts limit b s e v o i small read
  | bitList limit => intro _ b s e v o i small read; exact bitList_root facts limit b s e v o i small read
  | progressiveBitList limit =>
    intro _ b s e v o i small read; exact progressiveBitList_root facts limit b s e v o i small read
  -- A vector is rooted as a fixed-size record when plain, and element by element otherwise.
  | vector element length ih =>
    intro sound b s e v o i small read
    cases isPlain : plain (.vector element length)
    · exact vector_root facts element length ih sound isPlain b s e v o i small read
    · exact plain_root facts _ isPlain sound b s e v o i small read
  -- Counted lists root their elements, then mix in their count.
  | list element limit ih =>
    intro sound b s e v o i small read; exact list_root facts element limit ih sound b s e v o i small read
  | progressiveList element limit ih =>
    intro sound b s e v o i small read
    exact progressiveList_root facts element limit ih sound b s e v o i small read
  -- A struct is rooted as a fixed-size record when plain, and field by field otherwise.
  | container names fields ih =>
    intro sound b s e v o i small read
    cases isPlain : plain (.container names fields)
    · exact container_root facts names fields ih sound isPlain b s e v o i small read
    · exact plain_root facts _ isPlain sound b s e v o i small read
  -- A progressive struct roots its fields at their layout positions, then mixes in the layout.
  | progressiveContainer active names fields ih =>
    intro sound b s e v o i small read
    exact progressiveContainer_root facts active names fields ih sound b s e v o i small read
  -- A union roots the option its selector names, then mixes in the selector.
  | compatibleUnion selectors options ih =>
    intro sound b s e v o i small read; exact union_root facts selectors options ih sound b s e v o i small read

end Ssz.Native.RootProof
