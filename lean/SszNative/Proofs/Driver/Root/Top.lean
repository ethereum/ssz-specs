import SszNative.Proofs.Driver.Root.ByteList
import SszNative.Proofs.Driver.Root.BitList
import SszNative.Proofs.Driver.Root.Dispatcher
import SszNative.Proofs.Driver.Root.List
import SszNative.Proofs.Driver.Root.Union
import SszNative.Proofs.Driver.Root.ProgressiveContainer

/-!
The root of an encoding, end to end: the call returns zero and writes the specification's root.

The dispatcher is proved for every type by induction on the type, each driver from its children's dispatcher calls.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Asm

/-- The dispatcher writes the Lean root of a range of every type. -/
theorem rootOf_ok {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RangeFns m)
    (d : Desc) : RootOfOk m w d := by
  induction d using Desc.rec (motive_2 := fun fields => ∀ field ∈ fields, RootOfOk m w field) with
  | nil => rename_i member; simp at member
  | cons field fields ihHead ihTail =>
    rename_i f member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ihHead
    · exact ihTail f member
  | bool => exact rootOf_dispatch hash gmod fns _ fun h => by simp [plain] at h
  | uint => exact rootOf_dispatch hash gmod fns _ fun h => by simp [plain] at h
  | byteVector => exact rootOf_dispatch hash gmod fns _ fun h => by simp [plain] at h
  | bitVector => exact rootOf_dispatch hash gmod fns _ fun h => by simp [plain] at h
  | byteList limit => exact rootOf_dispatch hash gmod fns _ fun _ => rootBytes_ok hash gmod fns limit
  | bitList limit => exact rootOf_dispatch hash gmod fns _ fun _ => rootBits_ok hash gmod fns limit
  | progressiveBitList limit =>
    exact rootOf_dispatch hash gmod fns _ fun _ => rootBitsProgressive_ok hash gmod fns limit
  | vector element length ih => exact rootOf_dispatch hash gmod fns _ fun h => rootVector_ok hash fns ih h
  | list element limit ih =>
    exact rootOf_dispatch hash gmod fns _ fun _ => rootList_ok hash gmod fns ih (.inl ⟨limit, rfl⟩)
  | progressiveList element limit ih =>
    exact rootOf_dispatch hash gmod fns _ fun _ => rootList_ok hash gmod fns ih (.inr ⟨limit, rfl⟩)
  | container names fields ih =>
    exact rootOf_dispatch hash gmod fns _ fun h => rootContainer_ok hash fns ih h
  | progressiveContainer active names fields ih =>
    exact rootOf_dispatch hash gmod fns _ fun _ => rootProgressiveContainer_ok hash fns ih
  | compatibleUnion selectors options ih =>
    exact rootOf_dispatch hash gmod fns _ fun _ => rootUnion_ok hash fns ih

/-- The top driver's frame holds fifteen words. -/
theorem hashTreeRootFrame : HashTreeRoot.fn.frame = 15 := by decide

/-- An encoding validation accepted decodes, as a whole range. -/
theorem accepted_of_validate {d : Desc} {b : ByteArray} (accepted : validate d b = .ok ()) :
    ∃ v, deserialize d (slice b 0 b.size) = .ok v := by
  have whole : slice b 0 b.size = b.data := by simp [slice, ← ByteArray.size_data]
  rw [validate_eq] at accepted
  rw [whole]
  cases h : deserialize d b.data with
  | error e => rw [h] at accepted; cases accepted
  | ok v => exact ⟨v, rfl⟩

/--
The root of an encoding validation accepted: the call returns zero and writes the specification's root of the value
the encoding holds.

The encoding, the plan, the output, the scratch and the context meet a range call's needs over the whole encoding:
the scratch holds as many bytes as the scratch bound gives, and misses everything else the call reads or writes.
Memory changes only at the output, in the scratch, and in the padding area.
-/
theorem hashTreeRoot_calls {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m)
    (fns : RangeFns m) {d : Desc} {sp : Nat} (room : w.stackLo + 128 + 256 + rootStack d ≤ sp) {mem : Memory}
    {plan data out scratch ctx table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    (pre : RangePre w mem d plan data 0 b.size out scratch ctx table zeros pad mask b) :
    ∃ mem', Calls m w "ssz_hash_tree_root" sp [UInt64.ofNat plan, UInt64.ofNat data, UInt64.ofNat b.size,
        UInt64.ofNat out, UInt64.ofNat scratch, UInt64.ofNat ctx] mem 0 mem' ∧
      (do let v ← deserialize d b.data; Ssz.hashTreeRoot d v) = .ok (nodeAt mem' out) ∧
      RootReady w ctx table zeros pad mask mem' ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (scratch ≤ a ∧ a < scratch + rootScratch d b.size) →
        ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a := by
  have sp' : w.stackLo + rootStack d + 256 ≤ sp - 8 - 8 * HashTreeRoot.fn.frame := by
    rw [hashTreeRootFrame]; omega
  obtain ⟨mem', call, root, ready, keep⟩ := rootOf_ok hash gmod fns d _ mem plan data 0 b.size out scratch
    ctx table zeros pad mask b sp' pre
  simp only [Nat.add_zero, Nat.sub_zero] at call root keep
  have r1 := Runs.call (m := m) (sp := sp - 8 - 8 * HashTreeRoot.fn.frame)
    (env := entryEnv [UInt64.ofNat plan, UInt64.ofNat data, UInt64.ofNat b.size, UInt64.ofNat out,
      UInt64.ofNat scratch, UInt64.ofNat ctx]) (mem := mem) (dst := 7)
    (args := [HashTreeRoot.plan, HashTreeRoot.data, HashTreeRoot.len, HashTreeRoot.out, HashTreeRoot.scratch,
      HashTreeRoot.ctx]) (by simp only [List.mapM_cons, List.mapM_nil]; rfl) call
  have r2 := Runs.set' (m := m) (w := w) (sp := sp - 8 - 8 * HashTreeRoot.fn.frame)
    (env := Asm.assign (entryEnv [UInt64.ofNat plan, UInt64.ofNat data, UInt64.ofNat b.size, UInt64.ofNat out,
      UInt64.ofNat scratch, UInt64.ofNat ctx]) 7 0) (mem := mem') (x := 6) (eval_lit 0)
  refine ⟨mem', Calls.fn fns.top (by rw [hashTreeRootFrame]; omega) rfl
    (Runs.block_cons r1 (Runs.block_cons r2 (Runs.block_nil _ _ _ _ _))) (eval_var assign_eq), ?_, ready, keep⟩
  -- The Lean root of the whole encoding is the specification's root of the value it decodes to.
  obtain ⟨v, read⟩ := pre.accepted
  have whole : slice b 0 b.size = b.data := by simp [slice, ← ByteArray.size_data]
  rw [whole] at read
  have agrees := RootProof.agrees RootProof.facts_hold d pre.sound b 0 b.size v (Nat.zero_le _) (Nat.le_refl _)
    pre.small (by rw [whole]; exact read)
  rw [root]
  simp only [read, Bind.bind, Except.bind]
  exact agrees

end EthLib.Consensus.Ssz.Native.Driver
