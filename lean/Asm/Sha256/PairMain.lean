import Asm.Sha256.PairProof

/-! The whole pair hash: two nodes in, their parent out, exactly as the specification combines them. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Sha256

open Ssz.Sha256 (Spec.State Spec.rounds Spec.compression Spec.inputWord Spec.inputWords
  Spec.messageWord Spec.addState Spec.initial Spec.digest)

/-- The 64-byte message a pair hash reads: the left node, then the right node. -/
def pairMessage (m : Machine) : ByteArray :=
  ⟨(m.bytes (m.read a1) 32).data ++ (m.bytes (m.read a2) 32).data⟩

theorem bytes_data_size {m : Machine} {a : BitVec 64} {n : Nat} : (m.bytes a n).data.size = n := by
  simp [Machine.bytes]

theorem pairWord_eq (m : Machine) {t : Nat} (early : t < 16) :
    (Spec.inputWords (pairMessage m) 0)[t] = pairWord m t := by
  rw [inputWords_get early, pairWord]
  split
  · -- A left word reads the first 32 bytes, which are the left node.
    have shifted := inputWord_shift (a := pairMessage m) (b := m.bytes (m.read a1) 32) (s := 0)
      (q := 4 * t) fun k below => by
        rw [pairMessage, get!_append, bytes_data_size, if_pos (by omega), Nat.zero_add]
    rwa [Nat.zero_add] at shifted
  · -- A right word reads 32 bytes further on, in the right node.
    have shifted := inputWord_shift (a := pairMessage m) (b := m.bytes (m.read a2) 32) (s := 32)
      (q := 4 * (t - 8)) fun k below => by
        rw [pairMessage, get!_append, bytes_data_size, if_neg (by omega),
          show 32 + (4 * (t - 8) + k) - 32 = 4 * (t - 8) + k by omega]
    rwa [show 32 + 4 * (t - 8) = 4 * t by omega] at shifted

theorem ivWord_initial : ∀ j, j < 8 → ivWord j = stateWord Spec.initial j := by
  decide

/-- The specification's combination of two nodes is SHA-256 of their concatenation. -/
theorem combine_eq (m : Machine) :
    ByteArray.mk (Ssz.combine (m.bytes (m.read a1) 32).data (m.bytes (m.read a2) 32).data) =
      Spec.digest (Spec.compression padWords
        (Spec.compression (Spec.inputWords (pairMessage m) 0) Spec.initial)) := by
  have size : (pairMessage m).size = 64 := by
    simp only [pairMessage, ByteArray.size, Array.size_append, bytes_data_size]
  have joined : ByteArray.mk (Ssz.combine (m.bytes (m.read a1) 32).data (m.bytes (m.read a2) 32).data) =
      Ssz.Sha256.hash (pairMessage m) := rfl
  rw [joined, ← hash_sixtyFour size, ← Ssz.Sha256.hash_refines _ (by omega)]

/-- Stored digest bytes are the specification's digest. -/
theorem bytes_digest {m : Machine} {out : BitVec 64} {state : Spec.State}
    (stored : ∀ k, k < 32 → m.mem (out + BitVec.ofNat 64 k) = digestByte (stateWord state (k / 4)) (k % 4)) :
    m.bytes out 32 = Spec.digest state := by
  apply ByteArray.ext
  simp only [Machine.bytes, Spec.digest]
  apply Array.ext
  · simp
  · intro i left right
    simp only [Array.getElem_ofFn]
    rw [stored i (by simpa using left)]
    have quarter : i / 4 < 8 := by simp at left; omega
    simp only [digestByte, stateWord, Nat.mod_eq_of_lt quarter]
    apply UInt8.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    simp [UInt8.toBitVec_ofNat]

/--
SHA-256 of the left node at a1 and the right node at a2, stored at the address in a frame slot.

Memory changes only at the 32 output bytes, and only working registers change.
-/
theorem pair_spec (m : Machine) (outSlot : Nat) (small : outSlot < 2048) :
    let out := m.load (m.read sp + BitVec.ofNat 64 outSlot) 8
    let m' := execBlock (pairCode outSlot) m
    m'.bytes out 32 = ⟨Ssz.combine (m.bytes (m.read a1) 32).data (m.bytes (m.read a2) 32).data⟩ ∧
      (∀ y, ¬Within y out 32 → m'.mem y = m.mem y) ∧ ∀ x, x ∉ workRegs → m'.read x = m.read x := by
  intro out m'
  have body : pairCode outSlot = (List.range 16).flatMap loadPairWord ++
      ((List.range 8).flatMap ivWordCode ++ ([.xor (carry 0) (wordHome 0 1) (wordHome 0 2)] ++
      (roundsCode 64 ++ ((List.range 8).flatMap ivForwardWord ++ ((List.range 8).map keepWord ++
      ([.xor (carry 0) (wordHome 0 1) (wordHome 0 2)] ++ (fusedRoundsCode 64 ++
      (((List.range 8).flatMap fun j => [keptForwardWord j]) ++ digestCode outSlot)))))))) := by
    simp only [pairCode, loadPairCode, ivCode, ivForwardCode, keepCode, keptForwardCode,
      List.append_assoc, ← List.map_eq_flatMap]
  simp only [m']
  rw [body, execBlock_append, execBlock_append]
  -- Load both nodes, then the initial state, then round zero's carry.
  obtain ⟨ring, mem1, frame1⟩ := loadPair_upto (m := m) 16 (by omega)
  generalize execBlock ((List.range 16).flatMap loadPairWord) m = m1 at ring mem1 frame1
  obtain ⟨iv, mem2, frame2⟩ := iv_upto (m := m1) 8 (by omega)
  generalize execBlock ((List.range 8).flatMap ivWordCode) m1 = m2 at iv mem2 frame2
  rw [execBlock_append, execBlock_cons, execBlock_nil, Instr.run]
  -- Round zero: the initial state in its homes, b xor c in the carry, the pair in the ring.
  have carry0 (j : Nat) (small : j < 8) : wordHome 0 j ≠ carry 0 := (wordHome_ne 0 j 0 0).2.1
  have ivHome (j : Nat) (small : j < 8) :
      Holds (m2.write (carry 0) (m2.read (wordHome 0 1) ^^^ m2.read (wordHome 0 2))) (wordHome 0 j)
        (stateWord Spec.initial j) := by
    rw [Holds, Machine.read_write_ne (carry0 j small), ← stateHome_eq j small, ← ivWord_initial j small]
    exact iv j small
  have inv0 : RoundsInv (Spec.inputWords (pairMessage m) 0) Spec.initial
      (m2.write (carry 0) (m2.read (wordHome 0 1) ^^^ m2.read (wordHome 0 2))) 0 (by omega)
      (m2.write (carry 0) (m2.read (wordHome 0 1) ^^^ m2.read (wordHome 0 2))) := by
    refine ⟨ivHome 0 (by omega), ivHome 1 (by omega), ivHome 2 (by omega), ivHome 3 (by omega),
      ivHome 4 (by omega), ivHome 5 (by omega), ivHome 6 (by omega), ivHome 7 (by omega), ?_,
      fun t near => ?_, rfl, fun _ _ => rfl⟩
    · have b := ivHome 1 (by omega)
      have c := ivHome 2 (by omega)
      rw [Holds, Machine.read_write_ne (carry0 1 (by omega))] at b
      rw [Holds, Machine.read_write_ne (carry0 2 (by omega))] at c
      rw [Holds, Machine.read_write_self (nonzero 0 0 0 0).2.2.symm, b, c, BitVec.signExtend_xor]
      rfl
    · have early : t < 16 := by simp [window] at near; omega
      rw [Holds, Machine.read_write_ne (ringSlot_ne t 0).1,
        frame2 _ (fun inside => ringSlot_not_state t inside), messageWord_early early, pairWord_eq m early]
      exact ring t early
  have mem3 : (m2.write (carry 0) (m2.read (wordHome 0 1) ^^^ m2.read (wordHome 0 2))).mem = m2.mem :=
    rfl
  have frame3 : ∀ x, x ≠ carry 0 →
      (m2.write (carry 0) (m2.read (wordHome 0 1) ^^^ m2.read (wordHome 0 2))).read x = m2.read x :=
    fun _ other => Machine.read_write_ne other
  generalize m2.write (carry 0) (m2.read (wordHome 0 1) ^^^ m2.read (wordHome 0 2)) = m3
    at inv0 mem3 frame3
  have inv64 := rounds_all inv0 64 (by omega)
  rw [execBlock_append]
  generalize execBlock (roundsCode 64) m3 = m4 at inv64
  generalize hW1 : Spec.rounds (Spec.inputWords (pairMessage m) 0) Spec.initial 64 (by omega) = W1
    at inv64
  have homes4 := homes_of_inv inv64
  rw [hW1] at homes4
  -- First feed-forward, then keep the chaining state in the ring.
  obtain ⟨fwd, -, mem5, frame5⟩ := forward_upto (m := m4) (code := ivForwardWord)
    (work := stateWord W1) (add := ivWord)
    (fun j mj small waiting _ => ivForward_word j mj small (waiting j small (Nat.le_refl _))) homes4
    8 (by omega)
  rw [execBlock_append]
  generalize execBlock ((List.range 8).flatMap ivForwardWord) m4 = m5 at fwd mem5 frame5
  obtain ⟨kept, mem6, frame6⟩ := keep_upto (m := m5) (chain := fun j => stateWord W1 j + ivWord j)
    fwd 8 (by omega)
  rw [execBlock_append]
  generalize execBlock ((List.range 8).map keepWord) m5 = m6 at kept mem6 frame6
  rw [execBlock_append, execBlock_cons, execBlock_nil, Instr.run]
  -- The chaining state after the first block, word by word.
  have chain1 (j : Nat) (small : j < 8) :
      stateWord (Spec.compression (Spec.inputWords (pairMessage m) 0) Spec.initial) j =
        stateWord W1 j + ivWord j := by
    rw [Spec.compression, hW1, stateWord_addState small, ivWord_initial j small, BitVec.add_comm]
  have chainHome (j : Nat) (small : j < 8) :
      Holds (m6.write (carry 0) (m6.read (wordHome 0 1) ^^^ m6.read (wordHome 0 2))) (wordHome 0 j)
        (stateWord (Spec.compression (Spec.inputWords (pairMessage m) 0) Spec.initial) j) := by
    rw [Holds, Machine.read_write_ne (carry0 j small), ← stateHome_eq j small,
      frame6 _ (fun inside => ringSlot_not_state_mem inside), chain1 j small]
    exact fwd j small
  have start2 : FusedInv (Spec.compression (Spec.inputWords (pairMessage m) 0) Spec.initial)
      (m6.write (carry 0) (m6.read (wordHome 0 1) ^^^ m6.read (wordHome 0 2))) 0 (by omega)
      (m6.write (carry 0) (m6.read (wordHome 0 1) ^^^ m6.read (wordHome 0 2))) := by
    refine ⟨chainHome 0 (by omega), chainHome 1 (by omega), chainHome 2 (by omega),
      chainHome 3 (by omega), chainHome 4 (by omega), chainHome 5 (by omega), chainHome 6 (by omega),
      chainHome 7 (by omega), ?_, rfl, fun _ _ _ _ _ => rfl⟩
    have b := chainHome 1 (by omega)
    have c := chainHome 2 (by omega)
    rw [Holds, Machine.read_write_ne (carry0 1 (by omega))] at b
    rw [Holds, Machine.read_write_ne (carry0 2 (by omega))] at c
    rw [Holds, Machine.read_write_self (nonzero 0 0 0 0).2.2.symm, b, c, BitVec.signExtend_xor]
    rfl
  have mem7 : (m6.write (carry 0) (m6.read (wordHome 0 1) ^^^ m6.read (wordHome 0 2))).mem = m6.mem :=
    rfl
  have frame7 : ∀ x, x ≠ carry 0 →
      (m6.write (carry 0) (m6.read (wordHome 0 1) ^^^ m6.read (wordHome 0 2))).read x = m6.read x :=
    fun _ other => Machine.read_write_ne other
  generalize m6.write (carry 0) (m6.read (wordHome 0 1) ^^^ m6.read (wordHome 0 2)) = m7
    at start2 mem7 frame7
  -- The padding block's rounds, with the chaining state waiting in the ring.
  have inv2 := fused_all start2 64 (by omega)
  rw [execBlock_append]
  generalize execBlock (fusedRoundsCode 64) m7 = m8 at inv2
  generalize hH1 : Spec.compression (Spec.inputWords (pairMessage m) 0) Spec.initial = H1
    at inv2 chain1
  have homes8 := homes_of_fused inv2
  generalize hW2 : Spec.rounds padWords H1 64 (by omega) = W2 at homes8
  have notCarry (t : Nat) : ringSlot t ∉ carryRegs.toList := by
    have all : ∀ b (_ : b < 16), wordRegs[b] ∉ carryRegs.toList := by decide
    exact all (t % 16) (Nat.mod_lt _ (by decide))
  have stash (j : Nat) (small : j < 8) : m8.read (ringSlot j) = (stateWord H1 j).signExtend 64 := by
    rw [inv2.frame _ (ringSlot_not_state j) (notCarry j) (ringSlot_ne j 0).2.1 (ringSlot_ne j 0).2.2,
      frame7 _ (ringSlot_ne j 0).1, chain1 j small]
    exact kept j small
  obtain ⟨fwd2, -, mem9, frame9⟩ := forward_upto (m := m8) (code := fun j => [keptForwardWord j])
    (work := stateWord W2) (add := stateWord H1)
    (fun j mj small waiting unchanged => keptForward_word j mj small (waiting j small (Nat.le_refl _))
      (by rw [Holds, unchanged _ (ringSlot_not_state j) (ringSlot_ne j 0).2.1]; exact stash j small))
    homes8 8 (by omega)
  rw [execBlock_append]
  generalize execBlock ((List.range 8).flatMap fun j => [keptForwardWord j]) m8 = m9 at fwd2 mem9 frame9
  -- Up to the digest, memory is untouched and only working registers have changed.
  have untouched : m9.mem = m.mem := by
    rw [mem9, inv2.mem, mem7, mem6, mem5, inv64.mem, mem3, mem2, mem1]
  have kept9 (x : Reg) (outside : x ∉ workRegs) : m9.read x = m.read x := by
    have notState : x ∉ stateRegs.toList := fun inside => outside (by simp [workRegs, inside])
    have notWord : x ∉ wordRegs.toList := fun inside => outside (by simp [workRegs, inside])
    have notCarryReg : x ∉ carryRegs.toList := fun inside => outside (by simp [workRegs, inside])
    have x0 : x ≠ t0 := ne_of_not_mem outside (by simp [workRegs])
    have x1 : x ≠ t1 := ne_of_not_mem outside (by simp [workRegs])
    have xc : x ≠ carry 0 := ne_of_not_mem outside (carry_mem 0)
    rw [frame9 x notState x0, inv2.frame x notState notCarryReg x0 x1, frame7 x xc, frame6 x notWord,
      frame5 x notState x0, inv64.frame x outside, frame3 x xc, frame2 x notState, frame1 x notWord x0]
  -- The digest code first reads the output address back from its frame slot.
  have pointer : m9.load (m9.read sp + (BitVec.ofNat 12 outSlot).signExtend 64) 8 = out := by
    rw [kept9 sp (by decide), signExtend_ofNat12 small, Machine.load_of_mem untouched]
  rw [digestCode, execBlock_cons, Instr.run, pointer]
  have chain2 (j : Nat) (small : j < 8) :
      stateWord (Spec.compression padWords H1) j = stateWord W2 j + stateWord H1 j := by
    rw [Spec.compression, hW2, stateWord_addState small, BitVec.add_comm]
  obtain ⟨stored, memD, frameD⟩ := digest_upto (m := m9.write t1 out) (out := out)
    (chain := stateWord (Spec.compression padWords H1)) (Machine.read_write_self (by decide))
    (fun j small => by
      rw [Holds, Machine.read_write_ne (stateHome_ne j small).2.2, chain2 j small]
      exact fwd2 j small)
    8 (by omega)
  generalize execBlock ((List.range 8).flatMap digestWord) (m9.write t1 out) = m10 at stored memD frameD
  refine ⟨?_, fun y outside => ?_, fun x outside => ?_⟩
  · rw [bytes_digest stored, combine_eq m, hH1]
  · rw [memD y outside, Machine.mem_write, untouched]
  · rw [frameD x (ne_of_not_mem outside (by simp [workRegs])),
      Machine.read_write_ne (ne_of_not_mem outside (by simp [workRegs])), kept9 x outside]

theorem fusedRoundsCode_straight : ∀ n, (fusedRoundsCode n).all Instr.straight
  | 0 => rfl
  | n + 1 => by
    simp only [fusedRoundsCode, List.all_append, fusedRoundsCode_straight n, Bool.true_and]
    simp [roundFusedCode, roundFusedCodeWith, rotations3Code, Instr.straight]

theorem pairCode_straight (outSlot : Nat) : ∀ i ∈ pairCode outSlot, i.straight := by
  apply List.all_eq_true.mp
  simp [pairCode, loadPairCode, loadPairWord, loadWordFrom, ivCode, ivWordCode, ivForwardCode,
    ivForwardWord, keepCode, keepWord, keptForwardCode, keptForwardWord, digestCode, digestWord,
    roundsCode_straight, fusedRoundsCode_straight, Instr.straight, List.all_flatMap, List.all_map]
  intro k _
  split <;> simp [Instr.straight]

end Ssz.Asm.Sha256
