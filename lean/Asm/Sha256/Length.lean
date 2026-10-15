import Asm.Sha256.Pair

/-! Instruction counts of the SHA-256 code, derived from its structure rather than by evaluating it. -/

namespace Ssz.Asm.Sha256

theorem length_flatMap_range {f : Nat → List Instr} {c : Nat} (each : ∀ k, (f k).length = c) :
    ∀ n, ((List.range n).flatMap f).length = n * c
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, length_flatMap_range each n,
      List.flatMap_singleton, each, Nat.succ_mul]

theorem length_map_range {f : Nat → Instr} : ∀ n, ((List.range n).map f).length = n := by
  simp

theorem roundsCode_length : ∀ n, (roundsCode n).length = 31 * n + 19 * (n - 16)
  | 0 => rfl
  | n + 1 => by
    rw [roundsCode, List.length_append, List.length_append, roundsCode_length n]
    split <;> simp [scheduleCode, scheduleCodeWith, rotations2Code, roundCode, roundCodeWith,
      rotations3Code] <;> omega

theorem fusedRoundsCode_length : ∀ n, (fusedRoundsCode n).length = 30 * n
  | 0 => rfl
  | n + 1 => by
    rw [fusedRoundsCode, List.length_append, fusedRoundsCode_length n]
    simp [roundFusedCode, roundFusedCodeWith, rotations3Code]
    omega

theorem pairCode_length (outSlot : Nat) : (pairCode outSlot).length = 5091 := by
  simp only [pairCode, loadPairCode, ivCode, ivForwardCode, keepCode, keptForwardCode, digestCode,
    List.length_append, List.length_cons, List.length_nil, roundsCode_length, fusedRoundsCode_length,
    length_map_range]
  rw [length_flatMap_range (c := 10) (fun k => by unfold loadPairWord; split <;> rfl),
    length_flatMap_range (c := 2) (fun _ => rfl), length_flatMap_range (c := 3) (fun _ => rfl),
    length_flatMap_range (c := 7) (fun _ => rfl)]

end Ssz.Asm.Sha256
