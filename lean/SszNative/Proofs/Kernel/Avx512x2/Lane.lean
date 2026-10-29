import SszNative.Proofs.Kernel.Avx512x2.View

/-!
One lane of the thirty-two-lane kernel's compute loops: each lane runs two scalar SHA-256 computations.

Lane l of the first batch's registers and rows is message l of the first batch, and likewise for the second.
A round of either batch is the sixteen-lane kernel's round, with its sum seeded from a row.
The second batch's round is the first batch's with its registers renamed.
A schedule step reads four words of its batch from their rows and writes the word sixteen rounds on.
-/

namespace Ssz.Native.Kernel.Avx512x2

open Ssz.Sha256 Ssz.Native.Asm
open Ssz.Native.Kernel.Avx512 (role home tmp roundT round_eq_roundT roundsTo roundsTo_succ roundTail tail_lane K W PW
  W_next role_ne_t1 tableWord_k tableWord_pad laneRun assign_same assign_ne assign_apply ternlog_96 role_lt)

/-- Roles repeat every eight rounds. -/
theorem role_mod (t j : Nat) : role t j = role (t % 8) j := by
  -- A role depends on the round modulo 8.
  simp only [role, Nat.mod_mod]

/-- A first-block round, as its seed, the constant's addition, and the sixteen-lane kernel's tail. -/
theorem firstRound_eq (b k : Nat) :
    firstRound b k = forBatch b (.vaddMem Avx512.t1 (role k 7) ⟨words, wordRel b k⟩ ::
      .vaddMem Avx512.t1 Avx512.t1 ⟨consts, 64 * k⟩ :: roundTail k) := rfl

/-- A padding round, as its seed and the sixteen-lane kernel's tail. -/
theorem paddingRound_eq (b k : Nat) :
    paddingRound b k = forBatch b (.vaddMem Avx512.t1 (role k 7) ⟨consts, 64 * k⟩ :: roundTail k) := rfl

/-- The tail of a round acts on registers alone. -/
theorem roundTail_pure (k : Nat) : ∀ i ∈ roundTail k, pure i := by
  -- Every instruction of the tail is a move, an addition, a rotation, or a ternary function.
  simp [roundTail, Avx512.roundCode, pure]

/-- The renamed tail of a round acts on registers alone. -/
theorem roundTail_rename_pure (k : Nat) : ∀ i ∈ (roundTail k).map (rename swapReg), pure i := by
  -- Renaming keeps each instruction's kind.
  simp [roundTail, Avx512.roundCode, pure, rename]

/-- The running sum is not a working word, renamed or not. -/
theorem swap_role_ne_t1 (t j : Nat) : swapReg (role t j) ≠ swapReg Avx512.t1 := by
  -- Renaming is one to one, and a working word is not the sum.
  intro h
  have := congrArg swapReg h
  rw [swapReg_swapReg, swapReg_swapReg] at this
  exact role_ne_t1 t j this

/--
A seeded round on one lane: the working words take one round, from the sum of H and two rows.

The seed is the first row, and the second is added to the sum before the tail.
-/
theorem seeded_lane (G : Gpr → UInt64) (v : View) (t j : Nat) (hj : j < 8) (m₁ m₂ : Mem) :
    (viewRun G (.vaddMem Avx512.t1 (role (t % 8) 7) m₁ :: .vaddMem Avx512.t1 Avx512.t1 m₂ :: roundTail (t % 8)) v).regs
        (role (t + 1) j) =
      (roundT (Vector.ofFn fun j : Fin 8 => v.regs (role t j))
        (v.regs (role t 7) + v.mem (addrOf G m₁) + v.mem (addrOf G m₂)))[j] := by
  simp only [viewRun]
  rw [viewRun_pure G _ (roundTail_pure _) _ (fun _ => 0) 0, role_mod (t + 1),
    show (t + 1) % 8 = (t % 8 + 1) % 8 by omega, ← role_mod (t % 8 + 1)]
  simp only
  rw [tail_lane _ _ _ _ _ _ hj]
  -- The tail reads the working words, untouched by the seed, and the seeded sum.
  simp only [viewStep, assign_same]
  congr 2
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_ofFn]
  · rw [assign_ne _ _ _ _ (role_ne_t1 _ _), assign_ne _ _ _ _ (role_ne_t1 _ _), ← role_mod]
  · rw [← role_mod]

/-- A padding-style round on one lane: the working words take one round, from H plus one row. -/
theorem single_lane (G : Gpr → UInt64) (v : View) (t j : Nat) (hj : j < 8) (m₁ : Mem) :
    (viewRun G (.vaddMem Avx512.t1 (role (t % 8) 7) m₁ :: roundTail (t % 8)) v).regs (role (t + 1) j) =
      (roundT (Vector.ofFn fun j : Fin 8 => v.regs (role t j)) (v.regs (role t 7) + v.mem (addrOf G m₁)))[j] := by
  simp only [viewRun]
  rw [viewRun_pure G _ (roundTail_pure _) _ (fun _ => 0) 0, role_mod (t + 1),
    show (t + 1) % 8 = (t % 8 + 1) % 8 by omega, ← role_mod (t % 8 + 1)]
  simp only
  rw [tail_lane _ _ _ _ _ _ hj]
  -- The tail reads the working words, untouched by the seed, and the seeded sum.
  simp only [viewStep, assign_same]
  congr 2
  apply Vector.ext; intro i hi
  simp only [Vector.getElem_ofFn]
  · rw [assign_ne _ _ _ _ (role_ne_t1 _ _), ← role_mod]
  · rw [← role_mod]

/-- A renamed list of instructions on a lane runs as the list on the lane's renamed registers. -/
theorem viewRun_renamed (G : Gpr → UInt64) (body : List Instr) (h : ∀ i ∈ body, pure i) (v : View) (r : Vreg) :
    (viewRun G (body.map (rename swapReg)) v).regs r =
      (viewRun G body ⟨fun x => v.regs (swapReg x), v.mem⟩).regs (swapReg r) := by
  -- Both run on registers alone, where renaming commutes with running.
  have h' : ∀ i ∈ body.map (rename swapReg), pure i := by
    intro i hi
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
    have := h i' hi'
    cases i' <;> simp_all [pure, rename]
  rw [viewRun_pure G _ h' _ (fun _ => 0) 0, viewRun_pure G _ h _ (fun _ => 0) 0]
  exact laneRun_rename swapReg swapReg_swapReg _ _ _ _ _ _

/-- The second batch's seeded round on one lane: its working words take one round, as the first batch's do. -/
theorem seeded_lane_swap (G : Gpr → UInt64) (v : View) (t j : Nat) (hj : j < 8) (m₁ m₂ : Mem) :
    (viewRun G ((Instr.vaddMem Avx512.t1 (role (t % 8) 7) m₁ :: .vaddMem Avx512.t1 Avx512.t1 m₂ ::
        roundTail (t % 8)).map (rename swapReg)) v).regs (swapReg (role (t + 1) j)) =
      (roundT (Vector.ofFn fun j : Fin 8 => v.regs (swapReg (role t j)))
        (v.regs (swapReg (role t 7)) + v.mem (addrOf G m₁) + v.mem (addrOf G m₂)))[j] := by
  -- The seed and the constant's addition renamed, then the renamed tail.
  simp only [List.map_cons, viewRun, rename]
  rw [viewRun_renamed G _ (roundTail_pure _), swapReg_swapReg,
    viewRun_pure G _ (roundTail_pure _) _ (fun _ => 0) 0, role_mod (t + 1),
    show (t + 1) % 8 = (t % 8 + 1) % 8 by omega, ← role_mod (t % 8 + 1)]
  simp only
  rw [tail_lane _ _ _ _ _ _ hj]
  -- The renamed seed writes the renamed sum, and leaves the renamed working words.
  simp only [viewStep, assign_apply]
  congr 2
  · apply Vector.ext; intro i hi
    simp only [Vector.getElem_ofFn]
    rw [if_neg (swap_role_ne_t1 _ _), if_neg (swap_role_ne_t1 _ _), ← role_mod]
  · simp only [ite_true]; rw [← role_mod]

/-- The second batch's padding-style round on one lane. -/
theorem single_lane_swap (G : Gpr → UInt64) (v : View) (t j : Nat) (hj : j < 8) (m₁ : Mem) :
    (viewRun G ((Instr.vaddMem Avx512.t1 (role (t % 8) 7) m₁ :: roundTail (t % 8)).map (rename swapReg)) v).regs
        (swapReg (role (t + 1) j)) =
      (roundT (Vector.ofFn fun j : Fin 8 => v.regs (swapReg (role t j)))
        (v.regs (swapReg (role t 7)) + v.mem (addrOf G m₁)))[j] := by
  -- The seed renamed, then the renamed tail.
  simp only [List.map_cons, viewRun, rename]
  rw [viewRun_renamed G _ (roundTail_pure _), swapReg_swapReg,
    viewRun_pure G _ (roundTail_pure _) _ (fun _ => 0) 0, role_mod (t + 1),
    show (t + 1) % 8 = (t % 8 + 1) % 8 by omega, ← role_mod (t % 8 + 1)]
  simp only
  rw [tail_lane _ _ _ _ _ _ hj]
  -- The renamed seed writes the renamed sum, and leaves the renamed working words.
  simp only [viewStep, assign_apply]
  congr 2
  · apply Vector.ext; intro i hi
    simp only [Vector.getElem_ofFn]
    rw [if_neg (swap_role_ne_t1 _ _), ← role_mod]
  · simp only [ite_true]; rw [← role_mod]

/-- A schedule step on one lane: it stores the word sixteen on, from the four words it reads. -/
theorem scheduleStep_mem (G : Gpr → UInt64) (v : View) (b k : Nat) :
    (viewRun G (scheduleStep b k) v).mem = assign v.mem (addrOf G ⟨words, wordRel b (k + 16)⟩)
      (v.mem (addrOf G ⟨words, wordRel b k⟩) + sigma0 (v.mem (addrOf G ⟨words, wordRel b (k + 1)⟩)) +
        v.mem (addrOf G ⟨words, wordRel b (k + 9)⟩) + sigma1 (v.mem (addrOf G ⟨words, wordRel b (k + 14)⟩))) := by
  -- The step adds the four words, with the two small sigmas built from rotations and a shift.
  simp only [scheduleStep, viewRun, viewStep]
  congr 1
  simp [assign, sa, sb, sc, sd, ternlog_96, sigma0, sigma1]
  ac_rfl

/-- The first batch's round registers: its working words, its sum, and its temporaries. -/
def inA (d : Vreg) : Bool := d.val < 8 || (24 ≤ d.val && d.val < 29)

/-- The second batch's round registers. -/
def inB (d : Vreg) : Bool := 8 ≤ d.val && d.val < 21

/-- The schedule steps' registers. -/
def inS (d : Vreg) : Bool := (21 ≤ d.val && d.val < 24) || d.val == 29

/-- Whether every register a list writes passes a test. -/
def writesIn (P : Vreg → Bool) (body : List Instr) : Bool :=
  body.all fun i => (destOf i).all P

/-- Whether a list stores nothing. -/
def storesNothing (body : List Instr) : Bool :=
  body.all fun i => match i with | .vstore .. => false | _ => true

/-- Each part of a round writes only its own registers, and no round stores. -/
theorem rounds_write : ∀ k, k < 8 →
    writesIn inA (firstRound 0 k) = true ∧ writesIn inB (firstRound 1 k) = true ∧
    writesIn inA (paddingRound 0 k) = true ∧ writesIn inB (paddingRound 1 k) = true ∧
    writesIn inS (scheduleStep 0 k) = true ∧ writesIn inS (scheduleStep 1 k) = true ∧
    storesNothing (firstRound 0 k) = true ∧ storesNothing (firstRound 1 k) = true ∧
    storesNothing (paddingRound 0 k) = true ∧ storesNothing (paddingRound 1 k) = true := by
  -- Every round position, checked by evaluation.
  decide

/-- A list that stores nothing leaves every row. -/
theorem viewRun_mem_nothing (G : Gpr → UInt64) (body : List Instr) (h : storesNothing body = true) (v : View) :
    (viewRun G body v).mem = v.mem := by
  funext a
  apply viewRun_mem_other
  intro i hi
  have := List.all_eq_true.mp h i hi
  cases i <;> simp_all [storeOf]

/-- A list whose writes pass a test leaves every register failing it. -/
theorem viewRun_regs_keep (G : Gpr → UInt64) (body : List Instr) (P : Vreg → Bool)
    (h : writesIn P body = true) (v : View) (r : Vreg) (hr : P r = false) :
    (viewRun G body v).regs r = v.regs r := by
  apply viewRun_regs_other
  intro i hi e
  have := List.all_eq_true.mp h i hi
  rw [e] at this
  simp [hr] at this

/-- The table's rows, as one lane sees them. -/
def TableRows (T : Nat) (l : Fin 16) (v : View) : Prop :=
  ∀ row < 149, v.mem (T + 64 * row) = tableWord (16 * row + l.val)

/-- The scratch area misses the table. -/
def FrameApart (S T : Nat) : Prop := S + frame ≤ T ∨ T + tableSize ≤ S

/-- Schedule-word rows of the two batches are distinct for distinct batches or words. -/
theorem wordSlot_inj (b b' u u' : Nat) (hb : b < 2) (hb' : b' < 2) (hu : u < 80) (hu' : u' < 80)
    (h : wordSlot b u = wordSlot b' u') : b = b' ∧ u = u' := by
  -- Words sit 128 bytes apart, and the batches 64 bytes apart within each word's pair of rows.
  simp only [wordSlot, frame] at h
  omega

/-- A schedule-word row is not a table row. -/
theorem wordSlot_ne_table (S T b u row : Nat) (apart : FrameApart S T) (hb : b < 2) (hu : u < 80) (hrow : row < 149) :
    S + wordSlot b u ≠ T + 64 * row := by
  -- The word rows lie in the scratch area, and the table rows in the table.
  simp only [FrameApart, frame, tableSize] at apart
  simp only [wordSlot, frame]
  omega

/-- Block i's schedule pointer plus an offset is a schedule-word row. -/
theorem words_addr (G : Gpr → UInt64) (S i b m : Nat) (hw : (G words).toNat = S + wordsBase i) (hi : i < 8)
    (hm : m < 24) : addrOf G ⟨words, wordRel b m⟩ = S + wordSlot b (8 * i + m) := by
  -- The pointer moves 1024 bytes, eight pairs of rows, per block.
  simp only [addrOf, hw, wordsBase, wordRel, wordSlot, frame]
  omega

/-- Block i's table pointer plus a round's offset is that round's row. -/
theorem consts_addr (G : Gpr → UInt64) (T i k : Nat) (hc : (G consts).toNat = T + 512 * i) :
    addrOf G ⟨consts, 64 * k⟩ = T + 64 * (8 * i + k) := by
  -- The pointer moves eight rows per block.
  simp only [addrOf, hc]
  omega

/-- One lane of the first blocks before round t: both batches' working words, their schedule words so far, and the table. -/
def FirstInv (S T : Nat) (l : Fin 16) (m : Nat → ByteArray) (t : Nat) (v : View) : Prop :=
  (Vector.ofFn fun j : Fin 8 => v.regs (role t j)) = roundsTo initialState K (W (m 0)) t ∧
  (Vector.ofFn fun j : Fin 8 => v.regs (swapReg (role t j))) = roundsTo initialState K (W (m 1)) t ∧
  (∀ b < 2, ∀ u < t + 16, u < 64 → v.mem (S + wordSlot b u) = W (m b) u) ∧
  TableRows T l v

/-- The last two terms of a sum swap. -/
theorem add_swap (a b c : UInt32) : a + b + c = a + c + b := by
  rw [UInt32.add_assoc, UInt32.add_comm b, ← UInt32.add_assoc]

/-- The first batch's working words are below register 8. -/
theorem role_small (t j : Nat) : (role t j).val < 8 := role_lt t j

/-- The second batch's working words are registers 8 to 15. -/
theorem swap_role_range (t j : Nat) : 8 ≤ (swapReg (role t j)).val ∧ (swapReg (role t j)).val < 16 := by
  -- Renaming moves registers below 8 up by 8.
  have := role_lt t j
  simp only [swapReg, if_pos this]
  simp only [Fin.val_add]
  omega

/-- One round of both batches' first blocks, with their schedule steps when words remain to compute. -/
def firstStep (sched : Bool) (k : Nat) : List Instr :=
  firstRound 0 k ++ firstRound 1 k ++ (if sched then scheduleStep 0 k ++ scheduleStep 1 k else [])

set_option maxHeartbeats 1000000 in
/-- Round t of both batches keeps the first-block invariant one round on. -/
theorem first_step (G : Gpr → UInt64) (S T : Nat) (l : Fin 16) (m : Nat → ByteArray) (t : Nat) (v : View)
    (sched : Bool) (ht : t < 64) (hs : sched = true ↔ t < 48) (hw : (G words).toNat = S + wordsBase (t / 8))
    (hc : (G consts).toNat = T + 512 * (t / 8)) (apart : FrameApart S T) (inv : FirstInv S T l m t v) :
    FirstInv S T l m (t + 1) (viewRun G (firstStep sched (t % 8)) v) := by
  obtain ⟨rolesA, rolesB, sched₀, rows⟩ := inv
  have k8 : t % 8 < 8 := Nat.mod_lt _ (by omega)
  have i8 : t / 8 < 8 := by omega
  have tk : 8 * (t / 8) + t % 8 = t := by omega
  -- The addresses the round and the schedule steps read and write.
  have wAddr : ∀ b < 2, ∀ d < 17, addrOf G ⟨words, wordRel b (t % 8 + d)⟩ = S + wordSlot b (t + d) := by
    intro b hb d hd
    rw [words_addr G S (t / 8) b _ hw i8 (by omega)]
    congr 2; omega
  have wAddr0 : ∀ b < 2, addrOf G ⟨words, wordRel b (t % 8)⟩ = S + wordSlot b t := fun b hb2 => by
    simpa using wAddr b hb2 0 (by omega)
  have kAddr : addrOf G ⟨consts, 64 * (t % 8)⟩ = T + 64 * t := by
    rw [consts_addr G T (t / 8) _ hc, tk]
  have kRow : v.mem (T + 64 * t) = K t := by
    rw [rows t (by omega), Avx512.tableWord_k t l.val ht l.isLt]
  -- The parts: the first batch's round, the second's, then the schedule steps.
  let v1 := viewRun G (firstRound 0 (t % 8)) v
  let v2 := viewRun G (firstRound 1 (t % 8)) v1
  obtain ⟨wA, wB, -, -, wS0, wS1, nA, nB, -, -⟩ := rounds_write (t % 8) k8
  have m1 : v1.mem = v.mem := viewRun_mem_nothing G _ nA v
  have m2 : v2.mem = v1.mem := viewRun_mem_nothing G _ nB v1
  have split : viewRun G (firstStep sched (t % 8)) v =
      viewRun G (if sched then scheduleStep 0 (t % 8) ++ scheduleStep 1 (t % 8) else []) v2 := by
    simp only [firstStep, viewRun_append, v2, v1]
  -- The schedule steps leave every register below 21 and the temporaries 24 to 28.
  have keepS : ∀ r : Vreg, (r.val < 21 ∨ (24 ≤ r.val ∧ r.val < 29)) →
      (viewRun G (if sched then scheduleStep 0 (t % 8) ++ scheduleStep 1 (t % 8) else []) v2).regs r = v2.regs r := by
    intro r hr
    split
    · rw [viewRun_append, viewRun_regs_keep G _ _ wS1 _ r (by simp [inS]; omega),
        viewRun_regs_keep G _ _ wS0 _ r (by simp [inS]; omega)]
    · rfl
  -- The first batch's working words: one round from its own, untouched by the second batch.
  have roleA : ∀ j < 8, v2.regs (role (t + 1) j) = v1.regs (role (t + 1) j) := fun j _ =>
    viewRun_regs_keep G _ _ wB v1 _ (by have := role_small (t + 1) j; simp [inB]; omega)
  have roleB : ∀ j < 8, v1.regs (swapReg (role t j)) = v.regs (swapReg (role t j)) := fun j _ =>
    viewRun_regs_keep G _ _ wA v _ (by have := swap_role_range t j; simp [inA]; omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The first batch's round.
    apply Vector.ext; intro j hj
    simp only [Vector.getElem_ofFn]
    rw [split, keepS _ (by have := role_small (t + 1) j; omega), roleA j hj]
    simp only [v1]
    rw [firstRound_eq, show forBatch 0 _ = _ from if_pos rfl, seeded_lane G v t j hj, roundsTo_succ,
      round_eq_roundT, ← rolesA, wAddr0 0 (by omega), kAddr, kRow, sched₀ 0 (by omega) t (by omega) ht]
    simp only [Vector.getElem_ofFn]
    rw [add_swap]
  · -- The second batch's round, on the lanes the first batch's round left.
    apply Vector.ext; intro j hj
    simp only [Vector.getElem_ofFn]
    rw [split, keepS _ (by have := swap_role_range (t + 1) j; omega)]
    simp only [v2]
    rw [firstRound_eq, show forBatch 1 _ = _ from if_neg (by decide), seeded_lane_swap G v1 t j hj, roundsTo_succ,
      round_eq_roundT, ← rolesB, m1, wAddr0 1 (by omega), kAddr, kRow, sched₀ 1 (by omega) t (by omega) ht]
    have same : (Vector.ofFn fun j : Fin 8 => v1.regs (swapReg (role t j))) =
        Vector.ofFn fun j : Fin 8 => v.regs (swapReg (role t j)) := by
      apply Vector.ext; intro i hi
      simp only [Vector.getElem_ofFn]
      exact roleB i hi
    rw [same, roleB 7 (by omega)]
    simp only [Vector.getElem_ofFn]
    rw [add_swap]
  · -- The schedule words: kept, or the one each step computes.
    intro b hb u hu hu64
    rw [split]
    by_cases fresh : u = t + 16
    · subst fresh
      have early : t < 48 := by omega
      rw [if_pos (hs.mpr early), viewRun_append, scheduleStep_mem, scheduleStep_mem]
      -- Every address as a schedule-word row.
      have a0 := wAddr0 0 (by omega)
      have a1 := wAddr0 1 (by omega)
      rw [a0, a1, wAddr 0 (by omega) 1 (by omega), wAddr 0 (by omega) 9 (by omega), wAddr 0 (by omega) 14 (by omega),
        wAddr 0 (by omega) 16 (by omega), wAddr 1 (by omega) 1 (by omega), wAddr 1 (by omega) 9 (by omega),
        wAddr 1 (by omega) 14 (by omega), wAddr 1 (by omega) 16 (by omega), m2, m1]
      -- Distinct rows: the two stores, and each read against the first store.
      have ne : ∀ b' b'' d, b' < 2 → b'' < 2 → d < 17 → (b' ≠ b'' ∨ d ≠ 16) →
          S + wordSlot b' (t + d) ≠ S + wordSlot b'' (t + 16) := by
        intro b' b'' d h1 h2 h3 h4 e
        have := wordSlot_inj b' b'' (t + d) (t + 16) h1 h2 (by omega) (by omega) (by omega)
        omega
      have n0 := ne 1 0 0 (by omega) (by omega) (by omega) (by omega)
      have n1 := ne 1 0 1 (by omega) (by omega) (by omega) (by omega)
      have n9 := ne 1 0 9 (by omega) (by omega) (by omega) (by omega)
      have n14 := ne 1 0 14 (by omega) (by omega) (by omega) (by omega)
      have n16 := ne 0 1 16 (by omega) (by omega) (by omega) (by omega)
      simp only [Nat.add_zero] at n0
      rw [W_next _ t early]
      rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
      · rw [assign_ne _ _ _ _ n16, assign_same, sched₀ 0 (by omega) _ (by omega) (by omega),
          sched₀ 0 (by omega) _ (by omega) (by omega), sched₀ 0 (by omega) _ (by omega) (by omega),
          sched₀ 0 (by omega) _ (by omega) (by omega)]
      · rw [assign_same, assign_ne _ _ _ _ n0, assign_ne _ _ _ _ n1, assign_ne _ _ _ _ n9, assign_ne _ _ _ _ n14,
          sched₀ 1 (by omega) _ (by omega) (by omega), sched₀ 1 (by omega) _ (by omega) (by omega),
          sched₀ 1 (by omega) _ (by omega) (by omega), sched₀ 1 (by omega) _ (by omega) (by omega)]
    · -- Older words: no store of this round reaches them.
      have old : u < t + 16 := by omega
      have keepMem : ∀ x, (∀ b' < 2, x ≠ S + wordSlot b' (t + 16)) →
          (viewRun G (if sched then scheduleStep 0 (t % 8) ++ scheduleStep 1 (t % 8) else []) v2).mem x = v2.mem x := by
        intro x hx
        split
        · rename_i hsch
          have early := hs.mp hsch
          rw [viewRun_append, scheduleStep_mem, scheduleStep_mem, assign_ne _ _ _ _ (by
            rw [wAddr 1 (by omega) 16 (by omega)]; exact hx 1 (by omega)), assign_ne _ _ _ _ (by
            rw [wAddr 0 (by omega) 16 (by omega)]; exact hx 0 (by omega))]
        · rfl
      rw [keepMem _ (fun b' hb' e => by
        have := wordSlot_inj b b' u (t + 16) hb hb' (by omega) (by omega) (by omega); omega), m2, m1]
      exact sched₀ b hb u old hu64
  · -- The table rows: no store reaches them.
    intro row hrow
    rw [split]
    have : (viewRun G (if sched then scheduleStep 0 (t % 8) ++ scheduleStep 1 (t % 8) else []) v2).mem
        (T + 64 * row) = v2.mem (T + 64 * row) := by
      split
      · rename_i hsch
        have early := hs.mp hsch
        rw [viewRun_append, scheduleStep_mem, scheduleStep_mem, assign_ne _ _ _ _ (by
          rw [wAddr 1 (by omega) 16 (by omega)]
          exact (wordSlot_ne_table S T 1 _ row apart (by omega) (by omega) hrow).symm), assign_ne _ _ _ _ (by
          rw [wAddr 0 (by omega) 16 (by omega)]
          exact (wordSlot_ne_table S T 0 _ row apart (by omega) (by omega) hrow).symm)]
      · rfl
    rw [this, m2, m1]
    exact rows row hrow

/-- A block of eight first-block rounds of both batches keeps the invariant eight rounds on. -/
theorem first_block (G : Gpr → UInt64) (S T : Nat) (l : Fin 16) (m : Nat → ByteArray) (i : Nat) (v : View)
    (sched : Bool) (hi : i < 8) (hs : sched = true ↔ i < 6) (hw : (G words).toNat = S + wordsBase i)
    (hc : (G consts).toNat = T + 512 * i) (apart : FrameApart S T) (inv : FirstInv S T l m (8 * i) v) :
    FirstInv S T l m (8 * i + 8) (viewRun G ((List.range 8).flatMap (firstStep sched)) v) := by
  -- One round at a time, each at round 8i + k.
  suffices h : ∀ k ≤ 8, FirstInv S T l m (8 * i + k) (viewRun G ((List.range k).flatMap (firstStep sched)) v) from
    h 8 (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => exact inv
  | succ k ih =>
    rw [viewRun_flatMap_succ]
    have step := first_step G S T l m (8 * i + k) _ sched (by omega) (by rw [hs]; omega)
      (by rw [show (8 * i + k) / 8 = i by omega]; exact hw) (by rw [show (8 * i + k) / 8 = i by omega]; exact hc) apart
      (ih (by omega))
    rwa [show (8 * i + k) % 8 = k by omega] at step

/-- One lane of the padding blocks before round t: both batches' working words, and the table. -/
def PadInv (T : Nat) (l : Fin 16) (mid : Nat → Vector UInt32 8) (t : Nat) (v : View) : Prop :=
  (Vector.ofFn fun j : Fin 8 => v.regs (role t j)) = roundsTo (mid 0) K PW t ∧
  (Vector.ofFn fun j : Fin 8 => v.regs (swapReg (role t j))) = roundsTo (mid 1) K PW t ∧
  TableRows T l v

/-- One padding round of both batches. -/
def padStep (k : Nat) : List Instr := paddingRound 0 k ++ paddingRound 1 k

/-- Round t of both batches' padding blocks keeps the invariant one round on. -/
theorem pad_step (G : Gpr → UInt64) (T : Nat) (l : Fin 16) (mid : Nat → Vector UInt32 8) (t : Nat) (v : View)
    (ht : t < 64) (hc : (G consts).toNat = T + 512 * (8 + t / 8)) (inv : PadInv T l mid t v) :
    PadInv T l mid (t + 1) (viewRun G (padStep (t % 8)) v) := by
  obtain ⟨rolesA, rolesB, rows⟩ := inv
  have k8 : t % 8 < 8 := Nat.mod_lt _ (by omega)
  obtain ⟨-, -, pA, pB, -, -, -, -, nA, nB⟩ := rounds_write (t % 8) k8
  -- The round's row: its constant plus the padding block's word, from the table.
  have pAddr : addrOf G ⟨consts, 64 * (t % 8)⟩ = T + 64 * (64 + t) := by
    rw [consts_addr G T (8 + t / 8) _ hc]; congr 1; omega
  have pRow : v.mem (T + 64 * (64 + t)) = K t + PW t := by
    rw [rows _ (by omega), show 16 * (64 + t) + l.val = 16 * (64 + t) + l.val from rfl,
      Avx512.tableWord_pad t l.val ht l.isLt]
  let v1 := viewRun G (paddingRound 0 (t % 8)) v
  have m1 : v1.mem = v.mem := viewRun_mem_nothing G _ nA v
  have split : viewRun G (padStep (t % 8)) v = viewRun G (paddingRound 1 (t % 8)) v1 := by
    simp only [padStep, viewRun_append, v1]
  have roleB : ∀ j < 8, v1.regs (swapReg (role t j)) = v.regs (swapReg (role t j)) := fun j _ =>
    viewRun_regs_keep G _ _ pA v _ (by have := swap_role_range t j; simp [inA]; omega)
  refine ⟨?_, ?_, ?_⟩
  · -- The first batch's round, untouched by the second batch's.
    apply Vector.ext; intro j hj
    simp only [Vector.getElem_ofFn]
    rw [split, viewRun_regs_keep G _ _ pB v1 _ (by have := role_small (t + 1) j; simp [inB]; omega)]
    simp only [v1]
    rw [paddingRound_eq, show forBatch 0 _ = _ from if_pos rfl, single_lane G v t j hj, roundsTo_succ,
      round_eq_roundT, ← rolesA, pAddr, pRow]
    simp only [Vector.getElem_ofFn]
    simp only [UInt32.add_assoc]
  · -- The second batch's round, on the lanes the first batch's round left.
    apply Vector.ext; intro j hj
    simp only [Vector.getElem_ofFn]
    rw [split, paddingRound_eq, show forBatch 1 _ = _ from if_neg (by decide), single_lane_swap G v1 t j hj,
      roundsTo_succ, round_eq_roundT, ← rolesB, m1, pAddr, pRow]
    have same : (Vector.ofFn fun j : Fin 8 => v1.regs (swapReg (role t j))) =
        Vector.ofFn fun j : Fin 8 => v.regs (swapReg (role t j)) := by
      apply Vector.ext; intro i hi
      simp only [Vector.getElem_ofFn]
      exact roleB i hi
    rw [same, roleB 7 (by omega)]
    simp only [Vector.getElem_ofFn]
    simp only [UInt32.add_assoc]
  · -- No padding round stores.
    intro row hrow
    rw [split, viewRun_mem_nothing G _ nB, m1]
    exact rows row hrow

/-- A block of eight padding rounds of both batches keeps the invariant eight rounds on. -/
theorem pad_block (G : Gpr → UInt64) (T : Nat) (l : Fin 16) (mid : Nat → Vector UInt32 8) (i : Nat) (v : View)
    (hi : i < 8) (hc : (G consts).toNat = T + 512 * (8 + i)) (inv : PadInv T l mid (8 * i) v) :
    PadInv T l mid (8 * i + 8) (viewRun G ((List.range 8).flatMap padStep) v) := by
  -- One round at a time, each at round 8i + k.
  suffices h : ∀ k ≤ 8, PadInv T l mid (8 * i + k) (viewRun G ((List.range k).flatMap padStep) v) from
    h 8 (Nat.le_refl _)
  intro k hk
  induction k with
  | zero => exact inv
  | succ k ih =>
    rw [viewRun_flatMap_succ]
    have step := pad_step G T l mid (8 * i + k) _ (by omega)
      (by rw [show (8 * i + k) / 8 = i by omega]; exact hc) (ih (by omega))
    rwa [show (8 * i + k) % 8 = k by omega] at step

/-- No padding round stores, so a padding block leaves every row. -/
theorem pad_block_mem (G : Gpr → UInt64) (v : View) :
    (viewRun G ((List.range 8).flatMap padStep) v).mem = v.mem := by
  apply viewRun_mem_nothing
  -- Every round of the block, checked by evaluation.
  decide +kernel

end Ssz.Native.Kernel.Avx512x2
