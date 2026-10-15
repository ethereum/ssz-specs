import Asm.Memory

/-! Spilling registers to a stack frame and reloading them, for any list of slots. -/

namespace Ssz.Asm

/-- Slots that fit a 12-bit immediate offset and never overlap one another. -/
def SlotsApart (slots : List (Reg × Nat)) : Prop :=
  (∀ s ∈ slots, s.2 + 8 < 2048) ∧ slots.Pairwise fun s t => s.2 + 8 ≤ t.2 ∨ t.2 + 8 ≤ s.2

theorem spills_cons {base : Reg} {s : Reg × Nat} {rest : List (Reg × Nat)} :
    spills base (s :: rest) = .sd s.1 base (BitVec.ofNat 12 s.2) :: spills base rest :=
  rfl

theorem reloads_cons {base : Reg} {s : Reg × Nat} {rest : List (Reg × Nat)} :
    reloads base (s :: rest) = .ld s.1 base (BitVec.ofNat 12 s.2) :: reloads base rest :=
  rfl

theorem spills_read {base : Reg} {m : Machine} {r : Reg} :
    ∀ {slots : List (Reg × Nat)}, (execBlock (spills base slots) m).read r = m.read r
  | [] => rfl
  | _ :: _ => by
    -- A store changes no register.
    simp only [spills_cons, execBlock_cons]
    exact (spills_read (m := Machine.store ..)).trans Machine.read_store

/-- Bytes outside every slot keep their old contents. -/
theorem spills_mem {base : Reg} {y : BitVec 64} :
    ∀ {slots : List (Reg × Nat)} {m : Machine}, (∀ s ∈ slots, s.2 < 2048) →
      (∀ s ∈ slots, ¬Within y (m.read base + BitVec.ofNat 64 s.2) 8) →
      (execBlock (spills base slots) m).mem y = m.mem y
  | [], _, _, _ => rfl
  | s :: rest, m, small, outside => by
    simp only [spills_cons, execBlock_cons, Instr.run]
    -- The base register is the same after the first store, so the later slots are where they were.
    rw [spills_mem (fun t mem => small t (by simp [mem])) (fun t mem => by
        simpa using outside t (by simp [mem])),
      signExtend_ofNat12 (small s (by simp)),
      Machine.mem_store_of_not_within (outside s (by simp))]

/-- Each slot holds the register spilled to it. -/
theorem spills_load {base : Reg} :
    ∀ {slots : List (Reg × Nat)} {m : Machine}, SlotsApart slots → ∀ s ∈ slots,
      (execBlock (spills base slots) m).load (m.read base + BitVec.ofNat 64 s.2) 8 = m.read s.1
  | [], _, _, _, absent => by simp at absent
  | first :: rest, m, ⟨small, apart⟩, s, mem => by
    simp only [List.pairwise_cons] at apart
    simp only [spills_cons, execBlock_cons, Instr.run]
    rw [signExtend_ofNat12 (by have := small first (by simp); omega)]
    rcases List.mem_cons.mp mem with here | later
    · -- Later slots miss this one, so the first store is still there to read.
      subst here
      have same := Machine.load_congr (n := 8) (a := m.read base + BitVec.ofNat 64 s.2)
        (m := execBlock (spills base rest)
          (m.store (m.read base + BitVec.ofNat 64 s.2) 8 (m.read s.1)))
        (m' := m.store (m.read base + BitVec.ofNat 64 s.2) 8 (m.read s.1))
        fun k within => spills_mem (fun t mem => by have := small t (by simp [mem]); omega)
          fun t mem => by
            simpa using disjoint_offsets (a := m.read base) (by have := apart.1 t mem; omega)
              (by have := small s (by simp); have := small t (by simp [mem]); omega) _
              ((within_offset (by omega)).mpr within)
      rw [same]
      exact Machine.load_store_self8
    · -- A later slot is read in the machine after the first store, whose registers are unchanged.
      have := spills_load (base := base) (m := Machine.store m (m.read base + BitVec.ofNat 64 first.2) 8
        (m.read first.1)) ⟨fun t mem => small t (by simp [mem]), apart.2⟩ s later
      simpa using this

/-- Each reloaded register holds its slot, and every other register keeps its value. -/
theorem reloads_spec {base : Reg} :
    ∀ {slots : List (Reg × Nat)} {m : Machine}, (∀ s ∈ slots, s.2 < 2048) →
      (slots.map Prod.fst).Pairwise (· ≠ ·) → (∀ s ∈ slots, s.1 ≠ base ∧ s.1 ≠ 0) →
      (execBlock (reloads base slots) m).mem = m.mem ∧
        (∀ s ∈ slots, (execBlock (reloads base slots) m).read s.1 =
          m.load (m.read base + BitVec.ofNat 64 s.2) 8) ∧
        ∀ q, q ∉ slots.map Prod.fst → (execBlock (reloads base slots) m).read q = m.read q
  | [], _, _, _, _ => by simp [reloads]
  | first :: rest, m, small, distinct, regs => by
    simp only [List.map_cons, List.pairwise_cons] at distinct
    simp only [reloads_cons, execBlock_cons, Instr.run]
    rw [signExtend_ofNat12 (small first (by simp))]
    obtain ⟨mem, loaded, kept⟩ := reloads_spec (base := base)
      (m := m.write first.1 (m.load (m.read base + BitVec.ofNat 64 first.2) 8))
      (fun t mem => small t (by simp [mem])) distinct.2 (fun t mem => regs t (by simp [mem]))
    -- The first load leaves memory and the base register alone.
    have baseSame : (m.write first.1 (m.load (m.read base + BitVec.ofNat 64 first.2) 8)).read base =
        m.read base := Machine.read_write_ne (Ne.symm (regs first (by simp)).1)
    refine ⟨by rw [mem]; rfl, fun s inside => ?_, fun q outside => ?_⟩
    · rcases List.mem_cons.mp inside with here | later
      · -- No later load writes the first register.
        subst here
        rw [kept s.1 (fun mem => distinct.1 s.1 mem rfl)]
        exact Machine.read_write_self (regs s (by simp)).2
      · rw [loaded s later, baseSame, Machine.load_write]
    · simp only [List.map_cons, List.mem_cons, not_or] at outside
      rw [kept q outside.2, Machine.read_write_ne outside.1]

end Ssz.Asm
