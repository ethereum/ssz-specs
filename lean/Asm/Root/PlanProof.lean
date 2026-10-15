import Asm.Root.Plan
import Asm.Merkle.Levels
import Ssz.Proofs.Flat.Bounded
import Ssz.Proofs.Hash.Sha256Laws

/-! A plan's steps leave each slot holding the node the specification computes there. -/

set_option linter.unusedSimpArgs false

namespace Ssz.Asm.Root

open Ssz
open Ssz.Asm.Merkle (zeroAt)

-- The node hash is SHA-256, which no proof here needs to evaluate.
attribute [local irreducible] Ssz.combine

/-- A slot holds a node. -/
def Holds (s : Scratch) (offset : Nat) (node : Bytes) : Prop :=
  readSlot s offset = node

/-- Slots hold nodes, pairwise. -/
def HoldsAll (s : Scratch) : List Nat → List Bytes → Prop
  | [], [] => True
  | offset :: offsets, node :: nodes => Holds s offset node ∧ HoldsAll s offsets nodes
  | _, _ => False

/-- Every step writes at or above an offset. -/
def WritesAbove (steps : List Step) (free : Nat) : Prop :=
  ∀ step ∈ steps, free ≤ step.dst

/-- Every step writes below an offset. -/
def WritesBelow (steps : List Step) (limit : Nat) : Prop :=
  ∀ step ∈ steps, step.dst + 32 ≤ limit

theorem runPlan_append {first second : List Step} {s : Scratch} :
    runPlan (first ++ second) s = runPlan second (runPlan first s) := by
  simp [runPlan, List.foldl_append]

theorem step_outside {step : Step} {s : Scratch} {a : Nat} (outside : a < step.dst ∨ step.dst + 32 ≤ a) :
    step.run s a = s a := by
  cases step with
  | chunk dst src len =>
    simp only [Step.run, Step.dst] at *
    rw [if_neg (by omega)]
  | hash dst left right =>
    simp only [Step.run, Step.dst] at *
    rw [if_neg (by omega)]

/-- Bytes below every step's slot are never written. -/
theorem runPlan_below {steps : List Step} {free a : Nat} (above : WritesAbove steps free) (below : a < free) :
    ∀ s, runPlan steps s a = s a := by
  induction steps with
  | nil => intro s; rfl
  | cons step steps ih =>
    intro s
    simp only [runPlan, List.foldl_cons]
    rw [show List.foldl (fun s step => step.run s) (step.run s) steps = runPlan steps (step.run s) from rfl,
      ih (fun t mem => above t (by simp [mem])), step_outside (Or.inl (by have := above step (by simp); omega))]

/-- A slot below every step's slot keeps its node. -/
theorem holds_below {steps : List Step} {free offset : Nat} {s : Scratch} {node : Bytes}
    (above : WritesAbove steps free) (low : offset + 32 ≤ free) (held : Holds s offset node) :
    Holds (runPlan steps s) offset node := by
  unfold Holds readSlot at *
  rw [← held]
  congr 1
  funext i
  exact runPlan_below above (by omega) s

theorem holdsAll_below {steps : List Step} {free : Nat} {s : Scratch} :
    ∀ {offsets : List Nat} {nodes : List Bytes}, WritesAbove steps free →
      (∀ o ∈ offsets, o + 32 ≤ free) → HoldsAll s offsets nodes → HoldsAll (runPlan steps s) offsets nodes
  | [], [], _, _, _ => trivial
  | o :: os, n :: ns, above, low, ⟨first, rest⟩ =>
    ⟨holds_below above (low o (by simp)) first,
      holdsAll_below above (fun o' mem => low o' (by simp [mem])) rest⟩
  | [], _ :: _, _, _, held | _ :: _, [], _, _, held => held.elim

/-- A hash step leaves the hash of its two slots in its own. -/
theorem hash_holds {dst left right : Nat} {s : Scratch} {l r : Bytes}
    (heldLeft : Holds s left l) (heldRight : Holds s right r) :
    Holds ((Step.hash dst left right).run s) dst (combine l r) := by
  have size : (combine l r).size = 32 := by unfold combine; simp
  have point (i : Nat) (below : i < 32) :
      (Step.hash dst left right).run s (dst + i) = (combine l r)[i]! := by
    simp only [Step.run]
    rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
    unfold Holds at heldLeft heldRight
    rw [heldLeft, heldRight]
  show Array.ofFn (fun i : Fin 32 => (Step.hash dst left right).run s (dst + i.val)) = combine l r
  apply Array.ext
  · rw [Array.size_ofFn, size]
  · intro i within _
    rw [Array.getElem_ofFn, point i (by simpa using within), getElem!_pos (combine l r) i (by omega)]

theorem runPlan_cons {step : Step} {steps : List Step} {s : Scratch} :
    runPlan (step :: steps) s = runPlan steps (step.run s) :=
  rfl

theorem writesAbove_singleton {step : Step} {free : Nat} (above : free ≤ step.dst) :
    WritesAbove [step] free := by
  intro t mem
  simp at mem
  subst mem
  exact above

/-- One level of a tree: parent i holds the hash of nodes 2i and 2i + 1, or of an odd node and the fill. -/
theorem pairSteps_spec {fill : Nat} {f : Bytes} (free : Nat) (nodes : List Nat) :
    ∀ (level : List Bytes) (s : Scratch),
      HoldsAll s nodes level → (∀ o ∈ nodes, o + 32 ≤ free) → Holds s fill f → fill + 32 ≤ free →
      WritesAbove (pairSteps fill free nodes).1 free ∧
        (pairSteps fill free nodes).2.length = (level.length + 1) / 2 ∧
        (∀ o ∈ (pairSteps fill free nodes).2, free ≤ o ∧ o + 32 ≤ free + 32 * ((level.length + 1) / 2)) ∧
        WritesBelow (pairSteps fill free nodes).1 (free + 32 * ((level.length + 1) / 2)) ∧
        HoldsAll (runPlan (pairSteps fill free nodes).1 s) (pairSteps fill free nodes).2
          (pairLevel combine f level) := by
  induction free, nodes using pairSteps.induct with
  | case1 free =>
    intro level s held _ _ _
    cases level with
    | nil => simp [pairSteps, WritesAbove, WritesBelow, HoldsAll, pairLevel]
    | cons _ _ => exact held.elim
  | case2 free node =>
    intro level s held low heldFill lowFill
    match level, held with
    | [x], ⟨heldX, _⟩ =>
      simp only [pairSteps, List.length_singleton]
      refine ⟨writesAbove_singleton (by simp [Step.dst]), by simp, by simp, ?_, ?_⟩
      · intro t mem
        simp at mem
        subst mem
        simp [Step.dst]
      · exact ⟨hash_holds heldX heldFill, trivial⟩
  | case3 free left right rest ih =>
    intro level s held low heldFill lowFill
    match level, held with
    | a :: b :: more, ⟨heldA, heldB, heldRest⟩ =>
      -- The first parent goes to the free slot, and the rest of the level starts one slot further on.
      have first : WritesAbove [Step.hash free left right] free := writesAbove_singleton (by simp [Step.dst])
      have restHeld := holdsAll_below (s := s) first (fun o mem => low o (by simp [mem])) heldRest
      have fillHeld := holds_below first lowFill heldFill
      obtain ⟨above, length, offsets, below, holds⟩ := ih more _
        restHeld (fun o mem => by have := low o (by simp [mem]); omega) fillHeld (by omega)
      simp only [pairSteps, List.length_cons]
      refine ⟨?_, by rw [length]; omega, ?_, ?_, ?_⟩
      · intro t mem
        simp only [List.mem_cons] at mem
        rcases mem with rfl | mem
        · simp [Step.dst]
        · have := above t mem
          omega
      · intro o mem
        simp only [List.mem_cons] at mem
        rcases mem with rfl | mem
        · omega
        · have := offsets o mem
          omega
      · intro t mem
        simp only [List.mem_cons] at mem
        rcases mem with rfl | mem
        · simp [Step.dst]
          omega
        · have := below t mem
          omega
      · rw [runPlan_cons]
        exact ⟨holds_below above (by omega) (hash_holds heldA heldB), holds⟩

/-- The zero subtrees of heights 0 to D sit at consecutive slots from a base. -/
def ZeroTable (s : Scratch) (zeros depth : Nat) : Prop :=
  ∀ k, k ≤ depth → Holds s (zeros + 32 * k) (zeroAt k)

theorem zeroTable_below {steps : List Step} {free zeros depth : Nat} {s : Scratch}
    (above : WritesAbove steps free) (low : zeros + 32 * (depth + 1) ≤ free) (table : ZeroTable s zeros depth) :
    ZeroTable (runPlan steps s) zeros depth :=
  fun k within => holds_below above (by
    have : 32 * k + 32 ≤ 32 * (depth + 1) := by omega
    omega) (table k within)

theorem holdsAll_length {s : Scratch} : ∀ {offsets : List Nat} {nodes : List Bytes},
    HoldsAll s offsets nodes → offsets.length = nodes.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, rest⟩ => by simp [holdsAll_length rest]
  | [], _ :: _, held | _ :: _, [], held => held.elim

/-- A tree folded up from a level of nodes: its root is the upward fold's first node, or the zero subtree. -/
theorem treeSteps_spec (zeros : Nat) (remaining height : Nat) (nodes : List Nat) (free : Nat) :
    ∀ (level : List Bytes) (s : Scratch),
      HoldsAll s nodes level → (∀ o ∈ nodes, o + 32 ≤ free) → ZeroTable s zeros (height + remaining) →
      zeros + 32 * (height + remaining + 1) ≤ free →
      WritesAbove (treeSteps zeros remaining height nodes free).steps free ∧
        WritesBelow (treeSteps zeros remaining height nodes free).steps
          (treeSteps zeros remaining height nodes free).free ∧
        free ≤ (treeSteps zeros remaining height nodes free).free ∧
        (treeSteps zeros remaining height nodes free).root + 32 ≤
          (treeSteps zeros remaining height nodes free).free ∧
        Holds (runPlan (treeSteps zeros remaining height nodes free).steps s)
          (treeSteps zeros remaining height nodes free).root
          ((foldUpTo combine zeroChunk remaining height level).headD (zeroAt (height + remaining))) := by
  induction remaining, height, nodes, free using treeSteps.induct zeros with
  | case1 height nodes free =>
    intro level s held low table zerosLow
    simp only [treeSteps, Nat.add_zero]
    refine ⟨by simp [WritesAbove], by simp [WritesBelow], Nat.le_refl _, ?_, ?_⟩
    · cases nodes with
      | nil => simp; omega
      | cons o _ => simpa using low o (by simp)
    · cases nodes with
      | nil =>
        cases level with
        | nil => exact table height (Nat.le_refl _)
        | cons _ _ => exact held.elim
      | cons o os =>
        cases level with
        | nil => exact held.elim
        | cons l ls => exact held.1
  | case2 remaining height nodes free lvl ih =>
    intro level s held low table zerosLow
    simp only [lvl] at ih
    have fill := table height (by omega)
    obtain ⟨above, length, offsets, below, holds⟩ := pairSteps_spec (fill := zeros + 32 * height)
      (f := zeroAt height) free nodes level s held low fill (by
        have : 32 * height + 32 ≤ 32 * (height + (remaining + 1) + 1) := by omega
        omega)
    have rest := ih (pairLevel combine (zeroAt height) level)
      (runPlan (pairSteps (zeros + 32 * height) free nodes).1 s) holds
      (fun o mem => by have := offsets o mem; rw [length]; omega)
      (by rw [show height + 1 + remaining = height + (remaining + 1) by omega]
          exact zeroTable_below above (by omega) table)
      (by omega)
    obtain ⟨restAbove, restBelow, restFree, restRoot, restHolds⟩ := rest
    simp only [treeSteps]
    refine ⟨?_, ?_, by omega, restRoot, ?_⟩
    · intro t mem
      rcases List.mem_append.mp mem with mem | mem
      · exact above t mem
      · have := restAbove t mem
        omega
    · intro t mem
      rcases List.mem_append.mp mem with mem | mem
      · have := below t mem
        omega
      · exact restBelow t mem
    · rw [runPlan_append, show height + (remaining + 1) = height + 1 + remaining by omega]
      exact restHolds

/-- Bytes of an encoding sit at consecutive offsets from a start. -/
def Encodes (s : Scratch) (src : Nat) (bytes : Bytes) : Prop :=
  ∀ i (within : i < bytes.size), s (src + i) = bytes[i]

/-- Chunk c of packed bytes: the bytes from 32c on, padded with zeros. -/
theorem packBytes_get {bytes : Bytes} {c : Nat} (within : c < (packBytes bytes).size) :
    (packBytes bytes)[c] = Array.ofFn (n := 32) fun j =>
      if 32 * c + j.val < bytes.size then bytes[32 * c + j.val]! else 0 := by
  simp only [packBytes, Array.getElem_ofFn]
  apply Array.ext
  · simp [bytesPerChunk]
    omega
  · intro j left right
    simp only [Array.size_ofFn] at right
    simp only [Array.getElem_ofFn]
    by_cases inside : 32 * c + j < bytes.size
    · rw [if_pos inside, Array.getElem_append_left (by simp [bytesPerChunk]; omega)]
      simp [bytesPerChunk, Nat.mul_comm c, getElem!_pos bytes (32 * c + j) inside]
    · rw [if_neg inside, Array.getElem_append_right (by simp [bytesPerChunk]; omega)]
      simp

/-- A chunk step copies its run of bytes into its slot and zero-fills the rest. -/
theorem chunk_holds {dst src len : Nat} {s : Scratch} :
    Holds ((Step.chunk dst src len).run s) dst
      (Array.ofFn (n := 32) fun j => if j.val < len then s (src + j.val) else 0) := by
  unfold Holds readSlot
  congr 1
  funext j
  simp only [Step.run]
  rw [if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]

theorem holdsAll_snoc {s : Scratch} {o : Nat} {x : Bytes} : ∀ {offsets : List Nat} {nodes : List Bytes},
    HoldsAll s offsets nodes → Holds s o x → HoldsAll s (offsets ++ [o]) (nodes ++ [x])
  | [], [], _, held => ⟨held, trivial⟩
  | _ :: _, _ :: _, ⟨first, rest⟩, held => ⟨first, holdsAll_snoc rest held⟩
  | [], _ :: _, h, _ | _ :: _, [], h, _ => h.elim

/-- The first c chunks of packed bytes, each in its slot. -/
theorem chunkSteps_upto {src size free : Nat} {bytes : Bytes} {s : Scratch} (enc : Encodes s src bytes)
    (sized : bytes.size = size) (low : src + size ≤ free) :
    ∀ c, c ≤ (size + 31) / 32 →
      let steps := (List.range c).map fun i => Step.chunk (free + 32 * i) (src + 32 * i) (min 32 (size - 32 * i))
      WritesAbove steps free ∧ WritesBelow steps (free + 32 * c) ∧
        HoldsAll (runPlan steps s) ((List.range c).map fun i => free + 32 * i) ((packBytes bytes).toList.take c)
  | 0, _ => by simp [WritesAbove, WritesBelow, runPlan, HoldsAll]
  | c + 1, bound => by
    intro steps
    obtain ⟨above, below, held⟩ := chunkSteps_upto enc sized low c (by omega)
    simp only [steps, List.range_succ, List.map_append, List.map_cons, List.map_nil]
    have chunkCount : c < (packBytes bytes).size := by simp [bytesPerChunk, sized]; omega
    refine ⟨?_, ?_, ?_⟩
    · intro t mem
      rcases List.mem_append.mp mem with mem | mem
      · exact above t mem
      · simp at mem; subst mem; simp [Step.dst]
    · intro t mem
      rcases List.mem_append.mp mem with mem | mem
      · have := below t mem; omega
      · simp at mem; subst mem; simp [Step.dst]; omega
    · rw [runPlan_append, List.take_add_one, Array.getElem?_toList, Array.getElem?_eq_getElem chunkCount]
      simp only [Option.toList_some]
      apply holdsAll_snoc
      · exact holdsAll_below (free := free + 32 * c) (writesAbove_singleton (by simp [Step.dst]))
          (fun o mem => by
            simp only [List.mem_map, List.mem_range] at mem
            obtain ⟨i, below, rfl⟩ := mem
            omega) held
      · -- The chunk's source bytes are untouched by the earlier chunks, which sit above the encoding.
        have chunk := chunk_holds (dst := free + 32 * c) (src := src + 32 * c)
          (len := min 32 (size - 32 * c)) (s := runPlan ((List.range c).map fun i =>
            Step.chunk (free + 32 * i) (src + 32 * i) (min 32 (size - 32 * i))) s)
        show Holds (runPlan [_] _) _ _
        rw [show runPlan [Step.chunk (free + 32 * c) (src + 32 * c) (min 32 (size - 32 * c))] _ =
          (Step.chunk (free + 32 * c) (src + 32 * c) (min 32 (size - 32 * c))).run _ from rfl]
        unfold Holds at chunk ⊢
        rw [chunk, packBytes_get chunkCount]
        congr 1
        funext j
        by_cases inside : 32 * c + j.val < bytes.size
        · rw [if_pos (by omega), if_pos inside, runPlan_below above (by omega),
            show src + 32 * c + j.val = src + (32 * c + j.val) by omega, enc _ inside,
            getElem!_pos bytes _ inside]
        · rw [if_neg (by omega), if_neg inside]

theorem zeroTable_mono {s : Scratch} {zeros depth depth' : Nat} (table : ZeroTable s zeros depth)
    (le : depth' ≤ depth) : ZeroTable s zeros depth' :=
  fun k within => table k (by omega)

/-- What a plan fragment guarantees: where it writes, and what its root slot holds. -/
structure Rooted (s : Scratch) (free : Nat) (out : Emitted) (node : Bytes) : Prop where
  /-- Every step writes at or above the free offset it started from. -/
  above : WritesAbove out.steps free
  /-- Every step writes below the free offset it hands on. -/
  below : WritesBelow out.steps out.free
  /-- The free offset only grows. -/
  grows : free ≤ out.free
  /-- The root slot lies below the free offset handed on. -/
  rootBelow : out.root + 32 ≤ out.free
  /-- The root slot holds the node. -/
  holds : Holds (runPlan out.steps s) out.root node

/-- Packed bytes: chunked, then folded into a tree just wide enough. -/
theorem packedSteps_spec {zeros src size free depth : Nat} {bytes : Bytes} {s : Scratch}
    (enc : Encodes s src bytes) (sized : bytes.size = size) (low : src + size ≤ free)
    (table : ZeroTable s zeros depth) (deep : depthFor ((size + 31) / 32) ≤ depth)
    (zerosLow : zeros + 32 * (depth + 1) ≤ free) :
    Rooted s free (packedSteps zeros src size free) (packedRoot bytes) := by
  have count : (packBytes bytes).size = (size + 31) / 32 := by simp [bytesPerChunk, sized]
  obtain ⟨chunkAbove, chunkBelow, chunkHeld⟩ := chunkSteps_upto enc sized low ((size + 31) / 32) (Nat.le_refl _)
  rw [← count, List.take_of_length_le (by simp)] at chunkHeld
  rw [count] at chunkHeld
  have tree := treeSteps_spec zeros (depthFor ((size + 31) / 32)) 0 (chunkSlots size free)
    (free + 32 * ((size + 31) / 32)) (packBytes bytes).toList _ chunkHeld
    (fun o mem => by
      simp only [chunkSlots, List.mem_map, List.mem_range] at mem
      obtain ⟨i, below, rfl⟩ := mem
      omega)
    (by rw [Nat.zero_add]
        exact zeroTable_mono (zeroTable_below chunkAbove zerosLow table) deep)
    (by
      have : 32 * (0 + depthFor ((size + 31) / 32) + 1) ≤ 32 * (depth + 1) := by omega
      omega)
  obtain ⟨treeAbove, treeBelow, treeFree, treeRoot, treeHolds⟩ := tree
  refine ⟨?_, ?_, by simp [packedSteps]; omega, treeRoot, ?_⟩
  · intro t mem
    rcases List.mem_append.mp mem with mem | mem
    · exact chunkAbove t mem
    · have := treeAbove t mem
      omega
  · intro t mem
    rcases List.mem_append.mp mem with mem | mem
    · have := chunkBelow t mem
      simp only [packedSteps]
      omega
    · exact treeBelow t mem
  · simp only [packedSteps]
    rw [runPlan_append]
    rw [Nat.zero_add] at treeHolds
    have flat : (foldUpTo combine zeroChunk (depthFor ((size + 31) / 32)) 0 (packBytes bytes).toList).headD
        (zeroAt (depthFor ((size + 31) / 32))) = packedRoot bytes := by
      rw [packedRoot, ← merkleizeFlat_eq_subtreeAt, count]
      rfl
    rw [← flat]
    exact treeHolds

end Ssz.Asm.Root
