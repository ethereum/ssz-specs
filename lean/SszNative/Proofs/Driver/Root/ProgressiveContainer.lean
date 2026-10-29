import SszNative.Proofs.Driver.Root.Container
import SszNative.Proofs.Driver.Root.List
import SszNative.Proofs.Root.Merkle

/-!
The progressive container driver writes the Lean root of a progressive container.

The fields driver writes the field roots, and each layout position takes the next field's root or a zero leaf.
The progressive tree driver folds the leaves, and the layout's node is mixed in, one bit per position.
-/

namespace Ssz.Native.Driver

open Ssz Ssz.Native.Ir Ssz.Native.Ir.Expr Ssz.Native.Ir.Stmt Ssz.Native.Asm

/-! ### The leaves -/

/-- A layout places one leaf per position. -/
theorem placeRoots_length : ∀ (active : List Bool) (roots : List ByteArray),
    (placeRoots active roots).length = active.length
  | [], _ => by simp [placeRoots]
  | false :: a, roots => by simp [placeRoots, placeRoots_length a roots]
  | true :: a, [] => by simp [placeRoots, placeRoots_length a []]
  | true :: a, _ :: rs => by simp [placeRoots, placeRoots_length a rs]

/-- Leaf j of a layout: at a set position the root after those of the set positions before it, else a zero leaf. -/
theorem placeRoots_get : ∀ (active : List Bool) (roots : List ByteArray) (j : Nat) (hj : j < active.length),
    (placeRoots active roots)[j]'(by rw [placeRoots_length]; exact hj) =
      if active[j] then roots.getD ((active.take j).countP id) zeroNode else zeroNode
  | [], _, _, hj => absurd hj (by simp)
  | false :: a, roots, 0, _ => by simp [placeRoots]
  | false :: a, roots, j + 1, hj => by
    simp only [placeRoots, List.getElem_cons_succ, List.take_succ_cons, List.countP_cons]
    rw [placeRoots_get a roots j (by simpa using hj)]
    simp
  | true :: a, [], 0, _ => by simp [placeRoots]
  | true :: a, [], j + 1, hj => by
    simp only [placeRoots, List.getElem_cons_succ]
    rw [placeRoots_get a [] j (by simpa using hj)]
    simp
  | true :: a, r :: rs, 0, _ => by simp [placeRoots]
  | true :: a, r :: rs, j + 1, hj => by
    simp only [placeRoots, List.getElem_cons_succ, List.take_succ_cons, List.countP_cons]
    rw [placeRoots_get a rs j (by simpa using hj)]
    simp

/-- Placed leaves are nodes when the roots are. -/
theorem placeRoots_sized : ∀ (active : List Bool) (roots : List ByteArray), (∀ r ∈ roots, r.size = 32) →
    ∀ r ∈ placeRoots active roots, r.size = 32
  | [], _, _, r, h => by simp [placeRoots] at h
  | false :: a, roots, sized, r, h => by
    simp only [placeRoots, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact placeRoots_sized a roots sized r h
  | true :: a, [], sized, r, h => by
    simp only [placeRoots, List.mem_cons] at h
    rcases h with rfl | h
    · rfl
    · exact placeRoots_sized a [] sized r h
  | true :: a, x :: rs, sized, r, h => by
    simp only [placeRoots, List.mem_cons] at h
    rcases h with rfl | h
    · exact sized _ (by simp)
    · exact placeRoots_sized a rs (fun y hy => sized y (by simp [hy])) r h

/-- The set positions before a set position are fewer than all of them. -/
theorem countP_take_lt (active : List Bool) (j : Nat) (hj : j < active.length) (set : active[j] = true) :
    (active.take j).countP id < active.countP id := by
  have split := congrArg (List.countP id) (List.take_append_drop (j + 1) active)
  rw [List.countP_append, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.countP_append] at split
  simp [set] at split
  omega

/-- The set positions up to the next one: one more when it is set. -/
theorem countP_take_succ (active : List Bool) (j : Nat) (hj : j < active.length) :
    (active.take (j + 1)).countP id = (active.take j).countP id + if active[j] then 1 else 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.countP_append]
  cases active[j] <;> simp

/-! ### The layout's node -/

/-- The byte with bit i set where a condition holds, for i below eight. -/
def orBits (c : Nat → Bool) : UInt8 :=
  (List.range 8).foldl (fun acc bit => if c bit then acc ||| ((1 : UInt8) <<< UInt8.ofNat bit) else acc) 0

/-- A byte from eight bits, as a chain of masks. -/
def orByte (x0 x1 x2 x3 x4 x5 x6 x7 : Bool) : UInt8 :=
  (((((((((0 : UInt8) ||| (if x0 then 1 else 0)) ||| (if x1 then 2 else 0)) ||| (if x2 then 4 else 0)) |||
    (if x3 then 8 else 0)) ||| (if x4 then 16 else 0)) ||| (if x5 then 32 else 0)) ||| (if x6 then 64 else 0)) |||
    (if x7 then 128 else 0))

/-- The byte of a condition is the byte of its eight bits. -/
theorem orBits_eight (c : Nat → Bool) : orBits c = orByte (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (c 6) (c 7) := by
  simp only [orBits, orByte, List.range, List.range.loop, List.foldl]
  cases c 0 <;> cases c 1 <;> cases c 2 <;> cases c 3 <;> cases c 4 <;> cases c 5 <;> cases c 6 <;> cases c 7 <;> rfl

/-- Setting one more bit of a byte masks it in. -/
theorem orByte_set : ∀ x0 x1 x2 x3 x4 x5 x6 x7 a : Bool, ∀ b : Fin 8,
    orByte (x0 || (0 == b.val && a)) (x1 || (1 == b.val && a)) (x2 || (2 == b.val && a)) (x3 || (3 == b.val && a))
      (x4 || (4 == b.val && a)) (x5 || (5 == b.val && a)) (x6 || (6 == b.val && a)) (x7 || (7 == b.val && a)) =
    if a then orByte x0 x1 x2 x3 x4 x5 x6 x7 ||| ((1 : UInt8) <<< UInt8.ofNat b.val)
    else orByte x0 x1 x2 x3 x4 x5 x6 x7 := by
  decide +kernel

/-- A byte read as a word, masked by a power of two below eight, and stored back as a byte. -/
theorem byte_or_pow : ∀ n : Fin 256, ∀ b : Fin 8,
    qwordByte (UInt64.ofNat n.val ||| UInt64.ofNat (2 ^ b.val)) 0 =
      UInt8.ofNat n.val ||| ((1 : UInt8) <<< UInt8.ofNat b.val) := by
  decide +kernel

/-- Bytes of the same bits are equal. -/
theorem orBits_congr {c c' : Nat → Bool} (h : ∀ bit < 8, c bit = c' bit) : orBits c = orBits c' := by
  rw [orBits_eight, orBits_eight, h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega), h 6 (by omega), h 7 (by omega)]

/-- Setting bit b of a byte where a condition holds masks the bit in. -/
theorem orBits_set (c : Nat → Bool) (a : Bool) (b : Nat) (hb : b < 8) :
    orBits (fun bit => c bit || (bit == b && a)) =
      if a then orBits c ||| ((1 : UInt8) <<< UInt8.ofNat b) else orBits c := by
  rw [orBits_eight, orBits_eight]
  exact orByte_set _ _ _ _ _ _ _ _ a ⟨b, hb⟩

/-- Byte q of the layout's node, from the positions before j. -/
def activeByte (active : List Bool) (j q : Nat) : UInt8 :=
  orBits fun bit => decide (8 * q + bit < j) && active.getD (8 * q + bit) false

/-- No position read yet leaves every byte zero. -/
theorem activeByte_zero (active : List Bool) (q : Nat) : activeByte active 0 q = 0 := by
  simp only [activeByte, Nat.not_lt_zero, decide_false, Bool.false_and]
  rfl

/-- A set position is inside the layout. -/
theorem getD_set {active : List Bool} {i : Nat} (h : active.getD i false = true) : i < active.length := by
  rcases Nat.lt_or_ge i active.length with lt | out
  · exact lt
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none out] at h
    cases h

/-- Reading one more position sets its bit in its byte, when the position is set. -/
theorem activeByte_step (active : List Bool) (j q : Nat) :
    activeByte active (j + 1) q = if q = j / 8 then
      (if active.getD j false then activeByte active j q ||| ((1 : UInt8) <<< UInt8.ofNat (j % 8))
        else activeByte active j q)
    else activeByte active j q := by
  by_cases hq : q = j / 8
  · rw [if_pos hq, activeByte, activeByte, ← orBits_set _ _ _ (Nat.mod_lt _ (by decide))]
    refine orBits_congr fun bit hb => ?_
    by_cases e : bit = j % 8
    · subst e
      have at_ : 8 * q + j % 8 = j := by omega
      rw [at_]
      simp
    · have ne : 8 * q + bit ≠ j := by omega
      have same : decide (8 * q + bit < j + 1) = decide (8 * q + bit < j) := by
        by_cases h : 8 * q + bit < j
        · simp [h, show 8 * q + bit < j + 1 by omega]
        · simp [h, show ¬ 8 * q + bit < j + 1 by omega]
      simp [same, e]
  · rw [if_neg hq]
    refine orBits_congr fun bit hb => ?_
    have ne : 8 * q + bit ≠ j := by omega
    have same : decide (8 * q + bit < j + 1) = decide (8 * q + bit < j) := by
      by_cases h : 8 * q + bit < j
      · simp [h, show 8 * q + bit < j + 1 by omega]
      · simp [h, show ¬ 8 * q + bit < j + 1 by omega]
    rw [same]

/-- Past every position, the bytes are the layout's node. -/
theorem activeByte_all (active : List Bool) (j q : Nat) (past : active.length ≤ j) (hq : q < 32) :
    (activeFieldsNode active).data[q]'(by simp [activeFieldsNode]; exact hq) = activeByte active j q := by
  simp only [activeFieldsNode, Array.getElem_map, Array.getElem_range, activeByte, orBits]
  congr 1
  funext acc bit
  by_cases h : active.getD (8 * q + bit) false = true
  · have := getD_set h
    simp only [h, show decide (8 * q + bit < j) = true from decide_eq_true (by omega), Bool.true_and]
  · have hf : active.getD (8 * q + bit) false = false := by simpa using h
    simp only [hf, Bool.and_false]

/-! ### Placing the leaves -/

/-- The progressive container driver's placement: each position takes the next field root, or a zero leaf. -/
abbrev placeLoop : Stmt :=
  while_ (lt RootProgressiveContainer.j RootProgressiveContainer.k) [
    ifElse (ne (ld (RootProgressiveContainer.bits + 8 * RootProgressiveContainer.j)) 0 &&&
        lt RootProgressiveContainer.idx RootProgressiveContainer.n)
      (copy32 (RootProgressiveContainer.l + 32 * RootProgressiveContainer.j)
        (RootProgressiveContainer.r + 32 * RootProgressiveContainer.idx) ++
        [RootProgressiveContainer.idx ::= RootProgressiveContainer.idx + 1])
      (zero32 (RootProgressiveContainer.l + 32 * RootProgressiveContainer.j)),
    RootProgressiveContainer.j ::= RootProgressiveContainer.j + 1]

/-- What the placement needs: the layout's words, the field roots, and the leaves' room after them. -/
structure PlacePre (w : World) (mem : Memory) (active : List Bool) (roots : List ByteArray) (bits l r : Nat) :
    Prop where
  /-- The layout's words are in memory. -/
  plan : WordsAt w mem bits (active.map fun b => if b then 1 else 0)
  /-- The leaves miss them. -/
  planApart : Apart (l, 32 * active.length) (bits, 8 * active.length)
  /-- The field roots are in memory. -/
  rootsAt : ∀ i (h : i < roots.length), nodeAt mem (r + 32 * i) = roots[i].data
  /-- One field root per set position. -/
  count : active.countP id = roots.length
  /-- The leaves are usable. -/
  lAcc : w.access l (32 * active.length) = true
  /-- The roots are usable. -/
  rAcc : w.access r (32 * roots.length) = true
  /-- The roots come before the leaves. -/
  before : r + 32 * roots.length ≤ l

/-- What the placement keeps: the variables before it, the leaves so far, and memory outside the leaves. -/
def PlaceAt (env : Env) (mem : Memory) (active : List Bool) (roots : List ByteArray) (l : Nat) (e : Env)
    (mm : Memory) (j : Nat) : Prop :=
  j ≤ active.length ∧ (∀ x < 11, e x = env x) ∧ e 11 = UInt64.ofNat j ∧
    e 12 = UInt64.ofNat ((active.take j).countP id) ∧
    (∀ i (hi : i < active.length), i < j →
      nodeAt mm (l + 32 * i) = ((placeRoots active roots)[i]'(by rw [placeRoots_length]; exact hi)).data) ∧
    ∀ a, ¬ (l ≤ a ∧ a < l + 32 * active.length) → mm a = mem a

set_option maxHeartbeats 4000000 in
/-- The placement puts each position's leaf at its node. -/
theorem placeLoop_ends {m : Module} {w : World} {sp : Nat} {mem : Memory} {active : List Bool}
    {roots : List ByteArray} {bits l r : Nat} (pp : PlacePre w mem active roots bits l r) {env : Env}
    (k6 : env 6 = UInt64.ofNat active.length) (b7 : env 7 = UInt64.ofNat bits)
    (n8 : env 8 = UInt64.ofNat roots.length) (r9 : env 9 = UInt64.ofNat r) (l10 : env 10 = UInt64.ofNat l)
    (j0 : env 11 = UInt64.ofNat 0) (i0 : env 12 = UInt64.ofNat 0) :
    Ends m w sp env mem placeLoop fun e mm => PlaceAt env mem active roots l e mm active.length := by
  have al := access_bound pp.lAcc
  have ar := access_bound pp.rAcc
  have before := pp.before
  have pa := pp.planApart
  simp only [Apart] at pa
  have kSmall : active.length < 2 ^ 64 := by omega
  have nSmall : roots.length < 2 ^ 64 := by omega
  refine (Ends.loop (fun e mm => ∃ j, PlaceAt env mem active roots l e mm j)
    (fun e _ => active.length - (e 11).toNat)
    ⟨0, Nat.zero_le _, fun _ _ => rfl, j0, by simpa using i0, fun _ _ h => absurd h (Nat.not_lt_zero _),
      fun _ _ => rfl⟩ ?_ ?_).mono ?_
  · rintro e mm ⟨j, hj, same, hj11, -⟩
    exact ⟨_, eval_lt (eval_var hj11) (eval_var ((same 6 (by omega)).trans k6)) (by omega) kSmall⟩
  · rintro e mm v ⟨j, hj, same, hj11, hidx, leaves, frame⟩ hv nz
    have e6 := (same 6 (by omega)).trans k6
    have e7 := (same 7 (by omega)).trans b7
    have e8 := (same 8 (by omega)).trans n8
    have e9 := (same 9 (by omega)).trans r9
    have e10 := (same 10 (by omega)).trans l10
    have c := eval_lt (w := w) (env := e) (mem := mm) (eval_var hj11) (eval_var e6) (by omega) kSmall
    rw [hv] at c
    have hlt : j < active.length := by
      by_cases h : j < active.length
      · exact h
      · rw [if_neg h] at c; cases c; exact absurd rfl nz
    have plan' : WordsAt w mm bits (active.map fun b => if b then 1 else 0) :=
      planAt_congr pp.plan fun a lo hi => frame a (by simp at hi; omega)
    have word := eval_word (w := w) (env := e) (mem := mm) plan' j (by simpa using hlt)
      (e := RootProgressiveContainer.bits + 8 * RootProgressiveContainer.j)
      (eval_add (eval_var e7) (eval_mul (eval_lit 8) (eval_var hj11)))
    simp only [List.getElem_map] at word
    have step := countP_take_succ active j hlt
    have measure : ∀ e' : Env, e' 11 = UInt64.ofNat (j + 1) →
        active.length - (e' 11).toNat < active.length - (e 11).toNat := fun e' h => by
      rw [h, hj11, ofNat_toNat (by omega), ofNat_toNat (by omega)]; omega
    have acc := access_sub (k := 32) pp.lAcc (show l ≤ l + 32 * j by omega) (by omega)
    by_cases set : active[j] = true
    · -- A set position takes the next field root.
      have clt := countP_take_lt active j hlt set
      rw [pp.count] at clt
      have w1 : eval w e mm (ld (RootProgressiveContainer.bits + 8 * RootProgressiveContainer.j)) =
          some (UInt64.ofNat 1) := by rw [word, set]; rfl
      have cnd : eval w e mm (ne (ld (RootProgressiveContainer.bits + 8 * RootProgressiveContainer.j)) 0 &&&
          lt RootProgressiveContainer.idx RootProgressiveContainer.n) = some 1 := by
        rw [eval_and (eval_ne w1 (eval_lit 0)) (eval_lt (eval_var hidx) (eval_var e8) (by omega) nSmall),
          if_neg (by decide), if_pos clt]
        rfl
      have cp := copy32_runs (m := m) (sp := sp) (env := e) (mem := mm)
        (dst := RootProgressiveContainer.l + 32 * RootProgressiveContainer.j)
        (src := RootProgressiveContainer.r + 32 * RootProgressiveContainer.idx)
        (fun _ => eval_add (eval_var e10) (eval_mul (eval_lit 32) (eval_var hj11)))
        (fun _ => eval_add (eval_var e9) (eval_mul (eval_lit 32) (eval_var hidx))) acc
        (access_sub pp.rAcc (by omega) (by omega)) (by simp only [Apart]; omega)
      have s1 := Runs.set' (m := m) (w := w) (sp := sp) (env := e)
        (mem := copied mm (l + 32 * j) (r + 32 * (active.take j).countP id) 32) (x := 12)
        (eval_add (eval_var hidx) (eval_lit 1))
      have s2 := Runs.set' (m := m) (w := w) (sp := sp)
        (env := Asm.assign e 12 (UInt64.ofNat ((active.take j).countP id + 1)))
        (mem := copied mm (l + 32 * j) (r + 32 * (active.take j).countP id) 32) (x := 11)
        (eval_add (eval_var (show Asm.assign e 12 (UInt64.ofNat ((active.take j).countP id + 1)) 11 =
          UInt64.ofNat j by rw [assign_ne (by decide)]; exact hj11)) (eval_lit 1))
      refine ⟨_, _, Runs.block_cons (Runs.ifElse_true 1 cnd (by decide) (Runs.block_append cp
        (Runs.block_cons s1 (Runs.block_nil _ _ _ _ _)))) (Runs.block_cons s2 (Runs.block_nil _ _ _ _ _)),
        ⟨j + 1, by omega, fun x hx => ?_, assign_eq, ?_, fun i hi lt => ?_, fun a o => ?_⟩, measure _ assign_eq⟩
      · rw [assign_ne (by omega), assign_ne (by omega)]; exact same x hx
      · rw [assign_ne (by decide), assign_eq, step, if_pos set]
      · by_cases ij : i = j
        · subst ij
          have copiedAt : nodeAt (copied mm (l + 32 * i) (r + 32 * (active.take i).countP id) 32) (l + 32 * i) =
              nodeAt mm (r + 32 * (active.take i).countP id) := by
            unfold nodeAt; congr 1; funext q; exact copied_in _ _ _ _ _ q.isLt
          rw [copiedAt, nodeAt_congr (m₂ := mem) fun q hq => frame _ (by omega),
            pp.rootsAt _ clt, placeRoots_get active roots i hi, if_pos set, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem clt, Option.getD_some]
        · rw [nodeAt_congr (m₂ := mm) fun q hq => copied_out (by omega)]
          exact leaves i hi (by omega)
      · rw [copied_out (by omega)]; exact frame a o
    · -- A gap takes a zero leaf.
      have set' : active[j] = false := by simpa using set
      have cle : (active.take j).countP id ≤ j := Nat.le_trans List.countP_le_length (List.length_take_le _ _)
      have w0 : eval w e mm (ld (RootProgressiveContainer.bits + 8 * RootProgressiveContainer.j)) =
          some (UInt64.ofNat 0) := by rw [word, set']; rfl
      have cnd : eval w e mm (ne (ld (RootProgressiveContainer.bits + 8 * RootProgressiveContainer.j)) 0 &&&
          lt RootProgressiveContainer.idx RootProgressiveContainer.n) = some 0 := by
        rw [eval_and (eval_ne w0 (eval_lit 0)) (eval_lt (eval_var hidx) (eval_var e8) (by omega) nSmall),
          if_pos rfl, UInt64.zero_and]
      have z := zero32_at (m := m) (sp := sp) (env := e) (mem := mm)
        (dst := RootProgressiveContainer.l + 32 * RootProgressiveContainer.j)
        (fun _ => eval_add (eval_var e10) (eval_mul (eval_lit 32) (eval_var hj11))) acc
      have s2 := Runs.set' (m := m) (w := w) (sp := sp) (env := e) (mem := zeroed mm (l + 32 * j)) (x := 11)
        (eval_add (eval_var hj11) (eval_lit 1))
      refine ⟨_, _, Runs.block_cons (Runs.ifElse_false cnd z) (Runs.block_cons s2 (Runs.block_nil _ _ _ _ _)),
        ⟨j + 1, by omega, fun x hx => ?_, assign_eq, ?_, fun i hi lt => ?_, fun a o => ?_⟩, measure _ assign_eq⟩
      · rw [assign_ne (by omega)]; exact same x hx
      · rw [assign_ne (by decide), hidx, step, if_neg set]; rfl
      · by_cases ij : i = j
        · subst ij
          rw [nodeAt_zeroed, placeRoots_get active roots i hi, if_neg set]
        · rw [nodeAt_congr (m₂ := mm) fun q hq => zeroed_outside (by omega)]
          exact leaves i hi (by omega)
      · rw [zeroed_outside (by omega)]; exact frame a o
  · rintro e mm ⟨⟨j, at_⟩, exit⟩
    obtain ⟨hj, same, hj11, -⟩ := id at_
    rw [eval_lt (eval_var hj11) (eval_var ((same 6 (by omega)).trans k6)) (by omega) kSmall] at exit
    have : j = active.length := by
      by_cases h : j < active.length
      · rw [if_pos h] at exit; cases exit
      · omega
    rw [this] at at_
    exact at_

/-! ### The layout's node, bit by bit -/

/-- The progressive container driver's layout loop: one bit per position, from the lowest. -/
abbrev layoutLoop : Stmt :=
  while_ (lt RootProgressiveContainer.j RootProgressiveContainer.k &&& lt RootProgressiveContainer.j 256) [
    when (ne (ld (RootProgressiveContainer.bits + 8 * RootProgressiveContainer.j)) 0)
      [st1 (RootProgressiveContainer.scratch + 32 + RootProgressiveContainer.j / 8)
        (ld1 (RootProgressiveContainer.scratch + 32 + RootProgressiveContainer.j / 8) ||| RootProgressiveContainer.pw)],
    RootProgressiveContainer.j ::= RootProgressiveContainer.j + 1,
    ifElse (eq (RootProgressiveContainer.j % 8) 0) [RootProgressiveContainer.pw ::= 1]
      [RootProgressiveContainer.pw ::= RootProgressiveContainer.pw + RootProgressiveContainer.pw]]

/-- What the layout loop keeps: the variables before it, the bit's power, the bytes so far, and memory elsewhere. -/
def LayoutAt (env : Env) (mem : Memory) (active : List Bool) (a : Nat) (e : Env) (mm : Memory) (j : Nat) : Prop :=
  j ≤ active.length ∧ (∀ x < 11, e x = env x) ∧ e 11 = UInt64.ofNat j ∧ e 13 = UInt64.ofNat (2 ^ (j % 8)) ∧
    (∀ q < 32, mm (a + q) = activeByte active j q) ∧ ∀ x, ¬ (a ≤ x ∧ x < a + 32) → mm x = mem x

set_option maxHeartbeats 4000000 in
/-- The layout loop writes the layout's node after the scratch's first node. -/
theorem layoutLoop_ends {m : Module} {w : World} {sp : Nat} {mem : Memory} {active : List Bool} {bits scratch : Nat}
    (plan : WordsAt w mem bits (active.map fun b => if b then 1 else 0))
    (apart : Apart (scratch + 32, 32) (bits, 8 * active.length)) (aAcc : w.access (scratch + 32) 32 = true)
    (few : active.length ≤ 256) {env : Env} (s4 : env 4 = UInt64.ofNat scratch)
    (k6 : env 6 = UInt64.ofNat active.length) (b7 : env 7 = UInt64.ofNat bits)
    (at0 : LayoutAt env mem active (scratch + 32) env mem 0) :
    Ends m w sp env mem layoutLoop fun e mm => LayoutAt env mem active (scratch + 32) e mm active.length := by
  have aa := access_bound aAcc
  have pa := apart
  simp only [Apart] at pa
  refine (Ends.loop (fun e mm => ∃ j, LayoutAt env mem active (scratch + 32) e mm j)
    (fun e _ => active.length - (e 11).toNat) ⟨0, at0⟩ ?_ ?_).mono ?_
  · rintro e mm ⟨j, hj, same, hj11, -⟩
    exact ⟨_, eval_and (eval_lt (eval_var hj11) (eval_var ((same 6 (by omega)).trans k6)) (by omega) (by omega))
      (eval_lt (eval_var hj11) (eval_lit 256) (by omega) (by omega))⟩
  · rintro e mm v ⟨j, hj, same, hj11, hpw, bytes, frame⟩ hv nz
    have e4 := (same 4 (by omega)).trans s4
    have e6 := (same 6 (by omega)).trans k6
    have e7 := (same 7 (by omega)).trans b7
    have c := eval_and (w := w) (env := e) (mem := mm)
      (eval_lt (eval_var hj11) (eval_var e6) (by omega) (by omega))
      (eval_lt (a := RootProgressiveContainer.j) (b := 256) (eval_var hj11) (eval_lit 256) (by omega) (by omega))
    rw [hv] at c
    have hlt : j < active.length := by
      by_cases h : j < active.length
      · exact h
      · rw [if_neg h, UInt64.zero_and] at c; cases c; exact absurd rfl nz
    have plan' : WordsAt w mm bits (active.map fun b => if b then 1 else 0) :=
      planAt_congr plan fun x lo hi => frame x (by simp at hi; omega)
    have word := eval_word (w := w) (env := e) (mem := mm) plan' j (by simpa using hlt)
      (e := RootProgressiveContainer.bits + 8 * RootProgressiveContainer.j)
      (eval_add (eval_var e7) (eval_mul (eval_lit 8) (eval_var hj11)))
    simp only [List.getElem_map] at word
    have getJ : active.getD j false = active[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    -- The position's bit, when it is set.
    obtain ⟨M, run1, bytes1, frame1⟩ : ∃ M, Runs m w sp e mm
        (when (ne (ld (RootProgressiveContainer.bits + 8 * RootProgressiveContainer.j)) 0)
          [st1 (RootProgressiveContainer.scratch + 32 + RootProgressiveContainer.j / 8)
            (ld1 (RootProgressiveContainer.scratch + 32 + RootProgressiveContainer.j / 8) |||
              RootProgressiveContainer.pw)]) e M ∧
        (∀ q < 32, M (scratch + 32 + q) = activeByte active (j + 1) q) ∧
        ∀ x, ¬ (scratch + 32 ≤ x ∧ x < scratch + 32 + 32) → M x = mem x := by
      by_cases set : active[j] = true
      · have w1 : eval w e mm (ld (RootProgressiveContainer.bits + 8 * RootProgressiveContainer.j)) =
            some (UInt64.ofNat 1) := by rw [word, set]; rfl
        have cnd := eval_ne (w := w) (env := e) (mem := mm) w1 (eval_lit 0)
        rw [if_neg (by decide)] at cnd
        have addr : ∀ mm', eval w e mm' (RootProgressiveContainer.scratch + 32 + RootProgressiveContainer.j / 8) =
            some (UInt64.ofNat (scratch + 32 + j / 8)) := fun mm' =>
          eval_add (eval_add (eval_var e4) (eval_lit 32))
            (eval_div (eval_var hj11) (eval_lit 8) (by omega) (by decide) (by decide))
        have acc1 : w.access (scratch + 32 + j / 8) 1 = true := access_sub aAcc (by omega) (by omega)
        have ld := eval_ld1_of (addr mm) acc1
        rw [readLE_byte] at ld
        have val := eval_or ld (eval_var hpw)
        have st := Runs.store m w sp e mm .b1 _ _ _ _ (addr mm) val
          (by rw [ofNat_toNat (by omega)]; exact acc1)
        rw [ofNat_toNat (by omega), show Width.bytes .b1 = 1 from rfl] at st
        refine ⟨_, Runs.when_true 1 cnd (by decide) (Runs.block_cons st (Runs.block_nil _ _ _ _ _)),
          fun q hq => ?_, fun x o => ?_⟩
        · rw [store_one, activeByte_step, getJ, if_pos set]
          by_cases hq' : q = j / 8
          · subst hq'
            rw [if_pos rfl, if_pos rfl, byte_or_pow ⟨_, (mm (scratch + 32 + j / 8)).toNat_lt⟩ ⟨j % 8, Nat.mod_lt _
              (by decide)⟩, UInt8.ofNat_toNat, bytes _ hq]
          · rw [if_neg (by omega), if_neg hq', bytes q hq]
        · rw [store_one, if_neg (by omega)]; exact frame x o
      · have set' : active[j] = false := by simpa using set
        have w0 : eval w e mm (ld (RootProgressiveContainer.bits + 8 * RootProgressiveContainer.j)) =
            some (UInt64.ofNat 0) := by rw [word, set']; rfl
        have cnd := eval_ne (w := w) (env := e) (mem := mm) w0 (eval_lit 0)
        rw [if_pos rfl] at cnd
        refine ⟨mm, Runs.when_false cnd, fun q hq => ?_, frame⟩
        rw [activeByte_step, getJ, set', bytes q hq]
        split <;> simp
    -- The next position, and its bit's power.
    have s2 := Runs.set' (m := m) (w := w) (sp := sp) (env := e) (mem := M) (x := 11)
      (eval_add (eval_var hj11) (eval_lit 1))
    have j2 : Asm.assign e 11 (UInt64.ofNat (j + 1)) 11 = UInt64.ofNat (j + 1) := assign_eq
    have pw2 : Asm.assign e 11 (UInt64.ofNat (j + 1)) 13 = UInt64.ofNat (2 ^ (j % 8)) := by
      rw [assign_ne (by decide)]; exact hpw
    have m8 := eval_eq (w := w) (env := Asm.assign e 11 (UInt64.ofNat (j + 1))) (mem := M) (b := 0)
      (eval_mod (a := RootProgressiveContainer.j) (b := 8) (eval_var j2) (eval_lit 8) (by omega) (by decide)
        (by decide)) (eval_lit 0) (by omega) (by decide)
    have pwSmall : 2 ^ (j % 8) < 256 := by
      have : j % 8 < 8 := Nat.mod_lt _ (by decide)
      exact Nat.lt_of_lt_of_le (Nat.pow_lt_pow_right (by decide) this) (by decide)
    obtain ⟨E3, run3, same3, j3, pw3⟩ : ∃ E3, Runs m w sp (Asm.assign e 11 (UInt64.ofNat (j + 1))) M
        (ifElse (eq (RootProgressiveContainer.j % 8) 0) [RootProgressiveContainer.pw ::= 1]
          [RootProgressiveContainer.pw ::= RootProgressiveContainer.pw + RootProgressiveContainer.pw]) E3 M ∧
        (∀ x < 11, E3 x = env x) ∧ E3 11 = UInt64.ofNat (j + 1) ∧ E3 13 = UInt64.ofNat (2 ^ ((j + 1) % 8)) := by
      by_cases wrap : (j + 1) % 8 = 0
      · rw [if_pos wrap] at m8
        refine ⟨_, Runs.ifElse_true 1 m8 (by decide) (Runs.block_cons (Runs.set' (eval_lit 1))
          (Runs.block_nil _ _ _ _ _)), fun x hx => ?_, by rw [assign_ne (by decide)] <;> exact j2, ?_⟩
        · rw [assign_ne (Nat.ne_of_lt (show x < 13 by omega)), assign_ne (by omega)]; exact same x hx
        · rw [assign_eq, wrap]
      · rw [if_neg wrap] at m8
        refine ⟨_, Runs.ifElse_false m8 (Runs.block_cons (Runs.set' (eval_add (eval_var pw2) (eval_var pw2)))
          (Runs.block_nil _ _ _ _ _)), fun x hx => ?_, by rw [assign_ne (by decide)] <;> exact j2, ?_⟩
        · rw [assign_ne (Nat.ne_of_lt (show x < 13 by omega)), assign_ne (by omega)]; exact same x hx
        · rw [assign_eq, show (j + 1) % 8 = j % 8 + 1 by omega, Nat.pow_succ]
          congr 1
          omega
    refine ⟨E3, M, Runs.block_cons run1 (Runs.block_cons s2 (Runs.block_cons run3 (Runs.block_nil _ _ _ _ _))),
      ⟨j + 1, by omega, same3, j3, pw3, bytes1, frame1⟩, ?_⟩
    show active.length - (E3 11).toNat < active.length - (e 11).toNat
    rw [j3, hj11, ofNat_toNat (by omega), ofNat_toNat (by omega)]
    omega
  · rintro e mm ⟨⟨j, at_⟩, exit⟩
    obtain ⟨hj, same, hj11, -⟩ := id at_
    rw [eval_and (eval_lt (eval_var hj11) (eval_var ((same 6 (by omega)).trans k6)) (by omega) (by omega))
      (eval_lt (a := RootProgressiveContainer.j) (b := 256) (eval_var hj11) (eval_lit 256) (by omega) (by omega))]
      at exit
    have : j = active.length := by
      by_cases h : j < active.length
      · rw [if_pos h, if_pos (by omega)] at exit; cases exit
      · omega
    rw [this] at at_
    exact at_

/-! ### The progressive container driver -/

/-- The progressive container driver's frame holds twenty-one words. -/
theorem progressiveContainerFrame : RootProgressiveContainer.fn.frame = 21 := by decide

/-- A progressive container's scratch below the cap: two nodes, then the fields' or the leaves' and the tree's. -/
theorem varNeed_progressiveContainer {active : List Bool} {names : List String} {fields : List Desc} {size : Nat}
    (below : varNeed (.progressiveContainer active names fields) size < scratchCap) :
    varNeed (.progressiveContainer active names fields) size = 64 + max (56 * fields.length + fieldsVarNeed fields size 0)
      (32 * fields.length + 32 * active.length + (2560 + 2048 + 32 * active.length)) := by
  simp only [varNeed, treeNeed, RootProgressive.spineBytes, zeroHeights, sadd, smul, sat] at below ⊢
  have := cap_eq
  omega

/-- A progressive container's stack is a level more than its deepest field's. -/
theorem rootStack_progressiveContainer (active : List Bool) (names : List String) (fields : List Desc) :
    rootStack (.progressiveContainer active names fields) = 12288 + 1024 * Desc.deepestNesting fields + 1024 := by
  simp only [rootStack, Desc.nesting]; omega

/-- A field finds its stack below the progressive container's frame and the fields driver's. -/
theorem progressiveContainer_room {lo sp n D : Nat} (hn : n ≤ D) (h : lo + (12288 + 1024 * D + 1024) + 0 ≤ sp) :
    lo + 176 + (12288 + 1024 * n) + 256 ≤ sp - 176 ∧ lo + 176 ≤ sp - 176 ∧ lo + 8 + 8 * 21 ≤ sp ∧
      lo + 8 + 8 * 19 + 10552 ≤ sp - 176 ∧ lo + 10392 ≤ sp - 176 := by
  omega

/-- The progressive container driver's variables that stay: the arguments, the layout, the count, and the buffers. -/
structure PCEnv (env : Env) (p src size out scratch ctx k bits n : Nat) : Prop where
  /-- The arguments. -/
  range : RangeEnv env p src size out scratch ctx
  /-- The layout's length. -/
  kV : env 6 = UInt64.ofNat k
  /-- The layout's first word. -/
  bitsV : env 7 = UInt64.ofNat bits
  /-- The field count. -/
  nV : env 8 = UInt64.ofNat n
  /-- The field roots. -/
  rV : env 9 = UInt64.ofNat (scratch + 64)
  /-- The leaves. -/
  lV : env 10 = UInt64.ofNat (scratch + 64 + 32 * n)

/-- Writing a working variable keeps the variables that stay. -/
theorem PCEnv.write {env : Env} {p src size out scratch ctx k bits n : Nat}
    (h : PCEnv env p src size out scratch ctx k bits n) {x : Nat} (v : UInt64) (hx : 11 ≤ x) :
    PCEnv (Asm.assign env x v) p src size out scratch ctx k bits n :=
  ⟨h.range.write v (by omega), by rw [assign_ne (by omega), h.kV], by rw [assign_ne (by omega), h.bitsV],
    by rw [assign_ne (by omega), h.nV], by rw [assign_ne (by omega), h.rV], by rw [assign_ne (by omega), h.lV]⟩

/-- Variables that agree below eleven keep what stays. -/
theorem PCEnv.congr {env e : Env} {p src size out scratch ctx k bits n : Nat}
    (h : PCEnv env p src size out scratch ctx k bits n) (same : ∀ x < 11, e x = env x) :
    PCEnv e p src size out scratch ctx k bits n :=
  ⟨⟨by rw [same 0 (by omega), h.range.p], by rw [same 1 (by omega), h.range.src],
    by rw [same 2 (by omega), h.range.size], by rw [same 3 (by omega), h.range.out],
    by rw [same 4 (by omega), h.range.scratch], by rw [same 5 (by omega), h.range.ctx]⟩,
    by rw [same 6 (by omega), h.kV], by rw [same 7 (by omega), h.bitsV], by rw [same 8 (by omega), h.nV],
    by rw [same 9 (by omega), h.rV], by rw [same 10 (by omega), h.lV]⟩

/-- The progressive container driver's body, in its parts. -/
theorem rootProgressiveContainer_body_eq : RootProgressiveContainer.fn.body = .block ([
    RootProgressiveContainer.k ::= ld (RootProgressiveContainer.p + 8),
    RootProgressiveContainer.bits ::= RootProgressiveContainer.p + 16,
    RootProgressiveContainer.n ::= ld (RootProgressiveContainer.bits + 8 * RootProgressiveContainer.k),
    RootProgressiveContainer.r ::= RootProgressiveContainer.scratch + 64,
    callInto RootProgressiveContainer.sink "ssz_root_fields"
      [RootProgressiveContainer.bits + 8 * RootProgressiveContainer.k + 8, RootProgressiveContainer.n,
        RootProgressiveContainer.src, RootProgressiveContainer.size, RootProgressiveContainer.r,
        RootProgressiveContainer.ctx],
    RootProgressiveContainer.l ::= RootProgressiveContainer.r + 32 * RootProgressiveContainer.n,
    RootProgressiveContainer.j ::= 0, RootProgressiveContainer.idx ::= 0, placeLoop,
    callInto RootProgressiveContainer.sink "ssz_root_progressive"
      [RootProgressiveContainer.l, RootProgressiveContainer.k, RootProgressiveContainer.scratch,
        RootProgressiveContainer.l + 32 * RootProgressiveContainer.k, RootProgressiveContainer.ctx]] ++
    (zero32 (RootProgressiveContainer.scratch + 32) ++
    [RootProgressiveContainer.j ::= 0, RootProgressiveContainer.pw ::= 1, layoutLoop,
      callInto RootProgressiveContainer.sink "ssz_hash_pairs"
        [RootProgressiveContainer.out, RootProgressiveContainer.scratch, RootProgressiveContainer.scratch + 32, 1,
          RootProgressiveContainer.ctx]])) := rfl

set_option maxHeartbeats 16000000 in
/-- The progressive container driver writes the Lean root of a progressive container. -/
theorem rootProgressiveContainer_ok {m : Module} {w : World} (hash : HashingOk m w) (fns : RangeFns m)
    {active : List Bool} {names : List String} {fields : List Desc} (ih : ∀ f ∈ fields, RootOfOk m w f) :
    RangeOk m w "ssz_root_progressive_container" (.progressiveContainer active names fields) := by
  intro sp mem p base start stop out scratch ctx table zeros pad mask b room pre
  have usize := pre.usize
  have small := pre.small
  unfold RootProof.Small at small
  rw [usize] at small
  have ordered := pre.ordered
  have inside := pre.inside
  have bound : addressBound = 2 ^ 63 := rfl
  have soundF : ∀ f ∈ fields, f.wellFormed = .ok () :=
    Validate.allWellFormed_mem fields (wellFormed_progressiveContainer pre.sound)
  have thinAll : narrowAll fields = true := by
    have := pre.thin; simp only [narrow, Bool.and_eq_true] at this; exact this.2
  obtain ⟨-, few⟩ := wellFormed_progressiveContainer_layout pre.sound
  have few' : active.length ≤ 256 := few
  have counted := progressive_count pre.sound
  -- What decoding gives: the fields' ranges, inside the struct, each decoding.
  obtain ⟨v, read⟩ := pre.accepted
  simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
  split at read
  · cases read
  rename_i values read'
  obtain ⟨cut, lead, ranges⟩ := struct_decoded ordered inside read'
  obtain ⟨rlen, sized, each⟩ := fieldRoots_nodes soundF inside pre.small ranges
  generalize hroots : fieldRoots fields b (rangesOf start (stop - start) (placesFrom fields b start 0)) = roots
    at rlen sized each
  -- The scratch: two nodes, then the fields' region, or the leaves and the progressive tree's scratch.
  obtain ⟨F, hF⟩ : ∃ F, fieldsVarNeed fields (stop - start) 0 = F := ⟨_, rfl⟩
  have need := varNeed_progressiveContainer pre.below
  rw [hF] at need
  have sAcc := pre.sAcc
  have sB := pre.sB
  have sPad := pre.sPad
  have sCtx := pre.sCtx
  have sTable := pre.sTable
  have sZeros := pre.sZeros
  have sOut := pre.sOut
  have sPlan := pre.sPlan
  have sSlack := pre.sSlack
  have below := pre.below
  rw [need] at sAcc sB sPad sCtx sTable sZeros sOut sPlan sSlack below
  have as := access_bound sAcc
  generalize hk : active.length = k at few' sAcc sB sPad sCtx sTable sZeros sOut sPlan sSlack below as
  generalize hn : fields.length = n at sAcc sB sPad sCtx sTable sZeros sOut sPlan sSlack below as
  -- The plan: the tag, the layout's length and words, the field count, then the fields' plans.
  have words : Plan.words (.progressiveContainer active names fields) =
      ([11, active.length] ++ active.map (fun b => if b then 1 else 0)) ++ ([fields.length] ++ Plan.wordsAll fields) := by
    rw [Plan.words]; simp
  have planAll := pre.plan
  rw [words] at planAll
  obtain ⟨planHead, planTail⟩ := wordsAt_split planAll
  obtain ⟨-, planA⟩ := wordsAt_split planHead
  obtain ⟨planN, planF⟩ := wordsAt_split planTail
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map, hk] at planA planN planF planTail
  have planLen : 8 * (Plan.words (.progressiveContainer active names fields)).length =
      16 + 8 * k + 8 + 8 * (Plan.wordsAll fields).length := by
    rw [words]; simp [hk]; omega
  rw [planLen] at sPlan
  have planPad := pre.planPad
  rw [planLen] at planPad
  have fitsAll := pre.fits
  rw [words] at fitsAll
  have fitsF : Fits (Plan.wordsAll fields) := (fits_split (fits_split fitsAll).2).2
  rw [show p + 8 * (0 + 1 + 1) = p + 16 by omega] at planA
  rw [show p + 8 * (0 + 1 + 1 + k) + 8 * (0 + 1) = p + 16 + 8 * k + 8 by omega] at planF
  rw [show p + 8 * (0 + 1 + 1 + k) = p + 16 + 8 * k by omega] at planTail
  -- Memory changed only in the scratch and the padding area keeps the plan's parts.
  let V := 64 + max (56 * n + F) (32 * n + 32 * k + (2560 + 2048 + 32 * k))
  have sP := sPlan
  have pP := planPad
  simp only [Apart] at sP pP
  have planOf : ∀ mm : Memory, (∀ a, ¬ (scratch ≤ a ∧ a < scratch + V) → ¬ (pad ≤ a ∧ a < pad + 1536) →
      mm a = mem a) → WordsAt w mm (p + 16) (active.map fun b => if b then 1 else 0) := fun mm fr =>
    planAt_congr planA fun a lo hi => fr a (by simp [hk] at hi; omega) (by simp [hk] at hi; omega)
  -- The stack.
  rw [rootStack_progressiveContainer] at room
  let sp' := sp - 8 - 8 * RootProgressiveContainer.fn.frame
  have spEq : sp' = sp - 176 := by simp only [sp', progressiveContainerFrame]; omega
  have roomF : w.stackLo + 176 ≤ sp' := by
    rw [spEq]; exact (progressiveContainer_room (Nat.le_refl _) room).2.1
  have room' : ∀ f ∈ fields, w.stackLo + 176 + rootStack f + 256 ≤ sp' := fun f mf => by
    rw [spEq]; exact (progressiveContainer_room (nesting_le_deepest fields f mf) room).1
  have progRoom : w.stackLo + 8 + 8 * 19 + treeStack ≤ sp' := by
    rw [spEq]; exact (progressiveContainer_room (Nat.le_refl _) room).2.2.2.1
  have hashRoom : w.stackLo + hashStack ≤ sp' := by
    rw [spEq]; exact (progressiveContainer_room (Nat.le_refl _) room).2.2.2.2
  have frameRoom : w.stackLo + 8 + 8 * RootProgressiveContainer.fn.frame ≤ sp := by
    rw [progressiveContainerFrame]; exact (progressiveContainer_room (Nat.le_refl _) room).2.2.1
  clear room
  -- The layout's length, its first word, the field count, and the field roots' place.
  let E0 := entryEnv [UInt64.ofNat p, UInt64.ofNat (base + start), UInt64.ofNat (stop - start), UInt64.ofNat out,
    UInt64.ofNat scratch, UInt64.ofNat ctx]
  have ev0 := rangeEnv_entry p (base + start) (stop - start) out scratch ctx
  have kw : eval w E0 mem (ld (RootProgressiveContainer.p + 8)) = some (UInt64.ofNat k) := by
    have := eval_word planHead 1 (by simp) (e := RootProgressiveContainer.p + 8) (eval_add (eval_var ev0.p) (eval_lit 8))
    rw [this]; simp [hk]
  have s1 := Runs.set' (m := m) (w := w) (sp := sp') (x := 6) kw
  have s2 := Runs.set' (m := m) (w := w) (sp := sp') (env := Asm.assign E0 6 (UInt64.ofNat k)) (mem := mem) (x := 7)
    (eval_add (eval_var ((ev0.write (UInt64.ofNat k) (by decide)).p)) (eval_lit 16))
  let E2 := Asm.assign (Asm.assign E0 6 (UInt64.ofNat k)) 7 (UInt64.ofNat (p + 16))
  have nw : eval w E2 mem (ld (RootProgressiveContainer.bits + 8 * RootProgressiveContainer.k)) =
      some (UInt64.ofNat n) := by
    have := eval_word planTail 0 (by simp) (e := RootProgressiveContainer.bits + 8 * RootProgressiveContainer.k)
      (by
        rw [Nat.mul_zero, Nat.add_zero]
        exact eval_add (eval_var (show E2 7 = UInt64.ofNat (p + 16) from assign_eq)) (eval_mul (eval_lit 8)
          (eval_var (show E2 6 = UInt64.ofNat k by simp only [E2]; rw [assign_ne (by decide), assign_eq]))))
    rw [this]; simp [hn]
  have s3 := Runs.set' (m := m) (w := w) (sp := sp') (x := 8) nw
  have s4 := Runs.set' (m := m) (w := w) (sp := sp') (env := Asm.assign E2 8 (UInt64.ofNat n)) (mem := mem) (x := 9)
    (eval_add (eval_var (((ev0.write (UInt64.ofNat k) (by decide)).write (UInt64.ofNat (p + 16)) (by decide)).write
      (UInt64.ofNat n) (by decide)).scratch) (eval_lit 64))
  let E4 := Asm.assign (Asm.assign E2 8 (UInt64.ofNat n)) 9 (UInt64.ofNat (scratch + 64))
  have ev4 : RangeEnv E4 p (base + start) (stop - start) out scratch ctx :=
    (((ev0.write _ (by decide)).write _ (by decide)).write _ (by decide)).write _ (by decide)
  -- The field roots, after two nodes of the scratch.
  have fpre : FieldsPre w mem fields (p + 16 + 8 * k + 8) base start stop (scratch + 64) (56 * n + F) ctx table zeros
      pad mask b :=
    { ready := pre.ready, plan := planF, fits := fitsF, holds := pre.holds, bAcc := pre.bAcc, ordered := ordered,
      inside := inside, small := pre.small, spread := pre.spread, sound := soundF,
      thin := narrowAll_mem fields thinAll, lead := lead, ranges := ranges,
      room := by rw [hF, hn]; exact Nat.le_refl _, below := by rw [hF]; omega,
      rAcc := access_sub sAcc (by omega) (by omega), rSlack := by omega,
      rB := apart_sub sB (by omega) (by omega), rPad := apart_sub sPad (by omega) (by omega),
      rCtx := apart_sub sCtx (by omega) (by omega), rTable := apart_sub sTable (by omega) (by omega),
      rZeros := apart_sub sZeros (by omega) (by omega),
      rPlan := apart_sub' (apart_sub sPlan (by omega) (by omega)) (by omega) (by omega), bPad := pre.bPad,
      planPad := apart_comm (apart_sub' (apart_comm planPad) (by omega) (by omega)), usize := usize }
  obtain ⟨mem1, call1, roots1, ready1, keep1⟩ := rootFields_calls fns ih roomF room' fpre
  rw [hn] at call1
  have r5 := Runs.call (m := m) (sp := sp') (env := E4) (mem := mem) (dst := 14)
    (args := [RootProgressiveContainer.bits + 8 * RootProgressiveContainer.k + 8, RootProgressiveContainer.n,
      RootProgressiveContainer.src, RootProgressiveContainer.size, RootProgressiveContainer.r,
      RootProgressiveContainer.ctx])
    (by
      have b4 : E4 7 = UInt64.ofNat (p + 16) := by simp only [E4, E2]; rw [assign_ne (by decide), assign_ne (by decide),
        assign_eq]
      have k4 : E4 6 = UInt64.ofNat k := by simp only [E4, E2]; rw [assign_ne (by decide), assign_ne (by decide),
        assign_ne (by decide), assign_eq]
      have n4 : E4 8 = UInt64.ofNat n := by simp only [E4]; rw [assign_ne (by decide), assign_eq]
      have r4 : E4 9 = UInt64.ofNat (scratch + 64) := assign_eq
      simp only [List.mapM_cons, List.mapM_nil, eval_add (eval_add (eval_var b4) (eval_mul (eval_lit 8) (eval_var k4)))
        (eval_lit 8), eval_var n4, eval_var ev4.src, eval_var ev4.size, eval_var r4, eval_var ev4.ctx]
      rfl) call1
  have frame1 : ∀ a, ¬ (scratch ≤ a ∧ a < scratch + V) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem1 a = mem a :=
    fun a o pd => keep1 a (fun h => o ⟨by omega, by omega⟩) pd
  -- The leaves, after the field roots.
  let E5 := Asm.assign E4 14 0
  have s5 := Runs.set' (m := m) (w := w) (sp := sp') (env := E5) (mem := mem1) (x := 10)
    (eval_add (eval_var (show E5 9 = UInt64.ofNat (scratch + 64) from rfl))
      (eval_mul (eval_lit 32) (eval_var (show E5 8 = UInt64.ofNat n from rfl))))
  let E6 := Asm.assign E5 10 (UInt64.ofNat (scratch + 64 + 32 * n))
  have s6 := Runs.set' (m := m) (w := w) (sp := sp') (env := E6) (mem := mem1) (x := 11) (eval_lit 0)
  have s7 := Runs.set' (m := m) (w := w) (sp := sp') (env := Asm.assign E6 11 (UInt64.ofNat 0)) (mem := mem1)
    (x := 12) (eval_lit 0)
  let E8 := Asm.assign (Asm.assign E6 11 (UInt64.ofNat 0)) 12 (UInt64.ofNat 0)
  have pc8 : PCEnv E8 p (base + start) (stop - start) out scratch ctx k (p + 16) n :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl⟩
  have pp : PlacePre w mem1 active roots (p + 16) (scratch + 64 + 32 * n) (scratch + 64) :=
    { plan := planOf mem1 frame1,
      planApart := by rw [hk]; exact apart_sub' (apart_sub sPlan (by omega) (by omega)) (by omega) (by omega),
      rootsAt := fun i hi => by rw [each i (by omega) hi]; exact roots1 i (by omega),
      count := counted.trans rlen.symm,
      lAcc := by rw [hk]; exact access_sub sAcc (by omega) (by omega),
      rAcc := by rw [rlen, hn]; exact access_sub sAcc (by omega) (by omega),
      before := by rw [rlen, hn]; exact Nat.le_refl _ }
  obtain ⟨E9, mem2, run9, -, same9, -, -, leaves9, frame9⟩ := placeLoop_ends (m := m) (sp := sp') pp
    (env := E8) (by rw [hk]; exact pc8.kV) pc8.bitsV (by rw [rlen, hn]; exact pc8.nV) pc8.rV pc8.lV rfl rfl
  have pc9 := pc8.congr same9
  have frame2 : ∀ a, ¬ (scratch ≤ a ∧ a < scratch + V) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem2 a = mem a :=
    fun a o pd => by rw [frame9 a (fun h => o ⟨by omega, by omega⟩)]; exact frame1 a o pd
  -- The progressive tree over the leaves, into the scratch's first node.
  have pspan : progressiveSpan k = 4608 + 32 * k := rfl
  have ppre : ProgPre w mem2 (scratch + 64 + 32 * n) k scratch (scratch + 64 + 32 * n + 32 * k) ctx table zeros pad
      mask (bytesAt mem2 (scratch + 64 + 32 * n) (32 * k)) :=
    { ready := pre.ready.within (o := scratch) (n := V) sCtx sTable sZeros frame2,
      held := holds_bytesAt _ _ _, inside := by simp [bytesAt, ByteArray.size],
      small := by simp only [bytesAt, ByteArray.size, Array.size_ofFn]; rw [usize]; omega,
      few := by omega, nAcc := access_sub sAcc (by omega) (by omega), nReach := by omega,
      oAcc := access_sub sAcc (by omega) (by omega), sAcc := access_sub sAcc (by omega) (by omega),
      sN := by simp only [Apart, bytesAt, ByteArray.size, Array.size_ofFn]; omega,
      sO := by simp only [Apart]; omega,
      sPad := apart_sub sPad (by omega) (by omega), sCtx := apart_sub sCtx (by omega) (by omega),
      sTable := apart_sub sTable (by omega) (by omega), sZeros := apart_sub sZeros (by omega) (by omega),
      oPad := apart_sub sPad (by omega) (by omega), oCtx := apart_sub sCtx (by omega) (by omega),
      oTable := apart_sub sTable (by omega) (by omega), oZeros := apart_sub sZeros (by omega) (by omega),
      nPad := by
        have := apart_sub (o₂ := scratch + 64 + 32 * n) (n₂ := 32 * k) sPad (by omega) (by omega)
        simpa [bytesAt, ByteArray.size] using this }
  obtain ⟨mem3, call3, root3, -, keep3⟩ := rootProgressive_calls hash fns.progressive (sp := sp') progRoom ppre
  have r10 := Runs.call (m := m) (sp := sp') (env := E9) (mem := mem2) (dst := 14)
    (args := [RootProgressiveContainer.l, RootProgressiveContainer.k, RootProgressiveContainer.scratch,
      RootProgressiveContainer.l + 32 * RootProgressiveContainer.k, RootProgressiveContainer.ctx])
    (by
      simp only [List.mapM_cons, List.mapM_nil, eval_var pc9.lV, eval_var pc9.kV, eval_var pc9.range.scratch,
        eval_add (eval_var pc9.lV) (eval_mul (eval_lit 32) (eval_var pc9.kV)), eval_var pc9.range.ctx]
      rfl) call3
  have pc10 := pc9.write (x := 14) 0 (by decide)
  have frame3 : ∀ a, ¬ (scratch ≤ a ∧ a < scratch + V) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem3 a = mem a :=
    fun a o pd => by
      rw [keep3 a (fun h => o ⟨by omega, by omega⟩) (fun h => o ⟨by omega, by omega⟩) pd]; exact frame2 a o pd
  -- The layout's node, after the tree's root.
  have z := zero32_at (m := m) (sp := sp') (env := Asm.assign E9 14 0) (mem := mem3)
    (dst := RootProgressiveContainer.scratch + 32) (fun _ => eval_add (eval_var pc10.range.scratch) (eval_lit 32))
    (access_sub sAcc (by omega) (by omega))
  have frame4 : ∀ a, ¬ (scratch ≤ a ∧ a < scratch + V) → ¬ (pad ≤ a ∧ a < pad + 1536) →
      zeroed mem3 (scratch + 32) a = mem a :=
    fun a o pd => by rw [zeroed_outside (by omega)]; exact frame3 a o pd
  have s8 := Runs.set' (m := m) (w := w) (sp := sp') (env := Asm.assign E9 14 0) (mem := zeroed mem3 (scratch + 32))
    (x := 11) (eval_lit 0)
  have s9 := Runs.set' (m := m) (w := w) (sp := sp') (env := Asm.assign (Asm.assign E9 14 0) 11 (UInt64.ofNat 0))
    (mem := zeroed mem3 (scratch + 32)) (x := 13) (eval_lit 1)
  let E12 := Asm.assign (Asm.assign (Asm.assign E9 14 0) 11 (UInt64.ofNat 0)) 13 (UInt64.ofNat 1)
  have pc12 : PCEnv E12 p (base + start) (stop - start) out scratch ctx k (p + 16) n :=
    (pc10.write _ (by decide)).write _ (by decide)
  have at0 : LayoutAt E12 (zeroed mem3 (scratch + 32)) active (scratch + 32) E12 (zeroed mem3 (scratch + 32)) 0 :=
    ⟨Nat.zero_le _, fun _ _ => rfl, by simp only [E12]; rw [assign_ne (by decide), assign_eq],
      by simp only [E12]; rw [assign_eq],
      fun q hq => by rw [activeByte_zero]; simp only [zeroed, Asm.store]; rw [if_pos ⟨by omega, by omega⟩],
      fun _ _ => rfl⟩
  obtain ⟨E13, mem5, run13, -, same13, -, -, bytes13, frame13⟩ := layoutLoop_ends (m := m) (sp := sp')
    (planOf _ frame4) (by rw [hk]; exact apart_sub' (apart_sub sPlan (by omega) (by omega)) (by omega) (by omega))
    (access_sub sAcc (by omega) (by omega)) (by omega) pc12.range.scratch (by rw [hk]; exact pc12.kV) pc12.bitsV at0
  have pc13 := pc12.congr same13
  have frame5 : ∀ a, ¬ (scratch ≤ a ∧ a < scratch + V) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem5 a = mem a :=
    fun a o pd => by rw [frame13 a (fun h => o ⟨by omega, by omega⟩)]; exact frame4 a o pd
  -- The tree's root and the layout's node, hashed into the output.
  obtain ⟨mem6, call6, node6, keep6⟩ := pairInto_runs (m := m) (w := w) hash (sp := sp') hashRoom (env := E13)
    (mem := mem5) (dst := 14) (out := out) (left := scratch)
    (args := [RootProgressiveContainer.out, RootProgressiveContainer.scratch, RootProgressiveContainer.scratch + 32, 1,
      RootProgressiveContainer.ctx])
    (pre.ready.within (o := scratch) (n := V) sCtx sTable sZeros frame5) (access_sub sAcc (by omega) (by omega))
    (by omega) pre.oAcc (apart_sub sOut (by omega) (by omega)) (apart_sub sPad (by omega) (by omega)) pre.oPad
    pre.oCtx pre.oTable
    (by
      simp only [List.mapM_cons, List.mapM_nil, eval_var pc13.range.out, eval_var pc13.range.scratch,
        eval_add (eval_var pc13.range.scratch) (eval_lit 32), eval_var pc13.range.ctx]
      rfl)
  have body : Runs m w sp' E0 mem RootProgressiveContainer.fn.body (Asm.assign E13 14 0) mem6 := by
    rw [rootProgressiveContainer_body_eq]
    exact Runs.block_append (Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons s3 (Runs.block_cons s4
      (Runs.block_cons r5 (Runs.block_cons s5 (Runs.block_cons s6 (Runs.block_cons s7 (Runs.block_cons run9
        (Runs.block_cons r10 (Runs.block_nil _ _ _ _ _)))))))))))
      (Runs.block_append z (Runs.block_cons s8 (Runs.block_cons s9 (Runs.block_cons run13
        (Runs.block_cons call6 (Runs.block_nil _ _ _ _ _))))))
  have frame : ∀ a, ¬ (out ≤ a ∧ a < out + 32) →
      ¬ (scratch ≤ a ∧ a < scratch + varNeed (.progressiveContainer active names fields) (stop - start)) →
      ¬ (pad ≤ a ∧ a < pad + 1536) → mem6 a = mem a := fun a o s pd => by
    rw [need] at s
    rw [keep6 a o pd]
    exact frame5 a (fun h => s ⟨by omega, by omega⟩) pd
  refine ⟨mem6, Calls.fn fns.progressiveContainer frameRoom rfl body rfl, ?_, pre.readyAfter frame, frame⟩
  -- The root: the progressive tree over the leaves, with the layout's node mixed in.
  have leavesSized := placeRoots_sized active roots sized
  have leavesLen : (placeRoots active roots).length = k := by rw [placeRoots_length, hk]
  obtain ⟨-, joinedSize⟩ := RootProof.joinNodes_nodes _ leavesSized
  rw [leavesLen] at joinedSize
  have n5s : nodeAt mem5 scratch = nodeAt mem3 scratch :=
    nodeAt_congr fun i hi => by rw [frame13 _ (by omega), zeroed_outside (by omega)]
  have n5a : nodeAt mem5 (scratch + 32) = (activeFieldsNode active).data := by
    apply Array.ext
    · simp [nodeAt, activeFieldsNode]
    · intro i h1 h2
      have hi : i < 32 := by simpa [nodeAt] using h1
      simp only [nodeAt, Array.getElem_ofFn]
      rw [bytes13 i hi, activeByte_all active active.length i (Nat.le_refl _) hi]
  have code : rootOf (.progressiveContainer active names fields) b start stop =
      hashPair (merkleizeProgressive (joinNodes (placeRoots active roots)) k) (activeFieldsNode active) := by
    rw [rootOf]
    simp only [cut, Except.toOption, Option.getD_some, hroots, leavesLen]
  have tree := merkleizeProgressive_of_nodeAt (mem := mem2) (a := scratch + 64 + 32 * n) (n := k)
    (x := joinNodes (placeRoots active roots))
    (fun i hi => by
      rw [nodeOf_joinNodes leavesSized (by omega)]
      exact leaves9 i (by omega) (by omega))
    (by omega) (.inr (by rw [usize]; omega)) usize (by omega)
  rw [node6, n5s, root3, n5a, code, RootProof.hashPair_data _ _
    (merkleizeProgressive_spec _ k (by omega) (by rw [usize]; omega)).1 (by simp [activeFieldsNode, ByteArray.size]),
    tree]

end Ssz.Native.Driver
