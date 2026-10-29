import SszNative.Proofs.Driver.Prove.Budget
import SszNative.Proofs.Driver.Validate.Basic
import SszNative.Proofs.Driver.View
import SszNative.Driver.Prove
import SszNative.Proofs.Driver.Branch.Common

/-!
The compiled slot reader finds the value at one position under a tree, as the Lean slots do.

A layout record holds the values under its tree in one of five ways, each a kind the record names in its first word.
The reader answers one with the value's plan node and range, or zero for a gap or a position past the end.
-/

namespace Ssz.Native.Driver.ProveProof

set_option maxRecDepth 20000

open Ssz Ssz.Native Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Ir.Stmt Ssz.Native.Ir.Expr Ssz.Native.Plan

/-- Types that each nest at most some levels nest at most that many at their deepest. -/
theorem deepest_le (k : Nat) : ∀ (ds : List Desc), (∀ d ∈ ds, d.nesting ≤ k) → Desc.deepestNesting ds ≤ k
  | [], _ => Nat.zero_le _
  | d :: rest, each => by
    simp only [Desc.deepestNesting]
    have := each d List.mem_cons_self
    have := deepest_le k rest fun x m => each x (List.mem_cons_of_mem _ m)
    omega

/-- A position of placed fields: a gap at a clear bit, or the field counted by the set bits before it. -/
theorem placeFields_getElem? : ∀ (active : List Bool) (xs : List (Desc × Nat × Nat)) (i : Nat) (h : i < active.length),
    (placeFields active xs)[i]? = some (if active[i] then xs[(active.take i).count true]? else none)
  | false :: active, xs, 0, _ => by simp [placeFields]
  | true :: active, x :: xs, 0, _ => by simp [placeFields]
  | true :: active, [], 0, _ => by simp [placeFields]
  | false :: active, xs, i + 1, h => by
    simp only [placeFields, List.getElem?_cons_succ, List.getElem_cons_succ, List.take_succ_cons,
      List.count_cons_of_ne (by decide : false ≠ true)]
    exact placeFields_getElem? active xs i (by simp at h; omega)
  | true :: active, x :: xs, i + 1, h => by
    simp only [placeFields, List.getElem?_cons_succ, List.getElem_cons_succ, List.take_succ_cons, List.count_cons_self]
    exact placeFields_getElem? active xs i (by simp at h; omega)
  | true :: active, [], i + 1, h => by
    simp only [placeFields, List.getElem?_cons_succ, List.getElem_cons_succ, List.take_succ_cons, List.count_cons_self,
      List.getElem?_nil]
    rw [placeFields_getElem? active [] i (by simp at h; omega)]
    simp

/-- Placed fields take one position per bit of the layout. -/
theorem placed_length : ∀ (active : List Bool) (xs : List (Desc × Nat × Nat)),
    (placeFields active xs).length = active.length
  | [], _ => rfl
  | false :: active, xs => by simp [placeFields, placed_length active xs]
  | true :: active, _ :: xs => by simp [placeFields, placed_length active xs]
  | true :: active, [] => by simp [placeFields, placed_length active []]

/-- The set bits before one more position: those before it, and the bit there. -/
theorem count_take_succ (l : List Bool) (j : Nat) (h : j < l.length) :
    (l.take (j + 1)).count true = (l.take j).count true + if l[j] then 1 else 0 := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  by_cases on : l[j] <;> simp [List.count_append, on]

/-- At most as many bits are set before a position as there are positions before it. -/
theorem count_take_le (l : List Bool) (j : Nat) : (l.take j).count true ≤ j :=
  Nat.le_trans List.count_le_length (List.length_take_le _ _)

/-- One range of a sequence's bodies: from its offset to the next, or to the end for the last. -/
theorem bodyRanges_getElem? (b : ByteArray) (start stop count i : Nat) (h : i < count) :
    (bodyRanges b start stop count)[i]? = some (start + offsetAt b (start + i * 4),
      if i + 1 < count then start + offsetAt b (start + (i + 1) * 4) else start + (stop - start)) := by
  simp only [bodyRanges, bytesPerOffset, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simp; omega)]
  simp only [List.getElem_zip, Option.map_some, List.getElem_map, List.getElem_range]
  split
  · rw [List.getElem_append_left (by simp; omega)]
    simp
  · rw [List.getElem_append_right (by simp; omega)]
    simp


/--
How a layout record holds the values under its tree, as the slot reader reads them.

The record's first word names the kind, its second the count of positions.
Plan nodes are held as addresses whose words are the types', inside a range of addresses, and ranges as positions in
the encoding.
A struct's table of ranges ends by a given address.
Types reached through the plan walk nest at most a given number of levels.
-/
inductive Held (w : World) (mem : Memory) (lay : Nat) (b : ByteArray) (n lo hi top : Nat) : Slots → Prop
  /-- Values of one type, one width apart from a start. -/
  | stride (element : Desc) (start width count q : Nat) (kind : readLE mem lay 8 = 1)
      (counted : readLE mem (lay + 8) 8 = UInt64.ofNat count) (first : readLE mem (lay + 80) 8 = UInt64.ofNat start)
      (plan : readLE mem (lay + 96) 8 = UInt64.ofNat q) (wide : readLE mem (lay + 104) 8 = UInt64.ofNat width)
      (planned : Driver.PlanAt w mem q (words element)) (inPlan : lo ≤ q ∧ q + 8 * (words element).length ≤ hi)
      (small : count < 2 ^ 64) :
      Held w mem lay b n lo hi top (.stride element start width count)
  /-- A struct's fields, each with its range from the table after the record. -/
  | struct (fields : List Desc) (ranges : List (Nat × Nat)) (q : Nat) (kind : readLE mem lay 8 = 2)
      (counted : readLE mem (lay + 8) 8 = UInt64.ofNat fields.length)
      (plan : readLE mem (lay + 96) 8 = UInt64.ofNat q) (planned : Driver.PlanAt w mem q (wordsAll fields))
      (inPlan : lo ≤ q ∧ q + 8 * (wordsAll fields).length ≤ hi) (tableEnd : lay + 152 + 16 * fields.length ≤ top)
      (same : ranges.length = fields.length) (readable : w.access (lay + 144) (8 + 16 * fields.length) = true)
      (table : ∀ k (h : k < ranges.length), readLE mem (lay + 152 + 16 * k) 8 = UInt64.ofNat ranges[k].1 ∧
        readLE mem (lay + 160 + 16 * k) 8 = UInt64.ofNat ranges[k].2)
      (sound : ∀ f ∈ fields, f.wellFormed = .ok ()) (deep : Desc.deepestNesting fields ≤ n) :
      Held w mem lay b n lo hi top (.listed ((fields.zip ranges).map some))
  /-- A progressive struct's fields, placed at the set positions of its layout. -/
  | progressive (active : List Bool) (fields : List Desc) (ranges : List (Nat × Nat)) (q bits : Nat)
      (kind : readLE mem lay 8 = 3) (counted : readLE mem (lay + 8) 8 = UInt64.ofNat active.length)
      (layout : readLE mem (lay + 112) 8 = UInt64.ofNat bits)
      (set : ∀ k (h : k < active.length), w.access (bits + 8 * k) 8 = true ∧
        readLE mem (bits + 8 * k) 8 = if active[k] then 1 else 0)
      (short : active.length < 2 ^ 63)
      (fieldCount : readLE mem (lay + 144) 8 = UInt64.ofNat fields.length)
      (plan : readLE mem (lay + 96) 8 = UInt64.ofNat q) (planned : Driver.PlanAt w mem q (wordsAll fields))
      (inPlan : lo ≤ q ∧ q + 8 * (wordsAll fields).length ≤ hi) (tableEnd : lay + 152 + 16 * fields.length ≤ top)
      (bitsIn : lo ≤ bits ∧ bits + 8 * active.length ≤ hi)
      (same : ranges.length = fields.length) (readable : w.access (lay + 144) (8 + 16 * fields.length) = true)
      (table : ∀ k (h : k < ranges.length), readLE mem (lay + 152 + 16 * k) 8 = UInt64.ofNat ranges[k].1 ∧
        readLE mem (lay + 160 + 16 * k) 8 = UInt64.ofNat ranges[k].2)
      (sound : ∀ f ∈ fields, f.wellFormed = .ok ()) (deep : Desc.deepestNesting fields ≤ n) :
      Held w mem lay b n lo hi top (.listed (placeFields active (fields.zip ranges)))
  /-- A union's selected option, as its one position. -/
  | union (option : Desc) (s e q : Nat) (kind : readLE mem lay 8 = 4) (counted : readLE mem (lay + 8) 8 = 1)
      (first : readLE mem (lay + 80) 8 = UInt64.ofNat s) (last : readLE mem (lay + 88) 8 = UInt64.ofNat e)
      (plan : readLE mem (lay + 96) 8 = UInt64.ofNat q) (planned : Driver.PlanAt w mem q (words option))
      (inPlan : lo ≤ q ∧ q + 8 * (words option).length ≤ hi) :
      Held w mem lay b n lo hi top (.listed [some (option, s, e)])
  /-- A sequence's elements, each found through its offset. -/
  | offsets (element : Desc) (start stop count q data : Nat) (kind : readLE mem lay 8 = 5)
      (counted : readLE mem (lay + 8) 8 = UInt64.ofNat count) (encoding : readLE mem (lay + 72) 8 = UInt64.ofNat data)
      (first : readLE mem (lay + 80) 8 = UInt64.ofNat start) (last : readLE mem (lay + 88) 8 = UInt64.ofNat stop)
      (plan : readLE mem (lay + 96) 8 = UInt64.ofNat q) (planned : Driver.PlanAt w mem q (words element))
      (inPlan : lo ≤ q ∧ q + 8 * (words element).length ≤ hi) (bytes : BytesAt mem data b)
      (readable : w.access data b.size = true) (ordered : start ≤ stop)
      (inside : stop ≤ b.size) (offsetsIn : start + 4 * count ≤ b.size) :
      Held w mem lay b n lo hi top (.listed ((bodyRanges b start stop count).map fun (s, e) => some (element, s, e)))

/-- Memory with three words written one after another from an address. -/
def written3 (mem : Memory) (out : Nat) (a b c : UInt64) : Memory :=
  store (store (store mem out 8 (qwordByte a)) (out + 8) 8 (qwordByte b)) (out + 16) 8 (qwordByte c)

/--
What the slot reader does at a position: a value's plan node, inside a range of addresses, and range written, or
nothing at a gap.
-/
def SlotDone (m : Module) (w : World) (sp lay i out lo hi : Nat) (mem : Memory) :
    Option (Option (Desc × Nat × Nat)) → Prop
  | some (some (d, s, e)) => ∃ q, Driver.PlanAt w mem q (words d) ∧ lo ≤ q ∧ q + 8 * (words d).length ≤ hi ∧
      Calls m w "ssz_prove_slot" sp [UInt64.ofNat lay, UInt64.ofNat i, UInt64.ofNat out] mem 1
        (written3 mem out (UInt64.ofNat q) (UInt64.ofNat s) (UInt64.ofNat e))
  | _ => Calls m w "ssz_prove_slot" sp [UInt64.ofNat lay, UInt64.ofNat i, UInt64.ofNat out] mem 0 mem

/-- The slot reader's last step at a value: its plan node, start, and stop written, and one answered. -/
theorem slot_store {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {out : Nat}
    (at_ : env 2 = UInt64.ofNat out) (found : env 4 = 1) (writable : w.access out 24 = true) :
    Wp m w sp (.block [st (Var.mk 2) (Var.mk 7), st (Var.mk 2 + 8) (Var.mk 5), st (Var.mk 2 + 16) (Var.mk 6)]) env mem
      (fun env' mem' => eval w env' mem' ProveSlot.fn.result = some 1 ∧
        mem' = written3 mem out (env 7) (env 5) (env 6)) := by
  have ob := BranchProof.access_bound writable
  have w0 : w.access out 8 = true := BranchProof.access_prefix writable (by omega)
  have w8 : w.access (out + 8) 8 = true := BranchProof.access_sub writable (by omega)
  have w16 : w.access (out + 16) 8 = true := BranchProof.access_sub writable (by omega)
  refine Wp.store (by wev [at_]) (by wev []) (by wonly [at_, w0]) ?_
  refine Wp.store (by wev [at_]) (by wev []) (by wonly [at_, w8]) ?_
  refine Wp.store (by wev [at_]) (by wev []) (by wonly [at_, w16]) ?_
  refine Wp.done ⟨by wev [ProveSlot.fn, found], ?_⟩
  wonly [at_, written3]

/-- A struct's field, its plan node found by walking past the fields before it. -/
theorem field_plan {w : World} {mem : Memory} {q : Nat} {fields : List Desc} (planned : PlanAt w mem q (wordsAll fields))
    {k : Nat} (inside : k < fields.length) :
    PlanAt w mem q (wordsAll (fields.take k)) ∧
      PlanAt w mem (q + 8 * (wordsAll (fields.take k)).length) (words fields[k]) := by
  rw [← List.take_append_drop k fields, wordsAll_append, List.drop_eq_getElem_cons inside] at planned
  exact ⟨planned.left, (show PlanAt w mem _ (words fields[k] ++ wordsAll (fields.drop (k + 1))) from planned.right).left⟩

/-- A struct's field's plan lies inside the struct's fields' plan. -/
theorem field_plan_length {fields : List Desc} {k : Nat} (inside : k < fields.length) :
    (wordsAll (fields.take k)).length + (words fields[k]).length ≤ (wordsAll fields).length := by
  have := congrArg List.length (Validate.wordsAll_append (fields.take (k + 1)) (fields.drop (k + 1)))
  rw [List.take_append_drop, Validate.wordsAll_take_succ fields k inside] at this
  simp only [List.length_append] at this
  omega

/-- A struct's table entry after the record, readable. -/
theorem table_access {w : World} {lay len k a : Nat} (readable : w.access (lay + 144) (8 + 16 * len) = true)
    (inside : k < len) (ha : a = 8 ∨ a = 16) : w.access (lay + 144 + a + 16 * k) 8 = true := by
  rw [Nat.add_assoc]
  exact BranchProof.access_sub readable (by omega)

set_option maxHeartbeats 1000000 in
/--
The slot reader at a struct's field: the field's plan node found past the fields before it, its range read from the
table, all three written, and one answered.
-/
theorem field_store {m : Module} {w : World} (linked : HasCodec m) {inner n : Nat}
    (stack : w.stackLo + (8 + 8 * planSkip.frame) + walkLevel * n ≤ inner) {env : Env} {mem : Memory}
    {lay out q k x : Nat} {fields : List Desc} {ranges : List (Nat × Nat)} (hx : env x = UInt64.ofNat k)
    (x7 : x ≠ 7) (x5 : x ≠ 5) (h0 : env 0 = UInt64.ofNat lay) (h2 : env 2 = UInt64.ofNat out)
    (fixedPart : w.access lay 144 = true) (plan : readLE mem (lay + 96) 8 = UInt64.ofNat q)
    (planned : PlanAt w mem q (wordsAll fields)) (same : ranges.length = fields.length)
    (readable : w.access (lay + 144) (8 + 16 * fields.length) = true)
    (table : ∀ k (h : k < ranges.length), readLE mem (lay + 152 + 16 * k) 8 = UInt64.ofNat ranges[k].1 ∧
      readLE mem (lay + 160 + 16 * k) 8 = UInt64.ofNat ranges[k].2)
    (sound : ∀ f ∈ fields, f.wellFormed = .ok ()) (deep : Desc.deepestNesting fields ≤ n)
    (inside : k < fields.length) (writable : w.access out 24 = true) :
    Wp m w inner (.block (ProveSlot.field (.var x) ++
      [when (Var.mk 4) [st (Var.mk 2) (Var.mk 7), st (Var.mk 2 + 8) (Var.mk 5), st (Var.mk 2 + 16) (Var.mk 6)]]))
      env mem (fun env' mem' => eval w env' mem' ProveSlot.fn.result = some 1 ∧
        mem' = written3 mem out (UInt64.ofNat (q + 8 * (wordsAll (fields.take k)).length))
          (UInt64.ofNat (ranges[k]'(by omega)).1) (UInt64.ofNat (ranges[k]'(by omega)).2)) := by
  have lb := BranchProof.access_bound readable
  have acc96 : w.access (lay + 96) 8 = true := BranchProof.access_sub fixedPart (by omega)
  have ⟨before, _⟩ := field_plan planned inside
  -- The walk past the fields before this one nests no deeper than the struct's fields.
  have shallow : Desc.deepestNesting (fields.take k) ≤ n :=
    deepest_le n _ fun d member => Nat.le_trans (nesting_le_deepest fields d (List.mem_of_mem_take member)) deep
  have more := Nat.mul_le_mul_left walkLevel shallow
  have sk := skip_ok m w linked (fields.take k) (fun d member => next_ok m w linked d (sound d
    (List.mem_of_mem_take member))) inner mem q before (by omega)
  rw [List.length_take, Nat.min_eq_left (by omega)] at sk
  have ⟨start, stop⟩ := table k (by omega)
  have startAcc := table_access (k := k) readable inside (Or.inl rfl)
  have stopAcc := table_access (k := k) readable inside (Or.inr rfl)
  rw [show lay + 144 + 8 = lay + 152 by omega] at startAcc
  rw [show lay + 144 + 16 = lay + 160 by omega] at stopAcc
  simp only [ProveSlot.field, List.cons_append, List.nil_append]
  wcall sk [hx, h0, plan, acc96]
  wsteps [hx, x7, x5, h0, start, stop, startAcc, stopAcc]
  refine Wp.mono (slot_store (by wev [h2]) (by wev []) writable) fun env' mem' ⟨r, same⟩ => ⟨r, ?_⟩
  rw [same]
  wonly [written3, hx, x7, x5]

/-- The stack a slot read needs, with the plan walk under it for types nesting some levels. -/
abbrev slotRoom (n : Nat) : Nat := 8 + 8 * ProveSlot.fn.frame + (8 + 8 * planSkip.frame) + walkLevel * n

set_option maxHeartbeats 2000000 in
/--
A call of the slot reader at a position of a held record does what the Lean slots say is there.

It answers one and writes the value's plan node, start, and stop, or answers zero and writes nothing.
-/
theorem slot_calls {m : Module} {w : World} (linked : HasCodec m)
    (hf : m.fns.lookup "ssz_prove_slot" = some ProveSlot.fn) {sp n : Nat} (room : w.stackLo + slotRoom n ≤ sp)
    {mem : Memory} {lay lo hi top : Nat} {b : ByteArray} {slots : Slots}
    (held : Held w mem lay b n lo hi top slots)
    (fixedPart : w.access lay 144 = true) (i out : Nat) (iSmall : i < 2 ^ 63) (writable : w.access out 24 = true) :
    SlotDone m w sp lay i out lo hi mem (slots.at i) := by
  have lb := BranchProof.access_bound fixedPart
  have ob := BranchProof.access_bound writable
  have acc : ∀ k, k + 8 ≤ 144 → w.access (lay + k) 8 = true := fun k hk => BranchProof.access_sub fixedPart (by omega)
  have acc0 : w.access lay 8 = true := BranchProof.access_prefix fixedPart (by omega)
  have out0 : w.access out 8 = true := BranchProof.access_prefix writable (by omega)
  have outk : ∀ k, k + 8 ≤ 24 → w.access (out + k) 8 = true := fun k hk => BranchProof.access_sub writable (by omega)
  generalize hinner : sp - 8 - 8 * ProveSlot.fn.frame = inner
  cases held with
  | stride element start width count q kind counted first plan wide planned inPlan small =>
    simp only [Slots.at]
    by_cases inside : i < count
    · simp only [inside, if_true, SlotDone]
      refine ⟨q, planned, inPlan.1, inPlan.2, Calls.of_wp hf (by simp only [slotRoom] at room; omega) rfl ?_⟩
      rw [hinner]
      simp only [ProveSlot.fn]
      wsteps [acc, acc0, kind, counted, first, plan, wide, inside]
      refine Wp.mono (slot_store (by wev []) (by wev []) writable) fun env' mem' ⟨r, same⟩ => ⟨r, ?_⟩
      rw [same]
      wonly [written3]
      -- The value stops one width past where it starts.
      simp only [Nat.mul_succ, Nat.add_assoc]
    · simp only [inside, if_false, SlotDone]
      refine Calls.of_wp hf (by simp only [slotRoom] at room; omega) rfl ?_
      rw [hinner]
      simp only [ProveSlot.fn]
      wsteps [acc, acc0, kind, counted, first, inside]
      exact ⟨by wev [], trivial⟩
  | union option s e q kind counted first last plan planned inPlan =>
    simp only [Slots.at]
    by_cases zero : i = 0
    · subst zero
      simp only [List.getElem?_cons_zero, SlotDone]
      refine ⟨q, planned, inPlan.1, inPlan.2, Calls.of_wp hf (by simp only [slotRoom] at room; omega) rfl ?_⟩
      rw [hinner]
      simp only [ProveSlot.fn]
      wsteps [acc, acc0, kind, counted, first, last, plan]
      refine Wp.mono (slot_store (by wev []) (by wev []) writable) fun env' mem' ⟨r, same⟩ => ⟨r, ?_⟩
      rw [same]
      wonly [written3]
    · simp only [List.getElem?_cons, zero, if_false, List.getElem?_nil, SlotDone]
      refine Calls.of_wp hf (by simp only [slotRoom] at room; omega) rfl ?_
      rw [hinner]
      simp only [ProveSlot.fn]
      wsteps [acc, acc0, kind, counted, show ¬ i < 1 by omega]
      exact ⟨by wev [], trivial⟩
  | offsets element start stop count q data kind counted encoding first last plan planned inPlan bytes readable ordered
      inside offsetsIn =>
    simp only [Slots.at, List.getElem?_map]
    have db := BranchProof.access_bound readable
    by_cases within : i < count
    · rw [bodyRanges_getElem? b start stop count i within]
      simp only [Option.map_some, SlotDone]
      refine ⟨q, planned, inPlan.1, inPlan.2, Calls.of_wp hf (by simp only [slotRoom] at room; omega) rfl ?_⟩
      rw [hinner]
      simp only [ProveSlot.fn]
      -- The element's offset, read from the table at the sequence's start.
      have offset : readLE mem (data + start + 4 * i) 4 = UInt64.ofNat (offsetAt b (start + i * 4)) := by
        rw [show data + start + 4 * i = data + (start + i * 4) by omega,
          readLE_offset mem data b bytes _ (by omega)]
      have offsetAcc : w.access (data + start + 4 * i) 4 = true := by
        rw [show data + start + 4 * i = data + (start + 4 * i) by omega]
        exact BranchProof.access_sub readable (by omega)
      by_cases more : i + 1 < count
      · -- A body runs to the next offset.
        have next : readLE mem (data + start + 4 * i + 4) 4 = UInt64.ofNat (offsetAt b (start + (i + 1) * 4)) := by
          rw [show data + start + 4 * i + 4 = data + (start + (i + 1) * 4) by omega,
            readLE_offset mem data b bytes _ (by omega)]
        have nextAcc : w.access (data + start + 4 * i + 4) 4 = true := by
          rw [show data + start + 4 * i + 4 = data + (start + 4 * i + 4) by omega]
          exact BranchProof.access_sub readable (by omega)
        simp only [more, if_true]
        wsteps [acc, acc0, kind, counted, encoding, first, plan, within, offset, offsetAcc, next, nextAcc, more]
        refine Wp.mono (slot_store (by wev []) (by wev []) writable) fun env' mem' ⟨r, same⟩ => ⟨r, ?_⟩
        rw [same]
        wonly [written3]
      · -- The last body runs to the end.
        simp only [more, if_false, Nat.add_sub_cancel' ordered]
        wsteps [acc, acc0, kind, counted, encoding, first, last, plan, within, offset, offsetAcc, more]
        refine Wp.mono (slot_store (by wev []) (by wev []) writable) fun env' mem' ⟨r, same⟩ => ⟨r, ?_⟩
        rw [same]
        wonly [written3]
    · rw [List.getElem?_eq_none (by simp [bodyRanges]; omega)]
      simp only [Option.map_none, SlotDone]
      refine Calls.of_wp hf (by simp only [slotRoom] at room; omega) rfl ?_
      rw [hinner]
      simp only [ProveSlot.fn]
      wsteps [acc, acc0, kind, counted, within]
      exact ⟨by wev [], trivial⟩
  | struct fields ranges q kind counted plan planned inPlan tableEnd same readable table sound deep =>
    simp only [Slots.at, List.getElem?_map]
    have tb := BranchProof.access_bound readable
    have skipRoom : w.stackLo + (8 + 8 * planSkip.frame) + walkLevel * n ≤ inner := by
      simp only [slotRoom] at room; omega
    by_cases within : i < fields.length
    · rw [List.getElem?_eq_getElem (by simp; omega)]
      simp only [Option.map_some, List.getElem_zip, SlotDone]
      refine ⟨_, (field_plan planned within).2, by omega,
        by have := field_plan_length within; omega, Calls.of_wp hf (by simp only [slotRoom] at room; omega) rfl ?_⟩
      rw [hinner]
      simp only [ProveSlot.fn]
      wsteps [acc, acc0, kind, counted, within]
      refine field_store (x := 1) (k := i) linked skipRoom ?_ (by decide) (by decide) ?_ ?_
        fixedPart plan planned same readable table sound deep within writable
      all_goals wev []
    · rw [List.getElem?_eq_none (by simp; omega)]
      simp only [Option.map_none, SlotDone]
      refine Calls.of_wp hf (by simp only [slotRoom] at room; omega) rfl ?_
      rw [hinner]
      simp only [ProveSlot.fn]
      wsteps [acc, acc0, kind, counted, within]
      exact ⟨by wev [], trivial⟩
  | progressive active fields ranges q bits kind counted layout set short fieldCount plan planned inPlan tableEnd
      bitsIn same readable table sound deep =>
    simp only [Slots.at]
    have tb := BranchProof.access_bound readable
    have skipRoom : w.stackLo + (8 + 8 * planSkip.frame) + walkLevel * n ≤ inner := by
      simp only [slotRoom] at room; omega
    by_cases within : i < active.length
    · rw [placeFields_getElem? active _ i within]
      have ⟨bitAcc, bitVal⟩ := set i within
      have bb := BranchProof.access_bound bitAcc
      by_cases on : active[i] = true
      · -- A set position: its field is the one after those of the set positions before it.
        generalize hc : (active.take i).count true = c
        have cle : c ≤ i := hc ▸ count_take_le active i
        rw [if_pos on] at bitVal
        simp only [on, if_true]
        -- The run up to the loop counting the set positions before this one.
        have toLoop : ∀ (Q : Env → Memory → Prop), (∀ env, env 11 = UInt64.ofNat i → env 12 = UInt64.ofNat c →
            env 0 = UInt64.ofNat lay → env 1 = UInt64.ofNat i → env 2 = UInt64.ofNat out → env 4 = 0 →
            Wp m w inner (.block (when (lt (Var.mk 12) (ld (Var.mk 0 + 144))) (ProveSlot.field (Var.mk 12)) ::
              [when (Var.mk 4) [st (Var.mk 2) (Var.mk 7), st (Var.mk 2 + 8) (Var.mk 5),
                st (Var.mk 2 + 16) (Var.mk 6)]])) env mem Q) →
            Wp m w inner ProveSlot.fn.body (entryEnv [UInt64.ofNat lay, UInt64.ofNat i, UInt64.ofNat out]) mem Q := by
          intro Q rest
          simp only [ProveSlot.fn]
          wsteps [acc, acc0, kind, counted, within, layout, bitAcc, bitVal]
          refine Wp.loop (wp_loop (fun env mem' => mem' = mem ∧ ∃ jj, jj ≤ i ∧ env 11 = UInt64.ofNat jj ∧
              env 12 = UInt64.ofNat ((active.take jj).count true) ∧ env 0 = UInt64.ofNat lay ∧
              env 1 = UInt64.ofNat i ∧ env 2 = UInt64.ofNat out ∧ env 4 = 0 ∧ env 13 = UInt64.ofNat bits)
            (fun env _ => i - (env 11).toNat) ?_ ?_)
          · refine ⟨rfl, 0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> wev []
          rintro env mem' ⟨rfl, jj, hjj, h11, h12, h0, h1, h2, h4, h13⟩
          refine ⟨_, by wev [h11, h1], fun nz => ?_, fun z => ?_⟩
          · have below : jj < i := by
              rcases Nat.lt_or_ge jj i with h | h
              · exact h
              · simp [show ¬ jj < i by omega] at nz
            have ⟨jAcc, jVal⟩ := set jj (by omega)
            have jb := BranchProof.access_bound jAcc
            have step := count_take_succ active jj (by omega)
            by_cases jOn : active[jj] = true
            · simp only [jOn, if_true] at jVal step
              wsteps [h11, h12, h13, jAcc, jVal]
              exact ⟨⟨trivial, jj + 1, by omega, by wev [h11], by wev [h12, step], by wev [h0], by wev [h1],
                by wev [h2], by wev [h4], by wev [h13]⟩, by wonly [h11]; omega⟩
            · simp only [jOn, Bool.false_eq_true, if_false] at jVal step
              wsteps [h11, h12, h13, jAcc, jVal]
              exact ⟨⟨trivial, jj + 1, by omega, by wev [h11], by wev [h12, step], by wev [h0], by wev [h1],
                by wev [h2], by wev [h4], by wev [h13]⟩, by wonly [h11]; omega⟩
          · have done : jj = i := by
              rcases Nat.lt_or_ge jj i with h | h
              · simp [h] at z
              · omega
            subst done
            exact rest env h11 (by rw [h12, hc]) h0 h1 h2 h4
        by_cases has : c < fields.length
        · rw [List.getElem?_eq_getElem (by simp; omega)]
          simp only [List.getElem_zip, SlotDone]
          refine ⟨_, (field_plan planned has).2, by omega,
            by have := field_plan_length has; omega, Calls.of_wp hf (by simp only [slotRoom] at room; omega) rfl ?_⟩
          rw [hinner]
          refine toLoop _ fun env h11 h12 h0 h1 h2 h4 => ?_
          have acc144 : w.access (lay + 144) 8 = true := BranchProof.access_prefix readable (by omega)
          wsteps [h12, h0, fieldCount, acc144, has]
          exact field_store (x := 12) (k := c) linked skipRoom h12 (by decide) (by decide) h0 h2 fixedPart plan
            planned same readable table sound deep has writable
        · rw [List.getElem?_eq_none (by simp; omega)]
          simp only [SlotDone]
          refine Calls.of_wp hf (by simp only [slotRoom] at room; omega) rfl ?_
          rw [hinner]
          refine toLoop _ fun env h11 h12 h0 h1 h2 h4 => ?_
          have acc144 : w.access (lay + 144) 8 = true := BranchProof.access_prefix readable (by omega)
          wsteps [h12, h0, h4, fieldCount, acc144, has]
          exact ⟨by wev [ProveSlot.fn, h4], trivial⟩
      · -- A clear position is a gap.
        rw [if_neg on] at bitVal
        simp only [on, Bool.false_eq_true, if_false, SlotDone]
        refine Calls.of_wp hf (by simp only [slotRoom] at room; omega) rfl ?_
        rw [hinner]
        simp only [ProveSlot.fn]
        wsteps [acc, acc0, kind, counted, within, layout, bitAcc, bitVal]
        exact ⟨by wev [], trivial⟩
    · rw [List.getElem?_eq_none (by rw [placed_length]; omega)]
      simp only [SlotDone]
      refine Calls.of_wp hf (by simp only [slotRoom] at room; omega) rfl ?_
      rw [hinner]
      simp only [ProveSlot.fn]
      wsteps [acc, acc0, kind, counted, within]
      exact ⟨by wev [], trivial⟩

end Ssz.Native.Driver.ProveProof
