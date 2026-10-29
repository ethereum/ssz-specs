import SszNative.Proofs.Driver.Prove.Layout
import SszNative.Proofs.Driver.Root.Top
import SszNative.Proofs.Branch.Leaves
import SszNative.Proofs.Driver.Prove.Branch

/-!
The compiled leaves driver writes the leaves of a tree from one position to another, as the Lean leaves do.

Packed bytes are gathered from the encoding, with a bit list's delimiter cleared.
Plain values one width apart are rooted together, and every other value is rooted on its own, its plan and range found
by the slot reader.
What the calls rooting values do is taken as hypotheses, so the proof serves any type.
-/

namespace Ssz.Native.Driver.ProveProof

set_option maxRecDepth 20000

open Ssz Ssz.Native Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Ir.Stmt Ssz.Native.Ir.Expr Ssz.Native.Plan

/-! ### Records kept where memory agrees -/

/-- Eight bytes read the same where memory agrees on them. -/
theorem read_keep {mem mm : Memory} {a : Nat} {keep : Nat → Prop} (h : ∀ x, keep x → mm x = mem x)
    (inside : ∀ k < 8, keep (a + k)) : readLE mm a 8 = readLE mem a 8 :=
  readLE_congr _ _ _ 8 fun k hk => h _ (inside k hk)

/-- A plan's words stay where memory agrees on a range holding them. -/
theorem PlanAt.keep {w : World} {mem mm : Memory} {q lo hi : Nat} {ws : List Nat} (h : PlanAt w mem q ws)
    (within : lo ≤ q ∧ q + 8 * ws.length ≤ hi) (same : ∀ a, lo ≤ a → a < hi → mm a = mem a) : PlanAt w mm q ws :=
  PlanAt.frame h fun a h1 h2 => same a (by omega) (by omega)

/--
Where a record's values are read from: the record but for the walk's own words, the type's plan, and the encoding.
-/
def RecordFoot (lay top lo hi data size : Nat) (a : Nat) : Prop :=
  (lay ≤ a ∧ a < lay + 120) ∨ (lay + 144 ≤ a ∧ a < top) ∨ (lo ≤ a ∧ a < hi) ∨ (data ≤ a ∧ a < data + size)

/--
The values a record holds stay held where memory agrees on the record, the type's plan, and the encoding.

The record's fixed part and any table end by the given address.
-/
theorem Held.keep {w : World} {mem mm : Memory} {lay data : Nat} {b : ByteArray} {n lo hi top : Nat} {slots : Slots}
    (h : Held w mem lay b n lo hi top slots) (base : lay + 144 ≤ top)
    (encoding : readLE mem (lay + 72) 8 = UInt64.ofNat data) (dataSmall : data < 2 ^ 64)
    (same : ∀ a, RecordFoot lay top lo hi data b.size a → mm a = mem a) :
    Held w mm lay b n lo hi top slots := by
  have word : ∀ k, k + 8 ≤ 120 → readLE mm (lay + k) 8 = readLE mem (lay + k) 8 := fun k hk =>
    read_keep same fun i hi => by simp only [RecordFoot]; omega
  have word0 : readLE mm lay 8 = readLE mem lay 8 := by simpa using word 0 (by omega)
  have plan : ∀ a, lo ≤ a → a < hi → mm a = mem a := fun a h1 h2 => same a (by simp only [RecordFoot]; omega)
  cases h with
  | stride element start width count q kind counted first plan' wide planned inPlan small =>
    exact .stride element start width count q (by rw [word0, kind]) (by rw [word 8 (by omega), counted])
      (by rw [word 80 (by omega), first]) (by rw [word 96 (by omega), plan']) (by rw [word 104 (by omega), wide])
      (PlanAt.keep planned inPlan plan) inPlan small
  | struct fields ranges q kind counted plan' planned inPlan tableEnd same' readable table sound deep =>
    refine .struct fields ranges q (by rw [word0, kind]) (by rw [word 8 (by omega), counted])
      (by rw [word 96 (by omega), plan']) (PlanAt.keep planned inPlan plan) inPlan tableEnd same' readable
      (fun k hk => ?_) sound deep
    rw [read_keep same fun i hi => by simp only [RecordFoot]; omega,
      read_keep (a := lay + 160 + 16 * k) same fun i hi => by simp only [RecordFoot]; omega]
    exact table k hk
  | progressive active fields ranges q bits kind counted layout set short fieldCount plan' planned inPlan tableEnd
      bitsIn same' readable table sound deep =>
    refine .progressive active fields ranges q bits (by rw [word0, kind]) (by rw [word 8 (by omega), counted])
      (by rw [word 112 (by omega), layout]) (fun k hk => ⟨(set k hk).1, ?_⟩) short
      (by rw [read_keep same fun i hi => by simp only [RecordFoot]; omega, fieldCount])
      (by rw [word 96 (by omega), plan']) (PlanAt.keep planned inPlan plan) inPlan tableEnd bitsIn same' readable
      (fun k hk => ?_) sound deep
    · rw [read_keep same fun i hi => by simp only [RecordFoot]; omega]
      exact (set k hk).2
    · rw [read_keep same fun i hi => by simp only [RecordFoot]; omega,
        read_keep (a := lay + 160 + 16 * k) same fun i hi => by simp only [RecordFoot]; omega]
      exact table k hk
  | union option s e q kind counted first last plan' planned inPlan =>
    exact .union option s e q (by rw [word0, kind]) (by rw [word 8 (by omega), counted])
      (by rw [word 80 (by omega), first]) (by rw [word 88 (by omega), last]) (by rw [word 96 (by omega), plan'])
      (PlanAt.keep planned inPlan plan) inPlan
  | offsets element start stop count q data' kind counted encoding' first last plan' planned inPlan bytes readable
      ordered inside offsetsIn =>
    -- The record names one encoding, so the values' encoding is the one memory agrees on.
    have db := BranchProof.access_bound readable
    have same_data : data' = data := by
      have := encoding'.symm.trans encoding
      exact (Validate.ofNat_eq_ofNat (by omega) dataSmall).mp this
    subst same_data
    exact .offsets element start stop count q data' (by rw [word0, kind]) (by rw [word 8 (by omega), counted])
      (by rw [word 72 (by omega), encoding']) (by rw [word 80 (by omega), first]) (by rw [word 88 (by omega), last])
      (by rw [word 96 (by omega), plan']) (PlanAt.keep planned inPlan plan) inPlan
      (fun k hk => by rw [same _ (by simp only [RecordFoot]; omega)]; exact bytes k hk) readable ordered inside
      offsetsIn

/-- A record's leaves stay where memory agrees on the record, the type's plan, and the encoding. -/
theorem LeavesAt.keep {w : World} {mem mm : Memory} {lay data : Nat} {b : ByteArray} {n lo hi top : Nat}
    {leaves : EncodedLeaves} (h : LeavesAt w mem lay b n lo hi top leaves) (base : lay + 144 ≤ top)
    (encoding : readLE mem (lay + 72) 8 = UInt64.ofNat data) (dataSmall : data < 2 ^ 64)
    (same : ∀ a, RecordFoot lay top lo hi data b.size a → mm a = mem a) :
    LeavesAt w mm lay b n lo hi top leaves := by
  have word : ∀ k, k + 8 ≤ 120 → readLE mm (lay + k) 8 = readLE mem (lay + k) 8 := fun k hk =>
    read_keep same fun i hi => by simp only [RecordFoot]; omega
  have word0 : readLE mm lay 8 = readLE mem lay 8 := by simpa using word 0 (by omega)
  cases h with
  | packed a e cut kind first last flag bit cutSmall ordered inside =>
    exact .packed a e cut (by rw [word0, kind]) (by rw [word 80 (by omega), first]) (by rw [word 88 (by omega), last])
      (by rw [word 104 (by omega), flag]) (fun k hk => by rw [word 112 (by omega), bit k hk]) cutSmall ordered inside
  | nested slots held plainFlag =>
    exact .nested slots (held.keep base encoding dataSmall same)
      (fun e s wd c hs => by rw [word 112 (by omega), plainFlag e s wd c hs])

/-! ### The leaves as nodes -/

/-- Leaves of a layout from one position to another: as many as reach the last, cut to the layout's count. -/
theorem leavesIn_count (b : ByteArray) (layout : EncodedLayout) (first last : Nat) :
    (leavesIn b layout first last).2 = min last layout.count - first := by
  obtain ⟨leaves, limit, mixin⟩ := layout
  cases leaves with
  | packed => rfl
  | nested slots =>
    cases slots with
    | stride => simp only [leavesIn]; split <;> rfl
    | listed => rfl

/-- The leaf at a position: a value's root, or the zero node for a gap or a position past the end. -/
def slotRoot (b : ByteArray) : Option (Option (Desc × Nat × Nat)) → ByteArray
  | some (some (d, s, e)) => rootOf d b s e
  | _ => zeroNode

/-- A layout's values, as the slot reader finds them, or nothing under packed leaves. -/
def leafSlot (layout : EncodedLayout) (i : Nat) : Option (Option (Desc × Nat × Nat)) :=
  match layout.leaves with
  | .nested slots => slots.at i
  | .packed _ _ => none

/-- Joined nodes, read back from memory node by node, are the bytes memory holds. -/
theorem bytesAt_joinNodes {mem : Memory} {buf : Nat} {rs : List ByteArray} (sized : ∀ r ∈ rs, r.size = 32)
    (nodes : ∀ i (h : i < rs.length), nodeAt mem (buf + 32 * i) = rs[i].data) :
    bytesAt mem buf (32 * rs.length) = joinNodes rs := by
  have size := (RootProof.joinNodes_nodes rs sized).2
  apply ByteArray.ext
  apply Array.ext
  · simp only [bytesAt, Array.size_ofFn, ← ByteArray.size_data] at size ⊢
    exact size.symm
  · intro j h1 h2
    have hj : j < 32 * rs.length := by simpa [bytesAt] using h1
    have hi : j / 32 < rs.length := by omega
    have r32 : rs[j / 32].size = 32 := sized _ (List.getElem_mem hi)
    have node := nodeOf_joinNodes sized hi
    have here := nodes (j / 32) hi
    -- Byte j is byte j % 32 of node j / 32, both in memory and in the joined buffer.
    have inMem : mem (buf + j) = rs[j / 32].data[j % 32]'(by rw [ByteArray.size_data, r32]; omega) := by
      have := nodeAt_get mem (buf + 32 * (j / 32)) (j % 32) (by omega)
      simp only [here] at this
      rw [show buf + j = buf + 32 * (j / 32) + j % 32 by omega, ← this]
    have inJoin : (joinNodes rs).data[j]'h2 = rs[j / 32].data[j % 32]'(by rw [ByteArray.size_data, r32]; omega) := by
      have e := congrArg (fun a : Array UInt8 => a[j % 32]?) node
      simp only [Ssz.Native.nodeOf, ByteArray.data_extract] at e
      rw [Array.getElem?_extract, if_pos (by rw [ByteArray.size_data, size]; omega),
        show 0 + 32 * (j / 32) + j % 32 = j by omega, Array.getElem?_eq_getElem h2,
        Array.getElem?_eq_getElem (by rw [ByteArray.size_data, r32]; omega)] at e
      exact Option.some.inj e
    simp only [bytesAt, Array.getElem_ofFn]
    rw [inJoin, ← inMem]

/-- A listed position's root is the leaf at it. -/
theorem slotRoot_some (b : ByteArray) (x : Option (Desc × Nat × Nat)) : slotRoot b (some x) = listedRoot b x := by
  rcases x with _ | ⟨d, s, e⟩ <;> rfl

/-- Nested leaves rooted one at a time are each position's leaf, joined. -/
theorem leavesIn_nested {b : ByteArray} {layout : EncodedLayout} {slots : Slots} (first last : Nat)
    (nested : layout.leaves = .nested slots)
    (notChunked : ∀ e s wd c, slots = .stride e s wd c → plain e = false) :
    (leavesIn b layout first last).1 =
      joinNodes ((List.range (min last layout.count - first)).map fun i => slotRoot b (slots.at (first + i))) := by
  obtain ⟨leaves, limit, mixin⟩ := layout
  simp only at nested
  subst nested
  cases slots with
  | stride e s wd c =>
    simp only [leavesIn, notChunked e s wd c rfl, EncodedLayout.count, Slots.count, Bool.false_eq_true, if_false]
    congr 1
    apply List.map_congr_left
    intro i hi
    have := List.mem_range.mp hi
    simp only [Slots.at, show first + i < c by omega, if_true, slotRoot]
  | listed l =>
    simp only [leavesIn, EncodedLayout.count, Slots.count]
    congr 1
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range, Slots.at]
    rw [List.getElem?_eq_getElem (by simp at h1; omega), slotRoot_some]

/-! ### Packed bytes -/

/-- A byte of a range packed into nodes: the encoding's byte inside the range, zero past it. -/
def packByte (b : ByteArray) (a e p : Nat) : UInt8 :=
  if p < e - a then b.get! (a + p) else 0

/-- A byte with a bit list's delimiter cleared, when there is one. -/
def clearCut : Option Nat → UInt8 → UInt8
  | none, x => x
  | some k, x => x &&& ~~~((1 : UInt8) <<< UInt8.ofNat k)

/-- A range packed into nodes takes its nodes and one more. -/
theorem packRange_size (b : ByteArray) {a e : Nat} (ordered : a ≤ e) (inside : e ≤ b.size)
    (small : e - a + 64 < USize.size) : (packRange b a e).size = 32 * nodesFor (e - a) + 32 := by
  rw [← ByteArray.size_data, RootProof.packRange_data b a e ordered inside small]
  simp [nodesFor]
  omega

/-- A byte of a range packed into nodes. -/
theorem packRange_get (b : ByteArray) {a e p : Nat} (ordered : a ≤ e) (inside : e ≤ b.size)
    (small : e - a + 64 < USize.size) (hp : p < 32 * nodesFor (e - a) + 32) :
    (packRange b a e).get! p = packByte b a e p := by
  have size := packRange_size b ordered inside small
  rw [Kernel.get!_eq _ _ (by omega), ByteArray.getElem_eq_getElem_data]
  simp only [RootProof.packRange_data b a e ordered inside small, packByte]
  split
  · rw [Array.getElem_append_left (by simp; omega), Kernel.get!_eq _ _ (by omega),
      ByteArray.getElem_eq_getElem_data]
    simp
  · rw [Array.getElem_append_right (by simp; omega)]
    simp

/-- A packed range's nodes take as many bytes as the range packed into nodes. -/
theorem packedNodes_size (b : ByteArray) {a e : Nat} (cut : Option Nat) (ordered : a ≤ e) (inside : e ≤ b.size)
    (small : e - a + 64 < USize.size) : (packedNodes b a e cut).size = 32 * nodesFor (e - a) + 32 := by
  cases cut with
  | none => exact packRange_size b ordered inside small
  | some k =>
    simp only [packedNodes, ByteArray.set!, ByteArray.size, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    exact packRange_size b ordered inside small

/-- A byte of a packed range: the range's byte, with the delimiter cleared from the last one. -/
theorem packedNodes_get (b : ByteArray) {a e p : Nat} (cut : Option Nat) (ordered : a ≤ e) (inside : e ≤ b.size)
    (small : e - a + 64 < USize.size) (hp : p < 32 * nodesFor (e - a) + 32) (nonempty : ∀ k, cut = some k → a < e) :
    (packedNodes b a e cut).get! p =
      if p + 1 = e - a then clearCut cut (packByte b a e p) else packByte b a e p := by
  have size := packRange_size b ordered inside small
  cases cut with
  | none => simp only [packedNodes, clearCut, ite_self]; exact packRange_get b ordered inside small hp
  | some k =>
    have ne := nonempty k rfl
    simp only [packedNodes, clearCut]
    rw [← packRange_get b ordered inside small hp]
    simp only [ByteArray.set!, ByteArray.get!, Array.set!_eq_setIfInBounds]
    rw [getElem!_pos _ p (by simp; omega), Array.getElem_setIfInBounds (by simp; omega)]
    by_cases last : p + 1 = e - a
    · rw [if_pos (by omega), if_pos last, getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by simp; omega)]
      congr 2
      omega
    · rw [if_neg (by omega), if_neg last, getElem!_pos _ _ (by simp; omega)]


/-! ### Values rooted one at a time -/

/-- The variables the leaves driver keeps once it knows its count. -/
structure LeavesEnv (env : Env) (lay first buf ctx cnt data : Nat) : Prop where
  /-- The layout record. -/
  lay : env 0 = UInt64.ofNat lay
  /-- The first leaf. -/
  first : env 1 = UInt64.ofNat first
  /-- Where the nodes go. -/
  buf : env 3 = UInt64.ofNat buf
  /-- The context. -/
  ctx : env 4 = UInt64.ofNat ctx
  /-- How many leaves. -/
  cnt : env 5 = UInt64.ofNat cnt
  /-- The encoding's address. -/
  data : env 7 = UInt64.ofNat data

/-- Writing a variable past those kept keeps them. -/
theorem LeavesEnv.write {env : Env} {lay first buf ctx cnt data : Nat} (h : LeavesEnv env lay first buf ctx cnt data)
    {x : Nat} (v : UInt64) (hx : 8 ≤ x) : LeavesEnv (Asm.assign env x v) lay first buf ctx cnt data :=
  ⟨by rw [assign_ne (by omega), h.lay], by rw [assign_ne (by omega), h.first], by rw [assign_ne (by omega), h.buf],
    by rw [assign_ne (by omega), h.ctx], by rw [assign_ne (by omega), h.cnt], by rw [assign_ne (by omega), h.data]⟩

/-- Memory changed only in a buffer and the padding area. -/
def Kept (mem mm : Memory) (buf span pad : Nat) : Prop :=
  ∀ a, ¬ (buf ≤ a ∧ a < buf + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm a = mem a

/-- The bytes a record, the type's plan, and the encoding take. -/
def Footprint (lay top lo hi data size : Nat) (a : Nat) : Prop :=
  (lay ≤ a ∧ a < top) ∨ (lo ≤ a ∧ a < hi) ∨ (data ≤ a ∧ a < data + size)

/--
What a call rooting the value at one of the positions does, from memory changed only in the buffer and the padding
area.

It writes the value's root as node i of the buffer, and changes nothing else but the scratch past the nodes and the
padding area.
-/
def RootCalls (m : Module) (w : World) (sp : Nat) (mem : Memory) (b : ByteArray) (slots : Slots)
    (data first cnt buf span pad ctx lo hi : Nat) : Prop :=
  ∀ (mm : Memory) (i : Nat) (d : Desc) (s e q : Nat), Kept mem mm buf span pad → i < cnt →
    slots.at (first + i) = some (some (d, s, e)) → PlanAt w mm q (words d) → lo ≤ q →
    q + 8 * (words d).length ≤ hi →
    ∃ mm', Calls m w "ssz_root_of" sp [UInt64.ofNat q, UInt64.ofNat data + UInt64.ofNat s,
        UInt64.ofNat e - UInt64.ofNat s, UInt64.ofNat (buf + 32 * i), UInt64.ofNat (buf + 32 * cnt + 64),
        UInt64.ofNat ctx] mm 0 mm' ∧
      nodeAt mm' (buf + 32 * i) = (rootOf d b s e).data ∧
      ∀ a, ¬ (buf + 32 * i ≤ a ∧ a < buf + 32 * i + 32) → ¬ (buf + 32 * cnt + 64 ≤ a ∧ a < buf + span) →
        ¬ (pad ≤ a ∧ a < pad + 1536) → mm' a = mm a

/-- The leaves driver's loop rooting values one at a time. -/
abbrev leavesLoop : List Stmt :=
  [ProveLeaves.sl ::= ProveLeaves.buf + 32 * ProveLeaves.cnt + 32, ProveLeaves.i ::= 0,
    while_ (lt ProveLeaves.i ProveLeaves.cnt) [callInto ProveLeaves.sink "ssz_prove_slot"
        [ProveLeaves.lay, ProveLeaves.first + ProveLeaves.i, ProveLeaves.sl],
      ifElse ProveLeaves.sink
        [callInto ProveLeaves.sink "ssz_root_of"
          [ld ProveLeaves.sl, ProveLeaves.data + ld (ProveLeaves.sl + 8),
            ld (ProveLeaves.sl + 16) - ld (ProveLeaves.sl + 8), ProveLeaves.buf + 32 * ProveLeaves.i,
            ProveLeaves.sl + 32, ProveLeaves.ctx]]
        (zero32 (ProveLeaves.buf + 32 * ProveLeaves.i)),
      ProveLeaves.i ::= ProveLeaves.i + 1]]

/-- The loop's state: the values before one position rooted, and memory changed only in the buffer and the pad. -/
def LoopInv (mem : Memory) (b : ByteArray) (slots : Slots) (lay first buf ctx cnt data span pad : Nat) (env : Env)
    (mm : Memory) : Prop :=
  ∃ k, k ≤ cnt ∧ env 14 = UInt64.ofNat k ∧ env 15 = UInt64.ofNat (buf + 32 * cnt + 32) ∧
    LeavesEnv env lay first buf ctx cnt data ∧
    (∀ j < k, nodeAt mm (buf + 32 * j) = (slotRoot b (slots.at (first + j))).data) ∧ Kept mem mm buf span pad

set_option maxHeartbeats 4000000 in
/--
The leaves driver's loop roots each value from the first position on, as node i of the buffer, or writes the zero
node at a gap.

The slot reader finds each value, and what a call rooting it does is the hypothesis.
-/
theorem leaves_loop {m : Module} {w : World} (linked : HasCodec m)
    (hs : m.fns.lookup "ssz_prove_slot" = some ProveSlot.fn) {sp n : Nat} (room : w.stackLo + slotRoom n ≤ sp)
    {mem : Memory} {lay data lo hi top first cnt buf ctx span pad : Nat} {b : ByteArray} {slots : Slots}
    (held : Held w mem lay b n lo hi top slots) (fixedPart : w.access lay 144 = true) (base : lay + 144 ≤ top)
    (encoding : readLE mem (lay + 72) 8 = UInt64.ofNat data) (dataSmall : data < 2 ^ 64)
    (short : 0 < cnt → first + cnt < 2 ^ 63) (bufAcc : w.access buf span = true) (wide : 32 * cnt + 64 ≤ span)
    (away : ∀ a, (buf ≤ a ∧ a < buf + span) ∨ (pad ≤ a ∧ a < pad + 1536) → ¬ Footprint lay top lo hi data b.size a)
    (padAway : buf + span ≤ pad ∨ pad + 1536 ≤ buf)
    (roots : RootCalls m w sp mem b slots data first cnt buf span pad ctx lo hi)
    {env : Env} (ev : LeavesEnv env lay first buf ctx cnt data) :
    Wp m w sp (.block leavesLoop) env mem (fun env' mem' => env' 5 = UInt64.ofNat cnt ∧
      (∀ i < cnt, nodeAt mem' (buf + 32 * i) = (slotRoot b (slots.at (first + i))).data) ∧
      Kept mem mem' buf span pad) := by
  have bb := BranchProof.access_bound bufAcc
  have ⟨e0, e1, e3, e4, e5, e7⟩ := ev
  -- Memory changed only in the buffer and the pad keeps the record, the plan, and the encoding.
  have keepFoot : ∀ mm : Memory, Kept mem mm buf span pad → ∀ a, Footprint lay top lo hi data b.size a →
      mm a = mem a := fun mm k a foot => k a (fun h => away a (.inl h) foot) (fun h => away a (.inr h) foot)
  refine Wp.set (by wev [e3, e5]) (Wp.set (by wev []) (Wp.loop ?_))
  refine wp_loop (LoopInv mem b slots lay first buf ctx cnt data span pad) (fun env _ => cnt - (env 14).toNat)
    ⟨0, Nat.zero_le _, by wev [], by wev [e3, e5], (ev.write _ (by decide)).write _ (by decide),
      fun j hj => absurd hj (by omega), fun _ _ _ => rfl⟩ ?_
  rintro env mm ⟨k, hk, h14, h15, ev', nodes, kept⟩
  have ⟨f0, f1, f3, f4, f5, f7⟩ := ev'
  refine ⟨_, by wev [h14, f5], fun go => ?_, fun stop => ?_⟩
  rotate_left
  · -- Every position is rooted.
    have done : k = cnt := by
      rcases Nat.lt_or_ge k cnt with h | h
      · simp [h] at stop
      · omega
    subst done
    exact Wp.done ⟨f5, nodes, kept⟩
  have more : k < cnt := by
    rcases Nat.lt_or_ge k cnt with h | h
    · exact h
    · simp [show ¬ k < cnt by omega] at go
  -- The slot reader finds the value at the position, from the record memory still holds.
  have heldMM : Held w mm lay b n lo hi top slots :=
    held.keep base encoding dataSmall fun a h => keepFoot mm kept a (by simp only [RecordFoot] at h; simp only [Footprint]; omega)
  have inBuf : ∀ k j, k + j ≤ span → w.access (buf + k) j = true := fun k j h => BranchProof.access_sub bufAcc h
  have slAcc : w.access (buf + 32 * cnt + 32) 24 = true := by rw [Nat.add_assoc]; exact inBuf _ _ (by omega)
  have slot := slot_calls linked hs room heldMM fixedPart (first + k) (buf + 32 * cnt + 32)
    (by have := short (by omega); omega) slAcc
  have nodeAcc : w.access (buf + 32 * k) 32 = true := inBuf _ _ (by omega)
  -- Past the node just written, nothing the invariant reads changed.
  have step : ∀ mm' : Memory, Kept mem mm' buf span pad →
      (∀ j < k, ∀ x < 32, mm' (buf + 32 * j + x) = mm (buf + 32 * j + x)) →
      nodeAt mm' (buf + 32 * k) = (slotRoot b (slots.at (first + k))).data →
      ∀ env', env' 14 = UInt64.ofNat (k + 1) → env' 15 = UInt64.ofNat (buf + 32 * cnt + 32) →
        LeavesEnv env' lay first buf ctx cnt data →
        LoopInv mem b slots lay first buf ctx cnt data span pad env' mm' ∧
          cnt - (env' 14).toNat < cnt - (env 14).toNat := by
    intro mm' kept' same here env' g14 g15 ev''
    refine ⟨⟨k + 1, more, g14, g15, ev'', fun j hj => ?_, kept'⟩, ?_⟩
    · rcases Nat.lt_or_ge j k with lt | ge
      · rw [← nodes j lt]
        exact nodeAt_congr fun x hx => same j lt x hx
      · rw [show j = k by omega]; exact here
    · rw [g14, h14, Validate.toNat_ofNat_lt (by omega), Validate.toNat_ofNat_lt (by omega)]
      omega
  cases hsl : slots.at (first + k) with
  | some x =>
    cases x with
    | some v =>
      obtain ⟨d, s, e⟩ := v
      rw [hsl] at slot
      obtain ⟨q, planned, qlo, qhi, call⟩ := slot
      refine Wp.call (values := [UInt64.ofNat lay, UInt64.ofNat (first + k), UInt64.ofNat (buf + 32 * cnt + 32)])
        (by wev [f0, f1, h14, h15]) call ?_
      refine Wp.ifElse_t (by wev []) (by decide) ?_
      simp only [List.cons_append, List.nil_append]
      -- The value's plan node and range, read back from where the slot reader wrote them.
      generalize hm1 : written3 mm (buf + 32 * cnt + 32) (UInt64.ofNat q) (UInt64.ofNat s) (UInt64.ofNat e) = mm1
      have ⟨r0, r8, r16, out1⟩ := record_words mm (buf + 32 * cnt + 32) (buf + 32 * cnt + 32 + 8)
        (buf + 32 * cnt + 32 + 16) (UInt64.ofNat q) (UInt64.ofNat s) (UInt64.ofNat e) rfl rfl mm1 hm1.symm
      have a0 : w.access (buf + 32 * cnt + 32) 8 = true := BranchProof.access_prefix slAcc (by omega)
      have a8 : w.access (buf + 32 * cnt + 32 + 8) 8 = true := BranchProof.access_sub slAcc (by omega)
      have a16 : w.access (buf + 32 * cnt + 32 + 16) 8 = true := BranchProof.access_sub slAcc (by omega)
      have kept1 : Kept mem mm1 buf span pad := fun a h1 h2 => by
        rw [out1 a (by omega)]; exact kept a h1 h2
      have planned1 : PlanAt w mm1 q (words d) := PlanAt.keep planned ⟨qlo, qhi⟩ fun a h1 h2 =>
        (keepFoot mm1 kept1 a (.inr (.inl ⟨h1, h2⟩))).trans (keepFoot mm kept a (.inr (.inl ⟨h1, h2⟩))).symm
      obtain ⟨mm2, rcall, root, out2⟩ := roots mm1 k d s e q kept1 more hsl planned1 qlo qhi
      refine Wp.call (values := [UInt64.ofNat q, UInt64.ofNat data + UInt64.ofNat s, UInt64.ofNat e - UInt64.ofNat s,
        UInt64.ofNat (buf + 32 * k), UInt64.ofNat (buf + 32 * cnt + 64), UInt64.ofNat ctx])
        (by wev [assign_ne, f3, f4, f7, h14, h15, r0, r8, r16, a0, a8, a16]) rcall ?_
      refine Wp.set (by wev [h14]) (Wp.done (step mm2 (fun a h1 h2 => ?_) (fun j hj x hx => ?_) ?_ _
        (by wev [h14]) (by wev [h15])
        (((ev'.write (x := 13) _ (by decide)).write (x := 13) _ (by decide)).write (x := 14) _ (by decide))))
      · rw [out2 a (by omega) (by omega) h2, kept1 a h1 h2]
      · rw [out2 _ (by omega) (by omega) (by omega), out1 _ (by omega)]
      · rw [root, hsl]; rfl
    | none =>
      rw [hsl] at slot
      refine Wp.call (values := [UInt64.ofNat lay, UInt64.ofNat (first + k), UInt64.ofNat (buf + 32 * cnt + 32)])
        (by wev [f0, f1, h14, h15]) slot ?_
      refine Wp.ifElse_f (by wev []) ((Wp.block_append _ _ _ _).mpr ⟨_, _, zero32_at (a := buf + 32 * k)
        (fun _ => by wev [assign_ne, f3, h14]) nodeAcc, ?_⟩)
      refine Wp.set (by wev [h14]) (Wp.done (step _ (fun a h1 h2 => ?_) (fun j hj x hx => ?_) ?_ _
        (by wev [h14]) (by wev [h15]) ((ev'.write (x := 13) _ (by decide)).write (x := 14) _ (by decide))))
      · rw [zeroed, store_out (by omega), kept a h1 h2]
      · rw [zeroed, store_out (by omega)]
      · rw [hsl, nodeAt_zeroed]; rfl
  | none =>
    rw [hsl] at slot
    refine Wp.call (values := [UInt64.ofNat lay, UInt64.ofNat (first + k), UInt64.ofNat (buf + 32 * cnt + 32)])
      (by wev [f0, f1, h14, h15]) slot ?_
    refine Wp.ifElse_f (by wev []) ((Wp.block_append _ _ _ _).mpr ⟨_, _, zero32_at (a := buf + 32 * k)
      (fun _ => by wev [assign_ne, f3, h14]) nodeAcc, ?_⟩)
    refine Wp.set (by wev [h14]) (Wp.done (step _ (fun a h1 h2 => ?_) (fun j hj x hx => ?_) ?_ _
      (by wev [h14]) (by wev [h15]) ((ev'.write (x := 13) _ (by decide)).write (x := 14) _ (by decide))))
    · rw [zeroed, store_out (by omega), kept a h1 h2]
    · rw [zeroed, store_out (by omega)]
    · rw [hsl, nodeAt_zeroed]; rfl

/-! ### Packed leaves -/

/-- The byte the driver writes back over a bit list's delimiter, in a word, is the byte with the delimiter cleared. -/
theorem clear_table : ∀ x : Fin 256, ∀ k : Fin 8,
    qwordByte (UInt64.ofNat x.val &&& (255 ^^^ UInt64.ofNat (2 ^ k.val))) 0 =
      UInt8.ofNat x.val &&& ~~~((1 : UInt8) <<< UInt8.ofNat k.val) := by
  decide +kernel

/-- A byte read as a word, its delimiter cleared and stored back, is the byte with the delimiter cleared. -/
theorem clear_byte (x : UInt8) {k : Nat} (hk : k < 8) :
    qwordByte (UInt64.ofNat x.toNat &&& (255 ^^^ UInt64.ofNat (2 ^ k))) 0 = clearCut (some k) x := by
  have := clear_table ⟨x.toNat, x.toNat_lt⟩ ⟨k, hk⟩
  simp only at this
  rw [this, clearCut, UInt8.ofNat_toNat]

/-- One record gathered with no skip: its bytes, then zeros. -/
theorem gathered_one (mem : Memory) {out src width pad x : Nat} (hx : out ≤ x ∧ x < out + (width + pad)) :
    gathered mem out src 1 width 0 pad x = if x - out < width then mem (src + (x - out)) else 0 := by
  simp only [gathered, Nat.mul_one, if_pos hx, Kernel.recordByte, Nat.add_zero]
  rw [Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mul_zero, Nat.add_zero]

/-- The leaves driver's statements for packed leaves. -/
abbrev leavesPacked : List Stmt :=
  [ProveLeaves.a ::= ld (ProveLeaves.lay + 80), ProveLeaves.n ::= ld (ProveLeaves.lay + 88) - ProveLeaves.a,
    ProveLeaves.lo ::= 0, ProveLeaves.bytes ::= 0,
    when ProveLeaves.cnt [ProveLeaves.lo ::= 32 * ProveLeaves.first,
      ProveLeaves.hi ::= 32 * (ProveLeaves.first + ProveLeaves.cnt),
      when (lt ProveLeaves.n ProveLeaves.hi) [ProveLeaves.hi ::= ProveLeaves.n],
      when (lt ProveLeaves.lo ProveLeaves.hi) [ProveLeaves.bytes ::= ProveLeaves.hi - ProveLeaves.lo]],
    callInto ProveLeaves.sink "ssz_gather" [ProveLeaves.buf, ProveLeaves.data + ProveLeaves.a + ProveLeaves.lo, 1,
      ProveLeaves.bytes, 0, 32 * ProveLeaves.cnt + 32 - ProveLeaves.bytes],
    when (ld (ProveLeaves.lay + 104) &&& ne ProveLeaves.bytes 0 &&& eq (ProveLeaves.lo + ProveLeaves.bytes) ProveLeaves.n)
      [st1 (ProveLeaves.buf + ProveLeaves.bytes - 1)
        (ld1 (ProveLeaves.buf + ProveLeaves.bytes - 1) &&& (255 ^^^ ld (ProveLeaves.lay + 112)))]]

set_option maxHeartbeats 4000000 in
/--
The leaves driver's statements for packed leaves gather the bytes of the leaves asked for, zero past the range, and
clear a bit list's delimiter where its byte is gathered.

Memory changes only in the buffer.
-/
theorem leaves_packed {m : Module} {w : World} (gmod : GatherModule m) {sp : Nat} (room : w.stackLo + 8 ≤ sp)
    {mem : Memory} {lay data a e first cnt L buf ctx span : Nat} {cut : Option Nat} {b : ByteArray}
    (fixedPart : w.access lay 144 = true) (start : readLE mem (lay + 80) 8 = UInt64.ofNat a)
    (stop : readLE mem (lay + 88) 8 = UInt64.ofNat e) (flag : readLE mem (lay + 104) 8 = if cut.isSome then 1 else 0)
    (bit : ∀ k, cut = some k → readLE mem (lay + 112) 8 = UInt64.ofNat (2 ^ k))
    (cutSmall : ∀ k, cut = some k → k < 8 ∧ a < e) (ordered : a ≤ e) (inside : e ≤ b.size)
    (bytes : BytesAt mem data b) (readable : w.access data b.size = true) (small : 64 * b.size + 128 < 2 ^ 64)
    (usize : USize.size = 2 ^ 64) (within : L ≤ nodesFor (e - a)) (counted : cnt = L - first)
    (bufAcc : w.access buf span = true) (wide : 32 * cnt + 32 ≤ span)
    (dataApart : buf + span ≤ data ∨ data + b.size ≤ buf) (recApart : buf + span ≤ lay ∨ lay + 144 ≤ buf)
    {env : Env} (ev : LeavesEnv env lay first buf ctx cnt data) :
    Wp m w sp (.block leavesPacked) env mem (fun env' mem' => env' 5 = UInt64.ofNat cnt ∧
      bytesAt mem' buf (32 * cnt) = (packedNodes b a e cut).extract (32 * min first L) (32 * L) ∧
      ∀ x, ¬ (buf ≤ x ∧ x < buf + span) → mem' x = mem x) := by
  have bb := BranchProof.access_bound bufAcc
  have db := BranchProof.access_bound readable
  have lb := BranchProof.access_bound fixedPart
  have ⟨e0, e1, e3, e4, e5, e7⟩ := ev
  have acc : ∀ k, k + 8 ≤ 144 → w.access (lay + k) 8 = true := fun k hk => BranchProof.access_sub fixedPart (by omega)
  have nodesLe : nodesFor (e - a) ≤ b.size := by simp only [nodesFor]; omega
  -- The bytes copied and where they start: none for no leaves, else the leaves' bytes inside the range.
  let lo' := if cnt = 0 then 0 else 32 * first
  let bytes' := if cnt = 0 then 0 else min (e - a) (32 * (first + cnt)) - 32 * first
  suffices rest : ∀ env', LeavesEnv env' lay first buf ctx cnt data → env' 8 = UInt64.ofNat a →
      env' 9 = UInt64.ofNat (e - a) → env' 10 = UInt64.ofNat lo' → env' 12 = UInt64.ofNat bytes' →
      Wp m w sp (.block (leavesPacked.drop 5)) env' mem (fun env' mem' => env' 5 = UInt64.ofNat cnt ∧
        bytesAt mem' buf (32 * cnt) = (packedNodes b a e cut).extract (32 * min first L) (32 * L) ∧
        ∀ x, ¬ (buf ≤ x ∧ x < buf + span) → mem' x = mem x) by
    refine Wp.set (by wev [e0, start, acc]) (Wp.set (by wev [e0, stop, acc]) (Wp.set (by wev [])
      (Wp.set (by wev []) ?_)))
    have nf : nodesFor (e - a) = (e - a + 31) / 32 := rfl
    by_cases z : cnt = 0
    · refine Wp.when_f (by wev [e5, z]) (rest _ ((((ev.write (x := 8) _ (by decide)).write (x := 9) _ (by decide)).write
        (x := 10) _ (by decide)).write (x := 12) _ (by decide)) (by wev []) (by wev []) (by wev [lo', z])
        (by wev [bytes', z]))
    · have cntNe : UInt64.ofNat cnt ≠ 0 := fun h => z (by
        have := congrArg UInt64.toNat h
        rw [Validate.toNat_ofNat_lt (by omega)] at this
        simpa using this)
      refine Wp.when_t (by wev [e5]) cntNe ?_
      refine Wp.set (by wev [e1]) (Wp.set (by wev [e1, e5]) ?_)
      by_cases hn : e - a < 32 * (first + cnt)
      · refine Wp.when_t (by wev [hn]) (by wonly [hn]) (Wp.set (by wev []) ?_)
        refine Wp.when_t (by wev [show 32 * first < e - a by omega]) (by wonly [show 32 * first < e - a by omega])
          (Wp.set (by wev []) ?_)
        exact rest _ ((((((ev.write (x := 8) _ (by decide)).write (x := 9) _ (by decide)).write (x := 10) _
          (by decide)).write (x := 12) _ (by decide)).write (x := 10) _ (by decide)).write (x := 11) _ (by decide)
          |>.write (x := 11) _ (by decide) |>.write (x := 12) _ (by decide)) (by wev []) (by wev [])
          (by wev [lo', z]) (by wonly [bytes', z]; omega)
      · refine Wp.when_f (by wev [hn]) ?_
        refine Wp.when_t (by wev [show 32 * first < 32 * (first + cnt) by omega])
          (by wonly [show 32 * first < 32 * (first + cnt) by omega]) (Wp.set (by wev []) ?_)
        exact rest _ (((((ev.write (x := 8) _ (by decide)).write (x := 9) _ (by decide)).write (x := 10) _
          (by decide)).write (x := 12) _ (by decide)).write (x := 10) _ (by decide) |>.write (x := 11) _ (by decide)
          |>.write (x := 12) _ (by decide)) (by wev []) (by wev [])
          (by wev [lo', z]) (by wonly [bytes', z]; omega)
  intro env' ev' h8 h9 h10 h12
  have ⟨g0, g1, g3, g4, g5, g7⟩ := ev'
  have nf : nodesFor (e - a) = (e - a + 31) / 32 := rfl
  -- What the copied bytes are: inside the range, and exactly the leaves' bytes that lie in it.
  have bytesLe : bytes' ≤ 32 * cnt := by simp only [bytes']; split <;> omega
  have endLe : lo' + bytes' ≤ e - a := by simp only [lo', bytes']; split <;> omega
  have copied : ∀ j < 32 * cnt, (j < bytes' ↔ 32 * first + j < e - a) := fun j hj => by
    simp only [bytes']; split <;> omega
  have loIs : cnt ≠ 0 → lo' = 32 * first := fun h => by simp only [lo', h, if_false]
  have bytesIs : cnt ≠ 0 → bytes' = min (e - a) (32 * (first + cnt)) - 32 * first := fun h => by
    simp only [bytes', h, if_false]
  have pad : bytes' + (32 * cnt + 32 - bytes') = 32 * cnt + 32 := by omega
  have pre : GatherPre w buf (data + a + lo') 1 bytes' 0 (32 * cnt + 32 - bytes') :=
    ⟨by rw [pad, Nat.mul_one]; exact BranchProof.access_prefix bufAcc (by omega),
      fun i hi => by
        obtain rfl : i = 0 := by omega
        rw [Nat.mul_zero, Nat.add_zero, Nat.add_assoc]
        exact BranchProof.access_sub readable (by omega),
      by simp only [addressBound]; omega,
      fun i hi => by
        obtain rfl : i = 0 := by omega
        simp only [Apart]; rw [pad]; omega⟩
  have call := gather_call (m := m) (w := w) (sp := sp) (mem := mem) (out := UInt64.ofNat buf)
    (src := UInt64.ofNat (data + a + lo')) (count := 1) (width := UInt64.ofNat bytes') (skip := 0)
    (pad := UInt64.ofNat (32 * cnt + 32 - bytes')) gmod.general (Kernel.runs_gather w.cpu) (by simp)
    (by rw [ofNat_toNat (by omega), ofNat_toNat (by omega), ofNat_toNat (by omega), ofNat_toNat (by omega)]; exact pre)
    room
  rw [ofNat_toNat (by omega), ofNat_toNat (by omega), ofNat_toNat (by omega), ofNat_toNat (by omega)] at call
  simp only [UInt64.toNat_one, UInt64.toNat_zero] at call
  refine Wp.call (values := [UInt64.ofNat buf, UInt64.ofNat (data + a + lo'), 1, UInt64.ofNat bytes', 0,
    UInt64.ofNat (32 * cnt + 32 - bytes')]) (by wev [g3, g7, h8, h10, h12, g5]) call ?_
  generalize hm1 : gathered mem buf (data + a + lo') 1 bytes' 0 (32 * cnt + 32 - bytes') = mem1
  -- The gathered bytes: the range's bytes, then zeros; the record is as it was.
  have inGather : ∀ j < 32 * cnt + 32, mem1 (buf + j) = if j < bytes' then b.get! (a + lo' + j) else 0 := by
    intro j hj
    rw [← hm1, gathered_one mem ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
    split
    · rw [show data + a + lo' + j = data + (a + lo' + j) by omega, bytes _ (by omega)]
    · rfl
  have outGather : ∀ x, ¬ (buf ≤ x ∧ x < buf + span) → mem1 x = mem x := fun x hx => by
    rw [← hm1]
    simp only [gathered, Nat.mul_one]
    rw [if_neg (by rw [pad]; omega)]
  have recKeep : ∀ k, k + 8 ≤ 144 → readLE mem1 (lay + k) 8 = readLE mem (lay + k) 8 := fun k hk =>
    readLE_congr _ _ _ 8 fun i hi => outGather _ (by omega)
  -- The bytes the leaves span, read back from the packed range.
  have sizeX : ((packedNodes b a e cut).extract (32 * min first L) (32 * L)).size = 32 * cnt := by
    rw [ByteArray.size_extract, packedNodes_size b cut ordered inside (by rw [usize]; omega)]
    omega
  have getX : ∀ j < 32 * cnt, ((packedNodes b a e cut).extract (32 * min first L) (32 * L)).get! j =
      (packedNodes b a e cut).get! (32 * first + j) := fun j hj => by
    have size := packedNodes_size b cut ordered inside (by rw [usize]; omega)
    rw [Kernel.get!_eq _ _ (by omega), Kernel.get!_eq _ _ (by omega), ByteArray.getElem_extract]
    congr 1
    omega
  have finish : ∀ mem2 : Memory, (∀ x, ¬ (buf ≤ x ∧ x < buf + span) → mem2 x = mem x) →
      (∀ j < 32 * cnt, mem2 (buf + j) = (packedNodes b a e cut).get! (32 * first + j)) →
      (Asm.assign env' 13 0) 5 = UInt64.ofNat cnt ∧
        bytesAt mem2 buf (32 * cnt) = (packedNodes b a e cut).extract (32 * min first L) (32 * L) ∧
        ∀ x, ¬ (buf ≤ x ∧ x < buf + span) → mem2 x = mem x := fun mem2 out2 in2 =>
    ⟨by rw [assign_ne (by decide)]; exact g5,
      bytesAt_of_holds sizeX fun j hj => by rw [sizeX] at hj; rw [getX j hj]; exact in2 j hj, out2⟩
  have packedAt : ∀ j < 32 * cnt, (packedNodes b a e cut).get! (32 * first + j) =
      if 32 * first + j + 1 = e - a then clearCut cut (packByte b a e (32 * first + j))
      else packByte b a e (32 * first + j) := fun j hj =>
    packedNodes_get b cut ordered inside (by rw [usize]; omega) (by omega) fun k hk => (cutSmall k hk).2
  have gatherIs : ∀ j < 32 * cnt, mem1 (buf + j) = packByte b a e (32 * first + j) := fun j hj => by
    have z : cnt ≠ 0 := by omega
    rw [inGather j (by omega), packByte, loIs z]
    by_cases inside' : j < bytes'
    · rw [if_pos inside', if_pos ((copied j hj).mp inside')]
      congr 1
      omega
    · rw [if_neg inside', if_neg (fun h => inside' ((copied j hj).mpr h))]
  have f104 := (recKeep 104 (by omega)).trans flag
  cases cut with
  | none =>
    -- No delimiter: the gathered bytes are the leaves.
    refine Wp.when_f (by wev [f104, g0, acc]) (Wp.done (finish mem1 outGather fun j hj => ?_))
    rw [packedAt j hj, gatherIs j hj]
    simp only [clearCut, ite_self]
  | some k =>
    have ⟨k8, _⟩ := cutSmall k rfl
    have f112 := (recKeep 112 (by omega)).trans (bit k rfl)
    by_cases last : bytes' ≠ 0 ∧ lo' + bytes' = e - a
    · -- The delimiter's byte was gathered: its bit is cleared.
      have z : cnt ≠ 0 := by intro h; simp only [bytes', h, if_true] at last; omega
      have lastAcc : w.access (buf + bytes' - 1) 1 = true := by
        rw [show buf + bytes' - 1 = buf + (bytes' - 1) by omega]; exact BranchProof.access_sub bufAcc (by omega)
      refine Wp.when_t (by wev [f104, g0, acc, h10, h12, h9, last.1, last.2]) (by simp) ?_
      have v112 : eval w (Asm.assign env' 13 0) mem1 (255 ^^^ ld (Expr.var 0 + 112)) =
          some (255 ^^^ UInt64.ofNat (2 ^ k)) := BranchProof.eval_xor rfl (by wev [g0, acc, f112])
      refine Wp.store (x := UInt64.ofNat (buf + bytes' - 1))
        (y := UInt64.ofNat (mem1 (buf + bytes' - 1)).toNat &&& (255 ^^^ UInt64.ofNat (2 ^ k)))
        (by wev [g3, h12]) (by wonly [g3, h12, lastAcc, read1, v112]) (by wonly [lastAcc])
        (Wp.done (finish _ (fun x hx => ?_) fun j hj => ?_))
      · simp only [Width.bytes]
        rw [store_out (by rw [ofNat_toNat (by omega)]; omega), outGather x hx]
      · simp only [Width.bytes]
        rw [ofNat_toNat (by omega), packedAt j hj, ← gatherIs j hj]
        by_cases at_ : j = bytes' - 1
        · subst at_
          rw [store_in (by omega), if_pos (by rw [loIs z] at last; omega),
            show buf + (bytes' - 1) - (buf + bytes' - 1) = 0 by omega, show buf + (bytes' - 1) = buf + bytes' - 1 by omega,
            clear_byte _ k8]
        · rw [store_out (by omega), if_neg (by rw [loIs z] at last; omega)]
    · -- The delimiter's byte lies past the leaves, or there are none.
      refine Wp.when_f (by
        wonly [f104, g0, acc, h10, h12, h9]
        by_cases h1 : lo' + bytes' = e - a
        · rw [if_pos h1, if_pos (Classical.byContradiction fun h => last ⟨h, h1⟩)]
        · rw [if_neg h1]) (Wp.done (finish mem1 outGather fun j hj => ?_))
      have z : cnt ≠ 0 := by omega
      rw [packedAt j hj, ← gatherIs j hj, if_neg]
      intro h
      exact last ⟨by have := (copied j hj).mpr (by omega); omega, by rw [loIs z, bytesIs z]; omega⟩

/-! ### No values -/

/-- Columns of no nodes pair into columns of no nodes. -/
theorem pairUp_empty (count height : Nat) (zero : count = 0) :
    ∀ cols : List ByteArray, (∀ c ∈ cols, c.size = 0) →
      ∀ c ∈ columnTree.pairUp count height cols, c.size = 0
  | a :: b :: rest, h => by
    intro c hc
    simp only [columnTree.pairUp, List.mem_cons] at hc
    rcases hc with rfl | hc
    · simp [hashColumns, hashColumnsReference_size, zero]
    · exact pairUp_empty count height zero rest (fun c m => h c (by simp [m])) c hc
  | [a], _ => by
    intro c hc
    simp only [columnTree.pairUp, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc
    simp [hashFixed, hashFixedReference_size, zero]
  | [], _ => by intro c hc; simp [columnTree.pairUp] at hc

/-- A tree over columns of no nodes is a column of no nodes. -/
theorem columnTree_empty (count : Nat) (zero : count = 0) :
    ∀ fuel height (cols : List ByteArray), (∀ c ∈ cols, c.size = 0) → (columnTree cols count height fuel).size = 0
  | 0, height, cols, h => by
    rw [columnTree]
    cases cols with
    | nil => rfl
    | cons c _ => exact h c (by simp)
  | fuel + 1, height, cols, h => by
    match cols with
    | [] => rw [columnTree]; rfl
    | [c] => rw [columnTree]; exact h c (by simp)
    | a :: b :: rest =>
      rw [columnTree]
      all_goals first | exact columnTree_empty count zero fuel _ _ (pairUp_empty count height zero _ h) | simp

/-- A column of no nodes stays empty as it climbs. -/
theorem climbColumn_empty (count : Nat) (zero : count = 0) :
    ∀ levels height (col : ByteArray), col.size = 0 → (climbColumn col count height levels).size = 0
  | 0, _, _, h => h
  | levels + 1, height, col, _ => by
    rw [climbColumn]
    exact climbColumn_empty count zero levels _ _ (by simp [hashFixed, hashFixedReference_size, zero])

/-- Packed roots of no values are empty. -/
theorem packedRoots_empty (width nodes : Nat) (b : ByteArray) (start stride : Nat) :
    (packedRoots width nodes b start stride 0).size = 0 := by
  simp only [packedRoots]
  generalize depthFor nodes = depth
  have g : (gather b start.toUSize stride.toUSize width.toUSize (0 : Nat).toUSize (32 * 2 ^ depth).toUSize).size = 0 := by
    simp [gather, gatherReference_size]
  generalize gather b start.toUSize stride.toUSize width.toUSize (0 : Nat).toUSize (32 * 2 ^ depth).toUSize = L at g
  induction depth with
  | zero => simpa using g
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hashPairs, hashPairsReference_size, ih]
    rfl

mutual

/-- The roots of no values are empty. -/
theorem rootsOf_empty (d : Desc) (b : ByteArray) (start stride : Nat) : (rootsOf d b start stride 0).size = 0 := by
  match d with
  | .vector element length =>
    rw [rootsOf]
    split
    · exact packedRoots_empty _ _ _ _ _
    · simp only [beq_iff_eq, Nat.zero_ne_one, if_false]
      refine climbColumn_empty 0 rfl _ _ _ (columnTree_empty 0 rfl _ _ _ fun c m => ?_)
      simp only [elementColumns, List.mem_map, List.mem_range] at m
      obtain ⟨i, _, rfl⟩ := m
      exact rootsOf_empty element b _ stride
  | .container _ fields =>
    rw [rootsOf]
    simp only [beq_iff_eq, Nat.zero_ne_one, if_false]
    exact climbColumn_empty 0 rfl _ _ _ (columnTree_empty 0 rfl _ _ _ (fieldColumns_empty fields b start stride 0))
  | .bool | .uint _ | .byteVector _ | .bitVector _ | .byteList _ | .bitList _ | .progressiveBitList _
  | .list _ _ | .progressiveList _ _ | .progressiveContainer _ _ _ | .compatibleUnion _ _ =>
    rw [rootsOf] <;> first | exact packedRoots_empty _ _ _ _ _ | simp_all

/-- Each field's column of no records is empty. -/
theorem fieldColumns_empty (fields : List Desc) (b : ByteArray) (start stride offset : Nat) :
    ∀ c ∈ fieldColumns fields b start stride 0 offset, c.size = 0 := by
  match fields with
  | [] => intro c hc; simp [fieldColumns] at hc
  | f :: rest =>
    intro c hc
    rw [fieldColumns] at hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact rootsOf_empty f b _ stride
    · exact fieldColumns_empty rest b start stride _ c hc

end

/-- The chunked roots of no values are empty. -/
theorem chunkedRoots_empty (d : Desc) (b : ByteArray) (start stride : Nat) :
    chunkedRoots d b start stride 0 = ByteArray.empty := by
  rw [chunkedRoots, if_pos (Nat.zero_le _)]
  apply ByteArray.ext
  exact Array.eq_empty_of_size_eq_zero (rootsOf_empty d b start stride)

/-! ### The driver -/

/-- Values one width apart are held under kind one, with their plan node, start, and width in the record. -/
theorem Held.stride_facts {w : World} {mem : Memory} {lay n lo hi top : Nat} {b : ByteArray} {e : Desc}
    {s wd c : Nat} (h : Held w mem lay b n lo hi top (.stride e s wd c)) :
    readLE mem lay 8 = 1 ∧ ∃ q, readLE mem (lay + 96) 8 = UInt64.ofNat q ∧ readLE mem (lay + 80) 8 = UInt64.ofNat s ∧
      readLE mem (lay + 104) 8 = UInt64.ofNat wd ∧ PlanAt w mem q (words e) ∧ lo ≤ q ∧
      q + 8 * (words e).length ≤ hi := by
  cases h with
  | stride _ _ _ _ q kind _ first plan wide planned inPlan _ =>
    exact ⟨kind, q, plan, first, wide, planned, inPlan.1, inPlan.2⟩

/-- Listed values are held under a kind past one. -/
theorem Held.listed_kind {w : World} {mem : Memory} {lay n lo hi top : Nat} {b : ByteArray}
    {l : List (Option (Desc × Nat × Nat))} (h : Held w mem lay b n lo hi top (.listed l)) :
    readLE mem lay 8 ≠ 0 ∧ readLE mem lay 8 ≠ 1 := by
  cases h with
  | struct _ _ _ kind => rw [kind]; decide
  | progressive _ _ _ _ _ kind => rw [kind]; decide
  | union _ _ _ _ kind => rw [kind]; decide
  | offsets _ _ _ _ _ _ kind => rw [kind]; decide

/-- The leaves driver's statements once the last leaf is cut to the count. -/
abbrev leavesRest : List Stmt :=
  [ProveLeaves.cnt ::= 0, when (lt ProveLeaves.first ProveLeaves.last) [ProveLeaves.cnt ::= ProveLeaves.last - ProveLeaves.first],
    ProveLeaves.kind ::= ld ProveLeaves.lay, ProveLeaves.data ::= ld (ProveLeaves.lay + 72),
    ifElse (eq ProveLeaves.kind 0) leavesPacked
      [ifElse (eq ProveLeaves.kind 1 &&& ld (ProveLeaves.lay + 112))
        [when ProveLeaves.cnt [callInto ProveLeaves.sink "ssz_roots_chunked"
          [ld (ProveLeaves.lay + 96),
            ProveLeaves.data + ld (ProveLeaves.lay + 80) + ld (ProveLeaves.lay + 104) * ProveLeaves.first,
            ld (ProveLeaves.lay + 104), ProveLeaves.cnt, ProveLeaves.buf, ProveLeaves.ctx]]]
        leavesLoop]]

/--
What the call rooting plain values one width apart together does: from the memory the driver starts with, it writes
their roots at the buffer and changes nothing else but the buffer and the padding area.
The call is made only for at least one value.
-/
def ChunkCalls (m : Module) (w : World) (sp : Nat) (mem : Memory) (b : ByteArray) (slots : Slots)
    (data first cnt buf span pad ctx lo hi : Nat) : Prop :=
  ∀ element start width count q, 0 < cnt → slots = .stride element start width count → plain element = true →
    PlanAt w mem q (words element) → lo ≤ q → q + 8 * (words element).length ≤ hi →
    ∃ mem', Calls m w "ssz_roots_chunked" sp [UInt64.ofNat q,
        UInt64.ofNat data + UInt64.ofNat start + UInt64.ofNat width * UInt64.ofNat first, UInt64.ofNat width,
        UInt64.ofNat cnt, UInt64.ofNat buf, UInt64.ofNat ctx] mem 0 mem' ∧
      bytesAt mem' buf (32 * cnt) = chunkedRoots element b (start + width * first) width cnt ∧
      Kept mem mem' buf span pad

set_option maxHeartbeats 4000000 in
/--
A call of the leaves driver writes the Lean leaves of a layout from one position to another at the buffer, and
answers how many there are.

The record holds the layout, and memory holds the type's plan and the encoding, apart from the buffer and the padding
area.
What the calls rooting values do is a hypothesis, as the two contracts above.
Values are rooted one at a time only when they are not plain values one width apart.
Memory changes only in the buffer and the padding area.
-/
theorem leaves_calls {m : Module} {w : World} (linked : HasCodec m) (gmod : GatherModule m)
    (hf : m.fns.lookup "ssz_prove_leaves" = some ProveLeaves.fn)
    (hs : m.fns.lookup "ssz_prove_slot" = some ProveSlot.fn) {sp n : Nat}
    (room : w.stackLo + 8 + 8 * ProveLeaves.fn.frame + slotRoom n ≤ sp)
    {mem : Memory} {lay data lo hi top : Nat} {b : ByteArray} {layout : EncodedLayout}
    (counted : readLE mem (lay + 8) 8 = UInt64.ofNat layout.count)
    (encoding : readLE mem (lay + 72) 8 = UInt64.ofNat data)
    (leaves : LeavesAt w mem lay b n lo hi top layout.leaves)
    (fixedPart : w.access lay 144 = true) (base : lay + 144 ≤ top)
    (bytes : BytesAt mem data b) (readable : w.access data b.size = true) (small : 64 * b.size + 128 < 2 ^ 64)
    (usize : USize.size = 2 ^ 64) (countSmall : layout.count < 2 ^ 62)
    {first last buf ctx span pad : Nat} (firstSmall : first < 2 ^ 64) (lastSmall : last < 2 ^ 64)
    (bufAcc : w.access buf span = true) (wide : 32 * (min last layout.count - first) + 64 ≤ span)
    (away : ∀ a, (buf ≤ a ∧ a < buf + span) ∨ (pad ≤ a ∧ a < pad + 1536) → ¬ Footprint lay top lo hi data b.size a)
    (padAway : buf + span ≤ pad ∨ pad + 1536 ≤ buf) (dataApart : buf + span ≤ data ∨ data + b.size ≤ buf)
    (chunked : ∀ slots, layout.leaves = .nested slots →
      ChunkCalls m w (sp - 8 - 8 * ProveLeaves.fn.frame) mem b slots data first (min last layout.count - first) buf
        span pad ctx lo hi)
    (roots : ∀ slots, layout.leaves = .nested slots →
      (∀ element start width count, slots = .stride element start width count → plain element = false) →
      RootCalls m w (sp - 8 - 8 * ProveLeaves.fn.frame) mem b slots data first (min last layout.count - first) buf
        span pad ctx lo hi) :
    ∃ mem', Calls m w "ssz_prove_leaves" sp [UInt64.ofNat lay, UInt64.ofNat first, UInt64.ofNat last,
        UInt64.ofNat buf, UInt64.ofNat ctx] mem (UInt64.ofNat (leavesIn b layout first last).2) mem' ∧
      bytesAt mem' buf (32 * (leavesIn b layout first last).2) = (leavesIn b layout first last).1 ∧
      Kept mem mem' buf span pad := by
  have bb := BranchProof.access_bound bufAcc
  have db := BranchProof.access_bound readable
  have lb := BranchProof.access_bound fixedPart
  have acc : ∀ k, k + 8 ≤ 144 → w.access (lay + k) 8 = true := fun k hk => BranchProof.access_sub fixedPart (by omega)
  have acc0 : w.access lay 8 = true := BranchProof.access_prefix fixedPart (by omega)
  rw [leavesIn_count]
  generalize hL : min last layout.count = L at wide chunked roots
  generalize hc : L - first = cnt at wide chunked roots
  have recApart : buf + span ≤ lay ∨ lay + 144 ≤ buf := by
    rcases Nat.lt_or_ge buf lay with h | h
    · by_cases h' : buf + span ≤ lay
      · exact .inl h'
      · exact absurd (.inl ⟨by omega, by omega⟩) (away lay (.inl ⟨by omega, by omega⟩))
    · by_cases h' : lay + 144 ≤ buf
      · exact .inr h'
      · exact absurd (.inl ⟨h, by omega⟩) (away buf (.inl ⟨by omega, by omega⟩))
  have dataSmall : data < 2 ^ 64 := by
    rcases dataApart with h | h <;> omega
  have sr : 8 ≤ slotRoom n := by simp only [slotRoom]; omega
  have hcnt : L ≤ layout.count := by omega
  refine calls_of_wp hf (by omega) rfl ?_
  simp only [ProveLeaves.fn]
  -- The last leaf cut to the count, then the count of leaves, the kind, and the encoding.
  suffices cont : ∀ env, env 0 = UInt64.ofNat lay → env 1 = UInt64.ofNat first → env 2 = UInt64.ofNat L →
      env 3 = UInt64.ofNat buf → env 4 = UInt64.ofNat ctx →
      Wp m w (sp - 8 - 8 * ProveLeaves.fn.frame) (.block leavesRest) env mem
        (fun env' mem' => eval w env' mem' (Expr.var 5) = some (UInt64.ofNat cnt) ∧
          bytesAt mem' buf (32 * cnt) = (leavesIn b layout first last).1 ∧ Kept mem mem' buf span pad) by
    by_cases h : layout.count < last
    · refine Wp.when_t (by wev [counted, acc, h]) (by decide) (Wp.set (by wev [counted, acc]) ?_)
      exact cont _ (by wev []) (by wev []) (by wonly []; omega) (by wev []) (by wev [])
    · refine Wp.when_f (by wev [counted, acc, h]) ?_
      exact cont _ (by wev []) (by wev []) (by wonly []; omega) (by wev []) (by wev [])
  intro env e0 e1 e2 e3 e4
  refine Wp.set (by wev []) ?_
  suffices cont2 : ∀ env, LeavesEnv env lay first buf ctx cnt data → env 6 = readLE mem lay 8 →
      Wp m w (sp - 8 - 8 * ProveLeaves.fn.frame) (.block (leavesRest.drop 4)) env mem
        (fun env' mem' => eval w env' mem' (Expr.var 5) = some (UInt64.ofNat cnt) ∧
          bytesAt mem' buf (32 * cnt) = (leavesIn b layout first last).1 ∧ Kept mem mem' buf span pad) by
    have rest : ∀ env, env 0 = UInt64.ofNat lay → env 1 = UInt64.ofNat first → env 3 = UInt64.ofNat buf →
        env 4 = UInt64.ofNat ctx → env 5 = UInt64.ofNat cnt →
        Wp m w (sp - 8 - 8 * ProveLeaves.fn.frame) (.block (leavesRest.drop 2)) env mem
          (fun env' mem' => eval w env' mem' (Expr.var 5) = some (UInt64.ofNat cnt) ∧
            bytesAt mem' buf (32 * cnt) = (leavesIn b layout first last).1 ∧ Kept mem mem' buf span pad) :=
      fun env f0 f1 f3 f4 f5 => Wp.set (by wev [f0, acc0]) (Wp.set (by wev [f0, acc, encoding])
        (cont2 _ ⟨by wev [f0], by wev [f1], by wev [f3], by wev [f4], by wev [f5], by wev []⟩ (by wev [f0, acc0])))
    by_cases h : first < L
    · refine Wp.when_t (by wev [e1, e2, h]) (by decide) (Wp.set (by wev [e1, e2]) ?_)
      exact rest _ (by wev [e0]) (by wev [e1]) (by wev [e3]) (by wev [e4]) (by wonly [e1, e2]; omega)
    · refine Wp.when_f (by wev [e1, e2, h]) ?_
      exact rest _ (by wev [e0]) (by wev [e1]) (by wev [e3]) (by wev [e4]) (by wonly []; omega)
  intro env ev f6
  have ⟨f0, f1, f3, f4, f5, f7⟩ := ev
  obtain ⟨leavesL, limit, mixin⟩ := layout
  simp only [EncodedLayout.count] at counted hL countSmall hcnt
  cases leaves with
  | packed a e cut kind start stop flag bit cutSmall ordered inside =>
    refine Wp.ifElse_t (by wev [f6, kind, acc0]) (by decide) ?_
    simp only [List.append_nil]
    have within : L ≤ nodesFor (e - a) := by simpa using hcnt
    refine Wp.mono (leaves_packed gmod (by omega) fixedPart start stop flag bit cutSmall ordered inside bytes readable
      small usize within hc.symm bufAcc (by omega) dataApart recApart ev) ?_
    rintro env' mem' ⟨r5, nodes, kept⟩
    refine ⟨by wev [r5], ?_, fun a h1 _ => kept a h1⟩
    simp only [leavesIn, EncodedLayout.count] at hL ⊢
    rw [hL]
    exact nodes
  | nested slots held plainFlag =>
    -- Values rooted one at a time, each found by the slot reader.
    have loopCase : (∀ e s wd c, slots = .stride e s wd c → plain e = false) →
        Wp m w (sp - 8 - 8 * ProveLeaves.fn.frame) (.block leavesLoop) env mem
          (fun env' mem' => eval w env' mem' (Expr.var 5) = some (UInt64.ofNat cnt) ∧
            bytesAt mem' buf (32 * cnt) = (leavesIn b ⟨.nested slots, limit, mixin⟩ first last).1 ∧
            Kept mem mem' buf span pad) := fun notChunked => by
      refine Wp.mono (leaves_loop linked hs (by omega) held fixedPart base encoding dataSmall
        (fun pos => by simp only at hcnt; omega) bufAcc wide away padAway (roots slots rfl notChunked) ev) ?_
      rintro env' mem' ⟨r5, nodes, kept⟩
      refine ⟨by wev [r5], ?_, kept⟩
      rw [leavesIn_nested first last rfl notChunked]
      simp only [EncodedLayout.count] at hL ⊢
      rw [hL, hc]
      have len : ((List.range cnt).map fun i => slotRoot b (slots.at (first + i))).length = cnt := by simp
      conv => lhs; rw [← len]
      refine bytesAt_joinNodes (fun r hr => ?_) fun i hi => ?_
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
        have := congrArg Array.size (nodes i (List.mem_range.mp hi))
        simp only [nodeAt, Array.size_ofFn] at this
        rw [← ByteArray.size_data, ← this]
      · simp only [List.getElem_map, List.getElem_range]
        exact nodes i (by simpa using hi)
    cases slots with
    | stride e s wd c =>
      have ⟨kind1, q, plan, start, wide', planned, qlo, qhi⟩ := held.stride_facts
      have flag := plainFlag e s wd c rfl
      refine Wp.ifElse_f (by wev [f6, kind1, acc0]) ?_
      by_cases pl : plain e = true
      · -- Plain values are rooted together.
        rw [if_pos pl] at flag
        refine Wp.ifElse_t (by wev [f0, f6, kind1, acc0, acc, flag]) (by decide) ?_
        by_cases none : cnt = 0
        · -- No values: nothing is called, and no roots are written.
          refine Wp.when_f (by wev [f5, none]) (Wp.done ⟨by wev [f5], ?_, fun _ _ _ => rfl⟩)
          simp only [leavesIn, EncodedLayout.count, pl, if_true] at hL ⊢
          rw [hL, hc, none, chunkedRoots_empty]
          rfl
        refine Wp.when_t (by wev [f5]) (by
          intro z
          have := congrArg UInt64.toNat z
          rw [ofNat_toNat (by simp only at hcnt; omega)] at this
          exact none this) ?_
        obtain ⟨mem', call, nodes, kept⟩ := chunked _ rfl e s wd c q (by omega) rfl pl planned qlo qhi
        refine Wp.call (values := [UInt64.ofNat q, UInt64.ofNat data + UInt64.ofNat s + UInt64.ofNat wd *
          UInt64.ofNat first, UInt64.ofNat wd, UInt64.ofNat cnt, UInt64.ofNat buf, UInt64.ofNat ctx])
          (by wev [f0, f1, f3, f4, f5, f7, acc, plan, start, wide']) call (Wp.done ⟨by wev [f5], ?_, kept⟩)
        simp only [leavesIn, EncodedLayout.count, pl, if_true] at hL ⊢
        rw [hL, hc]
        exact nodes
      · rw [if_neg pl] at flag
        refine Wp.ifElse_f (by wev [f0, f6, kind1, acc0, acc, flag]) ?_
        exact loopCase fun e' s' wd' c' h => by cases h; simpa using pl
    | listed l =>
      have ⟨k0, k1⟩ := held.listed_kind
      refine Wp.ifElse_f (by wonly [f6, acc0]; simp [k0]) ?_
      refine Wp.ifElse_f (by wonly [f0, f6, acc0, acc]; simp [k1]) ?_
      exact loopCase fun e' s' wd' c' h => by cases h

end Ssz.Native.Driver.ProveProof
