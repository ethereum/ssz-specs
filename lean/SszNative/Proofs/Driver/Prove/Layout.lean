import SszNative.Proofs.Driver.Prove.Slot
import SszNative.Proofs.Driver.Root
import SszNative.Proofs.Driver.Fields
import SszNative.Proofs.Driver.Assemble

/-!
The compiled layout driver writes the record of the tree a range of an accepted encoding merkleizes into, as the
Lean layout describes it.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.ProveProof

set_option maxRecDepth 20000

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Plan

/-- Packed bytes of a range, with one bit of the last byte cleared when a position is given. -/
def packedNodes (b : ByteArray) (a e : Nat) : Option Nat → ByteArray
  | none => packRange b a e
  | some k =>
    let nodes := packRange b a e
    nodes.set! (e - a - 1) (nodes.get! (e - a - 1) &&& ~~~((1 : UInt8) <<< UInt8.ofNat k))

/-- A bit list's nodes are its bytes up to the last bit, the delimiter cleared where it shares a byte. -/
theorem bitNodes_packed (b : ByteArray) (start count : Nat) :
    bitNodes b start count = packedNodes b start (start + (count + 7) / 8)
      (if count % 8 = 0 then none else some (count % 8)) := by
  by_cases whole : count % 8 = 0
  · simp [bitNodes, packedNodes, whole]
  · simp only [bitNodes, packedNodes, whole, ite_false, beq_iff_eq]
    rw [show start + (count + 7) / 8 - start - 1 = count / 8 by omega]

/--
How a layout record holds the leaves under its tree.

Packed leaves are a range of the encoding, with the delimiter's bit cleared when it shares the last byte.
Nested leaves are held as the slot reader reads them, with the plain flag of values one width apart.
-/
inductive LeavesAt (w : World) (mem : Memory) (lay : Nat) (b : ByteArray) (n lo hi top : Nat) : EncodedLeaves → Prop
  /-- Bytes of the encoding packed into nodes. -/
  | packed (a e : Nat) (cut : Option Nat) (kind : readLE mem lay 8 = 0)
      (first : readLE mem (lay + 80) 8 = UInt64.ofNat a) (last : readLE mem (lay + 88) 8 = UInt64.ofNat e)
      (flag : readLE mem (lay + 104) 8 = if cut.isSome then 1 else 0)
      (bit : ∀ k, cut = some k → readLE mem (lay + 112) 8 = UInt64.ofNat (2 ^ k))
      (cutSmall : ∀ k, cut = some k → k < 8 ∧ a < e) (ordered : a ≤ e) (inside : e ≤ b.size) :
      LeavesAt w mem lay b n lo hi top (.packed (packedNodes b a e cut) (nodesFor (e - a)))
  /-- Values with roots of their own. -/
  | nested (slots : Slots) (held : Held w mem lay b n lo hi top slots)
      (plainFlag : ∀ element start width count, slots = .stride element start width count →
        readLE mem (lay + 112) 8 = if plain element then 1 else 0) :
      LeavesAt w mem lay b n lo hi top (.nested slots)

/-- A layout record holding a layout: its counts, its bound, its mixed-in word, the encoding, and its leaves. -/
structure LaidOut (w : World) (mem : Memory) (lay data : Nat) (b : ByteArray) (n lo hi top : Nat)
    (layout : EncodedLayout) :
    Prop where
  /-- How many leaves, gaps included. -/
  count : readLE mem (lay + 8) 8 = UInt64.ofNat layout.count
  /-- Whether the tree is bounded. -/
  bounded : readLE mem (lay + 16) 8 = if layout.limit.isSome then 1 else 0
  /-- The bounded tree's capacity. -/
  capacity : ∀ c, layout.limit = some c → readLE mem (lay + 24) 8 = UInt64.ofNat c
  /-- Whether a word is mixed in. -/
  mixed : readLE mem (lay + 32) 8 = if layout.mixin.isSome then 1 else 0
  /-- The mixed-in word. -/
  word : ∀ x, layout.mixin = some x → BranchProof.readNode mem (lay + 40) = x
  /-- The encoding's address. -/
  encoding : readLE mem (lay + 72) 8 = UInt64.ofNat data
  /-- The leaves. -/
  leaves : LeavesAt w mem lay b n lo hi top layout.leaves

/-- The bytes a type's layout record takes: the fixed part, then a struct's field ranges. -/
def recordBytes : Desc → Nat
  | .container _ fields | .progressiveContainer _ _ fields => layoutBytes + 8 + 16 * fields.length
  | _ => layoutBytes

/-- Memory with a count written as one little-endian node. -/
def lengthWritten (mem : Memory) (a : Nat) (c : UInt64) : Memory :=
  store (store (store (store mem a 8 (qwordByte c)) (a + 8) 8 (qwordByte 0)) (a + 16) 8 (qwordByte 0)) (a + 24) 8
    (qwordByte 0)

/-- A count below the word size written as a node reads back as its length node. -/
theorem readNode_lengthWritten (mem : Memory) (a c : Nat) (small : c < 2 ^ 64) :
    BranchProof.readNode (lengthWritten mem a (UInt64.ofNat c)) a = lengthNode c := by
  -- Each byte is the count's byte at that place, and zero past the eighth.
  have byte : ∀ i < 32, lengthWritten mem a (UInt64.ofNat c) (a + i) = UInt8.ofNat (c >>> (8 * i)) := by
    intro i hi
    simp only [lengthWritten, Asm.store]
    by_cases low : i < 8
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      apply UInt8.toNat_inj.mp
      simp only [qwordByte, Nat.add_sub_cancel_left, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
        Nat.toUInt64_eq]
      rw [Validate.toNat_ofNat_lt small, Validate.toNat_ofNat_lt (show 8 * i < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show 8 * i < 64 by omega)]
      simp
    · have zero : c >>> (8 * i) = 0 := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le small (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [zero]
      by_cases r3 : 24 ≤ i
      · rw [ite_eq_left (by omega)]; simp [qwordByte]
      by_cases r2 : 16 ≤ i
      · rw [ite_eq_right (by omega), ite_eq_left (by omega)]; simp [qwordByte]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]; simp [qwordByte]
  unfold BranchProof.readNode lengthNode
  rw [ByteArray.mk.injEq]
  apply Array.ext (by simp)
  intro i h1 _
  simp only [Array.getElem_ofFn, Array.getElem_map, Array.getElem_range]
  exact byte i (by simpa using h1)

/-- Memory holding a count's eight bytes then zeros reads back as the count's length node. -/
theorem readNode_count {mem : Memory} {a c : Nat} (small : c < 2 ^ 64)
    (h : ∀ i < 32, mem (a + i) = if i < 8 then qwordByte (UInt64.ofNat c) i else 0) :
    BranchProof.readNode mem a = lengthNode c := by
  rw [← readNode_lengthWritten mem a c small]
  apply BranchProof.readNode_congr
  intro i hi
  rw [h i hi]
  simp only [lengthWritten, Asm.store]
  repeat' split
  all_goals first | omega | (congr 1; omega) | simp [qwordByte]

/-- A store leaves every byte outside it as it was. -/
theorem store_out {mem : Memory} {b n : Nat} {f : Nat → UInt8} {a : Nat} (h : ¬ (b ≤ a ∧ a < b + n)) :
    store mem b n f a = mem a := by
  simp only [Asm.store]; rw [ite_eq_right h]

/-- A store sets every byte inside it. -/
theorem store_in {mem : Memory} {b n : Nat} {f : Nat → UInt8} {a : Nat} (h : b ≤ a ∧ a < b + n) :
    store mem b n f a = f (a - b) := by
  simp only [Asm.store]; rw [ite_eq_left h]

/-- A store elsewhere leaves eight bytes as they were. -/
theorem read_store_apart (mem : Memory) (a b n : Nat) (f : Nat → UInt8) (h : a + 8 ≤ b ∨ b + n ≤ a) :
    readLE (store mem b n f) a 8 = readLE mem a 8 :=
  readLE_congr _ _ a 8 fun k _ => by simp only [Asm.store]; rw [ite_eq_right (by omega)]

/-- A function's body reaching its result and memory meeting a condition is a call leaving such a memory. -/
theorem calls_of_wp {m : Module} {w : World} {sp : Nat} {f : String} {args : List UInt64} {mem : Memory} {fn : Fn}
    {r : UInt64} {P : Memory → Prop} (hf : m.fns.lookup f = some fn) (room : w.stackLo + 8 + 8 * fn.frame ≤ sp)
    (count : args.length = fn.params)
    (hb : Wp m w (sp - 8 - 8 * fn.frame) fn.body (entryEnv args) mem
      (fun env' mem' => eval w env' mem' fn.result = some r ∧ P mem')) :
    ∃ mem', Calls m w f sp args mem r mem' ∧ P mem' := by
  obtain ⟨e, mem', run, hr, hp⟩ := hb
  exact ⟨mem', Calls.fn hf room count run hr, hp⟩

/-- A quotient by 32 rounded up, as the driver forms it, is the rounded-up quotient's word. -/
theorem ceil32 (x : Nat) (hx : x < 2 ^ 64) :
    UInt64.ofNat (x / 32) + (if x % 32 = 0 then 0 else 1) = UInt64.ofNat ((x + 31) / 32) := by
  apply UInt64.toNat_inj.mp
  by_cases r : x % 32 = 0 <;>
    simp [r, UInt64.toNat_add, UInt64.toNat_ofNat, Nat.mod_eq_of_lt (show x / 32 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (x + 31) / 32 < 2 ^ 64 by omega)] <;> omega

/-- A quotient by 256 rounded up, as the driver forms it, is the rounded-up quotient's word. -/
theorem ceil256 (x : Nat) (hx : x < 2 ^ 64) :
    UInt64.ofNat (x / 256) + (if x % 256 = 0 then 0 else 1) = UInt64.ofNat ((x + 255) / 256) := by
  apply UInt64.toNat_inj.mp
  by_cases r : x % 256 = 0 <;>
    simp [r, UInt64.toNat_add, UInt64.toNat_ofNat, Nat.mod_eq_of_lt (show x / 256 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (x + 255) / 256 < 2 ^ 64 by omega)] <;> omega

/-- Takes steps of a block, stores included, for as long as one can be taken. -/
macro "lsteps" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| repeat ((first | (wstep [$args,*]) |
    (refine Ssz.Native.Ir.Wp.store (by wev [$args,*]) (by wev [$args,*]) (by wonly [$args,*]) ?_)) <;>
    try simp only [List.cons_append, List.nil_append, List.append_nil]))

/-- Reads a word of a record back through the stores that wrote it. -/
macro "rd" : tactic =>
  `(tactic| (simp (disch := omega) only [read_store_apart, readLE_store8]; try rfl))

/--
Facts a layout record's cases share: the record is writable, and the plan and the encoding are in memory, apart from
it.
-/
structure LayoutInput (w : World) (mem : Memory) (d : Desc) (b : ByteArray) (p data start stop lay : Nat) : Prop where
  /-- The type's plan. -/
  planned : PlanAt w mem p (words d)
  /-- The plan's words fit a word. -/
  fits : ∀ x ∈ words d, x < 2 ^ 64
  /-- The plan sits apart from the record. -/
  planApart : p + 8 * (words d).length ≤ lay ∨ lay + recordBytes d ≤ p
  /-- The record is writable. -/
  writable : w.access lay (recordBytes d) = true
  /-- The range is ordered. -/
  ordered : start ≤ stop
  /-- The range lies inside the encoding. -/
  inside : stop ≤ b.size
  /-- The encoding is small enough that eight bits per byte, and more, stay below the word size. -/
  small : 64 * b.size + 128 < 2 ^ 64
  /-- The encoding's bytes are in memory. -/
  bytes : BytesAt mem data b
  /-- The program may read them. -/
  readable : w.access data b.size = true
  /-- The encoding sits apart from the record. -/
  dataApart : data + b.size ≤ lay ∨ lay + recordBytes d ≤ data

/--
What the layout driver leaves: the record of a layout, its plan nodes inside the type's plan, its free pointer, and
nothing else changed.
-/
def LayoutDone (w : World) (mem mem' : Memory) (d : Desc) (p lay data : Nat) (b : ByteArray) (layout : EncodedLayout) :
    Prop :=
  LaidOut w mem' lay data b (d.nesting - 1) p (p + 8 * (words d).length) (lay + recordBytes d) layout ∧
    readLE mem' (lay + 120) 8 = UInt64.ofNat (lay + recordBytes d) ∧
    ∀ a, ¬ (lay ≤ a ∧ a < lay + recordBytes d) → mem' a = mem a

set_option hygiene false in
/-- Runs a basic type's record to its end, then reads every word of it back. -/
macro "basicRun" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    refine calls_of_wp hf room rfl ?_
    simp only [ProveLayout.fn, ProveLayout.basic, ProveLayout.packed, ProveLayout.mixCount, lengthNodeAt, ceilDiv,
      List.cons_append, List.nil_append]
    lsteps [acc, acc0, read_store_apart, Nat.add_assoc, $args,*]
    refine ⟨rfl, ?_⟩
    simp (disch := omega) only [Validate.toNat_ofNat_lt, Width.bytes, ceil32, ceil256, layoutBytes]
    refine ⟨⟨?_, ?_, fun c hc => ?_, ?_, fun x hx => ?_, ?_, ?_⟩, ?_, fun a ha => ?_⟩
    · simp only [EncodedLayout.count]; rd
    · rd
    · cases hc; rd
    · rd
    · -- A byte list mixes its size in, as a length node.
      cases hx
      all_goals
        refine readNode_count (by omega) fun i hi => ?_
        -- Each byte falls in one of the four words the node was written as.
        rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i by omega) with r | r | r | r
        · simp (disch := omega) only [store_out, store_in, r, ite_true]
          rw [show lay + 40 + i - (lay + 40) = i by omega]
        all_goals
          simp (disch := omega) only [store_out, store_in, show ¬ i < 8 by omega, ite_false]
          simp [qwordByte]
    · rd
    · exact LeavesAt.packed start stop none (by rd) (by rd) (by rd) (by rd) (fun k hk => by cases hk)
        (fun k hk => by cases hk) ordered inside
    · rd
    · simp only [recordBytes, layoutBytes] at ha
      simp (disch := omega) only [store_out]))

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
/-- A basic type's record: its bytes packed, the tree just wide enough or declared, a byte list's size mixed in. -/
theorem layout_basic {m : Module} {w : World} (hf : m.fns.lookup "ssz_prove_layout" = some ProveLayout.fn)
    {sp : Nat} (room : w.stackLo + 8 + 8 * ProveLayout.fn.frame ≤ sp) {mem : Memory} {d : Desc} {b : ByteArray}
    {p data start stop lay : Nat} {layout : EncodedLayout} (laid : layoutOf d b start stop = .ok layout)
    (basic : tag d ≤ 4) (input : LayoutInput w mem d b p data start stop lay) :
    ∃ mem', Calls m w "ssz_prove_layout" sp [UInt64.ofNat p, UInt64.ofNat data, UInt64.ofNat start,
      UInt64.ofNat stop, UInt64.ofNat lay] mem 0 mem' ∧ LayoutDone w mem mem' d p lay data b layout := by
  have planned := input.planned
  have pb := planned.1
  simp only [addressBound] at pb
  have ordered := input.ordered
  have inside := input.inside
  have small := input.small
  have head : ∀ (rest : List Nat) (t : Nat), words d = t :: rest → readLE mem p 8 = UInt64.ofNat t ∧
      w.access p 8 = true := fun rest t h => by
    rw [h] at planned
    exact ⟨(planned.2 0 (by simp)).2, by simpa using (planned.2 0 (by simp)).1⟩
  have second : ∀ (t x : Nat), words d = [t, x] → readLE mem (p + 8) 8 = UInt64.ofNat x ∧
      w.access (p + 8) 8 = true ∧ x < 2 ^ 64 := fun t x h => by
    have fx := input.fits x (by rw [h]; simp)
    rw [h] at planned
    exact ⟨(planned.2 1 (by simp)).2, (planned.2 1 (by simp)).1, fx⟩
  cases d <;> simp only [tag] at basic <;> try omega
  all_goals
    simp only [layoutOf, Except.ok.injEq] at laid
    subst laid
    have apart := input.planApart
    have writable := input.writable
    simp only [recordBytes, layoutBytes, words, List.length_cons, List.length_nil] at apart writable
    have lb := BranchProof.access_bound writable
    have acc : ∀ k, k + 8 ≤ 144 → w.access (lay + k) 8 = true := fun k hk => BranchProof.access_sub writable (by omega)
    have acc0 : w.access lay 8 = true := BranchProof.access_prefix writable (by omega)
  -- Each tag reads its own words of the plan: the tag, and a declared length or limit.
  · have ⟨t0, a0⟩ := head [] 0 rfl
    basicRun [t0, a0]
  · have ⟨t0, a0⟩ := head _ 1 rfl
    basicRun [t0, a0]
  · have ⟨t0, a0⟩ := head _ 2 rfl
    basicRun [t0, a0]
  · have ⟨t0, a0⟩ := head _ 3 rfl
    have ⟨t8, a8, _⟩ := second 3 _ rfl
    basicRun [t0, a0, t8, a8]
  · have ⟨t0, a0⟩ := head _ 4 rfl
    have ⟨t8, a8, _⟩ := second 4 _ rfl
    basicRun [t0, a0, t8, a8]

/-- A byte's halvings: whether one more is taken, and the highest set bit once they stop. -/
theorem halve_table : ∀ x < 256, ∀ j < 8, 1 ≤ x >>> j →
    (1 < x >>> j → j < 7) ∧ (x >>> j ≤ 1 → highestBit (UInt8.ofNat x) = j) := by
  decide +kernel

/--
The bit list's loop halves its last byte down to one, counting the halvings and doubling a power of two with each.

It ends with the byte's highest set bit and two to that bit, every other variable and the memory as they were.
-/
theorem halve_loop {m : Module} {w : World} {sp : Nat} {env0 : Env} {mem0 : Memory} {rest : List Stmt}
    {Q : Env → Memory → Prop} {x : Nat} (byte : x < 256) (set : 1 ≤ x)
    (hv : env0 14 = UInt64.ofNat x) (hb : env0 15 = 0) (hp : env0 16 = 1)
    (k : ∀ env, (∀ i, i ≠ 14 → i ≠ 15 → i ≠ 16 → env i = env0 i) →
      env 15 = UInt64.ofNat (highestBit (UInt8.ofNat x)) →
      env 16 = UInt64.ofNat (2 ^ highestBit (UInt8.ofNat x)) → Wp m w sp (.block rest) env mem0 Q) :
    Wp m w sp (.block (while_ (lt 1 ProveLayout.v)
      [ProveLayout.v ::= ProveLayout.v / 2, ProveLayout.hb ::= ProveLayout.hb + 1,
        ProveLayout.pw ::= ProveLayout.pw + ProveLayout.pw] :: rest)) env0 mem0 Q := by
  refine Wp.loop (wp_loop (fun env mem => mem = mem0 ∧ ∃ j, j < 8 ∧ env 14 = UInt64.ofNat (x >>> j) ∧
      env 15 = UInt64.ofNat j ∧ env 16 = UInt64.ofNat (2 ^ j) ∧ 1 ≤ x >>> j ∧
      ∀ i, i ≠ 14 → i ≠ 15 → i ≠ 16 → env i = env0 i)
    (fun env _ => (env 14).toNat) ⟨rfl, 0, by omega, by simpa using hv, by simpa using hb, by simpa using hp,
      by simpa using set, fun _ _ _ _ => rfl⟩ ?_)
  rintro env mem ⟨rfl, j, hj, e14, e15, e16, pos, same⟩
  have le := Nat.shiftRight_le x j
  have ⟨more, last⟩ := halve_table x byte j hj pos
  have pj : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨_, by wev [e14], fun go => ?_, fun stop => ?_⟩
  · have big : 1 < x >>> j := by
      rcases Nat.lt_or_ge 1 (x >>> j) with h | h
      · exact h
      · simp [show ¬ 1 < x >>> j by omega] at go
    have j7 := more big
    have halved : x >>> (j + 1) = x >>> j / 2 := Nat.shiftRight_succ x j
    have twice : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by rw [Nat.pow_succ]; omega
    wsteps [e14, e15, e16]
    refine ⟨⟨trivial, j + 1, by omega, by wev [halved], by wev [], by wev [twice, e16], by omega,
      fun i a b c => by wonly [a, b, c, same i a b c]⟩, ?_⟩
    wonly [e14, halved]
    omega
  · have done : x >>> j ≤ 1 := by
      rcases Nat.lt_or_ge 1 (x >>> j) with h | h
      · simp [h] at stop
      · exact h
    rw [last done] at k
    exact k env same e15 e16

/-- A store elsewhere leaves a byte as it was. -/
theorem read1_store_apart (mem : Memory) (a b n : Nat) (f : Nat → UInt8) (h : a + 1 ≤ b ∨ b + n ≤ a) :
    readLE (store mem b n f) a 1 = readLE mem a 1 :=
  readLE_congr _ _ a 1 fun k _ => by simp only [Asm.store]; rw [ite_eq_right (by omega)]

/-- A small word divided by eight. -/
theorem div8 (a : Nat) (ha : a < 2 ^ 64) : UInt64.ofNat a / 8 = UInt64.ofNat (a / 8) := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_div, Validate.toNat_ofNat_lt ha, Validate.toNat_ofNat_lt (show a / 8 < 2 ^ 64 by omega)]

/-- A small word's remainder by eight. -/
theorem mod8 (a : Nat) (ha : a < 2 ^ 64) : UInt64.ofNat a % 8 = UInt64.ofNat (a % 8) := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_mod, Validate.toNat_ofNat_lt ha, Validate.toNat_ofNat_lt (show a % 8 < 2 ^ 64 by omega)]

/-- A quotient by 32 rounded up, with the divisor cast from a number. -/
theorem ceil32' (x : Nat) (hx : x < 2 ^ 64) :
    UInt64.ofNat x / Nat.toUInt64 32 + (if UInt64.ofNat x % Nat.toUInt64 32 = 0 then 0 else 1) =
      UInt64.ofNat ((x + 31) / 32) := by
  have := ceil32 x hx
  have e : Nat.toUInt64 32 = 32 := rfl
  rw [e, ← this]
  have d : UInt64.ofNat x / 32 = UInt64.ofNat (x / 32) := by
    apply UInt64.toNat_inj.mp
    simp [UInt64.toNat_div, Validate.toNat_ofNat_lt hx, Validate.toNat_ofNat_lt (show x / 32 < 2 ^ 64 by omega)]
  have r : (UInt64.ofNat x % 32 = 0) ↔ x % 32 = 0 := by
    constructor
    · intro h; have := congrArg UInt64.toNat h
      simp [UInt64.toNat_mod, Validate.toNat_ofNat_lt hx] at this; omega
    · intro h; apply UInt64.toNat_inj.mp; simp [UInt64.toNat_mod, Validate.toNat_ofNat_lt hx]; omega
  rw [d]
  by_cases h : x % 32 = 0 <;> simp [h, r]

/-- A flag of a small word being nonzero is the flag of the number being nonzero. -/
theorem flag_ofNat (r : Nat) (hr : r < 2 ^ 64) :
    (if UInt64.ofNat r = 0 then (0 : UInt64) else 1) = if r = 0 then 0 else 1 := by
  by_cases h : r = 0
  · simp [h]
  · have : UInt64.ofNat r ≠ 0 := fun e => h (by have := congrArg UInt64.toNat e; simpa [Validate.toNat_ofNat_lt hr] using this)
    simp [h, this]

/-- A byte's highest set bit is one of its eight. -/
theorem highestBit_lt : ∀ x < 256, highestBit (UInt8.ofNat x) < 8 := by
  decide +kernel

/-- One byte of an encoding in memory, read as a word. -/
theorem read_byte {mem : Memory} {data : Nat} {b : ByteArray} (bytes : BytesAt mem data b) {k : Nat}
    (inside : k < b.size) : readLE mem (data + k) 1 = UInt64.ofNat (b.get! k).toNat := by
  simp only [readLE, bytes k inside]
  apply UInt64.toNat_inj.mp
  simp

set_option hygiene false in
/-- Runs a bit list's record to its end, the last byte halved down to its highest bit, then reads it back. -/
macro "bitRun" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    refine calls_of_wp hf room rfl ?_
    simp only [ProveLayout.fn, ProveLayout.bitList, ProveLayout.packed, ProveLayout.mixCount, lengthNodeAt, ceilDiv,
      List.cons_append, List.nil_append]
    lsteps [acc, acc0, lastByte, lastAcc, read_store_apart, read1_store_apart, Nat.add_assoc, $args,*]
    refine halve_loop xs xpos (by wev []) (by wev []) (by wev []) fun env same e15 e16 => ?_
    rw [back, hh] at e15 e16
    have p7 : 2 ^ top ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    lsteps [same, e15, e16, acc, acc0, read_store_apart, Nat.add_assoc, $args,*]
    refine ⟨rfl, ?_⟩
    have q : (8 * (stop - start - 1) + (top + 7)) / 8 = (8 * (stop - start - 1) + top + 7) / 8 := by omega
    have r8 : (8 * (stop - start - 1) + top) % 8 = top := by omega
    simp (disch := omega) only [Validate.toNat_ofNat_lt, Width.bytes, layoutBytes, ceil32, ceil256]
    refine ⟨⟨?_, ?_, fun c hc => ?_, ?_, fun y hy => ?_, ?_, ?_⟩, ?_, fun a ha => ?_⟩
    · simp only [EncodedLayout.count]; rd
      congr 1
      simp only [nodesFor]
      omega
    · rd
    · cases hc <;> rd
    · rd
    · -- The count of bits, mixed in as a length node.
      cases hy
      refine readNode_count (by omega) fun i hi => ?_
      rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i by omega) with r | r | r | r
      · simp (disch := omega) only [store_out, store_in, r, ite_true]
        rw [show lay + 40 + i - (lay + 40) = i by omega]
      all_goals
        simp (disch := omega) only [store_out, store_in, show ¬ i < 8 by omega, ite_false]
        simp [qwordByte]
    · rd
    · -- The bytes up to the last bit, the delimiter's bit cleared where it shares the last of them.
      simp only []
      rw [bitNodes_packed, show nodesFor ((8 * (stop - start - 1) + top + 7) / 8) =
        nodesFor (start + (8 * (stop - start - 1) + top + 7) / 8 - start) by congr 1; omega]
      refine LeavesAt.packed _ _ _ ?_ ?_ ?_ ?_ (fun k hk => ?_) (fun k hk => ?_) (by omega) (by omega)
      · rd
      · rd
      · rd
      · rd; rw [r8]; by_cases z : top = 0 <;> simp [z]
      · rw [r8] at hk
        by_cases z : top = 0
        · simp [z] at hk
        · simp only [z, ite_false, Option.some.injEq] at hk
          subst hk
          rd
      · rw [r8] at hk
        by_cases z : top = 0
        · simp [z] at hk
        · simp only [z, ite_false, Option.some.injEq] at hk
          exact ⟨by omega, by omega⟩
    · rd
    · simp only [recordBytes, layoutBytes] at ha
      simp (disch := omega) only [store_out]))

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
/--
A bit list's record: its bytes up to the last bit packed, the delimiter's bit noted where it shares a byte, and the
count of bits mixed in.
-/
theorem layout_bitList {m : Module} {w : World} (hf : m.fns.lookup "ssz_prove_layout" = some ProveLayout.fn)
    {sp : Nat} (room : w.stackLo + 8 + 8 * ProveLayout.fn.frame ≤ sp) {mem : Memory} {d : Desc} {b : ByteArray}
    {p data start stop lay : Nat} {layout : EncodedLayout} (laid : layoutOf d b start stop = .ok layout)
    (bits : tag d = 5 ∨ tag d = 6) (input : LayoutInput w mem d b p data start stop lay) (nonempty : start < stop)
    (delimited : b.get! (stop - 1) ≠ 0) :
    ∃ mem', Calls m w "ssz_prove_layout" sp [UInt64.ofNat p, UInt64.ofNat data, UInt64.ofNat start,
      UInt64.ofNat stop, UInt64.ofNat lay] mem 0 mem' ∧ LayoutDone w mem mem' d p lay data b layout := by
  have planned := input.planned
  have pb := planned.1
  simp only [addressBound] at pb
  have ordered := input.ordered
  have inside := input.inside
  have small := input.small
  have db := BranchProof.access_bound input.readable
  -- The last byte, which holds the delimiter.
  generalize hx : (b.get! (stop - 1)).toNat = x
  have xs : x < 256 := hx ▸ UInt8.toNat_lt _
  have xpos : 1 ≤ x := by
    rcases Nat.lt_or_ge x 1 with h | h
    · exact absurd (UInt8.toNat_inj.mp (by rw [hx]; simp; omega)) delimited
    · exact h
  have back : UInt8.ofNat x = b.get! (stop - 1) := by rw [← hx]; simp
  have lastByte : readLE mem (data + stop - 1) 1 = UInt64.ofNat x := by
    rw [show data + stop - 1 = data + (stop - 1) by omega, read_byte input.bytes (by omega), hx]
  have lastAcc : w.access (data + stop - 1) 1 = true := by
    rw [show data + stop - 1 = data + (stop - 1) by omega]
    exact BranchProof.access_sub input.readable (by omega)
  have hbl := highestBit_lt x xs
  rw [back] at hbl
  generalize hh : highestBit (b.get! (stop - 1)) = top at hbl
  have head : ∀ (rest : List Nat) (t : Nat), words d = t :: rest → readLE mem p 8 = UInt64.ofNat t ∧
      w.access p 8 = true := fun rest t e => by
    rw [e] at planned
    exact ⟨(planned.2 0 (by simp)).2, by simpa using (planned.2 0 (by simp)).1⟩
  cases d <;> simp only [tag] at bits <;> try omega
  all_goals
    simp only [layoutOf, bitCount, hh, Except.ok.injEq] at laid
    subst laid
    have apart := input.planApart
    have writable := input.writable
    have dapart := input.dataApart
    simp only [recordBytes, layoutBytes, words, Plan.bound, List.length_cons, List.length_nil] at apart writable dapart
    have lb := BranchProof.access_bound writable
    have acc : ∀ k, k + 8 ≤ 144 → w.access (lay + k) 8 = true := fun k hk => BranchProof.access_sub writable (by omega)
    have acc0 : w.access lay 8 = true := BranchProof.access_prefix writable (by omega)
  · rename_i limit
    have ⟨t0, a0⟩ := head _ 5 rfl
    have fl := input.fits limit (by simp [words])
    have t8 : readLE mem (p + 8) 8 = UInt64.ofNat limit := (planned.2 1 (by simp [words])).2
    have a8 : w.access (p + 8) 8 = true := (planned.2 1 (by simp [words])).1
    bitRun [t0, a0, t8, a8]
  · have ⟨t0, a0⟩ := head _ 6 rfl
    bitRun [t0, a0]

/-- A plan's words stay where memory agrees with them. -/
theorem PlanAt.frame {w : World} {mem mem' : Memory} {p : Nat} {ws : List Nat} (h : PlanAt w mem p ws)
    (same : ∀ a, p ≤ a → a < p + 8 * ws.length → mem' a = mem a) : PlanAt w mem' p ws := by
  refine ⟨h.1, fun k small => ⟨(h.2 k small).1, ?_⟩⟩
  rw [← (h.2 k small).2]
  exact readLE_congr _ _ _ 8 fun i hi => same _ (by omega) (by omega)

/-- A basic type's width is its item length, one of the six integer widths, and it has a fixed size. -/
theorem basic_width {e : Desc} (basic : e.isBasic = true) (sound : e.wellFormed = .ok ()) :
    fixedWidth e = e.itemLength ∧ e.itemLength ∈ [1, 2, 4, 8, 16, 32] ∧ hasWidth e = true := by
  cases e <;> simp [Desc.isBasic] at basic
  · simp [fixedWidth, Desc.itemLength, hasWidth]
  · rename_i width
    simp only [Desc.wellFormed] at sound
    split at sound
    · rename_i h
      simp only [List.contains_iff_mem] at h
      exact ⟨rfl, h, rfl⟩
    · cases sound

/-- A count of basic elements' nodes, as the driver forms it from the elements per node. -/
theorem basic_capacity (L w : Nat) (hw : w ∈ [1, 2, 4, 8, 16, 32]) (hL : L < 2 ^ 64) :
    UInt64.ofNat (L / (32 / w)) + (if L % (32 / w) = 0 then 0 else 1) = UInt64.ofNat ((L * w + 32 - 1) / 32) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  apply UInt64.toNat_inj.mp
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl <;>
    (split <;> (rename_i r; simp [UInt64.toNat_add, UInt64.toNat_ofNat]; omega))

/-- The element and the count of a sequence's values in a range of an encoding. -/
def sequenceOf (b : ByteArray) (start stop : Nat) : Desc → Option (Desc × Nat)
  | .vector element length => some (element, length)
  | .list element _ | .progressiveList element _ => some (element, elementCount element b start stop)
  | _ => none

/-- A store elsewhere leaves four bytes as they were. -/
theorem read4_store_apart (mem : Memory) (a b n : Nat) (f : Nat → UInt8) (h : a + 4 ≤ b ∨ b + n ≤ a) :
    readLE (store mem b n f) a 4 = readLE mem a 4 :=
  readLE_congr _ _ a 4 fun k _ => by simp only [Asm.store]; rw [ite_eq_right (by omega)]

/-- An offset is four bytes, so it stays below 2^32. -/
theorem offsetAt_lt (b : ByteArray) (x : Nat) : offsetAt b x < 2 ^ 32 := by
  have := (b.get! x).toNat_lt; have := (b.get! (x + 1)).toNat_lt; have := (b.get! (x + 2)).toNat_lt
  have := (b.get! (x + 3)).toNat_lt
  simp only [offsetAt]; omega

set_option hygiene false in
/-- Reads a count written as a length node at the record's mixed-in word back as that node. -/
macro "countWord" : tactic =>
  `(tactic| (
    refine readNode_count (by omega) fun i hi => ?_
    rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ 24 ≤ i by omega) with r | r | r | r
    · simp (disch := omega) only [store_out, store_in, r, ite_true]
      rw [show lay + 40 + i - (lay + 40) = i by omega]
      try rfl
    all_goals
      simp (disch := omega) only [store_out, store_in, show ¬ i < 8 by omega, ite_false]
      simp [qwordByte]))

/-- What an accepted encoding of a sequence tells the layout driver: its offset table fits in it. -/
structure SeqAccepted (element : Desc) (start stop count : Nat) : Prop where
  /-- The offsets of elements of no fixed size fit in the range. -/
  table : element.fixedSize = none → start + 4 * count ≤ stop
  /-- A nonempty list of them holds at least its first offset. -/
  first : element.fixedSize = none → start < stop → start + 4 ≤ stop

/-- A capacity of basic elements, as the driver forms it from the elements a node holds, is a node count. -/
theorem capacity_eval {w : World} {env : Env} {mem : Memory} {L iw : Nat} (hL : env 23 = UInt64.ofNat L)
    (hw : env 8 = Nat.toUInt64 iw) (items : iw ∈ [1, 2, 4, 8, 16, 32]) (bL : L < 2 ^ 64) :
    eval w env mem (ProveLayout.lim / (32 / ProveLayout.w) + ne (ProveLayout.lim % (32 / ProveLayout.w)) 0) =
      some (UInt64.ofNat ((L * iw + 32 - 1) / 32)) := by
  wonly [hL, hw]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at items
  have hb := Validate.toNat_ofNat_lt bL
  rcases items with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp
    first
    | (split <;> rename_i h <;> simp only [← UInt64.toNat_inj] at h ⊢ <;>
        simp [UInt64.toNat_add, UInt64.toNat_div, UInt64.toNat_mod, hb] at h ⊢ <;> omega)
    | (simp only [← UInt64.toNat_inj]; simp [hb]; omega)

set_option hygiene false in
/-- Reads every word of a sequence's record back, with a tactic for its leaves. -/
macro "recordFinish" leaves:tacticSeq : tactic =>
  `(tactic| (
    refine ⟨rfl, ?_⟩
    simp (disch := omega) only [Validate.toNat_ofNat_lt, Width.bytes, ceil32, layoutBytes]
    refine ⟨⟨?_, ?_, fun c hc => ?_, ?_, fun y hy => ?_, ?_, ?_⟩, ?_, fun a ha => ?_⟩
    · simp only [EncodedLayout.count, Slots.count, List.length_map, bodyRanges, List.length_zip,
        List.length_append, List.length_drop, List.length_range, List.length_cons, List.length_nil]
      rd
      try (congr 1; omega)
    · rd
    · cases hc <;> rd
    · rd
    · cases hy <;> countWord
    · rd
    · $leaves
    · rd
    · simp only [recordBytes, layoutBytes] at ha
      simp (disch := omega) only [store_out]))

set_option hygiene false in
/-- Basic elements' record: their bytes packed, after the capacity their count of nodes takes. -/
macro "packedFinish" L:term:max "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    lsteps [acc, acc0, te, ae, tag_le_one, basic, bitOf, hw, wd, read_store_apart, Nat.add_assoc, $args,*]
    refine Wp.store (by wev []) (capacity_eval (L := $L) (by wev []) (by wev [wd]) items (by omega)) (by wonly [acc]) ?_
    lsteps [acc, read_store_apart, Nat.add_assoc]
    recordFinish
      exact LeavesAt.packed start stop none (by rd) (by rd) (by rd) (by rd) (fun k hk => by cases hk)
        (fun k hk => by cases hk) ordered inside))

set_option hygiene false in
/-- Fixed-size elements' record: one width apart, with the plain flag read from the element's plan. -/
macro "strideFinish" ep:term:max small:term:max : tactic =>
  `(tactic| (
    refine Wp.call (values := [UInt64.ofNat $ep]) (by wev [])
      (planPlain_calls fns element $ep _ _ (PlanAt.frame pe fun a h1 h2 => by
        simp (disch := omega) only [store_out, Validate.toNat_ofNat_lt, Width.bytes]) eSound deep) ?_
    lsteps [acc, read_store_apart, Nat.add_assoc]
    recordFinish
      refine LeavesAt.nested _ (Held.stride element start _ _ $ep (by rd) (by rd) (by rd) (by rd) (by rd)
        (PlanAt.frame pe fun a h1 h2 => by simp (disch := omega) only [store_out])
        ⟨by omega, by simp only [words, Validate.bound_length, List.length_append, List.length_cons, List.length_nil,
          List.length_map]; omega⟩ $small) fun e s wd c h => ?_
      cases h
      rd))

set_option hygiene false in
/-- Elements of no fixed size: each found through its offset. -/
macro "offsetsFinish" ep:term:max : tactic =>
  `(tactic| (
    recordFinish
      refine LeavesAt.nested _ (Held.offsets element start stop _ $ep data (by rd) (by rd) (by rd) (by rd)
        (by rd) (by rd) (PlanAt.frame pe fun a h1 h2 => by simp (disch := omega) only [store_out])
        ⟨by omega, by simp only [words, Validate.bound_length, List.length_append, List.length_cons, List.length_nil,
          List.length_map]; omega⟩
        (fun k hk => by rw [← input.bytes k hk]; simp (disch := omega) only [store_out]) input.readable ordered
        inside (by omega)) fun e s wd c h => ?_
      cases h))

set_option hygiene false in
/-- Runs a sequence's record up to its element's two plan reads, then reads the element's tag. -/
macro "seqFront" ep:term:max "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    have deep : w.stackLo + 112 * element.nesting ≤ sp - 8 - 8 * ProveLayout.fn.frame := by omega
    refine calls_of_wp hf (by omega) rfl ?_
    simp only [ProveLayout.fn, ProveLayout.sequence, ProveLayout.packed, ProveLayout.mixCount, lengthNodeAt, ceilDiv,
      List.cons_append, List.nil_append]
    lsteps [acc, acc0, read_store_apart, Nat.add_assoc, $args,*]
    simp only [words, Validate.bound_length, List.length_append, List.length_cons, List.length_nil] at apart pb
    -- The element's width and whether it has one, read from its plan, which the stores so far missed.
    refine Wp.call (values := [UInt64.ofNat $ep]) (by wev [])
      (planWidth_calls fns element $ep _ _ (PlanAt.frame pe fun a h1 h2 => by
        simp (disch := omega) only [store_out, Validate.toNat_ofNat_lt, Width.bytes]) eSound eThin deep) ?_
    refine Wp.call (values := [UInt64.ofNat $ep]) (by wev [])
      (planFixed_calls fns element $ep _ _ (PlanAt.frame pe fun a h1 h2 => by
        simp (disch := omega) only [store_out, Validate.toNat_ofNat_lt, Width.bytes]) eSound deep) ?_
    have ⟨te, ae⟩ : readLE mem $ep 8 = UInt64.ofNat (tag element) ∧ w.access $ep 8 = true := by
      obtain ⟨rest, hr⟩ := words_head element
      have := pe.2 0 (by simp [hr])
      simp only [hr, Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at this
      exact ⟨this.2, this.1⟩
    have tl := tag_lt element
    simp only [layoutOf, encodedSequence, elementSlots, Except.ok.injEq] at laid
    subst laid))

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
/--
A sequence's record: basic elements packed, fixed-size ones one width apart, the others through their offsets, with a
list's count mixed in.
-/
theorem layout_sequence {m : Module} {w : World} (fns : PlanFns m)
    (hf : m.fns.lookup "ssz_prove_layout" = some ProveLayout.fn) {sp : Nat} {mem : Memory} {d : Desc} {b : ByteArray}
    (room : w.stackLo + 8 + 8 * ProveLayout.fn.frame + 112 * d.nesting ≤ sp)
    {p data start stop lay : Nat} {layout : EncodedLayout} (laid : layoutOf d b start stop = .ok layout)
    (seq : tag d = 7 ∨ tag d = 8 ∨ tag d = 9) (input : LayoutInput w mem d b p data start stop lay)
    (sound : d.wellFormed = .ok ()) (thin : narrow d = true)
    (accepted : ∀ element count, sequenceOf b start stop d = some (element, count) →
      SeqAccepted element start stop count) :
    ∃ mem', Calls m w "ssz_prove_layout" sp [UInt64.ofNat p, UInt64.ofNat data, UInt64.ofNat start,
      UInt64.ofNat stop, UInt64.ofNat lay] mem 0 mem' ∧ LayoutDone w mem mem' d p lay data b layout := by
  have planned := input.planned
  have pb := planned.1
  simp only [addressBound] at pb
  have ordered := input.ordered
  have inside := input.inside
  have small := input.small
  have db := BranchProof.access_bound input.readable
  have apart := input.planApart
  have writable := input.writable
  have dapart := input.dataApart
  cases d <;> simp only [tag] at seq <;> try omega
  all_goals
    rename_i element bound
    simp only [recordBytes, layoutBytes] at apart writable dapart
    have lb := BranchProof.access_bound writable
    have acc : ∀ k, k + 8 ≤ 144 → w.access (lay + k) 8 = true := fun k hk => BranchProof.access_sub writable (by omega)
    have acc0 : w.access lay 8 = true := BranchProof.access_prefix writable (by omega)
    have ⟨tableIn, firstIn⟩ := accepted _ _ rfl
    simp only [Desc.nesting] at room
  · -- A vector: its length read from the plan, then its element.
    have t0 : readLE mem p 8 = UInt64.ofNat 7 := (planned.2 0 (by simp [words])).2
    have a0 : w.access p 8 = true := (planned.2 0 (by simp [words])).1
    have t8 : readLE mem (p + 8) 8 = UInt64.ofNat bound := (planned.2 1 (by simp [words])).2
    have a8 : w.access (p + 8) 8 = true := (planned.2 1 (by simp [words])).1
    have pe : PlanAt w mem (p + 16) (words element) := by
      have := planned.right (a := [7, bound]); simpa [words] using this
    have eSound : element.wellFormed = .ok () := by
      revert sound; simp only [Desc.wellFormed]; split <;> simp_all [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
    have eThin : narrow element = true := by simp only [narrow, Bool.and_eq_true] at thin; exact thin.2
    have bl := input.fits bound (by simp [words])
    seqFront (p + 16) [t0, a0, t8, a8]
    by_cases basic : element.isBasic = true
    · -- Basic elements: their bytes packed, the capacity the length's bytes take.
      have ⟨wd, items, hw⟩ := basic_width basic eSound
      simp only [basic, ite_true]
      packedFinish bound []
    have nb : element.isBasic = false := by simpa using basic
    simp only [nb, Bool.false_eq_true, ite_false]
    by_cases hw : hasWidth element = true
    · -- Fixed-size elements: one width apart, rooted as columns when plain.
      simp only [fixedSize_eq, hw, ite_true]
      have fw := narrow_width element eThin _ (by rw [fixedSize_eq, ite_eq_left hw])
      lsteps [acc, acc0, te, ae, tag_le_one, nb, bitOf, hw, read_store_apart, Nat.add_assoc]
      strideFinish (p + 16) (by omega)
    · have hw' : hasWidth element = false := by simpa using hw
      have none_ : element.fixedSize = none := by rw [fixedSize_eq, ite_eq_right hw]
      have tIn := tableIn none_
      simp only [none_]
      lsteps [acc, acc0, te, ae, tag_le_one, nb, bitOf, hw', read_store_apart, Nat.add_assoc]
      offsetsFinish (p + 16)
  · -- A list: its limit read from the plan, its count from its encoding, and the count mixed in.
    have t0 : readLE mem p 8 = UInt64.ofNat 8 := (planned.2 0 (by simp [words])).2
    have a0 : w.access p 8 = true := (planned.2 0 (by simp [words])).1
    have t8 : readLE mem (p + 8) 8 = UInt64.ofNat bound := (planned.2 1 (by simp [words])).2
    have a8 : w.access (p + 8) 8 = true := (planned.2 1 (by simp [words])).1
    have pe : PlanAt w mem (p + 16) (words element) := by
      have := planned.right (a := [8, bound]); simpa [words] using this
    have bl := input.fits bound (by simp [words])
    have eSound : element.wellFormed = .ok () := by simpa only [Desc.wellFormed] using sound
    have eThin : narrow element = true := by simpa only [narrow] using thin
    seqFront (p + 16) [t0, a0, t8, a8]
    by_cases basic : element.isBasic = true
    · -- Basic elements: their bytes packed, their count the bytes over the width.
      have ⟨wd, items, hw⟩ := basic_width basic eSound
      have il : element.itemLength ≠ 0 := by simp at items; omega
      have il32 : element.itemLength ≤ 32 := by simp at items; omega
      have ec : elementCount element b start stop = (stop - start) / element.itemLength := by
        simp [elementCount, fixedSize_eq, hw, wd, il]
      have cs : (stop - start) / element.itemLength ≤ stop - start := Nat.div_le_self _ _
      simp only [basic, ite_true, ec]
      packedFinish bound [il]
    have nb : element.isBasic = false := by simpa using basic
    simp only [nb, Bool.false_eq_true, ite_false]
    by_cases hw : hasWidth element = true
    · -- Fixed-size elements: as many as fit, one width apart.
      have fw := narrow_width element eThin _ (by rw [fixedSize_eq, ite_eq_left hw])
      by_cases wz : fixedWidth element = 0
      · have ec : elementCount element b start stop = 0 := by simp [elementCount, fixedSize_eq, hw, wz]
        simp only [fixedSize_eq, hw, ite_true, ec, wz]
        lsteps [acc, acc0, te, ae, tag_le_one, nb, bitOf, hw, wz, read_store_apart, Nat.add_assoc]
        strideFinish (p + 16) (by omega)
      · have ec : elementCount element b start stop = (stop - start) / fixedWidth element := by
          simp [elementCount, fixedSize_eq, hw, wz]
        have cs : (stop - start) / fixedWidth element ≤ stop - start := Nat.div_le_self _ _
        simp only [fixedSize_eq, hw, ite_true, ec, wz]
        lsteps [acc, acc0, te, ae, tag_le_one, nb, bitOf, hw, wz, read_store_apart, Nat.add_assoc]
        strideFinish (p + 16) (by omega)
    · -- Elements of no fixed size: as many as the first offset counts.
      have hw' : hasWidth element = false := by simpa using hw
      have none_ : element.fixedSize = none := by rw [fixedSize_eq, ite_eq_right hw]
      have tIn := tableIn none_
      by_cases sz : stop - start = 0
      · have ec : elementCount element b start stop = 0 := by simp [elementCount, none_, sz]
        rw [ec] at tIn
        simp only [none_, ec]
        lsteps [acc, acc0, te, ae, tag_le_one, nb, bitOf, hw', sz, read_store_apart, Nat.add_assoc]
        offsetsFinish (p + 16)
      · have ec : elementCount element b start stop = offsetAt b start / 4 := by
          simp [elementCount, none_, sz, bytesPerOffset]
        rw [ec] at tIn
        have four := firstIn none_ (by omega)
        have ob := offsetAt_lt b start
        have off : readLE mem (data + start) 4 = UInt64.ofNat (offsetAt b start) :=
          readLE_offset mem data b input.bytes start (by omega)
        have offAcc : w.access (data + start) 4 = true := BranchProof.access_sub input.readable (by omega)
        simp only [none_, ec]
        lsteps [acc, acc0, te, ae, tag_le_one, nb, bitOf, hw', sz, off, offAcc, read_store_apart, read4_store_apart,
          Nat.add_assoc]
        offsetsFinish (p + 16)
  · -- A progressive list: no limit, its count from its encoding, and the count mixed in.
    have t0 : readLE mem p 8 = UInt64.ofNat 9 := (planned.2 0 (by simp [words])).2
    have a0 : w.access p 8 = true := (planned.2 0 (by simp [words])).1
    have pe : PlanAt w mem (p + 24) (words element) := by
      have := planned.right (a := 9 :: Plan.bound bound); simpa [words] using this
    have eSound : element.wellFormed = .ok () := by simpa only [Desc.wellFormed] using sound
    have eThin : narrow element = true := by simpa only [narrow] using thin
    seqFront (p + 24) [t0, a0]
    by_cases basic : element.isBasic = true
    · -- Basic elements: their bytes packed, their count the bytes over the width.
      have ⟨wd, items, hw⟩ := basic_width basic eSound
      have il : element.itemLength ≠ 0 := by simp at items; omega
      have il32 : element.itemLength ≤ 32 := by simp at items; omega
      have ec : elementCount element b start stop = (stop - start) / element.itemLength := by
        simp [elementCount, fixedSize_eq, hw, wd, il]
      have cs : (stop - start) / element.itemLength ≤ stop - start := Nat.div_le_self _ _
      simp only [basic, ite_true, ec]
      packedFinish 0 [il]
    have nb : element.isBasic = false := by simpa using basic
    simp only [nb, Bool.false_eq_true, ite_false]
    by_cases hw : hasWidth element = true
    · -- Fixed-size elements: as many as fit, one width apart.
      have fw := narrow_width element eThin _ (by rw [fixedSize_eq, ite_eq_left hw])
      by_cases wz : fixedWidth element = 0
      · have ec : elementCount element b start stop = 0 := by simp [elementCount, fixedSize_eq, hw, wz]
        simp only [fixedSize_eq, hw, ite_true, ec, wz]
        lsteps [acc, acc0, te, ae, tag_le_one, nb, bitOf, hw, wz, read_store_apart, Nat.add_assoc]
        strideFinish (p + 24) (by omega)
      · have ec : elementCount element b start stop = (stop - start) / fixedWidth element := by
          simp [elementCount, fixedSize_eq, hw, wz]
        have cs : (stop - start) / fixedWidth element ≤ stop - start := Nat.div_le_self _ _
        simp only [fixedSize_eq, hw, ite_true, ec, wz]
        lsteps [acc, acc0, te, ae, tag_le_one, nb, bitOf, hw, wz, read_store_apart, Nat.add_assoc]
        strideFinish (p + 24) (by omega)
    · -- Elements of no fixed size: as many as the first offset counts.
      have hw' : hasWidth element = false := by simpa using hw
      have none_ : element.fixedSize = none := by rw [fixedSize_eq, ite_eq_right hw]
      have tIn := tableIn none_
      by_cases sz : stop - start = 0
      · have ec : elementCount element b start stop = 0 := by simp [elementCount, none_, sz]
        rw [ec] at tIn
        simp only [none_, ec]
        lsteps [acc, acc0, te, ae, tag_le_one, nb, bitOf, hw', sz, read_store_apart, Nat.add_assoc]
        offsetsFinish (p + 24)
      · have ec : elementCount element b start stop = offsetAt b start / 4 := by
          simp [elementCount, none_, sz, bytesPerOffset]
        rw [ec] at tIn
        have four := firstIn none_ (by omega)
        have ob := offsetAt_lt b start
        have off : readLE mem (data + start) 4 = UInt64.ofNat (offsetAt b start) :=
          readLE_offset mem data b input.bytes start (by omega)
        have offAcc : w.access (data + start) 4 = true := BranchProof.access_sub input.readable (by omega)
        simp only [none_, ec]
        lsteps [acc, acc0, te, ae, tag_le_one, nb, bitOf, hw', sz, off, offAcc, read_store_apart, read4_store_apart,
          Nat.add_assoc]
        offsetsFinish (p + 24)

/-- A struct's accepted ranges are one per field. -/
theorem fieldRanges_length {fields : List Desc} {b : ByteArray} {start stop : Nat} {ranges : List (Nat × Nat)}
    (hr : fieldRanges fields b start stop = .ok ranges) : ranges.length = fields.length := by
  by_cases big : offsetBound ≤ stop - start
  · simp [fieldRanges, fieldPlaces, big, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at hr
  by_cases ok : budgetOk fields (stop - start) ∧
      tableOk (placeStarts (placesFrom fields b start 0)) (Desc.leadingWidth fields) (stop - start)
  · rw [fieldRanges_accepted fields b start stop big ok.1 ok.2] at hr
    cases hr
    rw [rangesOf_length, placesFrom_length]
  · exact absurd hr (fieldRanges_refused fields b start stop big ok ranges)

/-- The ranges driver on a struct an accepted encoding holds writes its ranges and answers zero. -/
theorem fields_calls {m : Module} {w : World} (linked : HasCodec m) {sp : Nat} {mem : Memory} {fields : List Desc}
    {data start stop out q : Nat} {b : ByteArray} {ranges : List (Nat × Nat)}
    (hr : fieldRanges fields b start stop = .ok ranges)
    (sound : ∀ f ∈ fields, f.wellFormed = .ok ()) (thin : ∀ f ∈ fields, narrow f = true)
    (total : ∀ width, Desc.fieldsFixedSize fields = some width → width < 2 ^ 62)
    (leadSmall : Desc.leadingWidth fields < 2 ^ 62) (plan : PlanAt w mem q (wordsAll fields))
    (planApart : q + 8 * (wordsAll fields).length ≤ out ∨ out + 8 * (1 + 2 * fields.length) ≤ q)
    (at_ : ViewMemory w mem data b out fields.length) (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (room : w.stackLo + 8 + 8 * fieldsView.frame + fieldsRoom fields ≤ sp) :
    Calls m w "ssz_fields_ranges" sp [UInt64.ofNat q, UInt64.ofNat data, UInt64.ofNat start, UInt64.ofNat stop,
      UInt64.ofNat fields.length, UInt64.ofNat out] mem 0 (viewed out ranges mem) := by
  have := fields_ok m w linked sp mem fields data start stop out fields.length q b sound thin total leadSmall plan
    planApart at_ ordered inside room
  rw [hr] at this
  simpa [viewOutcome, fieldRanges_length hr] using this

/-- A word below a view's output reads as it did before the view was written. -/
theorem read_viewed_far (out : Nat) (ranges : List (Nat × Nat)) (mem : Memory) (a : Nat) (h : a + 8 ≤ out) :
    readLE (viewed out ranges mem) a 8 = readLE mem a 8 :=
  readLE_congr _ _ a 8 fun k _ => wordsAt_far out _ _ mem (1 + 2 * ranges.length) (a + k)
    (fun _ hk => by simpa using hk) (.inl (by omega))

/-- A byte outside a view's output is as it was before the view was written. -/
theorem viewed_far (out : Nat) (ranges : List (Nat × Nat)) (mem : Memory) (x : Nat)
    (h : x < out ∨ out + 8 * (1 + 2 * ranges.length) ≤ x) : viewed out ranges mem x = mem x :=
  wordsAt_far out _ _ mem (1 + 2 * ranges.length) x (fun _ hk => by simpa using hk) h

/-- A word outside a view's output reads as it did before the view was written. -/
theorem read_viewed_apart (out : Nat) (ranges : List (Nat × Nat)) (mem : Memory) (a : Nat)
    (h : a + 8 ≤ out ∨ out + 8 * (1 + 2 * ranges.length) ≤ a) :
    readLE (viewed out ranges mem) a 8 = readLE mem a 8 :=
  readLE_congr _ _ a 8 fun k _ => viewed_far out ranges mem (a + k) (by omega)

/-- A word outside the bytes a loop wrote reads as it did before the loop. -/
theorem read_frame {mem mem0 : Memory} {lo hi : Nat} (frame : ∀ x, ¬ (lo ≤ x ∧ x < hi) → mem x = mem0 x) (a : Nat)
    (h : a + 8 ≤ lo ∨ hi ≤ a) : readLE mem a 8 = readLE mem0 a 8 :=
  readLE_congr _ _ a 8 fun k _ => frame _ (by omega)

/-- Reads a word of a struct's record back through the stores and the view that wrote it. -/
macro "rdv" : tactic =>
  `(tactic| (simp (disch := omega) only [read_store_apart, readLE_store8, read_viewed_far]; try rfl))

/-- A view's range words, read back from its output. -/
theorem read_viewed (out : Nat) (ranges : List (Nat × Nat)) (mem : Memory) (k : Nat) (h : k < ranges.length) :
    readLE (viewed out ranges mem) (out + 8 + 16 * k) 8 = UInt64.ofNat ranges[k].1 ∧
      readLE (viewed out ranges mem) (out + 16 + 16 * k) 8 = UInt64.ofNat ranges[k].2 := by
  have ⟨one, two⟩ := viewWord_get ranges k h
  constructor
  · have := readLE_wordsAt out (viewWord ranges) (fun j => decide (j < 1 + 2 * ranges.length)) mem (1 + 2 * k)
      (by simp; omega)
    rw [show out + 8 * (1 + 2 * k) = out + 8 + 16 * k by omega, one] at this
    exact this
  · have := readLE_wordsAt out (viewWord ranges) (fun j => decide (j < 1 + 2 * ranges.length)) mem (2 + 2 * k)
      (by simp; omega)
    rw [show out + 8 * (2 + 2 * k) = out + 16 + 16 * k by omega, two] at this
    exact this

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
/-- A struct's record: one leaf per field, each field's range in the table after the record. -/
theorem layout_struct {m : Module} {w : World} (linked : HasCodec m)
    (hf : m.fns.lookup "ssz_prove_layout" = some ProveLayout.fn) {sp : Nat} {mem : Memory} {names : List String}
    {fields : List Desc} {b : ByteArray}
    (room : w.stackLo + 8 + 8 * ProveLayout.fn.frame + (8 + 8 * fieldsView.frame + fieldsRoom fields) ≤ sp)
    {p data start stop lay : Nat} {layout : EncodedLayout}
    (laid : layoutOf (.container names fields) b start stop = .ok layout)
    (input : LayoutInput w mem (.container names fields) b p data start stop lay)
    (sound : (Desc.container names fields).wellFormed = .ok ()) (thin : narrow (.container names fields) = true)
    (leadSmall : Desc.leadingWidth fields < 2 ^ 62) :
    ∃ mem', Calls m w "ssz_prove_layout" sp [UInt64.ofNat p, UInt64.ofNat data, UInt64.ofNat start,
      UInt64.ofNat stop, UInt64.ofNat lay] mem 0 mem' ∧
      LayoutDone w mem mem' (.container names fields) p lay data b layout := by
  have planned := input.planned
  have pb := planned.1
  simp only [addressBound] at pb
  have ordered := input.ordered
  have inside := input.inside
  have small := input.small
  have db := BranchProof.access_bound input.readable
  have apart := input.planApart
  have writable := input.writable
  have dapart := input.dataApart
  simp only [recordBytes, layoutBytes] at apart writable dapart
  simp only [words, List.length_append, List.length_cons, List.length_nil] at apart pb
  have lb := BranchProof.access_bound writable
  have acc : ∀ k, k + 8 ≤ 144 → w.access (lay + k) 8 = true := fun k hk => BranchProof.access_sub writable (by omega)
  have acc0 : w.access lay 8 = true := BranchProof.access_prefix writable (by omega)
  have t0 : readLE mem p 8 = UInt64.ofNat 10 := (planned.2 0 (by simp [words])).2
  have a0 : w.access p 8 = true := (planned.2 0 (by simp [words])).1
  have t8 : readLE mem (p + 8) 8 = UInt64.ofNat fields.length := (planned.2 1 (by simp [words])).2
  have a8 : w.access (p + 8) 8 = true := (planned.2 1 (by simp [words])).1
  have pf : PlanAt w mem (p + 16) (wordsAll fields) := by
    have := planned.right (a := [10, fields.length]); simpa [words] using this
  have fieldsSound := allWellFormed_mem _ (wellFormed_container sound)
  have fieldsThin := narrow_mem _ (by simp only [narrow, Bool.and_eq_true] at thin; exact thin.2)
  have total : ∀ width, Desc.fieldsFixedSize fields = some width → width < 2 ^ 62 := fun width fixed => by
    simp only [narrow, Bool.and_eq_true] at thin; simpa [Desc.fixedSize, fixed] using thin.1
  simp only [layoutOf, bind, Except.bind] at laid
  cases hr : fieldRanges fields b start stop with
  | error e => simp [hr] at laid
  | ok ranges =>
  simp only [hr, pure, Except.pure, Except.ok.injEq] at laid
  subst laid
  have len := fieldRanges_length hr
  have tb : w.access (lay + 144) (8 + 16 * fields.length) = true := BranchProof.access_sub writable (by omega)
  have acc144 : w.access (lay + 144) 8 = true := BranchProof.access_prefix tb (by omega)
  have fl := wordsAll_length_ge fields
  have room' : w.stackLo + 8 + 8 * fieldsView.frame + fieldsRoom fields ≤ sp - 8 - 8 * ProveLayout.fn.frame := by
    omega
  refine calls_of_wp hf (by omega) rfl ?_
  simp only [ProveLayout.fn, ProveLayout.fields, List.cons_append, List.nil_append]
  lsteps [acc, acc0, acc144, t0, a0, t8, a8, read_store_apart, Nat.add_assoc]
  -- The field ranges, written by the codec's view into the table after the record.
  refine Wp.call (values := [UInt64.ofNat (p + 16), UInt64.ofNat data, UInt64.ofNat start, UInt64.ofNat stop,
      UInt64.ofNat fields.length, UInt64.ofNat (lay + 144)]) (by wev [])
    (fields_calls linked hr fieldsSound fieldsThin total leadSmall
      (PlanAt.frame pf fun a h1 h2 => by simp (disch := omega) only [store_out, Validate.toNat_ofNat_lt, Width.bytes])
      (by omega)
      ⟨fun k hk => by rw [← input.bytes k hk]; simp (disch := omega) only [store_out, Validate.toNat_ofNat_lt,
          Width.bytes], input.readable,
        by simp (disch := omega) only [Validate.toNat_ofNat_lt, Width.bytes, read_store_apart, readLE_store8],
        by omega, tb, by omega⟩ ordered inside room') ?_
  lsteps [acc, read_store_apart, Nat.add_assoc]
  refine ⟨rfl, ?_⟩
  simp (disch := omega) only [Validate.toNat_ofNat_lt, Width.bytes, layoutBytes]
  refine ⟨⟨?_, ?_, fun c hc => ?_, ?_, fun y hy => ?_, ?_, ?_⟩, ?_, fun a ha => ?_⟩
  · simp only [EncodedLayout.count, Slots.count, List.length_map, List.length_zip, len, Nat.min_self]; rdv
  · rdv
  · cases hc; rdv
  · rdv
  · cases hy
  · rdv
  · refine LeavesAt.nested _ (Held.struct fields ranges (p + 16) (by rdv) (by rdv) (by rdv)
      (PlanAt.frame pf fun a h1 h2 => by simp (disch := omega) only [store_out, viewed_far])
      ⟨by omega, by simp only [words, Validate.bound_length, List.length_append, List.length_cons, List.length_nil,
          List.length_map]; omega⟩
      (by simp only [recordBytes, layoutBytes]; omega) len tb
      (fun k h => ?_) fieldsSound (by simp [Desc.nesting])) fun e s wd c h => by cases h
    -- Each field's range, read from the table the view wrote.
    constructor
    · simp (disch := omega) only [read_store_apart]
      rw [show lay + 152 + 16 * k = lay + 144 + 8 + 16 * k by omega]
      exact (read_viewed (lay + 144) ranges _ k h).1
    · simp (disch := omega) only [read_store_apart]
      rw [show lay + 160 + 16 * k = lay + 144 + 16 + 16 * k by omega]
      exact (read_viewed (lay + 144) ranges _ k h).2
  · rdv
    try (simp only [recordBytes, layoutBytes]; congr 1; omega)
  · simp only [recordBytes, layoutBytes] at ha
    simp (disch := omega) only [store_out, viewed_far]

/-- Byte j of a layout's node once its first i positions are set in, one bit per set position. -/
def layoutByte (active : List Bool) (j : Nat) : Nat → UInt8
  | 0 => 0
  | i + 1 => layoutByte active j i |||
    (if i / 8 = j ∧ active.getD i false = true then (1 : UInt8) <<< UInt8.ofNat (i % 8) else 0)

/-- No position before a byte's first sets a bit in it. -/
theorem layoutByte_before (active : List Bool) (j : Nat) : ∀ i, i ≤ 8 * j → layoutByte active j i = 0
  | 0, _ => rfl
  | i + 1, h => by
    simp only [layoutByte, layoutByte_before active j i (by omega), show ¬ i / 8 = j by omega, false_and, ite_false]
    decide

/-- A byte's bits from its first position on, as the node's definition folds them. -/
theorem layoutByte_within (active : List Bool) (j : Nat) : ∀ t, t ≤ 8 →
    layoutByte active j (8 * j + t) = (List.range t).foldl (fun acc bit =>
      if active.getD (8 * j + bit) false then acc ||| ((1 : UInt8) <<< UInt8.ofNat bit) else acc) 0
  | 0, _ => layoutByte_before active j _ (by omega)
  | t + 1, h => by
    rw [show 8 * j + (t + 1) = (8 * j + t) + 1 by omega, layoutByte, layoutByte_within active j t (by omega),
      List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, show (8 * j + t) / 8 = j by omega, show (8 * j + t) % 8 = t by omega,
      true_and]
    split <;> simp

/-- No position past a byte's last sets a bit in it. -/
theorem layoutByte_after (active : List Bool) (j : Nat) : ∀ i, 8 * j + 8 ≤ i →
    layoutByte active j i = layoutByte active j (8 * j + 8)
  | 0, h => by omega
  | i + 1, h => by
    rcases Nat.lt_or_ge i (8 * j + 8) with lt | ge
    · rw [show i + 1 = 8 * j + 8 by omega]
    · simp only [layoutByte, layoutByte_after active j i ge, show ¬ i / 8 = j by omega, false_and, ite_false]
      simp

/-- No position past the layout's end sets a bit. -/
theorem layoutByte_past (active : List Bool) (j : Nat) (i : Nat) (h : active.length ≤ i) :
    ∀ n, layoutByte active j (i + n) = layoutByte active j i
  | 0 => rfl
  | n + 1 => by
    rw [show i + (n + 1) = (i + n) + 1 by omega, layoutByte, layoutByte_past active j i h n]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show active.length ≤ i + n by omega)]

/-- Once every position is set in, a byte is the layout node's byte. -/
theorem layoutByte_node (active : List Bool) (j : Nat) (hj : j < 32) (short : active.length ≤ 256) :
    layoutByte active j active.length = (activeFieldsNode active).data[j]'(by simp [activeFieldsNode]; omega) := by
  rw [← layoutByte_past active j active.length (Nat.le_refl _) (256 - active.length),
    show active.length + (256 - active.length) = 256 by omega, layoutByte_after active j 256 (by omega),
    layoutByte_within active j 8 (Nat.le_refl _)]
  simp [activeFieldsNode]

/-- Every byte joined with a power of two below 256, as the driver joins them in a word, keeps its low byte. -/
theorem byte_or_table : ∀ n < 256, ∀ t < 8,
    (UInt64.ofNat n ||| UInt64.ofNat (2 ^ t)).toUInt8 = UInt8.ofNat n ||| ((1 : UInt8) <<< UInt8.ofNat t) := by
  decide +kernel

/-- A byte joined with a power of two below 256, as the driver joins them in a word, keeps its low byte. -/
theorem byte_or (x : UInt8) (t : Nat) (ht : t < 8) :
    (UInt64.ofNat x.toNat ||| UInt64.ofNat (2 ^ t)).toUInt8 = x ||| ((1 : UInt8) <<< UInt8.ofNat t) := by
  have := byte_or_table x.toNat x.toNat_lt t ht
  rwa [UInt8.ofNat_toNat] at this

/-- One byte read as a word. -/
theorem read1 (mem : Memory) (a : Nat) : readLE mem a 1 = UInt64.ofNat (mem a).toNat := by
  apply UInt64.toNat_inj.mp
  simp [readLE]

set_option maxHeartbeats 4000000 in
/--
The progressive struct's loop sets one bit of the mixed-in word per set position of its layout, from the lowest.

It ends with each byte of the word as the layout's node has it, every other byte and every variable but the index and
the power of two as they were.
-/
theorem active_loop {m : Module} {w : World} {sp : Nat} {env0 : Env} {mem0 : Memory} {rest : List Stmt}
    {Q : Env → Memory → Prop} {active : List Bool} {lay bits : Nat} (short : active.length ≤ 256)
    (lb : lay + 72 ≤ 2 ^ 63) (h4 : env0 4 = UInt64.ofNat lay) (h17 : env0 17 = UInt64.ofNat bits)
    (h20 : env0 20 = UInt64.ofNat active.length) (h19 : env0 19 = 0) (h16 : env0 16 = 1)
    (zeroed : ∀ j < 32, mem0 (lay + 40 + j) = 0) (writable : ∀ j < 32, w.access (lay + 40 + j) 1 = true)
    (set : ∀ k (h : k < active.length), w.access (bits + 8 * k) 8 = true ∧
      readLE mem0 (bits + 8 * k) 8 = if active[k] then 1 else 0)
    (bb : bits + 8 * active.length ≤ 2 ^ 63) (apart : bits + 8 * active.length ≤ lay + 40 ∨ lay + 72 ≤ bits)
    (k : ∀ env mem, (∀ i, i ≠ 19 → i ≠ 16 → env i = env0 i) →
      (∀ x, ¬ (lay + 40 ≤ x ∧ x < lay + 72) → mem x = mem0 x) →
      (∀ j < 32, mem (lay + 40 + j) = layoutByte active j active.length) → Wp m w sp (.block rest) env mem Q) :
    Wp m w sp (.block (while_ (lt ProveLayout.i ProveLayout.k &&& lt ProveLayout.i 256) [
      when (ne (ld (ProveLayout.bits + 8 * ProveLayout.i)) 0)
        [st1 (ProveLayout.lay + 40 + ProveLayout.i / 8) (ld1 (ProveLayout.lay + 40 + ProveLayout.i / 8) |||
          ProveLayout.pw)],
      ProveLayout.i ::= ProveLayout.i + 1,
      ifElse (eq (ProveLayout.i % 8) 0) [ProveLayout.pw ::= 1] [ProveLayout.pw ::= ProveLayout.pw + ProveLayout.pw]]
      :: rest)) env0 mem0 Q := by
  refine Wp.loop (wp_loop (fun env mem => ∃ i, i ≤ active.length ∧ env 19 = UInt64.ofNat i ∧
      env 16 = UInt64.ofNat (2 ^ (i % 8)) ∧ (∀ x, x ≠ 19 → x ≠ 16 → env x = env0 x) ∧
      (∀ x, ¬ (lay + 40 ≤ x ∧ x < lay + 72) → mem x = mem0 x) ∧
      ∀ j < 32, mem (lay + 40 + j) = layoutByte active j i)
    (fun env _ => active.length - (env 19).toNat)
    ⟨0, Nat.zero_le _, by simpa using h19, by simpa using h16, fun _ _ _ => rfl, fun _ _ => rfl,
      fun j hj => by rw [zeroed j hj]; rfl⟩ ?_)
  rintro env mem ⟨i, hi, e19, e16, same, frame, bytes⟩
  have s4 := same 4 (by decide) (by decide)
  have s17 := same 17 (by decide) (by decide)
  have s20 := same 20 (by decide) (by decide)
  rw [h4] at s4
  rw [h17] at s17
  rw [h20] at s20
  refine ⟨_, by wev [e19, s20], fun go => ?_, fun stop => ?_⟩
  · have more : i < active.length := by
      rcases Nat.lt_or_ge i active.length with h | h
      · exact h
      · simp [show ¬ i < active.length by omega] at go
    have ⟨bAcc, bVal⟩ := set i more
    -- The layout's word for this position, which the bytes written so far miss.
    have bit : readLE mem (bits + 8 * i) 8 = if active[i] then 1 else 0 := by
      rw [← bVal]
      exact readLE_congr _ _ _ 8 fun t ht => frame _ (by omega)
    have t8 : i % 8 < 8 := Nat.mod_lt _ (by decide)
    have p8 : 2 ^ (i % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have j32 : i / 8 < 32 := by omega
    have byteRead : readLE mem (lay + 40 + i / 8) 1 = UInt64.ofNat (layoutByte active (i / 8) i).toNat := by
      rw [read1, bytes _ j32]
    have byteAcc := writable _ j32
    -- The power of two for the next position: back to one at a byte's start, doubled otherwise.
    have twice : (i + 1) % 8 ≠ 0 → UInt64.ofNat (2 ^ (i % 8)) + UInt64.ofNat (2 ^ (i % 8)) =
        UInt64.ofNat (2 ^ ((i + 1) % 8)) := fun z => by
      rw [show (i + 1) % 8 = i % 8 + 1 by omega, Nat.pow_succ, Validate.ofNat_add_ofNat]
      congr 1
      omega
    have onePow : (i + 1) % 8 = 0 → (1 : UInt64) = UInt64.ofNat (2 ^ ((i + 1) % 8)) := fun z => by rw [z]; rfl
    have unchanged : ∀ j, j ≠ i / 8 → layoutByte active j (i + 1) = layoutByte active j i := fun j hj => by
      simp [layoutByte, Ne.symm hj]
    by_cases on : active[i] = true
    · simp only [on, ite_true] at bit
      have grown : layoutByte active (i / 8) (i + 1) =
          layoutByte active (i / 8) i ||| ((1 : UInt8) <<< UInt8.ofNat (i % 8)) := by
        simp [layoutByte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem more, on]
      lsteps [s4, s17, e19, e16, bit, bAcc, byteRead, byteAcc]
      rcases Decidable.em ((i + 1) % 8 = 0) with z | z
      all_goals
        lsteps [z]
        refine ⟨⟨i + 1, by omega, by wev [], by wev [z, onePow, twice, e16], fun x a b => by wonly [a, b, same x a b],
          fun x hx => by rw [store_out (by simp [Width.bytes]; omega)]; exact frame x hx, fun j hj => ?_⟩, ?_⟩
        · by_cases at_ : j = i / 8
          · subst at_
            rw [store_in (by simp [Width.bytes]; omega), grown, show lay + 40 + i / 8 - (UInt64.ofNat (lay + 40 + i / 8)).toNat = 0 by
              rw [Validate.toNat_ofNat_lt (by omega)]; omega]
            simp only [qwordByte, Nat.mul_zero, Nat.toUInt64_eq]
            have sh : ∀ x : UInt64, x >>> UInt64.ofNat 0 = x := fun x => UInt64.toNat_inj.mp (by simp)
            rw [sh, byte_or _ _ t8]
          · rw [store_out (by simp [Width.bytes]; omega), unchanged j at_]
            exact bytes j hj
        · wonly [e19]
          omega
    · simp only [on, Bool.false_eq_true, ite_false] at bit
      lsteps [s4, s17, e19, e16, bit, bAcc]
      rcases Decidable.em ((i + 1) % 8 = 0) with z | z
      all_goals
        lsteps [z]
        refine ⟨⟨i + 1, by omega, by wev [], by wev [z, onePow, twice, e16], fun x a b => by wonly [a, b, same x a b],
          frame, fun j hj => ?_⟩, ?_⟩
        · rw [bytes j hj]
          simp [layoutByte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem more, on]
        · wonly [e19]
          omega
  · -- The loop ends past the last position.
    have done : i = active.length := by
      rcases Nat.lt_or_ge i active.length with h | h
      · simp [h, show i < 256 by omega] at stop
      · omega
    subst done
    exact k env mem same frame bytes

/-- A view's count word, read back from its output. -/
theorem read_viewed_count (out : Nat) (ranges : List (Nat × Nat)) (mem : Memory) :
    readLE (viewed out ranges mem) out 8 = UInt64.ofNat ranges.length := by
  have := readLE_wordsAt out (viewWord ranges) (fun j => decide (j < 1 + 2 * ranges.length)) mem 0 (by simp; omega)
  simpa [viewWord, viewed] using this

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 16000000 in
/--
A progressive struct's record: its fields placed at the set positions of its layout, each range in the table after
the record, and the layout mixed in as a node.
-/
theorem layout_progressive {m : Module} {w : World} (linked : HasCodec m)
    (hf : m.fns.lookup "ssz_prove_layout" = some ProveLayout.fn) {sp : Nat} {mem : Memory} {active : List Bool}
    {names : List String} {fields : List Desc} {b : ByteArray}
    (room : w.stackLo + 8 + 8 * ProveLayout.fn.frame + (8 + 8 * fieldsView.frame + fieldsRoom fields) ≤ sp)
    {p data start stop lay : Nat} {layout : EncodedLayout}
    (laid : layoutOf (.progressiveContainer active names fields) b start stop = .ok layout)
    (input : LayoutInput w mem (.progressiveContainer active names fields) b p data start stop lay)
    (sound : (Desc.progressiveContainer active names fields).wellFormed = .ok ())
    (thin : narrow (.progressiveContainer active names fields) = true)
    (leadSmall : Desc.leadingWidth fields < 2 ^ 62) :
    ∃ mem', Calls m w "ssz_prove_layout" sp [UInt64.ofNat p, UInt64.ofNat data, UInt64.ofNat start,
      UInt64.ofNat stop, UInt64.ofNat lay] mem 0 mem' ∧
      LayoutDone w mem mem' (.progressiveContainer active names fields) p lay data b layout := by
  have planned := input.planned
  have pb := planned.1
  simp only [addressBound] at pb
  have ordered := input.ordered
  have inside := input.inside
  have small := input.small
  have db := BranchProof.access_bound input.readable
  have apart := input.planApart
  have writable := input.writable
  have dapart := input.dataApart
  have short := (wellFormed_progressiveContainer_layout sound).2
  simp only [maxActiveFields] at short
  simp only [recordBytes, layoutBytes] at apart writable dapart
  simp only [words, List.length_append, List.length_cons, List.length_nil, List.length_map] at apart pb
  have lb := BranchProof.access_bound writable
  have acc : ∀ k, k + 8 ≤ 144 → w.access (lay + k) 8 = true := fun k hk => BranchProof.access_sub writable (by omega)
  have acc0 : w.access lay 8 = true := BranchProof.access_prefix writable (by omega)
  -- The plan: the tag, the layout's length and words, the field count, then the fields.
  have shape : words (.progressiveContainer active names fields) =
      ([11, active.length] ++ active.map (fun b => if b then 1 else 0)) ++ ([fields.length] ++ wordsAll fields) := by
    simp [words]
  rw [shape] at planned
  have t0 : readLE mem p 8 = UInt64.ofNat 11 := (planned.2 0 (by simp)).2
  have a0 : w.access p 8 = true := (planned.2 0 (by simp)).1
  have t8 : readLE mem (p + 8) 8 = UInt64.ofNat active.length := (planned.2 1 (by simp)).2
  have a8 : w.access (p + 8) 8 = true := (planned.2 1 (by simp)).1
  have layoutWords : ∀ k (h : k < active.length), w.access (p + 16 + 8 * k) 8 = true ∧
      readLE mem (p + 16 + 8 * k) 8 = if active[k] then 1 else 0 := fun k h => by
    have := planned.2 (2 + k) (by simp; try omega)
    rw [show p + 8 * (2 + k) = p + 16 + 8 * k by omega] at this
    refine ⟨this.1, ?_⟩
    rw [this.2, List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp)]
    simp only [List.length_cons, List.length_nil, List.getElem_map, show 2 + k - 2 = k by omega]
    split <;> rfl
  have tail := planned.right
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map] at tail
  have tc : readLE mem (p + 16 + 8 * active.length) 8 = UInt64.ofNat fields.length := by
    have := (tail.2 0 (by simp)).2
    rw [show p + 8 * (1 + 1 + active.length) + 8 * 0 = p + 16 + 8 * active.length by omega] at this
    exact this
  have tca : w.access (p + 16 + 8 * active.length) 8 = true := by
    have := (tail.2 0 (by simp)).1
    rwa [show p + 8 * (1 + 1 + active.length) + 8 * 0 = p + 16 + 8 * active.length by omega] at this
  have pf : PlanAt w mem (p + 16 + 8 * active.length + 8) (wordsAll fields) := by
    have := tail.right (a := [fields.length])
    simp only [List.length_cons, List.length_nil] at this
    rw [show p + 16 + 8 * active.length + 8 = p + 8 * (1 + 1 + active.length) + 8 * 1 by omega]
    exact this
  have fieldsSound := allWellFormed_mem _ (wellFormed_progressiveContainer sound)
  have fieldsThin := narrow_mem _ (by simp only [narrow, Bool.and_eq_true] at thin; exact thin.2)
  have total : ∀ width, Desc.fieldsFixedSize fields = some width → width < 2 ^ 62 := fun width fixed => by
    simp only [narrow, Bool.and_eq_true] at thin; simpa [Desc.fixedSize, fixed] using thin.1
  simp only [layoutOf, bind, Except.bind] at laid
  cases hr : fieldRanges fields b start stop with
  | error e => simp [hr] at laid
  | ok ranges =>
  simp only [hr, pure, Except.pure, Except.ok.injEq] at laid
  subst laid
  have len := fieldRanges_length hr
  have tb : w.access (lay + 144) (8 + 16 * fields.length) = true := BranchProof.access_sub writable (by omega)
  have acc144 : w.access (lay + 144) 8 = true := BranchProof.access_prefix tb (by omega)
  have fl := wordsAll_length_ge fields
  have room' : w.stackLo + 8 + 8 * fieldsView.frame + fieldsRoom fields ≤ sp - 8 - 8 * ProveLayout.fn.frame := by
    omega
  refine calls_of_wp hf (by omega) rfl ?_
  simp only [ProveLayout.fn, ProveLayout.fields, ProveLayout.activeWord, zero32, List.range, List.range.loop,
    List.map, List.cons_append, List.nil_append, List.append_assoc]
  lsteps [acc, acc0, acc144, t0, a0, t8, a8, tc, tca, read_store_apart]
  -- The field ranges, written by the codec's view into the table after the record.
  refine Wp.call (values := [UInt64.ofNat (p + 16 + 8 * active.length + 8), UInt64.ofNat data, UInt64.ofNat start,
      UInt64.ofNat stop, UInt64.ofNat fields.length, UInt64.ofNat (lay + 144)]) (by wev [])
    (fields_calls linked hr fieldsSound fieldsThin total leadSmall
      (PlanAt.frame pf fun a h1 h2 => by simp (disch := omega) only [store_out, Validate.toNat_ofNat_lt, Width.bytes])
      (by omega)
      ⟨fun k hk => by rw [← input.bytes k hk]; simp (disch := omega) only [store_out, Validate.toNat_ofNat_lt,
          Width.bytes], input.readable,
        by simp (disch := omega) only [Validate.toNat_ofNat_lt, Width.bytes, read_store_apart, readLE_store8],
        by omega, tb, by omega⟩ ordered inside room') ?_
  lsteps [acc, read_store_apart, Nat.add_assoc]
  -- The layout's word, one bit per set position.
  refine active_loop (active := active) (lay := lay) (bits := p + 16) short (by omega) (by wev []) (by wev [])
    (by wev []) (by wev []) (by wev []) (fun j hj => ?_)
    (fun j hj => by rw [Nat.add_assoc]; exact BranchProof.access_sub writable (by omega))
    (fun k hk => ⟨(layoutWords k hk).1, ?_⟩) (by omega) (by omega) fun env memL same frame bytes => ?_
  · rcases (show j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) ∨ 24 ≤ j by omega) with r | r | r | r <;>
      simp (disch := omega) only [store_out, store_in, Validate.toNat_ofNat_lt, Width.bytes] <;> simp [qwordByte]
  · simp (disch := omega) only [read_store_apart, read_viewed_apart, Validate.toNat_ofNat_lt, Width.bytes]
    exact (layoutWords k hk).2
  have rdf := read_frame frame
  lsteps [same, acc]
  refine ⟨rfl, ?_⟩
  simp (disch := omega) only [Validate.toNat_ofNat_lt, Width.bytes, layoutBytes]
  refine ⟨⟨?_, ?_, fun c hc => ?_, ?_, fun y hy => ?_, ?_, ?_⟩, ?_, fun a ha => ?_⟩
  · simp only [EncodedLayout.count, Slots.count, placed_length]
    simp (disch := omega) only [read_store_apart, rdf, readLE_store8, read_viewed_apart, Validate.toNat_ofNat_lt,
      Width.bytes]
    try rfl
  · simp (disch := omega) only [read_store_apart, rdf, readLE_store8, read_viewed_apart, Validate.toNat_ofNat_lt,
      Width.bytes]
    try rfl
  · cases hc
  · simp (disch := omega) only [read_store_apart, rdf, readLE_store8, read_viewed_apart, Validate.toNat_ofNat_lt,
      Width.bytes]
    try rfl
  · -- The layout's node, byte by byte as the loop left it.
    cases hy
    apply ByteArray.ext
    apply Array.ext (by simp [BranchProof.readNode, activeFieldsNode])
    intro i h1 _
    have hi : i < 32 := by simpa [BranchProof.readNode] using h1
    simp only [BranchProof.readNode, Array.getElem_ofFn]
    rw [store_out (by omega), bytes i hi, layoutByte_node active i hi short]
  · simp (disch := omega) only [read_store_apart, rdf, readLE_store8, read_viewed_apart, Validate.toNat_ofNat_lt,
      Width.bytes]
  · -- The fields at the layout's set positions, each range from the table the view wrote.
    refine LeavesAt.nested _ (Held.progressive active fields ranges (p + 16 + 8 * active.length + 8) (p + 16)
      (by simp (disch := omega) only [read_store_apart, rdf, readLE_store8, read_viewed_apart, Validate.toNat_ofNat_lt, Width.bytes]; try rfl) (by simp (disch := omega) only [read_store_apart, rdf, readLE_store8, read_viewed_apart, Validate.toNat_ofNat_lt, Width.bytes]; try rfl) (by simp (disch := omega) only [read_store_apart, rdf, readLE_store8, read_viewed_apart, Validate.toNat_ofNat_lt, Width.bytes]; try rfl)
      (fun k hk => ⟨(layoutWords k hk).1, by simp (disch := omega) only [read_store_apart, rdf, readLE_store8, read_viewed_apart, Validate.toNat_ofNat_lt, Width.bytes]; exact (layoutWords k hk).2⟩) (by omega)
      (by simp (disch := omega) only [read_store_apart, rdf, readLE_store8, read_viewed_apart, Validate.toNat_ofNat_lt, Width.bytes]; rw [read_viewed_count, len]) (by simp (disch := omega) only [read_store_apart, rdf, readLE_store8, read_viewed_apart, Validate.toNat_ofNat_lt, Width.bytes]; try rfl)
      (PlanAt.frame pf fun a h1 h2 => by
        rw [store_out (by simp [Width.bytes]; omega), frame a (by omega)]
        simp (disch := omega) only [store_out, viewed_far, Validate.toNat_ofNat_lt, Width.bytes])
      ⟨by omega, by simp only [words, Validate.bound_length, List.length_append, List.length_cons, List.length_nil,
          List.length_map]; omega⟩
      (by simp only [recordBytes, layoutBytes]; omega)
      ⟨by omega, by simp only [words, List.length_append, List.length_cons, List.length_nil, List.length_map]; omega⟩
      len tb (fun k h => ?_) fieldsSound (by simp [Desc.nesting])) fun e s wd c h => by cases h
    constructor
    · simp (disch := omega) only [read_store_apart, rdf, Validate.toNat_ofNat_lt, Width.bytes]
      rw [show lay + 152 + 16 * k = lay + 144 + 8 + 16 * k by omega]
      exact (read_viewed (lay + 144) ranges _ k h).1
    · simp (disch := omega) only [read_store_apart, rdf, Validate.toNat_ofNat_lt, Width.bytes]
      rw [show lay + 160 + 16 * k = lay + 144 + 16 + 16 * k by omega]
      exact (read_viewed (lay + 144) ranges _ k h).2
  · simp (disch := omega) only [read_store_apart, rdf, readLE_store8, read_viewed_apart, Validate.toNat_ofNat_lt,
      Width.bytes]
    try (simp only [recordBytes, layoutBytes]; congr 1; omega)
  · simp only [recordBytes, layoutBytes] at ha
    rw [store_out (by simp [Width.bytes]; omega), frame a (by omega)]
    simp (disch := omega) only [store_out, viewed_far, Validate.toNat_ofNat_lt, Width.bytes]

set_option maxHeartbeats 4000000 in
/--
The union's loop walks the options, past each one whose selector is not the encoding's, to the first one whose is.

It ends at the option the selector names, with its plan node, every other variable and the memory as they were.
-/
theorem union_loop {m : Module} {w : World} (linked : HasCodec m) {sp : Nat} {env0 : Env} {mem0 : Memory}
    {rest : List Stmt} {Q : Env → Memory → Prop} {selectors : List Nat} {options : List Desc} {option : Desc}
    {p s : Nat} (same : selectors.length = options.length)
    (h0 : env0 0 = UInt64.ofNat p) (h9 : env0 9 = UInt64.ofNat options.length) (h24 : env0 24 = UInt64.ofNat s)
    (h18 : env0 18 = UInt64.ofNat (p + 16 + 8 * options.length)) (h19 : env0 19 = 0) (h21 : env0 21 = 0)
    (sels : ∀ k (h : k < selectors.length), w.access (p + 16 + 8 * k) 8 = true ∧
      readLE mem0 (p + 16 + 8 * k) 8 = UInt64.ofNat selectors[k])
    (fits : ∀ k (h : k < selectors.length), selectors[k] < 2 ^ 64) (ss : s < 2 ^ 64)
    (plans : PlanAt w mem0 (p + 16 + 8 * options.length) (wordsAll options))
    (sound : ∀ o ∈ options, o.wellFormed = .ok ())
    (stack : w.stackLo + walkLevel * Desc.deepestNesting options ≤ sp)
    (picked : lookupOption selectors options s = .ok option)
    (k : ∀ env idx (h : idx < options.length), options[idx] = option →
      env 18 = UInt64.ofNat (p + 16 + 8 * options.length + 8 * (wordsAll (options.take idx)).length) →
      (∀ x, x ≠ 18 → x ≠ 19 → x ≠ 21 → env x = env0 x) → Wp m w sp (.block rest) env mem0 Q) :
    Wp m w sp (.block (while_ (lt ProveLayout.i ProveLayout.n &&& eq ProveLayout.found 0) [
      ifElse (eq (ld (ProveLayout.p + 16 + 8 * ProveLayout.i)) ProveLayout.sel) [ProveLayout.found ::= 1]
        [callInto ProveLayout.q "ssz_plan_next" [ProveLayout.q], ProveLayout.i ::= ProveLayout.i + 1]]
      :: rest)) env0 mem0 Q := by
  have pb := plans.1
  simp only [addressBound] at pb
  refine Wp.loop (wp_loop (fun env mem => mem = mem0 ∧ ∃ i, i ≤ options.length ∧ env 19 = UInt64.ofNat i ∧
      env 18 = UInt64.ofNat (p + 16 + 8 * options.length + 8 * (wordsAll (options.take i)).length) ∧
      (∀ j (h : j < i) (h' : j < selectors.length), selectors[j] ≠ s) ∧
      (env 21 = 0 ∨ (env 21 = 1 ∧ ∃ h : i < options.length, selectors[i]'(by omega) = s)) ∧
      ∀ x, x ≠ 18 → x ≠ 19 → x ≠ 21 → env x = env0 x)
    (fun env _ => 2 * (options.length - (env 19).toNat) + (if env 21 = 0 then 1 else 0))
    ⟨rfl, 0, Nat.zero_le _, by simpa using h19, by simpa [wordsAll] using h18, fun j h => by omega, .inl h21,
      fun _ _ _ _ => rfl⟩ ?_)
  rintro env mem ⟨rfl, i, hi, e19, e18, before, state, rest'⟩
  have s0 := rest' 0 (by decide) (by decide) (by decide)
  have s9 := rest' 9 (by decide) (by decide) (by decide)
  have s24 := rest' 24 (by decide) (by decide) (by decide)
  rw [h0] at s0
  rw [h9] at s9
  rw [h24] at s24
  rcases state with z | ⟨one, hlt, hsel⟩
  · refine ⟨_, by wev [e19, s9, z], fun go => ?_, fun stop => ?_⟩
    · have more : i < options.length := by
        rcases Nat.lt_or_ge i options.length with h | h
        · exact h
        · simp [show ¬ i < options.length by omega] at go
      have ⟨sAcc, sVal⟩ := sels i (by omega)
      have sf := fits i (by omega)
      by_cases hit : selectors[i]'(by omega) = s
      · -- The selector matches: the option is found, and the walk stops here.
        wsteps [s0, e19, sAcc, sVal, s24, hit]
        refine ⟨⟨trivial, i, hi, by wev [e19], by wev [e18], before, .inr ⟨by wev [], more, hit⟩,
          fun x a b c => by wonly [a, b, c, rest' x a b c]⟩, ?_⟩
        wonly [e19, z]
        omega
      · -- Another option: its plan node is walked past.
        have ⟨_, here⟩ := field_plan plans more
        have deep := nesting_le_deepest options _ (List.getElem_mem more)
        have more' : walkLevel * options[i].nesting ≤ walkLevel * Desc.deepestNesting options :=
          Nat.mul_le_mul_left _ deep
        wsteps [s0, e19, sAcc, sVal, s24, hit]
        refine Wp.call (values := [UInt64.ofNat (p + 16 + 8 * options.length +
            8 * (wordsAll (options.take i)).length)]) (by wev [e18])
          (next_ok m w linked options[i] (sound _ (List.getElem_mem more)) sp _ _ here (by omega)) ?_
        wsteps [e19]
        have grow := Validate.wordsAll_take_succ options i more
        refine ⟨⟨trivial, i + 1, by omega, by wev [], ?_, fun j h h' => ?_, .inl (by wev [z]),
          fun x a b c => by wonly [a, b, c, rest' x a b c]⟩, ?_⟩
        · rw [grow, List.length_append]
          wonly []
          congr 1
          omega
        · rcases Nat.lt_or_ge j i with h' | h'
          · exact before j h' _
          · simp only [show j = i by omega]; exact hit
        · wonly [e19, z]
          omega
    · -- Every option was walked past, which the selector's lookup refuses.
      have done : i = options.length := by
        rcases Nat.lt_or_ge i options.length with h | h
        · simp [h] at stop
        · omega
      subst done
      rw [lookupOption_none selectors options s same fun j h => before j (by omega) h] at picked
      cases picked
  · refine ⟨_, by wev [e19, s9, one], fun go => ?_, fun _ => ?_⟩
    · simp at go
    · rw [lookupOption_first selectors options s i same (by omega) hsel fun j hj => before j hj _] at picked
      cases picked
      exact k env i hlt rfl e18 rest'

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 8000000 in
/-- A union's record: its selected option, after the selector, as one leaf, and the selector mixed in. -/
theorem layout_union {m : Module} {w : World} (linked : HasCodec m)
    (hf : m.fns.lookup "ssz_prove_layout" = some ProveLayout.fn) {sp : Nat} {mem : Memory} {selectors : List Nat}
    {options : List Desc} {b : ByteArray}
    (room : w.stackLo + 8 + 8 * ProveLayout.fn.frame + walkLevel * Desc.deepestNesting options ≤ sp)
    {p data start stop lay : Nat} {layout : EncodedLayout}
    (laid : layoutOf (.compatibleUnion selectors options) b start stop = .ok layout)
    (input : LayoutInput w mem (.compatibleUnion selectors options) b p data start stop lay)
    (sound : (Desc.compatibleUnion selectors options).wellFormed = .ok ()) (nonempty : start < stop) :
    ∃ mem', Calls m w "ssz_prove_layout" sp [UInt64.ofNat p, UInt64.ofNat data, UInt64.ofNat start,
      UInt64.ofNat stop, UInt64.ofNat lay] mem 0 mem' ∧
      LayoutDone w mem mem' (.compatibleUnion selectors options) p lay data b layout := by
  have planned := input.planned
  have pb := planned.1
  simp only [addressBound] at pb
  have ordered := input.ordered
  have inside := input.inside
  have small := input.small
  have db := BranchProof.access_bound input.readable
  have apart := input.planApart
  have writable := input.writable
  have dapart := input.dataApart
  have same := wellFormed_union_paired sound
  simp only [recordBytes, layoutBytes] at apart writable dapart
  simp only [words, List.length_append, List.length_cons, List.length_nil] at apart pb
  have lb := BranchProof.access_bound writable
  have acc : ∀ k, k + 8 ≤ 144 → w.access (lay + k) 8 = true := fun k hk => BranchProof.access_sub writable (by omega)
  have acc0 : w.access lay 8 = true := BranchProof.access_prefix writable (by omega)
  have shape : words (.compatibleUnion selectors options) = ([12, options.length] ++ selectors) ++ wordsAll options := by
    simp [words]
  rw [shape] at planned
  have t0 : readLE mem p 8 = UInt64.ofNat 12 := (planned.2 0 (by simp)).2
  have a0 : w.access p 8 = true := (planned.2 0 (by simp)).1
  have t8 : readLE mem (p + 8) 8 = UInt64.ofNat options.length := (planned.2 1 (by simp)).2
  have a8 : w.access (p + 8) 8 = true := (planned.2 1 (by simp)).1
  have selWords : ∀ k (h : k < selectors.length), w.access (p + 16 + 8 * k) 8 = true ∧
      readLE mem (p + 16 + 8 * k) 8 = UInt64.ofNat selectors[k] := fun k h => by
    have := planned.2 (2 + k) (by simp; omega)
    rw [show p + 8 * (2 + k) = p + 16 + 8 * k by omega] at this
    refine ⟨this.1, ?_⟩
    rw [this.2, List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp)]
    simp only [List.length_cons, List.length_nil, show 2 + k - (1 + 1) = k by omega]
  have selFits : ∀ k (h : k < selectors.length), selectors[k] < 2 ^ 64 := fun k h =>
    input.fits _ (by simp [words])
  have po : PlanAt w mem (p + 16 + 8 * options.length) (wordsAll options) := by
    have := planned.right
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    rw [show p + 16 + 8 * options.length = p + 8 * (1 + 1 + selectors.length) by omega]
    exact this
  have optionsSound := allWellFormed_mem _ (wellFormed_union sound)
  -- The selector, the first byte of the range.
  generalize hx : (b.get! start).toNat = x
  have xs : x < 256 := hx ▸ UInt8.toNat_lt _
  have selByte : readLE mem (data + start) 1 = UInt64.ofNat x := by rw [read_byte input.bytes (by omega), hx]
  have selAcc : w.access (data + start) 1 = true := BranchProof.access_sub input.readable (by omega)
  simp only [layoutOf, bind, Except.bind, hx] at laid
  cases hl : lookupOption selectors options x with
  | error e => simp [hl] at laid
  | ok option =>
  simp only [hl, pure, Except.pure, Except.ok.injEq] at laid
  subst laid
  have room' : w.stackLo + walkLevel * Desc.deepestNesting options ≤ sp - 8 - 8 * ProveLayout.fn.frame := by omega
  refine calls_of_wp hf (by omega) rfl ?_
  simp only [ProveLayout.fn, ProveLayout.union, ProveLayout.mixCount, lengthNodeAt, List.cons_append,
    List.nil_append]
  lsteps [acc, acc0, t0, a0, t8, a8, selByte, selAcc, read_store_apart, read1_store_apart]
  refine union_loop linked same (by wev []) (by wev []) (by wev []) (by wev []) (by wev []) (by wev [])
    (fun k h => ⟨(selWords k h).1, ?_⟩) selFits (by omega)
    (PlanAt.frame po fun a h1 h2 => by simp (disch := omega) only [store_out, Validate.toNat_ofNat_lt, Width.bytes])
    optionsSound room' hl fun env idx h hopt e18 rest' => ?_
  · simp (disch := omega) only [read_store_apart, Validate.toNat_ofNat_lt, Width.bytes]
    exact (selWords k h).2
  have ⟨_, here⟩ := field_plan po h
  rw [hopt] at here
  have bound : (wordsAll (options.take idx)).length + (words option).length ≤ (wordsAll options).length := by
    have := congrArg List.length (Validate.wordsAll_append (options.take (idx + 1)) (options.drop (idx + 1)))
    rw [List.take_append_drop, Validate.wordsAll_take_succ options idx h, hopt] at this
    simp only [List.length_append] at this
    omega
  lsteps [rest', e18, acc, acc0, read_store_apart, Nat.add_assoc]
  refine ⟨rfl, ?_⟩
  simp (disch := omega) only [Validate.toNat_ofNat_lt, Width.bytes, layoutBytes]
  refine ⟨⟨?_, ?_, fun c hc => ?_, ?_, fun y hy => ?_, ?_, ?_⟩, ?_, fun a ha => ?_⟩
  · simp only [EncodedLayout.count, Slots.count, List.length_cons, List.length_nil]; rd
  · rd
  · cases hc; rd
  · rd
  · cases hy
    countWord
  · rd
  · refine LeavesAt.nested _ (Held.union option (start + 1) stop _ (by rd) (by rd) (by rd) (by rd)
      (by rd; try (congr 1; omega))
      (PlanAt.frame here fun a h1 h2 => by simp (disch := omega) only [store_out])
      ⟨by omega, by simp only [words, Validate.bound_length, List.length_append, List.length_cons, List.length_nil,
          List.length_map]; omega⟩) fun e s wd c h => by cases h
  · rd
  · simp only [recordBytes, layoutBytes] at ha
    simp (disch := omega) only [store_out]

/-- The stack the layout driver needs below its own frame: the plan reads and the field view it calls. -/
def layoutRoom : Desc → Nat
  | .vector element _ | .list element _ | .progressiveList element _ => 112 * (element.nesting + 1)
  | .container _ fields | .progressiveContainer _ _ fields => 8 + 8 * fieldsView.frame + fieldsRoom fields
  | .compatibleUnion _ options => walkLevel * Desc.deepestNesting options
  | _ => 0

/-- What an accepted encoding of a range tells the layout driver, by the type's kind. -/
def LayoutAccepted (d : Desc) (b : ByteArray) (start stop : Nat) : Prop :=
  match d with
  | .bitList _ | .progressiveBitList _ => start < stop ∧ b.get! (stop - 1) ≠ 0
  | .vector _ _ | .list _ _ | .progressiveList _ _ =>
    ∀ element count, sequenceOf b start stop d = some (element, count) → SeqAccepted element start stop count
  | .container _ fields | .progressiveContainer _ _ fields => Desc.leadingWidth fields < 2 ^ 62
  | .compatibleUnion _ _ => start < stop
  | _ => True

/--
A call of the layout driver on a range of an accepted encoding writes the record of the tree the Lean layout
describes, and changes nothing else.
-/
theorem layout_calls {m : Module} {w : World} (fns : PlanFns m)
    (hf : m.fns.lookup "ssz_prove_layout" = some ProveLayout.fn) {sp : Nat} {mem : Memory} {d : Desc}
    {b : ByteArray} (room : w.stackLo + 8 + 8 * ProveLayout.fn.frame + layoutRoom d ≤ sp)
    {p data start stop lay : Nat} {layout : EncodedLayout} (laid : layoutOf d b start stop = .ok layout)
    (input : LayoutInput w mem d b p data start stop lay) (sound : d.wellFormed = .ok ())
    (thin : narrow d = true) (accepted : LayoutAccepted d b start stop) :
    ∃ mem', Calls m w "ssz_prove_layout" sp [UInt64.ofNat p, UInt64.ofNat data, UInt64.ofNat start,
      UInt64.ofNat stop, UInt64.ofNat lay] mem 0 mem' ∧ LayoutDone w mem mem' d p lay data b layout := by
  cases d with
  | bool | uint _ | byteVector _ | byteList _ | bitVector _ =>
    exact layout_basic hf (by omega) laid (by simp [tag]) input
  | bitList _ | progressiveBitList _ =>
    exact layout_bitList hf (by omega) laid (by simp [tag]) input accepted.1 accepted.2
  | vector _ _ | list _ _ | progressiveList _ _ =>
    exact layout_sequence fns hf (by simp only [layoutRoom, Desc.nesting] at room ⊢; omega) laid (by simp [tag])
      input sound thin accepted
  | container _ _ => exact layout_struct fns.codec hf room laid input sound thin accepted
  | progressiveContainer _ _ _ => exact layout_progressive fns.codec hf room laid input sound thin accepted
  | compatibleUnion _ _ => exact layout_union fns.codec hf room laid input sound accepted

end EthLib.Consensus.Ssz.Native.Driver.ProveProof
