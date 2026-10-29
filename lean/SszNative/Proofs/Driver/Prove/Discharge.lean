import SszNative.Proofs.Driver.Prove.Progressive
import SszNative.Proofs.Branch.Main

/-!
The calls the leaves driver makes, proved from the root drivers, for the layout of a range decoding accepts.

Every value under such a layout is a child type of the range's type, and its own range decodes.
So each value meets a root call's needs, and the chunked roots of plain values meet the chunked driver's.
-/

namespace Ssz.Native.Driver.ProveProof

set_option maxRecDepth 20000

open Ssz Ssz.Native Ssz.Native.Ir Ssz.Native.Asm Ssz.Native.Plan

/-! ### The values under a layout -/

/-- A type directly inside another: a sequence's element, a struct's field, or a union's option. -/
def IsChild (d : Desc) : Desc → Prop
  | .vector element _ | .list element _ | .progressiveList element _ => d = element
  | .container _ fields | .progressiveContainer _ _ fields => d ∈ fields
  | .compatibleUnion _ options => d ∈ options
  | _ => False

/-- A placed field is one of the fields. -/
theorem mem_placeFields : ∀ (active : List Bool) (xs : List (Desc × Nat × Nat)) (x : Desc × Nat × Nat),
    some x ∈ placeFields active xs → x ∈ xs
  | [], _, _, h => by simp [placeFields] at h
  | false :: active, xs, x, h => by
    simp only [placeFields, List.mem_cons, reduceCtorEq, false_or] at h
    exact mem_placeFields active xs x h
  | true :: active, y :: xs, x, h => by
    simp only [placeFields, List.mem_cons, Option.some.injEq] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (mem_placeFields active xs x h)
  | true :: active, [], x, h => by
    simp only [placeFields, List.mem_cons, reduceCtorEq, false_or] at h
    exact mem_placeFields active [] x h

/-- Every value a layout holds is of a child type. -/
theorem layout_child {d0 : Desc} {b : ByteArray} {start stop : Nat} {layout : EncodedLayout}
    (laid : layoutOf d0 b start stop = .ok layout) {slots : Slots} (nested : layout.leaves = .nested slots)
    {i : Nat} {d : Desc} {s e : Nat} (at_ : slots.at i = some (some (d, s, e))) : IsChild d d0 := by
  -- Values listed with their ranges are children when the listed types are.
  have listed : ∀ (l : List (Option (Desc × Nat × Nat))) (ds : List Desc), slots = .listed l →
      (∀ x, some x ∈ l → x.1 ∈ ds) → d ∈ ds := fun l ds hs each => by
    subst hs
    exact each (d, s, e) (List.mem_of_getElem? at_)
  cases d0 with
  | bool | uint _ | byteVector _ | byteList _ | bitVector _ | bitList _ | progressiveBitList _ =>
    simp only [layoutOf] at laid
    cases laid
    cases nested
  | vector element length | list element length | progressiveList element length =>
    simp only [layoutOf] at laid
    cases laid
    simp only [encodedSequence] at nested
    split at nested
    · cases nested
    · simp only [EncodedLeaves.nested.injEq] at nested
      subst nested
      simp only [IsChild]
      simp only [elementSlots] at at_
      split at at_
      · simp only [Slots.at] at at_
        split at at_
        · simp only [Option.some.injEq, Prod.mk.injEq] at at_
          exact at_.1.symm
        · cases at_
      · simp only [Slots.at, List.getElem?_map] at at_
        obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp at_
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact h.1.symm
  | container names fields | progressiveContainer active names fields =>
    simp only [layoutOf, Bind.bind, Except.bind] at laid
    split at laid
    · cases laid
    · simp only [pure, Except.pure, Except.ok.injEq] at laid
      subst laid
      simp only [EncodedLeaves.nested.injEq] at nested
      simp only [IsChild]
      first
      | refine listed _ fields nested.symm fun x hx => ?_
        obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hx
        simp only [Option.some.injEq] at hxy
        subst hxy
        exact (List.of_mem_zip hy).1
      | refine listed _ fields nested.symm fun x hx => ?_
        exact (List.of_mem_zip (mem_placeFields _ _ _ hx)).1
  | compatibleUnion selectors options =>
    simp only [layoutOf, Bind.bind, Except.bind] at laid
    split at laid
    · cases laid
    · rename_i option found
      simp only [pure, Except.pure, Except.ok.injEq] at laid
      subst laid
      simp only [EncodedLeaves.nested.injEq] at nested
      simp only [IsChild]
      refine listed _ options nested.symm fun x hx => ?_
      simp only [List.mem_singleton, Option.some.injEq] at hx
      subst hx
      exact lookupOption_mem _ _ _ _ found

/-- A child of a narrow type is narrow. -/
theorem IsChild.narrow {d d0 : Desc} (h : IsChild d d0) (thin : narrow d0 = true) : narrow d = true := by
  cases d0 <;> simp only [IsChild] at h
  all_goals first
    | (subst h; simp only [Driver.narrow, Bool.and_eq_true] at thin; first | exact thin.2 | exact thin)
    | (simp only [Driver.narrow, Bool.and_eq_true] at thin
       first | exact narrow_mem _ thin.2 _ h | exact narrow_mem _ thin _ h)

/-- The words of a type in a list are among the list's words. -/
theorem words_sub_all : ∀ (ds : List Desc) (d : Desc), d ∈ ds → ∀ x ∈ words d, x ∈ wordsAll ds
  | [], _, h, _, _ => by simp at h
  | f :: rest, d, h, x, hx => by
    simp only [wordsAll, List.mem_append]
    rcases List.mem_cons.mp h with rfl | h
    · exact .inl hx
    · exact .inr (words_sub_all rest d h x hx)

/-- A child's plan words fit a word when its parent's do. -/
theorem IsChild.fits {d d0 : Desc} (h : IsChild d d0) (fits : Fits (words d0)) : Fits (words d) := by
  intro x hx
  apply fits x
  cases d0 <;> simp only [IsChild] at h
  all_goals first
    | (subst h; simp [words, hx])
    | (simp only [words, List.mem_append, List.mem_cons]; simp [words_sub_all _ _ h x hx])

/-- What a value under the layout of an accepted range is: a child type, well formed, and its range decoding. -/
structure ChildOk (d0 d : Desc) (b : ByteArray) (s e : Nat) : Prop where
  /-- The range runs forward. -/
  ordered : s ≤ e
  /-- It lies inside the encoding. -/
  inside : e ≤ b.size
  /-- It decodes as a value of the type. -/
  accepted : ∃ v, deserialize d (slice b s e) = .ok v
  /-- The type is legal. -/
  sound : d.wellFormed = .ok ()
  /-- It nests less deeply than its parent. -/
  shallow : d.nesting < d0.nesting
  /-- It is a child type. -/
  child : IsChild d d0

/-- Every value under the layout of an accepted range is accepted, inside the encoding, and of a child type. -/
theorem layout_children {d0 : Desc} {b : ByteArray} {start stop : Nat} {layout : EncodedLayout}
    (sound : d0.wellFormed = .ok ()) (ordered : start ≤ stop) (inside : stop ≤ b.size) (small : RootProof.Small b)
    (accepted : ∃ v, deserialize d0 (slice b start stop) = .ok v) (laid : layoutOf d0 b start stop = .ok layout)
    {slots : Slots} (nested : layout.leaves = .nested slots) {i : Nat} {d : Desc} {s e : Nat}
    (at_ : slots.at i = some (some (d, s, e))) : ChildOk d0 d b s e := by
  obtain ⟨v, read⟩ := accepted
  obtain ⟨E, L, laidE, layL, c⟩ := BranchProof.laysOut d0 sound b start stop v ordered inside small read
  rw [laid] at laidE
  cases laidE
  have agree := c.leaves
  rw [nested] at agree
  cases hL : L.leaves with
  | packed _ => rw [hL] at agree; exact absurd agree id
  | nested values =>
    rw [hL] at agree
    obtain ⟨counted, each, _⟩ := agree
    have below : i < values.length := by
      rw [← counted]
      apply Nat.lt_of_not_le
      intro past
      rw [BranchProof.Slots.at_none slots i past] at at_
      cases at_
    obtain ⟨x, hx, sa⟩ := each i below
    rw [at_] at hx
    cases hx
    cases hv : values[i] with
    | none => rw [hv] at sa; exact absurd sa id
    | some p =>
      obtain ⟨d', v'⟩ := p
      rw [hv] at sa
      obtain ⟨same, wf, o, ins, dec⟩ := sa
      subst same
      have member : some (d, v') ∈ values := by rw [← hv]; exact List.getElem_mem below
      exact ⟨o, ins, ⟨v', dec⟩, wf, merkleLayout_child_nesting d0 v L layL values hL d v' member,
        layout_child laid nested at_⟩

/-! ### Values rooted one at a time -/

/-- A run inside a range every address of which misses a region misses the region, when both are nonempty. -/
theorem run_apart {lo hi x n o k : Nat} (each : ∀ a, lo ≤ a → a < hi → a < o ∨ o + k ≤ a) (h1 : lo ≤ x)
    (h2 : x + n ≤ hi) (pos : 0 < n) (kpos : 0 < k) : x + n ≤ o ∨ o + k ≤ x := by
  by_cases h : x + n ≤ o ∨ o + k ≤ x
  · exact h
  · have := each (max x o) (by omega) (by omega)
    omega

/-- Every type's plan has a word. -/
theorem words_pos (d : Desc) : 0 < (words d).length := by
  cases d <;> simp [words]

/--
Where the leaves driver roots values, and what the root driver needs there: the context filled, the encoding in
memory, and the node buffer usable, below the address bound, and apart from the encoding, the context's buffers, the
plan, and the padding area.
-/
structure LeavesRoom (w : World) (mem : Memory) (b : ByteArray) (data buf span ctx table zeros pad lo hi : Nat)
    (mask : UInt64) : Prop where
  /-- The context is filled. -/
  ready : RootReady w ctx table zeros pad mask mem
  /-- The encoding is in memory. -/
  bytes : BytesAt mem data b
  /-- The encoding is usable. -/
  readable : w.access data b.size = true
  /-- Eight bits per byte of the encoding, and more, stay below the word size. -/
  small : 64 * b.size + 128 < 2 ^ 64
  /-- Twice the encoding's size past its address stays below the address bound. -/
  spread : data + 2 * b.size ≤ addressBound
  /-- A machine word holds a full 64-bit size. -/
  usize : USize.size = 2 ^ 64
  /-- The buffer is usable. -/
  bufAcc : w.access buf span = true
  /-- The buffer ends a node short of the address bound. -/
  slack : buf + span + 32 ≤ addressBound
  /-- The buffer misses the encoding. -/
  bufData : Apart (buf, span) (data, b.size)
  /-- It misses the padding area. -/
  bufPad : Apart (buf, span) (pad, 1536)
  /-- It misses the context. -/
  bufCtx : Apart (buf, span) (ctx, 32)
  /-- It misses the table. -/
  bufTable : Apart (buf, span) (table, Kernel.tableSize)
  /-- It misses the zero roots. -/
  bufZeros : Apart (buf, span) (zeros, 32 * (zeroHeights + 1))
  /-- It misses the plan. -/
  bufPlan : ∀ a, lo ≤ a → a < hi → a < buf ∨ buf + span ≤ a
  /-- The encoding misses the padding area. -/
  dataPad : Apart (data, b.size) (pad, 1536)
  /-- The plan misses the padding area. -/
  planPad : ∀ a, lo ≤ a → a < hi → a < pad ∨ pad + 1536 ≤ a

/-- What a value rooted on its own needs: a well-formed narrow type whose range decodes, a stack, and scratch. -/
structure ValueOk (w : World) (sp : Nat) (b : ByteArray) (cnt span : Nat) (d : Desc) (s e : Nat) : Prop where
  /-- The range runs forward. -/
  ordered : s ≤ e
  /-- It lies inside the encoding. -/
  inside : e ≤ b.size
  /-- It decodes as a value of the type. -/
  accepted : ∃ v, deserialize d (slice b s e) = .ok v
  /-- The type is legal. -/
  sound : d.wellFormed = .ok ()
  /-- Every fixed-size type inside it is far below the word size. -/
  thin : narrow d = true
  /-- Its plan's words fit a word. -/
  fits : Fits (words d)
  /-- The stack holds a root call. -/
  stack : w.stackLo + rootStack d + 256 ≤ sp
  /-- The scratch bound is below the cap. -/
  below : varNeed d (e - s) < scratchCap
  /-- The scratch past the nodes holds it. -/
  room : 32 * cnt + 64 + varNeed d (e - s) ≤ span

/-- The calls rooting values one at a time do what the leaves driver needs, from the root driver's contract. -/
theorem rootCalls_of {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RangeFns m)
    {sp : Nat} {mem : Memory} {b : ByteArray} {slots : Slots}
    {data first cnt buf span pad ctx lo hi table zeros : Nat} {mask : UInt64}
    (room : LeavesRoom w mem b data buf span ctx table zeros pad lo hi mask)
    (each : ∀ i d s e, i < cnt → slots.at (first + i) = some (some (d, s, e)) → ValueOk w sp b cnt span d s e) :
    RootCalls m w sp mem b slots data first cnt buf span pad ctx lo hi := by
  intro mm i d s e q kept below at_ planned qlo qhi
  have ok := each i d s e below at_
  have spanPos : 0 < span := by have := ok.room; omega
  have a8 := run_apart room.bufPlan qlo qhi (by have := words_pos d; omega) spanPos
  have a9 := run_apart room.planPad qlo qhi (by have := words_pos d; omega) (by decide)
  have a1 := room.bufPad
  have a2 := room.bufCtx
  have a3 := room.bufTable
  have a4 := room.bufZeros
  have a5 := room.ready.padCtx
  have a6 := room.ready.padTable
  have a7 := room.ready.padZeros
  have a10 := room.bufData
  have a11 := room.dataPad
  simp only [Apart] at a1 a2 a3 a4 a5 a6 a7 a10 a11
  have bb := BranchProof.access_bound room.bufAcc
  have db := BranchProof.access_bound room.readable
  have small := room.small
  have fitsIn := ok.room
  have endIn := ok.inside
  have runs := ok.ordered
  -- Memory outside the buffer and the padding area is as at the start.
  have far : ∀ a, (a < buf ∨ buf + span ≤ a) → (a < pad ∨ pad + 1536 ≤ a) → mm a = mem a :=
    fun a h1 h2 => kept a (by omega) (by omega)
  have ready : RootReady w ctx table zeros pad mask mm := RootReady.frame room.ready fun a h => by
    simp only [RootReady.Held] at h
    exact far a (by omega) (by omega)
  have holds : Holds mm data b := fun k hk => by rw [far _ (by omega) (by omega)]; exact room.bytes k hk
  have pre : RangePre w mm d q data s e (buf + 32 * i) (buf + 32 * cnt + 64) ctx table zeros pad mask b :=
    rangePre_of ready planned ok.fits holds room.readable ok.ordered ok.inside
      (by simp only [RootProof.Small]; rw [room.usize]; exact small) room.spread ok.sound ok.thin ok.accepted
      ok.below room.bufAcc room.slack room.bufData room.bufPad room.bufCtx room.bufTable room.bufZeros
      (by simp only [Apart]; omega) room.dataPad (by simp only [Apart]; omega) ⟨by omega, by omega⟩
      ⟨by omega, by omega⟩ (by simp only [Apart]; omega) room.usize
  obtain ⟨mm', call, node, _, keep⟩ := rootOf_ok hash gmod fns d sp mm q data s e (buf + 32 * i)
    (buf + 32 * cnt + 64) ctx table zeros pad mask b ok.stack pre
  refine ⟨mm', ?_, node, fun a h1 h2 h3 => keep a h1 (fun h => h2 ⟨h.1, by omega⟩) h3⟩
  rw [ofNat_add', ofNat_sub' ok.ordered]
  exact call

/-! ### Plain values rooted together -/

/-- The scratch a run of plain values rooted chunk by chunk needs: a chunk of one, or of the most records. -/
def chunkNeed (element : Desc) (cnt : Nat) : Nat :=
  max (rootsNeed element 1) (rootsNeed element (min cnt recordsPerChunk))

/-- A chunk of a run of plain values needs at most the run's chunk scratch. -/
theorem chunkNeed_le (element : Desc) {cnt c : Nat} (pos : 1 ≤ c) (le : c ≤ min cnt recordsPerChunk) :
    rootsNeed element c ≤ chunkNeed element cnt := by
  unfold chunkNeed
  by_cases one : c = 1
  · subst one; exact Nat.le_max_left _ _
  · exact Nat.le_trans (rootsNeed_grow element (by omega) le) (Nat.le_max_right _ _)

/-- What a run of plain values one width apart, rooted together, needs: a legal type, its values inside the
encoding, a stack, and scratch. -/
structure ChunkOk (w : World) (sp : Nat) (b : ByteArray) (first cnt span : Nat) (element : Desc) (start width : Nat) :
    Prop where
  /-- The type is legal. -/
  sound : element.wellFormed = .ok ()
  /-- Every fixed-size type inside it is far below the word size. -/
  thin : narrow element = true
  /-- The values are one value's width apart. -/
  wide : width = fixedWidth element
  /-- The values lie inside the encoding. -/
  inside : start + width * (first + cnt) ≤ b.size
  /-- The stack holds a chunked call. -/
  stack : w.stackLo + 8 + 8 * RootsChunked.fn.frame + rootsStack element ≤ sp
  /-- The scratch bound is below the cap. -/
  below : chunkNeed element cnt < scratchCap
  /-- The nodes and the scratch past them fit the buffer. -/
  room : 32 * cnt + chunkNeed element cnt ≤ span

set_option maxHeartbeats 2000000 in
/-- The call rooting plain values together does what the leaves driver needs, from the roots drivers' contracts. -/
theorem chunkCalls_of {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RootsFns m)
    {sp : Nat} {mem : Memory} {b : ByteArray} {slots : Slots}
    {data first cnt buf span pad ctx lo hi table zeros : Nat} {mask : UInt64}
    (room : LeavesRoom w mem b data buf span ctx table zeros pad lo hi mask)
    (each : ∀ element start width count, 0 < cnt → slots = .stride element start width count →
      plain element = true → ChunkOk w sp b first cnt span element start width) :
    ChunkCalls m w sp mem b slots data first cnt buf span pad ctx lo hi := by
  intro element start width count q pos hs pl planned qlo qhi
  have ok := each element start width count pos hs pl
  have spanPos : 0 < span := by have := ok.room; omega
  have a8 := run_apart room.bufPlan qlo qhi (by have := words_pos element; omega) spanPos
  have a9 := run_apart room.planPad qlo qhi (by have := words_pos element; omega) (by decide)
  have a1 := room.bufPad
  have a2 := room.bufCtx
  have a3 := room.bufTable
  have a4 := room.bufZeros
  have a5 := room.ready.padCtx
  have a6 := room.ready.padTable
  have a7 := room.ready.padZeros
  have a10 := room.bufData
  have a11 := room.dataPad
  simp only [Apart] at a1 a2 a3 a4 a5 a6 a7 a10 a11
  have bb := BranchProof.access_bound room.bufAcc
  have db := BranchProof.access_bound room.readable
  have small := room.small
  have slack := room.slack
  have spread := room.spread
  have bound : addressBound = 2 ^ 63 := rfl
  have chunk : recordsPerChunk = 1024 := rfl
  have capv := cap_eq
  have okE : Rootable element := ⟨pl, ok.sound, ok.thin⟩
  have wv := ok.wide
  have narrowW := width_narrow element pl ok.thin
  have ins := ok.inside
  have fitsIn := ok.room
  have under := ok.below
  have stack := ok.stack
  rw [chunkedFrame] at stack
  -- The run starts this many bytes into the encoding.
  generalize hS : start + width * first = S
  have runIn : S + width * cnt ≤ b.size := by
    rw [← hS, Nat.add_assoc, ← Nat.mul_add]; exact ins
  let f := fun done c => rootsOf element b (S + width * done) width c
  have sized : ∀ done c, done < cnt → done % recordsPerChunk = 0 → c = min recordsPerChunk (cnt - done) →
      (f done c).size = 32 * c := fun done c lt _ hc =>
    rootsOf_size element okE room.usize b _ width c (by rw [hc, chunk]; omega)
      (Nat.lt_of_le_of_lt (chunkNeed_le element (cnt := cnt) (by rw [hc, chunk]; omega)
        (by rw [chunk] at hc ⊢; omega)) under)
  obtain ⟨mem', call, held, keep⟩ := rootsChunked_calls (m := m) (w := w) fns.chunked (sp := sp)
    (by rw [chunkedFrame]; omega) (mem0 := mem) (p := q) (src := data + S) (stride := width) (count := cnt) (out := buf) (ctx := ctx)
    (pad := pad) (span := span) f sized pos (by omega) room.bufPad (by omega)
    (fun mm done c agree lt _ hc => by
      have cpos : 1 ≤ c := by rw [hc, chunk]; omega
      have cle : done + c ≤ cnt := by rw [hc, chunk]; omega
      have need := chunkNeed_le element (cnt := cnt) cpos (by rw [chunk] at hc ⊢; omega)
      have wc : width ≤ width * c := Nat.le_mul_of_pos_right _ cpos
      have far : ∀ a, (a < buf ∨ buf + span ≤ a) → (a < pad ∨ pad + 1536 ≤ a) → mm a = mem a :=
        fun a h1 h2 => agree a (by omega) (by omega)
      have ready : RootReady w ctx table zeros pad mask mm := RootReady.frame room.ready fun a h => by
        simp only [RootReady.Held] at h
        exact far a (by omega) (by omega)
      have plan : WordsAt w mm q (words element) := PlanAt.frame planned fun a h1 h2 => far a (by omega) (by omega)
      have holds : Holds mm data b := fun k hk => by rw [far _ (by omega) (by omega)]; exact room.bytes k hk
      have span' : width * (done + c) ≤ width * cnt := Nat.mul_le_mul_left _ cle
      rw [Nat.mul_add] at span'
      have pre : RootsPre w mm element q data (S + width * done) width c (buf + 32 * done) ctx table zeros pad mask
          b :=
        ⟨ready, plan, holds, room.readable, by omega, by omega, cpos,
          fun j hj => by
            have := Nat.mul_le_mul_left width (show done + j + 1 ≤ cnt by omega)
            rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at this
            omega,
          by omega, by omega,
          Driver.access_sub room.bufAcc (by omega) (by omega), by omega,
          by simp only [Apart]; omega, by simp only [Apart]; omega, by simp only [Apart]; omega,
          by simp only [Apart]; omega, by simp only [Apart]; omega, by simp only [Apart]; omega,
          a11, by simp only [Apart]; omega, room.usize⟩
      obtain ⟨mm', calls, roots, _, frame⟩ := rootsOf_ok hash gmod fns element okE (sp - 8 - 8 * RootsChunked.fn.frame)
        mm q data (S + width * done) width c (buf + 32 * done) ctx table zeros pad mask b
        (by rw [chunkedFrame]; omega) pre
      refine ⟨mm', ?_, roots, fun a o pd => frame a (fun h => o ⟨h.1, by omega⟩) pd⟩
      rw [show data + (S + width * done) = data + S + width * done by omega] at calls
      exact calls)
  -- The chunks joined are the chunked roots of the run.
  have joined : (if cnt ≤ recordsPerChunk then f 0 cnt
      else chunkJoin f cnt ((cnt + recordsPerChunk - 1) / recordsPerChunk)) = chunkedRoots element b S width cnt := by
    split
    · rename_i few
      rw [chunkedRoots, if_pos few]
      simp only [f, Nat.mul_zero, Nat.add_zero]
    · rename_i many
      rw [chunkedRoots_join _ _ _ _ _ many]
  rw [joined] at held
  have size : (chunkedRoots element b S width cnt).size = 32 * cnt :=
    chunkedRoots_size element (rootsOf_size element okE room.usize) b S width cnt pos
      (Nat.lt_of_le_of_lt (chunkNeed_le element (cnt := cnt) (by rw [chunk]; omega) (by omega)) under)
  refine ⟨mem', ?_, bytesAt_of_holds size held, fun a h1 h2 => keep a h1 h2⟩
  rw [ofNat_mul', ofNat_add', ofNat_add', show data + start + width * first = data + S by omega]
  exact call

/-! ### What the layout driver needs -/

/--
A range decoding accepts tells the layout driver what it needs: a bit list's last byte, a sequence's offsets inside
it, a struct's fixed part far below the word size, and a union's selector.
-/
theorem layoutAccepted_of {d : Desc} {b : ByteArray} {start stop : Nat} (sound : d.wellFormed = .ok ())
    (ordered : start ≤ stop) (inside : stop ≤ b.size) (small : 64 * b.size + 128 < 2 ^ 64)
    (accepted : ∃ v, deserialize d (slice b start stop) = .ok v) : LayoutAccepted d b start stop := by
  obtain ⟨v, read⟩ := accepted
  cases d with
  | bool | uint _ | byteVector _ | byteList _ | bitVector _ => trivial
  | bitList _ | progressiveBitList _ =>
    simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    rename_i bits read'
    exact bits_decoded inside read'
  | vector element length =>
    have soundE := wellFormed_vector sound
    have nz : 1 ≤ length := by
      apply Nat.pos_of_ne_zero
      rintro rfl
      simp [Desc.wellFormed, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind] at sound
    obtain ⟨-, offsets, -, -⟩ := vector_decoded soundE ordered inside ⟨v, read⟩
    intro e c hs
    simp only [sequenceOf, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have var : element.fixedSize = none → hasWidth element = false := fun h => by
      rw [fixedSize_eq] at h
      cases hw : hasWidth element
      · rfl
      · rw [hw] at h; cases h
    exact ⟨fun h => by have := offsets (var h); omega, fun h _ => by have := offsets (var h); omega⟩
  | list element limit | progressiveList element limit =>
    simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
    split at read
    · cases read
    rename_i slices cut
    split at read
    · cases read
    rename_i values decoded
    obtain ⟨counted, -, -, -, -, varCount⟩ := list_decoded ordered inside cut decoded
    intro e c hs
    simp only [sequenceOf, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have var : element.fixedSize = none → hasWidth element = false := fun h => by
      rw [fixedSize_eq] at h
      cases hw : hasWidth element
      · rfl
      · rw [hw] at h; cases h
    refine ⟨fun h => ?_, fun h _ => ?_⟩
    all_goals
      rcases varCount (var h) with ⟨z, n⟩ | ⟨four, _, table⟩
      · omega
      · omega
  | container names fields | progressiveContainer active names fields =>
    simp only [deserialize, Bind.bind, Except.bind, pure, Except.pure] at read
    repeat (split at read; · cases read)
    rename_i values read'
    obtain ⟨-, lead, -⟩ := struct_decoded ordered inside read'
    show Desc.leadingWidth fields < 2 ^ 62
    omega
  | compatibleUnion selectors options =>
    have size := slice_size b start stop inside
    simp only [deserialize, throw, throwThe, MonadExceptOf.throw] at read
    split at read
    · cases read
    rename_i nonempty
    rw [size] at nonempty
    show start < stop
    simp at nonempty
    omega

/--
A call of the layout driver on a range decoding accepts writes the record of the tree the Lean layout describes, and
changes nothing else.
-/
theorem layout_calls_of_decoded {m : Module} {w : World} (fns : PlanFns m)
    (hf : m.fns.lookup "ssz_prove_layout" = some ProveLayout.fn) {sp : Nat} {mem : Memory} {d : Desc}
    {b : ByteArray} (room : w.stackLo + 8 + 8 * ProveLayout.fn.frame + layoutRoom d ≤ sp)
    {p data start stop lay : Nat} {layout : EncodedLayout} (laid : layoutOf d b start stop = .ok layout)
    (input : LayoutInput w mem d b p data start stop lay) (sound : d.wellFormed = .ok ())
    (thin : narrow d = true) (accepted : ∃ v, deserialize d (slice b start stop) = .ok v) :
    ∃ mem', Calls m w "ssz_prove_layout" sp [UInt64.ofNat p, UInt64.ofNat data, UInt64.ofNat start,
      UInt64.ofNat stop, UInt64.ofNat lay] mem 0 mem' ∧ LayoutDone w mem mem' d p lay data b layout :=
  layout_calls fns hf room laid input sound thin
    (layoutAccepted_of sound input.ordered input.inside input.small accepted)

/-! ### The calls under a layout -/

/-- A range decoding accepts, of a legal narrow type whose plan fits, and the layout it has. -/
structure Decoded (d0 : Desc) (b : ByteArray) (start stop : Nat) (layout : EncodedLayout) : Prop where
  /-- The type is legal. -/
  sound : d0.wellFormed = .ok ()
  /-- Every fixed-size type inside it is far below the word size. -/
  thin : narrow d0 = true
  /-- Its plan's words fit a word. -/
  fits : Fits (words d0)
  /-- The range runs forward. -/
  ordered : start ≤ stop
  /-- It lies inside the encoding. -/
  inside : stop ≤ b.size
  /-- It decodes. -/
  accepted : ∃ v, deserialize d0 (slice b start stop) = .ok v
  /-- Its layout. -/
  laid : layoutOf d0 b start stop = .ok layout

/--
The scratch the calls rooting the values under a layout need past the nodes: each value's own, where values are
rooted one at a time, and a run's chunk scratch, where plain values one width apart are rooted together.
-/
def LeavesNeed (layout : EncodedLayout) (span : Nat) : Prop :=
  ∀ slots, layout.leaves = .nested slots →
    ((∀ element start width count, slots = .stride element start width count → plain element = false) →
      ∀ i d s e, slots.at i = some (some (d, s, e)) →
        varNeed d (e - s) < scratchCap ∧ 32 * layout.count + 64 + varNeed d (e - s) ≤ span) ∧
    ∀ element start width count, slots = .stride element start width count → plain element = true →
      chunkNeed element count < scratchCap ∧ 32 * count + chunkNeed element count ≤ span

/-- A run's chunk scratch grows with the run. -/
theorem chunkNeed_mono (element : Desc) {a c : Nat} (h : a ≤ c) : chunkNeed element a ≤ chunkNeed element c := by
  unfold chunkNeed
  have chunk : recordsPerChunk = 1024 := rfl
  rw [chunk]
  by_cases two : 2 ≤ min a 1024
  · have := rootsNeed_grow element two (show min a 1024 ≤ min c 1024 by omega)
    exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans this (Nat.le_max_right _ _)⟩
  · rcases (show min a 1024 = 0 ∨ min a 1024 = 1 by omega) with z | o
    · rw [z, rootsNeed_zero]; exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.zero_le _⟩
    · rw [o]; exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩

/-- Values one width apart under a layout are each one value's width wide. -/
theorem layout_stride {d0 : Desc} {b : ByteArray} {start stop : Nat} {layout : EncodedLayout}
    (dec : Decoded d0 b start stop layout) (small : RootProof.Small b) {element : Desc} {s width count : Nat}
    (nested : layout.leaves = .nested (.stride element s width count)) : element.fixedSize = some width := by
  obtain ⟨v, read⟩ := dec.accepted
  obtain ⟨E, L, laidE, _, c⟩ := BranchProof.laysOut d0 dec.sound b start stop v dec.ordered dec.inside small read
  rw [dec.laid] at laidE
  cases laidE
  have agree := c.leaves
  rw [nested] at agree
  cases hL : L.leaves with
  | packed _ => rw [hL] at agree; exact absurd agree id
  | nested values =>
    rw [hL] at agree
    exact agree.2.2 element s width count rfl

/-- A child's stack is a level less than its parent's. -/
theorem rootStack_child {d d0 : Desc} (shallow : d.nesting < d0.nesting) : rootStack d + 1024 ≤ rootStack d0 := by
  unfold rootStack; omega

/-- The calls rooting values one at a time under the layout of an accepted range follow from the root driver. -/
theorem rootCalls_layout {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RangeFns m)
    {sp : Nat} {mem : Memory} {b : ByteArray} {d0 : Desc} {start stop : Nat} {layout : EncodedLayout}
    {data buf span pad ctx lo hi table zeros : Nat} {mask : UInt64}
    (dec : Decoded d0 b start stop layout) (room : LeavesRoom w mem b data buf span ctx table zeros pad lo hi mask)
    (stack : w.stackLo + rootStack d0 + 256 ≤ sp) (need : LeavesNeed layout span) (first last : Nat) (slots : Slots)
    (nested : layout.leaves = .nested slots)
    (notChunked : ∀ element start width count, slots = .stride element start width count → plain element = false) :
    RootCalls m w sp mem b slots data first (min last layout.count - first) buf span pad ctx lo hi := by
  have small : RootProof.Small b := by simp only [RootProof.Small]; rw [room.usize]; exact room.small
  refine rootCalls_of hash gmod fns room fun i d s e _ at_ => ?_
  have kid := layout_children dec.sound dec.ordered dec.inside small dec.accepted dec.laid nested at_
  obtain ⟨below, fits⟩ := (need slots nested).1 notChunked _ d s e at_
  have up := rootStack_child kid.shallow
  exact ⟨kid.ordered, kid.inside, kid.accepted, kid.sound, kid.child.narrow dec.thin, kid.child.fits dec.fits,
    by omega, below, by omega⟩

/-- The chunked call under the layout of an accepted range follows from the roots drivers. -/
theorem chunkCalls_layout {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RootsFns m)
    {sp : Nat} {mem : Memory} {b : ByteArray} {d0 : Desc} {start stop : Nat} {layout : EncodedLayout}
    {data buf span pad ctx lo hi table zeros : Nat} {mask : UInt64}
    (dec : Decoded d0 b start stop layout) (room : LeavesRoom w mem b data buf span ctx table zeros pad lo hi mask)
    (stack : w.stackLo + rootStack d0 + 256 ≤ sp) (need : LeavesNeed layout span) (first last : Nat) (slots : Slots)
    (nested : layout.leaves = .nested slots) :
    ChunkCalls m w sp mem b slots data first (min last layout.count - first) buf span pad ctx lo hi := by
  have small : RootProof.Small b := by simp only [RootProof.Small]; rw [room.usize]; exact room.small
  refine chunkCalls_of hash gmod fns room fun element s width count pos hs pl => ?_
  subst hs
  have counted : layout.count = count := by simp [EncodedLayout.count, nested, Slots.count]
  rw [counted] at pos ⊢
  -- The last value of the run lies inside the encoding, and is of a child type.
  have at_ : (Slots.stride element s width count).at (first + (min last count - first) - 1) =
      some (some (element, s + width * (first + (min last count - first) - 1),
        s + width * (first + (min last count - first) - 1 + 1))) := by
    simp only [Slots.at]; rw [if_pos (by omega)]
  have kid := layout_children dec.sound dec.ordered dec.inside small dec.accepted dec.laid nested at_
  have ends := kid.inside
  rw [show first + (min last count - first) - 1 + 1 = first + (min last count - first) by omega] at ends
  have wide : width = fixedWidth element := by
    have := layout_stride dec small nested
    rw [fixedSize_plain element pl] at this
    exact (Option.some.inj this).symm
  obtain ⟨below, fits⟩ := (need _ nested).2 element s width count rfl pl
  have grow := chunkNeed_mono element (show min last count - first ≤ count by omega)
  have up := rootStack_child kid.shallow
  have frame := chunkedFrame
  have deep : rootsStack element + 1024 ≤ rootStack element + 1024 := by
    unfold rootsStack rootStack columnsStack hashStack; omega
  refine ⟨kid.sound, kid.child.narrow dec.thin, wide, ends, by rw [frame]; omega, by omega, by omega⟩

/-! ### The drivers, with their root calls proved -/

set_option maxHeartbeats 4000000 in
/--
A call of the leaves driver on the layout of an accepted range writes the Lean leaves from one position to another at
the buffer, and answers how many there are.

The root calls under the layout are proved, given a stack for the range's type and the scratch the values need.
-/
theorem leaves_calls_decoded {m : Module} {w : World} (linked : HasCodec m) (gmod : GatherModule m)
    (hash : HashingOk m w) (fns : RangeFns m)
    (hf : m.fns.lookup "ssz_prove_leaves" = some ProveLeaves.fn)
    (hs : m.fns.lookup "ssz_prove_slot" = some ProveSlot.fn) {sp n : Nat}
    (room : w.stackLo + 8 + 8 * ProveLeaves.fn.frame + slotRoom n ≤ sp)
    {mem : Memory} {lay data lo hi top : Nat} {b : ByteArray} {layout : EncodedLayout}
    (counted : readLE mem (lay + 8) 8 = UInt64.ofNat layout.count)
    (encoding : readLE mem (lay + 72) 8 = UInt64.ofNat data)
    (leaves : LeavesAt w mem lay b n lo hi top layout.leaves)
    (fixedPart : w.access lay 144 = true) (base : lay + 144 ≤ top)
    (countSmall : layout.count < 2 ^ 62)
    {first last buf ctx span pad table zeros : Nat} {mask : UInt64} (firstSmall : first < 2 ^ 64)
    (lastSmall : last < 2 ^ 64) (wide : 32 * (min last layout.count - first) + 64 ≤ span)
    (away : ∀ a, (buf ≤ a ∧ a < buf + span) ∨ (pad ≤ a ∧ a < pad + 1536) → ¬ Footprint lay top lo hi data b.size a)
    {d0 : Desc} {start stop : Nat} (dec : Decoded d0 b start stop layout)
    (lroom : LeavesRoom w mem b data buf span ctx table zeros pad lo hi mask)
    (stack : w.stackLo + rootStack d0 + 256 ≤ sp - 8 - 8 * ProveLeaves.fn.frame) (need : LeavesNeed layout span) :
    ∃ mem', Calls m w "ssz_prove_leaves" sp [UInt64.ofNat lay, UInt64.ofNat first, UInt64.ofNat last,
        UInt64.ofNat buf, UInt64.ofNat ctx] mem (UInt64.ofNat (leavesIn b layout first last).2) mem' ∧
      bytesAt mem' buf (32 * (leavesIn b layout first last).2) = (leavesIn b layout first last).1 ∧
      Kept mem mem' buf span pad :=
  leaves_calls linked gmod hf hs room counted encoding leaves fixedPart base lroom.bytes lroom.readable lroom.small
    lroom.usize countSmall firstSmall lastSmall lroom.bufAcc wide away lroom.bufPad lroom.bufData
    (fun slots h => chunkCalls_layout hash gmod fns.roots dec lroom stack need first last slots h)
    (fun slots h notChunked => rootCalls_layout hash gmod fns dec lroom stack need first last slots h notChunked)

/-- What a walk's needs give the calls rooting values under its leaves, with the encoding apart from the padding
area and below the address bound, and the scratch below it. -/
theorem WalkPre.leavesRoom {w : World} {mem : Memory} {lay data lo hi top out ctx free span table zeros pad : Nat}
    {mask : UInt64} {b : ByteArray} (pre : WalkPre w mem lay data lo hi top out ctx free span table zeros pad mask b)
    (spread : data + 2 * b.size ≤ addressBound) (slack : free + span + 32 ≤ addressBound)
    (dataPad : Apart (data, b.size) (pad, 1536)) :
    LeavesRoom w mem b data free span ctx table zeros pad lo hi mask :=
  ⟨pre.ready, pre.bytes, pre.readable, pre.small, spread, pre.usize, pre.freeAcc, slack, pre.dataApart, pre.freePad,
    pre.freeCtx, pre.freeTable, pre.freeZeros,
    fun a h1 h2 => by
      by_cases inside : free ≤ a ∧ a < free + span
      · exact absurd (.inr (.inl ⟨h1, h2⟩)) (pre.away a (.inl inside))
      · omega,
    dataPad,
    fun a h1 h2 => by
      by_cases inside : pad ≤ a ∧ a < pad + 1536
      · exact absurd (.inr (.inl ⟨h1, h2⟩)) (pre.away a (.inr (.inl inside)))
      · omega⟩

set_option maxHeartbeats 4000000 in
/--
A call of the bounded walk on the layout of an accepted range answers what the Lean walk answers for a node of a
bounded subtree, and writes the node when there is one.

The root calls under the layout are proved, given a stack for the range's type and the scratch the values need.
The walk to a node of the value at one leaf is still a contract.
-/
theorem bounded_calls_decoded {m : Module} {w : World} (linked : HasCodec m) (gmod : GatherModule m)
    (hash : HashingOk m w) (fns : RangeFns m)
    (hf : m.fns.lookup "ssz_prove_bounded" = some ProveBounded.fn)
    (hd : m.fns.lookup "ssz_depth_for" = some DepthFor.fn)
    (hp : m.fns.lookup "ssz_prove_pow2" = some ProvePow2.fn)
    (hsh : m.fns.lookup "ssz_prove_shr" = some ProveShr.fn)
    (hl : m.fns.lookup "ssz_prove_leaves" = some ProveLeaves.fn)
    (hs : m.fns.lookup "ssz_prove_slot" = some ProveSlot.fn) {sp n : Nat}
    (room : w.stackLo + 8 + 8 * ProveBounded.fn.frame + boundedRoom n ≤ sp)
    {mem : Memory} {lay data lo hi top out ctx free span table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    {layout : EncodedLayout} (laid : LaidOut w mem lay data b n lo hi top layout)
    (pre : WalkPre w mem lay data lo hi top out ctx free span table zeros pad mask b)
    (wide : 64 * layout.count + 4096 ≤ span) (countSmall : layout.count < 2 ^ 62)
    (budget index depth leavesFrom capacity : Nat) (indexSmall : index < 2 ^ 64) (shallow : depth < 64)
    (fromSmall : leavesFrom < 2 ^ 62) (capSmall : capacity < 2 ^ 64)
    {d0 : Desc} {start stop : Nat} (dec : Decoded d0 b start stop layout)
    (spread : data + 2 * b.size ≤ addressBound) (slack : free + span + 32 ≤ addressBound)
    (dataPad : Apart (data, b.size) (pad, 1536))
    (stack : w.stackLo + rootStack d0 + 256 ≤ sp - 8 - 8 * ProveBounded.fn.frame - 8 - 8 * ProveLeaves.fn.frame)
    (need : LeavesNeed layout span)
    (child : ∀ slots, layout.leaves = .nested slots →
      ChildCalls m w (sp - 8 - 8 * ProveBounded.fn.frame) mem budget b slots data out ctx free span pad lo hi) :
    ∃ r mem', Calls m w "ssz_prove_bounded" sp [UInt64.ofNat lay, UInt64.ofNat index, UInt64.ofNat depth,
        UInt64.ofNat leavesFrom, UInt64.ofNat capacity] mem r mem' ∧
      r = proveCode (boundedNode budget b layout index depth leavesFrom capacity) ∧
      (∀ node, boundedNode budget b layout index depth leavesFrom capacity = .ok node →
        nodeAt mem' out = node.data) ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (free ≤ a ∧ a < free + span) → ¬ (pad ≤ a ∧ a < pad + 1536) →
        mem' a = mem a :=
  have lroom := pre.leavesRoom spread slack dataPad
  bounded_calls linked gmod hash hf hd hp hsh hl hs room laid pre wide countSmall budget index depth leavesFrom
    capacity indexSmall shallow fromSmall capSmall
    (fun first last slots h => chunkCalls_layout hash gmod fns.roots dec lroom stack need first last slots h)
    (fun first last slots h notChunked =>
      rootCalls_layout hash gmod fns dec lroom stack need first last slots h notChunked)
    child

/-! ### Calls from a moved buffer and changed memory -/

/-- More scratch serves the same values. -/
theorem LeavesNeed.mono {layout : EncodedLayout} {span span' : Nat} (need : LeavesNeed layout span)
    (le : span ≤ span') : LeavesNeed layout span' := fun slots h =>
  ⟨fun nc i d s e at_ => by have := ((need slots h).1 nc i d s e at_); omega,
    fun element start width count hs pl => by have := (need slots h).2 element start width count hs pl; omega⟩

/--
Where the leaves driver roots values stays a place it may root them when the buffer starts a node later, and when
memory changes only in the buffer's first node.
-/
theorem LeavesRoom.shift {w : World} {mem mm : Memory} {b : ByteArray}
    {data free span ctx table zeros pad lo hi buf span' : Nat} {mask : UInt64}
    (room : LeavesRoom w mem b data free span ctx table zeros pad lo hi mask) (node : 32 ≤ span)
    (shape : (buf = free ∧ span' = span) ∨ (buf = free + 32 ∧ span' = span - 32))
    (same : ∀ a, ¬ (free ≤ a ∧ a < free + 32) → mm a = mem a) :
    LeavesRoom w mm b data buf span' ctx table zeros pad lo hi mask := by
  have a1 := room.bufPad
  have a2 := room.bufCtx
  have a3 := room.bufTable
  have a4 := room.bufZeros
  have a10 := room.bufData
  simp only [Apart] at a1 a2 a3 a4 a10
  have inBuf : free ≤ buf ∧ buf + span' ≤ free + span := by omega
  refine ⟨RootReady.frame room.ready fun a h => ?_, fun k hk => ?_, room.readable, room.small, room.spread,
    room.usize, Driver.access_sub room.bufAcc inBuf.1 inBuf.2, by have := room.slack; omega,
    apart_sub room.bufData inBuf.1 inBuf.2, apart_sub room.bufPad inBuf.1 inBuf.2,
    apart_sub room.bufCtx inBuf.1 inBuf.2, apart_sub room.bufTable inBuf.1 inBuf.2,
    apart_sub room.bufZeros inBuf.1 inBuf.2, fun a h1 h2 => ?_, room.dataPad, room.planPad⟩
  · simp only [RootReady.Held] at h
    exact same a (by omega)
  · rw [same _ (by omega)]; exact room.bytes k hk
  · have := room.bufPlan a h1 h2; omega

/--
The calls rooting values one at a time under the layout of an accepted range, from any stack at most a bound, at the
buffer or a node past it, from memory changed only in the buffer's first node.
-/
theorem rootCalls_moved {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RangeFns m)
    {mem : Memory} {b : ByteArray} {d0 : Desc} {start stop : Nat} {layout : EncodedLayout}
    {data free span pad ctx lo hi table zeros : Nat} {mask : UInt64}
    (dec : Decoded d0 b start stop layout) (room : LeavesRoom w mem b data free span ctx table zeros pad lo hi mask)
    {bound : Nat} (stack : w.stackLo + rootStack d0 + 256 ≤ bound) (need : LeavesNeed layout (span - 32))
    (node : 32 ≤ span) :
    ∀ s mm buf span' first last slots, bound ≤ s →
      (buf = free ∧ span' = span) ∨ (buf = free + 32 ∧ span' = span - 32) →
      (∀ a, ¬ (free ≤ a ∧ a < free + 32) → mm a = mem a) → layout.leaves = .nested slots →
      (∀ element start width count, slots = .stride element start width count → plain element = false) →
      RootCalls m w s mm b slots data first (min last layout.count - first) buf span' pad ctx lo hi :=
  fun _ _ _ _ first last slots low shape same h nc =>
    rootCalls_layout hash gmod fns dec (room.shift node shape same) (by omega)
      (need.mono (by omega)) first last slots h nc

/--
The chunked call under the layout of an accepted range, from any stack at most a bound, at the buffer or a node past
it, from memory changed only in the buffer's first node.
-/
theorem chunkCalls_moved {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RootsFns m)
    {mem : Memory} {b : ByteArray} {d0 : Desc} {start stop : Nat} {layout : EncodedLayout}
    {data free span pad ctx lo hi table zeros : Nat} {mask : UInt64}
    (dec : Decoded d0 b start stop layout) (room : LeavesRoom w mem b data free span ctx table zeros pad lo hi mask)
    {bound : Nat} (stack : w.stackLo + rootStack d0 + 256 ≤ bound) (need : LeavesNeed layout (span - 32))
    (node : 32 ≤ span) :
    ∀ s mm buf span' first last slots, bound ≤ s →
      (buf = free ∧ span' = span) ∨ (buf = free + 32 ∧ span' = span - 32) →
      (∀ a, ¬ (free ≤ a ∧ a < free + 32) → mm a = mem a) → layout.leaves = .nested slots →
      ChunkCalls m w s mm b slots data first (min last layout.count - first) buf span' pad ctx lo hi :=
  fun _ _ _ _ first last slots low shape same h =>
    chunkCalls_layout hash gmod fns dec (room.shift node shape same) (by omega)
      (need.mono (by omega)) first last slots h

set_option maxHeartbeats 4000000 in
/--
A call of the progressive walk on the layout of an accepted range answers what the Lean walk answers for a node of a
progressive tree, and writes the node when there is one.

The root calls under the layout are proved, given a stack for the range's type and the scratch the values need a node
short of the scratch.
The walk to a node of the value at one leaf is still a contract.
-/
theorem progressive_calls_decoded {m : Module} {w : World} (linked : HasCodec m) (gmod : GatherModule m)
    (hash : HashingOk m w) (fns : RangeFns m)
    (hf : m.fns.lookup "ssz_prove_progressive" = some ProveProgressive.fn)
    (hwk : m.fns.lookup "ssz_prove_spine_walk" = some ProveSpineWalk.fn)
    (hbd : m.fns.lookup "ssz_prove_bounded" = some ProveBounded.fn)
    (hsp : m.fns.lookup "ssz_prove_spine" = some ProveSpine.fn)
    (hlv : m.fns.lookup "ssz_branch_level" = some Level.fn)
    (hd : m.fns.lookup "ssz_depth_for" = some DepthFor.fn)
    (hp : m.fns.lookup "ssz_prove_pow2" = some ProvePow2.fn)
    (hsh : m.fns.lookup "ssz_prove_shr" = some ProveShr.fn)
    (hl : m.fns.lookup "ssz_prove_leaves" = some ProveLeaves.fn)
    (hs : m.fns.lookup "ssz_prove_slot" = some ProveSlot.fn) {sp n : Nat}
    (room : w.stackLo + 8 + 8 * ProveProgressive.fn.frame + progressiveRoom n ≤ sp)
    {mem : Memory} {lay data lo hi top out ctx free span table zeros pad : Nat} {mask : UInt64} {b : ByteArray}
    {layout : EncodedLayout} (laid : LaidOut w mem lay data b n lo hi top layout)
    (pre : WalkPre w mem lay data lo hi top out ctx free span table zeros pad mask b)
    (wide : 64 * layout.count + 4672 ≤ span) (countSmall : layout.count < 2 ^ 57)
    (budget index depth j : Nat) (indexSmall : index < 2 ^ 64) (shallow : depth < 64)
    (reached : j = 0 ∨ spineStart (j - 1) < layout.count)
    {d0 : Desc} {start stop : Nat} (dec : Decoded d0 b start stop layout)
    (spread : data + 2 * b.size ≤ addressBound) (slack : free + span + 32 ≤ addressBound)
    (dataPad : Apart (data, b.size) (pad, 1536))
    (stack : w.stackLo + rootStack d0 + 256 ≤
      sp - 8 - 8 * ProveProgressive.fn.frame - 8 - 8 * ProveBounded.fn.frame - 8 - 8 * ProveLeaves.fn.frame)
    (need : LeavesNeed layout (span - 32))
    (child : ∀ slots, layout.leaves = .nested slots →
      ChildCalls m w (sp - 8 - 8 * ProveProgressive.fn.frame - 8 - 8 * ProveBounded.fn.frame) mem budget b slots
        data out ctx free span pad lo hi) :
    ∃ r mem', Calls m w "ssz_prove_progressive" sp [UInt64.ofNat lay, UInt64.ofNat index, UInt64.ofNat depth,
        UInt64.ofNat (spineStart j), UInt64.ofNat (4 ^ j)] mem r mem' ∧
      r = proveCode (progressiveNode budget b layout index depth (spineStart j) (4 ^ j)) ∧
      (∀ node, progressiveNode budget b layout index depth (spineStart j) (4 ^ j) = .ok node →
        nodeAt mem' out = node.data) ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + 32) → ¬ (free ≤ a ∧ a < free + span) → ¬ (pad ≤ a ∧ a < pad + 1536) →
        mem' a = mem a :=
  have lroom := pre.leavesRoom spread slack dataPad
  progressive_calls linked gmod hash hf hwk hbd hsp hlv hd hp hsh hl hs room laid pre wide countSmall budget index
    depth j indexSmall shallow reached
    (chunkCalls_moved hash gmod fns.roots dec lroom stack need (by omega))
    (rootCalls_moved hash gmod fns dec lroom stack need (by omega))
    child

end Ssz.Native.Driver.ProveProof
