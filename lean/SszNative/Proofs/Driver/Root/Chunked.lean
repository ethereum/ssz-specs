import SszNative.Proofs.Driver.Root.Columns

/-!
The chunked roots driver computes the Lean chunked roots.

The Lean computation roots each chunk of records in a task of its own, and joins the parts in order.
Tasks are pure, so the join is the sequential one: each chunk's roots, one after the other.
The driver roots the chunks in order, each right after the ones before it, and its scratch after that.
The proof takes what one call rooting a chunk does as a hypothesis, so it serves any element type.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Asm

/-! ### The sequential join -/

/-- Memory holding two buffers one after the other holds their join. -/
theorem _root_.EthLib.Consensus.Ssz.Native.Holds.append {mem : Memory} {a : Nat} {x y : ByteArray} (hx : Holds mem a x)
    (hy : Holds mem (a + x.size) y) : Holds mem a (x ++ y) := by
  intro i hi
  rw [ByteArray.size_append] at hi
  rw [Kernel.get!_eq _ _ (by rw [ByteArray.size_append]; omega)]
  by_cases left : i < x.size
  · rw [ByteArray.getElem_append_left left, hx i left, Kernel.get!_eq _ _ left]
  · rw [ByteArray.getElem_append_right (by omega), show a + i = a + x.size + (i - x.size) by omega,
      hy _ (by omega), Kernel.get!_eq _ _ (by omega)]

/-- The roots of the first chunks of a run, joined in order: each chunk's roots from the record it starts at. -/
def chunkJoin (f : Nat → Nat → ByteArray) (count k : Nat) : ByteArray :=
  (List.range k).foldl (fun out j => out ++ f (recordsPerChunk * j) (min recordsPerChunk (count - recordsPerChunk * j)))
    (ByteArray.emptyWithCapacity (32 * count + 32))

/-- One more chunk joins its roots after the others. -/
theorem chunkJoin_succ (f : Nat → Nat → ByteArray) (count k : Nat) :
    chunkJoin f count (k + 1) =
      chunkJoin f count k ++ f (recordsPerChunk * k) (min recordsPerChunk (count - recordsPerChunk * k)) := by
  simp only [chunkJoin, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/--
Chunks whose roots take one node per record join into one node per record rooted so far.

Only the chunks of the run need a root per record, so the count of chunks reaches at most one past the run.
-/
theorem chunkJoin_size {f : Nat → Nat → ByteArray} {count : Nat}
    (sized : ∀ done c, done < count → done % recordsPerChunk = 0 → c = min recordsPerChunk (count - done) →
      (f done c).size = 32 * c) :
    ∀ k, recordsPerChunk * k < count + recordsPerChunk →
      (chunkJoin f count k).size = 32 * min count (recordsPerChunk * k)
  | 0, _ => by simp only [chunkJoin, List.range_zero, List.foldl_nil, Nat.mul_zero, Nat.min_zero]; rfl
  | k + 1, h => by
    have chunk : recordsPerChunk = 1024 := rfl
    rw [chunk] at h
    rw [chunkJoin_succ, ByteArray.size_append, chunkJoin_size sized k (by rw [chunk]; omega),
      sized _ _ (by rw [chunk]; omega) (Nat.mul_mod_right _ _) rfl]
    simp only [recordsPerChunk]
    omega

/-- Above one chunk, the chunked roots are the chunks' roots joined in order, as the tasks are pure. -/
theorem chunkedRoots_join (d : Desc) (b : ByteArray) (start stride count : Nat) (big : ¬ count ≤ recordsPerChunk) :
    chunkedRoots d b start stride count =
      chunkJoin (fun done c => rootsOf d b (start + stride * done) stride c) count
        ((count + recordsPerChunk - 1) / recordsPerChunk) := by
  rw [chunkedRoots, ite_eq_right big]
  simp only [List.foldl_map, chunkJoin, Nat.mul_assoc]
  rfl

/-! ### The driver -/

/-- The chunked roots driver's frame holds fifteen words. -/
theorem chunkedFrame : RootsChunked.fn.frame = 15 := by decide

/-- The chunked roots driver's loop. -/
abbrev chunkLoop : Stmt :=
  while_ (lt RootsChunked.done RootsChunked.count) [RootsChunked.c ::= RootsChunked.count - RootsChunked.done,
    when (lt (recordsPerChunk : Nat) RootsChunked.c) [RootsChunked.c ::= (recordsPerChunk : Nat)],
    callInto RootsChunked.sink "ssz_roots_of" [RootsChunked.p, RootsChunked.src + RootsChunked.stride * RootsChunked.done,
      RootsChunked.stride, RootsChunked.c, RootsChunked.out + 32 * RootsChunked.done, RootsChunked.ctx],
    RootsChunked.done ::= RootsChunked.done + (recordsPerChunk : Nat)]

/--
The chunked roots driver writes, at the output, the roots of a run of records joined chunk by chunk.

What a call rooting one chunk does is a hypothesis: from any memory agreeing with the start outside the output's
region and the padding area, it writes the chunk's roots at their place, and changes only the bytes from there to the
region's end and the padding area.
Chunks start a whole number of chunks into the run.
-/
theorem rootsChunked_calls {m : Module} {w : World} (hf : m.fns.lookup "ssz_roots_chunked" = some RootsChunked.fn)
    {sp : Nat} (room : w.stackLo + 8 + 8 * RootsChunked.fn.frame ≤ sp) {mem0 : Memory}
    {p src stride count out ctx pad span : Nat} (f : Nat → Nat → ByteArray)
    (sized : ∀ done c, done < count → done % recordsPerChunk = 0 → c = min recordsPerChunk (count - done) →
      (f done c).size = 32 * c)
    (pos : 0 < count) (countSmall : count + recordsPerChunk < 2 ^ 64)
    (rPad : Apart (out, span) (pad, 1536)) (fits : 32 * count ≤ span)
    (call : ∀ (mem : Memory) (done c : Nat),
      (∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem a = mem0 a) →
      done < count → done % recordsPerChunk = 0 → c = min recordsPerChunk (count - done) →
      ∃ mem', Calls m w "ssz_roots_of" (sp - 8 - 8 * RootsChunked.fn.frame) [UInt64.ofNat p,
          UInt64.ofNat (src + stride * done), UInt64.ofNat stride, UInt64.ofNat c, UInt64.ofNat (out + 32 * done),
          UInt64.ofNat ctx] mem 0 mem' ∧
        Holds mem' (out + 32 * done) (f done c) ∧
        ∀ a, ¬ (out + 32 * done ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem a) :
    ∃ mem', Calls m w "ssz_roots_chunked" sp [UInt64.ofNat p, UInt64.ofNat src, UInt64.ofNat stride,
        UInt64.ofNat count, UInt64.ofNat out, UInt64.ofNat ctx] mem0 0 mem' ∧
      Holds mem' out (if count ≤ recordsPerChunk then f 0 count
        else chunkJoin f count ((count + recordsPerChunk - 1) / recordsPerChunk)) ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem' a = mem0 a := by
  have rp := rPad
  simp only [Apart] at rp
  have chunk : recordsPerChunk = 1024 := rfl
  let sp' := sp - 8 - 8 * RootsChunked.fn.frame
  let E0 := entryEnv [UInt64.ofNat p, UInt64.ofNat src, UInt64.ofNat stride, UInt64.ofNat count, UInt64.ofNat out,
    UInt64.ofNat ctx]
  have small := eval_le (w := w) (env := E0) (mem := mem0) (a := RootsChunked.count) (b := ((recordsPerChunk : Nat) : Expr))
    (eval_var (show E0 3 = UInt64.ofNat count from rfl)) (eval_cast _) (by omega) (by omega)
  by_cases few : count ≤ recordsPerChunk
  · -- One chunk: a single call roots the whole run.
    rw [ite_eq_left few] at small ⊢
    obtain ⟨mem', c, held, keep⟩ := call mem0 0 count (fun _ _ _ => rfl) pos (Nat.zero_mod _) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at c held keep
    refine ⟨mem', Calls.fn hf room rfl (Runs.ifElse_true 1 small (by decide) (Runs.block_cons (Runs.call
      (by simp only [List.mapM_cons, List.mapM_nil]; rfl) c) (Runs.block_nil _ _ _ _ _))) rfl, held,
      fun a o pd => keep a o pd⟩
  · -- Several chunks: the loop roots them in order, each after the ones before it.
    rw [ite_eq_right few] at small ⊢
    let E1 := Asm.assign E0 6 (UInt64.ofNat 0)
    have args : ∀ y < 6, E1 y = E0 y := fun y hy => assign_ne (by omega)
    -- The chunks rooted so far are held in order, and memory is as at the start outside the region.
    let inv : Env → Memory → Prop := fun e mm => ∃ k, k ≤ (count + 1023) / 1024 ∧
      e 6 = UInt64.ofNat (1024 * k) ∧ (∀ y < 6, e y = E0 y) ∧ Holds mm out (chunkJoin f count k) ∧
      ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mm a = mem0 a
    have ends := Ends.loop (m := m) (w := w) (sp := sp') (env := E1) (mem := mem0)
      (c := lt RootsChunked.done RootsChunked.count)
      (body := .block [RootsChunked.c ::= RootsChunked.count - RootsChunked.done,
        when (lt (recordsPerChunk : Nat) RootsChunked.c) [RootsChunked.c ::= (recordsPerChunk : Nat)],
        callInto RootsChunked.sink "ssz_roots_of" [RootsChunked.p,
          RootsChunked.src + RootsChunked.stride * RootsChunked.done, RootsChunked.stride, RootsChunked.c,
          RootsChunked.out + 32 * RootsChunked.done, RootsChunked.ctx],
        RootsChunked.done ::= RootsChunked.done + (recordsPerChunk : Nat)])
      inv (fun e _ => count + 1024 - (e 6).toNat)
      ⟨0, Nat.zero_le _, assign_eq, args, fun i hi => absurd hi (by
        rw [chunkJoin_size sized 0 (by rw [chunk]; omega), Nat.mul_zero, Nat.min_zero, Nat.mul_zero]; exact Nat.not_lt_zero _), fun _ _ _ => rfl⟩
      (fun e mm ⟨k, hk, d, a, _⟩ => ⟨_, eval_lt (eval_var d) (eval_var ((a 3 (by decide)).trans rfl)) (by omega)
        (by omega)⟩)
      (fun e mm v ⟨k, hk, d, a, held, frame⟩ hv nz => by
        have c' := eval_lt (w := w) (env := e) (mem := mm) (a := RootsChunked.done) (b := RootsChunked.count)
          (eval_var d) (eval_var ((a 3 (by decide)).trans rfl)) (by omega) (by omega)
        rw [hv] at c'
        have more : 1024 * k < count := by
          by_cases b : 1024 * k < count
          · exact b
          · rw [ite_eq_right b] at c'; cases c'; exact absurd rfl nz
        -- The chunk's record count: what is left, at most one chunk.
        have s0 := Runs.set' (m := m) (w := w) (sp := sp') (mem := mm) (x := 7) (env := e)
          (e := RootsChunked.count - RootsChunked.done)
          (eval_sub (eval_var ((a 3 (by decide)).trans rfl)) (eval_var d) (by omega))
        let F1 := Asm.assign e 7 (UInt64.ofNat (count - 1024 * k))
        have s1 : Runs m w sp' F1 mm (when (lt (recordsPerChunk : Nat) RootsChunked.c)
            [RootsChunked.c ::= (recordsPerChunk : Nat)])
            (Asm.assign e 7 (UInt64.ofNat (min recordsPerChunk (count - 1024 * k)))) mm := by
          have cc := eval_lt (w := w) (env := F1) (mem := mm) (a := ((recordsPerChunk : Nat) : Expr))
            (b := RootsChunked.c) (eval_cast _) (eval_var assign_eq) (by omega) (by omega)
          by_cases full : recordsPerChunk < count - 1024 * k
          · rw [ite_eq_left full] at cc
            rw [Nat.min_eq_left (by omega)]
            have : Runs m w sp' F1 mm (when (lt (recordsPerChunk : Nat) RootsChunked.c)
                [RootsChunked.c ::= (recordsPerChunk : Nat)]) (Asm.assign F1 7 (UInt64.ofNat recordsPerChunk)) mm :=
              Runs.when_true 1 cc (by decide) (Runs.block_cons (Runs.set' (eval_cast _)) (Runs.block_nil _ _ _ _ _))
            simp only [F1, assign_assign] at this
            exact this
          · rw [ite_eq_right full] at cc
            rw [Nat.min_eq_right (by omega)]
            exact Runs.when_false cc
        let F2 := Asm.assign e 7 (UInt64.ofNat (min recordsPerChunk (count - 1024 * k)))
        have f2 : ∀ y < 6, F2 y = E0 y := fun y hy => by simp only [F2]; rw [assign_ne (by omega), a y hy]
        have f6 : F2 6 = UInt64.ofNat (1024 * k) := by simp only [F2]; rw [assign_ne (by decide), d]
        obtain ⟨mem', c, held', keep⟩ := call mm (1024 * k) (min recordsPerChunk (count - 1024 * k)) frame
          more (Nat.mul_mod_right _ _) rfl
        have callRuns := Runs.call (m := m) (sp := sp') (env := F2) (mem := mm) (dst := 8)
          (args := [RootsChunked.p, RootsChunked.src + RootsChunked.stride * RootsChunked.done, RootsChunked.stride,
            RootsChunked.c, RootsChunked.out + 32 * RootsChunked.done, RootsChunked.ctx])
          (by
            simp only [List.mapM_cons, List.mapM_nil,
              eval_var ((f2 0 (by decide)).trans (show E0 0 = UInt64.ofNat p from rfl)),
              eval_add (eval_var ((f2 1 (by decide)).trans (show E0 1 = UInt64.ofNat src from rfl)))
                (eval_mul (eval_var ((f2 2 (by decide)).trans (show E0 2 = UInt64.ofNat stride from rfl)))
                  (eval_var f6)),
              eval_var ((f2 2 (by decide)).trans (show E0 2 = UInt64.ofNat stride from rfl)),
              eval_var (show F2 7 = UInt64.ofNat (min recordsPerChunk (count - 1024 * k)) from assign_eq),
              eval_add (eval_var ((f2 4 (by decide)).trans (show E0 4 = UInt64.ofNat out from rfl)))
                (eval_mul (eval_lit 32) (eval_var f6)),
              eval_var ((f2 5 (by decide)).trans (show E0 5 = UInt64.ofNat ctx from rfl))]
            rfl) c
        have s3 := Runs.set' (m := m) (w := w) (sp := sp') (mem := mem') (x := 6) (env := Asm.assign F2 8 0)
          (e := RootsChunked.done + (recordsPerChunk : Nat))
          (eval_add (eval_var (show Asm.assign F2 8 0 6 = UInt64.ofNat (1024 * k) by rw [assign_ne (by decide)]; exact f6))
            (eval_cast _))
        have size := chunkJoin_size sized k (by rw [chunk]; omega)
        refine ⟨_, mem', Runs.block_cons s0 (Runs.block_cons s1 (Runs.block_cons callRuns (Runs.block_cons s3
          (Runs.block_nil _ _ _ _ _)))), ⟨k + 1, by omega, ?_, fun y hy => ?_, ?_, fun a o pd => ?_⟩, ?_⟩
        · rw [assign_eq]; congr 1
        · rw [assign_ne (by omega), assign_ne (by omega), f2 y hy]
        · -- The new chunk's roots land right after the others, which the call left alone.
          rw [chunkJoin_succ]
          refine Holds.append (held.congr fun i hi => keep _ (by rw [size, chunk] at hi; omega) (by
            rw [size, chunk] at hi; omega)) ?_
          rw [size, show 32 * min count (recordsPerChunk * k) = 32 * (1024 * k) by simp only [recordsPerChunk]; omega]
          exact held'
        · rw [keep a (by omega) pd, frame a o pd]
        · show count + 1024 - (UInt64.ofNat (1024 * k + recordsPerChunk)).toNat < count + 1024 - (e 6).toNat
          rw [d, ofNat_toNat (by omega), ofNat_toNat (by omega)]
          omega)
    obtain ⟨e, mm, run, ⟨k, hk, d, a, held, frame⟩, exit⟩ := ends
    -- The loop stops once every chunk is rooted.
    have c' := eval_lt (w := w) (env := e) (mem := mm) (a := RootsChunked.done) (b := RootsChunked.count)
      (eval_var d) (eval_var ((a 3 (by decide)).trans rfl)) (by omega) (by omega)
    rw [exit] at c'
    have last : k = (count + recordsPerChunk - 1) / recordsPerChunk := by
      by_cases b : 1024 * k < count
      · rw [ite_eq_left b] at c'; cases c'
      · simp only [recordsPerChunk]; omega
    subst last
    exact ⟨mm, Calls.fn hf room rfl (Runs.ifElse_false small (Runs.block_cons (Runs.set' (eval_lit 0)) run)) rfl,
      held, frame⟩

end EthLib.Consensus.Ssz.Native.Driver
