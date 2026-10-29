import SszNative.Proofs.Driver.Validate.Probe

/-!
Checking a delimited bit encoding in place: not empty, closed by a set bit, and within its limit.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr

/-- The highest set bit of a byte, as the native check finds it: the last of seven shifts left nonzero. -/
def highest (y : UInt64) : UInt64 :=
  let s (k : Nat) (h : UInt64) : UInt64 := if (if y >>> k.toUInt64 = 0 then (0 : UInt64) else 1) ≠ 0 then k.toUInt64 else h
  s 7 (s 6 (s 5 (s 4 (s 3 (s 2 (s 1 0))))))

/-- The native search finds the highest set bit of every byte. -/
theorem highest_lt : ∀ n, n < 256 → highest (UInt64.ofNat n) = UInt64.ofNat (highestBit (UInt8.ofNat n)) := by
  decide +kernel

/-- The native search finds the highest set bit of every byte. -/
theorem highest_eq (x : UInt8) : highest (UInt64.ofNat x.toNat) = UInt64.ofNat (highestBit x) := by
  have := highest_lt x.toNat x.toNat_lt
  rwa [UInt8.ofNat_toNat] at this

/-- Takes a guarded assignment at the head of a block, its condition left as a value. -/
macro "wwhen" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    try show Ssz.Native.Ir.Wp _ _ _ (Ssz.Native.Ir.Stmt.block _) _ _ _
    refine Ssz.Native.Ir.Wp.when_assign (cv := ?cv) (ev := ?ev) ?hc ?he ?k
    case hc => ((wev [$args,*]); done)
    case he => ((wev [$args,*]); done)))

/-- Every byte of a stretch is zero. -/
def AllZero (b : ByteArray) (start n : Nat) : Prop := ∀ k < n, (b.get! (start + k)).toNat = 0

/-- Whether the property holds, decided. -/
instance (b : ByteArray) (start n : Nat) : Decidable (AllZero b start n) := by
  unfold AllZero; infer_instance

/-- A delimited bit encoding's outcome, case by case. -/
theorem discard_delimited (b : ByteArray) (start stop : Nat) (limit : Option Nat) :
    Functor.discard (delimitedCount b start stop limit) =
      if stop - start = 0 then .error .emptyEncoding
      else if (b.get! (stop - 1)).toNat = 0 then
        (if AllZero b start (stop - start) then .error .noDelimiter else .error .trailingZeros)
      else match limit with
        | some cap =>
          if cap < 8 * (stop - start - 1) + highestBit (b.get! (stop - 1)) then
            .error (.overLimit cap (8 * (stop - start - 1) + highestBit (b.get! (stop - 1))))
          else .ok ()
        | none => .ok () := by
  have hall : ((List.range (stop - start)).all (fun i => b.get! (start + i) == 0) = true) ↔
      AllZero b start (stop - start) := by
    simp only [AllZero, List.all_eq_true, List.mem_range, beq_iff_eq]
    constructor
    · intro h k hk; rw [h k hk]; rfl
    · intro h k hk; exact UInt8.toNat_inj.mp (by rw [h k hk]; rfl)
  have hf : b.get! (stop - 1) = 0 ↔ (b.get! (stop - 1)).toNat = 0 := by
    constructor
    · intro h; rw [h]; rfl
    · intro h; exact UInt8.toNat_inj.mp (by rw [h]; rfl)
  simp only [delimitedCount, Functor.discard]
  by_cases z : stop - start = 0
  · simp [z, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, Functor.mapConst, Except.map]
  · simp only [z, ite_false, beq_iff_eq, hf, hall]
    by_cases f : (b.get! (stop - 1)).toNat = 0
    · by_cases a : AllZero b start (stop - start) <;>
        simp [f, a, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, Functor.mapConst, Except.map]
    · cases limit with
      | none => simp [f, Functor.mapConst, Except.map, pure, Except.pure]
      | some cap =>
        by_cases o : cap < 8 * (stop - start - 1) + highestBit (b.get! (stop - 1)) <;>
          simp [f, o, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind, Functor.mapConst, Except.map,
            pure, Except.pure]

/-- Variables equal as functions run the same. -/
theorem wp_env_eq {m : Module} {w : World} {sp : Nat} {s : Stmt} {env env' : Env} {mem : Memory}
    {Q : Env → Memory → Prop} (h : env' = env) (k : Wp m w sp s env mem Q) : Wp m w sp s env' mem Q := h ▸ k

/-- One step of the search: the shift's test and the position it records. -/
def seek (y : UInt64) (k : Nat) (h : UInt64) : UInt64 :=
  if (if y >>> k.toUInt64 = 0 then (0 : UInt64) else 1) ≠ 0 then k.toUInt64 else h

/-- The search is its seven steps, the highest last. -/
theorem highest_seek (y : UInt64) :
    highest y = seek y 7 (seek y 6 (seek y 5 (seek y 4 (seek y 3 (seek y 2 (seek y 1 0)))))) := rfl

/-- One guarded step of the search, run from any variables. -/
theorem seek_step {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {Q : Env → Memory → Prop}
    {rest : List Stmt} (y : UInt64) (k : Nat) (hk : k < 64) (h7 : env 7 = y)
    (next : Wp m w sp (.block rest) (assign env 10 (seek y k (env 10))) mem Q) :
    Wp m w sp (.block (when (Expr.ne (.shr (Expr.var 7) k) 0) [(⟨10⟩ : Var) ::= ((k : Nat) : Expr)] :: rest))
      env mem Q := by
  refine Wp.when_assign (cv := if y >>> k.toUInt64 = 0 then 0 else 1) (ev := k.toUInt64) ?_ ?_ ?_
  · simp [eval_ne, eval_shr, h7, hk]
  · rfl
  · exact next

/-- The search for the highest set bit, as seven guarded steps. -/
theorem seek_all {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {Q : Env → Memory → Prop}
    {rest : List Stmt} (y : UInt64) (h7 : env 7 = y) (h10 : env 10 = 0)
    (next : Wp m w sp (.block rest) (assign env 10 (highest y)) mem Q) :
    Wp m w sp (.block ((List.range 7).map (fun k => when (Expr.ne (.shr (Expr.var 7) (k + 1)) 0)
      [(⟨10⟩ : Var) ::= ((k + 1 : Nat) : Expr)]) ++ rest)) env mem Q := by
  simp only [List.range, List.range.loop, List.map, List.cons_append, List.nil_append]
  have a7 : ∀ (e : Env) (j : Nat) (v : UInt64), j ≠ 7 → e 7 = y → assign e j v 7 = y := by
    intro e j v hj h; simp [Asm.assign, h]; intro c; omega
  refine seek_step y 1 (by omega) h7 ?_
  refine seek_step y 2 (by omega) (a7 _ _ _ (by omega) h7) ?_
  refine seek_step y 3 (by omega) (a7 _ _ _ (by omega) (a7 _ _ _ (by omega) h7)) ?_
  refine seek_step y 4 (by omega) (by simp [Asm.assign, h7]) ?_
  refine seek_step y 5 (by omega) (by simp [Asm.assign, h7]) ?_
  refine seek_step y 6 (by omega) (by simp [Asm.assign, h7]) ?_
  refine seek_step y 7 (by omega) (by simp [Asm.assign, h7]) ?_
  refine wp_env_eq ?_ next
  funext j; simp only [Asm.assign]; split
  · simp [highest_seek, h10]
  · rfl

/-- What checking a delimited bit encoding computes, a limit given as its presence and its value. -/
def delimitedOutcome (b : ByteArray) (start stop has lim : Nat) : Except Err Unit :=
  Functor.discard (delimitedCount b start stop (Plan.readBound has lim))

set_option maxHeartbeats 1000000 in
/-- Checking a delimited bit encoding natively refuses exactly as the Lean check does. -/
theorem delimited_calls {m : Module} {w : World} (hm : Loaded m) (mem : Memory) (base : Nat) (b : ByteArray)
    (start stop has lim err sp : Nat) (hle : start ≤ stop) (hs : stop ≤ b.size) (small : b.size < 2 ^ 60)
    (hhas : has < 2 ^ 64)
    (hlim : lim < 2 ^ 64) (hd : DataAt w mem base b) (ok : w.access err 32 = true)
    (room : Room w sp 0 2) :
    Calls m w "ssz_validate_delimited" sp [UInt64.ofNat (base + start), UInt64.ofNat (base + stop), UInt64.ofNat has,
      UInt64.ofNat lim, UInt64.ofNat err] mem
      (res (delimitedOutcome b start stop has lim)) (after mem err (delimitedOutcome b start stop has lim)) := by
  have db := hd.bound
  have eb : err + 32 ≤ 2 ^ 63 := by
    have := ok; simp only [World.access, Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  refine Calls.body 17 hm.delimited rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [delimitedFn, delimitedOutcome, discard_delimited]
  simp only [List.range, List.range.loop, List.map, List.cons_append, List.nil_append]
  have hsz : base + stop - (base + start) = stop - start := by omega
  wsteps [hsz]
  by_cases z : stop - start = 0
  · wsteps [hsz, z]
    wfail []
    wsteps []
    wfin [z, res, after, wrote_eq]
  · have rf : readLE mem (base + stop - 1) 1 = UInt64.ofNat (b.get! (stop - 1)).toNat := by
      rw [show base + stop - 1 = base + (stop - 1) by omega]; exact hd.byteAt _ (by omega)
    have af : w.access (base + stop - 1) 1 = true := by
      rw [show base + stop - 1 = base + (stop - 1) by omega]; exact hd.byteOk _ (by omega)
    have hbyte := (b.get! (stop - 1)).toNat_lt
    wsteps [hsz, z, rf, af]
    by_cases f : (b.get! (stop - 1)).toNat = 0
    · rw [ite_eq_right z, ite_eq_left f]
      wsteps [f]
      refine Wp.loop (wp_loop (fun env mem' => mem' = mem ∧ ∃ i, i ≤ stop - start ∧ env 8 = UInt64.ofNat i ∧
          env 6 = UInt64.ofNat (stop - start) ∧ env 4 = UInt64.ofNat err ∧ env 5 = 0 ∧ env 0 = UInt64.ofNat (base + start) ∧
          ((env 9 = 1 ∧ AllZero b start i) ∨ (env 9 = 0 ∧ ¬ AllZero b start (stop - start))))
        (fun env _ => stop - start - (env 8).toNat)
        ⟨rfl, 0, Nat.zero_le _, by wfin [], by wfin [], by wfin [], by wfin [], by wfin [],
          Or.inl ⟨by wfin [], fun k hk => absurd hk (Nat.not_lt_zero k)⟩⟩ ?_)
      rintro env mem' ⟨hmem, i, hi, h8, h6, h4, h5, h0, zs⟩
      subst mem'
      rcases zs with ⟨h9, all⟩ | ⟨h9, notall⟩
      · refine ⟨_, by wev [h8, h6, h9], fun nz => ?_, fun z' => ?_⟩
        · have hlt : i < stop - start := by
            rcases Nat.lt_or_ge i (stop - start) with h | h
            · exact h
            · simp [show ¬ i < stop - start by omega] at nz
          have ri : readLE mem (base + start + i) 1 = UInt64.ofNat (b.get! (start + i)).toNat := by
            rw [show base + start + i = base + (start + i) by omega]; exact hd.byteAt _ (by omega)
          have ai : w.access (base + start + i) 1 = true := by
            rw [show base + start + i = base + (start + i) by omega]; exact hd.byteOk _ (by omega)
          have hbi := (b.get! (start + i)).toNat_lt
          wwhen [h0, h8, ri, ai]
          wsteps [h8]
          by_cases bz : (b.get! (start + i)).toNat = 0
          · refine ⟨⟨trivial, i + 1, by omega, by wfin [], by wfin [h6], by wfin [h4], by wfin [h5], by wfin [h0],
              Or.inl ⟨by wfin [bz, h9], fun k hk => ?_⟩⟩, by wfin [h8]⟩
            rcases Nat.lt_or_ge k i with h | h
            · exact all k h
            · rw [show k = i by omega]; exact bz
          · refine ⟨⟨trivial, i + 1, by omega, by wfin [], by wfin [h6], by wfin [h4], by wfin [h5], by wfin [h0],
              Or.inr ⟨by wfin [bz], fun a => bz (a i hlt)⟩⟩, by wfin [h8]⟩
        · have hie : i = stop - start := by
            rcases Nat.lt_or_ge i (stop - start) with h | h
            · simp [h] at z'
            · omega
          subst hie
          wsteps [h9]
          wfail [h4]
          wsteps []
          wfin [res, after, wrote_eq, all]
      · refine ⟨_, by wev [h8, h6, h9], fun nz => absurd (by wonly []) nz, fun _ => ?_⟩
        wsteps [h9]
        wfail [h4]
        wsteps []
        wfin [res, after, wrote_eq, notall]
    · rw [ite_eq_right z, ite_eq_right f]
      wsteps [f]
      have hh := highest_eq (b.get! (stop - 1))
      generalize hy : (b.get! (stop - 1)).toNat = y at rf hbyte f hh
      refine seek_all (UInt64.ofNat y) (by wonly []) (by wonly []) ?_
      rw [hh]
      have hb7 : highestBit (b.get! (stop - 1)) ≤ 7 := by
        simp only [highestBit]; split <;> (try omega) <;> split <;> (try omega) <;> split <;> (try omega) <;>
          split <;> (try omega) <;> split <;> (try omega) <;> split <;> (try omega) <;> split <;> omega
      wsteps [hsz]
      by_cases hz : has = 0
      · wsteps [hz]
        wfin [Plan.readBound, hz, res, after]
      · by_cases o : lim < 8 * (stop - start - 1) + highestBit (b.get! (stop - 1))
        · wsteps [hz, o]
          wfail []
          wsteps []
          wfin [Plan.readBound, beq_iff_eq, hz, o, res, after, wrote_eq]
        · wsteps [hz, o]
          wfin [Plan.readBound, beq_iff_eq, hz, o, res, after]

end EthLib.Consensus.Ssz.Native.Driver.Validate
