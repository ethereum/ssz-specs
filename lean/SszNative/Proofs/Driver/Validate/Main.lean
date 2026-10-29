import SszNative.Proofs.Driver.Validate.Depth
import SszNative.Proofs.Driver.Validate.Pairs

/-!
The native decoding check, whole: the plan checked, then the encoding against it.

For a legal type nested no deeper than a plan may be, whose plan sits in memory, the plan's own check returns zero,
and the whole check returns zero exactly when the Lean check accepts the encoding, and one exactly when it refuses it,
with the refusal's four words written.
-/

namespace EthLib.Consensus.Ssz.Native.Driver.Validate

set_option maxRecDepth 20000

open EthLib.Consensus.Ssz EthLib.Consensus.Ssz.Native EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Asm EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Ir.Expr

/-! The plan's bytes, read back as its words. -/

/-- A word is eight bytes. -/
theorem wordBytes_length (x : Nat) : (Plan.wordBytes x).length = 8 := by simp [Plan.wordBytes]

/-- Words written as bytes take eight bytes each. -/
theorem flatMap_wordBytes_length : ∀ ws : List Nat, (ws.flatMap Plan.wordBytes).length = 8 * ws.length
  | [] => rfl
  | x :: ws => by simp [List.flatMap_cons, wordBytes_length, flatMap_wordBytes_length ws]; omega

/-- Each byte of words written as bytes is a byte of its word. -/
theorem flatMap_wordBytes_get : ∀ (ws : List Nat) (i k : Nat) (hi : i < ws.length) (hk : k < 8),
    (ws.flatMap Plan.wordBytes)[8 * i + k]'(by rw [flatMap_wordBytes_length]; omega) =
      UInt8.ofNat (ws[i] >>> (8 * k))
  | [], _, _, hi, _ => by simp at hi
  | x :: ws, 0, k, _, hk => by
    simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add]
    rw [List.getElem_append_left (by rw [wordBytes_length]; omega)]
    simp [Plan.wordBytes]
  | x :: ws, i + 1, k, hi, hk => by
    simp only [List.flatMap_cons]
    rw [List.getElem_append_right (by rw [wordBytes_length]; omega)]
    have := flatMap_wordBytes_get ws i k (by simp at hi; omega) hk
    simp only [wordBytes_length, List.getElem_cons_succ] at this ⊢
    rw [← this]
    congr 1
    omega

/-- The plan's bytes in memory: readable, each in its place. -/
def PlanBytes (w : World) (mem : Memory) (p : Nat) (d : Desc) : Prop :=
  w.access p (Plan.encode d).size ∧ ∀ i (h : i < (Plan.encode d).size), mem (p + i) = (Plan.encode d)[i]

/-- A plan's bytes are eight per word. -/
theorem encode_size (d : Desc) : (Plan.encode d).size = 8 * (Plan.words d).length := by
  show (List.toArray _).size = _
  rw [List.size_toArray, flatMap_wordBytes_length]

/-- A plan's bytes in memory are its words, when each word fits one. -/
theorem planAt_of_bytes {w : World} {mem : Memory} {p : Nat} {d : Desc} (h : PlanBytes w mem p d)
    (small : ∀ x ∈ Plan.words d, x < 2 ^ 64) : PlanAt w mem p (Plan.words d) := by
  refine ⟨by rw [← encode_size]; exact h.1, fun i hi => ?_⟩
  apply u64_eq
  rw [readLE_toNat _ _ _ (by omega)]
  have lt := small _ (List.getElem_mem hi)
  rw [show ((Plan.words d)[i]).toUInt64.toNat = (Plan.words d)[i] by simp; omega]
  rw [bytesNat_digits _ _ ((Plan.words d)[i]) 0 8 (fun k hk => ?_)]
  · simp; omega
  · have hb := h.2 (8 * i + k) (by rw [encode_size]; omega)
    rw [show p + 8 * i + k = p + (8 * i + k) by omega, hb]
    simp only [Plan.encode]
    show ((((Plan.words d).flatMap Plan.wordBytes).toArray)[8 * i + k]'_).toNat = _
    simp only [List.getElem_toArray, flatMap_wordBytes_get (Plan.words d) i k hi hk, Nat.zero_add]
    simp [Nat.shiftRight_eq_div_pow, Nat.pow_mul]

/-! The whole check. -/

set_option maxHeartbeats 4000000 in
/--
The plan's own check accepts the plan of a legal type nested no deeper than a plan may be.

The type names its fields by position, as a plan names them, and its widths fit the native check.
The stack holds two levels of nesting's room per level of the type, which the depth bound caps.
-/
theorem checkPlan_calls {m : Module} {w : World} (hm : Loaded m) (d : Desc)
    (wf : d.wellFormed = .ok ()) (fit : fitsNative d = true) (nm : named d = true) (deep : d.nesting ≤ maxNesting)
    (plan sp : Nat) (mem : Memory) (hplan : PlanBytes w mem plan d) (room : Room w sp (2 * d.nesting) 3) :
    Calls m w "ssz_check_plan" sp [UInt64.ofNat plan, UInt64.ofNat (Plan.encode d).size] mem 0 mem := by
  have hp := planAt_of_bytes hplan (words_lt d wf fit)
  have hb := hp.bound
  rw [encode_size d]
  -- The nesting walk reads past the plan, and so does the plan's check.
  have dc := depth_calls hm d wf fit plan (plan + 8 * (Plan.words d).length) maxNesting (sp - 8 - 8 * 7) mem hp
    (Nat.le_refl _) hb deep (by decide) (by simp only [Room] at room ⊢; omega)
  have pc := plan_calls hm d (fun _ => pairsOk hm) wf fit nm plan (plan + 8 * (Plan.words d).length) (sp - 8 - 8 * 7) mem hp
    (Nat.le_refl _) hb (by simp only [Room] at room ⊢; omega)
  have m8 : 8 * (Plan.words d).length % 8 = 0 := by omega
  have shallow : plan + 8 * (Plan.words d).length ≠ 18446744073709551614 := by omega
  refine Calls.body 7 hm.checkPlan rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [checkPlanFn]
  wsteps [m8]
  wcall dc []
  wsteps [shallow, deep_]
  wcall pc []
  wsteps []
  wfin []

set_option maxHeartbeats 4000000 in
/--
The native decoding check of a legal type's plan and an encoding returns what the Lean check gives: zero and memory
untouched when it accepts, one and the refusal's words written when it refuses.

The plan's bytes sit at one address, the encoding's at another, and the refusal's four words at a third, apart from both.
The type nests no deeper than a plan may be, and the stack holds two levels of nesting's room per level of the type.
-/
theorem validate_calls {m : Module} {w : World} (hm : Loaded m) (d : Desc)
    (wf : d.wellFormed = .ok ()) (fit : fitsNative d = true) (nm : named d = true) (deep : d.nesting ≤ maxNesting)
    (plan data err sp : Nat) (mem : Memory) (b : ByteArray)
    (hplan : PlanBytes w mem plan d) (hd : DataAt w mem data b)
    (cp : Clear err plan (Plan.encode d).size) (cd : Clear err data b.size) (ok : w.access err 32 = true)
    (small : b.size < 2 ^ 60) (room : Room w sp (2 * d.nesting) 5) :
    Calls m w "ssz_validate" sp [UInt64.ofNat plan, UInt64.ofNat (Plan.encode d).size, UInt64.ofNat data,
      UInt64.ofNat b.size, UInt64.ofNat err] mem (res (validate d b)) (after mem err (validate d b)) := by
  have hp := planAt_of_bytes hplan (words_lt d wf fit)
  have hb := hp.bound
  have db := hd.bound
  have es := encode_size d
  have cc := checkPlan_calls hm d wf fit nm deep plan (sp - 8 - 8 * 11) mem hplan
    (by simp only [Room] at room ⊢; omega)
  rw [es] at cp cc ⊢
  have rc := range_calls hm d fit plan (sp - 8 - 8 * 11) mem data b 0 b.size err hp cp hd cd ok (Nat.zero_le _)
    (Nat.le_refl _) small (by simp only [Room] at room ⊢; omega)
  simp only [Nat.add_zero] at rc
  rw [validate]
  refine Calls.body 11 hm.validate rfl (by simp only [Room] at room; omega) rfl ?_
  simp only [validateFn]
  wcall cc []
  wsteps []
  wcall rc []
  wsteps []
  wfin []

/-- The four words a refusal writes read back as its words. -/
theorem wrote_read (mem : Memory) (err : Nat) (e : Err) (i : Nat) (hi : i < 4) :
    readLE (wrote mem err e) (err + 8 * i) 8 = UInt64.ofNat (e.toWords[i]!) := by
  simp only [wrote, wrote4]
  have far : ∀ (m : Memory) (a : Nat) (v : UInt64), a + 8 ≤ err + 8 * i ∨ err + 8 * i + 8 ≤ a →
      readLE (Asm.store m a 8 (qwordByte v)) (err + 8 * i) 8 = readLE m (err + 8 * i) 8 := by
    intro m a v h
    apply readLE_congr
    intro k hk
    simp only [Asm.store]
    split
    · omega
    · rfl
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
  · rw [far _ _ _ (by omega), far _ _ _ (by omega), far _ _ _ (by omega)]
    simpa using readLE_store8 _ err _
  · rw [far _ _ _ (by omega), far _ _ _ (by omega)]
    simpa using readLE_store8 _ (err + 8) _
  · rw [far _ _ _ (by omega)]
    simpa using readLE_store8 _ (err + 16) _
  · simpa using readLE_store8 _ (err + 24) _

/--
The native decoding check, as the task states it.

For every legal type, its fields named by position as a plan names them, nested no deeper than a plan may be, whose
widths fit the native check, with the plan's bytes and an encoding's bytes in memory: the call returns zero with memory untouched exactly when the Lean check
accepts the encoding, and one exactly when it refuses it, with the refusal's words at the refusal's address.
-/
theorem validate_correct {m : Module} {w : World} (hm : Loaded m) (d : Desc)
    (wf : d.wellFormed = .ok ()) (fit : fitsNative d = true) (nm : named d = true) (deep : d.nesting ≤ maxNesting)
    (plan data err sp : Nat) (mem : Memory) (b : ByteArray)
    (hplan : PlanBytes w mem plan d) (hd : DataAt w mem data b)
    (cp : Clear err plan (Plan.encode d).size) (cd : Clear err data b.size) (ok : w.access err 32 = true)
    (small : b.size < 2 ^ 60) (room : Room w sp (2 * d.nesting) 5) :
    ∃ r mem', Calls m w "ssz_validate" sp [UInt64.ofNat plan, UInt64.ofNat (Plan.encode d).size, UInt64.ofNat data,
        UInt64.ofNat b.size, UInt64.ofNat err] mem r mem' ∧
      ((validate d b = .ok () ∧ r = 0 ∧ mem' = mem) ∨
       (∃ e, validate d b = .error e ∧ r = 1 ∧
          ∀ i < 4, readLE mem' (err + 8 * i) 8 = UInt64.ofNat (e.toWords[i]!))) := by
  refine ⟨_, _, validate_calls hm d wf fit nm deep plan data err sp mem b hplan hd cp cd ok small room, ?_⟩
  cases h : validate d b with
  | ok u => left; exact ⟨rfl, rfl, rfl⟩
  | error e => right; exact ⟨e, rfl, rfl, fun i hi => wrote_read mem err e i hi⟩

end EthLib.Consensus.Ssz.Native.Driver.Validate
