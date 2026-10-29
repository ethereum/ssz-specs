import SszNative.Proofs.Driver.Root
import SszNative.Proofs.Driver.Tree
import SszNative.Proofs.Kernel.Detect
import SszNative.Driver.Gather

/-!
The gather dispatcher gathers fields exactly as the general gather does.

Every gathering kernel has the same meaning: each record's field, copied into its slot and padded with zeros.
The dispatcher reads the shape and the feature mask, and calls one kernel: an AVX one for a width and a slot it
handles, when the mask says the processor runs it, and the general one otherwise.
So whichever kernel runs, the memory after is the gathered memory.
-/

namespace Ssz.Native.Driver

open Ssz.Native.Ir Ssz.Native.Ir.Expr Ssz.Native.Ir.Stmt Ssz.Native.Asm

/-- The field widths with an AVX gather into 32-byte slots. -/
abbrev narrowWidths : List Nat := [1, 2, 4, 8, 16, 32]

/-- A module holds a gathering kernel under a name, as a routine outside the language with its proved meaning. -/
def GatherAt (m : Module) (name : String) (code : Array Instr) (fixed : Option (Nat × Nat)) : Prop :=
  m.fns.lookup name = none ∧ m.ext.lookup name = some (gatherExtern code fixed)

/-- A module holding the gather dispatcher, and the gathering kernels it calls, under their exported names. -/
structure GatherModule (m : Module) : Prop where
  /-- The dispatcher, compiled from the language. -/
  dispatcher : m.fns.lookup "ssz_gather_field" = some gatherField
  /-- The general gather. -/
  general : GatherAt m "ssz_gather" Kernel.gather none
  /-- The AVX gather for each narrow width into 32-byte slots. -/
  node : ∀ k ∈ narrowWidths, GatherAt m s!"ssz_gather_{k}" (Kernel.gatherNode k) (some (k, 32 - k))
  /-- The AVX gather of 48-byte keys into 64-byte slots. -/
  key : GatherAt m "ssz_gather_key" Kernel.gatherKey (some (48, 16))

/-- The processor runs the AVX gathers when the feature mask's third bit is set. -/
def GatherKernelsRun (w : World) (mask : UInt64) : Prop :=
  mask &&& 4 ≠ 0 → (∀ k, w.cpu.runs (Kernel.gatherNode k) = true) ∧ w.cpu.runs Kernel.gatherKey = true

/-- The mask the detection routine returns lets the dispatcher call the AVX gathers it chooses. -/
theorem gatherKernelsRun_featureMask (w : World) : GatherKernelsRun w w.cpu.featureMask := fun bit =>
  ⟨fun k => (Kernel.runs_of_mask_avx w.cpu k bit).1, (Kernel.runs_of_mask_avx w.cpu 0 bit).2⟩

/-- The dispatcher's frame holds seventeen words. -/
theorem gatherFieldFrame : gatherField.frame = 17 := by decide

/-- The stack a call to the dispatcher needs: its return address and frame, then a kernel's return address. -/
abbrev gatherStack : Nat := 152

/--
What a call to the gather dispatcher does, for every gather meeting the kernels' conditions.

The shape's three words and the feature mask are in memory, and the processor runs the gathers the mask names.
The memory after is the gathered memory, whichever kernel ran.
-/
def GatherCalls (m : Module) (w : World) : Prop :=
  ∀ (sp : Nat) (mem : Memory) (out src count width skip pad : UInt64) (shape ctx : Nat) (mask : UInt64),
    GatherPre w out.toNat src.toNat count.toNat width.toNat skip.toNat pad.toNat →
    w.access shape 24 = true → readLE mem shape 8 = width → readLE mem (shape + 8) 8 = skip →
    readLE mem (shape + 16) 8 = pad → w.access ctx 8 = true → readLE mem ctx 8 = mask →
    GatherKernelsRun w mask → w.stackLo + gatherStack ≤ sp →
    ∃ r, Calls m w "ssz_gather_field" sp [out, src, count, UInt64.ofNat shape, UInt64.ofNat ctx] mem r
      (gathered mem out.toNat src.toNat count.toNat width.toNat skip.toNat pad.toNat)

variable {m : Module} {w : World}

/-- A gathering kernel the processor runs, called on a gather meeting its conditions, gathers. -/
theorem gather_call {name : String} {code : Array Instr} {fixed : Option (Nat × Nat)} {sp : Nat} {mem : Memory}
    {out src count width skip pad : UInt64} (h : GatherAt m name code fixed) (runs : w.cpu.runs code = true)
    (fix : ∀ f ∈ fixed, width.toNat = f.1 ∧ pad.toNat = f.2)
    (pre : GatherPre w out.toNat src.toNat count.toNat width.toNat skip.toNat pad.toNat) (room : w.stackLo + 8 ≤ sp) :
    Calls m w name sp [out, src, count, width, skip, pad] mem 0
      (gathered mem out.toNat src.toNat count.toNat width.toNat skip.toNat pad.toNat) :=
  Calls.ext h.1 h.2 room (by simp only [gatherExtern]; rw [if_pos ⟨runs, fix, pre⟩])

/-- The variables a gather's call reads, as the dispatcher loads them. -/
structure GatherEnv (env : Env) (out src count width skip pad : UInt64) : Prop where
  /-- The output. -/
  out : env 0 = out
  /-- The first field. -/
  src : env 1 = src
  /-- The count. -/
  count : env 2 = count
  /-- The width. -/
  width : env 5 = width
  /-- The skip. -/
  skip : env 6 = skip
  /-- The pad. -/
  pad : env 7 = pad

/-- Writing the path or the sink keeps the variables a gather's call reads. -/
theorem GatherEnv.write {env : Env} {out src count width skip pad : UInt64} (h : GatherEnv env out src count width skip pad)
    {x : Nat} (v : UInt64) (hx : x = 8 ∨ x = 9) : GatherEnv (Asm.assign env x v) out src count width skip pad := by
  rcases hx with rfl | rfl <;>
    exact ⟨by simp [Asm.assign, h.out], by simp [Asm.assign, h.src], by simp [Asm.assign, h.count],
      by simp [Asm.assign, h.width], by simp [Asm.assign, h.skip], by simp [Asm.assign, h.pad]⟩

/-- A call to one gathering kernel, then the path set to one, gathers. -/
theorem gatherCall_runs {name : String} {code : Array Instr} {fixed : Option (Nat × Nat)} {sp : Nat} {env : Env}
    {mem : Memory} {out src count width skip pad : UInt64} (h : GatherAt m name code fixed)
    (runs : w.cpu.runs code = true) (fix : ∀ f ∈ fixed, width.toNat = f.1 ∧ pad.toNat = f.2)
    (pre : GatherPre w out.toNat src.toNat count.toNat width.toNat skip.toNat pad.toNat) (room : w.stackLo + 8 ≤ sp)
    (he : GatherEnv env out src count width skip pad) :
    Runs m w sp env mem (.block [GatherVars.gatherCall name, GatherVars.path ::= 1])
      (Asm.assign (Asm.assign env 9 0) 8 1)
      (gathered mem out.toNat src.toNat count.toNat width.toNat skip.toNat pad.toNat) :=
  Runs.block_cons (Runs.call (by simp [eval, he.out, he.src, he.count, he.width, he.skip, he.pad])
    (gather_call h runs fix pre room)) (Runs.block_cons (Runs.set' rfl) (Runs.block_nil _ _ _ _ _))

/-- The guarded call of the narrow gathers for some widths: the one for the width when there is one. -/
theorem narrow_runs (mod : GatherModule m) {sp : Nat} {out src count width skip pad : UInt64}
    (cpu : ∀ k, w.cpu.runs (Kernel.gatherNode k) = true) (slot : width + pad = 32)
    (pre : GatherPre w out.toNat src.toNat count.toNat width.toNat skip.toNat pad.toNat) (room : w.stackLo + 8 ≤ sp) :
    ∀ (ks : List Nat), (∀ k ∈ ks, k ∈ narrowWidths) → ks.Nodup → ∀ (env : Env) (mem : Memory),
      GatherEnv env out src count width skip pad →
      Runs m w sp env mem (.block (ks.map fun k =>
          when (eq GatherVars.width (k : Nat)) [GatherVars.gatherCall s!"ssz_gather_{k}", GatherVars.path ::= 1]))
        (if width.toNat ∈ ks then Asm.assign (Asm.assign env 9 0) 8 1 else env)
        (if width.toNat ∈ ks then gathered mem out.toNat src.toNat count.toNat width.toNat skip.toNat pad.toNat
          else mem)
  | [], _, _, env, mem, _ => by simpa using Runs.block_nil m w sp env mem
  | k :: rest, sub, nd, env, mem, he => by
    have kn := sub k (by simp)
    have kSmall : k < 2 ^ 64 := by simp [narrowWidths] at kn; omega
    have nd' := List.nodup_cons.mp nd
    by_cases hit : width.toNat = k
    · -- The width's own gather runs, and no later width matches.
      have miss : width.toNat ∉ rest := by rw [hit]; exact nd'.1
      have eqw : width = UInt64.ofNat k := by
        apply UInt64.toNat_inj.mp; rw [hit, ofNat_toNat kSmall]
      -- A narrow width fills the slot without wrapping, so the pad is the rest of the slot.
      have padK : pad.toNat = 32 - k := by
        have sum := congrArg UInt64.toNat slot
        have kle : k ≤ 32 := by simp [narrowWidths] at kn; omega
        have pl := pad.toNat_lt
        rw [UInt64.toNat_add] at sum
        simp only [UInt64.reduceToNat] at sum
        omega
      have step := gatherCall_runs (mem := mem) (mod.node k kn) (cpu k) (by simp; omega) pre room he
      have tail := narrow_runs mod cpu slot pre room rest (fun j hj => sub j (by simp [hj])) nd'.2
        (Asm.assign (Asm.assign env 9 0) 8 1)
        (gathered mem out.toNat src.toNat count.toNat width.toNat skip.toNat pad.toNat) ((he.write 0 (Or.inr rfl)).write 1 (Or.inl rfl))
      rw [if_neg miss, if_neg miss] at tail
      have mem' : width.toNat ∈ k :: rest := by simp [hit]
      rw [if_pos mem', if_pos mem']
      exact Runs.block_cons (Runs.when_true 1 (by simp [eval, Cond.holds, he.width, eqw]) (by decide) step) tail
    · -- Another width: nothing runs, and the rest decide.
      have nev : width ≠ UInt64.ofNat k := by
        intro e; apply hit; rw [e, ofNat_toNat kSmall]
      have tail := narrow_runs mod cpu slot pre room rest (fun j hj => sub j (by simp [hj])) nd'.2 env mem he
      have same : (width.toNat ∈ k :: rest) = (width.toNat ∈ rest) := by simp [hit]
      simp only [same]
      exact Runs.block_cons (Runs.when_false (by simp [eval, Cond.holds, he.width, nev])) tail

/-- The AVX part of the dispatcher: the narrow gathers by width, then the key gather. -/
abbrev avxPart : Stmt :=
  when GatherVars.avx [when (eq (GatherVars.width + GatherVars.pad) 32) (narrowWidths.map fun k =>
      when (eq GatherVars.width (k : Nat)) [GatherVars.gatherCall s!"ssz_gather_{k}", GatherVars.path ::= 1]),
    when (eq GatherVars.width 48 &&& eq GatherVars.pad 16) [GatherVars.gatherCall "ssz_gather_key",
      GatherVars.path ::= 1]]

/-- The key test answers one exactly for a 48-byte width and a 16-byte pad. -/
theorem eval_key {env : Env} {mem : Memory} {width pad : UInt64} (hw : env 5 = width) (hp : env 7 = pad) :
    eval w env mem (eq GatherVars.width 48 &&& eq GatherVars.pad 16) =
      some (if width = 48 ∧ pad = 16 then 1 else 0) := by
  by_cases a : width = 48 <;> by_cases b : pad = 16 <;> simp [eval, Cond.holds, hw, hp, a, b]

/--
The AVX part either gathers with an AVX routine and sets the path to one, or leaves everything as it was with the
path at zero.
-/
theorem avxPart_runs (mod : GatherModule m) {sp : Nat} {env : Env} {mem : Memory} {mask : UInt64}
    {out src count width skip pad : UInt64} (he : GatherEnv env out src count width skip pad)
    (h10 : env 10 = if mask &&& 4 = 0 then 0 else 1) (h8 : env 8 = 0) (kernels : GatherKernelsRun w mask)
    (pre : GatherPre w out.toNat src.toNat count.toNat width.toNat skip.toNat pad.toNat) (room : w.stackLo + 8 ≤ sp) :
    ∃ env' mem', Runs m w sp env mem avxPart env' mem' ∧
      ((env' 8 = 0 ∧ mem' = mem ∧ GatherEnv env' out src count width skip pad) ∨
        (env' 8 = 1 ∧ mem' = gathered mem out.toNat src.toNat count.toNat width.toNat skip.toNat pad.toNat)) := by
  by_cases A : mask &&& 4 = 0
  · -- No AVX: nothing runs.
    exact ⟨env, mem, Runs.when_false (by simp [eval, h10, A]), Or.inl ⟨h8, rfl, he⟩⟩
  have cpu := kernels A
  have avxOn : eval w env mem (.var GatherVars.avx.idx) = some 1 := by simp [eval, h10, A]
  by_cases hit : width + pad = 32 ∧ width.toNat ∈ narrowWidths
  · -- A narrow width into a 32-byte slot: its own routine, and the key test fails.
    have narrow := narrow_runs mod cpu.1 hit.1 pre room narrowWidths (fun _ h => h) (by decide) env
      mem he
    rw [if_pos hit.2, if_pos hit.2] at narrow
    have small : width.toNat ≤ 32 := by have := hit.2; simp [narrowWidths] at this; omega
    have n48 : ¬ (width = 48 ∧ pad = 16) := by
      intro h; have := congrArg UInt64.toNat h.1; simp at this; omega
    have he' := (he.write 0 (Or.inr rfl)).write 1 (Or.inl rfl)
    refine ⟨_, _, Runs.when_true 1 avxOn (by decide) (Runs.block_cons
      (Runs.when_true 1 (by simp [eval, Cond.holds, he.width, he.pad, hit.1]) (by decide) narrow)
      (Runs.block_cons (Runs.when_false (by rw [eval_key he'.width he'.pad, if_neg n48]))
        (Runs.block_nil _ _ _ _ _))), Or.inr ⟨by simp [Asm.assign], rfl⟩⟩
  by_cases key : width = 48 ∧ pad = 16
  · -- A key into a 64-byte slot: the key routine.
    have n32 : width + pad ≠ 32 := by rw [key.1, key.2]; decide
    refine ⟨_, _, Runs.when_true 1 avxOn (by decide) (Runs.block_cons
      (Runs.when_false (by simp [eval, Cond.holds, he.width, he.pad, n32]))
      (Runs.block_cons (Runs.when_true 1 (by rw [eval_key he.width he.pad, if_pos key]) (by decide)
        (gatherCall_runs mod.key cpu.2 (by simp [key.1, key.2]) pre room he))
        (Runs.block_nil _ _ _ _ _))), Or.inr ⟨by simp [Asm.assign], rfl⟩⟩
  -- Any other shape: no AVX routine runs.
  have keyOff := Runs.when_false (m := m) (w := w) (sp := sp) (mem := mem) (body := [GatherVars.gatherCall "ssz_gather_key",
    GatherVars.path ::= 1]) (by rw [eval_key he.width he.pad, if_neg key])
  by_cases slot : width + pad = 32
  · have miss : width.toNat ∉ narrowWidths := fun h => hit ⟨slot, h⟩
    have narrow := narrow_runs mod cpu.1 slot pre room narrowWidths (fun _ h => h) (by decide) env
      mem he
    rw [if_neg miss, if_neg miss] at narrow
    exact ⟨_, _, Runs.when_true 1 avxOn (by decide) (Runs.block_cons
      (Runs.when_true 1 (by simp [eval, Cond.holds, he.width, he.pad, slot]) (by decide) narrow)
      (Runs.block_cons keyOff (Runs.block_nil _ _ _ _ _))), Or.inl ⟨h8, rfl, he⟩⟩
  · exact ⟨_, _, Runs.when_true 1 avxOn (by decide) (Runs.block_cons
      (Runs.when_false (by simp [eval, Cond.holds, he.width, he.pad, slot]))
      (Runs.block_cons keyOff (Runs.block_nil _ _ _ _ _))), Or.inl ⟨h8, rfl, he⟩⟩

/--
The gather dispatcher of a module holding it and its kernels gathers, whichever routine it picks.

It reads the shape and the mask before any routine runs, so the gather may write over them.
-/
theorem gatherCalls (w : World) (mod : GatherModule m) : GatherCalls m w := by
  intro sp mem out src count width skip pad shape ctx mask pre sacc s0 s8 s16 cacc cm kernels room
  have frame := gatherFieldFrame
  have stack : gatherStack = 152 := rfl
  have kroom : w.stackLo + 8 ≤ sp - 8 - 8 * gatherField.frame := by rw [frame]; omega
  let E0 := entryEnv [out, src, count, UInt64.ofNat shape, UInt64.ofNat ctx]
  let E3 := Asm.assign (Asm.assign (Asm.assign E0 5 width) 6 skip) 7 pad
  let E5 := Asm.assign (Asm.assign E3 8 0) 10 (if mask &&& 4 = 0 then 0 else 1)
  have v3 : ∀ e : Env, e 3 = UInt64.ofNat shape → eval w e mem (.var 3) = some (UInt64.ofNat shape) :=
    fun _ h => eval_var h
  -- The shape's words and the mask, loaded.
  have l0 : eval w E0 mem (ld GatherVars.shape) = some width := by
    rw [← s0]; exact eval_ld (v3 _ rfl) (access_sub sacc (Nat.le_refl _) (by omega))
  have l8 : eval w (Asm.assign E0 5 width) mem (ld (GatherVars.shape + 8)) = some skip := by
    rw [← s8]; exact eval_ld (eval_add (v3 _ rfl) (eval_lit 8)) (access_sub sacc (by omega) (by omega))
  have l16 : eval w (Asm.assign (Asm.assign E0 5 width) 6 skip) mem (ld (GatherVars.shape + 16)) = some pad := by
    rw [← s16]; exact eval_ld (eval_add (v3 _ rfl) (eval_lit 16)) (access_sub sacc (by omega) (by omega))
  have lm : eval w (Asm.assign E3 8 0) mem (Expr.ne (ld GatherVars.ctx &&& 4) 0) =
      some (if mask &&& 4 = 0 then 0 else 1) := by
    rw [← cm]; exact eval_ne (eval_and (eval_ld (eval_var rfl) cacc) (eval_lit 4)) (eval_lit 0)
  have he : GatherEnv E5 out src count width skip pad :=
    ⟨by simp [E5, E3, E0, Asm.assign, entryEnv], by simp [E5, E3, E0, Asm.assign, entryEnv],
      by simp [E5, E3, E0, Asm.assign, entryEnv], by simp [E5, E3, Asm.assign], by simp [E5, E3, Asm.assign],
      by simp [E5, E3, Asm.assign]⟩
  obtain ⟨EA, MA, avx, post⟩ := avxPart_runs mod he (by simp [E5, Asm.assign]) (by simp [E5, Asm.assign]) kernels pre
    kroom
  have start : Runs m w (sp - 8 - 8 * gatherField.frame) E0 mem (.block [GatherVars.width ::= ld GatherVars.shape,
      GatherVars.skip ::= ld (GatherVars.shape + 8), GatherVars.pad ::= ld (GatherVars.shape + 16),
      GatherVars.path ::= 0, GatherVars.avx ::= Expr.ne (ld GatherVars.ctx &&& 4) 0]) E5 mem :=
    Runs.block_cons (Runs.set' l0) (Runs.block_cons (Runs.set' l8) (Runs.block_cons (Runs.set' l16)
      (Runs.block_cons (Runs.set' rfl) (Runs.set' lm))))
  rcases post with ⟨p0, rfl, he'⟩ | ⟨p1, rfl⟩
  · -- No AVX routine ran: the general one does.
    exact ⟨_, Calls.fn mod.dispatcher (by rw [frame]; omega) rfl
      (Runs.block_append start (Runs.block_cons avx (Runs.block_cons
        (Runs.when_true 1 (by simp [eval, Cond.holds, p0]) (by decide)
          (Runs.block_cons (Runs.call (by simp [eval, he'.out, he'.src, he'.count, he'.width, he'.skip, he'.pad])
            (gather_call mod.general (Kernel.runs_gather w.cpu) (by simp) pre kroom)) (Runs.block_nil _ _ _ _ _)))
        (Runs.block_nil _ _ _ _ _)))) (eval_var rfl)⟩
  · -- An AVX routine ran and set the path, so the general one does not.
    exact ⟨_, Calls.fn mod.dispatcher (by rw [frame]; omega) rfl
      (Runs.block_append start (Runs.block_cons avx (Runs.block_cons
        (Runs.when_false (by simp [eval, Cond.holds, p1])) (Runs.block_nil _ _ _ _ _)))) (eval_var rfl)⟩

/-! ## The gathering part of a module -/

/-- The gather dispatcher, under its exported name. -/
def gatherFns : List (String × Fn) :=
  [("ssz_gather_field", gatherField)]

/-- The gathering kernels, under their exported names, each with the meaning its theorem gives. -/
noncomputable def gatherExterns : List (String × Extern) :=
  [("ssz_gather", gatherExtern Kernel.gather none),
    ("ssz_gather_1", gatherExtern (Kernel.gatherNode 1) (some (1, 31))),
    ("ssz_gather_2", gatherExtern (Kernel.gatherNode 2) (some (2, 30))),
    ("ssz_gather_4", gatherExtern (Kernel.gatherNode 4) (some (4, 28))),
    ("ssz_gather_8", gatherExtern (Kernel.gatherNode 8) (some (8, 24))),
    ("ssz_gather_16", gatherExtern (Kernel.gatherNode 16) (some (16, 16))),
    ("ssz_gather_32", gatherExtern (Kernel.gatherNode 32) (some (32, 0))),
    ("ssz_gather_key", gatherExtern Kernel.gatherKey (some (48, 16)))]

/-- The gathering kernels' exported names. -/
abbrev gatherNames : List String :=
  ["ssz_gather", "ssz_gather_1", "ssz_gather_2", "ssz_gather_4", "ssz_gather_8", "ssz_gather_16", "ssz_gather_32",
    "ssz_gather_key"]

/--
A module whose functions start with the hashing ones then the dispatcher, and whose routines start with the hashing
kernels then the gathering ones, holds the gather dispatcher and its kernels.

Its other functions must not take a gathering kernel's name, which would hide the kernel.
-/
theorem gatherModule_append (fns : List (String × Fn)) (ext : List (String × Extern))
    (fresh : ∀ name ∈ gatherNames, fns.lookup name = none) :
    GatherModule ⟨hashFns ++ gatherFns ++ fns, hashExterns ++ gatherExterns ++ ext⟩ := by
  -- Every name is found in the hashing and gathering lists, before anything else, or nowhere among the functions.
  refine ⟨?_, ⟨?_, ?_⟩, fun k hk => ?_, ⟨?_, ?_⟩⟩
  · rw [lookup_append]; rfl
  · rw [lookup_append, lookup_append, fresh _ (by simp)]; rfl
  · rw [lookup_append, lookup_append]; rfl
  · simp only [narrowWidths, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by rw [lookup_append, lookup_append, fresh _ (by decide)]; rfl, by rw [lookup_append, lookup_append]; rfl⟩
  · rw [lookup_append, lookup_append, fresh _ (by simp)]; rfl
  · rw [lookup_append, lookup_append]; rfl

end Ssz.Native.Driver
