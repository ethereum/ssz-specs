import SszNative.Proofs.Driver.Root.Size
import SszNative.Proofs.Root.Bytes

/-!
The fixed-size roots driver roots one record of a container as the Lean computation does.

Each field gets one node of a buffer, in order.
A field that fits one node is copied into a zeroed node, so its node is its bytes, zero-padded.
Any other field's root is written into its node by a call of the driver on the field's type.
The tree over the field nodes is the record's root.

The Lean computation writes the same nodes into a zero buffer with byte copies.
The proof follows the fields one at a time, with memory holding the nodes written so far.
What a call on a field's type does is taken as a hypothesis, so the proof is one step of an induction on the type.
-/

namespace EthLib.Consensus.Ssz.Native.Driver

open EthLib.Consensus.Ssz.Native.Ir EthLib.Consensus.Ssz.Native.Ir.Expr EthLib.Consensus.Ssz.Native.Ir.Stmt EthLib.Consensus.Ssz.Native.Asm

/-! ### Copies as buffers -/

/--
Memory after a copy holds the Lean copy of the buffers it held.

The source buffer and the destination buffer are both in memory, and the copied range lies inside each.
-/
theorem holds_copied {mem : Memory} {sa da : Nat} {src dest : ByteArray} (hs : Holds mem sa src)
    (hd : Holds mem da dest) {so d len : Nat} (inSrc : so + len ≤ src.size) (inDest : d + len ≤ dest.size) :
    Holds (copied mem (da + d) (sa + so) len) da (src.copySlice so dest d len) := by
  intro x hx
  rw [copySlice_size _ _ _ _ _ inSrc inDest] at hx
  rw [copySlice_get _ _ _ _ _ _ inSrc inDest hx]
  simp only [copied, Asm.store]
  split
  · -- Inside the copied range, the byte comes from the source.
    rw [ite_eq_left (by omega), show sa + so + (da + x - (da + d)) = sa + (so + (x - d)) by omega]
    exact hs _ (by omega)
  · -- Elsewhere, the destination's byte stays.
    rw [ite_eq_right (by omega)]
    exact hd x hx

/-- Memory holding a buffer holds its first bytes. -/
theorem _root_.EthLib.Consensus.Ssz.Native.Holds.take {mem : Memory} {a : Nat} {bytes : ByteArray} (h : Holds mem a bytes) (n : Nat) :
    Holds mem a (bytes.extract 0 n) := by
  intro i hi
  rw [ByteArray.size_extract] at hi
  rw [h i (by omega), Kernel.get!_eq _ _ (by omega), Kernel.get!_eq _ _ (by rw [ByteArray.size_extract]; omega),
    ByteArray.getElem_extract]
  simp only [Nat.zero_add]

/-- A copy that ends inside the first bytes of a buffer reads the same from those first bytes. -/
theorem copySlice_extract (src dest : ByteArray) (so d len n : Nat) (inSrc : so + len ≤ src.size)
    (ends : d + len ≤ n) (inDest : n ≤ dest.size) :
    src.copySlice so (dest.extract 0 n) d len = (src.copySlice so dest d len).extract 0 n := by
  have sz : (dest.extract 0 n).size = n := by rw [ByteArray.size_extract]; omega
  apply ByteArray.ext
  apply Array.ext
  · show (src.copySlice so (dest.extract 0 n) d len).size = ((src.copySlice so dest d len).extract 0 n).size
    rw [copySlice_size _ _ _ _ _ inSrc (by omega), sz, ByteArray.size_extract,
      copySlice_size _ _ _ _ _ inSrc (by omega)]
    omega
  · intro i h1 h2
    have hi : i < n := by
      have : (src.copySlice so (dest.extract 0 n) d len).size = n := by
        rw [copySlice_size _ _ _ _ _ inSrc (by omega), sz]
      exact this ▸ h1
    -- Compare byte by byte, through the copy's reading on each side.
    have left := copySlice_get src (dest.extract 0 n) so d len i inSrc (by omega) (by omega)
    have right := copySlice_get src dest so d len i inSrc (by omega) (by omega)
    rw [Kernel.get!_eq _ _ (by rw [copySlice_size _ _ _ _ _ inSrc (by omega), sz]; exact hi)] at left
    rw [Kernel.get!_eq _ _ (by rw [copySlice_size _ _ _ _ _ inSrc (by omega)]; omega)] at right
    show (src.copySlice so (dest.extract 0 n) d len)[i] = ((src.copySlice so dest d len).extract 0 n)[i]
    rw [left, ByteArray.getElem_extract]
    simp only [Nat.zero_add]
    rw [right]
    split
    · rfl
    · rw [Kernel.get!_eq _ _ (by omega), Kernel.get!_eq _ _ (by omega), ByteArray.getElem_extract]
      simp only [Nat.zero_add]

/-! ### The copy loops -/

/-- A word of zero stores zero bytes. -/
theorem qwordByte_of_zero (k : Nat) : qwordByte 0 k = 0 := by simp [qwordByte]

/-- Memory with a node of zeros stored at an address. -/
def zeroed (mem : Memory) (a : Nat) : Memory :=
  store mem a 32 fun _ => 0

/-- The four word stores of zero write a node of zeros. -/
theorem zero32_runs {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {slot : Nat}
    (hs : env RootsOf.slot.idx = UInt64.ofNat slot) (acc : w.access slot 32 = true) :
    Runs m w sp env mem (.block (zero32 RootsOf.slot)) env (zeroed mem slot) := by
  have bound : slot + 32 < 2 ^ 64 := by have := access_end acc; omega
  have st := fun (mm : Memory) (k : Nat) (hk : k + 8 ≤ 32) =>
    Runs.store m w sp env mm .b8 (RootsOf.slot + ((k : Nat) : Expr)) (0 : Expr) (UInt64.ofNat (slot + k)) 0
      (eval_add (eval_var hs) (eval_cast k)) rfl
      (by rw [ofNat_toNat (by omega)]; exact access_sub acc (by omega) (by simp only [Width.bytes]; omega))
  refine Runs.block_cons (st mem 0 (by decide)) (Runs.block_cons (st _ 8 (by decide)) (Runs.block_cons
    (st _ 16 (by decide)) (Runs.block_cons (st _ 24 (by decide)) ?_)))
  have same : ∀ mm : Memory, mm = zeroed mem slot → Runs m w sp env mm (.block []) env (zeroed mem slot) :=
    fun mm h => h ▸ Runs.block_nil _ _ _ _ _
  apply same
  funext a
  simp only [zeroed, Asm.store, ofNat_toNat (show slot + 0 < 2 ^ 64 by omega), ofNat_toNat (show slot + 8 < 2 ^ 64 by omega),
    ofNat_toNat (show slot + 16 < 2 ^ 64 by omega), ofNat_toNat (show slot + 24 < 2 ^ 64 by omega), Width.bytes,
    qwordByte_of_zero]
  by_cases h0 : slot ≤ a ∧ a < slot + 32
  · rw [ite_eq_left h0]; repeat' split
    all_goals first | rfl | omega
  · rw [ite_eq_right h0, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- One byte a program may use, loaded. -/
theorem eval_ld1_of {w : World} {env : Env} {mem : Memory} {a : Expr} {n : Nat}
    (ha : eval w env mem a = some (UInt64.ofNat n)) (acc : w.access n 1 = true) :
    eval w env mem (ld1 a) = some (readLE mem n 1) := by
  have bn : n < 2 ^ 64 := by have := access_bound acc; omega
  show eval w env mem (.load .b1 a) = _
  simp only [eval, ha, Option.bind_eq_bind, Option.bind, ofNat_toNat bn, Width.bytes, acc]
  rfl

/-- The statements that copy a field's bytes into its node: whole words first, then single bytes. -/
abbrev copyLoops : List Stmt :=
  [RootsOf.k ::= 0,
    while_ (le (RootsOf.k + 8) RootsOf.w)
      [st (RootsOf.slot + RootsOf.k) (ld (RootsOf.src + RootsOf.off + RootsOf.k)), RootsOf.k ::= RootsOf.k + 8],
    while_ (lt RootsOf.k RootsOf.w)
      [st1 (RootsOf.slot + RootsOf.k) (ld1 (RootsOf.src + RootsOf.off + RootsOf.k)), RootsOf.k ::= RootsOf.k + 1]]

/--
The copy loops copy a field's bytes to its node.

The bytes start at the record's address plus the field's offset, and both ranges are usable and apart.
Only the byte index changes among the variables, and it ends at the width.
-/
theorem copyLoops_runs {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {slot a o width : Nat}
    (hs : env RootsOf.slot.idx = UInt64.ofNat slot) (ha : env RootsOf.src.idx = UInt64.ofNat a)
    (ho : env RootsOf.off.idx = UInt64.ofNat o) (hw : env RootsOf.w.idx = UInt64.ofNat width)
    (sAcc : w.access (a + o) width = true) (dAcc : w.access slot width = true)
    (apart : a + o + width ≤ slot ∨ slot + width ≤ a + o) :
    Runs m w sp env mem (.block copyLoops) (Asm.assign env 17 (UInt64.ofNat width)) (copied mem slot (a + o) width) := by
  have sb := access_end sAcc
  have db := access_end dAcc
  -- The variables other than the index stay through both loops.
  have keep : ∀ k y, y ≠ 17 → Asm.assign env 17 (UInt64.ofNat k) y = env y := fun _ _ h => assign_ne h
  have sV := fun k => (keep k 16 (by decide)).trans hs
  have aV := fun k => (keep k 1 (by decide)).trans ha
  have oV := fun k => (keep k 15 (by decide)).trans ho
  have wV := fun k => (keep k 9 (by decide)).trans hw
  have srcAt : ∀ k mm, eval w (Asm.assign env 17 (UInt64.ofNat k)) mm (RootsOf.src + RootsOf.off + RootsOf.k) =
      some (UInt64.ofNat (a + o + k)) :=
    fun k _ => eval_add (eval_add (eval_var (aV k)) (eval_var (oV k))) (eval_var assign_eq)
  have dstAt : ∀ k mm, eval w (Asm.assign env 17 (UInt64.ofNat k)) mm (RootsOf.slot + RootsOf.k) =
      some (UInt64.ofNat (slot + k)) :=
    fun k _ => eval_add (eval_var (sV k)) (eval_var assign_eq)
  -- Whole words, while eight more bytes fit.
  let inv₁ : Env → Memory → Prop := fun e mm =>
    ∃ k, k ≤ width ∧ e = Asm.assign env 17 (UInt64.ofNat k) ∧ mm = copied mem slot (a + o) k
  have loop₁ := Runs.loop_inv (m := m) (w := w) (sp := sp) (c := le (RootsOf.k + 8) RootsOf.w)
    (body := .block [st (RootsOf.slot + RootsOf.k) (ld (RootsOf.src + RootsOf.off + RootsOf.k)),
      RootsOf.k ::= RootsOf.k + 8])
    inv₁ (fun e _ => width + 8 - (e 17).toNat)
    (fun e mm ⟨k, hk, he, _⟩ => ⟨_, he ▸ eval_le (eval_add (eval_var assign_eq) (eval_lit 8)) (eval_var (wV k))
      (by omega) (by omega)⟩)
    (by
      rintro e mm v ⟨k, hk, rfl, rfl⟩ hv nz
      have c := eval_le (w := w) (mem := copied mem slot (a + o) k) (eval_add (eval_var assign_eq) (eval_lit 8))
        (eval_var (wV k)) (show k + 8 < 2 ^ 64 by omega) (show width < 2 ^ 64 by omega)
      rw [hv] at c
      have more : k + 8 ≤ width := by
        by_cases h : k + 8 ≤ width
        · exact h
        · rw [ite_eq_right h] at c; cases c; exact absurd rfl nz
      have stored := Runs.store m w sp (Asm.assign env 17 (UInt64.ofNat k)) (copied mem slot (a + o) k) .b8 _ _ _ _
        (dstAt k _) (eval_ld (srcAt k _) (access_sub sAcc (by omega) (by omega)))
        (by rw [ofNat_toNat (by omega)]; exact access_sub dAcc (by omega) (by simp only [Width.bytes]; omega))
      rw [ofNat_toNat (by omega), Width.bytes,
        copied_more mem slot (a + o) k 8 (by omega) (store_load _ _ _)] at stored
      refine ⟨_, _, Runs.block_cons stored (Runs.block_cons (Runs.set' (eval_add (eval_var assign_eq) (eval_lit 8)))
        (Runs.block_nil _ _ _ _ _)), ⟨k + 8, more, by rw [assign_assign], rfl⟩, ?_⟩
      simp only [assign_eq]
      rw [ofNat_toNat (by omega), ofNat_toNat (by omega)]
      omega)
  obtain ⟨e₁, m₁, run₁, ⟨k₁, hk₁, rfl, rfl⟩, exit₁⟩ :=
    loop₁ _ _ ⟨0, Nat.zero_le _, rfl, (copied_zero _ _ _).symm⟩
  have stop₁ : ¬ k₁ + 8 ≤ width := by
    have c := eval_le (w := w) (mem := copied mem slot (a + o) k₁) (eval_add (eval_var assign_eq) (eval_lit 8))
      (eval_var (wV k₁)) (show k₁ + 8 < 2 ^ 64 by omega) (show width < 2 ^ 64 by omega)
    rw [exit₁] at c
    intro h; rw [ite_eq_left h] at c; cases c
  -- Then single bytes, while any are left.
  let inv₂ : Env → Memory → Prop := fun e mm =>
    ∃ k, k ≤ width ∧ e = Asm.assign env 17 (UInt64.ofNat k) ∧ mm = copied mem slot (a + o) k
  have loop₂ := Runs.loop_inv (m := m) (w := w) (sp := sp) (c := lt RootsOf.k RootsOf.w)
    (body := .block [st1 (RootsOf.slot + RootsOf.k) (ld1 (RootsOf.src + RootsOf.off + RootsOf.k)),
      RootsOf.k ::= RootsOf.k + 1])
    inv₂ (fun e _ => width + 1 - (e 17).toNat)
    (fun e mm ⟨k, hk, he, _⟩ => ⟨_, he ▸ eval_lt (eval_var assign_eq) (eval_var (wV k)) (by omega) (by omega)⟩)
    (by
      rintro e mm v ⟨k, hk, rfl, rfl⟩ hv nz
      have c := eval_lt (w := w) (mem := copied mem slot (a + o) k) (eval_var assign_eq) (eval_var (wV k))
        (show k < 2 ^ 64 by omega) (show width < 2 ^ 64 by omega)
      rw [hv] at c
      have more : k < width := by
        by_cases h : k < width
        · exact h
        · rw [ite_eq_right h] at c; cases c; exact absurd rfl nz
      have stored := Runs.store m w sp (Asm.assign env 17 (UInt64.ofNat k)) (copied mem slot (a + o) k) .b1 _ _ _ _
        (dstAt k _) (eval_ld1_of (srcAt k _) (access_sub sAcc (by omega) (by omega)))
        (by rw [ofNat_toNat (by omega)]; exact access_sub dAcc (by omega) (by simp only [Width.bytes]; omega))
      rw [ofNat_toNat (by omega), Width.bytes,
        copied_more mem slot (a + o) k 1 (by omega) (store_load1 _ _ _)] at stored
      refine ⟨_, _, Runs.block_cons stored (Runs.block_cons (Runs.set' (eval_add (eval_var assign_eq) (eval_lit 1)))
        (Runs.block_nil _ _ _ _ _)), ⟨k + 1, more, by rw [assign_assign], rfl⟩, ?_⟩
      simp only [assign_eq]
      rw [ofNat_toNat (by omega), ofNat_toNat (by omega)]
      omega)
  obtain ⟨e₂, m₂, run₂, ⟨k₂, hk₂, rfl, rfl⟩, exit₂⟩ := loop₂ _ _ ⟨k₁, hk₁, rfl, rfl⟩
  have stop₂ : k₂ = width := by
    have c := eval_lt (w := w) (mem := copied mem slot (a + o) k₂) (eval_var assign_eq) (eval_var (wV k₂))
      (show k₂ < 2 ^ 64 by omega) (show width < 2 ^ 64 by omega)
    rw [exit₂] at c
    by_cases h : k₂ < width
    · rw [ite_eq_left h] at c; cases c
    · omega
  subst stop₂
  exact Runs.block_cons (Runs.set' (eval_lit 0)) (Runs.block_cons run₁ (Runs.block_cons run₂ (Runs.block_nil _ _ _ _ _)))

/-- The copy into a field's node: a node of zeros, then the field's bytes over its start. -/
theorem copyLeaf_runs {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {slot a o width : Nat}
    (hs : env RootsOf.slot.idx = UInt64.ofNat slot) (ha : env RootsOf.src.idx = UInt64.ofNat a)
    (ho : env RootsOf.off.idx = UInt64.ofNat o) (hw : env RootsOf.w.idx = UInt64.ofNat width)
    (wide : width ≤ 32) (sAcc : w.access (a + o) width = true) (dAcc : w.access slot 32 = true)
    (apart : a + o + width ≤ slot ∨ slot + 32 ≤ a + o) :
    Runs m w sp env mem (.block RootsOf.copyLeaf) (Asm.assign env 17 (UInt64.ofNat width))
      (copied (zeroed mem slot) slot (a + o) width) :=
  Runs.block_append (zero32_runs hs dAcc)
    (copyLoops_runs hs ha ho hw sAcc (access_sub dAcc (Nat.le_refl _) (by omega)) (by omega))

/-! ### Whether a field packs -/

/-- A truth value as a word: one or zero. -/
theorem bitOf_ofNat (b : Bool) : bitOf b = UInt64.ofNat (if b then 1 else 0) := by cases b <;> rfl

/--
The packing test answers whether a field's root is its own bytes, zero-padded, from the field's plan node.

Only the tag and the test's answer change among the variables.
-/
theorem packsInto_runs {m : Module} {w : World} {sp : Nat} {env : Env} {mem : Memory} {f : Desc} {q : Nat}
    (hw : WordsAt w mem q (Plan.words f)) (he : env RootsOf.e.idx = UInt64.ofNat q) (thin : narrow f = true) :
    ∃ t, Runs m w sp env mem (.block RootsOf.packsInto)
      (Asm.assign (Asm.assign env 18 t) 19 (bitOf (packsIntoNode f))) mem := by
  have tagR := eval_tag (env := env) (e := (RootsOf.e : Expr)) hw (eval_var he)
  have s1 : Runs m w sp env mem (RootsOf.te ::= ld RootsOf.e) (Asm.assign env 18 (Plan.tag f).toUInt64) mem :=
    Runs.set' tagR
  have tl := tag_lt f
  -- The tag test, in any variables still holding the tag.
  have tag2 : ∀ (e : Env), e 18 = (Plan.tag f).toUInt64 →
      eval w e mem (Expr.eq RootsOf.te 2) = some (if Plan.tag f = 2 then 1 else 0) :=
    fun e h => eval_eq (eval_var h) (eval_lit 2) (by omega) (by decide)
  have tag4 : ∀ (e : Env), e 18 = (Plan.tag f).toUInt64 →
      eval w e mem (Expr.eq RootsOf.te 4) = some (if Plan.tag f = 4 then 1 else 0) :=
    fun e h => eval_eq (eval_var h) (eval_lit 4) (by omega) (by decide)
  have c1 := eval_le (w := w) (mem := mem) (a := (RootsOf.te : Expr)) (b := (1 : Expr))
    (env := Asm.assign env 18 (Plan.tag f).toUInt64) (eval_var assign_eq) (eval_lit 1) (by omega) (by decide)
  have s2 := Runs.set' (m := m) (sp := sp) (x := RootsOf.pk.idx) c1
  -- The length word, for byte and bit vectors.
  have lenR : ∀ (e : Env) n, Plan.words f = [Plan.tag f, n] → e 8 = UInt64.ofNat q →
      eval w e mem (ld (RootsOf.e + 8)) = some (UInt64.ofNat n) := fun e n hn h => by
    have := eval_word (env := e) (e := RootsOf.e + 8) hw 1 (by rw [hn]; simp)
      (eval_add (eval_var h) (eval_lit 8))
    rw [this]; simp only [hn]; rfl
  have e8 : ∀ v t, Asm.assign (Asm.assign env 18 t) 19 v 8 = UInt64.ofNat q := fun _ _ => by
    rw [assign_ne (by decide), assign_ne (by decide), he]
  have e18 : ∀ v, Asm.assign (Asm.assign env 18 (Plan.tag f).toUInt64) 19 v 18 = (Plan.tag f).toUInt64 := fun _ => by
    rw [assign_ne (by decide), assign_eq]
  refine ⟨(Plan.tag f).toUInt64, ?_⟩
  cases f with
  | byteVector n =>
    have nb : n < 2 ^ 62 := by simpa [narrow, Desc.fixedSize] using thin
    have c := eval_le (a := ld (RootsOf.e + 8)) (b := (32 : Expr)) (lenR _ n rfl (e8 (if Plan.tag (Desc.byteVector n) ≤ 1 then 1 else 0) (Plan.tag (Desc.byteVector n)).toUInt64)) (eval_lit 32) (by omega)
      (by decide)
    refine Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons (Runs.when_true 1
      (by rw [tag2 _ (e18 _)]; rfl) (by decide)
      (Runs.block_cons (Runs.set' c) (Runs.block_nil _ _ _ _ _))) (Runs.block_cons
      (Runs.when_false (by rw [tag4 _ (by rw [assign_ne (by decide)]; exact e18 _)]; rfl)) ?_)))
    rw [assign_assign]
    have : (if n ≤ 32 then 1 else 0 : UInt64) = bitOf (packsIntoNode (.byteVector n)) := by
      simp only [packsIntoNode, bitOf]; split <;> simp_all
    rw [this]; exact Runs.block_nil _ _ _ _ _
  | bitVector n =>
    have nb : n < 2 ^ 62 := by simpa [narrow] using thin
    have c := eval_le (a := ld (RootsOf.e + 8)) (b := (256 : Expr)) (lenR _ n rfl (e8 (if Plan.tag (Desc.bitVector n) ≤ 1 then 1 else 0) (Plan.tag (Desc.bitVector n)).toUInt64)) (eval_lit 256) (by omega)
      (by decide)
    refine Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons
      (Runs.when_false (by rw [tag2 _ (e18 _)]; rfl))
      (Runs.block_cons (Runs.when_true 1 (by rw [tag4 _ (e18 _)]; rfl) (by decide)
        (Runs.block_cons (Runs.set' c) (Runs.block_nil _ _ _ _ _))) ?_)))
    rw [assign_assign]
    have : (if n ≤ 256 then 1 else 0 : UInt64) = bitOf (packsIntoNode (.bitVector n)) := by
      simp only [packsIntoNode, bitOf]; split <;> simp_all
    rw [this]; exact Runs.block_nil _ _ _ _ _
  | _ =>
    refine Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons
      (Runs.when_false (by rw [tag2 _ (e18 _)]; rfl))
      (Runs.block_cons (Runs.when_false (by rw [tag4 _ (e18 _)]; rfl)) ?_)))
    exact Runs.block_nil _ _ _ _ _

/-! ### Fields of a container -/

/-- A well-formed value that is its own root is at most one node wide. -/
theorem packs_le_node (d : Desc) (packs : packsIntoNode d = true) (sound : d.wellFormed = .ok ()) :
    fixedWidth d ≤ 32 := by
  -- Integers come in the listed widths, and byte and bit vectors are bounded by the test itself.
  cases d with
  | uint w =>
    simp only [Desc.wellFormed] at sound
    split at sound
    · rename_i listed; simp only [fixedWidth]; simp at listed; omega
    · simp at sound
  | _ => simp_all [packsIntoNode, fixedWidth] <;> omega

/-- Every type of a plain and narrow list is plain and narrow. -/
theorem plainNarrow_mem : ∀ (fs : List Desc), plainAll fs = true → narrowAll fs = true →
    ∀ f ∈ fs, plain f = true ∧ narrow f = true
  | [], _, _, f, hf => absurd hf (List.not_mem_nil)
  | g :: rest, hp, hn, f, hf => by
    simp only [plainAll, narrowAll, Bool.and_eq_true] at hp hn
    rcases List.mem_cons.mp hf with rfl | later
    · exact ⟨hp.1, hn.1⟩
    · exact plainNarrow_mem rest hp.2 hn.2 f later

/-- Every field of a type the driver serves is served too. -/
theorem rootable_fields {names : List String} {fields : List Desc} (ok : Rootable (.container names fields)) :
    ∀ f ∈ fields, Rootable f := by
  obtain ⟨pl, wf, thin⟩ := ok
  have wfs := allWellFormed_mem fields (wellFormed_container wf)
  simp only [plain] at pl
  simp only [narrow, Bool.and_eq_true] at thin
  exact fun f hf => ⟨(plainNarrow_mem fields pl thin.2 f hf).1, wfs f hf, (plainNarrow_mem fields pl thin.2 f hf).2⟩

/--
The scratch bound of one record of a container, below the cap, is the root, the field nodes, then the larger of what
a field needs and what the tree needs.
-/
theorem containerNeed {names : List String} {fields : List Desc} (below : rootsNeed (.container names fields) 1 < scratchCap) :
    rootsNeed (.container names fields) 1 =
      32 + 32 * fields.length + max (fieldsRootsNeed fields 1 0) (4640 + 32 * fields.length) := by
  have top := fieldsRootsNeed_le fields 1 0 (Nat.zero_le _)
  simp only [rootsNeed, ↓reduceIte] at below ⊢
  generalize fieldsRootsNeed fields 1 0 = most at *
  simp only [treeNeed, sadd, smul, sat, RootProgressive.spineBytes, zeroHeights] at below ⊢
  generalize scratchCap = C at *
  omega

/-- What memory keeps: every byte outside an output region and the padding area is as at the start. -/
def Keeps (mem mem₀ : Memory) (out span pad : Nat) : Prop :=
  ∀ a, ¬ (out ≤ a ∧ a < out + span) → ¬ (pad ≤ a ∧ a < pad + 1536) → mem a = mem₀ a

/-! ### The loop over fields -/

/-- The variables the loop over fields keeps: the arguments, the count, the field node, the nodes, the index, the offset. -/
structure LeafEnv (env : Env) (p src stride out ctx n q o j : Nat) : Prop where
  /-- The arguments, for one record. -/
  args : RootsEnv env p src stride 1 out ctx
  /-- The field count. -/
  len : env RootsOf.len.idx = UInt64.ofNat n
  /-- The current field's plan node. -/
  e : env RootsOf.e.idx = UInt64.ofNat q
  /-- The field nodes, right after the root. -/
  r : env RootsOf.r.idx = UInt64.ofNat (out + 32)
  /-- The current field's index. -/
  i : env RootsOf.i.idx = UInt64.ofNat j
  /-- The current field's offset in the record. -/
  off : env RootsOf.off.idx = UInt64.ofNat o

/-- Writing a scratch variable keeps what the loop over fields keeps. -/
theorem LeafEnv.write {env : Env} {p src stride out ctx n q o j : Nat} (h : LeafEnv env p src stride out ctx n q o j)
    {x : Nat} (v : UInt64) (hx : x = 9 ∨ x = 10 ∨ 16 ≤ x) :
    LeafEnv (Asm.assign env x v) p src stride out ctx n q o j :=
  ⟨h.args.write v (by omega), by rw [assign_ne (show 7 ≠ x by omega), h.len],
    by rw [assign_ne (show 8 ≠ x by omega), h.e], by rw [assign_ne (show 11 ≠ x by omega), h.r],
    by rw [assign_ne (show 14 ≠ x by omega), h.i], by rw [assign_ne (show 15 ≠ x by omega), h.off]⟩

/-- A field's node as the Lean computation writes it: its bytes when it fits a node, its root otherwise. -/
def leafNext (f : Desc) (b : ByteArray) (start offset : Nat) (leaves : ByteArray) (node : Nat) : ByteArray :=
  if packsIntoNode f then b.copySlice (start + offset) leaves (32 * node) (fixedWidth f)
  else (rootsOf f b (start + offset) (fixedWidth f) 1).copySlice 0 leaves (32 * node) 32

/-- The leaves of a field and the fields after it: its node, then theirs. -/
theorem fieldLeaves_cons (f : Desc) (rest : List Desc) (b : ByteArray) (start offset : Nat) (leaves : ByteArray)
    (node : Nat) : fieldLeaves (f :: rest) b start offset leaves node =
      fieldLeaves rest b start (offset + fixedWidth f) (leafNext f b start offset leaves node) (node + 1) := by
  rw [fieldLeaves]; rfl

/-- The statements of one field's turn: its width, its node's address, the packing test, its node, the next field. -/
abbrev leafBody : List Stmt :=
  [callInto RootsOf.w "ssz_plan_fixed_width" [RootsOf.e], RootsOf.slot ::= RootsOf.r + 32 * RootsOf.i] ++
    RootsOf.packsInto ++
    [ifElse RootsOf.pk RootsOf.copyLeaf [callInto RootsOf.sink "ssz_roots_of"
        [RootsOf.e, RootsOf.src + RootsOf.off, RootsOf.w, 1, RootsOf.slot, RootsOf.ctx]],
      RootsOf.off ::= RootsOf.off + RootsOf.w, callInto RootsOf.e "ssz_plan_next" [RootsOf.e],
      RootsOf.i ::= RootsOf.i + 1]

/-- A byte of a buffer's first bytes is the buffer's byte. -/
theorem extract_get! (bytes : ByteArray) {n x : Nat} (hx : x < n) (hn : n ≤ bytes.size) :
    (bytes.extract 0 n).get! x = bytes.get! x := by
  rw [Kernel.get!_eq _ _ (by rw [ByteArray.size_extract]; omega), Kernel.get!_eq _ _ (by omega),
    ByteArray.getElem_extract]
  simp only [Nat.zero_add]

/-- Memory holds a buffer's first bytes when it holds each of them. -/
theorem holds_prefix {mem : Memory} {a n : Nat} {bytes : ByteArray} (hn : n ≤ bytes.size)
    (h : ∀ x < n, mem (a + x) = bytes.get! x) : Holds mem a (bytes.extract 0 n) := by
  intro x hx
  rw [ByteArray.size_extract] at hx
  rw [extract_get! bytes (by omega) hn]
  exact h x (by omega)

/-- Memory holding a buffer's first bytes holds each of them. -/
theorem Holds.prefix_get {mem : Memory} {a n : Nat} {bytes : ByteArray} (h : Holds mem a (bytes.extract 0 n))
    (hn : n ≤ bytes.size) {x : Nat} (hx : x < n) : mem (a + x) = bytes.get! x := by
  rw [h x (by rw [ByteArray.size_extract]; omega), extract_get! bytes hx hn]

/--
One field's turn writes its node as the Lean computation does, and moves to the next field.

The nodes written so far stay, the node after them is the field's, and memory keeps every byte outside the output
region and the padding area.
What a call on the field's type does is a hypothesis, and so is the size of the field's root.
-/
theorem leafBody_runs {m : Module} {w : World} (fns : RootsFns m) {sp : Nat} {mem₀ mem : Memory}
    {names : List String} {fields : List Desc} {p base start stride out ctx table zeros pad : Nat} {mask : UInt64}
    {b : ByteArray} (pre : RootsPre w mem₀ (.container names fields) p base start stride 1 out ctx table zeros pad mask b)
    (ok : Rootable (.container names fields)) (ih : ∀ f ∈ fields, RootsOfOk m w f)
    (room : ∀ f ∈ fields, w.stackLo + rootsStack f ≤ sp)
    (planRoom : w.stackLo + 112 * Desc.deepestNesting fields ≤ sp) {f : Desc} (fm : f ∈ fields) {q o j : Nat} {leaves : ByteArray} {env : Env}
    (sized : packsIntoNode f = false → (rootsOf f b (start + o) (fixedWidth f) 1).size = 32)
    (ev : LeafEnv env p (base + start) stride out ctx fields.length q o j) (jl : j < fields.length)
    (planF : WordsAt w mem₀ q (Plan.words f))
    (planIn : p ≤ q ∧ q + 8 * (Plan.words f).length ≤ p + 8 * (Plan.words (.container names fields)).length)
    (offIn : o + fixedWidth f ≤ fieldsWidth fields) (size : leaves.size = 32 * fields.length + 32)
    (zero : ∀ x, 32 * j ≤ x → x < leaves.size → leaves.get! x = 0)
    (held : Holds mem (out + 32) (leaves.extract 0 (32 * j)))
    (keeps : Keeps mem mem₀ out (rootsNeed (.container names fields) 1) pad) :
    ∃ env' mem', Runs m w sp env mem (.block leafBody) env' mem' ∧
      LeafEnv env' p (base + start) stride out ctx fields.length (q + 8 * (Plan.words f).length) (o + fixedWidth f)
        (j + 1) ∧
      (leafNext f b start o leaves j).size = leaves.size ∧
      (∀ x, 32 * (j + 1) ≤ x → x < leaves.size → (leafNext f b start o leaves j).get! x = 0) ∧
      Holds mem' (out + 32) ((leafNext f b start o leaves j).extract 0 (32 * (j + 1))) ∧
      Keeps mem' mem₀ out (rootsNeed (.container names fields) 1) pad := by
  obtain ⟨pl, wf, thin⟩ := rootable_fields ok f fm
  have wide := width_narrow f pl thin
  have capv := cap_eq
  -- The bound's parts, and where the field's node and its scratch lie inside it.
  have hNeed := containerNeed (names := names) pre.below
  have below := pre.below
  have fNeed := fieldsRootsNeed_mem fields 1 0 f fm
  -- The field's plan walks need no more stack than the deepest field's.
  have nest := Ssz.Native.Driver.nesting_le_deepest fields f fm
  have walk : w.stackLo + 112 * f.nesting ≤ sp := Nat.le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ nest) _) planRoom
  have inside := pre.inside 0 pre.pos
  simp only [Nat.mul_zero, Nat.add_zero, fixedWidth] at inside
  have bEnd := access_end pre.bAcc
  have oEnd := access_end pre.acc
  have oB := pre.oB
  have oPad := pre.oPad
  have oPlan := pre.oPlan
  have planPad := pre.planPad
  have bPad := pre.bPad
  simp only [Apart] at oB oPad oPlan planPad bPad
  -- The field's plan node is still in memory.
  have planAt : ∀ mm : Memory, Keeps mm mem₀ out (rootsNeed (.container names fields) 1) pad → WordsAt w mm q (Plan.words f) := fun mm k =>
    planAt_congr planF fun a lo hi => k a (by omega) (by omega)
  -- Its width.
  have width := planWidth_calls fns.plan f q sp mem (planAt mem keeps) wf thin walk
  have r1 := Runs.call (m := m) (sp := sp) (env := env) (mem := mem) (dst := RootsOf.w.idx) (args := [RootsOf.e])
    (by simp only [List.mapM_cons, List.mapM_nil, eval_var ev.e]; rfl) width
  have ev1 := ev.write (x := 9) (fixedWidth f).toUInt64 (by omega)
  have w1 : Asm.assign env 9 (fixedWidth f).toUInt64 9 = UInt64.ofNat (fixedWidth f) := assign_eq
  -- Its node's address.
  have r2 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem) (x := RootsOf.slot.idx)
    (eval_add (eval_var ev1.r) (eval_mul (eval_lit 32) (eval_var ev1.i)))
  have ev2 := ev1.write (x := 16) (UInt64.ofNat (out + 32 + 32 * j)) (by omega)
  have s2 : Asm.assign (Asm.assign env 9 (fixedWidth f).toUInt64) 16 (UInt64.ofNat (out + 32 + 32 * j)) 16 =
      UInt64.ofNat (out + 32 + 32 * j) := assign_eq
  -- The packing test.
  obtain ⟨t, r3⟩ := packsInto_runs (m := m) (sp := sp) (mem := mem) (planAt mem keeps) ev2.e thin
  let E3 := Asm.assign (Asm.assign (Asm.assign (Asm.assign env 9 (fixedWidth f).toUInt64) 16
    (UInt64.ofNat (out + 32 + 32 * j))) 18 t) 19 (bitOf (packsIntoNode f))
  have ev3 : LeafEnv E3 p (base + start) stride out ctx fields.length q o j :=
    (ev2.write (x := 18) t (by omega)).write (x := 19) _ (by omega)
  have e3w : E3 9 = UInt64.ofNat (fixedWidth f) := by
    simp only [E3]; rw [assign_ne (by decide), assign_ne (by decide), assign_ne (by decide)]; exact w1
  have e3s : E3 16 = UInt64.ofNat (out + 32 + 32 * j) := by
    simp only [E3]; rw [assign_ne (by decide), assign_ne (by decide)]; exact s2
  -- The field's node, written either way.
  have node : ∃ E4 mem₄, Runs m w sp E3 mem (ifElse RootsOf.pk RootsOf.copyLeaf [callInto RootsOf.sink "ssz_roots_of"
        [RootsOf.e, RootsOf.src + RootsOf.off, RootsOf.w, 1, RootsOf.slot, RootsOf.ctx]]) E4 mem₄ ∧
      LeafEnv E4 p (base + start) stride out ctx fields.length q o j ∧ E4 9 = UInt64.ofNat (fixedWidth f) ∧
      (leafNext f b start o leaves j).size = leaves.size ∧
      (∀ x, 32 * (j + 1) ≤ x → x < leaves.size → (leafNext f b start o leaves j).get! x = 0) ∧
      Holds mem₄ (out + 32) ((leafNext f b start o leaves j).extract 0 (32 * (j + 1))) ∧
      Keeps mem₄ mem₀ out (rootsNeed (.container names fields) 1) pad := by
    have e3e : E3 19 = bitOf (packsIntoNode f) := assign_eq
    by_cases packs : packsIntoNode f = true
    · -- A field that fits a node: a node of zeros, then the field's bytes over its start.
      have fw := packs_le_node f packs wf
      have dAcc : w.access (out + 32 + 32 * j) 32 = true := access_sub pre.acc (by omega) (by omega)
      have sAcc : w.access (base + start + o) (fixedWidth f) = true := access_sub pre.bAcc (by omega) (by omega)
      have run := copyLeaf_runs (m := m) (w := w) (sp := sp) (env := E3) (mem := mem) e3s ev3.args.src ev3.off e3w fw
        sAcc dAcc (by omega)
      have hl : leafNext f b start o leaves j = b.copySlice (start + o) leaves (32 * j) (fixedWidth f) := by
        unfold leafNext; rw [ite_eq_left packs]
      rw [hl]
      refine ⟨_, _, Runs.ite_true 1 (eval_var (by rw [e3e, packs]; rfl)) (by decide) run,
        ev3.write _ (by omega), by rw [assign_ne (by decide)]; exact e3w,
        copySlice_size _ _ _ _ _ (by omega) (by omega), fun x lo hx => ?_, ?_, fun a ha hp => ?_⟩
      · rw [copySlice_get _ _ _ _ _ _ (by omega) (by omega) hx, ite_eq_right (by omega)]
        exact zero x (by omega) hx
      · -- The copy into the zeroed node is the Lean copy into the zero buffer's first nodes.
        rw [← copySlice_extract b leaves (start + o) (32 * j) (fixedWidth f) (32 * (j + 1)) (by omega) (by omega)
          (by omega)]
        have hz : Holds (zeroed mem (out + 32 + 32 * j)) (out + 32) (leaves.extract 0 (32 * (j + 1))) :=
          holds_prefix (by omega) fun x hx => by
            by_cases lo : x < 32 * j
            · simp only [zeroed, Asm.store]; rw [ite_eq_right (by omega)]; exact Holds.prefix_get held (by omega) lo
            · simp only [zeroed, Asm.store]; rw [ite_eq_left (by omega), zero x (by omega) (by omega)]
        have hb : Holds (zeroed mem (out + 32 + 32 * j)) base b := fun i hi => by
          simp only [zeroed, Asm.store]
          rw [ite_eq_right (by omega), keeps _ (by omega) (by omega)]
          exact pre.holds i hi
        have := holds_copied hb hz (so := start + o) (d := 32 * j) (len := fixedWidth f) (by omega)
          (by rw [ByteArray.size_extract]; omega)
        rwa [← Nat.add_assoc base start o] at this
      · -- The copy writes only inside the field's node.
        simp only [copied, zeroed, Asm.store]
        rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact keeps a ha hp
    · -- Any other field: a call on its type writes its root at its node.
      have sz := sized (by simpa using packs)
      have childPre := pre.child (mem₂ := mem) (e := f) (p₂ := q) (start₂ := start + o) (stride₂ := fixedWidth f)
        (count₂ := 1) (out₂ := out + 32 + 32 * j) keeps planF planIn (Nat.le_refl _) (by omega) (Nat.le_refl 1)
        (fun i hi => by have : i = 0 := by omega
                        subst this; omega)
        (by have sd := pre.spread; have gp := pre.gap; simp only [fixedWidth] at sd gp; omega) (by omega)
        ⟨by omega, by omega⟩
      obtain ⟨mem₄, call, post⟩ := ih f fm sp mem q base (start + o) (fixedWidth f) 1 (out + 32 + 32 * j) ctx table
        zeros pad mask b (room f fm) childPre
      obtain ⟨held₄, -, keep₄⟩ := post
      have hsrc : eval w E3 mem (RootsOf.src + RootsOf.off) = some (UInt64.ofNat (base + (start + o))) := by
        rw [← Nat.add_assoc]; exact eval_add (eval_var ev3.args.src) (eval_var ev3.off)
      have r := Runs.call (m := m) (sp := sp) (env := E3) (mem := mem) (dst := RootsOf.sink.idx)
        (args := [RootsOf.e, RootsOf.src + RootsOf.off, RootsOf.w, 1, RootsOf.slot, RootsOf.ctx])
        (by simp only [List.mapM_cons, List.mapM_nil, eval_var ev3.e, hsrc, eval_var e3w, eval_lit, eval_var e3s,
              eval_var ev3.args.ctx]; rfl) call
      have hl : leafNext f b start o leaves j =
          (rootsOf f b (start + o) (fixedWidth f) 1).copySlice 0 leaves (32 * j) 32 := by
        unfold leafNext; rw [ite_eq_right packs]
      rw [hl]
      refine ⟨_, _, Runs.ite_false (eval_var (by rw [e3e, show packsIntoNode f = false by simpa using packs]; rfl))
        (Runs.block_cons r (Runs.block_nil _ _ _ _ _)),
        ev3.write (x := 10) _ (Or.inr (Or.inl rfl)), by rw [assign_ne (by decide)]; exact e3w,
        copySlice_size _ _ _ _ _ (by omega) (by omega), fun x lo hx => ?_, ?_, fun a ha hp => ?_⟩
      · rw [copySlice_get _ _ _ _ _ _ (by omega) (by omega) hx, ite_eq_right (by omega)]
        exact zero x (by omega) hx
      · -- The nodes before stay, and the field's node holds its root.
        refine holds_prefix (by rw [copySlice_size _ _ _ _ _ (by omega) (by omega)]; omega) fun x hx => ?_
        rw [copySlice_get _ _ _ _ _ _ (by omega) (by omega) (by omega)]
        split
        · rw [show out + 32 + x = out + 32 + 32 * j + (0 + (x - 32 * j)) by omega]
          exact held₄ _ (by omega)
        · rw [keep₄ _ (by omega) (by omega)]
          exact Holds.prefix_get held (by omega) (by omega)
      · rw [keep₄ a (by omega) hp]
        exact keeps a ha hp
  obtain ⟨E4, mem₄, r4, ev4, w4, nSize, nZero, nHeld, nKeeps⟩ := node
  -- The next offset, the next field's plan node, and the next index.
  have r5 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem₄) (x := RootsOf.off.idx)
    (eval_add (eval_var ev4.off) (eval_var w4))
  let E5 := Asm.assign E4 15 (UInt64.ofNat (o + fixedWidth f))
  have e5 : E5 8 = UInt64.ofNat q := by simp only [E5]; rw [assign_ne (by decide)]; exact ev4.e
  have next := next_ok m w fns.plan.codec f wf sp mem₄ q (planAt mem₄ nKeeps) (by rw [walkLevel_eq]; exact walk)
  have r6 := Runs.call (m := m) (sp := sp) (env := E5) (mem := mem₄) (dst := RootsOf.e.idx) (args := [RootsOf.e])
    (by simp only [List.mapM_cons, List.mapM_nil, eval_var e5]; rfl) next
  let E6 := Asm.assign E5 8 (q + 8 * (Plan.words f).length).toUInt64
  have e6 : E6 14 = UInt64.ofNat j := by
    simp only [E6, E5]; rw [assign_ne (by decide), assign_ne (by decide)]; exact ev4.i
  have r7 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem₄) (env := E6) (x := RootsOf.i.idx)
    (eval_add (eval_var e6) (eval_lit 1))
  refine ⟨_, mem₄, Runs.block_append (Runs.block_append (Runs.block_cons r1 (Runs.block_cons r2
    (Runs.block_nil _ _ _ _ _))) r3) (Runs.block_cons r4 (Runs.block_cons r5 (Runs.block_cons r6
      (Runs.block_cons r7 (Runs.block_nil _ _ _ _ _))))), ?_, nSize, nZero, nHeld, nKeeps⟩
  exact ⟨((ev4.args.write _ (by decide)).write _ (by decide)).write _ (by decide),
    by simp only [E6, E5]; rw [assign_ne (by decide), assign_ne (by decide), assign_ne (by decide), ev4.len],
    by simp only [E6, E5]; rw [assign_ne (by decide), assign_eq],
    by simp only [E6, E5]; rw [assign_ne (by decide), assign_ne (by decide), assign_ne (by decide), ev4.r],
    assign_eq,
    by simp only [E6, E5]; rw [assign_ne (by decide), assign_ne (by decide), assign_eq]⟩

/-- The loop over fields: one turn per field. -/
abbrev leafLoop : Stmt := while_ (lt RootsOf.i RootsOf.len) leafBody

/--
The loop over fields writes, from the current field on, every field node as the Lean computation does.

It ends at the last field, with memory holding the record's field nodes.
-/
theorem leafLoop_runs {m : Module} {w : World} (fns : RootsFns m) {sp : Nat} {mem₀ : Memory}
    {names : List String} {fields : List Desc} {p base start stride out ctx table zeros pad : Nat} {mask : UInt64}
    {b : ByteArray} (pre : RootsPre w mem₀ (.container names fields) p base start stride 1 out ctx table zeros pad mask b)
    (ok : Rootable (.container names fields)) (ih : ∀ f ∈ fields, RootsOfOk m w f)
    (room : ∀ f ∈ fields, w.stackLo + rootsStack f ≤ sp)
    (planRoom : w.stackLo + 112 * Desc.deepestNesting fields ≤ sp)
    (sized : ∀ f ∈ fields, ∀ s, packsIntoNode f = false → (rootsOf f b s (fixedWidth f) 1).size = 32) :
    ∀ (fs : List Desc), (∀ f ∈ fs, f ∈ fields) → ∀ (q o j : Nat) (leaves : ByteArray) (env : Env) (mem : Memory),
      LeafEnv env p (base + start) stride out ctx fields.length q o j → j + fs.length = fields.length →
      WordsAt w mem₀ q (Plan.wordsAll fs) →
      p ≤ q ∧ q + 8 * (Plan.wordsAll fs).length ≤ p + 8 * (Plan.words (.container names fields)).length →
      o + fieldsWidth fs ≤ fieldsWidth fields → leaves.size = 32 * fields.length + 32 →
      (∀ x, 32 * j ≤ x → x < leaves.size → leaves.get! x = 0) →
      Holds mem (out + 32) (leaves.extract 0 (32 * j)) →
      Keeps mem mem₀ out (rootsNeed (.container names fields) 1) pad →
      ∃ env' mem', Runs m w sp env mem leafLoop env' mem' ∧
        (∃ q' o', LeafEnv env' p (base + start) stride out ctx fields.length q' o' fields.length) ∧
        (fieldLeaves fs b start o leaves j).size = leaves.size ∧
        Holds mem' (out + 32) ((fieldLeaves fs b start o leaves j).extract 0 (32 * fields.length)) ∧
        Keeps mem' mem₀ out (rootsNeed (.container names fields) 1) pad
  | [], _, q, o, j, leaves, env, mem, ev, count, _, _, _, _, _, held, keeps => by
    -- No field is left: the index is the count, and the loop stops.
    simp only [List.length_nil, Nat.add_zero] at count
    subst count
    have hn := containerNeed (names := names) pre.below
    have hb := pre.below
    have capv := cap_eq
    have c := eval_lt (w := w) (mem := mem) (eval_var ev.i) (eval_var ev.len) (by omega) (by omega)
    rw [ite_eq_right (Nat.lt_irrefl _)] at c
    rw [fieldLeaves]
    exact ⟨env, mem, Runs.loop_exit _ _ _ _ _ _ _ c, ⟨q, o, ev⟩, rfl, held, keeps⟩
  | f :: rest, sub, q, o, j, leaves, env, mem, ev, count, plan, planIn, offIn, size, zero, held, keeps => by
    simp only [List.length_cons] at count
    simp only [Plan.wordsAll] at plan planIn
    simp only [fieldsWidth] at offIn
    obtain ⟨planF, planRest⟩ := wordsAt_split plan
    simp only [List.length_append] at planIn
    have fm := sub f (List.mem_cons_self ..)
    -- This field's turn.
    obtain ⟨env₁, mem₁, body, ev₁, size₁, zero₁, held₁, keeps₁⟩ := leafBody_runs fns pre ok ih room planRoom fm
      (sized f fm (start + o)) ev (by omega) planF ⟨planIn.1, by omega⟩ (by omega) size zero held keeps
    -- The fields after it.
    obtain ⟨env₂, mem₂, loop, ev₂, size₂, held₂, keeps₂⟩ := leafLoop_runs fns pre ok ih room planRoom sized rest
      (fun g hg => sub g (List.mem_cons_of_mem _ hg)) _ _ (j + 1) _ env₁ mem₁ ev₁ (by omega) planRest
      ⟨by omega, by omega⟩ (by omega) (by rw [size₁, size]) (fun x lo hx => zero₁ x lo (by rw [size₁] at hx; exact hx))
      held₁ keeps₁
    have hn := containerNeed (names := names) pre.below
    have hb := pre.below
    have capv := cap_eq
    have c := eval_lt (w := w) (mem := mem) (eval_var ev.i) (eval_var ev.len) (by omega) (by omega)
    rw [ite_eq_left (by omega)] at c
    rw [fieldLeaves_cons]
    exact ⟨env₂, mem₂, Runs.loop_step 1 c (by decide) body loop, ev₂, by rw [size₂, size₁], held₂, keeps₂⟩

/-! ### The record's tree -/

/-- Memory holding a buffer's first bytes reads, at each node's place among them, the buffer's node. -/
theorem nodeAt_of_prefix {mem : Memory} {a n : Nat} {bytes : ByteArray} (h : Holds mem a (bytes.extract 0 n))
    (hn : n ≤ bytes.size) {i : Nat} (inside : 32 * i + 32 ≤ n) : nodeAt mem (a + 32 * i) = nodeOf bytes 0 i := by
  apply Array.ext
  · simp [nodeAt, nodeOf]; omega
  · intro k h1 h2
    have hk : k < 32 := by simpa [nodeAt] using h1
    simp only [nodeAt, Array.getElem_ofFn, nodeOf, Nat.zero_add, ByteArray.data_extract, Array.getElem_extract]
    rw [Nat.add_assoc, Holds.prefix_get h hn (by omega), Kernel.get!_eq _ _ (by omega), ByteArray.getElem_eq_getElem_data]

/-- Memory holds a node-sized buffer whose bytes are the node read there. -/
theorem holds_of_nodeAt {mem : Memory} {a : Nat} {bytes : ByteArray} (size : bytes.size = 32)
    (h : nodeAt mem a = bytes.data) : Holds mem a bytes := by
  intro i hi
  have := nodeAt_get mem a i (by omega)
  rw [← this, Kernel.get!_eq _ _ hi, ByteArray.getElem_eq_getElem_data]
  simp only [h]

/-- The statements that root one record of a container: its field nodes, then their tree. -/
abbrev containerOnePath : List Stmt :=
  [RootsOf.r ::= RootsOf.out + 32, leafLoop, callInto RootsOf.d "ssz_depth_for" [RootsOf.len],
    callInto RootsOf.sink "ssz_merkleize"
      [RootsOf.r, RootsOf.len, RootsOf.d, RootsOf.out, RootsOf.r + 32 * RootsOf.len + 32, RootsOf.ctx]]

/-- The driver takes the one-record path for a container once the node's count and first field are read. -/
theorem containerOne_body : ∃ vec one many other, RootsOf.fn.body = .block [RootsOf.tag ::= ld RootsOf.p,
    ifElse (eq RootsOf.tag 7) vec [ifElse (eq RootsOf.tag 10) [RootsOf.len ::= ld (RootsOf.p + 8),
      RootsOf.e ::= RootsOf.p + 16, RootsOf.off ::= 0, RootsOf.i ::= 0,
      ifElse (eq RootsOf.count 1) one many] other]] ∧ one = containerOnePath :=
  ⟨_, _, _, _, rfl, rfl⟩

/--
One record of a container is rooted as the Lean computation roots it: its field nodes, then the tree over them.

The plan node's field count, first field and a zero index and offset are already read.
What a call on each field's type does is a hypothesis, the step an induction on the type takes.
-/
theorem containerOne_runs {m : Module} {w : World} (hash : HashingOk m w) (fns : RootsFns m) {sp : Nat}
    {mem : Memory} {names : List String} {fields : List Desc} {p base start stride out ctx table zeros pad : Nat}
    {mask : UInt64} {b : ByteArray}
    (pre : RootsPre w mem (.container names fields) p base start stride 1 out ctx table zeros pad mask b)
    (ok : Rootable (.container names fields)) (ih : ∀ f ∈ fields, RootsOfOk m w f)
    (room : ∀ f ∈ fields, w.stackLo + rootsStack f ≤ sp)
    (planRoom : w.stackLo + 112 * Desc.deepestNesting fields ≤ sp) (treeRoom : w.stackLo + treeStack ≤ sp)
    {env : Env} (ev : RootsEnv env p (base + start) stride 1 out ctx)
    (hlen : env RootsOf.len.idx = UInt64.ofNat fields.length) (he : env RootsOf.e.idx = UInt64.ofNat (p + 16))
    (hi : env RootsOf.i.idx = UInt64.ofNat 0) (ho : env RootsOf.off.idx = UInt64.ofNat 0) :
    ∃ env' mem', Runs m w sp env mem (.block containerOnePath) env' mem' ∧
      RootsPost w mem mem' out (rootsNeed (.container names fields) 1) ctx table zeros pad mask
        (rootsOf (.container names fields) b start stride 1) := by
  have hNeed := containerNeed (names := names) pre.below
  have below := pre.below
  have capv := cap_eq
  -- A field's root is one node.
  have sized : ∀ f ∈ fields, ∀ s, packsIntoNode f = false → (rootsOf f b s (fixedWidth f) 1).size = 32 :=
    fun f fm s _ => by
      have := fieldsRootsNeed_mem fields 1 0 f fm
      simpa using rootsOf_size f (rootable_fields ok f fm) pre.usize b s (fixedWidth f) 1 (Nat.le_refl 1) (by omega)
  have oEnd := access_end pre.acc
  have oPad := pre.oPad
  have oCtx := pre.oCtx
  have oTable := pre.oTable
  have oZeros := pre.oZeros
  simp only [Apart] at oPad oCtx oTable oZeros
  -- The nodes' address.
  have r1 := Runs.set' (m := m) (w := w) (sp := sp) (mem := mem) (env := env) (x := RootsOf.r.idx)
    (eval_add (eval_var ev.out) (eval_lit 32))
  have ev1 : LeafEnv (Asm.assign env 11 (UInt64.ofNat (out + 32))) p (base + start) stride out ctx fields.length (p + 16) 0 0 :=
    ⟨ev.write _ (by decide), by rw [assign_ne (by decide), hlen], by rw [assign_ne (by decide), he], assign_eq,
      by rw [assign_ne (by decide), hi], by rw [assign_ne (by decide), ho]⟩
  -- The fields' plan nodes follow the container's two words.
  have plan := pre.plan
  simp only [Plan.words] at plan
  obtain ⟨_, planFields⟩ := wordsAt_split plan
  simp only [List.length_cons, List.length_nil] at planFields
  -- The Lean computation's buffer of nodes starts as zeros.
  -- Kept as plain numbers, since the word size as a term is costly to unfold.
  have small : 32 * fields.length + 32 < 2 ^ 64 := by omega
  have smallB : 32 * fields.length < 2 ^ 64 := by omega
  obtain ⟨zSize, zZero⟩ := zeros_spec (32 * fields.length + 32) (by rw [pre.usize]; exact small)
  have planLen : (Plan.words (Desc.container names fields)).length = 2 + (Plan.wordsAll fields).length := by
    simp only [Plan.words, List.length_append, List.length_cons, List.length_nil]
  obtain ⟨env₂, mem₂, loop, ⟨q', o', ev₂⟩, lSize, held₂, keeps₂⟩ := leafLoop_runs fns pre ok ih room planRoom sized
    fields (fun f h => h) (p + 16) 0 0 (Ssz.Native.zeros (32 * fields.length + 32)) _ mem ev1 (by omega)
    (by simpa using planFields) ⟨by omega, by rw [planLen]; omega⟩ (by simp) (by rw [zSize])
    (fun x _ hx => zZero x (by rw [zSize] at hx; exact hx))
    (fun i hi => absurd hi (by simp)) (fun _ _ _ => rfl)
  -- The tree's depth.
  have dframe : DepthFor.fn.frame = 5 := by decide
  have hstack : treeStack = 160 + 10392 := rfl
  have depth := depthFor_calls (w := w) fns.plan.depth (sp := sp) (by rw [dframe]; omega) (UInt64.ofNat fields.length) mem₂
  rw [ofNat_toNat (by omega)] at depth
  have r3 := Runs.call (m := m) (sp := sp) (env := env₂) (mem := mem₂) (dst := RootsOf.d.idx) (args := [RootsOf.len])
    (by simp only [List.mapM_cons, List.mapM_nil, eval_var ev₂.len]; rfl) depth
  have dle : depthFor fields.length ≤ 64 := by
    have := depthFor_word (UInt64.ofNat fields.length); rwa [ofNat_toNat (by omega)] at this
  have fits := le_two_pow_depthFor fields.length
  -- The context is still filled, and the tree's buffers lie inside the output region.
  have ready₂ := pre.ready.region pre.oCtx pre.oTable pre.oZeros keeps₂
  have pc := ready₂.padCtx
  have pt := ready₂.padTable
  have pz := ready₂.padZeros
  simp only [Apart] at pc pt pz
  have tp : TreePre w mem₂ (out + 32) fields.length (depthFor fields.length) out
      (out + 32 + 32 * fields.length + 32) ctx table zeros pad mask :=
    ⟨ready₂.ctxAccess, ready₂.maskAt, ready₂.tableAt, ready₂.zerosAt, ready₂.padAt, ready₂.tableHeld,
      ready₂.tableAccess, ready₂.zeroRoots, ready₂.zerosAccess, dle, fits, access_sub pre.acc (by omega) (by omega),
      access_sub pre.acc (by omega) (by omega), access_sub pre.acc (by omega) (by omega), ready₂.padAccess,
      by simp only [Apart]; omega, by simp only [Apart]; omega, by simp only [Apart]; omega,
      by simp only [Apart]; omega, by simp only [Apart]; omega, by simp only [Apart]; omega,
      by simp only [Apart]; omega, by simp only [Apart]; omega, by simp only [Apart]; omega,
      by simp only [Apart]; omega, by omega, by simp only [Apart]; omega, by simp only [Apart]; omega⟩
  -- The tree over the field nodes.
  obtain ⟨mem₃, call, root, frame⟩ := treeCalls_native hash.merkleize tp ready₂.kernels treeRoom (by rw [pre.usize]; exact smallB)
  let E3 := Asm.assign env₂ 12 (depthFor fields.length).toUInt64
  have e3 : ∀ y, y ≠ 12 → E3 y = env₂ y := fun _ h => assign_ne h
  have r4 := Runs.call (m := m) (sp := sp) (env := E3) (mem := mem₂) (dst := RootsOf.sink.idx)
    (args := [RootsOf.r, RootsOf.len, RootsOf.d, RootsOf.out, RootsOf.r + 32 * RootsOf.len + 32, RootsOf.ctx])
    (by
      simp only [List.mapM_cons, List.mapM_nil, eval_var ((e3 11 (by decide)).trans ev₂.r),
        eval_var ((e3 7 (by decide)).trans ev₂.len), eval_var (show E3 12 = _ from assign_eq),
        eval_var ((e3 4 (by decide)).trans ev₂.args.out),
        eval_add (eval_add (eval_var ((e3 11 (by decide)).trans ev₂.r))
          (eval_mul (eval_lit 32) (eval_var ((e3 7 (by decide)).trans ev₂.len)))) (eval_lit 32),
        eval_var ((e3 5 (by decide)).trans ev₂.args.ctx)]
      rfl) call
  -- Memory keeps every byte outside the output region and the padding area.
  have k3 : Keeps mem₃ mem out (rootsNeed (.container names fields) 1) pad := fun a ha hp => by
    rw [frame a (by omega) hp (by omega)]; exact keeps₂ a ha hp
  refine ⟨_, mem₃, Runs.block_cons r1 (Runs.block_cons loop (Runs.block_cons r3 (Runs.block_cons r4
    (Runs.block_nil _ _ _ _ _)))), ?_, pre.ready.region pre.oCtx pre.oTable pre.oZeros k3, k3⟩
  -- The root is the Lean tree over the Lean field nodes, which memory held.
  have code : rootsOf (.container names fields) b start stride 1 =
      merkleizeDepth (fieldLeaves fields b start 0 (Ssz.Native.zeros (32 * fields.length + 32)) 0) fields.length
        (depthFor fields.length) := by
    rw [rootsOf]; simp
  rw [code]
  rw [zSize] at lSize
  obtain ⟨ms, md⟩ := merkleizeDepth_spec (fieldLeaves fields b start 0 (Ssz.Native.zeros (32 * fields.length + 32)) 0)
    fields.length (depthFor fields.length) fits (by rw [lSize]; exact Nat.le_add_right _ _) (by rw [lSize, pre.usize]; exact small)
  have bsize : (bytesAt mem₂ (out + 32) (32 * fields.length)).size = 32 * fields.length := by
    simp [bytesAt, ByteArray.size]
  obtain ⟨_, md'⟩ := merkleizeDepth_spec (bytesAt mem₂ (out + 32) (32 * fields.length)) fields.length
    (depthFor fields.length) fits (Nat.le_of_eq bsize.symm) (by rw [bsize, pre.usize]; exact smallB)
  have nodes : nodesFrom (bytesAt mem₂ (out + 32) (32 * fields.length)) 0 fields.length =
      nodesFrom (fieldLeaves fields b start 0 (Ssz.Native.zeros (32 * fields.length + 32)) 0) 0 fields.length := by
    apply Array.ext
    · simp
    · intro i h1 _
      simp only [nodesFrom_size] at h1
      simp only [nodesFrom, Array.getElem_ofFn]
      rw [nodeOf_bytesAt _ _ _ _ h1, nodeAt_of_prefix held₂ (by rw [lSize]; exact Nat.le_add_right _ _)
        (by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left 32 h1)]
  refine holds_of_nodeAt ms ?_
  rw [root, md', nodes, md]

end EthLib.Consensus.Ssz.Native.Driver
