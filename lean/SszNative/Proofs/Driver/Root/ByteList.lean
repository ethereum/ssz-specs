import Ssz.Proofs.Codec.DecodeFits
import SszNative.Proofs.Driver.Root.Range

/-!
The byte list driver writes the Lean root of a byte list.

It gathers the bytes into zero-padded nodes in the scratch, roots them at the limit's depth, and mixes in the length.
The gather and the mix-in serve the other list drivers too, so they are stated on their own.
-/

namespace Ssz.Native.Driver

open Ssz Ssz.Native.Ir Ssz.Native.Ir.Expr Ssz.Native.Ir.Stmt Ssz.Native.Asm

/-! ### Bytes packed into nodes -/

/-- Memory after gathering a range into one slot of whole nodes holds the range packed into nodes. -/
theorem holds_packGather {mem : Memory} {base : Nat} {b : ByteArray} (holds : Holds mem base b) (buf : Nat)
    {start stop : Nat} (ordered : start ≤ stop) (inside : stop ≤ b.size) (small : stop - start + 64 < USize.size) :
    Holds (gathered mem buf (base + start) 1 (stop - start) 0 (32 * nodesFor (stop - start) + 32 - (stop - start)))
      buf (packRange b start stop) := by
  have data := RootProof.packRange_data b start stop ordered inside small
  have sizeEq : (packRange b start stop).size = 32 * nodesFor (stop - start) + 32 := by
    rw [← ByteArray.size_data, data]; simp [nodesFor]; omega
  intro i hi
  rw [sizeEq] at hi
  have slot : stop - start + (32 * nodesFor (stop - start) + 32 - (stop - start)) =
      32 * nodesFor (stop - start) + 32 := by simp only [nodesFor]; omega
  have byte := Kernel.recordByte_at mem buf (base + start) (stop - start) 0
    (32 * nodesFor (stop - start) + 32 - (stop - start)) 0 i (by omega)
  simp only [Nat.mul_zero, Nat.add_zero] at byte
  simp only [gathered]
  rw [if_pos ⟨by omega, by rw [slot]; omega⟩, byte, Kernel.get!_eq _ _ (by rw [sizeEq]; exact hi),
    ByteArray.getElem_eq_getElem_data]
  simp only [data]
  split
  · rename_i lt
    rw [Array.getElem_append_left (by simp; omega)]
    simp only [Array.getElem_extract]
    rw [Nat.add_assoc, holds _ (by omega), Kernel.get!_eq _ _ (by omega), ByteArray.getElem_eq_getElem_data]
  · rw [Array.getElem_append_right (by simp; omega)]
    simp

/--
The call gathering a range of the encoding into zero-padded nodes at a buffer.

The buffer holds the range's nodes and one spare node, and misses the encoding.
Memory changes only in the buffer.
-/
theorem packGather_runs {m : Module} {w : World} (gmod : GatherModule m) {sp : Nat} (room : w.stackLo + 8 ≤ sp)
    {env : Env} {mem : Memory} {args : List Expr} {dst : Nat} {base buf start stop : Nat} {b : ByteArray}
    (holds : Holds mem base b) (bAcc : w.access base b.size = true) (ordered : start ≤ stop) (inside : stop ≤ b.size)
    (small : stop - start + 64 < USize.size) (usize : USize.size = 2 ^ 64)
    (bufAcc : w.access buf (32 * nodesFor (stop - start) + 32) = true)
    (apart : Apart (buf, 32 * nodesFor (stop - start) + 32) (base, b.size))
    (hv : args.mapM (eval w env mem) = some [UInt64.ofNat buf, UInt64.ofNat (base + start), 1,
      UInt64.ofNat (stop - start), 0, UInt64.ofNat (32 * nodesFor (stop - start) + 32 - (stop - start))]) :
    ∃ mm, Runs m w sp env mem (.call "ssz_gather" args dst) (Asm.assign env dst 0) mm ∧
      Holds mm buf (packRange b start stop) ∧
      ∀ a, ¬ (buf ≤ a ∧ a < buf + (32 * nodesFor (stop - start) + 32)) → mm a = mem a := by
  have ab := access_bound bAcc
  have abuf := access_bound bufAcc
  have ap := apart
  simp only [Apart] at ap
  have slot : stop - start + (32 * nodesFor (stop - start) + 32 - (stop - start)) =
      32 * nodesFor (stop - start) + 32 := by simp only [nodesFor]; omega
  have pre : GatherPre w buf (base + start) 1 (stop - start) 0 (32 * nodesFor (stop - start) + 32 - (stop - start)) :=
    ⟨by rw [slot, Nat.mul_one]; exact bufAcc,
      fun i hi => by
        obtain rfl : i = 0 := by omega
        exact access_sub bAcc (by omega) (by omega),
      by simp only [addressBound]; omega,
      fun i hi => by
        obtain rfl : i = 0 := by omega
        simp only [Apart]; rw [slot]; omega⟩
  have call := gather_call (m := m) (w := w) (sp := sp) (mem := mem) (out := UInt64.ofNat buf)
    (src := UInt64.ofNat (base + start)) (count := 1) (width := UInt64.ofNat (stop - start)) (skip := 0)
    (pad := UInt64.ofNat (32 * nodesFor (stop - start) + 32 - (stop - start))) gmod.general
    (Kernel.runs_gather w.cpu) (by simp)
    (by rw [ofNat_toNat (by omega), ofNat_toNat (by omega), ofNat_toNat (by omega), ofNat_toNat (by omega)]; exact pre)
    room
  rw [ofNat_toNat (by omega), ofNat_toNat (by omega), ofNat_toNat (by omega), ofNat_toNat (by omega)] at call
  refine ⟨_, Runs.call hv call, holds_packGather holds buf ordered inside small, fun a o => ?_⟩
  simp only [gathered]
  rw [if_neg (by simp only [UInt64.toNat_one, Nat.mul_one]; rw [slot]; exact o)]

/-! ### The scratch a byte list takes -/

/-- The scratch bound of a list's nodes and tree, when below the cap, has no saturated step. -/
theorem listNeed_eq {n : Nat} (below : sadd (sadd 96 (smul 32 n)) (treeNeed n) < scratchCap) :
    sadd (sadd 96 (smul 32 n)) (treeNeed n) = 96 + 32 * n + (2560 + 2048 + 32 * n) := by
  simp only [treeNeed, RootProgressive.spineBytes, zeroHeights] at below ⊢
  simp only [sadd, smul, sat] at below ⊢
  have := cap_eq
  omega

/-! ### The driver -/

set_option maxHeartbeats 1000000 in
/-- The byte list driver's body writes the Lean root of a byte list's range. -/
theorem rootBytes_body {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RangeFns m)
    {limit : Nat} {sp : Nat} {mem : Memory} {p base start stop out scratch ctx table zeros pad : Nat} {mask : UInt64}
    {b : ByteArray} (room : w.stackLo + 12288 ≤ sp)
    (pre : RangePre w mem (.byteList limit) p base start stop out scratch ctx table zeros pad mask b)
    {env : Env} (ev : RangeEnv env p (base + start) (stop - start) out scratch ctx) :
    ∃ env' mem', Runs m w sp env mem RootBytes.fn.body env' mem' ∧
      RangePost w mem mem' out scratch (varNeed (.byteList limit) (stop - start)) ctx table zeros pad mask
        (rootOf (.byteList limit) b start stop) := by
  have usize := pre.usize
  have small := pre.small
  unfold RootProof.Small at small
  rw [usize] at small
  have ordered := pre.ordered
  have inside := pre.inside
  have spread := pre.spread
  have bound : addressBound = 2 ^ 63 := rfl
  have zh : zeroHeights = 64 := rfl
  -- The range fits the limit.
  obtain ⟨v, read⟩ := pre.accepted
  have fitsLimit : stop - start ≤ limit := by
    have := deserialize_byteList_size read
    rwa [slice_size b start stop inside] at this
  -- The scratch: the root and the length's node, then the nodes and a spare, then the tree's levels.
  generalize hsize : stop - start = size at ev fitsLimit
  generalize hn : nodesFor size = n
  have hn' : n = (size + 31) / 32 := by rw [← hn]; rfl
  have need : varNeed (.byteList limit) size = 96 + 32 * n + (2560 + 2048 + 32 * n) := by
    have := pre.below
    rw [hsize] at this
    simp only [varNeed] at this ⊢
    rw [← hn]
    exact listNeed_eq this
  have sAcc := pre.sAcc
  have sSlack := pre.sSlack
  have sB := pre.sB
  have sPad := pre.sPad
  have sCtx := pre.sCtx
  have sTable := pre.sTable
  have sZeros := pre.sZeros
  have sOut := pre.sOut
  have sPlan := pre.sPlan
  have oPad := pre.oPad
  have oCtx := pre.oCtx
  have oTable := pre.oTable
  have oZeros := pre.oZeros
  have bPad := pre.bPad
  have rPad := pre.ready.padCtx
  have rTable := pre.ready.padTable
  have rZeros := pre.ready.padZeros
  rw [hsize, need] at sAcc sSlack sB sPad sCtx sTable sZeros sOut sPlan
  have ab := access_bound pre.bAcc
  have as := access_bound sAcc
  have limitSmall : limit < 2 ^ 64 := pre.fits limit (by simp [Plan.words])
  -- The node count.
  have e1 : eval w env mem (ceilDiv RootBytes.size 32) = some (UInt64.ofNat n) := by
    have := eval_ceilDiv (w := w) (env := env) (mem := mem) (a := RootBytes.size) (eval_var ev.size) 32 (by omega)
    rw [this, ofNat_toNat (by omega), hn']
    rfl
  have s1 := Runs.set' (m := m) (w := w) (sp := sp) (x := 6) e1
  have ev1 := ev.write (x := 6) (UInt64.ofNat n) (by decide)
  have n1 : Asm.assign env 6 (UInt64.ofNat n) 6 = UInt64.ofNat n := assign_eq
  generalize Asm.assign env 6 (UInt64.ofNat n) = E1 at s1 ev1 n1
  have s2 := Runs.set' (m := m) (w := w) (sp := sp) (env := E1) (mem := mem) (x := 7)
    (eval_add (eval_var ev1.scratch) (eval_lit 64))
  have ev2 := ev1.write (x := 7) (UInt64.ofNat (scratch + 64)) (by decide)
  have n2 : Asm.assign E1 7 (UInt64.ofNat (scratch + 64)) 6 = UInt64.ofNat n := by
    rw [assign_ne (by decide)]; exact n1
  have b2 : Asm.assign E1 7 (UInt64.ofNat (scratch + 64)) 7 = UInt64.ofNat (scratch + 64) := assign_eq
  generalize Asm.assign E1 7 (UInt64.ofNat (scratch + 64)) = E2 at s2 ev2 n2 b2
  -- The gather into the nodes.
  have hv : ([RootBytes.buf, RootBytes.src, 1, RootBytes.size, 0, 32 * RootBytes.nodes + 32 - RootBytes.size] :
      List Expr).mapM (eval w E2 mem) = some [UInt64.ofNat (scratch + 64), UInt64.ofNat (base + start), 1,
        UInt64.ofNat (stop - start), 0, UInt64.ofNat (32 * nodesFor (stop - start) + 32 - (stop - start))] := by
    rw [hsize, hn]
    simp only [List.mapM_cons, List.mapM_nil, eval_var b2, eval_var ev2.src, eval_var ev2.size,
      eval_sub (eval_add (eval_mul (eval_lit 32) (eval_var n2)) (eval_lit 32)) (eval_var ev2.size)
        (show size ≤ 32 * n + 32 by omega)]
    rfl
  obtain ⟨mem1, g1, held1, keep1⟩ := packGather_runs (m := m) (w := w) gmod (sp := sp) (by omega) (env := E2)
    (mem := mem) (dst := 9) (buf := scratch + 64) pre.holds pre.bAcc ordered inside
    (by rw [usize]; omega) usize (by rw [hsize, hn]; exact access_sub sAcc (by omega) (by omega))
    (by rw [hsize, hn]; exact apart_sub sB (by omega) (by omega)) hv
  rw [hsize, hn] at keep1
  have ev3 := ev2.write (x := 9) 0 (by decide)
  have n3 : Asm.assign E2 9 0 6 = UInt64.ofNat n := by rw [assign_ne (by decide)]; exact n2
  have b3 : Asm.assign E2 9 0 7 = UInt64.ofNat (scratch + 64) := by rw [assign_ne (by decide)]; exact b2
  generalize Asm.assign E2 9 0 = E3 at g1 ev3 n3 b3
  -- The depth of the limit's tree.
  have planHead : WordsAt w mem1 p [3, limit] := by
    refine planAt_congr pre.plan fun a lo hi => keep1 a ?_
    have := sPlan
    simp only [Apart, Plan.words, List.length_cons, List.length_nil] at this hi
    omega
  have lw : eval w E3 mem1 (ld (RootBytes.p + 8)) = some (UInt64.ofNat limit) :=
    eval_word planHead 1 (by simp) (e := RootBytes.p + 8) (eval_add (eval_var ev3.p) (eval_lit 8))
  have dframe : DepthFor.fn.frame = 5 := by decide
  have dcall := depthFor_calls (m := m) (w := w) fns.roots.plan.depth (sp := sp) (by rw [dframe]; omega)
    (UInt64.ofNat (nodesFor limit)) mem1
  rw [ofNat_toNat (by simp only [nodesFor]; omega)] at dcall
  have r4 := Runs.call (m := m) (sp := sp) (env := E3) (mem := mem1) (dst := 8)
    (args := [ceilDiv (ld (RootBytes.p + 8)) 32])
    (by
      simp only [List.mapM_cons, List.mapM_nil]
      rw [eval_ceilDiv lw 32 (by omega), ofNat_toNat limitSmall]
      rfl) dcall
  generalize hd : depthFor (nodesFor limit) = depth at r4
  have ev4 := ev3.write (x := 8) depth.toUInt64 (by decide)
  have n4 : Asm.assign E3 8 depth.toUInt64 6 = UInt64.ofNat n := by rw [assign_ne (by decide)]; exact n3
  have b4 : Asm.assign E3 8 depth.toUInt64 7 = UInt64.ofNat (scratch + 64) := by
    rw [assign_ne (by decide)]; exact b3
  have d4 : Asm.assign E3 8 depth.toUInt64 8 = UInt64.ofNat depth := assign_eq
  generalize Asm.assign E3 8 depth.toUInt64 = E4 at r4 ev4 n4 b4 d4
  have deep : depth ≤ 64 := by rw [← hd]; exact depthFor_le_of_le_two_pow (by simp only [nodesFor]; omega)
  have fitsTree : n ≤ 2 ^ depth := by
    rw [← hd, ← hn]; exact Nat.le_trans (Nat.div_le_div_right (by omega)) (le_two_pow_depthFor _)
  -- The tree over the nodes, into the scratch's first node.
  have ready1 := pre.ready.within (o := scratch + 64) (n := 32 * n + 32) (apart_sub sCtx (by omega) (by omega))
    (apart_sub sTable (by omega) (by omega)) (apart_sub sZeros (by omega) (by omega)) fun a o _ => keep1 a o
  have tpre : TreePre w mem1 (scratch + 64) n depth scratch (scratch + 64 + 32 * n + 32) ctx table zeros pad
      mask :=
    { ctxAccess := ready1.ctxAccess, maskAt := ready1.maskAt, tableAt := ready1.tableAt, zerosAt := ready1.zerosAt,
      padAt := ready1.padAt, tableBytes := ready1.tableHeld, tableAccess := ready1.tableAccess,
      zeroRoots := ready1.zeroRoots, zerosAccess := ready1.zerosAccess, deep := by rw [zh]; omega,
      fits := fitsTree, nodesAccess := access_sub sAcc (by omega) (by omega),
      outAccess := access_sub sAcc (by omega) (by omega), scratchAccess := access_sub sAcc (by omega) (by omega),
      padAccess := ready1.padAccess, scratchNodes := by simp only [Apart]; omega,
      scratchOut := by simp only [Apart]; omega, scratchCtx := apart_sub sCtx (by omega) (by omega),
      scratchTable := apart_sub sTable (by omega) (by omega), scratchZeros := apart_sub sZeros (by omega) (by omega),
      scratchPad := apart_sub sPad (by omega) (by omega),
      padNodes := apart_comm (apart_sub sPad (by omega) (by omega)),
      padCtx := ready1.padCtx, padTable := ready1.padTable, padZeros := ready1.padZeros,
      nodesReach := by omega, outNodes := by simp only [Apart]; omega, outZeros := apart_sub sZeros (by omega) (by omega) }
  obtain ⟨mem2, call2, root2, keep2⟩ := treeCalls_native hash.merkleize (sp := sp) tpre ready1.kernels (by
    simp only [treeStack, hashStack]; omega) (by rw [usize]; omega)
  have r5 := Runs.call (m := m) (sp := sp) (env := E4) (mem := mem1) (dst := 9)
    (args := [RootBytes.buf, RootBytes.nodes, RootBytes.d, RootBytes.scratch,
      RootBytes.buf + 32 * RootBytes.nodes + 32, RootBytes.ctx])
    (by
      simp only [List.mapM_cons, List.mapM_nil, eval_var b4, eval_var n4, eval_var d4, eval_var ev4.scratch,
        eval_add (eval_add (eval_var b4) (eval_mul (eval_lit 32) (eval_var n4))) (eval_lit 32), eval_var ev4.ctx]
      rfl) call2
  have ev5 := ev4.write (x := 9) 0 (by decide)
  generalize Asm.assign E4 9 0 = E5 at r5 ev5
  -- The tree's root is the Lean tree over the packed bytes.
  have packedSize := (RootProof.packRange_nodes b start stop ordered inside (by rw [usize]; omega)).2
  rw [hsize, hn] at packedSize
  have rootData : nodeAt mem2 scratch =
      (merkleizeCapacity (packRange b start stop) n (nodesFor limit)).data := by
    rw [root2, merkleizeDepth_of_holds held1 (by rw [packedSize]; omega) fitsTree
      (by rw [packedSize, usize]; omega), merkleizeCapacity, hd]
  have keep12 : ∀ a, ¬ (scratch ≤ a ∧ a < scratch + (96 + 32 * n + (2560 + 2048 + 32 * n))) →
      ¬ (pad ≤ a ∧ a < pad + 1536) → mem2 a = mem a := fun a o pd => by
    rw [keep2 a (fun h => o ⟨by omega, by omega⟩) pd (fun h => o ⟨by omega, by omega⟩),
      keep1 a (fun h => o ⟨by omega, by omega⟩)]
  have ready2 := pre.ready.within (o := scratch) (n := 96 + 32 * n + (2560 + 2048 + 32 * n)) sCtx sTable sZeros
    keep12
  -- The length mixed in.
  obtain ⟨E6, mem3, run3, root3, ready3, keep3⟩ := mixin_ends hash (sp := sp) (by simp only [hashStack]; omega)
    ready2 ev5.scratch ev5.out ev5.ctx (cnt := RootBytes.size) (n := size) (fun _ => eval_var ev5.size) (by omega)
    (access_sub sAcc (by omega) (by omega)) (by omega) pre.oAcc (apart_sub sOut (by omega) (by omega))
    (apart_sub sPad (by omega) (by omega)) (apart_sub sCtx (by omega) (by omega))
    (apart_sub sTable (by omega) (by omega)) (apart_sub sZeros (by omega) (by omega)) pre.oPad pre.oCtx pre.oTable pre.oZeros 9
  have body : Runs m w sp env mem RootBytes.fn.body E6 mem3 := by
    show Runs m w sp env mem (.block (_ ++ _ ++ _)) E6 mem3
    rw [List.append_assoc]
    exact Runs.block_append (Runs.block_cons s1 (Runs.block_cons s2 (Runs.block_cons g1 (Runs.block_cons r4
      (Runs.block_cons r5 (Runs.block_nil _ _ _ _ _)))))) run3
  refine ⟨E6, mem3, body, ?_, ready3, ?_⟩
  · -- The root: the tree over the packed bytes, with the length mixed in.
    have treeSize := (merkleizeCapacity_spec (packRange b start stop) n (nodesFor limit)
      (by rw [← hn]; exact Nat.div_le_div_right (by omega)) (by rw [packedSize]; omega)
      (by rw [packedSize, usize]; omega)).1
    have code : rootOf (.byteList limit) b start stop =
        hashPair (merkleizeCapacity (packRange b start stop) n (nodesFor limit)) (lengthNode size) := by
      rw [rootOf, hsize, hn]
    rw [root3, rootData, code, RootProof.hashPair_data _ _ treeSize (by simp [lengthNode, ByteArray.size])]
  · intro a o s pd
    rw [need] at s
    rw [keep3 a (fun h => s ⟨by omega, by omega⟩) o pd]
    exact keep12 a s pd

/-- The byte list driver writes the Lean root of a byte list's range. -/
theorem rootBytes_ok {m : Module} {w : World} (hash : HashingOk m w) (gmod : GatherModule m) (fns : RangeFns m)
    (limit : Nat) : RangeOk m w "ssz_root_bytes" (.byteList limit) := by
  intro sp mem p base start stop out scratch ctx table zeros pad mask b room pre
  have frame : RootBytes.fn.frame = 17 := by decide
  have stack : rootStack (.byteList limit) = 12288 + 1024 := rfl
  obtain ⟨env', mem', run, post⟩ := rootBytes_body hash gmod fns (sp := sp - 8 - 8 * RootBytes.fn.frame)
    (by rw [frame]; omega) pre (rangeEnv_entry _ _ _ _ _ _)
  exact ⟨mem', Calls.fn fns.bytes (by rw [frame]; omega) rfl run rfl, post⟩

end Ssz.Native.Driver
