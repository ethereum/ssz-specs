import SszNative.Ir.Dsl

/-!
Hashing runs of node pairs, on the fastest kernels the processor has.

Every driver receives a context in memory, filled once by the caller:

```text
    ctx + 0    the feature mask the detection routine returns
    ctx + 8    the address of the kernels' constant table
    ctx + 16   the address of the zero-tree roots, 32 bytes per height
    ctx + 24   the address of a 1536-byte scratch area for a padded batch
```

Whole batches of thirty-two go to the two-batch AVX-512 kernel, then one batch of sixteen to the one-batch kernel.
The rest go two at a time, then one, to the SHA instruction kernels.
Without them, the rest is copied into one padded batch of sixteen.
Without AVX-512 either, whole batches of eight go to the AVX2 kernel, and the rest into one padded batch of eight.
Without AVX2 either, the SSE2 kernel every x86-64 processor runs takes batches of four, then one padded batch.
-/

namespace Ssz.Native.Driver

open Ssz.Native.Ir Ssz.Native.Ir.Expr Ssz.Native.Ir.Stmt

/-- The three ways a run of pairs is laid out, by the strides of its left and right nodes. -/
inductive Layout where
  /-- Adjacent nodes of one level: left and right 64 bytes apart each. -/
  | pairs
  /-- Two separate columns: left and right 32 bytes apart each. -/
  | columns
  /-- A column against one fixed node: left 32 bytes apart, right fixed. -/
  | fixed
  deriving DecidableEq, Repr

/-- The kernel name suffix and the strides of a layout. -/
def Layout.info : Layout → String × Nat × Nat
  | .pairs => ("pairs", 64, 64)
  | .columns => ("columns", 32, 32)
  | .fixed => ("fixed", 32, 0)

/-- Thirty-two bytes copied, eight at a time. -/
def copy32 (dst src : Expr) : List Stmt :=
  (List.range 4).map fun k => st (dst + ((8 * k : Nat) : Expr)) (ld (src + ((8 * k : Nat) : Expr)))

section
/-- The output address. -/
private def out : Var := ⟨0⟩
/-- The address of the first left node. -/
private def left : Var := ⟨1⟩
/-- The address of the first right node. -/
private def right : Var := ⟨2⟩
/-- How many pairs, or nodes, remain. -/
private def count : Var := ⟨3⟩
/-- The context the caller filled. -/
private def ctx : Var := ⟨4⟩
/-- The feature mask. -/
private def mask : Var := ⟨5⟩
/-- The address of the constant table. -/
private def table : Var := ⟨6⟩
/-- A number of pairs one kernel call takes. -/
private def n : Var := ⟨7⟩
/-- The result, always zero. -/
private def status : Var := ⟨8⟩
/-- A loop index, also the sink for kernels' zero results. -/
private def i : Var := ⟨9⟩
/-- The padded batch area. -/
private def pad : Var := ⟨10⟩

/-- Move every pointer past a number of pairs, and count them off. -/
def advance (ls rs : Nat) (pairsDone : Expr) : List Stmt :=
  [out ::= out + 32 * pairsDone, left ::= left + (↑ls : Expr) * pairsDone,
    right ::= right + (↑rs : Expr) * pairsDone, count ::= count - pairsDone]

/--
Whole batches of 2^k pairs, in one call to a kernel taking that many pairs per unit of its count.

Shifts count the batches and the pairs they cover, so no division or product sits before the call.
-/
def batches (kernel : String) (k ls rs : Nat) : List Stmt :=
  [n ::= .shr count k, when (ne n 0) [.call kernel [out, left, right, n, table] i.idx], n ::= .shl n k] ++
    advance ls rs n

/--
The last pairs, fewer than a batch, copied into one batch and hashed there by a kernel taking a batch per unit.

Messages go from the padding area, digests to 1024 bytes past it, and only the real digests are copied out.
The unused messages hold whatever the area held, and their digests are never read.
-/
def padded (kernel : String) (ls rs : Nat) : List Stmt :=
  [when (ne count 0) [pad ::= ld (ctx + 24), i ::= 0,
    while_ (lt i count) (copy32 (pad + 64 * i) (left + (↑ls : Expr) * i) ++
      copy32 (pad + 64 * i + 32) (right + (↑rs : Expr) * i) ++ [i ::= i + 1]),
    .call kernel [pad + 1024, pad, pad + 32, 1, table] i.idx, i ::= 0,
    while_ (lt i count) (copy32 (out + 32 * i) (pad + 1024 + 32 * i) ++ [i ::= i + 1])]]

/--
Hash a run of pairs in one layout: arguments out, left, right, count, ctx.

Returns zero: every x86-64 processor runs the last resort, the SSE2 kernel.
-/
def hashRun (layout : Layout) : Fn :=
  let (suffix, ls, rs) := layout.info
  let kernel (family : String) := s!"ssz_sha256_{family}_{suffix}"
  { params := 5, vars := 11, result := status,
    body := .block [mask ::= ld ctx, table ::= ld (ctx + 8), status ::= 0,
      -- Whole batches of thirty-two, then one of sixteen.
      when (ne (mask &&& 2) 0) (batches (kernel "avx512x2") 5 ls rs ++ batches (kernel "avx512") 4 ls rs),
      ifElse (ne (mask &&& 1) 0)
        -- Twos, then a last single pair.
        (batches (kernel "shani_dual") 1 ls rs ++
          [when (ne count 0) [.call (kernel "shani") [out, left, right, count, table] i.idx]])
        [ifElse (ne (mask &&& 2) 0)
          -- One padded batch of sixteen.
          (padded "ssz_sha256_avx512_pairs" ls rs)
          [ifElse (ne (mask &&& 8) 0)
            -- Whole batches of eight, then one padded batch.
            (batches (kernel "avx2") 3 ls rs ++ padded "ssz_sha256_avx2_pairs" ls rs)
            -- Whole batches of four, then one padded batch.
            (batches (kernel "baseline") 2 ls rs ++ padded "ssz_sha256_baseline_pairs" ls rs)]]] }
end

end Ssz.Native.Driver
