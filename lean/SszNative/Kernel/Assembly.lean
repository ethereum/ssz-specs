import SszNative.Asm.Print
import SszNative.Kernel.Avx512
import SszNative.Kernel.Avx512x2
import SszNative.Kernel.Avx2
import SszNative.Kernel.Baseline
import SszNative.Kernel.ShaNi
import SszNative.Kernel.ShaNiDual
import SszNative.Kernel.Gather
import SszNative.Kernel.Detect
import SszNative.Driver.Tree
import SszNative.Driver.Gather
import SszNative.Driver.Codec
import SszNative.Driver.Root
import SszNative.Driver.Branch
import SszNative.Driver.Prove
import SszNative.Driver.Validate
import SszNative.Driver.TreeStore
import SszNative.Ir.Link

/-! The native kernels and their constant table, as the one assembler file the native library is built from. -/

namespace EthLib.Consensus.Ssz.Native

/-- The drivers written in the language, each under its exported name. -/
def shippedFns : List (String × Ir.Fn) :=
  [("ssz_hash_pairs", Driver.hashRun .pairs),
    ("ssz_hash_columns", Driver.hashRun .columns),
    ("ssz_hash_fixed", Driver.hashRun .fixed),
    ("ssz_merkleize", Driver.merkleize),
    ("ssz_gather_field", Driver.gatherField)] ++
  Driver.codecFns ++ Driver.rootFns ++ Driver.branchFns ++ Driver.proveFns ++ Driver.Validate.fns ++
  Driver.treeStoreFns

/-- The kernels written by hand, and the feature detection, each under its exported name. -/
def shippedExterns : Asm.Image :=
  #[("ssz_sha256_avx512_pairs", Kernel.Avx512.program 64 64),
    ("ssz_sha256_avx512_columns", Kernel.Avx512.program 32 32),
    ("ssz_sha256_avx512_fixed", Kernel.Avx512.program 32 0),
    ("ssz_sha256_avx512x2_pairs", Kernel.Avx512x2.program 64 64),
    ("ssz_sha256_avx512x2_columns", Kernel.Avx512x2.program 32 32),
    ("ssz_sha256_avx512x2_fixed", Kernel.Avx512x2.program 32 0),
    ("ssz_sha256_avx2_pairs", Kernel.Avx2.program 64 64),
    ("ssz_sha256_avx2_columns", Kernel.Avx2.program 32 32),
    ("ssz_sha256_avx2_fixed", Kernel.Avx2.program 32 0),
    ("ssz_sha256_baseline_pairs", Kernel.Baseline.program 64 64),
    ("ssz_sha256_baseline_columns", Kernel.Baseline.program 32 32),
    ("ssz_sha256_baseline_fixed", Kernel.Baseline.program 32 0),
    ("ssz_sha256_shani_pairs", Kernel.ShaNi.program 64 64),
    ("ssz_sha256_shani_columns", Kernel.ShaNi.program 32 32),
    ("ssz_sha256_shani_fixed", Kernel.ShaNi.program 32 0),
    ("ssz_sha256_shani_dual_pairs", Kernel.ShaNiDual.program 64 64),
    ("ssz_sha256_shani_dual_columns", Kernel.ShaNiDual.program 32 32),
    ("ssz_sha256_shani_dual_fixed", Kernel.ShaNiDual.program 32 0),
    ("ssz_gather", Kernel.gather),
    ("ssz_gather_1", Kernel.gatherNode 1),
    ("ssz_gather_2", Kernel.gatherNode 2),
    ("ssz_gather_4", Kernel.gatherNode 4),
    ("ssz_gather_8", Kernel.gatherNode 8),
    ("ssz_gather_16", Kernel.gatherNode 16),
    ("ssz_gather_32", Kernel.gatherNode 32),
    ("ssz_gather_key", Kernel.gatherKey),
    ("ssz_cpu_features", Kernel.detect)]

/-- The routines, each under its exported name: the drivers compiled and linked, then the kernels. -/
def routines : List (String × Array Asm.Instr) :=
  (Ir.Module.link shippedFns shippedExterns).toList

/-- Every routine's operands fit their encodings, so the assembler encodes each as the model reads it. -/
theorem routines_valid : routines.all (fun routine => Asm.valid routine.2) = true := by
  decide +kernel

/-- No two routines export the same name, so every call and every label lands where it is meant to. -/
theorem routines_distinct : (routines.map (·.1)).Nodup := by
  decide +kernel

/-- The assembler file, which `native/kernels_x86.S` must equal. -/
def assembly : String :=
  Asm.file routines [("ssz_sha256_table", Kernel.table), ("ssz_zero_roots", Driver.zeroRootsTable)] routines_valid

end EthLib.Consensus.Ssz.Native
