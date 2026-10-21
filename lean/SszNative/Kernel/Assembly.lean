import SszNative.Asm.Print
import SszNative.Kernel.Avx512
import SszNative.Kernel.ShaNi
import SszNative.Kernel.ShaNiDual
import SszNative.Kernel.Gather

/-! The native kernels and their constant table, as the one assembler file the native library is built from. -/

namespace Ssz.Native

/-- The assembler file, which `native/kernels_x86.S` must equal. -/
def assembly : String :=
  Asm.file
    [("ssz_sha256_avx512_pairs", Kernel.Avx512.program 64 64),
      ("ssz_sha256_avx512_columns", Kernel.Avx512.program 32 32),
      ("ssz_sha256_avx512_fixed", Kernel.Avx512.program 32 0),
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
      ("ssz_gather_key", Kernel.gatherKey)]
    [("ssz_sha256_table", Kernel.table)]

end Ssz.Native
